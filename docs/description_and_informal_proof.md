Verified optimised epoch processing
===================================

Implementations of the Ethereum [consensus specification][consensus-specs] typically make use of
algorithmic optimisations to achieve high performance. The correctness of these optimisations is
critical to Ethereum's security, and so far they have been checked by manual review, testing and
fuzzing. To further increase assurance we propose to formally prove correctness of an optimised
implementation.

This document describes the optimised implementation which we are in the process of verifying,
and includes a high-level argument for its correctness.

## Scope

We only consider the `process_epoch` function which is responsible for computing state changes at
the end of each 32-slot epoch. Block processing (`process_block`) is considered out of scope for now
but may be covered by future work.

Our goal is to verify an implementation of `process_epoch` containing the minimum number of $O(n)$
iterations over the validator set ($n$ is the number of validators). We consider not only the
`state.validators` field, but also the other length $n$ fields of the state including:

- `.validators`
- `.balances`
- `.previous_epoch_participation`
- `.current_epoch_participation`
- `.inactivity_scores`

The specification version targeted is v1.3.0, for the Capella hard fork. We anticipate that the
proofs will be able to be updated for Deneb quite easily because there are minimal changes to epoch
processing in the Deneb fork.

## Motivation

As the validator set grows the amount of computation required to process blocks and states
increases. If the algorithms from [consensus-specs][] were to be used as-is, the running time of
`process_epoch` would be increasing quadratically ($O(n^2)$) as validators are added.

Another motivation for optimising epoch processing is that it grants implementations the freedom to
explore different state models. Some clients have already switched their `BeaconState`
representation from an array-based model to a tree-based model, which allows for better sharing of
data between states, and therefore better caching. The downside of the tree-based model is that it
tends to have substantially slower indexing (e.g. computing `state.validators[i]`), and
iteration is slightly slower (same time complexity with a larger constant).

| Operation | Array-based | Tree-based  |
|-----------|-------------|-------------|
| index     | $O(1)$      | $O(\log n)$ |
| iterate   | $O(n)$      | $O(c * n)$  |

Hence in the tree-based paradigm it becomes even more important to remove random-access indexing,
and to remove $O(n^2)$ nested iterations which amplify the higher cost of tree-based iteration.

## Algorithm Description

The key idea behind the optimised implementation is the combination of several stages
of `process_epoch` into a single iteration. This single iteration applies mutations to the
`validators`, `balances` and `inactivity_scores` in a way that preserves the semantics of the
original `process_epoch` function. Care is taken to ensure that reads and writes are not reordered
in a way that causes an overwritten value to be observed by a function which expects
to read the prior value. The spec's separate stages make this analysis of which fields are read and
written by individual functions quite straight-forward, and this forms a large part of our
correctness argument.

The stages of `process_epoch` which are combined into the single iteration are:

- `process_inactivity_updates`
- `process_rewards_and_penalties`
- `process_registry_updates`
- `process_slashings`
- `process_effective_balance_updates`

These functions represent the most computationally intense parts of `process_epoch`, with the other
functions not involving any $O(n)$ or greater processing. The exception is
`process_justification_and_finalization`, which is given special treatment due to its use of
aggregate information.

### Aggregates and Data Dependencies

The data dependencies between fields are such that the updated values of
`.validators`/`.balances`/`.inactivity_scores` for the $i$-th validator can be computed _mostly_
from the previous values for the $i$-validator. In other words, without dependence on the values
for other validators. This is the primary reason that we are able to

The exception to this are the aggregate values which are computed over the entire validator set and
fed into the calculations for each individual validator.

The fundamental aggregate values are the sums of effective balances for different subsets of the
validator set. We consider 7 variations of these sums: 1 for the set of validators active in
the previous epoch (`total_active_balance`) and 6 for the subsets of validators active in the previous
and current epochs respectively, who attested correctly for each of 3 attestation flags (head,
target, source).

From these aggregate sums the finalization and justification aggregates are computed,
which also feed into later calculations. Conveniently, the aggregate sums can be computed _once_ at
the beginning of `process_epoch` and reused in all subsequent phases. The handling of these
aggregates happens as part of the _Progressive Balances Cache_ described below.

The activation queue also requires aggregation over the entire validator set, and we have a
two-phase process for this aggregation which is computed over two subsequent `process_epoch` calls.
See the _Activation Queue_ section below.

## Progressive Balances Cache

We define the progressive balances cache as a structure holding the 7 aggregate balances like so:

```python
class ProgressiveBalancesCache:
    # Total active balance for the previous epoch.
    total_active_balance: Gwei
    # Attestation total balances for the previous epoch.
    # Indexed by `TIMELY_SOURCE_FLAG_INDEX`, etc.
    previous_epoch_flag_attesting_balances: List[Gwei, 3],
    # Attestation total balances for the current epoch.
    current_epoch_flag_attesting_balances: List[Gwei, 3],
```

The correct values of the progressive balances cache are defined by the `valid_progressive_balances`
predicate:

```python
def get_flag_attesting_balance(state: BeaconState, flag_index: int, epoch: Epoch) -> Gwei:
    return get_total_balance(state, get_unslashed_participating_indices(state, flag_index, epoch))

def valid_progressive_balances(
    state: BeaconState,
    p: ProgressiveBalancesCache
) -> Bool:
    previous_epoch = get_previous_epoch(state)
    current_epoch = get_current_epoch(state)

    return p.total_active_balance == get_total_active_balance(state) and
        p.previous_epoch_flag_attesting_balances == [
            get_flag_attesting_balance(state, TIMELY_SOURCE_FLAG_INDEX, previous_epoch),
            get_flag_attesting_balance(state, TIMELY_TARGET_FLAG_INDEX, previous_epoch),
            get_flag_attesting_balance(state, TIMELY_HEAD_FLAG_INDEX, previous_epoch)
        ] and
        p.current_epoch_flag_attesting_balances == [
            get_flag_attesting_balance(state, TIMELY_SOURCE_FLAG_INDEX, current_epoch),
            get_flag_attesting_balance(state, TIMELY_TARGET_FLAG_INDEX, current_epoch),
            get_flag_attesting_balance(state, TIMELY_HEAD_FLAG_INDEX, current_epoch)
        ]
```

Since changes were made to fork choice to handle unrealised justification and finalization
(see [disclosure][fc_pull_tips_disc]), consensus clients need to run
`process_justification_and_finalization` after _every_ block. To do this efficiently, many of them
include a cache that is equivalent to the progressive balances cache. This cache is called
_progressive_ because it computes the aggregate sums incrementally, updating them after relevant
events in each block.

Although in future work we may prove the correctness of a progressive balance cache implementation,
in this formalisation of `process_epoch` we assume that there exists _some_ function called
`get_progressive_balances` which satisfies:

```python
valid_progressive_balances(state, get_progressive_balances(state)) == True
```

Implementations may choose to use an existing progressive balances cache if they have one,
or can compute one anew in a single iteration, bringing the total number of $O(n)$ iterations in
epoch processing to 2.

```python
def get_progressive_balances(state):
    # Get cached balances from state or compute in a single iteration.
    # [ASSUMED]
    ...
```

## Activation Queue

Another aggregate computation requiring special consideration is the calculation of the activation
queue: the list of validators to be activated in the next epoch. The spec calculates this in its
own $O(n)$ iteration during `process_registry_updates`:

```python
# Queue validators eligible for activation and not yet dequeued for activation
activation_queue = sorted([
    index for index, validator in enumerate(state.validators)
    if is_eligible_for_activation(state, validator)
    # Order by the sequence of activation_eligibility_epoch setting and then index
], key=lambda index: (state.validators[index].activation_eligibility_epoch, index))
```

Instead of this loop, our algorithm computes the queue across two consecutive calls to `process_epoch` as part of the single-pass loops of each:

- In the first single-pass loop (end of epoch $N - 1$): add validators that *could* be eligible for
  activation at the end of epoch $N$ to a cache that is sorted by `(activation_eligibiliy_epoch,
  validator_index)`.
- In the second single-pass loop (end of epoch $N$): filter the validators from the preliminary
  queue based on whether their `activation_eligibility_epoch` is less than or equal to the
  finalized epoch, and the `churn_limit` (which bounds the number of activated validators).

Formally we define the activation queue as a structure:

```python
class ActivationQueue:
    # List of validators that *could* be eligible for activation.
    # Implementations should use a data structure with O(log n) inserts instead of a list.
    eligible_validators: [(Epoch, ValidatorIndex)]
```

Entry into the tentative activation queue is determined by the predicate
`could_be_eligible_for_activation_at(validator, N)`:

```python
def could_be_eligible_for_activation_at(validator: Validator, epoch: Epoch) -> bool:
    return (
        # Placement in queue *could be* finalized at `epoch`
        validator.activation_eligibility_epoch < epoch
        # Has not yet been activated
        and validator.activation_epoch == FAR_FUTURE_EPOCH
    )
```

This predicate is called for each validator during epoch processing at the end
of epoch $N - 1$ by the function:

```python
def add_if_could_be_eligible_for_activation(
    activation_queue: ActivationQueue,
    index: ValidatorIndex,
    validator: Validator,
    next_epoch: Epoch
):
    if could_be_eligible_for_activation_at(validator, next_epoch):
        self.eligible_validators.append((validator.activation_eligibility_epoch, index))
        self.eligible_validators.sort()
```

This is usually done as part of epoch processing for the previous epoch, although for cases where
that is not possible we also define an initialization function:

```python
def new_activation_queue(
    state: BeaconState
) -> ActivationQueue:
    activation_queue = ActivationQueue()
    next_epoch = get_current_epoch(state) + 1
    for (i, validator) in enumerate(state.validators):
        add_if_could_be_eligible_for_activation(activation_queue, i, validator, next_epoch)
    return activation_queue
```

During epoch processing for epoch $N$, the speculative queue is restricted based
on the true finalized epoch and the churn limit:

```python
def get_validators_eligible_for_activation(
    activation_queue: ActivationQueue,
    finalized_epoch: Epoch,
    churn_limit: uint64,
) -> [ValidatorIndex]:
    return [
        index for (eligibility_epoch, index) in activation_queue.eligible_validators
        if eligibility_epoch <= finalized_epoch
    ][:churn_limit]
```

## Epoch Cache

TODO

### Overview for `process_epoch`

```python
def process_epoch(state: BeaconState) -> None:
    # Compute (or fetch) the aggregates computed over the entire validator set.
    progressive_balances = get_progressive_balances(state)

    # [CHANGED] Use the aggregate sums to compute justification and finalization.
    process_justification_and_finalization(state, progressive_balances)

    # [CHANGED] Compute the majority of processing in a single iteration, utilising the progressive
    # balances for aggregates.
    process_epoch_single_pass(state, progressive_balances)

    # [CHANGED] Reorder `process_slashings` and `process_eth1_data_reset` after
    # `process_effective_balances` which is now part of `process_epoch_single_pass`.
    process_slashings(state)
    process_eth1_data_reset(state)

    # [UNCHANGED] These functions are unaffacted.
    process_slashings_reset(state)
    process_randao_mixes_reset(state)
    process_historical_summaries_update(state)
    process_participation_flag_updates(state)
    process_sync_committee_updates(state)
```

### Single-pass epoch processing `process_epoch_single_pass`

We define a few helper data structures which are used to pass information around during
single-pass epoch processing:

```python
# Information about a single validator that is bundled for reuse.
class ValidatorInfo:
    index: ValidatorIndex,
    effective_balance: uint64,
    base_reward: uint64,
    is_eligible: bool,
    is_slashed: bool,
    is_active_current_epoch: bool,
    is_active_previous_epoch: bool,
    previous_epoch_participation: ParticipationFlags,
    current_epoch_participation: ParticipationFlags,
```

```python
# Information about the state that is fixed for the duration of single-pass processing.
class StateContext:
    current_epoch: Epoch,
    next_epoch: Epoch,
    is_in_inactivity_leak: bool,
    churn_limit: uint64,
```

```python
# Shared context for rewards and penalties calculations.
class RewardsAndPenaltiesContext:
    unslashed_participating_increments_array: [uint64; NUM_FLAG_INDICES],
    active_increments: uint64,
```

```python
# Shared context for `process_slashings` calculations.
class SlashingsContext:
    adjusted_total_slashing_balance: uint64,
    target_withdrawable_epoch: Epoch,
```

```python
# Shared context for `process_effective_balance_updates`.
class EffectiveBalancesContext:
    downward_threshold: uint64,
    upward_threshold: uint64,
```

We define initialisers for these contexts:

```python
def new_slashings_context(
    state: BeaconState,
    state_ctxt: StateContext,
) -> SlashingsContext:
    adjusted_total_slashing_balance = min(
        sum(state.slashings) * PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX, total_balance
    )
    target_withdrawable_epoch = (
        state_ctxt.current_peoch + EPOCHS_PER_SLASHINGS_VECTOR // 2
    )
    return SlashingsContext(
        adjusted_total_slashing_balance=adjusted_total_slashing_balance,
        target_withdrawable_epoch=target_withdrawable_epoch,
    )
```

```python
def unslashed_participating_increment(flag_index) -> Gwei:
    unslashed_participating_balance = (
        progressive_balances.previous_epoch_flag_attesting_balances[flag_index]
    )
    return unslashed_participating_balance // EFFECTIVE_BALANCE_INCREMENT

def new_rewards_and_penalties_context(
    progressive_balances: ProgressiveBalancesCache,
) -> RewardsAndPenaltiesContext:
    unslashed_participating_increments_array = [
        unslashed_participating_increment(flag_index)
        for flag_index in range(NUM_FLAG_INDICES)
    ]
    active_increments = (
        progressive_balances.total_active_balance // EFFECTIVE_BALANCE_INCREMENT
    )
    return RewardsAndPenaltiesContext(
        unslashed_participating_increments_array=unslashed_participating_increments_array,
        active_increments=active_increments,
    )
```

```python
def new_effective_balances_context() -> EffectiveBalancesContext:
    hysteresis_increment = uint64(EFFECTIVE_BALANCE_INCREMENT // HYSTERESIS_QUOTIENT)
    return EffectiveBalancesContext(
        downward_threshold=hysteresis_increment * HYSTERESIS_DOWNWARD_MULTIPLIER,
        upward_threshold=hysteresis_increment * HYSTERESIS_UPWARD_MULTIPLIER,
    )
```

```python
def is_unslashed_participating_index(
    validator_info: ValidatorInfo, flag_index: int
) -> bool:
    return (
        validator_info.is_active_previous_epoch
        and not validator_info.is_slashed
        and has_flag(validator_info.previous_epoch_participation, flag_index)
    )
```

```python
def get_base_reward_fast(
    effective_balance: Gwei,
    progressive_balances: ProgressiveBalancesCache,
) -> Gwei:
    increments = effective_balance // EFFECTIVE_BALANCE_INCREMENT
    return Gwei(increments * get_base_reward_per_increment_fast(progressive_balances))


def get_base_reward_per_increment_fast(
    progressive_balances: ProgressiveBalances,
) -> Gwei:
    return Gwei(
        EFFECTIVE_BALANCE_INCREMENT
        * BASE_REWARD_FACTOR
        // integer_squareroot(progressive_balances.total_active_balance)
    )
```

The function which fuses the loops for the stages is called `process_epoch_single_pass`:

```python
def process_epoch_single_pass(
    state: BeaconState,
    progressive_balances: ProgressiveBalancesCache,
) -> None:
    assert valid_progessive_balances(state, progressive_balances)

    # TODO: need active indices cache to eliminate loop in `get_validator_churn_limit`
    state_ctxt = StateContext(
        current_epoch=get_current_epoch(state),
        next_epoch=get_current_epcoch(state) + 1,
        is_in_inactivity_leak=is_in_inactivity_leak(state),
        churn_limit=get_validator_churn_limit(state),
    )
    slashings_ctxt = new_slashings_context(state, state_ctxt)
    rewards_ctxt = new_rewards_and_penalties_context(progressive_balances)
    effective_balances_ctxt = new_effective_balances_ctxt()

    # Determine the final activation queue.
    activation_queue = get_validators_eligible_for_activation(
        state.activation_queue,
        state.finalized_checkpoint.epoch,
        state_ctxt.churn_limit,
    )
    # Create a new speculative activation queue for next epoch.
    next_epoch_activation_queue = ActivationQueue(eligible_validators=[])

    for (
        index,
        validator,
        balance,
        inactivity_score,
        prev_participation,
        curr_participation,
    ) in zip(
        range(0, len(state.validators)),
        state.validators,
        state.balances,
        state.inactivity_scores,
        state.previous_epoch_participation,
        state.current_epoch_participation,
    ):
        is_active_current_epoch = is_active_validator(validator, current_epoch)
        is_active_previous_epoch = is_active_validator(validator, previous_epoch)
        is_eligible = is_active_previous_epoch or (
            validator.slashed and previous_epoch + 1 < validator.withdrawable_epoch
        )
        validator_info = ValidatorInfo(
            index=index,
            effective_balance=validator.effective_balance,
            base_reward=get_base_reward_fast(validator.effective_balance, progressive_balances),
            is_eligible=is_eligible,
            is_active_current_epoch=is_active_current_epoch,
            is_active_previous_epoch=is_active_previous_epoch,
            previous_epoch_participation=prev_participation,
            current_epoch_participation=curr_participation
        )

        if current_epoch != GENESIS_EPOCH:
            # Note: we may change the presentation of this mutation. Due to primitive types
            # being immutable in Python we cannot pass a mutable reference. Our Isabelle
            # formalisation will likely model the mutation natively (a write to the heap).
            inactivity_score = process_single_inactivity_update(
                inactivity_score,
                validator_info,
                state_ctxt,
            )
            state.inactivity_scores[index] = inactivity_score

            balance = process_single_reward_and_penalty(
                balance,
                inactivity_score,
                validator_info,
                rewards_ctxt,
                state_ctxt
            )
            state.balances[index] = balance

        # TODO define exit cache
        process_single_registry_update(
            validator,
            validator_info,
            state.exit_cache,
            activation_queue,
            next_epoch_activation_queue,
            state_ctxt,
        )

    state.activation_queue = next_epoch_activation_queue
```

### Inactivity: `process_single_inactivity_update`

```python
def process_single_inactivity_update(
    inactivity_score: uint64,
    validator_info: ValidatorInfo,
    state_ctxt: StateContext,
) -> uint64:
    if not validator_info.is_eligible:
        return inactivity_score

    # Increase inactivity score of inactive validators
    new_inactivity_score = inactivity_score
    if is_unslashed_participating_index(validator_info, TIMELY_TARGET_FLAG_INDEX):
        new_inactivity_score -= min(1, inactivity_score)
    else:
        new_inactivity_score += INACTIVITY_SCORE_BIAS

    # Decrease the inactivity score of all eligible validators during a leak-free epoch
    if not state_ctxt.is_in_inactivity_leak:
        new_inactivity_score -= min(
            INACTIVITY_SCORE_RECOVERY_RATE, new_inactivity_score
        )

    return new_inactivity_score
```

### Rewards and Penalties: `process_single_reward_and_penalty`

```python
def process_single_reward_and_penalty(
    balance: Gwei,
    inactivity_score: uint64,
    validator_info: ValidatorInfo,
    rewards_ctxt: RewardsAndPenaltiesContext,
    state_ctxt: StateContext,
) -> uint64:
    if not validator_info.is_eligible:
        return balance

    rewards = 0
    penalties = 0

    for flag_index in range(len(PARTICIPATION_FLAG_WEIGHTS)):
        reward, penalty = get_flag_index_delta(
            validator_info, flag_index, rewards_ctxt, state_ctxt
        )
        rewards += reward
        penalties += penalty

    reward, penalty = get_inactivity_penalty_delta(
        validator_info,
        inactivity_score,
        state_ctxt,
    )
    rewards += reward
    penalties += penalty

    if rewards != 0 or penalties != 0:
        new_balance = balance + rewards
        new_balance = 0 if penalties > new_balance else new_balance - penalties
        return new_balance
    else:
        return balance
```

```python
def get_flag_index_delta(
    validator_info: ValidatorInfo,
    flag_index: int,
    rewards_ctxt: RewardsAndPenaltiesContext,
    state_ctxt: StateContext,
) -> (Gwei, Gwei):
    base_reward = validator_info.base_reward
    weight = PARTICIPATION_FLAG_WEIGHTS[flag_index]
    unslashed_participating_increments = (
        rewards_ctxt.unslashed_participating_increments_array[flag_index]
    )

    if is_unslashed_participating_index(validator_info, flag_index):
        if not state_ctxt.is_in_inactivity_leak:
            reward_numerator = base_reward * weight * unslashed_participating_increments
            reward_denominator = rewards_ctxt.active_increments * WEIGHT_DENOMINATOR
            reward = reward_numerator / reward_denominator
            return (reward, 0)
    elif flag_index != TIMELY_HEAD_FLAG_INDEX:
        penalty = base_reward * weight / WEIGHT_DENOMINATOR
        return (0, penalty)
    return (0, 0)
```

```python
def get_inactivity_penalty_delta(
    validator_info: ValidatorInfo,
    inactivity_score: uint64,
    state_ctxt: StateContext,
) -> (Gwei, Gwei):
    # Implementation note: could abstract over fork's inactivity penalty quotient here
    if not is_unslashed_participating_index(TIMELY_TARGET_FLAG_INDEX):
        penalty_numerator = validator_info.effective_balance * inactivity_score
        penalty_denominator = INACTIVITY_SCORE_BIAS * INACTIVITY_PENALTY_QUOTIENT_BELLATRIX
        penalty = penalty_numerator / penalty_denominator
        return (0, penalty)
    return (0, 0)
```

## Registry Updates: `process_single_registry_update`

```python
def process_single_registry_update(
    validator: Validator,
    validator_info: ValidatorInfo,
    exit_cache: ExitCache,
    activation_queue: [ValidatorIndex],
    next_epoch_activation_queue: ActivationQueue,
    state_ctxt: StateContext,
):
    current_epoch = state_ctxt.current_epoch

    if is_eligible_for_activation_queue(validator):
        validator.activation_eligibility_epoch = current_epoch + 1

    if (
        is_active_validator(validator, current_epoch)
        and validator.effective_balance <= EJECTION_BALANCE
    ):
        # TODO: define `initiate_validator_exit_fast` and exit cache
        initiate_validator_exit_fast(validator, exit_cache, state_ctxt)

    if validator_info.index in activation_queue:
        validator.activation_epoch = compute_activation_exit_epoch(current_epoch)

    # Caching: add to speculative activation queue for next epoch.
    add_if_could_be_eligible_for_activation(
        new_activation_queue,
        validator_info.index,
        validator,
        state_ctxt.next_epoch,
    )
```

## Informal Proof Sketch

### Auxiliary Lemmas

**Lemma `justification_upper_bound`:** During epoch processing at the end of epoch
$N$, after running `process_justification_and_finalization` the current justified epoch of the
state is at most $N$.

**Proof**: By induction on $N$. For $N=0$, the current justified epoch is also 0. For later epochs,
`current_justified_checkpoint` is not modified outside of `process_justification_and_finalization`,
which either sets it to a checkpoint with epoch $N - 1$ (the previous epoch), the current epoch
($N$), or leaves it untouched ($N - 1$ by the inductive hypothesis).

**Lemma `finalization_upper_bound`:** If $N > 0$ then during epoch processing at the end of epoch
$N$, after running `process_justification_and_finalization` the finalized epoch of the state is at
most $N - 1$.

**Proof**: By induction on $N$. At the end of epoch $N = 1$ the finalized checkpoint remains at epoch
0 due to the early return for `current_epoch <= GENESIS_EPOCH + 1`. In subsequent epochs the
finalized epoch is set in `process_justification_and_finalization` to either the previous epoch's
current justified epoch (at most $N - 1$ by lemma `justification_upper_bound`) or the previous
epoch's previous justified epoch (at most $N - 2$ due to this value being set from
`current_justified_checkpoint`).

**Lemma `active_indices_fixed`:** The value of `get_active_validator_indices(state, N)` is the
same for all intermediate values of `state` during epoch processing at the end of epoch `N`.

**Proof:** TODO

**Lemma `prev_active_indices_fixed`:** The value of `get_active_validator_indices(state, N - 1)` is
the same for all intermediate values of `state` during epoch processing at the end of epoch `N`.

**Proof:** TODO

**Lemma `total_active_balance_fixed`:** During epoch processing at the end of epoch $N$,
the value of `get_total_active_balance(state, N)` is fixed for all intermediate states prior to
the execution of `process_effective_balance_updates`.

**Proof**: The total active balance is computed from the list of validator indices active in the
current epoch, which is fixed, per lemma `active_indices_fixed`. The other input is the
`effective_balance` for each validator, which is only updated in
`process_effective_balance_updates`.  Therefore the value of `get_total_active_balance` is constant
until `process_effective_balance_updates` executes.

**Lemma `base_reward_fixed`:** During epoch processing at the end of epoch $N$,
the value of `get_base_reward(state, index)` is fixed per-index for all intermediate states prior to
the execution of `process_effective_balance_updates`.

**Proof:** The base reward is computed from the validator's effective balance and the total active
balance for the current epoch, both of which are fixed until `process_effective_balance_updates`
executes (by lemma `total_active_balance_fixed`).

**Lemma `is_in_inactivity_leak_fixed`:** During epoch processing at the end of epoch $N$,
the value of `is_in_inactivity_leak(state)` is fixed for all intermediate states _after_ the
execution of `process_justification_and_finalization`.

**Proof:** The inactivity leak calculation depends on the previous epoch, which is fixed
for the given states (the `slot` being constant). Additionally it depends on the finalized epoch,
which can only change as part of `process_justification_and_finalization`.

### Activation Queue Proof

**Lemma `aq_correct`:** The activation queue computed by `process_registry_updates` is equal to
the queue computed by `get_validators_eligible_for_activation`.

**Proof:**

- We handle epoch $N = 0$ separately. In this case the activation queue computed by
  `process_registry_updates` contains `churn_limit` validators with
  `activation_eligibility_epoch=0`. The tentative queue formed by calling
  `new_activation_queue` on any epoch 0 state contains all validators with
  `activation_eligibility_epoch < 1`, i.e. `activation_eligibility_epoch=0`. Due to
  `activation_eligibility_epoch` being immutable throughout block processing, it is sufficient
  to use any epoch 0 state. The filtering of the tentative queue by
  `get_validators_eligible_for_activation` does not remove any validators, because the finalized
  epoch is 0 and cannot change (`<= GENESIS_EPOCH + 1`). The tentative queue is sorted the same as
  the queue from `process_registry_updates`, and is reduced to at most `churn_limit` items by
  `get_validators_eligible_for_activation`. Therefore, as long as the `churn_limit` parameter is set
  to `get_churn_limit(state)`, the two queues are equal.
- For $N > 0$ we have:
    - In epoch processing at the end of epoch $N - 1$ we compute the tentative queue containing
      all validators with `activation_eligibility_epoch < N` that have not yet been activated.
    - In epoch processing at the end of epoch $N$ we know that the finalized epoch is $\leq N - 1$
      by the lemma `finalization_upper_bound`.
    - Validators do not become eligible for activation until the epoch *after* they are processed
      by `process_registry_updates`, which sets `activation_eligibility_epoch = current_epoch + 1`.
      Therefore validators that are marked eligible in epoch $N - 1$ have an eligibility epoch
      equal to $N$, and validators marked eligible in epoch $N$ have an eligibility epoch equal to
      $N + 1$. Neither are eligible for activation in epoch $N$, because the activation queue
      considers only validators with `activation_eligibility_epoch <= state.finalized_checkpoint.epoch <= N - 1`.
      Therefore the list of not-yet-activated validators in the tentative queue with
      `activation_eligibility_epoch < N` is a superset of the list of validators in the activation
      queue.
    - By filtering the tentative queue based on the new finalized epoch computed during epoch $N$,
      we obtain equality with the `activation_queue` from `process_registry_updates`. Due to the
      queue being sorted by increasing eligibility epoch, the `activation_queue` is a prefix of
      the tentative queue prior to filtering.
    - The churn limit used to limit both queues is equal, so the list of validators considered
      for activation is the same for both approaches.

### Justificaton and Finalization Proof

**Lemma:** Computing justification and finalization using the progressive balances cache
is equivalent to `process_justification_and_finalization`.

**Proof**: The progressive balances cache `p` satisfies `valid_progressive_balances(pre_state, p)` where `pre_state` is the state at the very start of epoch processing before any changes are made. During the execution of `process_justification_and_finalization`, the aggregate values `total_active_balance`, `previous_target_balance` and `current_target_balance` are equal to `p.total_active_balance`, `p.previous_epoch_flag_attesting_balances[TIMELY_TARGET_FLAG_INDEX]` and `p.current_epoch_flag_attesting_balances[TIMELY_TARGET_FLAG_INDEX]` respectively. This follows from the equality established by `valid_progressive_balances` and the fact that no modifications are made to `pre_state` before these values are calculated by `process_justification_and_finalization`. Therefore, both functions pass the same values to `weigh_justification_and_finalization`
, and compute the same result.

### Rewards and Penalties Proof

**Lemma:** Computing rewards and penalties during `process_epoch_single_pass` is equivalent
to computing them using `process_rewards_and_penalties`.

**Proof:** In `process_rewards_and_penalties` rewards are computed for the entire validator registry
for each of the 3 attestation flags using `get_flag_index_deltas`, while
`get_inactivity_penalty_delta` computes the rewards for inactivity penalties. Our claim is that the
single-pass functions `get_flag_index_delta` and `get_inactivity_penalty` compute the same rewards
for each individual index, and that the fusion into a single loop does not affect the result.

For `get_flag_index_deltas` the main inputs are the list of `unslashed_participating_indices`, and
the `unslashed_participating_balance` derived from the participating indices and their respective
effective balances (`state.validators[i].effective_balance`). The participating indices are computed
by `get_unslashed_participating_indices` which uses `get_active_validator_indices` for the previous
epoch. By the lemma `prev_active_indices_fixed` we know that the set of active indices is equal to
the set of active indices that would have been computed from the `pre_state` at the start of epoch
processing (before any mutations were made). Further, the `previous_epoch_particiption` field used
to determine participation is only mutated as part of `process_participation_flag_updates`, which
happens *after* single-pass epoch processing and *after* `process_rewards_and_penalties`. Similarly,
the slashed status of each validator is immutable throughout all of epoch processing and does not
affect the result of `get_unslashed_participating_indices`. Therefore the participating indices used
by `get_flag_index_deltas` are equal to the indices used by `valid_progressive_balances` at the
start of epoch processing. Likewise the validator `effective_balance` field is immutable until
`process_effective_balance_updates` runs, and so the `unslashed_participating_balance` is equal to
the corresponding total balance from the
`progressive_balances.previous_epoch_flag_attesting_balances[flag_index]`.

Having established that the list of eligible indices and the total unslashed participating balance
are equal, it remains to show that the delta computed for each validator index is equal under both
approaches. In the spec's implementation, `get_base_reward(state, index)` and
`is_in_inactivity_leak(state)` are the two remaining inputs to the reward calculation. We know
that the `base_reward` value used in `get_flag_index_deltas` is equal to the `base_reward` used by
single-pass rewards processing which was computed at the start of epoch processing, by the lemma
`base_reward_fixed`. For `is_in_inactivity_leak`, we know that the value cached by single-pass epoch
processing is equal to the value used by `get_flag_index_deltas` by the lemma
`is_in_inactivity_leak_fixed` (both single-pass processing and `get_flag_index_deltas` execute after
`process_justification_and_finalization`).

TODO:

- similar argument for inactivity_penalties

Additionally, note that there is no data dependence between the values for different validator
indices, so it is equivalent to compute and apply all the deltas for validator index $i$
before computing any deltas for flag index $j$.

#### Supporting `call_db` analysis

```
> SELECT * FROM indirect_writes WHERE field = "previous_epoch_participation";
process_participation_flag_updates|previous_epoch_participation
```

```
> SELECT * FROM indirect_writes WHERE field = "validators.effective_balance";
process_effective_balance_updates|validators.effective_balance
```

```
> SELECT * FROM indirect_writes WHERE field = "validators.slashed";
# empty
```

### It is safe to reorder `process_slashings`

### It is safe to reorder `process_eth1_data_reset`

[consensus-specs]: https://github.com/ethereum/consensus-specs
[fc_pull_tips_disc]: https://notes.ethereum.org/@djrtwo/2023-fork-choice-reorg-disclosure
