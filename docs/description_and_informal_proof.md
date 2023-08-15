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

| Operation | Array-based | Tree-based |
|-----------|-------------|------------|
| index     | $O(1)$      | $O(log n)$ |
| iterate   | $O(n)$      | $O(c n)$   |

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

From these fundamental aggregate sums the finalization and justification aggregates are computed,
which also feed into later calculations. Conveniently, the aggregate sums can be computed _once_ at
the beginning of `process_epoch` and reused by all subsequent phases.

## Progressive Balances Cache

```python
get_total_balance(
    state,
    get_unslashed_participating_indices(state, TIMELY_TARGET_FLAG_INDEX, get_previous_epoch(state)),
)
```

## Activation Queue

TODO

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

## Informal Proof Sketch

### It is safe to cache the progressive balances

TODO

### It is safe to reorder `process_slashings`

### It is safe to reorder `process_eth1_data_reset`

[consensus-specs]: https://github.com/ethereum/consensus-specs
