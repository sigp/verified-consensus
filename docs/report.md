Verified Optimised Epoch Processing Final Report
===================================



This document describes the results achieved in the project to verify optimisations to the Epoch Processing pass.

## Outcomes

At the high level, we achieved the following


- Developed a verification framework in Isabelle/HOL that allowed the representation of Ethereum specifications in Separation Logic and Concurrent Refinement Algebra
- Translated a large portion of the python 'abstract spec' for Ethereum Epoch Processing into the Isabelle/HOL theorem prover.
- Translated the optimisations described in the project outline into Isabelle/HOL.
- Provided high-level abstract specifications for the python spec in terms of Separation Logic Hoare Triples
- Provided high-level abstract specifications for the optimised implementation in terms of Separation Logic Hoare Triples.

Additional outcomes not in-scope for the project goals include the development of a generic separation algebra for all data structures and a reasonable upper bound on the safety 
properties required for avoiding integer overflow and/or other numeric errors for epoch processing, as well as bounds on the range of configuration values that will avoid faults. 


We go into a bit more detail of each outcome below:

## The framework

In this project we developed a novel framework for representing abstract specifications in the Isabelle/HOL theorem prover. We shallowly-embed programs as 
monadic functions returning continuations in the CRA (concurrent refinement algebra) abstract type. That is, each program is automatically a specification of its own behaviour.  
This allows a high level of modularity - the monadic representation should be readable to any Haskell or Rust programmer (with some added sugar for mutation), while abstracting over the underlying representation in the refinement algebra.
 In turn, the algebra abstracts over the concrete comptuational model. 

For example, we abstract over the python sorting algorithm used in the specification through the non-determinism given by the algebra. Likewise, we abstract over allocation and deallocation of variables, 
though this could be adjusted for a memory-constrained context easily. 

The goal was that someone relatively unfamiliar with formal verification could read and write programs, and that we could freely change the underlying semantics of the syntax as needed. Similar to e.g. Dafny, the programmer can add in a contract in the form of pre- or post-conditions as part of the program definition, or specified independently as required. Due to our layers of abstraction, extending the translated specifications to a concurrent or parallel setting
would be relatively trivial in our framework.  We were also able to use existing Isabelle/HOL libraries, such as the machine-word formalisation. This gives a high level of assurance that we are capturing as much of the details of real code as is reasonable. 

## The translation

Using said framework, we translated all affected portions of the python abstract spec into our framework as well as the optimised implementation, which we believe we were able to do with a high degree of faithfulness to the python representation. 
The main difference is in the representation of loops, where we favour functional-style maps and folds over the imperative for/while. 

We have the following as an example:

```
 def get_inactivity_penalty_deltas(state: BeaconState) -> Tuple[Sequence[Gwei], Sequence[Gwei]]:
    """
    Return the inactivity penalty deltas by considering timely target participation flags and inactivity scores.
    """
    rewards = [Gwei(0) for _ in range(len(state.validators))]
    penalties = [Gwei(0) for _ in range(len(state.validators))]
    previous_epoch = get_previous_epoch(state)
    matching_target_indices = get_unslashed_participating_indices(state, TIMELY_TARGET_FLAG_INDEX, previous_epoch)
    for index in get_eligible_validator_indices(state):
        if index not in matching_target_indices:
            penalty_numerator = state.validators[index].effective_balance * state.inactivity_scores[index]
            penalty_denominator = INACTIVITY_SCORE_BIAS * INACTIVITY_PENALTY_QUOTIENT_BELLATRIX
            penalties[index] += Gwei(penalty_numerator // penalty_denominator)
    return rewards, penalties
```

and in Isabelle

```
"definition get_inactivity_penalty_deltas ::
  "(u64 list × u64 list, 'a) cont"
where
  "get_inactivity_penalty_deltas ≡ do {
    vs <- read validators;
    rewards   <- alloc (VariableList [0. _ <- [0..<length v]] );
    penalties <- alloc (VariableList [0. _ <- [0..<length v]]);
    previous_epoch <- get_previous_epoch;
    matching_target_indices <- get_unslashed_participating_indices TIMELY_TARGET_FLAG_INDEX previous_epoch;
    eligible_validator_indices <- get_eligible_validator_indices;
    vs <- read validators;
    scores <- read inactivity_scores; 
    _ <- (mapM (λindex. do {
      reward  <- mut (rewards[index]);
      penalty <- mut (penalties[index)];
      let index_nat = u64_to_nat index;
      when (index ∉ matching_target_indices) do {
        validator <- (vs[index]!);
        inactivity_score <- (scores[index]!);
        penalty_numerator <- effective_balance_f validator .* inactivity_score;
        penalty_denominator <- INACTIVITY_SCORE_BIAS config .* INACTIVITY_PENALTY_QUOTIENT_ALTAIR;
        new_penalty <- penalty_numerator \\ penalty_denominator;
        (penalty := penalty .+ new_penalty)}) 
        eligible_validator_indices);
    final_penalties <- read penalties;
    final_rewards   <- read rewards;
    free rewards;
    free penalties;
    return (final_rewards, final_penalties)
  }"
```
  
Although it is a tad more verbose, the expansion is mostly due to the requirement of each side-effect-causing invocation to be on its own line. This is in order to make the order and control of effects explicit.
  
One difficulty we found in the translation is that while as a whole Epoch Processing is represented as a pure function from state -> state, there is a fair amount of in-place mutation of individual fields 
in the python specification. This means care must be taken to translate the python reference semantics, and could introduce the potential for bugs in the future. 

## The specification

Although the optimised implementation is a refinement of sorts,  it is only a refinement when treating Epoch Processing as an atomic step. That means that only the end-to-end specifications refine each other. We give 
end-to-end specifications in the form of Hoare Triples, {pre} program {post}, in order to show that the python specification and the optimised implementation meet the specifications used in the paper proof. 

For example, we have 

```
{ λs. length vs < 2^64 ∧ 
      length is = length vs ∧
      safe_mul INACTIVITY_PENALTY_QUOTIENT_ALTAIR (INACTIVITY_SCORE_BIAS config) ∧ 
      INACTIVITY_SCORE_BIAS config * INACTIVITY_PENALTY_QUOTIENT_ALTAIR ≠ 0 ∧
      (∀i ∈ (list.set (eligible_validator_indices (previous_epoch (current_epoch bs)) 
                      (previous_epoch (current_epoch bs) + 1) vs)). 
                      safe_mul (is[i]) (effective_balance_f (vs[i]))) ∧
      previous_epoch (current_epoch bs) ≤ previous_epoch (current_epoch bs) + 1 ∧
      (validators ↦ vs * beacon_slots ↦ bs * previous_epoch_participation ↦ pep * 
       current_epoch_participation ↦ cep * inactivity_scores ↦ is *
       (inactivity_scores ↦ is * previous_epoch_participation ↦ pep * 
        current_epoch_participation ↦ cep * beacon_slots ↦ bs * validators ↦ vs -->* 
        P (map (λ_. 0) [0..<length vs],
           map (inactivity_penalty' vs bs is pep) [0..<length vs]))) s }
   get_inactivity_penalty_deltas
{ P }
```

for get_inactivity_penalty_deltas. The specification has a pure component, denoting the safety requirements for the command, and a spatial component in separation logic. The (*) syntax refers to separating conjunction, for the purposes of this report it simply means that we have a local specification, that can be used in a wider context.

All affected components were given Hoare Triples of this form, verifying that they match the specifications required for the paper proof, both in terms of the behaviour of the components given by the Hoare Triples
 and the independence of the passes given by the separation logic.
 
## Future Work

The bulk of the effort in this project was developing and designing the framework for the proofs, rather than the proofs themselves.

Sadly, some aspects of Epoch Processing have changed over the course of this project. Future work could update the correspondences involved in much smaller timeframes. We could also mechanise a larger portion of the overall proof, reducing the paper gap. Futhermore, we could expand the coverage to the entire python specification.

Other work could involve further optimisations. For example, a cursory examination of the passes in Epoch Processing reveal some clearly parallel computations currently run sequentially. As our framework supports concurrency, both via the algebra and the separation logic, verifying those low-hanging fruit is within reach. 


