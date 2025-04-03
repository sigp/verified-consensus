Verified optimised epoch processing
===================================

This repository contains a work-in-progress formalisation of Ethereum consensus in Isabelle/HOL.

The scope is a verified implementation of optimised epoch processing for Capella. Future
stages may pursue verification of block processing optimisations as well.

There is a complete description of the algorithm with sketches of the proofs here:

- [Algorithm Description and Proof Sketch](./docs/description_and_informal_proof.md).

The algorithm description is designed to be consumed by client implementers and
researchers, and mirrors the spec by implementing the algorithm in Python.

We are now in the process of formalising the proofs in Isabelle/HOL:

- [`Word_Lib`](./Word_Lib): Library for machine words. 
- [`algebra`](./algebra): Rely-guarantee algebra and trace model instantantiation, the former gives the semantic meaning to our verification and the latter is simply a instance for consistency checking.
- [`jormungand`)(./jormungand): Separation Logic algebra and mechanisation, including proof tactics. Adapted from previous work by the authors.
- [`Cont_Monad_Algebra.thy`](./Cont_Monad_Algebra.thy): Formalisation of the continuation monad with some added syntactic sugar for imperative state updates.
- [`Lens.thy`])(./Lens.thy): Formalisation of lenses, used for representation of the state and abstract model for separation algebra.
- [`Fun_Algebra.thy`](./Fun_Algebra.thy): Generic separation algebra based on pointed sets of endofunctions. 
- [`Sep_Logic_Incomplete.thy`](./Sep_Logic_Incomplete.thy): Contains as assumptions aspects of the formalisation due to be mechanised fully at a later date. 
- [`Hoare_Logic.thy`](./Hoare_Logic.thy): Formalisation of Hoare Logic as inequalities in the rely-guarantee algebra.
- [`Hoare_VCG.thy`](./Hoare_VCG.thy): Hoare triples for generic program constructs. 
- [`Types.thy`](./Types.thy): Choice of representation types for the Python spec.
- [`Unsigned.thy`](./Unsigned.thy): Formalisation of all unsigned operations on machine words/epochs etc. 
- [`Config.thy`](./Config.thy): Abstract model of all possible configuration options for Epoch Processing
- [`VerifiedConsensus.thy`](./VerifiedConsensus.thy): Brings together the formalisation of python with our algebra. 
- [`sqrt_proof.thy`](./sqrt_proof.thy): Proof of correctness of the integer square root algorithm used in the Python spec.
- [`ProcessEpoch.thy`](./ProcessEpoch.thy): Translation of the Python spec to our continuation monad.
- [`ProcessEpoch_O.thy`](./ProcessEpoch_O.thy): Translation of the optimised spec to our continuation monad.
- [`Process_Epoch_O_Specs.thy`](./Process_Epoch_O_Specs.thy): Proofs of functional correctness of the python and optimised specifications

## Call DB

While developing the algorithm and mapping out the proofs we created a small database for call-graph
analysis, focussing on reads and writes of `BeaconState` fields. Our hope is that it may be useful
for other projects, or that a similar approach could be applied in future work on fork choice/block
processing.

- [`call_db`: sqlite database of reads & writes](./call_db/README.md).

## Implementations

- [Lighthouse][lighthouse_impl]: The Lighthouse `tree-states` branch uses a closely-related variant
  of the optimised epoch processing algorithm. It is presently undergoing differential fuzzing.

## Authors

- Callum Bannister ([@onomatic][]), Sigma Prime
- Michael Sproul ([@michaelsproul][]), Sigma Prime

We are grateful to the Ethereum Foundation for a grant supporting this work.




[@onomatic]: https://github.com/onomatic
[@michaelsproul]: https://github.com/michaelsproul
[lighthouse_impl]: https://github.com/sigp/lighthouse/blob/tree-states/consensus/state_processing/src/per_epoch_processing/single_pass.rs
