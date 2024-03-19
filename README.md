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

- [`algebra`](./algebra): Separation logic algebra which is the base layer for the proofs.
- [`ProcessEpoch.thy`](./ProcessEpoch.thy): Translation of the Python spec to our continuation monad.

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
