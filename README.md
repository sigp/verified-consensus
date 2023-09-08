Verified optimised epoch processing
===================================

This repository contains a work-in-progress formalisation of Ethereum consensus in Isabelle/HOL.

The initial scope is a verified implementation of optimised epoch processing for Capella. Future
stages may pursue verification of block processing optimisations as well.

Presently, work is focussed on the algorithm description and proof sketch:

- [Algorithm Description and Proof Sketch](./docs/description_and_informal_proof.md).

This document is designed to be consumed by client implementers and researchers, and mirrors the
spec by sketching the algorithm in Python.

A supporting database for call-graph analysis is also included:

- [`call_db`: sqlite database of reads & writes](./call_db/README.md).

## Authors

- Michael Sproul (@michaelsproul), Sigma Prime
- Callum Bannister (@onomatic), Sigma Prime

We are thankful to the Ethereum Foundation for a grant supporting this work.
