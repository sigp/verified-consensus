Verified optimised epoch processing
===================================

Implementations of the Ethereum [consensus specification][consensus-specs] typically make use of
algorithmic optimisations to achieve high performance. The correctness of these optimisations is
critical to Ethereum's security, and so far they have been checked by manual review, testing and
fuzzing. To further increase assurance we propose to formally prove correctness of an optimised
implementation.

This document describes the optimised implementation which we are in the process of verifying,
and includes a high-level argument for its correctness.

## Motivation and Scope

We only consider the `process_epoch` function which. Block processing (`process_block`) is
considered out of scope for now but may be covered by future work.

Our goal is to verify an implementation of `process_epoch` containing the minimum number of `O(n)`
iterations over the validator set, where `n` is the number of validators.

## Algorithm Description

## Informal Proof Sketch

[consensus-specs]: https://github.com/ethereum/consensus-specs
