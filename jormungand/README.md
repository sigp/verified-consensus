[![Build Status](https://travis-ci.org/SEL4PROJ/jormungand.svg?branch=master)](https://travis-ci.org/SEL4PROJ/jormungand)

This repository contains the supporting Isabelle/HOL theories
for the paper "Backwards and Forwards with Separation Logic".

Hoare_Sep_Tactics/ contains the main relevant theory files, they are

 * Det_Monad, the formalisation of a deterministic state monad with failure (Section 2)
 * Hoare_Sep_Tactics, the currently in-use weakest-precondition separation logic method (Section 5)
 * Extended_Separation_Algebra, which contains theories about septraction, separating coimplication and theorems relating the two (Section 4),
 * SP, which contains the strongest-postcondition method (Section 6),
 * Sep_SP, which contains the strongest-postcondition separation logics (Section 6),
 * Sep_Forward, which contains the simplifier for septraction and separating coimplication, and
 * Simple_Separation_Example, which contains the examples of weakest preconditions and strongest postconditions from the paper (Sections 5 and 6)

case_study/ contains a copy of the l4v project, of interest to the paper are
* proof/capDL-api/*, which contains a portion of the system initialisation proofs (Section 5)
* proof/capDL-api/KHeap_Forward_DP, which contains the use of the forward reasoning framework on
  a portion of the system initialisation proofs (Section 6), and
* sys-init/* which contains the remainder of the system initialisation proofs (Section 5)

The theories compile with Isabelle2016-1:

    export L4V_ARCH=ARM
    isabelle build -v -D .
