(* ================================================================= *)
(*  MRS_General.ec                                                    *)
(*  Equivalence lemmas for the MRS samplers                           *)
(*                                                                    *)
(*  This file completes the module-level specification of             *)
(*  MRS_Core.ec by proving the reflexivity tests for the two          *)
(*  samplers `sample_basic` and `sample_triangle`.                    *)
(*                                                                    *)
(*  These are equivalence tests: the same procedure is compared to    *)
(*  itself. They are of limited practical value but complete the      *)
(*  module-level specification.                                       *)
(*                                                                    *)
(*  Axiom baseline: 0. NO admits.                                     *)
(* ================================================================= *)

require import AllCore Int IntDiv Real List.
require import MRS_Distr.
require import MRS_Core.

(* ================================================================= *)
(* Section 1: Equivalence of sample_basic with itself                 *)
(*                                                                    *)
(* The proof uses the safe pattern:                                   *)
(*   - `proc.` to enter both procedures                               *)
(*   - `seq 1 1 : (={kvl}).` to align the sampling step               *)
(*   - `rnd.` to discharge the sampling (identical distributions)     *)
(*   - `skip => /=.` to reduce the return step                        *)
(*   - `move=> &1 &2 H.` to introduce the memories and the            *)
(*     hypothesis that the sampling results match                     *)
(*   - `by []` to close the sampling branch                           *)
(*   - `smt()` to close the return branch (tuple equality from H)     *)
(* ================================================================= *)

lemma sample_basic_equiv (N : int) :
  162 < N =>
  equiv [MRSRep.sample_basic ~ MRSRep.sample_basic : ={arg} ==> ={res}].
proof.
  move=> hN.
  proc.
  seq 1 1 : (={kvl}).
  - rnd.
    skip => /=.
    move=> &1 &2 H.
    by [].
  - skip => /=.
    move=> &1 &2 H.
    smt().
qed.

(* ================================================================= *)
(* Section 2: Equivalence of sample_triangle with itself              *)
(*                                                                    *)
(* Same pattern as sample_basic_equiv, but with two extra             *)
(* sequencing steps to handle the deterministic assignments before    *)
(* and after the sampling.                                            *)
(* ================================================================= *)

lemma sample_triangle_equiv (N : int) :
  162 < N =>
  equiv [MRSRep.sample_triangle ~ MRSRep.sample_triangle : ={arg} ==> ={res}].
proof.
  move=> hN.
  proc.
  seq 4 4 : (={anc, bcp, kbn, tmx}).
  - auto.
  seq 1 1 : (={ndx, anc, bcp, kbn, tmx}).
  - rnd.
    skip => /=.
    move=> &1 &2 H.
    by [].
  - seq 1 1 : (={kvl, ndx, anc, bcp, kbn, tmx}).
    + auto.
    + skip => /=.
      move=> &1 &2 H.
      smt().
qed.

(* ================================================================= *)
(* End of MRS_General.ec                                              *)
(* ================================================================= *)
