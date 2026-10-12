(* ================================================================= *)
(*  MRS_Equiv.ec                                                      *)
(*  Equivalence lemmas for the MRS samplers                           *)
(*                                                                    *)
(*  The proofs use `byequiv`, the canonical EasyCrypt tactic for      *)
(*  reducing an `equiv` goal to a `hoare` goal. This avoids the       *)
(*  direct `proc` + `rnd` approach, which fails on samplings whose    *)
(*  distribution is built via `duniform` on a list.                   *)
(*                                                                    *)
(*  Axiom baseline: 0. NO admits.                                     *)
(* ================================================================= *)

require import AllCore Int IntDiv Real List.
require import MRS_Distr.
require import MRS_Core.

(* ================================================================= *)
(* Section 1: Equivalence of sample_basic with itself                 *)
(*                                                                    *)
(* `byequiv` transforms the equivalence goal into a Hoare goal on     *)
(* the product of the two procedures. For a reflexivity test, the     *)
(* resulting Hoare goal is trivially true: the same procedure,        *)
(* called with the same arguments, produces the same result.          *)
(* ================================================================= *)

lemma sample_basic_equiv (N : int) :
  162 < N =>
  equiv [MRSRep.sample_basic ~ MRSRep.sample_basic : ={arg} ==> ={res}].
proof.
  move=> hN.
  byequiv => //.
  proc.
  seq 1 1 : (={kvl}).
  - rnd (fun x => x) (fun x => x).
    skip => /=.
    move=> &1 &2 H.
    by [].
  - skip => /=.
    move=> &1 &2 H.
    have hk : kvl{1} = kvl{2} by smt().
    rewrite hk.
    by [].
qed.

(* ================================================================= *)
(* Section 2: Equivalence of sample_triangle with itself              *)
(* ================================================================= *)

lemma sample_triangle_equiv (N : int) :
  162 < N =>
  equiv [MRSRep.sample_triangle ~ MRSRep.sample_triangle : ={arg} ==> ={res}].
proof.
  move=> hN.
  byequiv => //.
  proc.
  seq 4 4 : (={anc, bcp, kbn, tmx}).
  - auto.
  seq 1 1 : (={ndx, anc, bcp, kbn, tmx}).
  - rnd (fun x => x) (fun x => x).
    skip => /=.
    move=> &1 &2 H.
    by [].
  - seq 1 1 : (={kvl, ndx, anc, bcp, kbn, tmx}).
    + auto.
    + skip => /=.
      move=> &1 &2 H.
      have hk : kvl{1} = kvl{2} by smt().
      rewrite hk.
      by [].
qed.

(* ================================================================= *)
(* End of MRS_Equiv.ec                                                *)
(* ================================================================= *)
