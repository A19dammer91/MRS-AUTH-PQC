(* ================================================================= *)
(*  MRS_DenyProof.ec                                                  *)
(*  Proof of the deniability theorem (replaces the last axiom).       *)
(*                                                                    *)
(*  Plan (MRSChain and MRSRep have no global state):                  *)
(*    DenyGame ~ DenyAlt  : adversary always gets ch0 (chains are     *)
(*                          swapped when bit = 1).                    *)
(*    DenyAlt  ~ DenyLate : the challenge bit is sampled last.        *)
(*    DenyLate ~ DenyLate : flipping the bit (x -> 1 - x) gives       *)
(*                          Pr[res] = Pr[!res]; with Pr[true] = 1     *)
(*                          this yields Pr[res] = 1/2.                *)
(*                                                                    *)
(*  Needs: islossless A.guess.                                        *)
(* ================================================================= *)

require import AllCore Bool Int IntDiv Real List Distr.
require import MRS_Core MRS_Distr MRS_Chain MRS_Deny.

(* ----------------------------------------------------------------- *)
(* A. Losslessness                                                    *)
(* ----------------------------------------------------------------- *)

lemma duniform_int_ll (n : int) : is_lossless (duniform_int n).
proof.
  case (n < 0) => h.
  - have -> : duniform_int n = dunit 0 by rewrite /duniform_int h /=.
    exact dunit_ll.
  - have -> : duniform_int n = Distr.duniform (range 0 (n + 1))
      by rewrite /duniform_int h /=.
    apply duniform_ll.
    smt(size_range size_eq0).
qed.

lemma sample_basic_ll : islossless MRSRep.sample_basic.
proof.
  proc. rnd. skip. smt(duniform_int_ll).
qed.

lemma sample_triangle_ll : islossless MRSRep.sample_triangle.
proof.
  proc. wp. rnd. wp. skip. smt(duniform_int_ll).
qed.

lemma build_ll : islossless MRSChain.build.
proof.
  proc.
  while (true) (depth - i).
  - move=> z.
    wp.
    if.
    + call sample_triangle_ll. skip. smt().
    + call sample_basic_ll. skip. smt().
  - wp. skip. smt().
qed.

lemma build_sim :
  equiv [MRSChain.build ~ MRSChain.build : ={arg} ==> ={res}].
proof. proc; sim. qed.

(* ----------------------------------------------------------------- *)
(* B. Support and symmetry of the challenge bit                       *)
(* ----------------------------------------------------------------- *)

lemma supp_duniform_int_1 (x : int) :
  x \in duniform_int 1 <=> (x = 0 \/ x = 1).
proof.
  rewrite /duniform_int ifF 1:/#.
  rewrite supp_duniform mem_range.
  smt().
qed.

lemma bit_mu1_symm (x : int) :
  x \in duniform_int 1 =>
  mu1 (duniform_int 1) x = mu1 (duniform_int 1) (1 - x).
proof.
  move=> /supp_duniform_int_1 [hx | hx].
  - by rewrite hx /= challenge_bit_uniform_zero challenge_bit_uniform_one.
  - by rewrite hx /= challenge_bit_uniform_zero challenge_bit_uniform_one.
qed.

(* ----------------------------------------------------------------- *)
(* C. Intermediate games                                              *)
(* ----------------------------------------------------------------- *)

module DenyAlt (A : MRSAdversary) = {
  proc main(N depth : int, tri : int list) : bool = {
    var bit : int;
    var ch0, ch1 : int list;
    var g : bool;

    bit <$ duniform_int 1;
    ch0 <@ MRSChain.build(N, depth, tri);
    ch1 <@ MRSChain.build(N, depth, tri);
    g <@ A.guess(ch0);

    return (g = (bit = 1));
  }
}.

module DenyLate (A : MRSAdversary) = {
  proc main(N depth : int, tri : int list) : bool = {
    var bit : int;
    var ch0, ch1 : int list;
    var g : bool;

    ch0 <@ MRSChain.build(N, depth, tri);
    ch1 <@ MRSChain.build(N, depth, tri);
    g <@ A.guess(ch0);
    bit <$ duniform_int 1;

    return (g = (bit = 1));
  }
}.

(* Step 1: the adversary always gets ch0 (chains swapped if bit = 1). *)
lemma deny_alt_equiv (A <: MRSAdversary) :
  equiv [DenyGame(A).main ~ DenyAlt(A).main :
    ={arg, glob A} ==> ={res}].
proof.
  proc.
  seq 1 1 : (={N, depth, tri, glob A, bit}).
  - by auto.
  swap{1} 1 2.
  case (bit{1} = 1).
  - swap{2} 1 1.
    seq 3 2 : (={glob A, bit} /\ bit{1} = 1 /\ b{1} = (bit{1} = 1)
               /\ ch1{1} = ch0{2}).
    + wp. call build_sim. call build_sim. skip. smt().
    wp. call (_ : true). wp. skip. smt().
  - seq 3 2 : (={glob A, bit} /\ !(bit{1} = 1) /\ b{1} = (bit{1} = 1)
               /\ ch0{1} = ch0{2}).
    + wp. call build_sim. call build_sim. skip. smt().
    wp. call (_ : true). wp. skip. smt().
qed.

(* Step 2: sample the bit last. *)
lemma deny_late_equiv (A <: MRSAdversary) :
  equiv [DenyAlt(A).main ~ DenyLate(A).main :
    ={arg, glob A} ==> ={res}].
proof.
  proc.
  swap{1} 1 3.
  sim.
qed.

(* Step 3: flipping the bit flips the result. *)
lemma late_flip (A <: MRSAdversary) :
  equiv [DenyLate(A).main ~ DenyLate(A).main :
    ={arg, glob A} ==> res{1} = !res{2}].
proof.
  proc.
  seq 3 3 : (={glob A, g}).
  - call (_ : true). call build_sim. call build_sim. skip. smt().
  wp.
  rnd (fun (x : int) => 1 - x) (fun (x : int) => 1 - x).
  skip.
  progress; smt(supp_duniform_int_1 bit_mu1_symm).
qed.

(* Step 4: Pr[true] = 1. *)
lemma late_ll (A <: MRSAdversary) &m (N depth : int) (tri : int list) :
  islossless A.guess =>
  Pr[DenyLate(A).main(N, depth, tri) @ &m : true] = 1%r.
proof.
  move=> hA.
  byphoare (_ : arg = (N, depth, tri) ==> true) => //.
  proc.
  wp. rnd. call hA. call build_ll. call build_ll. skip.
  smt(duniform_int_ll).
qed.

(* Step 5: Pr[res] = 1/2 for the late game. *)
lemma late_half (A <: MRSAdversary) &m (N depth : int) (tri : int list) :
  islossless A.guess =>
  Pr[DenyLate(A).main(N, depth, tri) @ &m : res] = 1%r / 2%r.
proof.
  move=> hA.
  have h1 :
    Pr[DenyLate(A).main(N, depth, tri) @ &m : res]
    = Pr[DenyLate(A).main(N, depth, tri) @ &m : !res].
  - byequiv (late_flip A); smt().
  have h2 :
    Pr[DenyLate(A).main(N, depth, tri) @ &m : !res]
    = 1%r - Pr[DenyLate(A).main(N, depth, tri) @ &m : res].
  - rewrite Pr[mu_not].
    rewrite (late_ll A &m N depth tri hA).
    done.
  smt().
qed.

(* ----------------------------------------------------------------- *)
(* D. The theorem                                                     *)
(* ----------------------------------------------------------------- *)

lemma deny_success_probability_proved
    (A <: MRSAdversary) &m (N depth : int) (tri : int list) :
  islossless A.guess =>
  Pr[DenyGame(A).main(N, depth, tri) @ &m : res] = 1%r / 2%r.
proof.
  move=> hA.
  have -> :
    Pr[DenyGame(A).main(N, depth, tri) @ &m : res]
    = Pr[DenyAlt(A).main(N, depth, tri) @ &m : res].
  - byequiv (deny_alt_equiv A); smt().
  have -> :
    Pr[DenyAlt(A).main(N, depth, tri) @ &m : res]
    = Pr[DenyLate(A).main(N, depth, tri) @ &m : res].
  - byequiv (deny_late_equiv A); smt().
  exact (late_half A &m N depth tri hA).
qed.
