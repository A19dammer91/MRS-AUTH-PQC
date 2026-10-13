(* ================================================================= *)
(*  MRS_DenyProof.ec                                                  *)
(*  Proof of the deniability theorem (replaces the last axiom).       *)
(*                                                                    *)
(*  Proof plan (MRSChain and MRSRep have no global state):            *)
(*    DenyGame ~ DenyAlt   : the adversary always gets ch0; the two   *)
(*                           chains are swapped when bit = 1.         *)
(*    DenyAlt  ~ DenyLate  : the challenge bit is sampled last.       *)
(*    Pr[DenyLate : res] = 1/2, because the bit is fair and           *)
(*                           independent of the guess.                *)
(*                                                                    *)
(*  Needs: islossless A.guess (otherwise the statement is false).     *)
(* ================================================================= *)

require import AllCore Bool Int IntDiv Real List Distr.
require import MRS_Core MRS_Distr MRS_Chain MRS_Deny.

(* ----------------------------------------------------------------- *)
(* A. Losslessness                                                    *)
(* ----------------------------------------------------------------- *)

lemma duniform_int_ll (n : int) : is_lossless (duniform_int n).
proof.
  rewrite /duniform_int.
  case (n < 0) => h.
  - by rewrite h /=; exact dunit_ll.
  - rewrite h /=.
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
(* B. Fairness of the bit against an arbitrary guess                  *)
(* ----------------------------------------------------------------- *)

lemma bit_half (g : bool) :
  Distr.mu (duniform_int 1) (fun (bit : int) => g = (bit = 1)) = 1%r / 2%r.
proof.
  have h1 := challenge_bit_uniform_one.
  rewrite /mu1 in h1.
  case g => hg.
  - have -> : (fun (bit : int) => g = (bit = 1)) = pred1 1.
      by apply fun_ext => x; rewrite /pred1 /=; smt().
    exact h1.
  - have -> : (fun (bit : int) => g = (bit = 1)) = predC (pred1 1).
      by apply fun_ext => x; rewrite /predC /pred1 /=; smt().
    rewrite mu_not.
    have hll := duniform_int_ll 1.
    rewrite /is_lossless /weight in hll.
    smt().
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

(* Step 3: with the bit last, the success probability is 1/2. *)
lemma late_half (A <: MRSAdversary) &m (N depth : int) (tri : int list) :
  islossless A.guess =>
  Pr[DenyLate(A).main(N, depth, tri) @ &m : res] = 1%r / 2%r.
proof.
  move=> hA.
  byphoare (_ : arg = (N, depth, tri) ==> res) => //.
  proc.
  seq 3 : true 1%r (1%r / 2%r) 0%r 0%r.
  - call hA. call build_ll. call build_ll. skip. smt().
  - wp. rnd (fun (bit : int) => g = (bit = 1)). skip. progress.
    + by apply bit_half.
  - hoare. skip. smt().
  - hoare. skip. smt().
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
  - by byequiv (deny_alt_equiv A).
  have -> :
    Pr[DenyAlt(A).main(N, depth, tri) @ &m : res]
    = Pr[DenyLate(A).main(N, depth, tri) @ &m : res].
  - by byequiv (deny_late_equiv A).
  exact (late_half A &m N depth tri hA).
qed.
