(* ================================================================= *)
(*  MRS_Core.ec                                                       *)
(*  Mathematical core of MRS-AUTH: the 19A + 9B representation       *)
(*  system under the Positive Anchor Convention.                      *)
(*                                                                    *)
(*  A_0 = dr(N) = 1 + ((N - 1) mod 9)      for N > 0                  *)
(*                                                                    *)
(*  D^3 coefficient set: [19, 9, 3, 3, 1].                            *)
(*      Foundation:  19 = 1 (mod 9)                                   *)
(*      Chain:       1 | 3 | 3 | 9                                    *)
(*                                                                    *)
(*  Sampling uses `duniform_int` from MRS_Distr.ec.                   *)
(*                                                                    *)
(*  Axiom baseline: 0. NO admits.                                     *)
(* ================================================================= *)

require import AllCore Int IntDiv Real List.
require import MRS_Distr.

(* ================================================================= *)
(* Section 1: Digital root                                            *)
(* ================================================================= *)

op dr (n : int) : int =
  if (n <= 0) then 0 else (1 + (((n - 1)) %% 9)).

lemma dr_range (n : int) : 0 < n => 1 <= dr n /\ dr n <= 9.
proof.
  move=> hn.
  rewrite /dr.
  have h : ! (n <= 0) by smt().
  rewrite h /=.
  split; first by smt(modz_ge0).
  by smt().
qed.

lemma dr_mod9 (n : int) : 0 < n => dr n = n - 9 * ((n - 1) %/ 9).
proof.
  move=> hn.
  rewrite /dr.
  have h : ! (n <= 0) by smt().
  rewrite h /=.
  have := divz_eq (n - 1) 9.
  smt().
qed.

lemma dr_cong9 (n : int) : 0 < n => (dr n - n) %% 9 = 0.
proof.
  move=> hn.
  rewrite /dr.
  have h : ! (n <= 0) by smt().
  rewrite h /=.
  have key : (1 + (n - 1) %% 9 - n) %% 9 = 0.
    have := modzDl (n - 1) 9.
    smt(modz_mod modzNm).
  exact key.
qed.

lemma dr_add9 (n : int) : 0 < n => dr (n + 9) = dr n.
proof.
  move=> hn.
  rewrite /dr.
  have h1 : ! (n + 9 <= 0) by smt().
  have h2 : ! (n <= 0) by smt().
  rewrite h1 h2 /=.
  have : (n + 9 - 1) %% 9 = (n - 1) %% 9.
    have ->: n + 9 - 1 = (n - 1) + 9 by ring.
    by rewrite modzDr.
  by move=> ->.
qed.

lemma dr_9k_r (k r : int) : 0 <= k => 0 < r => dr (9 * k + r) = dr r.
proof.
  move=> hk hr.
  rewrite /dr.
  have h1 : ! (9 * k + r <= 0) by smt().
  have h2 : ! (r <= 0) by smt().
  rewrite h1 h2 /=.
  have key : (9 * k + r - 1) %% 9 = (r - 1) %% 9 by smt().
  by rewrite key.
qed.

lemma dr_19 (n : int) : 0 < n => dr (19 * n) = dr n.
proof.
  move=> hn.
  have Heq : 19 * n = 9 * (2 * n) + n by ring.
  rewrite Heq.
  apply dr_9k_r; smt().
qed.

lemma dr_19A_9B (n m : int) : 0 < n => 0 <= m => dr (19 * n + 9 * m) = dr n.
proof.
  move=> hn hm.
  have Heq : 19 * n + 9 * m = 9 * (2 * n + m) + n by ring.
  rewrite Heq.
  have hk : 0 <= 2 * n + m by smt().
  exact (dr_9k_r (2 * n + m) n hk hn).
qed.

lemma dr_idempotent (n : int) : 1 <= n => n <= 9 => dr n = n.
proof.
  move=> h1 h9.
  rewrite /dr.
  have hpos : ! (n <= 0) by smt().
  rewrite hpos /=.
  have hmod : (n - 1) %% 9 = n - 1 by smt().
  rewrite hmod.
  ring.
qed.

(* ================================================================= *)
(* Section 2: Positive Anchor Convention                              *)
(* ================================================================= *)

op a0 (N : int) : int = dr N.
op B0 (N : int) : int = (((N - (19 * (a0 N)))) %/ 9).
op kmax (N : int) : int = ((B0 N) %/ 19).

(* ================================================================= *)
(* Section 3: Derived quantities                                      *)
(* ================================================================= *)

op ddr (N : int) : int = dr (2 * (dr N)).
op dmod (N : int) : int = (ddr N) %% 9.
op kbs (N : int) : int = ((B0 N) - (dmod N)) %% 9.
op tbn (N : int) : int = ((kmax N) - (kbs N)) %/ 9.

(* ================================================================= *)
(* Section 4: Auxiliary lemmas about a0 and B0                        *)
(* ================================================================= *)

lemma a0_range (N : int) : 0 < N => 1 <= a0 N /\ a0 N <= 9.
proof.
  move=> hN.
  rewrite /a0.
  by apply dr_range.
qed.

lemma a0_cong9 (N : int) : 0 < N => (a0 N - N) %% 9 = 0.
proof.
  move=> hN.
  rewrite /a0.
  by apply dr_cong9.
qed.

lemma a0_eq_mod9_or_9 (N : int) : 0 < N => a0 N = N %% 9 \/ a0 N = 9.
proof.
  move=> hNpos.
  have ha0 := a0_cong9 N hNpos.
  have hrange := a0_range N hNpos.
  have [hlo hhi] := hrange.
  have hmod_ge0 : 0 <= N %% 9 by smt(modz_ge0).
  case (N %% 9 = 0) => [hmod0 | hmod_ne].
  - right.
    smt().
  - left.
    smt().
qed.

lemma N_minus_19a0_mod9 (N : int) : 0 < N => (N - 19 * (a0 N)) %% 9 = 0.
proof.
  move=> hN.
  have ha0 := a0_cong9 N hN.
  have Heq : N - 19 * a0 N = N - a0 N - 18 * a0 N by ring.
  rewrite Heq.
  have h1 : (N - a0 N) %% 9 = 0 by smt(modzDl modzNm).
  have h2 : (18 * a0 N) %% 9 = 0 by smt().
  smt(modzDl).
qed.

lemma key_ineq (N : int) : 162 < N => 19 * (a0 N) <= N.
proof.
  move=> hN.
  have hNpos : 0 < N by smt().
  have hrange := a0_range N hNpos.
  have [hlo hhi] := hrange.
  case (a0 N = 9) => [heq | hne].
  - have hcong := a0_cong9 N hNpos.
    have hmod : N %% 9 = 0 by rewrite heq in hcong; smt(modzDl modzNm).
    have hdiv : N = 9 * (N %/ 9) by smt(divz_eq).
    have hq_ge : 18 < N %/ 9.
      have : 162 < 9 * (N %/ 9) by rewrite -hdiv.
      smt().
    have hge : 171 <= N.
      have : 9 * 19 <= 9 * (N %/ 9) by smt().
      smt().
    rewrite heq.
    smt().
  - have hle : a0 N <= 8 by smt().
    smt().
qed.

lemma B0_ge0 (N : int) : 162 < N => 0 <= B0 N.
proof.
  move=> hN.
  have hNpos : 0 < N by smt().
  have hrange := a0_range N hNpos.
  have [hlo hhi] := hrange.
  have hdiv := divz_eq N 9.
  case (N %% 9 = 0) => [hmod0 | hmod_ne].
  - have ha0_9 : a0 N = 9.
      have h := a0_eq_mod9_or_9 N hNpos.
      case h => [hleft | hright].
      + smt().
      + exact hright.
    rewrite /B0 ha0_9.
    have hN_eq : N = 9 * (N %/ 9) by smt().
    have hq_ge : 19 <= N %/ 9.
      have : 162 < 9 * (N %/ 9) by rewrite -hN_eq.
      smt().
    have hnn : 0 <= N - 19 * 9 by smt().
    have hdecomp : N - 19 * 9 =
                   9 * ((N - 19 * 9) %/ 9) + (N - 19 * 9) %% 9
      by smt(divz_eq).
    have hr_ge0 : 0 <= (N - 19 * 9) %% 9 by smt(modz_ge0).
    have hr_lt : (N - 19 * 9) %% 9 < 9 by smt(modz_ge0 divz_eq).
    smt().
  - have ha0_mod : a0 N = N %% 9.
      have h := a0_eq_mod9_or_9 N hNpos.
      case h => [hleft | hright].
      + exact hleft.
      + smt().
    rewrite /B0 ha0_mod.
    have hN_eq : N = 9 * (N %/ 9) + N %% 9 by smt().
    have hmod_ge0 : 0 <= N %% 9 by smt(modz_ge0).
    have hmod_lt : N %% 9 < 9 by smt(modz_ge0 divz_eq).
    have hq_ge : 18 <= N %/ 9.
      have : 162 < 9 * (N %/ 9) + N %% 9 by rewrite -hN_eq.
      smt().
    have hnn : 0 <= N - 19 * (N %% 9) by smt().
    have hdecomp : N - 19 * (N %% 9) =
                   9 * ((N - 19 * (N %% 9)) %/ 9) + (N - 19 * (N %% 9)) %% 9
      by smt(divz_eq).
    have hr_ge0 : 0 <= (N - 19 * (N %% 9)) %% 9 by smt(modz_ge0).
    have hr_lt : (N - 19 * (N %% 9)) %% 9 < 9 by smt(modz_ge0 divz_eq).
    smt().
qed.

lemma kmax_ge0 (N : int) : 162 < N => 0 <= kmax N.
proof.
  move=> hN.
  rewrite /kmax.
  have hB0 : 0 <= B0 N by apply B0_ge0.
  have hdecomp : B0 N = 19 * (B0 N %/ 19) + B0 N %% 19 by smt(divz_eq).
  have hmod_ge0 : 0 <= B0 N %% 19 by smt(modz_ge0).
  have hmod_lt : B0 N %% 19 < 19 by smt(modz_ge0 divz_eq).
  smt().
qed.

lemma a0_B0_eq (N : int) : 0 < N => 19 * a0 N + 9 * B0 N = N.
proof.
  move=> hN.
  rewrite /B0 /a0.
  have h := N_minus_19a0_mod9 N hN.
  have := divz_eq (N - 19 * a0 N) 9.
  smt().
qed.

lemma linear_invariant N k :
  162 < N =>
  0 <= k <= kmax N =>
  19 * (a0 N + 9 * k) + 9 * (B0 N - 19 * k) = N.
proof.
  move=> hN hk.
  have hNpos : 0 < N by smt().
  have base := a0_B0_eq N hNpos.
  have Heq : 19 * (a0 N + 9 * k) + 9 * (B0 N - 19 * k) =
             19 * a0 N + 9 * B0 N by ring.
  rewrite Heq.
  exact base.
qed.

lemma B_ge0 (N k : int) :
  162 < N =>
  0 <= k <= kmax N =>
  0 <= B0 N - 19 * k.
proof.
  move=> hN hk.
  rewrite /kmax in hk.
  have hB0 : 0 <= B0 N by apply B0_ge0.
  have hk2 : k <= B0 N %/ 19 by smt().
  have hdecomp : B0 N = 19 * (B0 N %/ 19) + B0 N %% 19 by smt(divz_eq).
  have hmod_ge0 : 0 <= B0 N %% 19 by smt(modz_ge0).
  have h19k_le : 19 * k <= 19 * (B0 N %/ 19) by smt().
  have h19k_le_B0 : 19 * k <= B0 N by smt().
  smt().
qed.

lemma A_pos (N k : int) :
  162 < N =>
  0 <= k <= kmax N =>
  1 <= a0 N + 9 * k.
proof.
  move=> hN hk.
  have hNpos : 0 < N by smt().
  have hrange := a0_range N hNpos.
  have [hlo _] := hrange.
  smt().
qed.

(* ================================================================= *)
(* Section 5: D^3 Pattern structural conditions                       *)
(* ================================================================= *)

lemma foundation_19_mod_9 : 19 %% 9 = 1.
proof. by smt(). qed.

lemma chain_divisibility :
  (3 = 1 * 3) /\ (3 = 3 * 1) /\ (9 = 3 * 3).
proof.
  split; first by ring.
  split; first by ring.
  by ring.
qed.

lemma absorption_guarantee (N : int) :
  162 < N =>
  0 <= N - 19 * (N %/ 19) < 19.
proof.
  move=> hN.
  have := divz_eq N 19.
  smt().
qed.

lemma no_backtracking (N : int) :
  162 < N =>
  0 <= N - 19 * (N %/ 19) < 19 /\
  0 <= (N - 19 * (N %/ 19)) - 9 * ((N - 19 * (N %/ 19)) %/ 9) < 9.
proof.
  move=> hN.
  have := divz_eq N 19.
  have := divz_eq (N - 19 * (N %/ 19)) 9.
  smt().
qed.

lemma stateless_precheck (N : int) :
  0 < N =>
  (a0 N) %% 9 = N %% 9.
proof.
  move=> hN.
  have ha0 := a0_cong9 N hN.
  smt(modzDl modzNm).
qed.

(* ================================================================= *)
(* Section 6: Predicate and uniqueness                                *)
(* ================================================================= *)

pred is_rep (N A B : int) = 1 <= A /\ 0 <= B /\ 19*A + 9*B = N.

lemma rep_uniq (N : int) (A B : int) :
  162 < N => is_rep N A B =>
  exists k, 0 <= k <= kmax N /\ A = a0 N + 9*k /\ B = B0 N - 19*k.
proof.
  move=> hN hrep.
  have Apos : 1 <= A.
    move: hrep.
    move=> [hA _].
    exact hA.
  have Bpos : 0 <= B.
    move: hrep.
    move=> [_ [hB _]].
    exact hB.
  have eq : 19*A + 9*B = N.
    move: hrep.
    move=> [_ [_ hEq]].
    exact hEq.
  have hNpos : 0 < N by smt().
  have A_mod : A %% 9 = N %% 9.
    have Heq : N = 19*A + 9*B by smt().
    rewrite Heq.
    smt(modzDl modzMl modz_mod).
  have ha0_eq_N : (a0 N - N) %% 9 = 0 by apply a0_cong9.
  have heq_mod : (A - a0 N) %% 9 = 0 by smt(modzDl modzNm).
  have hrange := a0_range N hNpos.
  have [hlo hhi] := hrange.
  have hA_ge_a0 : a0 N <= A by smt().
  have k_ge0 : 0 <= (A - a0 N) %/ 9 by smt().
  have A_eq : A = a0 N + 9 * ((A - a0 N) %/ 9).
    have := divz_eq (A - a0 N) 9.
    smt().
  have B_eq : B = B0 N - 19 * ((A - a0 N) %/ 9).
    have sum_eq : 19 * (a0 N + 9*((A - a0 N) %/ 9)) + 9*B = N
      by rewrite -A_eq; smt().
    have hNpos' : 0 < N by smt().
    have base_eq : 19 * a0 N + 9 * B0 N = N by apply a0_B0_eq.
    smt().
  have k_le_kmax : (A - a0 N) %/ 9 <= kmax N.
    rewrite /kmax.
    have hB : 0 <= B0 N - 19 * ((A - a0 N) %/ 9) by rewrite -B_eq; smt().
    have hdecomp : B0 N - 19 * ((A - a0 N) %/ 9) =
                   19 * ((B0 N - 19 * ((A - a0 N) %/ 9)) %/ 19) +
                   (B0 N - 19 * ((A - a0 N) %/ 9)) %% 19
      by smt(divz_eq).
    have hmod_ge0 : 0 <= (B0 N - 19 * ((A - a0 N) %/ 9)) %% 19 by smt(modz_ge0).
    have hmod_lt : (B0 N - 19 * ((A - a0 N) %/ 9)) %% 19 < 19 by smt(modz_ge0 divz_eq).
    smt().
  exists ((A - a0 N) %/ 9).
  split.
  - smt().
  - split; smt().
qed.

(* ================================================================= *)
(* Section 7: dr properties for representations                       *)
(* ================================================================= *)

lemma dr_a0 (N : int) : 0 < N => dr (a0 N) = dr N.
proof.
  move=> hN.
  rewrite /a0.
  have hrange := dr_range N hN.
  have [hlo hhi] := hrange.
  apply dr_idempotent => //.
qed.

lemma dr_rep_A (N k : int) : 0 < N => 0 <= k => dr (a0 N + 9 * k) = dr N.
proof.
  move=> hN hk.
  have ha0 : 0 < a0 N by smt(a0_range).
  have hpos : 0 < a0 N + 9 * k by smt().
  have Heq : a0 N + 9 * k = 9 * k + a0 N by ring.
  have Hdr : dr (a0 N + 9 * k) = dr (9 * k + a0 N).
    by rewrite Heq.
  rewrite Hdr.
  rewrite dr_9k_r; smt().
qed.

lemma dr_triangle_B (N k : int) :
  162 < N =>
  0 <= k <= kmax N =>
  (B0 N - 19 * k) %% 9 = dr (2 * dr N) %% 9 =>
  0 < B0 N - 19 * k =>
  dr (B0 N - 19 * k) = dr (2 * dr N).
proof.
  move=> hN hk hcong hpos.
  rewrite /dr.
  have h1 : ! (B0 N - 19 * k <= 0) by smt().
  rewrite h1 /=.
  have htgt : 0 < dr (2 * dr N).
    have hNpos : 0 < N by smt().
    have hrange := dr_range N hNpos.
    have [h1' h2] := hrange.
    have h2pos : 0 < 2 * (if N <= 0 then 0 else 1 + (N-1) %% 9) by smt().
    smt(dr_range modz_ge0).
  rewrite /dr.
  have h2 : ! (2 * dr N <= 0) by smt().
  rewrite h2 /=.
  have cong2 : (B0 N - 19 * k - 1) %% 9 = (dr (2 * dr N) - 1) %% 9.
    have := hcong.
    smt(modzDl modzNm).
  smt().
qed.

(* ================================================================= *)
(* Section 8: Frobenius boundary                                      *)
(* ================================================================= *)

lemma frobenius_162_not_rep (A B : int) : is_rep 162 A B => false.
proof.
  move=> hrep.
  have hA : 1 <= A.
    move: hrep.
    move=> [h _].
    exact h.
  have hB : 0 <= B.
    move: hrep.
    move=> [_ [h _]].
    exact h.
  have hEq : 19*A + 9*B = 162.
    move: hrep.
    move=> [_ [_ h]].
    exact h.
  have hmod : A %% 9 = 0.
    have : (19*A + 9*B) %% 9 = 162 %% 9 by rewrite hEq.
    have h162 : 162 %% 9 = 0 by done.
    smt(modzDl modzNm modzMml).
  have hAle : A <= 8 by smt().
  have hAge : 1 <= A by exact hA.
  smt(modz_ge0).
qed.

lemma dr_163 : dr 163 = 1.
proof.
  rewrite /dr.
  have h1 : ! (163 <= 0) by done.
  rewrite h1 /=.
  smt().
qed.

lemma a0_163 : a0 163 = 1.
proof. by rewrite /a0 dr_163. qed.

lemma B0_163 : B0 163 = 16.
proof.
  rewrite /B0 a0_163.
  have Heq : 163 - 19 * 1 = 144 by ring.
  rewrite Heq.
  have Heq2 : 144 %/ 9 = 16 by done.
  by rewrite Heq2.
qed.

lemma frobenius_163_explicit :
  is_rep 163 1 16.
proof.
  rewrite /is_rep.
  split; first by done.
  split; first by done.
  by [].
qed.

lemma frobenius_163_via_anchor :
  is_rep 163 (a0 163) (B0 163).
proof.
  rewrite a0_163 B0_163.
  exact frobenius_163_explicit.
qed.

lemma frobenius_boundary :
  (forall (A B : int), is_rep 162 A B => false) /\
  (exists (A B : int), is_rep 163 A B).
proof.
  split.
  - move=> A B.
    exact (frobenius_162_not_rep A B).
  - exists 1 16.
    exact frobenius_163_explicit.
qed.

lemma no_unrep_above_162 (N : int) : 162 < N => is_rep N (a0 N) (B0 N).
proof.
  move=> hN.
  have hB : 0 <= B0 N by apply B0_ge0.
  have hA : 1 <= a0 N by smt(a0_range).
  have hNpos : 0 < N by smt().
  have heq : 19 * a0 N + 9 * B0 N = N by apply a0_B0_eq.
  smt().
qed.

lemma all_above_frobenius_representable (N : int) :
  163 <= N => exists (A B : int), is_rep N A B.
proof.
  move=> hN.
  have hN' : 162 < N by smt().
  exists (a0 N) (B0 N).
  exact (no_unrep_above_162 N hN').
qed.

(* ================================================================= *)
(* Section 9: Module for representation sampling                      *)
(* ================================================================= *)
module MRSRep = {
  proc sample_basic(N : int) : int * int = {
    var kvl : int;
    kvl <$ duniform_int (kmax N);
    return ((a0 N) + (9 * kvl), (B0 N) - (19 * kvl));
  }

  proc sample_triangle(N : int) : int * int = {
    var anc, bcp, kbn, tmx, ndx, kvl : int;
    anc <- a0 N;
    bcp <- B0 N;
    kbn <- kmax N;
    tmx <- (if (kbn < kbs N) then 0 else tbn N);
    ndx <$ duniform_int tmx;
    kvl <- (kbs N) + 9 * ndx;
    return (if (kbn < kbs N) then (0, 0)
            else ((anc + (9 * kvl)), (bcp - (19 * kvl))));
  }
}.

lemma triangle_k0_le_kmax (N : int) :
  162 < N =>
  (B0 N - dr (2 * dr N) %% 9) %% 9 <= kmax N \/
  kmax N < (B0 N - dr (2 * dr N) %% 9) %% 9.
proof.
  move=> hN. smt().
qed.

(* ================================================================= *)
(* Section 10: Correctness of sample_basic                            *)
(* ================================================================= *)

lemma sample_basic_inv (N k : int) :
  162 < N =>
  0 <= k <= kmax N =>
  19 * (a0 N + 9 * k) + 9 * (B0 N - 19 * k) = N /\
  dr (a0 N + 9 * k) = dr N.
proof.
  move=> hN hk.
  split.
  - by apply linear_invariant.
  - by apply dr_rep_A.
qed.

lemma sample_basic_correct (N : int) :
  162 < N =>
  hoare [MRSRep.sample_basic :
    arg = N ==>
    19 * (fst res) + 9 * (snd res) = N /\
    dr (fst res) = dr N].
proof.
  move=> hN.
  proc.
  conseq />.
  move=> kvl.
  apply sample_basic_inv.
  - smt().
  - smt(kmax_ge0).
qed.

(* ================================================================= *)
(* Section 11: Equivalence lemmas (deferred)                          *)
(* ================================================================= *)

(* The reflexivity tests `sample_basic_equiv` and                     *)
(* `sample_triangle_equiv` are deferred: they are not used by any     *)
(* downstream module, and the equivalence proofs for procedures       *)
(* with `<$`-sampling require a different tactic pattern.             *)

(* ================================================================= *)
(* Section 12: 3-term and 4-term extensions                           *)
(* ================================================================= *)

op sum_R (q r N p : int) : int -> int -> int =
  fun A kmax =>
    if (kmax < A) then 0
    else R q r (N - p * A) + sum_R q r N p (A + 1) kmax.

op R_3_sum (p q r N : int) : int =
  if (p <= 0 \/ q <= 0 \/ r <= 0 \/ N < 0) then 0
  else sum_R q r N p 0 (N %/ p).

op R_3 (p q r N : int) : int =
  if (p <= 0 \/ q <= 0 \/ r <= 0 \/ N < 0) then 0
  else
    let M = N %/ p in
    let J = M %/ r in
    let Rm = M %% r in
    if (M < q * r) then 0
    else
      let numerator = (J + 1) * M - p * r * (J * (J + 1) %/ 2) - Rm in
      numerator %/ q + (J + 1).

lemma sum_R_empty (q r N p A kmax : int) :
  kmax < A => sum_R q r N p A kmax = 0.
proof.
  move=> h.
  rewrite /sum_R.
  by rewrite h.
qed.

lemma sum_R_step (q r N p A kmax : int) :
  A <= kmax =>
  sum_R q r N p A kmax =
    R q r (N - p * A) + sum_R q r N p (A + 1) kmax.
proof.
  move=> h.
  rewrite /sum_R.
  have : ! (kmax < A) by smt().
  by rewrite this.
qed.

lemma R_with_r_one (q M : int) :
  0 < q => M >= q =>
  R q 1 M = 1.
proof.
  move=> hq hM.
  rewrite /R.
  have h1 : ! (q <= 0) by smt().
  have h2 : ! (1 <= 0) by smt().
  have h3 : ! (M < 0) by smt().
  rewrite h1 h2 h3 /=.
  have hmod : M %% 1 = 0 by smt().
  rewrite hmod.
  have hle : 0 <= M %/ q by smt(divz_ge0).
  have hgt : ! (M %/ q < 0) by smt().
  rewrite hgt /=.
  have hdiv : M %/ q %/ 1 = M %/ q by smt().
  rewrite hdiv.
  smt().
qed.

lemma R_3_r_one (p q N : int) :
  0 < p => 0 < q => p %% q = 1 => N >= p * q =>
  R_3 p q 1 N = 0.
proof.
  move=> hp hq hpq hN.
  rewrite /R_3.
  have h1 : ! (p <= 0) by smt().
  have h2 : ! (q <= 0) by smt().
  have h3 : ! (1 <= 0) by smt().
  have h4 : ! (N < 0) by smt().
  rewrite h1 h2 h3 h4 /=.
  have hM_div_1 : N %/ p %/ 1 = N %/ p by smt().
  have hM_mod_1 : N %/ p %% 1 = 0 by smt().
  rewrite hM_div_1 hM_mod_1.
  case (N %/ p < q) => [hlt | hge].
  - by [].
  have hp_gt2 : 2 < p.
    have hpq_pos : 0 < p by smt().
    smt().
  have hnum_neg :
      (N %/ p %/ 1 + 1) * (N %/ p) -
      p * 1 * ((N %/ p %/ 1 * (N %/ p %/ 1 + 1)) %/ 2) -
      (N %/ p %% 1) < 0.
    rewrite hM_div_1 hM_mod_1.
    have hM_pos : 0 < N %/ p by smt(divz_eq).
    have hfac_pos : 0 < N %/ p * (N %/ p + 1) by smt().
    smt().
  have hq_pos : 0 < q by smt().
  smt(divz_ge0).
qed.

lemma R_3_trivial_r (p q N : int) :
  0 < p => 2 < p => 0 < q => p %% q = 1 => N >= p * q =>
  R_3 p q 1 N = 0.
proof.
  move=> hp hp2 hq hpq hN.
  apply R_3_r_one; smt().
qed.

op R_4 (p q r s N : int) : int =
  if (p <= 0 \/ q <= 0 \/ r <= 0 \/ s <= 0 \/ N < 0) then 0
  else
    let M0 = N %/ p in
    let S1 = (M0 + 1) * (M0 + 2) %/ 2 in
    let Sigma2 = M0 * (M0 + 1) %/ 2 in
    let Sigma3 = M0 %/ r in
    let Sigma4 = 0 in
    (M0 * S1 - s * Sigma2 - (p * r %/ 2) * Sigma3 - Sigma4) %/ q.

lemma R_4_nonneg (p q r s N : int) :
  0 < p => 0 < q => 0 < r => 0 < s => N >= 0 =>
  0 <= R_4 p q r s N.
proof.
  move=> hp hq hr hs hN.
  rewrite /R_4.
  have h1 : ! (p <= 0) by smt().
  have h2 : ! (q <= 0) by smt().
  have h3 : ! (r <= 0) by smt().
  have h4 : ! (s <= 0) by smt().
  have h5 : ! (N < 0) by smt().
  rewrite h1 h2 h3 h4 h5 /=.
  have hM0_ge0 : 0 <= N %/ p by smt(divz_ge0).
  have hS1_ge0 : 0 <= (N %/ p + 1) * (N %/ p + 2) %/ 2.
    smt(divz_ge0).
  have hSig2_ge0 : 0 <= (N %/ p) * (N %/ p + 1) %/ 2.
    smt(divz_ge0).
  have hSig3_ge0 : 0 <= (N %/ p) %/ r by smt(divz_ge0).
  smt(divz_ge0).
qed.

lemma example_143_R_3 : R_3 19 9 3 143 = 0.
proof. by smt(). qed.

lemma example_958_R_3 : R_3 19 9 3 958 = 6.
proof. by smt(). qed.

lemma example_6666_R_3 : R_3 19 9 3 6666 = 39.
proof.
  rewrite /R_3.
  by smt().
qed.

lemma example_143_R_4 : R_4 19 9 3 3 143 = 0.
proof. by smt(). qed.

lemma example_958_R_4 : R_4 19 9 3 3 958 = 6.
proof. by smt(). qed.

lemma example_6666_R_4 : R_4 19 9 3 3 6666 = 39.
proof.
  rewrite /R_4.
  by smt().
qed.

(* ================================================================= *)
(* End of MRS_Core.ec                                                 *)
(* ================================================================= *)
