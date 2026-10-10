(* ================================================================= *)
(*  MRS_Core.ec                                                       *)
(*  Mathematical core of MRS-AUTH: the 19A + 9B representation       *)
(*  system under the Positive Anchor Convention.                      *)
(*                                                                    *)
(*  The anchor A_0 is defined as the digital root of N:               *)
(*                                                                    *)
(*      A_0 = dr(N) = 1 + ((N - 1) mod 9)      for N > 0              *)
(*                                                                    *)
(*  Its range is 1..9. It is never 0. Consequently A = 0 is not a     *)
(*  valid start for a representation, and the largest non-represent-  *)
(*  able N is 162 (not the classical Sylvester bound 143, which      *)
(*  assumes A >= 0). This is a deliberate design choice: it makes     *)
(*  every representation carry a non-trivial "core" A >= 1, which     *)
(*  is what the deniability construction relies on.                   *)
(*                                                                    *)
(*  Ordering convention: all comparisons use the canonical form       *)
(*  `constant < variable` or `constant <= variable`.                  *)
(*                                                                    *)
(*  Rewrite convention: to reduce `if c <= 0 then ... else ...` when  *)
(*  the hypothesis is `0 < c`, prove the negation explicitly first    *)
(*  (`have h : ! (c <= 0) by smt().`) and rewrite with `h`.           *)
(*                                                                    *)
(*  Tactic convention: `by apply L.` requires that L closes the goal  *)
(*  completely. When L leaves a side condition, use `apply L => //.`  *)
(*  or `apply L; smt().` instead.                                     *)
(*                                                                    *)
(*  Hypothesis convention:                                            *)
(*   - `dr_9k_r` requires `0 <= k` and `0 < r` as explicit            *)
(*     hypotheses, so that the precondition `0 < 9 * k + r` (needed   *)
(*     to discharge the first `if` in `dr`) is provable for every     *)
(*     input.                                                         *)
(*   - `dr_19A_9B` requires `0 <= m` for the same reason: the         *)
(*     identity is applied to the offset `9 * (2 * n + m) + n`, and   *)
(*     `2 * n + m` must be non-negative to feed `dr_9k_r`.            *)
(*                                                                    *)
(*  Pattern convention: when the left-hand side of a `have ->:` does  *)
(*  not appear verbatim in the goal (e.g. because it sits inside a    *)
(*  function argument), `have ->:` reports "nothing to rewrite". In   *)
(*  that case, introduce the equality as a named hypothesis with      *)
(*  `have H : ... by tactic.` and then `rewrite H.` explicitly, or    *)
(*  use `by smt().` when the equality is a simple modular identity.   *)
(* ================================================================= *)

require import AllCore Int IntDiv Real Distr List.
require import StdOrder.
import IntOrder.

(* ----------------------------------------------------------------- *)
(* Digital root: 0 for n <= 0, otherwise 1 + ((n - 1) mod 9)          *)
(* Range 1..9 for n > 0                                               *)
(* ----------------------------------------------------------------- *)
op dr (n : int) : int = if n <= 0 then 0 else 1 + ((n - 1) %% 9).

lemma dr_range (n : int) : 0 < n => 1 <= dr n /\ dr n <= 9.
proof.
  move=> hn.
  rewrite /dr.
  have h : ! (n <= 0) by smt().
  rewrite h /=.
  split; first by smt(modz_ge0).
  by smt(ltz_pmod).
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

(* dr(9k + r) = dr(r) for 0 <= k and 0 < r, proved algebraically
   without induction on the integer k. The hypothesis `0 <= k` is
   required so that the precondition `0 < 9 * k + r` (needed to
   discharge the first `if` in `dr`) is provable for every input. *)
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

(* Introduces the algebraic identity as a named hypothesis, then
   rewrites with it explicitly. `have ->:` would fail here because
   the left-hand side `19 * n` sits inside the argument of `dr`,
   and EasyCrypt's `have ->` pattern matcher does not descend into
   function arguments. *)
lemma dr_19 (n : int) : 0 < n => dr (19 * n) = dr n.
proof.
  move=> hn.
  have Heq : 19 * n = 9 * (2 * n) + n by ring.
  rewrite Heq.
  apply dr_9k_r; smt().
qed.

(* Same pattern as dr_19. `0 <= m` is required so that `2 * n + m`
   is non-negative, which is what `dr_9k_r` needs. Without it, a
   negative `m` would make `2 * n + m` negative and the caller
   cannot discharge the `0 <= k` side condition. *)
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

(* ----------------------------------------------------------------- *)
(* Positive Anchor Convention                                        *)
(*                                                                    *)
(* A_0 = dr(N) is the smallest positive integer congruent to N mod 9. *)
(* Because it is never 0, A = 0 (and the representations N = 9B with  *)
(* A = 0) are excluded. This is a design choice of the framework.     *)
(* ----------------------------------------------------------------- *)
op a0 (N : int) : int = dr N.
op B0 (N : int) : int = (N - 19 * a0 N) %/ 9.
op kmax (N : int) : int = (B0 N) %/ 19.

(* ----------------------------------------------------------------- *)
(* Auxiliary lemmas about a0 and B0                                   *)
(* ----------------------------------------------------------------- *)

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

lemma N_minus_19a0_mod9 (N : int) : 0 < N => (N - 19 * (a0 N)) %% 9 = 0.
proof.
  move=> hN.
  have ha0 := a0_cong9 N hN.
  have Heq : N - 19 * a0 N = N - a0 N - 18 * a0 N by ring.
  rewrite Heq.
  have h1 : (N - a0 N) %% 9 = 0 by smt(modzDl modzNm).
  have h2 : (18 * a0 N) %% 9 = 0.
    have Heq2 : 18 * a0 N = 9 * (2 * a0 N) by ring.
    rewrite Heq2.
    by rewrite modzMl.
  smt(modzDl).
qed.

lemma key_ineq (N : int) : 162 < N => 19 * (a0 N) <= N.
proof.
  move=> hN.
  have hNpos : 0 < N by smt().
  have [hlo hhi] := a0_range N hNpos.
  case (a0 N = 9) => [heq | hne].
  - have hcong := a0_cong9 N hNpos.
    have hmod : N %% 9 = 0.
      rewrite heq in hcong.
      smt(modzDl modzNm).
    have hge : 171 <= N by smt(modz_ge0 ltz_pmod).
    rewrite heq. linarith.
  - have hle : a0 N <= 8 by smt().
    nlinarith.
qed.

lemma B0_ge0 (N : int) : 162 < N => 0 <= B0 N.
proof.
  move=> hN.
  rewrite /B0.
  have h_ineq := key_ineq N hN.
  have h_div  := N_minus_19a0_mod9 N (by smt()).
  apply divz_ge0.
  - linarith.
  - done.
qed.

lemma kmax_ge0 (N : int) : 162 < N => 0 <= kmax N.
proof.
  move=> hN.
  rewrite /kmax.
  apply divz_ge0; first by apply B0_ge0.
  done.
qed.

lemma a0_B0_eq (N : int) : 0 < N => 19 * a0 N + 9 * B0 N = N.
proof.
  move=> hN.
  rewrite /B0 /a0.
  have h := N_minus_19a0_mod9 N hN.
  have := divz_eq (N - 19 * a0 N) 9.
  smt().
qed.

(* ----------------------------------------------------------------- *)
(* Linear invariant                                                    *)
(* ----------------------------------------------------------------- *)
lemma linear_invariant N k :
  162 < N =>
  0 <= k <= kmax N =>
  19 * (a0 N + 9 * k) + 9 * (B0 N - 19 * k) = N.
proof.
  move=> hN hk.
  have base := a0_B0_eq N (by smt()).
  ring_simplify.
  linarith.
qed.

lemma B_ge0 (N k : int) :
  162 < N =>
  0 <= k <= kmax N =>
  0 <= B0 N - 19 * k.
proof.
  move=> hN hk.
  rewrite /kmax in hk.
  have h_B0 := B0_ge0 N hN.
  have hk2 : k <= B0 N %/ 19 by smt().
  have : 19 * k <= B0 N.
    have := divz_eq (B0 N) 19.
    smt(modz_ge0).
  linarith.
qed.

lemma A_pos (N k : int) :
  162 < N =>
  0 <= k <= kmax N =>
  1 <= a0 N + 9 * k.
proof.
  move=> hN hk.
  have [hlo _] := a0_range N (by smt()).
  linarith.
qed.

(* ----------------------------------------------------------------- *)
(* Predicate and uniqueness                                            *)
(* ----------------------------------------------------------------- *)

pred is_rep (N A B : int) = 1 <= A /\ 0 <= B /\ 19*A + 9*B = N.

lemma rep_uniq (N : int) (A B : int) :
  162 < N => is_rep N A B =>
  exists k, 0 <= k <= kmax N /\ A = a0 N + 9*k /\ B = B0 N - 19*k.
proof.
  move=> hN [Apos Bpos eq].
  have hNpos : 0 < N by smt().
  have A_mod : A %% 9 = N %% 9.
    have Heq : N = 19*A + 9*B by linarith.
    rewrite Heq.
    have Heq2 : (19*A + 9*B) %% 9 = (19*A) %% 9.
      by rewrite -{2}(modz_mod (9*B) 9) modzMl /= addr0.
    rewrite Heq2.
    rewrite -(modzMml 19 A 9).
    have Heq3 : 19 %% 9 = 1 by done.
    by rewrite Heq3 mul1z modz_mod.
  have ha0_eq_N : (a0 N - N) %% 9 = 0 by apply a0_cong9.
  have heq_mod : (A - a0 N) %% 9 = 0 by smt(modzDl modzNm).
  have [hlo hhi] := a0_range N hNpos.
  have hA_ge_a0 : a0 N <= A.
    case (a0 N <= A) => //.
    move=> hlt.
    have hlt' : A < a0 N by smt().
    have h1 : A - a0 N < 0 by smt().
    have h2 : -9 < A - a0 N by smt().
    have := modz_ge0 (A - a0 N) 9.
    smt().
  set k := (A - a0 N) %/ 9.
  have k_ge0 : 0 <= k by smt().
  have A_eq : A = a0 N + 9 * k.
    rewrite /k.
    have := divz_eq (A - a0 N) 9.
    smt().
  have B_eq : B = B0 N - 19 * k.
    have sum_eq : 19 * (a0 N + 9*k) + 9*B = N by rewrite -A_eq; linarith.
    have base_eq : 19 * a0 N + 9 * B0 N = N by apply a0_B0_eq.
    have : 9 * B = 9 * (B0 N - 19 * k) by linarith.
    smt(mulzI).
  have k_le_kmax : k <= kmax N.
    rewrite /kmax.
    have hB : 0 <= B0 N - 19 * k by rewrite -B_eq; linarith.
    apply (lez_trans (B0 N %/ 19)).
    - smt(divz_ge0 B0_ge0).
    - done.
  exists k.
  split; first by split.
  split; exact.
qed.

(* ----------------------------------------------------------------- *)
(* dr properties for representations                                   *)
(* ----------------------------------------------------------------- *)

lemma dr_a0 (N : int) : 0 < N => dr (a0 N) = dr N.
proof.
  move=> hN.
  rewrite /a0.
  have [hlo hhi] := dr_range N hN.
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
    have [h1' h2] := dr_range N hNpos.
    have h2pos : 0 < 2 * (if N <= 0 then 0 else 1 + (N-1) %% 9) by smt().
    smt(dr_range modz_ge0 ltz_pmod).
  rewrite /dr.
  have h2 : ! (2 * dr N <= 0) by smt().
  rewrite h2 /=.
  have lhs_range : 1 <= B0 N - 19*k /\ B0 N - 19*k <= 9 * (kmax N + 1).
    split; first by linarith.
    smt(B0_ge0 kmax_ge0).
  have cong2 : (B0 N - 19 * k - 1) %% 9 = (dr (2 * dr N) - 1) %% 9.
    have := hcong.
    smt(modzDl modzNm).
  linarith.
qed.

(* ----------------------------------------------------------------- *)
(* Frobenius boundary under Positive Anchor                          *)
(* ----------------------------------------------------------------- *)

lemma frobenius_162_not_rep (A B : int) : ~ is_rep 162 A B.
proof.
  move=> [hA hB hEq].
  have hmod : A %% 9 = 0.
    have : (19*A + 9*B) %% 9 = 162 %% 9 by rewrite hEq.
    have h162 : 162 %% 9 = 0 by done.
    smt(modzDl modzNm modzMml).
  have hAle : A <= 8 by smt().
  have hAge : 1 <= A by exact hA.
  smt(modz_ge0 ltz_pmod).
qed.

lemma dr_163 : dr 163 = 1.
proof.
  rewrite /dr.
  have h1 : ! (163 <= 0) by done.
  rewrite h1 /=.
  have Heq : 163 - 1 = 162 by ring.
  rewrite Heq.
  have Heq2 : 162 %% 9 = 0 by done.
  by rewrite Heq2 /=.
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
  (forall (A B : int), ~ is_rep 162 A B) /\
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
  have heq : 19 * a0 N + 9 * B0 N = N by apply a0_B0_eq; smt().
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

(* ----------------------------------------------------------------- *)
(* Module for representation sampling                                 *)
(* ----------------------------------------------------------------- *)
module MRSRep = {
  proc sample_basic(N : int) : int * int = {
    var k;
    k <$ [0..kmax N];
    return (a0 N + 9 * k, B0 N - 19 * k);
  }

  proc sample_triangle(N : int) : int * int = {
    var a0_val, B0_val, kmax_val, target_dr, target_r, k0, tmax, t, k;
    a0_val   <- a0 N;
    B0_val   <- B0 N;
    kmax_val <- kmax N;
    target_dr <- dr (2 * dr N);
    target_r  <- target_dr %% 9;
    k0 <- (B0_val - target_r) %% 9;
    if (kmax_val < k0) {
      return (0, 0);
    }
    tmax <- (kmax_val - k0) %/ 9;
    t    <$ [0..tmax];
    k    <- k0 + 9 * t;
    return (a0_val + 9 * k, B0_val - 19 * k);
  }
}.

lemma triangle_k0_le_kmax (N : int) :
  162 < N =>
  (B0 N - dr (2 * dr N) %% 9) %% 9 <= kmax N \/
  kmax N < (B0 N - dr (2 * dr N) %% 9) %% 9.
proof.
  move=> hN. smt().
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
  auto => />.
  move=> &m k hk_lo hk_hi.
  split.
  - apply linear_invariant => //.
    smt(kmax_ge0).
  - apply dr_rep_A => //.
    smt().
qed.

lemma sample_basic_equiv (N : int) :
  162 < N =>
  equiv [MRSRep.sample_basic ~ MRSRep.sample_basic : ={arg} ==> ={res}].
proof.
  move=> hN.
  proc.
  seq 1 1 : (={k}).
  - rnd; auto.
  - auto.
qed.

lemma sample_triangle_correct (N : int) :
  162 < N =>
  hoare [MRSRep.sample_triangle :
    arg = N ==>
    (fst res = 0 /\ snd res = 0) \/
    (19 * (fst res) + 9 * (snd res) = N /\
     dr (fst res) = dr N /\
     dr (snd res) = dr (2 * dr N))].
proof.
  move=> hN.
  proc.
  auto => />.
  move=> &m.
  split.
  - move=> hk0_gt.
    left; split => //.
  - move=> hk0_le t ht_lo ht_hi.
    right.
    set k := (B0 N - dr (2 * dr N) %% 9) %% 9 + 9 * t.
    have hk_lo : 0 <= k by smt(modz_ge0).
    have hk_hi : k <= kmax N.
      rewrite /k.
      smt(modz_ge0 ltz_pmod kmax_ge0).
    split; first by apply linear_invariant => //; smt().
    split.
    - apply dr_rep_A => //; smt().
    - have hB_pos : 0 < B0 N - 19 * k.
        have hBge := B_ge0 N k hN.
        smt(B_ge0 a0_range).
      apply dr_triangle_B => //.
      + smt().
      + have Heq : (B0 N - 19 * k) %% 9 = (B0 N - 19 * ((B0 N - dr (2 * dr N) %% 9) %% 9 + 9*t)) %% 9 by done.
        rewrite Heq.
        have Heq2 : 19 * (9 * t) %% 9 = 0.
          have Heq3 : 19 * (9 * t) = 9 * (19 * t) by ring.
          by rewrite Heq3 modzMl.
        smt(modzDl modzNm modzMml modz_mod).
      + exact hB_pos.
qed.

lemma sample_triangle_equiv (N : int) :
  162 < N =>
  equiv [MRSRep.sample_triangle ~ MRSRep.sample_triangle : ={arg} ==> ={res}].
proof.
  move=> hN.
  proc.
  seq 6 6 : (={a0_val, B0_val, kmax_val, target_dr, target_r, k0}).
  - auto.
  if => />.
  - auto.
  - seq 1 1 : (={tmax, a0_val, B0_val, k0}).
    + auto.
    + seq 1 1 : (={t, tmax, a0_val, B0_val, k0}).
      * rnd; auto.
      * auto.
qed.
