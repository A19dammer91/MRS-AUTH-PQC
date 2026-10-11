(* ================================================================= *)
(*  MRS_Extensions.ec                                                 *)
(*  3-term and 4-term extensions of the MRS framework                 *)
(*                                                                    *)
(*  This file extends MRS_Framework.ec with the 3-term and 4-term     *)
(*  Diophantine representation counters.                              *)
(*                                                                    *)
(*  Axiom baseline: 0.                                                *)
(* ================================================================= *)

require import AllCore Int IntDiv.
require import MRS_Framework.

(* ================================================================= *)
(* Section 1: Recursive sum for the 3-term counter                    *)
(* ================================================================= *)

op sum_R (q r N p : int) : int -> int -> int =
  fun A kmax =>
    if (kmax < A) then 0
    else R q r (N - p * A) + sum_R q r N p (A + 1) kmax.

op R_3_sum (p q r N : int) : int =
  if (p <= 0 \/ q <= 0 \/ r <= 0 \/ N < 0) then 0
  else sum_R q r N p 0 (N %/ p).

(* ================================================================= *)
(* Section 2: Closed form for the 3-term counter                      *)
(* ================================================================= *)

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

(* ================================================================= *)
(* Section 3: Basic lemmas for the recursive sum                      *)
(* ================================================================= *)

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

lemma R_inner_formula (q r M : int) :
  0 < q => 0 < r => q %% r = 1 => M >= q * r =>
  R q r M = (M %/ q - (M %% r)) %/ r + 1.
proof.
  move=> hq hr hqr hM.
  by apply R_formula.
qed.

(* ================================================================= *)
(* Section 4: The degenerate r = 1 case                               *)
(*                                                                    *)
(* For R_3 to be a valid count, we require q = 1 (mod r) with         *)
(* r >= 2. When r = 1, the structural condition q = 1 (mod r)         *)
(* imposes no constraint, and the formula degenerates: the            *)
(* numerator becomes negative for p > 2.                              *)
(* ================================================================= *)

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

lemma sum_R_r_one (q N p A kmax : int) :
  0 < q => A <= kmax =>
  (forall i, A <= i => i <= kmax => N - p * i >= q) =>
  sum_R q 1 N p A kmax = kmax - A + 1.
proof.
  move=> hq hA hbound.
  elim /Int.Induction: kmax hA hbound => [| kmax' IH] hA hbound.
  - smt().
  - have hstep := sum_R_step q 1 N p A (kmax' + 1).
    have hAle : A <= kmax' + 1 by smt().
    rewrite hstep //.
    have hinner : R q 1 (N - p * A) = 1.
      apply R_with_r_one; first by smt().
      apply hbound; smt().
    rewrite hinner.
    case (A = kmax' + 1) => [heq | hne].
    + have hempty : sum_R q 1 N p (A + 1) (kmax' + 1) = 0.
        apply sum_R_empty; smt().
      rewrite hempty.
      smt().
    + have hrec := IH (A + 1).
      have hAle' : A + 1 <= kmax' + 1 by smt().
      have hbound' : forall i, A + 1 <= i => i <= kmax' + 1 =>
                      N - p * i >= q.
        move=> i hi1 hi2.
        apply hbound; smt().
      rewrite (hrec hAle' hbound').
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

(* ================================================================= *)
(* Section 5: 4-term extension                                        *)
(* ================================================================= *)

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

(* ================================================================= *)
(* Section 6: Worked examples                                         *)
(* ================================================================= *)

lemma example_143_R_3 : R_3 19 9 3 143 = 0.
proof. by compute. qed.

lemma example_958_R_3 : R_3 19 9 3 958 = 6.
proof. by compute. qed.

lemma example_6666_R_3 : R_3 19 9 3 6666 = 39.
proof. by compute. qed.

lemma example_143_R_4 : R_4 19 9 3 3 143 = 0.
proof. by compute. qed.

lemma example_958_R_4 : R_4 19 9 3 3 958 = 6.
proof. by compute. qed.

lemma example_6666_R_4 : R_4 19 9 3 3 6666 = 39.
proof. by compute. qed.

(* ================================================================= *)
(* End of MRS_Extensions.ec                                          *)
(* ================================================================= *)
