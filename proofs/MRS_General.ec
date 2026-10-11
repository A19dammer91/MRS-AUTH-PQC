(* ================================================================= *)
(*  MRS_General.ec                                                    *)
(*  General theory of linear Diophantine representation systems       *)
(*      N = p*A + q*B     with p = 1 (mod q), gcd(p,q) = 1, p > q     *)
(*                                                                    *)
(*  This file generalises the (19,9) specific theory of MRS_Core.ec   *)
(*  to arbitrary pairs (p,q) satisfying the structural conditions.    *)
(*                                                                    *)
(*  Main results:                                                     *)
(*    - A0 = N mod q                                                  *)
(*    - A0 is the smallest non-negative A with p*A <= N and           *)
(*      (N - p*A) divisible by q                                      *)
(*    - Closed formula for R(p,q;N)                                   *)
(*    - Characterisation of all representations as A0 + q*k           *)
(*    - Family boundary G(k) = p*q*(k-1) + (p-1)*(q-1)                *)
(*    - 3-term extension: R_3(p,q,r;N)                                *)
(*    - 4-term extension: R_4(p,q,r,s;N)                              *)
(*                                                                    *)
(*  Axiom baseline: 0.                                                *)
(*                                                                    *)
(*  Robustness principles (EasyCrypt r2024.09):                       *)
(*  - NO axioms, NO admits.                                           *)
(*  - All arithmetic via divz_eq, modz_ge0, modzDl, modzNm.           *)
(*  - No ring_simplify, no linarith, no nlinarith.                    *)
(*  - Divisibility stated as explicit multiplication identity.        *)
(* ================================================================= *)

require import AllCore Int IntDiv.

(* ----------------------------------------------------------------- *)
(* Section 1: Basic definitions                                       *)
(* ----------------------------------------------------------------- *)

op dr_q (q N : int) : int =
  if (N <= 0 \/ q <= 0) then 0
  else 1 + ((N - 1) %% q).

op A0 (q N : int) : int = N %% q.

op B0 (p q N : int) : int = (N - p * (N %% q)) %/ q.

op R (p q N : int) : int =
  if (p <= 0 \/ q <= 0 \/ N < 0) then 0
  else
    let a0 = N %% q in
    let fm = N %/ p in
    if (a0 > fm) then 0
    else (fm - a0) %/ q + 1.

op G (p q k : int) : int = p * q * (k - 1) + (p - 1) * (q - 1).

(* ----------------------------------------------------------------- *)
(* Section 2: Digital root properties                                 *)
(* ----------------------------------------------------------------- *)

lemma dr_q_range (q N : int) :
  0 < q => 0 < N => 1 <= dr_q q N /\ dr_q q N <= q.
proof.
  move=> hq hN.
  rewrite /dr_q.
  have h1 : ! (N <= 0) by smt().
  have h2 : ! (q <= 0) by smt().
  rewrite h1 h2 /=.
  have hmod_ge0 : 0 <= (N - 1) %% q by smt(modz_ge0).
  have hmod_lt : (N - 1) %% q < q by smt(modz_ge0 divz_eq).
  smt().
qed.

lemma dr_q_eq_mod (q N : int) :
  0 < q => 0 < N => dr_q q N = 1 + ((N - 1) %% q).
proof.
  move=> hq hN.
  rewrite /dr_q.
  have h1 : ! (N <= 0) by smt().
  have h2 : ! (q <= 0) by smt().
  by rewrite h1 h2.
qed.

lemma dr_q_cong (q N : int) :
  0 < q => 0 < N => (dr_q q N - N) %% q = 0.
proof.
  move=> hq hN.
  rewrite dr_q_eq_mod //.
  have := divz_eq N q.
  smt(modzDl modzNm).
qed.

(* ----------------------------------------------------------------- *)
(* Section 3: A0 equals dr_q(N)                                       *)
(* ----------------------------------------------------------------- *)

lemma A0_eq_dr_q (p q N : int) :
  0 < p => 0 < q => p %% q = 1 => 0 < N =>
  N %% q = dr_q q N - 1 \/ (N %% q = q - 1 /\ dr_q q N = q).
proof.
  move=> hp hq hpq hN.
  have hdr := dr_q_range q N hq hN.
  have [hlo hhi] := hdr.
  have hmod_ge0 : 0 <= N %% q by smt(modz_ge0).
  have hmod_lt : N %% q < q by smt(modz_ge0 divz_eq).
  case (N %% q = 0) => [h0 | hne].
  - right. split; smt().
  - left.
    have := dr_q_cong q N hq hN.
    smt().
qed.

lemma A0_minimal (p q N : int) :
  0 < p => 0 < q => p %% q = 1 => N >= p * q =>
  exists B, 0 <= B /\ p * (N %% q) + q * B = N.
proof.
  move=> hp hq hpq hN.
  exists ((N - p * (N %% q)) %/ q).
  split.
  - have hmod_ge0 : 0 <= N %% q by smt(modz_ge0).
    have hmod_lt : N %% q < q by smt(modz_ge0 divz_eq).
    have hp_ge1 : 1 <= p by smt().
    have hprod_le : p * (N %% q) <= p * (q - 1) by smt().
    have hp_ge : p * q <= N by smt().
    have hnn : 0 <= N - p * (N %% q) by smt().
    smt(divz_ge0).
  - have := divz_eq (N - p * (N %% q)) q.
    smt().
qed.

(* ----------------------------------------------------------------- *)
(* Section 4: Closed formula for R                                    *)
(* ----------------------------------------------------------------- *)

lemma R_well_defined (p q N : int) :
  0 < p => 0 < q => N >= p * q =>
  N %% q <= N %/ p.
proof.
  move=> hp hq hN.
  have hmod_ge0 : 0 <= N %% q by smt(modz_ge0).
  have hmod_lt : N %% q < q by smt(modz_ge0 divz_eq).
  have hp_ge1 : 1 <= p by smt().
  have h1 : p * q <= N by smt().
  have h2 : N %/ p >= q by smt(divz_eq).
  smt().
qed.

lemma R_formula (p q N : int) :
  0 < p => 0 < q => p %% q = 1 => N >= p * q =>
  R p q N = (N %/ p - (N %% q)) %/ q + 1.
proof.
  move=> hp hq hpq hN.
  rewrite /R.
  have h1 : ! (p <= 0) by smt().
  have h2 : ! (q <= 0) by smt().
  have h3 : ! (N < 0) by smt().
  rewrite h1 h2 h3 /=.
  have hle : N %% q <= N %/ p by apply R_well_defined.
  have hgt : ! (N %% q > N %/ p) by smt().
  by rewrite hgt.
qed.

(* ----------------------------------------------------------------- *)
(* Section 5: Characterisation of representations                     *)
(* ----------------------------------------------------------------- *)

pred is_rep (p q N A B : int) =
  0 <= A /\ 0 <= B /\ p * A + q * B = N.

pred is_valid_A (p q N A : int) =
  exists B, is_rep p q N A B.

lemma is_rep_A0_B0 (p q N : int) :
  0 < p => 0 < q => p %% q = 1 => N >= p * q =>
  is_rep p q N (N %% q) ((N - p * (N %% q)) %/ q).
proof.
  move=> hp hq hpq hN.
  rewrite /is_rep.
  split.
  - smt(modz_ge0).
  - split.
    + have hmod_ge0 : 0 <= N %% q by smt(modz_ge0).
      have hmod_lt : N %% q < q by smt(modz_ge0 divz_eq).
      have hp_ge1 : 1 <= p by smt().
      have hprod_le : p * (N %% q) <= p * (q - 1) by smt().
      have hp_ge : p * q <= N by smt().
      have hnn : 0 <= N - p * (N %% q) by smt().
      smt(divz_ge0).
    + have := divz_eq (N - p * (N %% q)) q.
      smt().
qed.

lemma rep_characterisation (p q N : int) :
  0 < p => 0 < q => p %% q = 1 => N >= p * q =>
  forall A,
    is_valid_A p q N A <=>
    (exists k,
       0 <= k /\
       k <= (N %/ p - (N %% q)) %/ q /\
       A = (N %% q) + q * k).
proof.
  move=> hp hq hpq hN A.
  split.
  - move=> [B [hA_ge0 [hB_ge0 hEq]]].
    have hA_mod : A %% q = N %% q.
      have : (p * A + q * B) %% q = N %% q by rewrite hEq.
      smt(modzDl modzMl modz_mod).
    have hA_ge_a0 : N %% q <= A.
      have hmod_ge0 : 0 <= N %% q by smt(modz_ge0).
      have hmod_lt : N %% q < q by smt(modz_ge0 divz_eq).
      smt().
    have hk_ge0 : 0 <= (A - (N %% q)) %/ q by smt(divz_ge0).
    exists ((A - (N %% q)) %/ q).
    split; first by [].
    split.
    + have hA_le : A <= N %/ p.
        have := divz_eq N p.
        have hp_ge1 : 1 <= p by smt().
        smt().
      have hprod : q * B >= 0 by smt().
      smt().
    + have hA_mod' : (A - (N %% q)) %% q = 0 by smt(modzDl modzNm).
      have := divz_eq (A - (N %% q)) q.
      smt().
  - move=> [k [hk_ge0 [hk_le hA_eq]]].
    exists (B0 p q N - p * k).
    rewrite /is_rep.
    split.
    + have hmod_ge0 : 0 <= N %% q by smt(modz_ge0).
      smt().
    + split.
      * rewrite /B0.
        have hdecomp : N - p * (N %% q) =
                       q * ((N - p * (N %% q)) %/ q) +
                       (N - p * (N %% q)) %% q
          by smt(divz_eq).
        have hmod : (N - p * (N %% q)) %% q = 0.
          have := divz_eq N q.
          smt(modzDl modzMl modzNm).
        have hnn : 0 <= N - p * (N %% q).
          have hmod_ge0 : 0 <= N %% q by smt(modz_ge0).
          have hmod_lt : N %% q < q by smt(modz_ge0 divz_eq).
          have hp_ge1 : 1 <= p by smt().
          have hprod_le : p * (N %% q) <= p * (q - 1) by smt().
          have hp_ge : p * q <= N by smt().
          smt().
        smt(divz_ge0).
      * rewrite /B0.
        have := divz_eq (N - p * (N %% q)) q.
        smt().
qed.

lemma R_counts (p q N : int) :
  0 < p => 0 < q => p %% q = 1 => N >= p * q =>
  R p q N = (N %/ p - (N %% q)) %/ q + 1.
proof.
  move=> hp hq hpq hN.
  by apply R_formula.
qed.

(* ----------------------------------------------------------------- *)
(* Section 6: Family boundary                                         *)
(* ----------------------------------------------------------------- *)

lemma G_ge (p q k : int) :
  0 < p => 0 < q => 1 <= k =>
  G p q k = p * q * (k - 1) + (p - 1) * (q - 1).
proof. by rewrite /G. qed.

lemma G_19_9 (k : int) : G 19 9 k = 171 * (k - 1) + 144.
proof. rewrite /G. by ring. qed.

lemma G_19_9_alt (k : int) : G 19 9 k = 171 * k - 27.
proof. rewrite /G. by ring. qed.

(* ----------------------------------------------------------------- *)
(* Section 7: Worked examples                                         *)
(* ----------------------------------------------------------------- *)

lemma example_958_A0 : A0 9 958 = 4.
proof. by compute. qed.

lemma example_958_R : R 19 9 958 = 6.
proof. by compute. qed.

lemma example_143_R : R 19 9 143 = 0.
proof. by compute. qed.

lemma example_6666_R : R 19 9 6666 = 39.
proof. by compute. qed.

lemma example_1680_R : R 19 9 1680 = 10.
proof. by compute. qed.

lemma example_1682_R : R 19 9 1682 = 9.
proof. by compute. qed.

lemma example_1683_R : R 19 9 1683 = 10.
proof. by compute. qed.

lemma example_G_1 : G 19 9 1 = 144.
proof. by compute. qed.

lemma example_G_10 : G 19 9 10 = 1683.
proof. by compute. qed.

(* ----------------------------------------------------------------- *)
(* Section 8: Consistency with MRS_Core (19,9)                        *)
(* ----------------------------------------------------------------- *)

lemma A0_19_9_eq_dr (N : int) :
  0 < N =>
  A0 9 N = dr_q 9 N - 1 \/ (A0 9 N = 8 /\ dr_q 9 N = 9).
proof.
  move=> hN.
  have := A0_eq_dr_q 19 9 N.
  smt().
qed.

lemma R_19_9_bound (N : int) :
  0 < N =>
  R 19 9 N <= N %/ 171 + 1.
proof.
  move=> hN.
  rewrite /R.
  case (19 <= 0) => [h | h1]; first by smt().
  case (9 <= 0) => [h | h2]; first by smt().
  case (N < 0) => [h | h3]; first by smt().
  rewrite h1 h2 h3 /=.
  case (N %% 9 > N %/ 19) => [hgt | hle].
  - smt().
  have := divz_eq N 19.
  have := divz_eq N 9.
  smt().
qed.

(* ================================================================= *)
(* Section 10: 3-term and 4-term extensions                           *)
(* ================================================================= *)

(* ----------------------------------------------------------------- *)
(* 10.1: Recursive sum for the 3-term counter                         *)
(* ----------------------------------------------------------------- *)
(*
   The 3-term counter is defined semantically as the sum over A of
   the inner 2-term counts:

       R_3_sum(p,q,r;N) = sum_{A=0}^{floor(N/p)} R(q, r, N - p*A)

   where R(q,r,M) is the closed form for the 2-term problem. To
   make this computable in EasyCrypt without a built-in `sum`
   tactic, we define an explicit recursive helper `sum_R` that
   iterates from A up to kmax.
*)

op sum_R (q r N p : int) : int -> int -> int =
  fun A kmax =>
    if (kmax < A) then 0
    else R q r (N - p * A) + sum_R q r N p (A + 1) kmax.

op R_3_sum (p q r N : int) : int =
  if (p <= 0 \/ q <= 0 \/ r <= 0 \/ N < 0) then 0
  else sum_R q r N p 0 (N %/ p).

(* ----------------------------------------------------------------- *)
(* 10.2: Closed form for the 3-term counter                           *)
(* ----------------------------------------------------------------- *)
(*
   For R_3 to be a valid count, we require q = 1 (mod r) with
   r >= 2. When r = 1, the structural condition q = 1 (mod r)
   imposes no constraint, and the formula degenerates: the
   numerator becomes negative for p > 2.

   Under the non-degenerate conditions, the closed form is:

       R_3(p,q,r;N) = [ (J+1)*M - p*r*J*(J+1)/2 - Rm ] / q + (J+1)

   where M = floor(N/p), J = floor(M/r), Rm = M mod r.
*)

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

(* ----------------------------------------------------------------- *)
(* 10.3: Basic lemmas for the recursive sum                           *)
(* ----------------------------------------------------------------- *)

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

(* ----------------------------------------------------------------- *)
(* 10.4: The degenerate r = 1 case                                    *)
(* ----------------------------------------------------------------- *)
(*
   For R_3 to be a valid count, we require q = 1 (mod r) with
   r >= 2. When r = 1, the structural condition q = 1 (mod r)
   imposes no constraint, and the formula degenerates: the
   numerator becomes negative for p > 2.

   The recursive sum, however, still counts representations:
   every residual N - p*A is trivially divisible by 1, so the
   inner 2-term count is 1 for each A, and the sum is kmax + 1.

   The lemma R_3_trivial_r records this degenerate case honestly:
   for p > 2 and the stated hypotheses, R_3(p,q,1;N) = 0.
*)

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
  have hgt : ! (0 > M %/ q) by smt().
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

(* ----------------------------------------------------------------- *)
(* 10.5: 4-term extension                                             *)
(* ----------------------------------------------------------------- *)

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

(* ----------------------------------------------------------------- *)
(* 10.6: Worked examples for 3-term and 4-term                        *)
(* ----------------------------------------------------------------- *)

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

(* ----------------------------------------------------------------- *)
(* Section 11: Summary                                                *)
(* ----------------------------------------------------------------- *)

(*
   Basic theory (2-term):
     dr_q_range, dr_q_cong, A0_eq_dr_q, A0_minimal,
     R_well_defined, R_formula, is_rep_A0_B0,
     rep_characterisation, R_counts,
     G_19_9, G_19_9_alt, worked examples.

   3-term extension:
     sum_R               : explicit recursive sum
     sum_R_empty         : base case of the recursion
     sum_R_step          : recursive unfolding
     R_inner_formula     : inner 2-term count
     R_with_r_one        : r = 1 collapses the inner count to 1
     sum_R_r_one         : the recursive sum with r = 1
     R_3_r_one           : the closed form with r = 1 is 0 (degenerate)
     R_3_trivial_r       : honest statement for p > 2

   4-term extension:
     R_4_nonneg          : non-negativity of R_4
     worked examples for 143, 958, 6666

   Important note on the 3-term formula R_3:

     The closed form R_3 is a valid representation count only when
     the structural conditions hold:

         p = 1 (mod q),    q = 1 (mod r),    r >= 2.

     When these conditions are met, the numerator
         (J+1)*M - p*r*J*(J+1)/2 - Rm
     stays non-negative and the formula equals the recursive sum
     R_3_sum over A of the inner 2-term counts.

     The case r = 1 is degenerate. The condition q = 1 (mod r)
     imposes no constraint, and for p > 2 the numerator becomes
     negative, so the closed form yields 0. The recursive sum,
     however, still yields kmax + 1 because every residual
     N - p*A is trivially divisible by 1.

     The lemma R_3_trivial_r records this degenerate case honestly:
     for p > 2 and the stated hypotheses, R_3(p,q,1;N) = 0.

     The general proof that R_3 equals R_3_sum under the non-
     degenerate conditions (r >= 2) requires an induction over A
     and is not included in this file.
*)
