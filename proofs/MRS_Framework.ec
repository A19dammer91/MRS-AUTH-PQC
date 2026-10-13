(* ================================================================= *)
(*  MRS_Framework.ec                                                  *)
(*  General framework for linear Diophantine representation systems   *)
(*      N = p*A + q*B     with p = 1 (mod q), gcd(p,q) = 1, p > q     *)
(*                                                                    *)
(*  This file establishes the general theory for arbitrary pairs      *)
(*  (p,q) satisfying the structural conditions. It is independent     *)
(*  of MRS_Core.ec and can be compiled on its own.                    *)
(*                                                                    *)
(*  Axiom baseline: 0.                                                *)
(*                                                                    *)
(*  Robustness principles (EasyCrypt r2024.09):                       *)
(*  - `>` and `>=` are written as `<` and `<=` with reversed operands *)
(*  - NO axioms, NO admits.                                           *)
(*  - Compound goals are split with `split.` before `smt()`.          *)
(* ================================================================= *)

require import AllCore Int IntDiv.

(* ================================================================= *)
(* Section 0: Auxiliary lemmas about div and mod                      *)
(* ================================================================= *)

lemma my_modz_ge0 (a b : int) :
  0 < b => 0 <= a %% b.
proof.
  move=> hb.
  smt().
qed.

lemma my_modz_lt (a b : int) :
  0 < b => a %% b < b.
proof.
  move=> hb.
  have hdecomp := divz_eq a b.
  smt().
qed.

lemma my_modz_range (a b : int) :
  0 < b => 0 <= a %% b /\ a %% b < b.
proof.
  move=> hb.
  split.
  - apply my_modz_ge0. smt().
  - apply my_modz_lt. smt().
qed.

lemma my_modzMl (a b : int) :
  (a * b) %% b = 0.
proof.
  by apply modzMl.
qed.

(* ================================================================= *)
(* Section 1: Basic definitions                                       *)
(* ================================================================= *)

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
    if (fm < a0) then 0
    else (fm - a0) %/ q + 1.

op G (p q k : int) : int = p * q * (k - 1) + (p - 1) * (q - 1).

(* ================================================================= *)
(* Section 2: Digital root properties                                 *)
(* ================================================================= *)

lemma dr_q_range (q N : int) :
  0 < q => 0 < N => 1 <= dr_q q N /\ dr_q q N <= q.
proof.
  move=> hq hN.
  rewrite /dr_q.
  have h1 : ! (N <= 0) by smt().
  have h2 : ! (q <= 0) by smt().
  rewrite h1 h2 /=.
  have [hmod_ge0 hmod_lt] := my_modz_range (N - 1) q hq.
  split.
  - smt().
  - have hle : 1 + ((N - 1) %% q) <= 1 + (q - 1) by smt().
    have heq : 1 + (q - 1) = q by ring.
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
  have hq_ne : q <> 0 by smt().
  have hdiv := divz_eq (N - 1) q.
  have hN_decomp := divz_eq N q.
  have [hmod_ge0 hmod_lt] := my_modz_range N q hq.
  case (N %% q = 0) => [hmod0 | hmod_ne].
  - have hN_eq : N = N %/ q * q by smt().
    have hNm1_mod : (N - 1) %% q = q - 1.
      have hq_ge1 : 1 <= q by smt().
      have hN_ge_q : q <= N by smt().
      have hdiv_ge1 : 1 <= N %/ q by smt(divz_eq).
      have : N - 1 = (N %/ q - 1) * q + (q - 1) by smt().
      move=> hdecomp2.
      have : (N - 1) %% q = ((N %/ q - 1) * q + (q - 1)) %% q by smt().
      rewrite this.
      have : ((N %/ q - 1) * q + (q - 1)) %% q = (q - 1) %% q.
        by smt(modzDl).
      rewrite this.
      by smt().
    rewrite hNm1_mod.
    rewrite hN_eq.
    have : 1 + (q - 1) - N %/ q * q = (1 - N %/ q) * q by ring.
    move=> ->.
    by smt(modzMl).
  - have hNm1_mod : (N - 1) %% q = N %% q - 1.
      have hN_eq : N = N %/ q * q + N %% q by smt().
      have : N - 1 = N %/ q * q + (N %% q - 1) by smt().
      move=> hdecomp2.
      have : (N - 1) %% q = (N %/ q * q + (N %% q - 1)) %% q by smt().
      rewrite this.
      have : (N %/ q * q + (N %% q - 1)) %% q = (N %% q - 1) %% q.
        by smt(modzDl).
      rewrite this.
      have hmod_ge1 : 1 <= N %% q by smt().
      have hNm1_ge0 : 0 <= N %% q - 1 by smt().
      have hNm1_lt : N %% q - 1 < q by smt().
      by smt().
    rewrite hNm1_mod.
    have hN_eq : N = N %/ q * q + N %% q by smt().
    rewrite hN_eq.
    have : 1 + (N %% q - 1) - (N %/ q * q + N %% q) = -(N %/ q * q) by ring.
    move=> ->.
    have : -(N %/ q * q) = (-(N %/ q)) * q by ring.
    move=> ->.
    by smt(modzMl).
qed.

(* ================================================================= *)
(* Section 3: A0 equals dr_q(N)                                       *)
(* ================================================================= *)

lemma A0_eq_dr_q (p q N : int) :
  0 < p => 0 < q => p %% q = 1 => 0 < N =>
  N %% q = dr_q q N - 1 \/ (N %% q = q - 1 /\ dr_q q N = q).
proof.
  move=> hp hq hpq hN.
  have hdr := dr_q_range q N hq hN.
  have [hlo hhi] := hdr.
  have [hmod_ge0 hmod_lt] := my_modz_range N q hq.
  case (N %% q = 0) => [h0 | hne].
  - right.
    split.
    + exact h0.
    + rewrite dr_q_eq_mod //.
      have hNm1_mod : (N - 1) %% q = q - 1.
        have hq_ge1 : 1 <= q by smt().
        have hN_eq : N = N %/ q * q by smt().
        have hdiv_ge1 : 1 <= N %/ q by smt(divz_eq).
        have : N - 1 = (N %/ q - 1) * q + (q - 1) by smt().
        move=> hdecomp2.
        have : (N - 1) %% q = ((N %/ q - 1) * q + (q - 1)) %% q by smt().
        rewrite this.
        have : ((N %/ q - 1) * q + (q - 1)) %% q = (q - 1) %% q.
          by smt(modzDl).
        rewrite this.
        by smt().
      rewrite hNm1_mod.
      by ring.
  - left.
    have := dr_q_cong q N hq hN.
    smt().
qed.

lemma A0_minimal (p q N : int) :
  0 < p => 0 < q => p %% q = 1 => p * q <= N =>
  exists B, 0 <= B /\ p * (N %% q) + q * B = N.
proof.
  move=> hp hq hpq hN.
  exists ((N - p * (N %% q)) %/ q).
  split.
  - have [hmod_ge0 hmod_lt] := my_modz_range N q hq.
    have hp_ge1 : 1 <= p by smt().
    have hprod_le : p * (N %% q) <= p * (q - 1) by smt().
    have hnn : 0 <= N - p * (N %% q) by smt().
    apply divz_ge0. exact hnn.
  - have [hmod_ge0 hmod_lt] := my_modz_range N q hq.
    have hp_ge1 : 1 <= p by smt().
    have hprod_le : p * (N %% q) <= p * (q - 1) by smt().
    have hnn : 0 <= N - p * (N %% q) by smt().
    have hdecomp := divz_eq (N - p * (N %% q)) q.
    have hq_ne : q <> 0 by smt().
    have hmod : (N - p * (N %% q)) %% q = 0.
      have hN_eq : N = N %/ q * q + N %% q by smt().
      have : N - p * (N %% q) = (1 - p) * (N %% q) + N %/ q * q by smt().
      move=> hsub.
      have : (N - p * (N %% q)) %% q =
             ((1 - p) * (N %% q) + N %/ q * q) %% q by smt().
      rewrite this.
      have : ((1 - p) * (N %% q) + N %/ q * q) %% q =
             ((1 - p) * (N %% q)) %% q by smt(modzDl).
      rewrite this.
      have hpd := divz_eq p q.
      have hp_eq : p = p %/ q * q + 1 by smt().
      have hp_m1 : p - 1 = p %/ q * q by smt().
      have : 1 - p = -(p - 1) by ring.
      move=> ->.
      rewrite hp_m1.
      have : - (p %/ q * q) * (N %% q) = (- (p %/ q) * (N %% q)) * q by ring.
      move=> ->.
      by smt(modzMl).
    rewrite hmod in hdecomp.
    have : q * ((N - p * (N %% q)) %/ q) = N - p * (N %% q) by smt().
    smt().
qed.

(* ================================================================= *)
(* Section 4: Closed formula for R                                    *)
(* ================================================================= *)

lemma R_well_defined (p q N : int) :
  0 < p => 0 < q => p * q <= N =>
  N %% q <= N %/ p.
proof.
  move=> hp hq hN.
  have [hmod_ge0 hmod_lt] := my_modz_range N q hq.
  have hp_ge1 : 1 <= p by smt().
  have h2 : q <= N %/ p by smt(divz_eq).
  smt().
qed.

lemma R_formula (p q N : int) :
  0 < p => 0 < q => p %% q = 1 => p * q <= N =>
  R p q N = (N %/ p - (N %% q)) %/ q + 1.
proof.
  move=> hp hq hpq hN.
  rewrite /R.
  have h1 : ! (p <= 0) by smt().
  have h2 : ! (q <= 0) by smt().
  have h3 : ! (N < 0) by smt().
  rewrite h1 h2 h3 /=.
  have hle : N %% q <= N %/ p by apply R_well_defined.
  have hgt : ! (N %/ p < N %% q) by smt().
  by rewrite hgt.
qed.

(* ================================================================= *)
(* Section 5: Characterisation of representations                     *)
(* ================================================================= *)

pred is_rep (p q N A B : int) =
  0 <= A /\ 0 <= B /\ p * A + q * B = N.

pred is_valid_A (p q N A : int) =
  exists B, is_rep p q N A B.

lemma is_rep_A0_B0 (p q N : int) :
  0 < p => 0 < q => p %% q = 1 => p * q <= N =>
  is_rep p q N (N %% q) ((N - p * (N %% q)) %/ q).
proof.
  move=> hp hq hpq hN.
  rewrite /is_rep.
  split.
  - by apply my_modz_ge0.
  - split.
    + have [hmod_ge0 hmod_lt] := my_modz_range N q hq.
      have hp_ge1 : 1 <= p by smt().
      have hprod_le : p * (N %% q) <= p * (q - 1) by smt().
      have hnn : 0 <= N - p * (N %% q) by smt().
      apply divz_ge0. exact hnn.
    + have hmin := A0_minimal p q N hp hq hpq hN.
      move: hmin => [B [hB_ge0 hB_eq]].
      have hdecomp := divz_eq (N - p * (N %% q)) q.
      have [hmod_ge0 hmod_lt] := my_modz_range N q hq.
      have hp_ge1 : 1 <= p by smt().
      have hprod_le : p * (N %% q) <= p * (q - 1) by smt().
      have hnn : 0 <= N - p * (N %% q) by smt().
      have hmod : (N - p * (N %% q)) %% q = 0.
        have hq_ne : q <> 0 by smt().
        have hN_eq : N = N %/ q * q + N %% q by smt().
        have : N - p * (N %% q) = (1 - p) * (N %% q) + N %/ q * q by smt().
        move=> hsub.
        have : (N - p * (N %% q)) %% q =
               ((1 - p) * (N %% q) + N %/ q * q) %% q by smt().
        rewrite this.
        have : ((1 - p) * (N %% q) + N %/ q * q) %% q =
               ((1 - p) * (N %% q)) %% q by smt(modzDl).
        rewrite this.
        have hp_eq : p = p %/ q * q + 1 by smt(divz_eq).
        have hp_m1 : p - 1 = p %/ q * q by smt().
        have : 1 - p = -(p - 1) by ring.
        move=> ->.
        rewrite hp_m1.
        have : - (p %/ q * q) * (N %% q) = (- (p %/ q) * (N %% q)) * q by ring.
        move=> ->.
        by smt(modzMl).
      have : q * ((N - p * (N %% q)) %/ q) = N - p * (N %% q) by smt().
      smt().
qed.

lemma rep_characterisation_forward (p q N : int) :
  0 < p => 0 < q => p %% q = 1 => p * q <= N =>
  forall A,
    is_valid_A p q N A =>
    (exists k,
       0 <= k /\
       k <= (N %/ p - (N %% q)) %/ q /\
       A = (N %% q) + q * k).
proof.
  move=> hp hq hpq hN A.
  move=> [B [hA_ge0 [hB_ge0 hEq]]].
  have hA_mod : A %% q = N %% q.
    have : (p * A + q * B) %% q = N %% q by rewrite hEq.
    smt(modzDl modzMl modz_mod).
  have hA_ge_a0 : N %% q <= A.
    have [hmod_ge0 hmod_lt] := my_modz_range N q hq.
    smt().
  have hk_ge0 : 0 <= (A - (N %% q)) %/ q.
    apply divz_ge0; smt().
  exists ((A - (N %% q)) %/ q).
  split; first by [].
  split.
  - have hA_le : A <= N %/ p.
      have := divz_eq N p.
      have hp_ge1 : 1 <= p by smt().
      smt().
    have hprod : q * B >= 0 by smt().
    smt().
  - have hA_mod' : (A - (N %% q)) %% q = 0 by smt(modzDl modzNm).
    have := divz_eq (A - (N %% q)) q.
    smt().
qed.

(* ================================================================= *)
(* Section 6: Family boundary                                         *)
(* ================================================================= *)

lemma G_ge (p q k : int) :
  0 < p => 0 < q => 1 <= k =>
  G p q k = p * q * (k - 1) + (p - 1) * (q - 1).
proof. by rewrite /G. qed.

lemma G_19_9 (k : int) : G 19 9 k = 171 * (k - 1) + 144.
proof. rewrite /G. by ring. qed.

lemma G_19_9_alt (k : int) : G 19 9 k = 171 * k - 27.
proof. rewrite /G. by ring. qed.

(* ================================================================= *)
(* Section 7: Worked examples                                         *)
(* ================================================================= *)

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

(* ================================================================= *)
(* Section 8: Consistency with MRS_Core (19,9)                        *)
(* ================================================================= *)

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
  case (N %/ 19 < N %% 9) => [hlt | hle].
  - smt().
  have := divz_eq N 19.
  have := divz_eq N 9.
  smt().
qed.

(* ================================================================= *)
(* End of MRS_Framework.ec                                           *)
(* ================================================================= *)
