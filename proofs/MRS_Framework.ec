(* ================================================================= *)
(*  MRS_Framework.ec                                                  *)
(*  General framework for linear Diophantine representation systems   *)
(*  N = p*A + q*B, with p = 1 (mod q), p > q                          *)
(* ================================================================= *)

require import AllCore Int IntDiv.

(* ================================================================= *)
(* Section 0: Auxiliary modular arithmetic                            *)
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
  smt(divz_eq).
qed.

lemma my_modz_range (a b : int) :
  0 < b => 0 <= a %% b /\ a %% b < b.
proof.
  move=> hb.
  split.
  - exact (my_modz_ge0 a b hb).
  - exact (my_modz_lt a b hb).
qed.

(* ================================================================= *)
(* Section 1: Definitions                                             *)
(* ================================================================= *)

op dr_q (q N : int) : int =
  if N <= 0 \/ q <= 0 then 0
  else 1 + ((N - 1) %% q).

op A0 (q N : int) : int = N %% q.

op B0 (p q N : int) : int =
  (N - p * (N %% q)) %/ q.

op R (p q N : int) : int =
  if p <= 0 \/ q <= 0 \/ N < 0 then 0
  else
    let a0 = N %% q in
    let fm = N %/ p in
    if fm < a0 then 0
    else (fm - a0) %/ q + 1.

op G (p q k : int) : int =
  p * q * (k - 1) + (p - 1) * (q - 1).

(* ================================================================= *)
(* Section 2: Digital-root properties                                 *)
(* ================================================================= *)

lemma dr_q_range (q N : int) :
  0 < q => 0 < N =>
  1 <= dr_q q N /\ dr_q q N <= q.
proof.
  move=> hq hN.
  rewrite /dr_q.
  have hNpos : ! (N <= 0) by smt().
  have hqpos : ! (q <= 0) by smt().
  rewrite hNpos hqpos /=.
  have [hlo hhi] := my_modz_range (N - 1) q hq.
  split; smt().
qed.

lemma dr_q_eq_mod (q N : int) :
  0 < q => 0 < N =>
  dr_q q N = 1 + ((N - 1) %% q).
proof.
  move=> hq hN.
  rewrite /dr_q.
  have hNpos : ! (N <= 0) by smt().
  have hqpos : ! (q <= 0) by smt().
  by rewrite hNpos hqpos.
qed.

lemma dr_q_cong (q N : int) :
  0 < q => 0 < N =>
  (dr_q q N - N) %% q = 0.
proof.
  move=> hq hN.
  rewrite dr_q_eq_mod //.
  have hdiv : N = N %/ q * q + N %% q by smt(divz_eq).
  case (N %% q = 0) => hzero.
  - have hNmul : N = N %/ q * q by smt().
    have hprev : (N - 1) %% q = q - 1.
      have hdecomp : N - 1 = (N %/ q - 1) * q + (q - 1) by smt().
      rewrite hdecomp.
      have hmod : ((N %/ q - 1) * q + (q - 1)) %% q = (q - 1) %% q
        by smt(modzDl).
      rewrite hmod.
      have hqrange : 0 <= q - 1 /\ q - 1 < q by smt().
      smt().
    rewrite hprev hNmul.
    have hqpos : 0 < q by smt().
    have hmultiple : (1 - N %/ q) * q %% q = 0 by apply modzMl.
    smt().
  - have hrempos : 0 < N %% q by smt().
    have hprev : (N - 1) %% q = N %% q - 1.
      have hdecomp : N - 1 = N %/ q * q + (N %% q - 1) by smt().
      rewrite hdecomp.
      have hmod : (N %/ q * q + (N %% q - 1)) %% q = (N %% q - 1) %% q
        by smt(modzDl).
      rewrite hmod.
      have hremrange : 0 <= N %% q - 1 /\ N %% q - 1 < q by smt().
      smt().
    rewrite hprev hdiv.
    smt().
qed.

(* ================================================================= *)
(* Section 3: A0 and digital-root relationship                        *)
(* ================================================================= *)

lemma A0_eq_dr_q (p q N : int) :
  0 < p => 0 < q => p %% q = 1 => 0 < N =>
  N %% q = dr_q q N - 1 \/
  (N %% q = q - 1 /\ dr_q q N = q).
proof.
  move=> hp hq hpq hN.
  have hroot : dr_q q N = 1 + ((N - 1) %% q).
    rewrite /dr_q.
    have hNpos : ! (N <= 0) by smt().
    have hqpos : ! (q <= 0) by smt().
    by rewrite hNpos hqpos.

  have hdiv : N = N %/ q * q + N %% q by smt(divz_eq).

    case (N %% q = 0) => hzero.
  - have hprev : (N - 1) %% q = q - 1 by smt().
    right.
    split.
    + rewrite hroot hprev. smt().
    + rewrite hroot hprev. smt().

  - have hprev : (N - 1) %% q = N %% q - 1 by smt().
    left.
    rewrite hroot hprev.
    smt().
qed.

  - have hprev : (N - 1) %% q = N %% q - 1.
      have hrempos : 0 < N %% q by smt().
      have hdecomp : N - 1 = N %/ q * q + (N %% q - 1) by smt().
      rewrite hdecomp.
      have hmod : (N %/ q * q + (N %% q - 1)) %% q = (N %% q - 1) %% q
        by smt(modzDl).
      rewrite hmod.
      have hremrange : 0 <= N %% q - 1 /\ N %% q - 1 < q by smt().
      smt().
    left.
    rewrite hroot hprev.
    smt().
qed.

(* ================================================================= *)
(* Section 4: Minimal representation                                  *)
(* ================================================================= *)

lemma A0_minimal (p q N : int) :
  0 < p => 0 < q => p %% q = 1 => p * q <= N =>
  exists B, 0 <= B /\ p * (N %% q) + q * B = N.
proof.
  move=> hp hq hpq hN.
  exists ((N - p * (N %% q)) %/ q).
  split.
  - have [hlo hhi] := my_modz_range N q hq.
    have hnum : 0 <= N - p * (N %% q) by smt(divz_eq).
    smt(divz_ge0).
  - have hdiv : N = N %/ q * q + N %% q by smt(divz_eq).
    have hpdiv : p = p %/ q * q + 1 by smt(divz_eq).
    have hmod : (N - p * (N %% q)) %% q = 0 by smt().
    have hquot : q * ((N - p * (N %% q)) %/ q) = N - p * (N %% q)
      by smt(divz_eq).
    smt().
qed.

(* ================================================================= *)
(* Section 5: Representation count                                    *)
(* ================================================================= *)

lemma R_well_defined (p q N : int) :
  0 < p => 0 < q => p * q <= N =>
  N %% q <= N %/ p.
proof.
  move=> hp hq hN.
  have [hlo hhi] := my_modz_range N q hq.
  smt(divz_eq).
qed.

lemma R_formula (p q N : int) :
  0 < p => 0 < q => p %% q = 1 => p * q <= N =>
  R p q N = (N %/ p - N %% q) %/ q + 1.
proof.
  move=> hp hq hpq hN.
  rewrite /R.
  have hppos : ! (p <= 0) by smt().
  have hqpos : ! (q <= 0) by smt().
  have hNpos : ! (N < 0) by smt().
  rewrite hppos hqpos hNpos /=.
  have hle : N %% q <= N %/ p
    by exact (R_well_defined p q N hp hq hN).
  have hnot : ! (N %/ p < N %% q) by smt().
  by rewrite hnot.
qed.

(* ================================================================= *)
(* Section 6: Representation predicates                              *)
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
  - exact (my_modz_ge0 N q hq).
  - split.
    + have hnum : 0 <= N - p * (N %% q) by smt(divz_eq).
      smt(divz_ge0).
    + have hmin := A0_minimal p q N hp hq hpq hN.
      move: hmin => [B [hB hEq]].
      have hquot : q * ((N - p * (N %% q)) %/ q) = N - p * (N %% q)
        by smt(divz_eq).
      smt().
qed.

lemma rep_characterisation_forward (p q N : int) :
  0 < p => 0 < q => p %% q = 1 => p * q <= N =>
  forall A,
    is_valid_A p q N A =>
    exists k,
      0 <= k /\
      k <= (N %/ p - N %% q) %/ q /\
      A = N %% q + q * k.
proof.
  move=> hp hq hpq hN A.
  move=> [B [hA [hB hEq]]].
  have hAmod : A %% q = N %% q by smt(modzMl modzDl).
  have hAle : A <= N %/ p by smt(divz_eq).
  have hAlo : N %% q <= A by smt().
  exists ((A - N %% q) %/ q).
  have hnum : 0 <= A - N %% q by smt().
  have hmod : (A - N %% q) %% q = 0 by smt(modzDl).
  have hquot : q * ((A - N %% q) %/ q) = A - N %% q by smt(divz_eq).
  split; first smt(divz_ge0).
  split; first smt().
  smt().
qed.

(* ================================================================= *)
(* Section 7: Boundary function                                       *)
(* ================================================================= *)

lemma G_ge (p q k : int) :
  0 < p => 0 < q => 1 <= k =>
  G p q k = p * q * (k - 1) + (p - 1) * (q - 1).
proof.
  by rewrite /G.
qed.

lemma G_19_9 (k : int) :
  G 19 9 k = 171 * (k - 1) + 144.
proof.
  rewrite /G.
  by ring.
qed.

lemma G_19_9_alt (k : int) :
  G 19 9 k = 171 * k - 27.
proof.
  rewrite /G.
  by ring.
qed.

(* ================================================================= *)
(* Section 8: Examples                                                *)
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
(* Section 9: The (19,9) instance                                     *)
(* ================================================================= *)

lemma A0_19_9_eq_dr (N : int) :
  0 < N =>
  A0 9 N = dr_q 9 N - 1 \/
  (A0 9 N = 8 /\ dr_q 9 N = 9).
proof.
  move=> hN.
  rewrite /A0.
  have h := A0_eq_dr_q 19 9 N.
  have hp : 0 < 19 by smt().
  have hq : 0 < 9 by smt().
  have hpq : 19 %% 9 = 1 by compute.
  exact (h hp hq hpq hN).
qed.

lemma R_19_9_bound (N : int) :
  0 < N =>
  R 19 9 N <= N %/ 171 + 1.
proof.
  move=> hN.
  rewrite /R.
  have hp : ! (19 <= 0) by smt().
  have hq : ! (9 <= 0) by smt().
  have hn : ! (N < 0) by smt().
  rewrite hp hq hn /=.
  case (N %/ 19 < N %% 9) => hcase.
  - smt().
  - have hdiv19 : N = N %/ 19 * 19 + N %% 19 by smt(divz_eq).
    have hdiv9 : N = N %/ 9 * 9 + N %% 9 by smt(divz_eq).
    smt(divz_eq).
qed.

(* ================================================================= *)
(* End of MRS_Framework.ec                                            *)
(* ================================================================= *)
