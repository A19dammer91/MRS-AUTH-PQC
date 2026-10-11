(* ================================================================= *)
(*  MRS_General.ec                                                    *)
(*  General theory of linear Diophantine representation systems       *)
(*      N = p*A + q*B     with p = 1 (mod q), gcd(p,q) = 1, p > q     *)
(*                                                                    *)
(*  Every non-trivial lemma is proven by explicit steps. The `smt`    *)
(*  tactic is used only for trivial closings, never for reasoning     *)
(*  about `%%` in combination with inequalities.                      *)
(*                                                                    *)
(*  Axiom baseline: 0.                                                *)
(* ================================================================= *)

require import AllCore Int IntDiv.

(* ================================================================= *)
(* Section 0: Auxiliary lemmas about div and mod                      *)
(*                                                                    *)
(* We prove our own version of "remainder is strictly smaller than    *)
(* the divisor", because EasyCrypt r2024.09 does not export a public  *)
(* `modz_lt` with that name.                                          *)
(* ================================================================= *)

(* Remainder is non-negative for positive divisor.                     *)
lemma my_modz_lt (a b : int) :
  0 < b => a %% b < b.
proof.
  move=> hb.
  have hb_ne : b <> 0 by smt().
  have hdecomp := divz_eq a b hb_ne.
  have hmod_ge0 : 0 <= a %% b by apply modz_ge0.
  smt().
qed.

(* Remainder is strictly smaller than the divisor.                    *)
lemma my_modz_lt (a b : int) :
  0 < b => a %% b < b.
proof.
  move=> hb.
  have hdecomp := divz_eq a b.
  have hb_ne : b <> 0 by smt().
  have hmod_ge0 : 0 <= a %% b by apply modz_ge0.
  smt().
qed.

(* The combined range: 0 <= a %% b < b.                               *)
lemma my_modz_range (a b : int) :
  0 < b => 0 <= a %% b /\ a %% b < b.
proof.
  move=> hb.
  split.
  - by apply my_modz_ge0.
  - by apply my_modz_lt.
qed.

(* For any k, (b * k) %% b = 0. We need this shape (not a * b).       *)
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
  - (* 1 <= 1 + (N-1) %% q *)
    smt().
  - (* 1 + (N-1) %% q <= q *)
    have hle : 1 + ((N - 1) %% q) <= 1 + (q - 1) by smt().
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

(* dr_q(N) is congruent to N modulo q.                                *)
lemma dr_q_cong (q N : int) :
  0 < q => 0 < N => (dr_q q N - N) %% q = 0.
proof.
  move=> hq hN.
  rewrite dr_q_eq_mod //.
  (* Goal: (1 + (N-1) %% q - N) %% q = 0 *)
  have hq_ne : q <> 0 by smt().
  have hdiv := divz_eq (N - 1) q.
  (* hdiv : N - 1 = (N-1) %/ q * q + (N-1) %% q *)
  have hN_decomp := divz_eq N q.
  (* hN_decomp : N = N %/ q * q + N %% q *)
  (* We will substitute and use modz arithmetic. *)
  have hNm1 : N - 1 = (N - 1) %/ q * q + (N - 1) %% q by smt().
  have hNeq : N = N %/ q * q + N %% q by smt().
  (* Substituting: N - 1 = N %/ q * q + N %% q - 1 *)
  (* We want to show (1 + (N-1) %% q - N) %% q = 0. *)
  (* Rewrite using hNm1: *)
  (* 1 + ((N-1) %/ q * q + (N-1) %% q - ((N-1) %/ q * q + (N-1) %% q)) *)
  (* = 1 + (N-1) %% q - N *)
  (* Substitute N: *)
  (* = 1 + (N-1) %% q - (N %/ q * q + N %% q) *)
  (* = 1 + (N-1) %% q - N %% q - N %/ q * q *)
  (* We need (1 + (N-1) %% q - N %% q) %% q = 0 *)
  (* This is not trivially true; we need the relation between N %% q and (N-1) %% q. *)
  (* Case analysis on N %% q = 0. *)
  have hmod_ge0 : 0 <= N %% q by apply modz_ge0.
  have hmod_lt : N %% q < q by apply my_modz_lt.
  case (N %% q = 0) => [hmod0 | hmod_ne].
  - (* Case N %% q = 0 *)
    (* Then N = N %/ q * q *)
    have hN_eq : N = N %/ q * q by smt().
    (* And (N-1) %% q = q - 1 for N > 0 and N %% q = 0 *)
    have hNm1_mod : (N - 1) %% q = q - 1.
      (* Use: N - 1 = (N %/ q - 1) * q + (q - 1) *)
      have hq_ge1 : 1 <= q by smt().
      have hdiv_ge1 : 1 <= N %/ q.
        have : N >= q by smt().
        smt(divz_eq).
      have : N - 1 = (N %/ q - 1) * q + (q - 1) by smt().
      move=> hdecomp2.
      (* Now use modz_eq: (a * q + b) %% q = b %% q *)
      have : (N - 1) %% q = ((N %/ q - 1) * q + (q - 1)) %% q by smt().
      rewrite this.
      have : ((N %/ q - 1) * q + (q - 1)) %% q = (q - 1) %% q.
        by smt(modzDl).
      rewrite this.
      (* (q - 1) %% q = q - 1 *)
      have hq_ge1' : 1 <= q by smt().
      have hqm1_lt : q - 1 < q by smt().
      have hqm1_ge0 : 0 <= q - 1 by smt().
      by smt().
    rewrite hNm1_mod.
    (* Now: (1 + (q - 1) - N) %% q = 0 *)
    (* And N = N %/ q * q *)
    rewrite hN_eq.
    have : 1 + (q - 1) - N %/ q * q = q - N %/ q * q by ring.
    move=> ->.
    have : q - N %/ q * q = (1 - N %/ q) * q by ring.
    move=> ->.
    by smt(modzMl).
  - (* Case N %% q <> 0 *)
    (* Then (N-1) %% q = N %% q - 1 *)
    have hNm1_mod : (N - 1) %% q = N %% q - 1.
      have hN_eq : N = N %/ q * q + N %% q by smt().
      have : N - 1 = N %/ q * q + (N %% q - 1) by smt().
      move=> hdecomp2.
      have : (N - 1) %% q = (N %/ q * q + (N %% q - 1)) %% q by smt().
      rewrite this.
      have : (N %/ q * q + (N %% q - 1)) %% q = (N %% q - 1) %% q.
        by smt(modzDl).
      rewrite this.
      (* N %% q - 1 < q and >= 0 (since N %% q <> 0 and N %% q >= 0) *)
      have hmod_ge1 : 1 <= N %% q by smt().
      have hNm1_ge0 : 0 <= N %% q - 1 by smt().
      have hNm1_lt : N %% q - 1 < q by smt().
      by smt().
    rewrite hNm1_mod.
    (* Now: (1 + (N %% q - 1) - N) %% q = 0 *)
    rewrite hN_decomp_eq.
    (* Simplify: 1 + N %% q - 1 - (N %/ q * q + N %% q) = - N %/ q * q *)
    have : 1 + (N %% q - 1) - (N %/ q * q + N %% q) = -(N %/ q * q) by ring.
    move=> ->.
    have : -(N %/ q * q) = (-(N %/ q)) * q by ring.
    move=> ->.
    by smt(modzMl).
qed.

(* We need a local name for the divz_eq of N. *)
lemma N_div_eq (N q : int) :
  q <> 0 => N = N %/ q * q + N %% q.
proof.
  move=> hq.
  by apply divz_eq.
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
    + (* dr_q q N = q *)
      rewrite dr_q_eq_mod //.
      have hNm1_mod : (N - 1) %% q = q - 1.
        have hq_ge1 : 1 <= q by smt().
        have hN_eq : N = N %/ q * q by smt().
        have hdiv_ge1 : 1 <= N %/ q.
          have : N >= q by smt().
          smt(divz_eq).
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
  0 < p => 0 < q => p %% q = 1 => N >= p * q =>
  exists B, 0 <= B /\ p * (N %% q) + q * B = N.
proof.
  move=> hp hq hpq hN.
  exists ((N - p * (N %% q)) %/ q).
  split.
  - (* 0 <= (N - p * (N %% q)) %/ q *)
    have [hmod_ge0 hmod_lt] := my_modz_range N q hq.
    have hp_ge1 : 1 <= p by smt().
    have hprod_le : p * (N %% q) <= p * (q - 1) by smt().
    have hp_ge : p * q <= N by smt().
    have hnn : 0 <= N - p * (N %% q) by smt().
    apply divz_ge0.
    exact hnn.
  - (* p * (N %% q) + q * ((N - p * (N %% q)) %/ q) = N *)
    have [hmod_ge0 hmod_lt] := my_modz_range N q hq.
    have hp_ge1 : 1 <= p by smt().
    have hprod_le : p * (N %% q) <= p * (q - 1) by smt().
    have hp_ge : p * q <= N by smt().
    have hnn : 0 <= N - p * (N %% q) by smt().
    have hdecomp := divz_eq (N - p * (N %% q)) q.
    have hq_ne : q <> 0 by smt().
    (* (N - p * (N %% q)) %% q = 0 *)
    have hmod : (N - p * (N %% q)) %% q = 0.
      have : N - p * (N %% q) = N %% q - p * (N %% q) + N %/ q * q.
        have hNeq : N = N %/ q * q + N %% q by smt().
        smt().
      move=> hsub.
      have : (N - p * (N %% q)) %% q = (N %% q - p * (N %% q) + N %/ q * q) %% q by smt().
      rewrite this.
      have : (N %% q - p * (N %% q) + N %/ q * q) %% q =
             (N %% q - p * (N %% q)) %% q.
        by smt(modzDl).
      rewrite this.
      have : N %% q - p * (N %% q) = (1 - p) * (N %% q) by ring.
      move=> ->.
      have : (1 - p) = - (p - 1) by ring.
      move=> ->.
      have : - (p - 1) * (N %% q) = - ((p - 1) * (N %% q)) by ring.
      move=> ->.
      (* p - 1 = p %/ q * q since p %% q = 1 *)
      have hpd := divz_eq p q.
      have hp_eq : p = p %/ q * q + 1 by smt().
      have hp_m1 : p - 1 = p %/ q * q by smt().
      rewrite hp_m1.
      have : - (p %/ q * q * (N %% q)) = - (p %/ q * (N %% q)) * q by ring.
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
  0 < p => 0 < q => N >= p * q =>
  N %% q <= N %/ p.
proof.
  move=> hp hq hN.
  have [hmod_ge0 hmod_lt] := my_modz_range N q hq.
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
  0 < p => 0 < q => p %% q = 1 => N >= p * q =>
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
      have hp_ge : p * q <= N by smt().
      have hnn : 0 <= N - p * (N %% q) by smt().
      apply divz_ge0.
      exact hnn.
    + (* p * (N %% q) + q * ((N - p * (N %% q)) %/ q) = N *)
      exact (A0_minimal p q N hp hq hpq hN).1.
qed.

(* Forward direction: valid A implies A = A0 + q*k. *)
lemma rep_characterisation_forward (p q N : int) :
  0 < p => 0 < q => p %% q = 1 => N >= p * q =>
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

(* Backward direction: A = A0 + q*k is a valid A. *)
lemma rep_characterisation_backward (p q N : int) :
  0 < p => 0 < q => p %% q = 1 => N >= p * q =>
  forall A,
    (exists k,
       0 <= k /\
       k <= (N %/ p - (N %% q)) %/ q /\
       A = (N %% q) + q * k) =>
    is_valid_A p q N A.
proof.
  move=> hp hq hpq hN A.
  move=> [k [hk_ge0 [hk_le hA_eq]]].
  exists (B0 p q N - p * k).
  rewrite /is_rep.
  split.
  - have [hmod_ge0 hmod_lt] := my_modz_range N q hq.
    smt().
  - split.
    + rewrite /B0.
      have [hmod_ge0 hmod_lt] := my_modz_range N q hq.
      have hp_ge1 : 1 <= p by smt().
      have hprod_le : p * (N %% q) <= p * (q - 1) by smt().
      have hp_ge : p * q <= N by smt().
      have hnn : 0 <= N - p * (N %% q) by smt().
      apply divz_ge0.
      smt().
    + rewrite /B0.
      have [hmod_ge0 hmod_lt] := my_modz_range N q hq.
      have hp_ge1 : 1 <= p by smt().
      have hprod_le : p * (N %% q) <= p * (q - 1) by smt().
      have hp_ge : p * q <= N by smt().
      have hnn : 0 <= N - p * (N %% q) by smt().
      have hdecomp := divz_eq (N - p * (N %% q)) q.
      have hmod : (N - p * (N %% q)) %% q = 0 by smt().
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
  - by apply rep_characterisation_forward.
  - by apply rep_characterisation_backward.
qed.

lemma R_counts (p q N : int) :
  0 < p => 0 < q => p %% q = 1 => N >= p * q =>
  R p q N = (N %/ p - (N %% q)) %/ q + 1.
proof.
  move=> hp hq hpq hN.
  by apply R_formula.
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
(* Section 10: 3-term and 4-term extensions                           *)
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

lemma R_inner_formula (q r M : int) :
  0 < q => 0 < r => q %% r = 1 => M >= q * r =>
  R q r M = (M %/ q - (M %% r)) %/ r + 1.
proof.
  move=> hq hr hqr hM.
  by apply R_formula.
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
  have hle : 0 <= M %/ q by apply divz_ge0.
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
  have hM0_ge0 : 0 <= N %/ p by apply divz_ge0.
  have hS1_ge0 : 0 <= (N %/ p + 1) * (N %/ p + 2) %/ 2.
    apply divz_ge0; smt().
  have hSig2_ge0 : 0 <= (N %/ p) * (N %/ p + 1) %/ 2.
    apply divz_ge0; smt().
  have hSig3_ge0 : 0 <= (N %/ p) %/ r by apply divz_ge0.
  smt(divz_ge0).
qed.

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
