(* ============================================================ *)
(* MRS FRAMEWORK                                                *)
(* Multi Representation System                                  *)
(* General parameters p and q                                   *)
(* Primary instance: p = 19, q = 9                              *)
(* ============================================================ *)

(* ------------------------------------------------------------ *)
(* 1. DIGITAL ROOT AND MODULAR RESIDUE                          *)
(* ------------------------------------------------------------ *)

(* Digital root in the range 1,...,q for positive N and q. *)
op dr_q (q N : int) : int =
  1 + ((N - 1) %% q).

(* Ordinary modular residue: always in the range 0,...,q-1. *)
op residue_q (q N : int) : int =
  N %% q.

(* The digital root for the primary modulus 9. *)
op dr_9 (N : int) : int =
  dr_q 9 N.

(* ------------------------------------------------------------ *)
(* 2. FIRST REQUIRED VALUE AND REPRESENTATION                   *)
(* ------------------------------------------------------------ *)

(* A0 is the ordinary modular residue. *)
op A0 (q N : int) : int =
  N %% q.

(* The first positive representative of the residue class. *)
op Astart (q N : int) : int =
  dr_q q N.

(* A representation of N by p*A + q*B. *)
pred is_rep (p q N A B : int) =
  1 <= A /\
  0 <= B /\
  p * A + q * B = N.

(* A candidate A-value for the system p*A + q*B = N. *)
pred is_valid_A (p q N A : int) =
  1 <= A /\
  p * A <= N /\
  (N - p * A) %% q = 0.

(* ------------------------------------------------------------ *)
(* 3. BASIC MODULAR PROPERTIES                                  *)
(* ------------------------------------------------------------ *)

lemma residue_q_def (q N : int) :
  residue_q q N = N %% q.
proof.
  by rewrite /residue_q.
qed.

lemma A0_def (q N : int) :
  A0 q N = N %% q.
proof.
  by rewrite /A0.
qed.

lemma dr_9_def (N : int) :
  dr_9 N = dr_q 9 N.
proof.
  by rewrite /dr_9.
qed.

(* The digital root is congruent to N modulo q. *)
lemma dr_q_cong (q N : int) :
  0 < q =>
  0 < N =>
  (dr_q q N - N) %% q = 0.
proof.
  move=> hq hN.
  rewrite /dr_q.
  have hNdiv :
    N = (N %/ q) * q + N %% q
    by smt(divz_eq).
  have hprevdiv :
    N - 1 = ((N - 1) %/ q) * q + (N - 1) %% q
    by smt(divz_eq).
  smt().
qed.

(* Specialization to the modulus 9. *)
lemma dr_9_cong (N : int) :
  0 < N =>
  (dr_9 N - N) %% 9 = 0.
proof.
  move=> hN.
  have hq : 0 < 9 by smt().
  have h := dr_q_cong 9 N.
  smt().
qed.

(* The digital root lies between 1 and q. *)
lemma dr_q_range (q N : int) :
  0 < q =>
  0 < N =>
  1 <= dr_q q N /\ dr_q q N <= q.
proof.
  move=> hq hN.
  rewrite /dr_q.
  have hmod :
    0 <= (N - 1) %% q < q
    by smt().
  smt().
qed.

(* For modulus 9, the digital root lies between 1 and 9. *)
lemma dr_9_range (N : int) :
  0 < N =>
  1 <= dr_9 N /\ dr_9 N <= 9.
proof.
  move=> hN.
  have h := dr_q_range 9 N.
  smt().
qed.

(* The ordinary residue is zero exactly when q divides N. *)
lemma residue_zero_iff (q N : int) :
  0 < q =>
  (N %% q = 0 <=> exists k, N = k * q).
proof.
  move=> hq.
  smt(divz_eq).
qed.

(* ------------------------------------------------------------ *)
(* 4. DIGITAL ROOT VERSUS ORDINARY RESIDUE                      *)
(* ------------------------------------------------------------ *)

(* For positive N, the digital root equals the ordinary residue
   when the residue is nonzero. When the residue is zero,
   the digital root is q. *)
lemma dr_q_residue_cases (q N : int) :
  0 < q =>
  0 < N =>
  (N %% q <> 0 => dr_q q N = N %% q) /\
  (N %% q = 0 => dr_q q N = q).
proof.
  move=> hq hN.
  rewrite /dr_q.
  have hNdiv :
    N = (N %/ q) * q + N %% q
    by smt(divz_eq).
  have hprevdiv :
    N - 1 = ((N - 1) %/ q) * q + (N - 1) %% q
    by smt(divz_eq).
  split.
  - move=> hrem.
    smt().
  - move=> hrem.
    smt().
qed.

(* ------------------------------------------------------------ *)
(* 5. REPRESENTATION IDENTITIES                                 *)
(* ------------------------------------------------------------ *)

lemma is_rep_equation (p q N A B : int) :
  is_rep p q N A B =>
  p * A + q * B = N.
proof.
  rewrite /is_rep.
  smt().
qed.

lemma is_rep_bounds (p q N A B : int) :
  is_rep p q N A B =>
  1 <= A /\ 0 <= B.
proof.
  rewrite /is_rep.
  smt().
qed.

lemma is_rep_implies_valid_A (p q N A B : int) :
  0 < q =>
  p * A + q * B = N =>
  1 <= A =>
  0 <= B =>
  is_valid_A p q N A.
proof.
  move=> hq hEq hA hB.
  rewrite /is_valid_A.
  split.
  - smt().
  split.
  - smt().
  - rewrite hEq.
    have hmod : (q * B) %% q = 0
      by smt(divz_eq).
    smt().
qed.

(* If A is valid, its corresponding B can be obtained by division. *)
op B_from_A (p q N A : int) : int =
  (N - p * A) %/ q.

lemma B_from_A_equation (p q N A : int) :
  0 < q =>
  is_valid_A p q N A =>
  p * A + q * B_from_A p q N A = N.
proof.
  move=> hq.
  rewrite /is_valid_A /B_from_A.
  move=> [hA [hbound hmod]].
  have hdiv :
    N - p * A =
      ((N - p * A) %/ q) * q +
      (N - p * A) %% q
    by smt(divz_eq).
  smt().
qed.

lemma is_valid_A_gives_rep (p q N A : int) :
  0 < q =>
  is_valid_A p q N A =>
  0 <= B_from_A p q N A =>
  is_rep p q N A (B_from_A p q N A).
proof.
  move=> hq hvalid hB.
  rewrite /is_rep.
  split.
  - rewrite /is_valid_A in hvalid.
    smt().
  split.
  - exact hB.
  - have hEq := B_from_A_equation p q N A hq hvalid.
    smt().
qed.

(* ------------------------------------------------------------ *)
(* 6. THE PRIMARY (19,9) SYSTEM                                 *)
(* ------------------------------------------------------------ *)

op p19 : int = 19.
op q9  : int = 9.

pred is_rep_19_9 (N A B : int) =
  is_rep 19 9 N A B.

op A0_19_9 (N : int) : int =
  A0 9 N.

op Astart_19_9 (N : int) : int =
  dr_q 9 N.

op B_19_9 (N A : int) : int =
  B_from_A 19 9 N A.

lemma dr_19_9_cong (N : int) :
  0 < N =>
  (Astart_19_9 N - N) %% 9 = 0.
proof.
  move=> hN.
  rewrite /Astart_19_9.
  have h := dr_q_cong 9 N.
  smt().
qed.

lemma A0_19_9_def (N : int) :
  A0_19_9 N = N %% 9.
proof.
  by rewrite /A0_19_9 /A0.
qed.

lemma Astart_19_9_range (N : int) :
  0 < N =>
  1 <= Astart_19_9 N /\ Astart_19_9 N <= 9.
proof.
  move=> hN.
  rewrite /Astart_19_9.
  have h := dr_q_range 9 N.
  smt().
qed.

lemma rep_19_9_equation (N A B : int) :
  is_rep_19_9 N A B =>
  19 * A + 9 * B = N.
proof.
  rewrite /is_rep_19_9 /is_rep.
  smt().
qed.

(* ------------------------------------------------------------ *)
(* 7. REPRESENTATION COUNT FORMULA                              *)
(* ------------------------------------------------------------ *)

(* This is the proposed count formula for N >= 171.
   It is kept separate from the representation predicates so
   that its mathematical domain can be checked independently. *)
op R_19_9 (N : int) : int =
  ((N %/ 19 - dr_q 9 N) %/ 9) + 1.

(* Upper bound on A in every representation. *)
lemma A_upper_bound_19_9 (N A B : int) :
  is_rep_19_9 N A B =>
  19 * A <= N.
proof.
  rewrite /is_rep_19_9 /is_rep.
  smt().
qed.

(* Every representation has A in the residue class of N modulo 9. *)
lemma rep_19_9_congruence (N A B : int) :
  is_rep_19_9 N A B =>
  (A - N) %% 9 = 0.
proof.
  rewrite /is_rep_19_9 /is_rep.
  move=> [hA [hB hEq]].
  have hmod : (9 * B) %% 9 = 0
    by smt(divz_eq).
  have hpmod : (19 * A) %% 9 = A %% 9
    by smt(divz_eq).
  smt().
qed.

(* ------------------------------------------------------------ *)
(* 8. NUMERICAL CHECKS                                          *)
(* ------------------------------------------------------------ *)

lemma dr_9_1991 :
  dr_9 1991 = 2.
proof.
  rewrite /dr_9 /dr_q.
  smt().
qed.

lemma residue_9_1991 :
  A0 9 1991 = 2.
proof.
  rewrite /A0.
  smt().
qed.

lemma dr_9_958 :
  dr_9 958 = 4.
proof.
  rewrite /dr_9 /dr_q.
  smt().
qed.

lemma rep_958_4_98 :
  is_rep_19_9 958 4 98.
proof.
  rewrite /is_rep_19_9 /is_rep.
  smt().
qed.

lemma rep_958_13_79 :
  is_rep_19_9 958 13 79.
proof.
  rewrite /is_rep_19_9 /is_rep.
  smt().
qed.

lemma rep_958_22_60 :
  is_rep_19_9 958 22 60.
proof.
  rewrite /is_rep_19_9 /is_rep.
  smt().
qed.

lemma rep_958_31_41 :
  is_rep_19_9 958 31 41.
proof.
  rewrite /is_rep_19_9 /is_rep.
  smt().
qed.

lemma rep_958_40_22 :
  is_rep_19_9 958 40 22.
proof.
  rewrite /is_rep_19_9 /is_rep.
  smt().
qed.

lemma rep_958_49_3 :
  is_rep_19_9 958 49 3.
proof.
  rewrite /is_rep_19_9 /is_rep.
  smt().
qed.
