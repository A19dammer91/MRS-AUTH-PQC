(* ================================================================ *)
(* Standalone verification: RustTemporalBarrier                     *)
(* ================================================================ *)

lemma refinement_backward_security (n dm : int) :
  162 < n =>
  hoare [RustTemporalBarrier.sample_with_zeroize :
    N = n /\ deadline_micros = dm ==>
    attacker_obs (rust_to_abstract res) = false \/
    (exists xa xb,
        res = RustValid (xa, xb) /\
        19 * xa + 9 * xb = n /\
        (0 < xb => dr xb = dr (2 * dr n)))].
proof.
  move=> hn.
  conseq (refinement_step1 n dm).
  all: by move=> &m; smt(refinement_pure).
qed.
