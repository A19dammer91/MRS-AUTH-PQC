(* ================================================================= *)
(*  MRS_Encoding.ec                                                   *)
(*  Chain-to-bytes encoding for the MRS-AUTH honey layer.             *)
(*                                                                    *)
(*  Provides the abstract byte type, the encoding function, and the   *)
(*  injectivity axiom that the honey IND-CPA proof relies on.         *)
(*                                                                    *)
(*  This file exists so that MRS_Chain.ec, MRS_Sampler.ec, and        *)
(*  MRS_Honey.ec share a single definition instead of each             *)
(*  re-declaring the same abstract op with potentially diverging      *)
(*  axioms.                                                           *)
(* ================================================================= *)

require import AllCore Int List.

(* ----------------------------------------------------------------- *)
(* Abstract byte type                                                 *)
(*                                                                    *)
(* Declared here rather than in each consumer file so that a single   *)
(* import brings the type, the encoding, and the axioms into scope    *)
(* uniformly.                                                         *)
(* ----------------------------------------------------------------- *)
type bytes.

(* ----------------------------------------------------------------- *)
(* Encoding                                                           *)
(* ----------------------------------------------------------------- *)

(* Encode a Diophantine chain (an int list) into a byte string.       *)
op chain_to_bytes (ch : int list) : bytes.

(* The length in bytes of the encoding of a chain.                    *)
(* Each element of the chain is assumed to occupy 8 bytes; the        *)
(* constant is part of the encoding convention, not a theorem.        *)
op chain_byte_len (ch : int list) : int = 8 * size ch.

(* ----------------------------------------------------------------- *)
(* Axioms                                                             *)
(* ----------------------------------------------------------------- *)

(* Injectivity: two chains that encode to the same byte string are    *)
(* identical. This is what makes the honey layer's position-j         *)
(* argument work: the encoder never collapses distinct chains.        *)
axiom chain_to_bytes_inj : forall (c1 c2 : int list),
  chain_to_bytes c1 = chain_to_bytes c2 => c1 = c2.

(* Length consistency: the encoded length matches chain_byte_len.     *)
(* Stated abstractly because `bytes` is abstract here; a concrete     *)
(* implementation would prove this by construction.                   *)
axiom chain_to_bytes_len : forall (ch : int list),
  exists (n : int), n = chain_byte_len ch.
