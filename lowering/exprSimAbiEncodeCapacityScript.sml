Theory exprSimAbiEncodeCapacity
Ancestors
  exprSimAbiEncodeSourceMetadata abiEncodeEndpointMetadata
  createMemoryInterface exprSimHypsDefs abiBuiltinAllocation words arithmetic

Theorem abi_encode_nonword_output_representable:
  expr_body_pre ce cx env
    (TypeBuiltin ann (AbiEncode F mid) ty [e]) es ==>
  32 + 32 * word_size
    (abi_size_bound ce.ce_struct_fields (expr_type e) +
     (case mid of NONE => 0 | SOME _ => 4)) < dimword (:256)
Proof
  strip_tac >> drule abi_encode_endpoint_output_size >> simp[] >>
  simp[dimword_def] >> decide_tac
QED

Theorem abi_encode_nonword_length_bound:
  expr_body_pre ce cx env e es /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av ==>
  LENGTH (enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av) <=
    abi_size_bound ce.ce_struct_fields (expr_type e)
Proof
  metis_tac[abi_encode_body_evaluated_metadata, create_ctor_encoding_bound]
QED

Theorem abi_encode_payload_capacity:
  n <= maxlen ==>
  32+m+n <= 32+32*word_size (maxlen+m)
Proof
  mp_tac (Q.SPEC `maxlen+m` abi_builtin_word_size_capacity) >> decide_tac
QED

(* Operand typing supplies the length bound; the outer builtin precondition
   independently supplies representability of the rounded output allocation. *)
Theorem abi_encode_nonword_numerical_capacity:
  expr_body_pre ce cx env e es /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid) ty [e]) es /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av ==>
  let bytes = enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av in
  let maxlen = abi_size_bound ce.ce_struct_fields (expr_type e) in
  let m = case mid of NONE => 0 | SOME _ => 4 in
  let outsz = 32+32*word_size (maxlen+m) in
  LENGTH bytes <= maxlen /\ 32+m+LENGTH bytes <= outsz /\
  outsz < dimword (:256) /\ LENGTH bytes+m < dimword (:256) /\
  32+(case mid of NONE => 0 | SOME _ => 32) <= outsz
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_encode_nonword_length_bound >> strip_tac >>
  drule abi_encode_nonword_output_representable >> strip_tac >>
  drule abi_encode_payload_capacity >>
  disch_then (qspec_then `(case mid of NONE => 0 | SOME _ => 4)` assume_tac) >>
  simp[] >> Cases_on `mid` >> simp[] >>
  qspec_then `abi_size_bound ce.ce_struct_fields (expr_type e)` mp_tac
    (GEN_ALL abi_builtin_rounded_selector_store) >> simp[]
QED

(* The remaining address checks depend only on the registered output extent,
   not on a source address. This applies unchanged to the empty-source path. *)
Theorem abi_encode_output_address_bounds:
  n <= maxlen /\
  outsz = 32+32*word_size (maxlen+(case mid of NONE => 0 | SOME _ => 4)) /\
  p+outsz <= next /\ next < dimword (:256) ==>
  p < dimword (:256) /\
  (mid <> NONE ==> p+32 < dimword (:256)) /\
  p+32+(case mid of NONE => 0 | SOME _ => 4)+n <= next
Proof
  strip_tac >>
  qpat_assum `n <= maxlen` (mp_then Any mp_tac abi_encode_payload_capacity) >>
  disch_then (qspec_then `(case mid of NONE => 0 | SOME _ => 4)` assume_tac) >>
  `32 <= outsz` by simp[] >> gvs[] >> decide_tac
QED
