Theory abiDecodePtrCallerBounds
Ancestors
  allocLimits supportedTypes compileEnv words list arithmetic venomMemProps

(* A flat tuple needs at most one extra ABI offset word per memory word. *)
Theorem abi_decode_scalar_abi_capacity:
  supported_scalar_type ty ==>
  abi_embedded_static_size sf ty +
    (if is_abi_dynamic sf ty then abi_size_bound sf ty else 0) <=
      2 * type_memory_bytes ce ty
Proof
  Cases_on `ty` >> simp[supported_scalar_type_def,
    supported_word_type_def, supported_string_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[supported_word_type_def, supported_string_type_def]
  >~ [`BytesT bd`] >>> HEADGOAL (Cases_on `bd` >>
       simp[supported_word_type_def, supported_string_type_def]) >>
  simp[abi_embedded_static_size_def, is_abi_dynamic_def,
    abi_size_bound_def, abi_static_size_def, type_memory_bytes_def]
QED

Theorem abi_decode_flat_abi_capacity:
  !tys. EVERY supported_scalar_type tys ==>
  abi_size_bound sf (TupleT tys) <= 2 * type_memory_bytes ce (TupleT tys)
Proof
  Induct >> simp[abi_size_bound_def, type_memory_bytes_def] >>
  rpt strip_tac >> drule abi_decode_scalar_abi_capacity >>
  disch_then (qspecl_then [`sf`,`ce`] mp_tac) >>
  first_x_assum drule >> simp[abi_size_bound_def, type_memory_bytes_def] >>
  decide_tac
QED
