Theory exprSimAbiDecodeBuiltinLayout
Ancestors
  exprSimAbiDecodeMinimumLayout exprSimAbiDecodeBuiltinSource
  abiCallerAbiShape abiCallerAbiBound abiDecoderCoherence
  compileEnv vyperABI contractABI list arithmetic

Theorem abi_decode_coherent_bound:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
    abi_caller_abi_bound sf env ty
Proof
  ho_match_mp_tac abi_decoder_coherent_ind >> rpt conj_tac
  >- simp[abi_caller_abi_bound_base]
  >- (rpt strip_tac >>
      simp[abi_caller_abi_bound_def, is_abi_dynamic_def, abi_static_size_def,
           abi_size_bound_def, vyper_to_abi_type_def, vyper_is_dynamic_def,
           vyper_abi_size_bound_def, is_dynamic_def])
  >- (rpt strip_tac >> irule abi_caller_abi_bound_array >> simp[])
  >- (rpt strip_tac >> irule abi_caller_abi_bound_tuple >>
      gvs[LIST_REL_EL_EQN, EVERY_EL] >> metis_tac[])
  >> rpt strip_tac >> irule abi_caller_abi_bound_struct >>
  qexistsl_tac [`args`, `fields`] >> simp[] >>
  gvs[LIST_REL_EL_EQN, EVERY_EL] >> metis_tac[]
QED

Theorem abi_decode_builtin_guard_reject:
  abi_decoder_coherent ce env sf ty tv /\
  ~(abi_static_size sf ty <= LENGTH bs /\ LENGTH bs <= abi_size_bound sf ty) ==>
  evaluate_abi_decode env ty bs = INR "abi_decode invalid"
Proof
  strip_tac >> drule abi_decode_coherent_minimum >> strip_tac >>
  drule abi_decode_coherent_bound >>
  simp_tac bool_ss [abi_caller_abi_bound_def] >> strip_tac >>
  irule abi_decode_builtin_source_size_reject >> metis_tac[]
QED

Theorem abi_decode_builtin_guard_view:
  abi_decoder_coherent ce env sf ty tv /\
  abi_static_size sf ty <= LENGTH bs /\ LENGTH bs <= abi_size_bound sf ty ==>
  (abi_decode_source_accepts env ty
    (abi_decode_source_view (vyper_to_abi_type env ty) bs 0) v <=>
   evaluate_abi_decode env ty bs = INL v)
Proof
  strip_tac >> drule abi_decode_coherent_minimum >> strip_tac >>
  drule abi_decode_coherent_bound >>
  simp_tac bool_ss [abi_caller_abi_bound_def] >> strip_tac >>
  drule abi_decode_coherent_shape >>
  simp_tac bool_ss [abi_caller_abi_shape_def] >> strip_tac >>
  irule abi_decode_builtin_source_view_window >> simp[] >> metis_tac[LESS_EQUAL_ANTISYM]
QED
