(* TOP-LEVEL: checked static tuple payloads fit the actual compiler ABI
   allocation. The exact bound is the evaluated source memory footprint.
   Helpers remove dynamic tails only when every field is static. *)
Theory abiStaticBounds
Ancestors
  abiTypeWidths abiTypeShape abiLogPackingReady typeLayoutProps typedCopyProducer
  context compileEnv compileVyper valueEncoding vyperTypeContract
  vyperABI vyperValue contractABI list arithmetic

Theorem abi_static_tail_lengths:
  !tys sfields.
    ~EXISTS (is_abi_dynamic sfields) tys ==>
    SUM (MAP (\ty. abi_embedded_static_size sfields ty +
      (if is_abi_dynamic sfields ty then abi_size_bound sfields ty else 0)) tys) =
      SUM (MAP (abi_embedded_static_size sfields) tys)
Proof
  Induct_on `tys` >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspec_then `sfields` mp_tac) >> simp[]
QED

Theorem abi_static_tuple_bound:
  !sfields tys.
    ~EXISTS (is_abi_dynamic sfields) tys ==>
    abi_size_bound sfields (TupleT tys) = SUM (MAP (abi_embedded_static_size sfields) tys)
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [Once abi_size_bound_def] >>
  drule_all abi_static_tail_lengths >> simp[]
QED

Theorem evaluated_static_tuple_abi_bound:
  !tenv sfields tys tvs.
    abi_struct_env_rel tenv sfields /\ LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys tvs /\
    ~EXISTS (\ty. is_dynamic (vyper_to_abi_type tenv ty)) tys ==>
    abi_size_bound sfields (TupleT tys) = type_memory_size_list tvs
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`tenv`, `tys`, `sfields`, `tvs`] (CONJUNCT2 abi_type_dynamic_joint)) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  `EXISTS (is_abi_dynamic sfields) tys = EXISTS (\ty. is_dynamic (vyper_to_abi_type tenv ty)) tys` by
    (irule abi_dynamic_exists >> simp[]) >>
  `~EXISTS (is_abi_dynamic sfields) tys` by asm_simp_tac bool_ss [] >>
  drule_all abi_static_tuple_bound >> DISCH_TAC >>
  drule_all evaluated_static_embedded_list_width >> simp[]
QED

Theorem checked_static_tuple_capacity:
  !tops dep layouts addr art tys tvs.
    check_contract dep layouts addr [(NONE,tops)] = SOME art /\
    LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) tys tvs /\
    ~EXISTS (\ty. is_dynamic (vyper_to_abi_type (type_env tops) ty)) tys ==>
    abi_size_bound (make_struct_fields_map tops) (TupleT tys) = type_memory_size_list tvs /\
    type_memory_size_list tvs <= MAX 32 (abi_size_bound (make_struct_fields_map tops) (TupleT tys))
Proof
  rpt gen_tac >> strip_tac >> drule checked_contract_struct_args_unique >> DISCH_TAC >>
  drule abi_struct_env_rel_tops >> DISCH_TAC >>
  drule_all evaluated_static_tuple_abi_bound >> DISCH_TAC >> simp[]
QED

Theorem checked_log_static_capacity:
  !tops dep layouts addr art cenv flags args fts ftvs.
    check_contract dep layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    LENGTH flags = LENGTH args /\ LIST_REL event_arg_compatible fts (MAP SND args) /\
    LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) fts ftvs /\
    ~EXISTS (\ty. is_dynamic (vyper_to_abi_type (type_env tops) ty)) (log_non_indexed_types flags fts) ==>
    abi_size_bound cenv.ce_struct_fields (TupleT (log_non_indexed_types flags fts)) =
      type_memory_size_list (select_log_args F flags ftvs) /\
    type_memory_size_list (select_log_args F flags ftvs) <=
      MAX 32 (abi_size_bound cenv.ce_struct_fields (TupleT (log_non_indexed_types flags fts)))
Proof
  rpt gen_tac >> strip_tac >> drule_all log_non_indexed_evaluate_types >> DISCH_TAC >>
  drule_all checked_static_tuple_capacity >> simp[]
QED
