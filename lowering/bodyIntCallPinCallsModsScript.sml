Theory bodyIntCallPinCallsMods
Ancestors
  exprLowering compileEnv
Libs
  monadsyntax

(* Compare the complete compiler actions, including the returned state.
   Each callback equation is at the two pins of the same environment. *)

Theorem pin_call_mem_bytes[local]:
  type_memory_bytes (ce with ce_module := src) ty = type_memory_bytes ce ty
Proof
  irule type_memory_bytes_struct_fields >> simp[]
QED

Theorem pin_call_elem_size[local]:
  elem_size_in_location (ce with ce_module := src) loc =
  elem_size_in_location ce loc
Proof
  simp[FUN_EQ_THM, elem_size_in_location_def, pin_call_mem_bytes]
QED

Theorem pin_call_materialize[local]:
  unwrap_value (ce with ce_module := src) = unwrap_value ce /\
  compile_store_memory (ce with ce_module := src) = compile_store_memory ce ==>
  compile_materialize_vv (ce with ce_module := src) = compile_materialize_vv ce
Proof
  strip_tac >> simp[FUN_EQ_THM, compile_materialize_vv_def, pin_call_mem_bytes]
QED

Theorem pin_call_snapshot:
  unwrap_value (ce with ce_module := src) = unwrap_value ce /\
  compile_store_memory (ce with ce_module := src) = compile_store_memory ce ==>
  compile_snapshot_vv (ce with ce_module := src) = compile_snapshot_vv ce
Proof
  strip_tac >> drule_all pin_call_materialize >> strip_tac >>
  simp[FUN_EQ_THM, compile_snapshot_vv_def]
QED

Theorem compile_subscript_module_pin_cong:
  f (ce with ce_module := src) = g ce /\
  lower_value f (ce with ce_module := src) = lower_value g ce /\
  compile_snapshot_vv (ce with ce_module := src) = compile_snapshot_vv ce /\
  place_type (ce with ce_module := src) = place_type ce ==>
  compile_subscript f (ce with ce_module := src) rt ty base_e idx =
  compile_subscript g ce rt ty base_e idx
Proof
  strip_tac >>
  simp[compile_subscript_def, copies_subscript_base_def, pin_call_elem_size]
QED

Theorem compile_attribute_module_pin_cong:
  f (ce with ce_module := src) = g ce ==>
  compile_attribute f (ce with ce_module := src) rt ty base_e fld =
  compile_attribute g ce rt ty base_e fld
Proof
  strip_tac >> simp[compile_attribute_def]
QED

Theorem compile_get_target_ptr_module_pin_cong:
  lower_value f (ce with ce_module := src) = lower_value g ce ==>
  !t. compile_get_target_ptr f (ce with ce_module := src) t =
      compile_get_target_ptr g ce t
Proof
  strip_tac >> gen_tac >> measureInduct_on `base_assignment_target_size t` >>
  Cases_on `t` >> gs[vyperASTTheory.expr_size_def] >>
  simp[compile_get_target_ptr_def, pin_call_elem_size]
QED

Theorem pin_call_keyword[local]:
  f (ce with ce_module := src) = g ce /\
  lower_value f (ce with ce_module := src) = lower_value g ce /\
  lowered_value_type (ce with ce_module := src) = lowered_value_type ce /\
  compile_materialize_vv (ce with ce_module := src) = compile_materialize_vv ce ==>
  compile_ext_call_kwarg f (ce with ce_module := src) rt k e =
  compile_ext_call_kwarg g ce rt k e
Proof
  strip_tac >> simp[compile_ext_call_kwarg_def]
QED

Theorem compile_ext_call_kwargs_module_pin_cong:
  f (ce with ce_module := src) = g ce /\
  lower_value f (ce with ce_module := src) = lower_value g ce /\
  lowered_value_type (ce with ce_module := src) = lowered_value_type ce /\
  unwrap_value (ce with ce_module := src) = unwrap_value ce /\
  compile_store_memory (ce with ce_module := src) = compile_store_memory ce ==>
  !rt ks es. compile_ext_call_kwargs f (ce with ce_module := src) rt ks es =
             compile_ext_call_kwargs g ce rt ks es
Proof
  strip_tac >> drule_all pin_call_materialize >> strip_tac >>
  drule_all pin_call_keyword >> strip_tac >>
  gen_tac >> Induct >> simp[compile_ext_call_kwargs_def] >>
  rpt strip_tac >> rename1 `compile_ext_call_kwargs _ _ _ (_::_) es` >>
  Cases_on `es` >> simp[compile_ext_call_kwargs_def]
QED

Theorem pin_call_target_mutate[local]:
  call_can_mutate (ce with ce_module := src) ct = call_can_mutate ce ct
Proof
  Cases_on `ct` >> simp[call_can_mutate_def]
QED

Theorem pin_call_mutate[local]:
  (!ce e. expr_can_mutate (ce with ce_module := src) e = expr_can_mutate ce e) /\
  (!ce es. exprs_can_mutate (ce with ce_module := src) es = exprs_can_mutate ce es) /\
  (!ce opt. opt_expr_can_mutate (ce with ce_module := src) opt = opt_expr_can_mutate ce opt) /\
  (!ce kes. named_exprs_can_mutate (ce with ce_module := src) kes =
            named_exprs_can_mutate ce kes)
Proof
  ho_match_mp_tac expr_can_mutate_ind >> rpt strip_tac >>
  once_rewrite_tac[expr_can_mutate_def] >> gs[pin_call_target_mutate]
QED

Theorem pin_call_ext_args[local]:
  f (ce with ce_module := src) = g ce /\
  compile_snapshot_vv (ce with ce_module := src) = compile_snapshot_vv ce ==>
  !kw tys es. compile_ext_call_args f (ce with ce_module := src) kw tys es =
              compile_ext_call_args g ce kw tys es
Proof
  strip_tac >> gen_tac >> Induct >> simp[compile_ext_call_args_def] >>
  rpt strip_tac >> rename1 `compile_ext_call_args _ _ _ (_::_) es` >>
  Cases_on `es` >> simp[compile_ext_call_args_def, pin_call_mutate]
QED

Theorem compile_call_ext_module_pin_cong:
  f (ce with ce_module := src) = g ce /\
  lower_value f (ce with ce_module := src) = lower_value g ce /\
  lowered_value_type (ce with ce_module := src) = lowered_value_type ce /\
  unwrap_value (ce with ce_module := src) = unwrap_value ce /\
  compile_store_memory (ce with ce_module := src) = compile_store_memory ce /\
  type_to_abi_dec_info ce.ce_struct_fields (ce with ce_module := src) =
    type_to_abi_dec_info ce.ce_struct_fields ce /\
  compile_external_call_kwargs (ce with ce_module := src) =
    compile_external_call_kwargs ce ==>
  compile_call f (ce with ce_module := src) rt ty (ExtCall static skip (nm,tys,rty) ks)
    es d st =
  compile_call g ce rt ty (ExtCall static skip (nm,tys,rty) ks) es d st
Proof
  strip_tac >>
  drule_all pin_call_snapshot >> strip_tac >>
  drule_all pin_call_ext_args >> strip_tac >>
  drule_all compile_ext_call_kwargs_module_pin_cong >> strip_tac >>
  Cases_on `es` >> simp[compile_call_def, pin_call_mem_bytes]
QED

Theorem compile_call_other_module_pin_cong:
  lower_value f (ce with ce_module := src) = lower_value g ce /\
  compile_multi_exprs f (ce with ce_module := src) = compile_multi_exprs g ce /\
  (!rt ks es. compile_ext_call_kwargs f (ce with ce_module := src) rt ks es =
              compile_ext_call_kwargs g ce rt ks es) /\
  (!fid. ct <> IntCall fid) /\
  (!static skip sig ks. ct <> ExtCall static skip sig ks) /\
  (!ck salt rof kws. ct <> CreateTarget ck salt rof kws) ==>
  compile_call f (ce with ce_module := src) rt ty ct es d st =
  compile_call g ce rt ty ct es d st
Proof
  Cases_on `ct` >> simp[] >> rpt strip_tac >> simp[compile_call_def]
QED

Theorem pin_call_create_ctor[local]:
  f (ce with ce_module := src) = g ce /\
  lowered_value_type (ce with ce_module := src) = lowered_value_type ce /\
  compile_snapshot_vv (ce with ce_module := src) = compile_snapshot_vv ce ==>
  !es. compile_create_ctor_args f (ce with ce_module := src) es =
       compile_create_ctor_args g ce es
Proof
  strip_tac >> Induct >> simp[compile_create_ctor_args_def, pin_call_mutate]
QED

Theorem pin_call_create_bytecode[local]:
  compile_create_snapshot (ce with ce_module := src) = compile_create_snapshot ce
Proof
  simp[FUN_EQ_THM, compile_create_snapshot_def, pin_call_mem_bytes]
QED

Theorem pin_call_create_blueprint[local]:
  f (ce with ce_module := src) = g ce /\
  lowered_value_type (ce with ce_module := src) = lowered_value_type ce /\
  unwrap_value (ce with ce_module := src) = unwrap_value ce /\
  compile_snapshot_vv (ce with ce_module := src) = compile_snapshot_vv ce /\
  (!es. compile_create_ctor_args f (ce with ce_module := src) es =
        compile_create_ctor_args g ce es) /\
  (!dst vs tys. compile_abi_encode_values_to_buf (ce with ce_module := src) dst (ZIP (vs,tys)) =
                compile_abi_encode_values_to_buf ce dst (ZIP (vs,tys))) ==>
  compile_create_blueprint_args f (ce with ce_module := src) raw later es =
  compile_create_blueprint_args g ce raw later es
Proof
  strip_tac >> Cases_on `raw` >- (
    Cases_on `es` >> simp[compile_create_blueprint_args_def] >>
    Cases_on `t` >> simp[compile_create_blueprint_args_def, pin_call_mutate]) >>
  simp[compile_create_blueprint_args_def]
QED

Theorem pin_call_create_salt[local]:
  lower_value f (ce with ce_module := src) = lower_value g ce ==>
  !o'. compile_create_salt f (ce with ce_module := src) o' = compile_create_salt g ce o'
Proof
  strip_tac >> Cases >> simp[compile_create_salt_def]
QED

Theorem pin_call_create_raw[local]:
  f (ce with ce_module := src) = g ce /\
  lower_value f (ce with ce_module := src) = lower_value g ce /\
  lowered_value_type (ce with ce_module := src) = lowered_value_type ce /\
  (!es. compile_create_ctor_args f (ce with ce_module := src) es =
        compile_create_ctor_args g ce es) /\
  (!salt. compile_create_salt f (ce with ce_module := src) salt =
          compile_create_salt g ce salt) /\
  (!dst vs tys. compile_abi_encode_values_to_buf (ce with ce_module := src) dst (ZIP (vs,tys)) =
                compile_abi_encode_values_to_buf ce dst (ZIP (vs,tys))) ==>
  compile_raw_create f (ce with ce_module := src) b v es salt rof =
  compile_raw_create g ce b v es salt rof
Proof
  strip_tac >> simp[compile_raw_create_def, pin_call_create_bytecode]
QED

Theorem compile_call_create_module_pin_cong:
  f (ce with ce_module := src) = g ce /\
  lower_value f (ce with ce_module := src) = lower_value g ce /\
  lowered_value_type (ce with ce_module := src) = lowered_value_type ce /\
  unwrap_value (ce with ce_module := src) = unwrap_value ce /\
  compile_store_memory (ce with ce_module := src) = compile_store_memory ce /\
  compile_abi_encode_payload (ce with ce_module := src) = compile_abi_encode_payload ce ==>
  compile_call f (ce with ce_module := src) rt ty (CreateTarget ck salted rof kws) es d st =
  compile_call g ce rt ty (CreateTarget ck salted rof kws) es d st
Proof
  strip_tac >>
  `!dst vs tys. compile_abi_encode_values_to_buf (ce with ce_module := src) dst (ZIP (vs,tys)) =
                compile_abi_encode_values_to_buf ce dst (ZIP (vs,tys))` by (
    qpat_assum `compile_abi_encode_payload _ = _` mp_tac >>
    simp[FUN_EQ_THM, compile_abi_encode_payload_def] >>
    disch_then (qspec_then `F` mp_tac) >> simp[]) >>
  drule_all pin_call_snapshot >> strip_tac >>
  drule_all pin_call_create_ctor >> strip_tac >>
  drule pin_call_create_salt >> strip_tac >>
  drule_all pin_call_create_raw >> strip_tac >>
  drule_all pin_call_create_blueprint >> strip_tac >>
  Cases_on `es` >> simp[compile_call_def, compile_create_call_def] >>
  Cases_on `t` >> simp[compile_create_call_def] >>
  Cases_on `ck` >> simp[]
QED
