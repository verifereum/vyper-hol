Theory exprSimAbiEncodeTranslatedResult
Ancestors
  exprSimAbiEncodeTranslatedCounted exprSimAbiEncodeNonwordResult
  exprSimAbiEncodeBytesOwnership exprSimAbiEncodeCapacity
  abiBuiltinEncodeSource vyperTypeInvariants vyperTypeSystem vyperAST exprSimHypsDefs
  exprSimAbiEncodeSourceMetadata abiBuiltinEncodeMethod valueEncoding
  valueEncodingProps abiBuiltinEncodeRun loweringPosts exprBopSimProps
  exprSimAbiEncodeOriginFrame vyperState vyperInterpreter

Theorem abi_encode_translated_success_suffix:
  expr_post ctx func ce cx e es origin sa s0 es' v op s /\
  expr_body_pre ce cx env e es /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid0) ty [e]) es /\
  mid = OPTION_MAP bytes_method_id_word mid0 /\
  ~is_word_type (expr_type e) /\
  ei = type_to_abi_enc_info ce.ce_struct_fields ce (lowered_value_type ce e) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\ value_has_type tv v /\
  vyper_to_abi (get_tenv cx) (lowered_value_type ce e) v = SOME av /\
  lower_abi_encode F mid op ei (abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)) sa = (out,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  (!l. op <> Label l) /\ (!x. op = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (sa.cs_blocks = sb.cs_blocks \/ sb.cs_current_insts <> [] \/
   !bb. lookup_block sb.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  local_ptrs_reserved ce origin /\ origin.cs_next_var <= sa.cs_next_var /\
  origin.cs_next_id <= sa.cs_next_id /\ MAP FDOM es.scopes = MAP FDOM es'.scopes ==>
  ?actual.
    gas_marked_path F ctx func s 0 (OK actual) /\
    ~actual.vs_halted /\ actual.vs_current_bb = sb.cs_current_bb /\
    actual.vs_inst_idx = LENGTH sb.cs_current_insts /\
    vv_post ctx func ce cx (TypeBuiltin ann (AbiEncode F mid0) ty [e])
      es origin sb s0 es'
      (Value (BytesV (abi_encode_method_id_bytes mid0 ++
        enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av)))
      (LocatedValue (expr_type (TypeBuiltin ann (AbiEncode F mid0) ty [e]))
        <|ptr_operand := out; ptr_location := LocMemory|>) actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_translated_counted_suffix >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_encode_nonword_origin_frame >> strip_tac >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    metis_tac[exprSimHypsTheory.expr_body_pre_lowered_fits] >>
  `?stv. evaluate_type (get_tenv cx) (expr_type e) = SOME stv` by
    metis_tac[optionTheory.IS_SOME_EXISTS,
      exprSimHypsTheory.expr_body_pre_type_evaluates] >>
  `vyper_to_abi_type (get_tenv cx) (lowered_value_type ce e) =
   vyper_to_abi_type (get_tenv cx) (expr_type e)` by
    metis_tac[exprSimAbiEncodeArgsPhysicalCapacityTheory.abi_args_fits_abi_type] >>
  `vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av` by
    metis_tac[exprSimAbiEncodeArgsPhysicalCapacityTheory.abi_args_fits_conversion] >>
  fs[] >>
  drule_all abi_encode_nonword_result_bound >> strip_tac >>
  drule_all abi_encode_nonword_numerical_capacity >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `well_typed_type_builtin_args (AbiEncode F mid0) ty [expr_type e]` by
    fs[expr_body_pre_def, well_typed_expr_def] >>
  `val_in_memory (BaseTV (BytesT (Dynamic N)))
    (BytesV (abi_encode_method_id_bytes mid0 ++
      enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av)) p actual.vs_memory` by
    (irule abi_encode_nonword_result_memory >>
     conj_tac >- (qexists_tac `mid` >> gvs[]) >>
     metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `FLOOKUP actual.vs_allocas sa.cs_next_id = SOME(p,outsz)` >>
  `!name b n. local_region ce es'.scopes actual name b n ==> p+outsz <= b \/ b+n <= p` by
    (rpt strip_tac >> drule_all abi_encode_row_local_exclusion >> simp[]) >>
  drule abi_encode_strict_id_growth >> strip_tac >>
  qexists_tac `actual` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule abi_encode_bytes_vv_post >>
  goal_assum (drule_at Any) >>
  simp[read_result_def, return_def] >>
  qexistsl_tac [`sa.cs_next_id`, `p`, `outsz`] >>
  `p < dimword (:256)` by decide_tac >>
  simp[] >>
  Cases_on `mid0` >> gvs[abi_encode_method_id_bytes_def, Abbr `outsz`] >>
  fs[well_typed_type_builtin_args_def] >> metis_tac[]
QED
