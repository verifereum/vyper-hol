Theory exprSimAbiEncodeNonwordResult
Ancestors
  exprSimAbiEncodeBytesOwnership exprSimAbiEncodeCapacity
  abiBuiltinEncodeSource vyperTypeInvariants vyperTypeSystem vyperAST exprSimHypsDefs
  exprSimAbiEncodeSourceMetadata abiBuiltinEncodeMethod valueEncoding
  valueEncodingProps abiBuiltinEncodeRun loweringPosts exprBopSimProps
  exprSimAbiEncodeNonwordCounted exprSimAbiEncodeOriginFrame
  exprSimAbiEncodeCapacity vyperState vyperInterpreter

Theorem abi_encode_nonword_result_type:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid) ty [e]) es ==>
  ?N. expr_type (TypeBuiltin ann (AbiEncode F mid) ty [e]) =
        BaseT (BytesT (Dynamic N)) /\
      ty = TupleT [expr_type e] /\
      vyper_abi_size_bound (get_tenv cx) (expr_type e) +
        abi_encode_method_id_size mid <= N
Proof
  simp[expr_body_pre_def, well_typed_expr_def, type_builtin_result_ok_def,
    abi_encode_size_ok_def, expr_type_def] >>
  strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  gvs[]
QED

Theorem abi_encode_nonword_result_bound:
  expr_body_pre ce cx env e es /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid) ty [e]) es /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av ==>
  ?N. expr_type (TypeBuiltin ann (AbiEncode F mid) ty [e]) =
        BaseT (BytesT (Dynamic N)) /\
      ty = TupleT [expr_type e] /\
      LENGTH (abi_encode_method_id_bytes mid ++
        enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av) <= N
Proof
  strip_tac >> drule_all abi_encode_nonword_length_bound >> strip_tac >>
  drule abi_encode_nonword_result_type >> strip_tac >>
  drule_all abi_encode_body_evaluated_metadata >> strip_tac >>
  qexists_tac `N` >> simp[abi_encode_method_id_size_def] >>
  gvs[abi_encode_method_id_size_def] >> decide_tac
QED

Theorem abi_encode_nonword_result_memory:
  well_typed_type_builtin_args (AbiEncode F mid0) ty [ety] /\
  mid = OPTION_MAP bytes_method_id_word mid0 /\
  mload p actual = n2w (LENGTH bytes + (case mid of NONE => 0 | SOME _ => 4)) /\
  mem_bytes_at (p+32+(case mid of NONE => 0 | SOME _ => 4))
    (LENGTH bytes) actual.vs_memory = bytes /\
  (case mid of NONE => T | SOME selector =>
    mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes selector) ==>
  val_in_memory (BaseTV (BytesT (Dynamic N)))
    (BytesV (abi_encode_method_id_bytes mid0 ++ bytes)) p actual.vs_memory
Proof
  strip_tac >> drule abi_builtin_encode_checked_prefix >> strip_tac >>
  Cases_on `mid`
  >- (Cases_on `mid0` >> gvs[abi_builtin_encode_prefix_def,
        abi_encode_method_id_bytes_def, val_in_memory_def, mem_word_at_eq_mload]) >>
  fs[] >> drule_all abi_builtin_encode_method_value >> strip_tac >>
  Cases_on `mid0` >> gvs[abi_builtin_encode_prefix_def,
    abi_encode_method_id_bytes_def, val_in_memory_def, mem_word_at_eq_mload,
    abi_builtin_encode_method_bytes_length]
QED

Theorem abi_encode_nonword_source_result:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid) ty [e]) es /\
  vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av ==>
  evaluate_type_builtin cx (AbiEncode F mid) ty [expr_type e] [v] =
    INL (BytesV (abi_encode_method_id_bytes mid ++
      enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av))
Proof
  strip_tac >> drule abi_encode_nonword_result_type >> strip_tac >>
  gvs[] >> irule abi_builtin_encode_source_single >> simp[]
QED

Theorem abi_encode_bytes_vv_post:
  expr_type e = BaseT (BytesT (Dynamic N)) /\
  stmt_state_rel ctx func ce cx es' actual /\
  read_result cx result es' = (INL (BytesV payload),es') /\
  eval_operand out actual = SOME (n2w p) /\ p < dimword (:256) /\
  LENGTH payload <= N /\
  val_in_memory (BaseTV (BytesT (Dynamic N))) (BytesV payload) p actual.vs_memory /\
  FLOOKUP actual.vs_allocas aid = SOME(p,sz) /\
  origin.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  32+LENGTH payload <= sz /\
  (!name b n. local_region ce es'.scopes actual name b n ==> p+sz <= b \/ b+n <= p) /\
  wb_frame ce es origin s0 actual ==>
  vv_post ctx func ce cx e es origin sb s0 es' result
    (LocatedValue (expr_type e) <|ptr_operand := out; ptr_location := LocMemory|>) actual
Proof
  strip_tac >> simp_tac bool_ss [vv_post_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (simp[] >> irule abi_encode_bytes_vv_holds >>
    goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >- (simp[] >> irule abi_encode_bytes_vv_at >>
    goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  fs[wb_frame_def] >> first_assum ACCEPT_TAC
QED

Theorem abi_encode_nonword_success_suffix:
  expr_post ctx func ce cx e es origin sa s0 es' v op s /\
  expr_body_pre ce cx env e es /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid0) ty [e]) es /\
  mid = OPTION_MAP bytes_method_id_word mid0 /\
  ~is_word_type (expr_type e) /\
  abi_enc_plan (get_tenv cx) (expr_type e) ei /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v /\
  vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av /\
  lower_abi_encode F mid op ei (abi_size_bound ce.ce_struct_fields (expr_type e)) sa = (out,sb) /\
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
  drule_all abi_encode_nonword_counted_suffix >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_encode_nonword_origin_frame >> strip_tac >>
  drule_all abi_encode_nonword_result_bound >> strip_tac >>
  drule_all abi_encode_nonword_numerical_capacity >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `well_typed_type_builtin_args (AbiEncode F mid0) ty [expr_type e]` by
    fs[expr_body_pre_def, well_typed_expr_def] >>
  drule_all abi_encode_nonword_result_memory >>
  disch_then (qspec_then `N` assume_tac) >>
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
