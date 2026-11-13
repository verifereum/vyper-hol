(* Memory-safe value simulation of abi_encode's single nonword argument:
   the counted run of bodyMemTbAbiEncodeNonword, S1's result facts, the
   store bound of the bytes result and the allocation history. *)
Theory bodyMemTbAbiEncodeNonwordCase
Ancestors
  bodyMemTbAbiEncodeNonword bodyMemBiSha256Compose exprSimAbiEncodeNonwordCase
  exprSimAbiEncodeNonwordResult exprSimAbiEncodeOriginFrame
  exprSimAbiEncodeBytesOwnership exprSimAbiEncodeCapacity exprSimMemDefs
  fragGasPathFrameMem fragGasMode gasSummary exprSimProps valueEncoding
  exprSimHashBoundary abiBuiltinEncodeCode emitHelper compileEnv
  exprSimHash vyperInterpreter vyperState exprSimSource exprSimWordArgs
  exprLowering exprBopLowering vyperAST list exprSimHypsDefs exprSimDefs
  exprSimAbiEncodeRuntimeInputs vyperTypeCallGraph
  exprLoweringProps exprBopSimProps vyperTypeSystem fragExec vyperContext
  exprSimAbiEncodePrefixWindow vyperTypeABI exprOperandVar loweringPosts
  exprReasonOperand exprSimAbiEncodeOblivious vyperTypeInvariants
  vyperEvalExprPreservesScopesDom loweringStateRelDefs exprSimAbiEncodeExecFrame
  venomState words arithmetic

Theorem abi_encode_bytes_store_bound:
  pr.ptr_operand = out /\ pr.ptr_location = LocMemory /\
  eval_operand out t = SOME (n2w p) /\ p < dimword (:256) /\
  LENGTH payload <= cap /\ p + (32 + 32 * word_size cap) <= t.vs_alloca_next ==>
  vv_store_bound cx (BaseT (BytesT (Dynamic N))) (BaseT (BytesT (Dynamic cap))) es'
    (Value (BytesV payload)) (LocatedValue vt pr) t
Proof
  strip_tac >>
  `word_size (LENGTH payload) <= word_size cap` by
    simp[vfmConstantsTheory.word_size_def, DIV_LE_MONOTONE] >>
  rw[vv_store_bound_def] >>
  gvs[read_result_def, return_def, vyperValueTheory.evaluate_type_def,
    val_store_size_def, type_memory_size_def]
QED

Theorem abi_encode_nonword_success_mem:
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
  (!x. op = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  local_ptrs_reserved ce origin /\ origin.cs_next_var <= sa.cs_next_var /\
  origin.cs_next_id <= sa.cs_next_id /\ MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  alloca_history func s ==>
  ?cnt actual.
    gas_path_mem ctx func s cnt (OK actual) /\
    ~actual.vs_halted /\ actual.vs_current_bb = sb.cs_current_bb /\
    actual.vs_inst_idx = LENGTH sb.cs_current_insts /\
    vv_post ctx func ce cx (TypeBuiltin ann (AbiEncode F mid0) ty [e])
      es origin sb s0 es'
      (Value (BytesV (abi_encode_method_id_bytes mid0 ++
        enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av)))
      (LocatedValue ann (mk_ptr out LocMemory)) actual /\
    vv_store_bound cx ann
      (lowered_value_type ce (TypeBuiltin ann (AbiEncode F mid0) ty [e])) es'
      (Value (BytesV (abi_encode_method_id_bytes mid0 ++
        enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av)))
      (LocatedValue ann (mk_ptr out LocMemory)) actual /\
    alloca_history func actual /\ s.vs_alloca_next <= actual.vs_alloca_next
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_nonword_counted_mem >> strip_tac >>
  drule_all abi_encode_nonword_origin_frame >> strip_tac >>
  `stmt_state_rel ctx func ce cx es' s` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [expr_post_def] >> metis_tac[]) >>
  `alloca_history func actual` by
    (`alloca_inv s` by fs[stmt_state_rel_def] >>
     drule gas_path_mem_allocation_state >>
     disch_then (qspec_then `actual` mp_tac) >> simp[]) >>
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
  `~expr_has_effect e ==> pure_frame ce func es origin s0 actual` by
    (strip_tac >>
     qpat_assum `expr_post _ _ _ _ e _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     `pure_frame ce func es origin s0 s` by
       (qpat_x_assum `~expr_has_effect e ==> _` irule >> first_assum ACCEPT_TAC) >>
     match_mp_tac (Q.SPECL [`ce`, `func`, `es`, `es'`, `origin`, `sa`, `s0`, `s`, `actual`]
                     exprSimPropsTheory.pure_frame_trans) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `p < dimword (:256)` by decide_tac >>
  suspend "post"
QED

Resume abi_encode_nonword_success_mem[post]:
  `vv_post ctx func ce cx (TypeBuiltin ann (AbiEncode F mid0) ty [e])
      es origin sb s0 es'
      (Value (BytesV (abi_encode_method_id_bytes mid0 ++
        enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av)))
      (LocatedValue (expr_type (TypeBuiltin ann (AbiEncode F mid0) ty [e]))
        <|ptr_operand := out; ptr_location := LocMemory|>) actual` by
    (irule abi_encode_bytes_vv_post >>
     goal_assum (drule_at Any) >>
     simp[read_result_def, return_def] >>
     qexistsl_tac [`sa.cs_next_id`, `p`, `outsz`] >>
     simp[] >>
     Cases_on `mid0` >> gvs[abi_encode_method_id_bytes_def, Abbr `outsz`] >>
     fs[well_typed_type_builtin_args_def] >> metis_tac[]) >>
  `lowered_value_type ce (TypeBuiltin ann (AbiEncode F mid0) ty [e]) =
     BaseT (BytesT (Dynamic (abi_size_bound ce.ce_struct_fields (lowered_value_type ce e) +
       (case mid of NONE => 0 | SOME _ => 4))))` by
    (simp[lowered_value_type_def] >> Cases_on `mid0` >> gvs[]) >>
  `ann = BaseT (BytesT (Dynamic N))` by
    (qpat_assum `expr_type (TypeBuiltin _ _ _ _) = _`
       (ACCEPT_TAC o REWRITE_RULE [expr_type_def])) >>
  pop_assum SUBST_ALL_TAC >>
  qexistsl_tac [`cnt`, `actual`] >>
  asm_rewrite_tac[] >>
  conj_tac
  >- (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ (LocatedValue _ _) _` mp_tac >>
      simp[expr_type_def] >>
      match_mp_tac (DISCH_ALL (fst (EQ_IMP_RULE
        (UNDISCH abi_encode_vv_post_pointer_cong)))) >>
      simp[contextTheory.mk_ptr_def]) >>
  irule abi_encode_bytes_store_bound >>
  conj_tac >- (Cases_on `mid0` >>
    gvs[abi_encode_method_id_bytes_def, well_typed_type_builtin_args_def]) >>
  conj_tac >- simp[contextTheory.mk_ptr_def] >>
  qexistsl_tac [`out`, `p`] >>
  simp[contextTheory.mk_ptr_def, Abbr `outsz`] >>
  Cases_on `mid0` >> gvs[]
QED
Finalise abi_encode_nonword_success_mem

Theorem compile_abi_encode_nonword_vv_sim_mem:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid) ty [e]) es /\
  expr_sim_mem ctx func ce cx (expr_type e) e es /\
  ~is_word_type (expr_type e) ==>
  expr_vv_sim_mem ctx func ce cx cty (TypeBuiltin ann (AbiEncode F mid) ty [e]) es
Proof
  strip_tac >> rewrite_tac[expr_vv_sim_mem_def] >> rpt strip_tac >>
  `expr_body_pre ce cx env e es` by
    (irule abi_encode_body_arg_pre >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_abi_encode_nonword_shape] >>
  pairarg_tac >> rename1 `lower_value _ _ _ _ sa = (op,sm)` >>
  simp[] >> simp[as_ptr_val_def] >>
  Cases_on `lower_abi_encode F (OPTION_MAP bytes_method_id_word mid) op
    (type_to_abi_enc_info ce.ce_struct_fields ce (lowered_value_type ce e))
    (abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)) sm` >>
  rename1 `lower_abi_encode _ _ _ _ _ sm = (out,sn)` >>
  simp[as_ptr_val_def] >> strip_tac >> gvs[] >>
  `!l. op <> Label l` by
    (irule lower_compile_expr_not_label >> goal_assum (drule_at Any) >>
     qexists_tac `env` >>
     fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def]) >>
  drule_all lower_abi_encode_frag_facts >> strip_tac >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split] >>
  `local_ptrs_reserved ce sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  `eval_expr cx (TypeBuiltin ann (AbiEncode F mid) ty [e]) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v ee. ((case evaluate_type_builtin cx (AbiEncode F mid) ty [expr_type e] [v] of
        INL w => INL (Value w) | INR err => INR (Error err)),ee))` by
    (irule eval_expr_singleton_type_builtin_action >>
     simp[type_builtin_args_length_ok_def]) >>
  asm_rewrite_tac[] >>
  irule sha256_expr_sim_mem_suffix >>
  first_assum (irule_at (Pat `expr_sim_mem _ _ _ _ _ _ _`)) >>
  first_assum (irule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> Cases_on `exc` >> Cases_on `r` >> simp[expr_exit_def] >>
      rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def]) >>
  rpt strip_tac >>
  suspend "cont"
QED

Resume compile_abi_encode_nonword_vv_sim_mem[cont]:
  `expr_body_pre ce cx env e (es with gas_obs := gs)` by simp[] >>
  drule_at (Pat `bind _ _ _ = _`)
    (CONV_RULE (DEPTH_CONV ETA_CONV) abi_encode_operand_success_type) >>
  disch_then (qspecl_then [`env`,`ce`] mp_tac) >> simp[] >> strip_tac >>
  drule_all (cj 1 vyper_to_abi_total) >> strip_tac >>
  drule_all abi_encode_nonword_source_result >> strip_tac >>
  `!x. op = Var x ==> not_fresh_at sm x` by
    metis_tac[compile_lower_value_var] >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> rpt strip_tac >>
     drule eval_expr_preserves_scopes_dom >> strip_tac >>
     drule read_result_state >> strip_tac >> gvs[]) >>
  drule_at (Pat `bind _ _ _ = _`)
    (CONV_RULE (DEPTH_CONV ETA_CONV) abiEncodeArgsCaseTheory.abi_args_success_ready) >>
  disch_then (qspecl_then [`env`,`ce`] mp_tac) >> simp[] >> strip_tac >>
  `?ptv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME ptv /\
    value_has_type ptv v` by metis_tac[] >>
  drule exprSimHypsTheory.expr_body_pre_physical_type >> strip_tac >>
  `vyper_to_abi (get_tenv cx) (lowered_value_type ce e) v = SOME av` by
    (drule_all (cj 1 exprSimAbiEncodeArgsPhysicalCapacityTheory.abi_args_fits_conversion) >>
     simp[]) >>
  `?cnt actual. gas_path_mem ctx func t cnt (OK actual) /\
    ~actual.vs_halted /\ actual.vs_current_bb = sb.cs_current_bb /\
    actual.vs_inst_idx = LENGTH sb.cs_current_insts /\
    vv_post ctx func ce cx (TypeBuiltin ann (AbiEncode F mid) ty [e])
      es sa sb s0 ee (Value (BytesV (abi_encode_method_id_bytes mid ++
        enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av)))
      (LocatedValue ann (mk_ptr out LocMemory)) actual /\
    vv_store_bound cx ann
      (lowered_value_type ce (TypeBuiltin ann (AbiEncode F mid) ty [e])) ee
      (Value (BytesV (abi_encode_method_id_bytes mid ++
        enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av)))
      (LocatedValue ann (mk_ptr out LocMemory)) actual /\
    alloca_history func actual /\ t.vs_alloca_next <= actual.vs_alloca_next` by
    (irule abi_encode_nonword_success_mem >>
     simp[] >> conj_tac
     >- (qexists_tac `env` >> simp[]) >>
     goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     gvs[]) >>
  `ee with gas_obs := [] = ee` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  qexists_tac `REPLICATE cnt F` >> simp[gas_summary_at_def] >>
  qexistsl_tac [`INL (Value (BytesV (abi_encode_method_id_bytes mid ++
    enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av)))`,
    `ee`, `OK actual`] >>
  simp[gas_marked_exec_def, gas_marked_path_def, expr_type_def]
QED
Finalise compile_abi_encode_nonword_vv_sim_mem
