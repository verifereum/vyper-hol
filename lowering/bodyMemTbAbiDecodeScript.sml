(* Memory case of the body induction for abi_decode (admitted; its own piece). *)
Theory bodyMemTbAbiDecode
Ancestors
  abiDecodeMemTyped abiDecodeMemBuiltinEntry abiDecodeMemBuiltinReject
  abiDecodeMemBuiltinSource abiDecodeMemBuiltinSuccess abiDecodeMemBuiltinCapacity
  abiDecodeMemActualFrame abiDecodeMemMemberReentry abiDecodeMemLayout abiDecodeMemSiteEffect
  exprSimAbiDecodeCallerSuffix exprSimAbiDecodeCompose bodyExprForceMemory
  exprSimAbiDecodeBodySuccess exprSimAbiDecodeInputBound exprSimAbiDecodeReject
  exprSimAbiDecodeResources exprOperandVar exprReasonOperand exprSimAbiDecodeLiveFrame
  exprSimAbiDecodeOblivious exprSimAbiDecodeBodyEntry exprSimAbiDecodeEntryTyping
  exprSimHypsDefs exprSimDefs exprSimHyps exprSimSource exprSafeOperand exprOpenFirstOperand
  exprLowering exprLoweringProps loweringPosts localPtrsProps compileEnv abiDecoderReentry
  abiDecoderSiteEffect gasSummary gasSummaryCompose gasExemptCert gasOutcome gasNormalPrefix
  actualDecoderSites loweringStateRelDefs abiDecoderContract
  fragGasPath fragGasPathMem fragGasMode fragExec venomExecSemantics venomState
  vyperTypeExprSoundness vyperTypeExprResult vyperTypeInvariants vyperTypeSystem
  vyperTyping vyperValue vyperState vyperContext vyperAST words finite_map list arithmetic
  abiDecodeMemPrimitiveReentry abiDecodeMemBytesReentry abiDecodeMemBulkReentry
  abiDecodeMemStaticFrame abiDecodeMemHeaderReject abiDecodeMemNoScratch
  bodyMemoryPreds abiDecodeMemHeader abiDecodeMemAllocationSizes abiDecodeMemArrayBody abiDecodeMemLoopEntry abiDecodeMemArrayHeaderFrame abiDecodeMemArrayEntry abiDecodeMemLoopIteration abiDecodeMemArraySetup abiDecodeMemIndexedSetup abiDecodeMemElementReentry abiDecodeMemMembers abiDecodeMemLoopControl abiDecodeMemElementPointer abiDecodeMemMemberPointer abiDecodeMemReentry abiDecodeMemScratch abiDecodeMemBulkExecution abiDecodeMemBulkBody abiDecodeMemBulkPrefix abiDecodeMemBulk abiDecodeMemRange abiDecodeMemOperand abiDecodeMemPrimitive abiDecodeMemBytes abiDecodeMemBytesGuards abiDecodeMemCountGuard

(* The conditional assembly uses exactly the checked canonical decoder boundary.
   These ML terms introduce no HOL constants or assumed theorems. *)
val (decoder_scalar_pre, decoder_result) =
  dest_imp (snd (strip_forall (concl abi_decode_typed_scalar_memory)));
val (decoder_entry, _) = dest_conj decoder_scalar_pre;
val decoder_implication = mk_imp (decoder_entry, decoder_result);
val decoder_parameters = ["ctx", "func", "limit", "base_op", "hi", "B", "P", "H",
  "snap", "keep_word", "ce", "env", "sf", "ty", "tv", "dst", "src", "st", "fin",
  "s", "sb", "d"];
val decoder_contract = list_mk_forall
  (map (fn name => valOf (List.find (fn v => fst (dest_var v) = name)
    (free_vars decoder_implication))) decoder_parameters, decoder_implication);

Theorem abi_decode_mem_builtin_outcome_conditional[local]:
  ^decoder_contract ==>
  lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) st = (out,fin) /\
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  assignable_type env ty /\ abi_decode_bytes_widths env ty /\ fn_has_code st fin func /\
  abi_builtin_decode_site_resources ctx func st fin.cs_next_id
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) (LENGTH bs) p d s /\
  val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) p s.vs_memory /\
  eval_operand data s = SOME(n2w p) /\ alloca_history func s /\
  abi_decoder_operand_live st.cs_next_var data /\ immutable_alloca_sep func ce cx es s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (?t. gas_path_mem ctx func s 0 (OK t) /\
    abi_decode_immutable_success ce env ty tv bs out d st fin ctx func cx es s t /\
    alloca_history func t /\ ~t.vs_halted /\ t.vs_current_bb = fin.cs_current_bb /\
    t.vs_inst_idx = LENGTH fin.cs_current_insts) \/
  (?msg t. evaluate_abi_decode env ty bs = INR msg /\
    gas_marked_path T ctx func s 0 (Abort Revert_abort t))
Proof
  strip_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  Cases_on `abi_static_size ce.ce_struct_fields ty <= LENGTH bs /\
    LENGTH bs <= abi_size_bound ce.ce_struct_fields ty`
  >- suspend "valid" >>
  drule_all abi_decode_mem_builtin_reject >> strip_tac >> disj2_tac >>
  qexistsl_tac [`"abi_decode invalid"`, `t`] >> simp[]
QED

Resume abi_decode_mem_builtin_outcome_conditional[valid]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  qpat_x_assum `abi_static_size ce.ce_struct_fields ty <= LENGTH bs /\ _`
    strip_assume_tac >>
  drule_all abi_decode_mem_builtin_entry >>
  disch_then (qx_choosel_then [`ops`, `ready`, `limit_st`, `prepared`]
    (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qpat_assum `decode_site_resources ctx func prepared`
    (MAP_EVERY assume_tac o CONJUNCTS o REWRITE_RULE [decode_site_resources_def]) >>
  qpat_assum `EVERY (abi_decoder_operand_live ready.cs_next_var) _`
    (MAP_EVERY assume_tac o CONJUNCTS o REWRITE_RULE [EVERY_DEF]) >>
  first_x_assum (qspecl_then [`ctx`, `func`, `limit_st`, `FST (SND ops)`,
    `SND (SND ops)`, `p+32`, `LENGTH bs`, `LENGTH bs`, `bs`, `\q. F`,
    `ce`, `env`, `ce.ce_struct_fields`, `ty`, `tv`, `FST ops`, `Lit 0w`,
    `ready`, `fin`, `prepared`, `0`, `d`] mp_tac) >>
  simp_tac bool_ss [LET_THM] >>
  (impl_tac >- (asm_simp_tac (srw_ss()) [decode_site_resources_def,
    eval_operand_def] >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qexistsl_tac [`abi_builtin_decode_output_site st
      (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)`,
      `d`, `type_memory_bytes ce ty`] >> simp[])) >>
  disch_then (DISJ_CASES_THEN2
    (qx_choosel_then [`finished`, `decoded`] (MAP_EVERY assume_tac o CONJUNCTS))
    (qx_choose_then `reverted` (MAP_EVERY assume_tac o CONJUNCTS)))
  >- suspend "normal" >>
  suspend "revert"
QED

Resume abi_decode_mem_builtin_outcome_conditional[normal]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  `evaluate_abi_decode env ty bs = INL decoded` by
    (drule_all abi_decode_mem_builtin_source_iff >>
     disch_then (qspec_then `decoded` mp_tac) >> fs[]) >>
  qpat_x_assum `?afp. (!p n. MEM (p,n) afp <=> ?inst. MEM inst (fn_insts func) /\ _) /\ _`
    (qx_choose_then `actual_fp` strip_assume_tac) >>
  `decode_site_resources ctx func finished` by
    (simp_tac bool_ss [decode_site_resources_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [`u` |-> `prepared`, `t` |-> `finished`, `v` |-> `decoded`,
    `afp` |-> `actual_fp`] abi_decode_mem_builtin_success) >>
  (impl_tac >- (asm_simp_tac (srw_ss()) [EVERY_DEF] >> metis_tac[])) >>
  strip_tac >> disj1_tac >> qexists_tac `finished` >> simp[]
QED

Resume abi_decode_mem_builtin_outcome_conditional[revert]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  `?msg. evaluate_abi_decode env ty bs = INR msg` by
    (Cases_on `evaluate_abi_decode env ty bs` >> simp[] >>
     drule_all abi_decode_mem_builtin_source_iff >>
     disch_then (qspec_then `a` mp_tac) >> fs[]) >>
  disj2_tac >> qexistsl_tac [`msg`, `reverted`] >> simp[] >>
  fs[gas_marked_path_def] >> metis_tac[gas_path_mem_then, ADD_CLAUSES]
QED

Finalise abi_decode_mem_builtin_outcome_conditional[local]

Theorem abi_decode_mem_caller_suffix_conditional[local]:
  ^decoder_contract ==>
  expr_body_pre ce cx env (TypeBuiltin ann (AbiDecode unwrap) ty [e]) es /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\
  expr_post ctx func ce cx e es sa start s0 (ee with gas_obs := []) (BytesV bs) data s /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\ local_ptrs_reserved ce sa /\
  lower_value compile_expr ce (expr_type e) e sa = (data,start) /\
  lower_abi_decode data
    (type_to_abi_dec_info ce.ce_struct_fields ce
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty))
    (abi_static_size ce.ce_struct_fields
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty))
    (abi_size_bound ce.ce_struct_fields
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty))
    (type_memory_bytes ce
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty)) start = (out,final) /\
  fn_has_code start final func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts ==>
  gas_summary_at T (ctx,func) []
    (bind (lift_sum (evaluate_type_builtin cx (AbiDecode unwrap) ty [expr_type e] [BytesV bs]))
      (\w. return (Value w))) (ee with gas_obs := [],s)
    (\res es1 t. ?v. res = INL (Value v) /\
      vv_post ctx func ce cx (TypeBuiltin ann (AbiDecode unwrap) ty [e]) es sa final s0
        es1 (Value v) (LocatedValue ann (mk_ptr out LocMemory)) t /\
      vv_store_bound cx (expr_type (TypeBuiltin ann (AbiDecode unwrap) ty [e]))
        (lowered_value_type ce (TypeBuiltin ann (AbiDecode unwrap) ty [e])) es1
        (Value v) (LocatedValue ann (mk_ptr out LocMemory)) t /\
      t.vs_current_bb = final.cs_current_bb /\ t.vs_inst_idx = LENGTH final.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
    (\res es1 r. expr_exit res r)
Proof
  strip_tac >> strip_tac >>
  `cs_extends sa start` by metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends start final` by metis_tac[lower_abi_decode_frag_facts] >>
  `sa.cs_next_var <= start.cs_next_var /\ start.cs_next_var <= final.cs_next_var` by
    (conj_tac >- metis_tac[cj 2 compile_expr_grows] >>
     qpat_assum `lower_abi_decode _ _ _ _ _ _ = _`
       (mp_tac o Q.AP_TERM `SND`) >>
     metis_tac[ci_mono_lower_abi_decode, ci_mono_def, pairTheory.SND]) >>
  `local_ptrs_reserved ce start` by metis_tac[local_ptrs_reserved_next_var] >>
  `abi_size_bound ce.ce_struct_fields
    (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty) < dimword (:256)` by
    metis_tac[abi_decode_body_input_word_bound] >>
  `type_memory_bytes ce
    (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty) < dimword (:256)` by
    (drule abi_decode_body_output_bound >> simp[wordsTheory.dimword_def] >> decide_tac) >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic n))) /\
    ~is_word_type (expr_type e)` by
    (`well_typed_expr env e /\ env.type_defs = get_tenv cx` by
       metis_tac[expr_body_pre_def, abi_decode_parent_type, abi_decode_inv_type_env,
         listTheory.CONS_11] >>
     `IS_SOME (evaluate_type (get_tenv cx) (expr_type e))` by
       metis_tac[expr_body_pre_type_builtin_head, expr_body_pre_type_evaluates] >>
     gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(), compileEnvTheory.is_word_type_def]) >>
  suspend "resources"
QED

Resume abi_decode_mem_caller_suffix_conditional[resources]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  drule_all abi_decode_caller_resources >> strip_tac >>
  `abi_decoder_operand_live start.cs_next_var data` by
    (`!x. data = Var x ==> not_fresh_at start x` by
       metis_tac[compile_lower_value_var] >>
     Cases_on `data` >> gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       not_fresh_at_def]) >>
  `data <> Label start.cs_current_bb` by
    (`expr_body_pre ce cx env e es` by metis_tac[expr_body_pre_type_builtin_head] >>
     irule lower_compile_expr_not_label >> goal_assum (drule_at Any) >>
     qexists_tac `env` >> fs[expr_body_pre_def, expr_sim_inv_def]) >>
  `immutable_alloca_sep func ce cx (ee with gas_obs := []) s` by
    (fs[loweringPostsTheory.expr_post_def, stmt_state_rel_def,
       immutable_alloca_sep_def, local_region_def] >> metis_tac[]) >>
  drule abi_decode_body_wrapped_coherent >> strip_tac >>
  `assignable_type (get_tenv cx)
    (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty)` by
    metis_tac[abi_decode_body_wrapped_assignable] >>
  `abi_decode_bytes_widths (get_tenv cx)
    (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty)` by
    metis_tac[abi_decode_body_wrapped_widths] >>
  drule_all abi_decode_mem_builtin_outcome_conditional >>
  disch_then (DISJ_CASES_THEN strip_assume_tac)
  >- suspend "success" >>
  rename1 `gas_marked_path T ctx func s 0 (Abort Revert_abort rejected)` >>
  drule abi_decode_builtin_reject >> strip_tac >>
  simp[gas_summary_at_def, gas_marked_exec_def, gas_marked_path_def,
    vyperStateTheory.bind_def, vyperStateTheory.lift_sum_def,
    vyperStateTheory.return_def] >>
  qexistsl_tac [`INR (Error (RuntimeError e'))`, `ee`, `Abort Revert_abort rejected`] >>
  gvs[vyperStateTheory.raise_def, exprSimDefsTheory.expr_exit_def]
QED

Resume abi_decode_mem_caller_suffix_conditional[success]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  `?rtv. evaluate_type (get_tenv cx) ty = SOME rtv` by
    (drule abi_decode_body_target >> strip_tac >>
     drule vyperTypeSystemTheory.assignable_type_well_formed >>
     simp[vyperTypeSystemTheory.well_formed_type_def, optionTheory.IS_SOME_EXISTS]) >>
  `tv = (if unwrap /\ needs_external_call_wrap ty then TupleTV [rtv] else rtv)` by
    (drule abiDecoderCoherenceTheory.abi_decoder_coherent_header >>
     fs[abiDecoderCoherenceTheory.abi_decoder_header_def] >>
     drule abi_decode_wrapped_type >> metis_tac[optionTheory.SOME_11]) >>
  gvs[] >>
  `?v. evaluate_type_builtin cx (AbiDecode unwrap) ty [expr_type e] [BytesV bs] = INL v /\
    vv_post ctx func ce cx (TypeBuiltin ann (AbiDecode unwrap) ty [e]) es sa final s0
      (ee with gas_obs := []) (Value v) (LocatedValue ann (mk_ptr out LocMemory)) t` by
    (irule abi_decode_body_caller_success >> simp[] >>
     metis_tac[]) >>
  simp[gas_summary_at_def, gas_marked_exec_def, gas_marked_path_def,
    vyperStateTheory.bind_def, vyperStateTheory.lift_sum_def,
    vyperStateTheory.return_def] >>
  `vv_store_bound cx (expr_type (TypeBuiltin ann (AbiDecode unwrap) ty [e]))
      (lowered_value_type ce (TypeBuiltin ann (AbiDecode unwrap) ty [e]))
      (ee with gas_obs := []) (Value v) (LocatedValue ann (mk_ptr out LocMemory)) t /\
    s.vs_alloca_next <= t.vs_alloca_next` by
      (drule_all abi_decode_mem_caller_capacity >> simp[]) >>
  qexistsl_tac [`INL (Value v)`, `ee`, `OK t`] >>
  gvs[vyperStateTheory.return_def] >> decide_tac
QED
Finalise abi_decode_mem_caller_suffix_conditional[local]

Theorem abi_decode_mem_normal_prefix_conditional[local]:
  ^decoder_contract ==>
  expr_body_pre ce cx env (TypeBuiltin ann (AbiDecode unwrap) ty [e]) es /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\ local_ptrs_reserved ce sa /\
  lower_value compile_expr ce (expr_type e) e sa = (data,start) /\
  lower_abi_decode data
    (type_to_abi_dec_info ce.ce_struct_fields ce
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty))
    (abi_static_size ce.ce_struct_fields
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty))
    (abi_size_bound ce.ce_struct_fields
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty))
    (type_memory_bytes ce
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty)) start = (out,final) /\
  fn_has_code start final func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  gas_marked_exec T (ctx,func) (bind (eval_expr cx e) (read_result cx))
    (es,s0) marks (INL v) ee (OK s) /\
  expr_post ctx func ce cx e es sa start s0 (ee with gas_obs := []) v data s /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts ==>
  gas_summary_at T (ctx,func) marks
    (eval_expr cx (TypeBuiltin ann (AbiDecode unwrap) ty [e])) (es,s0)
    (\res es1 t. ?tv. res = INL tv /\
      vv_post ctx func ce cx (TypeBuiltin ann (AbiDecode unwrap) ty [e]) es sa final s0
        es1 tv (LocatedValue ann (mk_ptr out LocMemory)) t /\
      vv_store_bound cx (expr_type (TypeBuiltin ann (AbiDecode unwrap) ty [e]))
        (lowered_value_type ce (TypeBuiltin ann (AbiDecode unwrap) ty [e])) es1
        tv (LocatedValue ann (mk_ptr out LocMemory)) t /\
      t.vs_current_bb = final.cs_current_bb /\ t.vs_inst_idx = LENGTH final.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
    (\res es1 r. expr_exit res r)
Proof
  strip_tac >> strip_tac >>
  `expr_body_pre ce cx env e es` by
    metis_tac[expr_body_pre_type_builtin_head] >>
  `evaluate_type (get_tenv cx) (expr_type e) =
    SOME (BaseTV (BytesT (Dynamic n)))` by
    (drule expr_body_pre_type_evaluates >>
     simp[vyperValueTheory.evaluate_type_def, AllCaseEqs()]) >>
  `bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL v, ee with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
      (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_result_typed env e (Value v)` by
    (irule (cj 3 expr_body_pre_eval) >>
     qexistsl_tac [`ce`, `cx`,
       `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
       `ee with gas_obs := []`] >> fs[bind_def]) >>
  `?bs. v = BytesV bs` by
    (`env.type_defs = get_tenv cx` by
       metis_tac[abi_decode_inv_type_env, expr_body_pre_def] >>
     fs[expr_result_typed_def, expr_runtime_typed_def, value_result_typed_def] >>
     Cases_on `v` >> gvs[value_has_type_def]) >> gvs[] >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule abi_decode_observed_scopes_dom >> simp[]) >>
  `lower_value compile_expr ce (expr_type e) e sa = (data,start)` by metis_tac[] >>
  drule_all abi_decode_mem_caller_suffix_conditional >>
  rewrite_tac[gas_summary_at_def] >> strip_tac >>
  `ann = ty` by
    metis_tac[abi_decode_parent_type, expr_body_pre_def] >>
  pop_assum SUBST_ALL_TAC >>
  rewrite_tac[abi_decode_singleton_source] >>
  qexistsl_tac [`res`, `es_end`, `r`] >>
  (conj_tac
   >- (irule (SRULE [] (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal)) >>
       goal_assum (drule_at Any) >> metis_tac[]) >>
   gvs[] >> metis_tac[])
QED

Theorem abi_decode_mem_vv_conditional[local]:
  ^decoder_contract ==>
  !ctx func cenv cx env ty ann unwrap target args es.
    expr_body_pre cenv cx env (TypeBuiltin ann (AbiDecode unwrap) target args) es /\
    (!e. MEM e args ==> expr_sim_mem ctx func cenv cx (expr_type e) e es) ==>
    expr_vv_sim_mem ctx func cenv cx ty
      (TypeBuiltin ann (AbiDecode unwrap) target args) es
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `well_typed_expr env (TypeBuiltin ann (AbiDecode unwrap) target args)` by
    fs[expr_body_pre_def] >>
  drule abi_decode_parent_type >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env e es` by
    metis_tac[expr_body_pre_type_builtin_head] >>
  `expr_sim_mem ctx func cenv cx (expr_type e) e es` by metis_tac[MEM] >>
  simp[expr_vv_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_expr_type_builtin_dispatch,
       Once (CONJUNCT2 (CONJUNCT2 compile_expr_raw_def)),
       compile_type_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[oneline exprLoweringTheory.as_ptr_val_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  rename1 `compile_expr cenv (BaseT (BytesT (Dynamic n))) e sa = (evv, sm)` >>
  rename1 `unwrap_value cenv evv sm = (data, start)` >>
  `lower_value compile_expr cenv (expr_type e) e sa = (data,start)` by
    simp[lower_value_def, comp_bind_def] >>
  `cs_extends sa start` by
    metis_tac[compile_expr_extends, unwrap_value_extends, cs_extends_trans] >>
  drule lower_abi_decode_frag_facts >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  `gas_admissible (vyperState$bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  suspend "child"
QED

Resume abi_decode_mem_vv_conditional[child]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`, `start`, `data`, `s0`] mp_tac) >>
  (impl_tac >- metis_tac[]) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [gas_summary_at_def]) >>
      strip_tac
      >- (gvs[] >>
          `~t.vs_halted` by
            metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
          irule abi_decode_mem_normal_prefix_conditional >>
          goal_assum (drule_at Any) >> metis_tac[]) >>
      Cases_on `res` >- gvs[expr_exit_def] >>
      rewrite_tac[abi_decode_singleton_source, gas_summary_at_def] >>
      qexistsl_tac [`INR y`, `es_end`, `r`] >> simp[] >>
      conj_tac >- (irule gas_marked_exec_bind_exception >> simp[]) >>
      disj2_tac >>
      Cases_on `y` >> Cases_on `r` >> gvs[expr_exit_def] >>
      Cases_on `e'` >> gvs[expr_exit_def]) >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  irule abi_decode_child_exempt_cert >> simp[]
QED

Finalise abi_decode_mem_vv_conditional[local]

Theorem body_type_builtin_abi_decode_mem_conditional[local]:
  ^decoder_contract ==>
  !cx v11 unwrap typ es.
    (!s'' x t.
       type_check (type_builtin_args_length_ok (AbiDecode unwrap) (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (TypeBuiltin v11 (AbiDecode unwrap) typ es)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  irule body_expr_mem_ok_intro >> conj_tac
  >- (rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  `well_typed_expr env (TypeBuiltin v11 (AbiDecode unwrap) typ es)` by
    fs[expr_body_pre_def] >>
  `v11 = typ` by metis_tac[abi_decode_body_target] >>
  qpat_x_assum `v11 = typ` SUBST_ALL_TAC >>
  drule abi_decode_parent_type >> strip_tac >> gvs[] >>
  `body_exprs_mem_ok cx [e]` by
    (first_x_assum irule >>
     simp[type_check_def, assert_def, type_builtin_args_length_ok_def]) >>
  `body_expr_mem_ok cx e` by fs[body_exprs_mem_ok_def] >>
  `expr_vv_sim_mem ctx func cenv cx ty (TypeBuiltin typ (AbiDecode unwrap) typ [e]) es'` by
    (irule abi_decode_mem_vv_conditional >> simp[] >> rpt strip_tac >> gvs[] >>
     `expr_body_pre cenv cx env e es'` by
       metis_tac[expr_body_pre_type_builtin_head] >>
     metis_tac[body_expr_mem_ok_def]) >>
  simp[] >> irule body_expr_sim_mem_of_vv_sim_mem >> qexists_tac `env` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_expr_type_builtin_dispatch,
    Once (CONJUNCT2 (CONJUNCT2 compile_expr_raw_def)),
    compile_type_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> gvs[]) >> simp[oneline as_ptr_val_def] >>
  strip_tac >> gvs[AllCaseEqs()]
QED

Theorem body_type_builtin_abi_decode_mem_case:
  !cx v11 unwrap typ es.
    (!s'' x t.
       type_check (type_builtin_args_length_ok (AbiDecode unwrap) (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (TypeBuiltin v11 (AbiDecode unwrap) typ es)
Proof
  cheat
QED
