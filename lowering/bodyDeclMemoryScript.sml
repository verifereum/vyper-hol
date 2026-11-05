(* Declaration store: source-state and memory continuation boundaries. *)
Theory bodyDeclMemory
Ancestors
  bodyDeclMemoryCounted bodyDeclMemoryCore
  gasOutcome gasSummary fragGasMode fragGasPathMem
  loweringPosts exprSimProps stmtSimProps exprSimHypsDefs
  bodyNameMemoryFacts bodyCopyMemory bodyMemoryDefs stmtSimDeclMem
  localPtrsProps stmtSimDeclStore stmtSimDecl valueCopy valueCopyBytes
  exprOperandVar freshWrites valueTypingMemoryProps vyperTyping
  exprSimDefs stmtSimDefs venomState valueEncoding valueEncodingProofs
  intCallResult compileEnv exprLoweringProps loweringSlice exprLowering
  exprSimBufferStore words venomExecSemantics stmtLowering context
  fragExec fragExecMem allocaHistoryFragment list rich_list emitHelper
  emitHelperProps venomInst exprSimLiteralBuffer exprSimAlloc exprSimBuffer
  finite_map bodySimDeclCases allocLimits bodySim exprSimHyps
  vyperTypeSystem vyperTypeInvariants memoryLocalRhsProps
  supportedStmtTraverse supportedExprTraverse vyperTypeCallGraph
  vyperTypeCallStackSoundness vyperInterpreter vyperState


Theorem body_annassign_read_eval[local]:
  evaluate_type (get_tenv cx) ty = SOME tyv /\
  (do tv <- eval_expr cx e; read_result cx tv od) es = (INL v,es) /\
  lookup_scopes id es.scopes = NONE /\ es.scopes = sc :: rest ==>
  eval_stmt cx (AnnAssign id ty e) es =
    (INL (), es with scopes :=
      (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest)
Proof
  strip_tac >>
  qpat_x_assum `(do tv <- _; _ od) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, return_def,
       lift_option_type_def] >>
  Cases_on `eval_expr cx e es` >> Cases_on `q` >> simp[] >>
  Cases_on `read_result cx x r` >> Cases_on `q` >> simp[] >>
  strip_tac >> gvs[] >>
  simp[new_variable_def, bind_def, ignore_bind_def, get_scopes_def,
       type_check_def, assert_def, set_scopes_def, return_def]
QED

Theorem body_annassign_name_eval_tails[local]:
  lookup_scopes source_id es.scopes = SOME entry /\
  evaluate_type (get_tenv cx) ty = SOME entry.type /\
  lookup_scopes id es.scopes = NONE /\ es.scopes = sc :: rest ==>
  !tail. eval_stmt cx (AnnAssign id ty (Name ty source_id))
    (es with gas_obs := tail) =
    (INL (), (es with scopes :=
      (sc |+ (id, <|assignable := T; type := entry.type;
        value := entry.value; popped := []|>)) :: rest) with gas_obs := tail)
Proof
  strip_tac >> gen_tac >>
  `lookup_scopes source_id (es with gas_obs := tail).scopes = SOME entry` by fs[] >>
  drule_then (qspecl_then [`cx`, `ty`] mp_tac) eval_name_word >>
  strip_tac >>
  `lookup_scopes id (es with gas_obs := tail).scopes = NONE /\
   (es with gas_obs := tail).scopes = sc :: rest` by fs[] >>
  drule_all body_annassign_read_eval >> simp[]
QED

Theorem body_annassign_name_path[local]:
  declare_local ce id ty sa = (c,st) /\ ce.ce_alloca_locals /\
  lookup_scopes id es.scopes = NONE /\ FLOOKUP ce.ce_vars id = NONE /\
  p = STRING #"%" (toString sa.cs_next_var) /\
  emit_inst ALLOCA [Lit (n2w (type_memory_bytes ce ty))] [p] st = ((),sA) /\
  (!u. lower_value compile_expr c ty (Name ty source_id) u = (src,u)) /\
  compile_assign_value c (Var p) LocMemory src F (SOME LocMemory)
    ty ty info bytes sA = ((),sb) /\
  expr_sim_pre c cx env (Name ty source_id) es /\
  (do result <- eval_expr cx (Name ty source_id); read_result cx result od) es = (INL v,es) /\
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tyv /\
  type_memory_bytes c ty = type_memory_size tyv /\
  type_memory_bytes ce ty = type_memory_size tyv /\
  type_memory_size tyv + 64 < dimword (:256) /\ es.scopes = sc :: rest /\
  fn_has_code sa sA func /\ fn_has_code sA sb func /\
  cs_extends sa sA /\ cs_extends sA sb /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s /\
  alloca_history func s /\ return_buf_frame d ce sa s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    stmt_state_rel ctx func c cx
      (es with scopes :=
        (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest) t /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    return_buf_frame d c sb t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b)
Proof
  strip_tac >>
  `type_memory_bytes ce ty < dimword (:256)` by decide_tac >>
  `!l. FLOOKUP ce.ce_vars id = SOME l ==> ?q sz. l = PtrVar q sz` by simp[] >>
  drule_all annassign_setup_shape >> strip_tac >>
  drule_all annassign_setup_body_gas_path_mem >> strip_tac >>
  gvs[] >>
  qmatch_asmsub_abbrev_tac `MEM A (fn_insts func)` >>
  `A.inst_opcode = ALLOCA /\
   A.inst_outputs = [STRING #"%" (toString sa.cs_next_var)] /\
   A.inst_id = sa.cs_next_id` by simp[Abbr `A`, mk_inst_def] >>
  `w2n w + type_memory_size tyv <= t.vs_alloca_next` by decide_tac >>
  `lower_value compile_expr c ty (Name ty source_id) sA = (src,sA) /\
   lookup_scopes id es.scopes = NONE /\
   not_local_ptr c es.scopes (STRING #"%" (toString sa.cs_next_var)) /\
   FLOOKUP t.vs_allocas A.inst_id = SOME (w2n w,type_memory_size tyv) /\
   type_memory_size tyv <= type_memory_size tyv` by simp[] >>
  `sa.cs_next_var <= sA.cs_next_var` by
    (drule emit_inst_extends >> simp[] >> decide_tac) >>
  drule_all annassign_name_rhs_body_path >>
  disch_then (qspec_then `T` (qx_choose_then `t2` strip_assume_tac)) >>
  qexists_tac `t2` >>
  `gas_path_mem ctx func s (0 + 0) (OK t2)` by
    (irule gas_path_mem_then >> qexists_tac `t` >> simp[]) >>
  fs[] >> rpt strip_tac >>
  metis_tac[not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem body_annassign_name_prepare[local]:
  body_inv tops ctx ce cx /\
  supported_stmt tops bindings (AnnAssign id ty (Name ty source_id)) /\
  expr_sim_inv ce cx env es /\ ce_locals_declared ce env /\
  locals_alloc_ok ce env /\
  type_stmt env ret_ty (AnnAssign id ty (Name ty source_id)) = SOME env' /\
  stmt_exprs_ok ce (AnnAssign id ty (Name ty source_id)) /\
  call_evaluation_safe cx (int_calls_stmt (AnnAssign id ty (Name ty source_id))) /\
  ~is_word_type ty /\ 0 < type_memory_bytes ce ty /\
  stmt_env ce lctx ret_ty (AnnAssign id ty (Name ty source_id)) sa = (c,sb) ==>
  ?tyv v sc rest st sA src info es'.
    eval_stmt cx (AnnAssign id ty (Name ty source_id)) es = (INL (),es') /\
    (!tail. eval_stmt cx (AnnAssign id ty (Name ty source_id))
      (es with gas_obs := tail) = (INL (),es' with gas_obs := tail)) /\
    es' = es with scopes :=
      (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest /\
    es.scopes = sc :: rest /\ cenv_top_ext ce c es'.scopes /\
    ce.ce_alloca_locals /\ FLOOKUP ce.ce_vars id = NONE /\
    lookup_scopes id es.scopes = NONE /\
    declare_local ce id ty sa = (c,st) /\
    emit_inst ALLOCA [Lit (n2w (type_memory_bytes ce ty))]
      [STRING #"%" (toString sa.cs_next_var)] st = ((),sA) /\
    (!u. lower_value compile_expr c ty (Name ty source_id) u = (src,u)) /\
    compile_assign_value c (Var (STRING #"%" (toString sa.cs_next_var)))
      LocMemory src F (SOME LocMemory) ty ty info (type_memory_bytes ce ty) sA = ((),sb) /\
    expr_sim_pre c cx env (Name ty source_id) es /\
    (do result <- eval_expr cx (Name ty source_id); read_result cx result od) es = (INL v,es) /\
    evaluate_type (get_tenv cx) ty = SOME tyv /\
    type_memory_bytes c ty = type_memory_size tyv /\
    type_memory_bytes ce ty = type_memory_size tyv /\
    type_memory_size tyv + 64 < dimword (:256)
Proof
  strip_tac >>
  `FLOOKUP ce.ce_vars id = NONE` by
    (irule declared_name_unbound >> metis_tac[]) >>
  `well_typed_expr env (Name ty source_id) /\ assignable_type env.type_defs ty /\
   id NOTIN FDOM env.var_types` by gvs[type_stmt_def, AllCaseEqs()] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?tyv. evaluate_type (get_tenv cx) ty = SOME tyv` by
    metis_tac[assignable_type_well_formed, well_formed_type_def,
              optionTheory.IS_SOME_EXISTS] >>
  `ce.ce_alloca_locals` by fs[body_inv_def] >>
  `lookup_scopes id es.scopes = NONE` by
    (Cases_on `lookup_scopes id es.scopes` >> simp[] >>
     gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     res_tac >> gvs[FLOOKUP_DEF]) >>
  `type_memory_bytes ce ty = type_memory_size tyv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `type_memory_bytes ce ty < 2 ** 64` by
    gvs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
  `type_memory_size tyv + 64 < dimword (:256)` by
    metis_tac[allocation_limit_word_room] >>
  `!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
     is_dynamic (vyper_to_abi_type (type_env (cx_tops cx)) target)` by
    (gvs[body_inv_def] >> drule gasContextTheory.cx_tops_module >>
     rw[] >> gvs[] >> metis_tac[]) >>
  `expr_sim_pre ce cx env (Name ty source_id) es` by
    (gvs[expr_sim_pre_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         byte_widths_expr_def, alloc_limits_expr_def, int_calls_expr_def,
         expr_has_evm_run_def, supported_expr_exists_def, expr_evm_run_root_def,
         supportedProgramTheory.expr_abi_decode_target_root_def,
         call_evaluation_safe_def, exprLoweringTheory.is_extcode_def] >>
     metis_tac[]) >>
  drule stmt_env_annassign >> strip_tac >>
  `same_frame ce c` by
    (drule_then irule declare_local_same_frame >> simp[]) >>
  `expr_sim_inv c cx env es` by metis_tac[expr_sim_inv_declare_local] >>
  `c.ce_struct_fields = ce.ce_struct_fields` by
    fs[same_frame_def, compile_env_component_equality] >>
  `type_memory_bytes c = type_memory_bytes ce` by
    (irule compileEnvTheory.type_memory_bytes_frame >> simp[]) >>
  `expr_sim_pre c cx env (Name ty source_id) es` by
    gvs[expr_sim_pre_def, alloc_limits_expr_def, type_alloc_ok_def] >>
  drule_all declare_local_ptr >> strip_tac >>
  drule_all body_annassign_name_compiler_parts >> strip_tac >>
  `?entry. lookup_scopes source_id es.scopes = SOME entry /\
     evaluate_type (get_tenv cx) ty = SOME entry.type /\
     value_has_type entry.type entry.value` by
    (gvs[expr_sim_pre_def, expr_sim_inv_def] >>
     drule_all vyperTypeEnvTheory.well_typed_Name_lookup >> strip_tac >>
     gvs[env_consistent_def, env_context_consistent_def]) >>
  drule_all body_name_nonword_compile >> strip_tac >>
  `sB = sA` by (qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >> simp[]) >>
  `sV = sA /\ vv_location vv = SOME LocMemory /\
   lowered_value_type c (Name ty source_id) = ty` by
    (qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
     simp[compile_expr_def, compile_name_vv_def, comp_return_def,
          vyperASTTheory.expr_type_def, contextTheory.mk_ptr_def,
          vv_location_def, lowered_value_type_def] >>
     rpt strip_tac >> gvs[vv_location_def]) >>
  `(do result <- eval_expr cx (Name ty source_id); read_result cx result od) es =
    (INL entry.value,es)` by (irule eval_name_word >> simp[]) >>
  `?sc rest. es.scopes = sc :: rest` by
    (Cases_on `es.scopes` >> gvs[lookup_scopes_def]) >>
  drule_all body_annassign_name_eval_tails >> strip_tac >>
  drule_all body_annassign_read_eval >> strip_tac >>
  qmatch_asmsub_abbrev_tac `eval_stmt cx (AnnAssign id ty (Name ty source_id)) es = (INL (),es_end)` >>
  `cenv_top_ext ce c es_end.scopes` by
    (irule annassign_word_top_ext >> simp[] >>
     goal_assum (drule_at (Pat `declare_local _ _ _ _ = _`)) >>
     simp[] >> qexistsl_tac [`cx`, `Name ty source_id`, `es`] >> simp[]) >>
  gvs[Abbr `es_end`] >> goal_assum (drule_at Any)
QED

Theorem body_annassign_name_code[local]:
  declare_local ce id ty sa = (c,st) /\ ce.ce_alloca_locals /\
  FLOOKUP ce.ce_vars id = NONE /\ local_ptrs_reserved ce sa /\
  emit_inst ALLOCA [Lit (n2w (type_memory_bytes ce ty))]
    [STRING #"%" (toString sa.cs_next_var)] st = ((),sA) /\
  compile_assign_value c (Var (STRING #"%" (toString sa.cs_next_var)))
    LocMemory src F (SOME LocMemory) ty ty info bytes sA = ((),sb) /\
  0 < type_memory_bytes c ty /\ fn_has_code sa sb func ==>
  cs_extends sa sA /\ cs_extends sA sb /\
  fn_has_code sa sA func /\ fn_has_code sA sb func /\ ~block_is_terminated sb
Proof
  strip_tac >>
  `!l. FLOOKUP ce.ce_vars id = SOME l ==> ?q sz. l = PtrVar q sz` by simp[] >>
  drule_all declare_local_ptr >> strip_tac >>
  `cs_extends sA sb` by
    (irule (SRULE [cs_appends_def] compile_assign_memory_widen_appends) >>
     goal_assum (drule_at Any) >> simp[]) >>
  `fn_has_code st sb func` by gvs[fn_has_code_def, emitted_blocks_def] >>
  drule_all annassign_alloca_code >> strip_tac >>
  `cs_extends sa sA` by
    (drule emit_inst_extends >> strip_tac >> gvs[cs_extends_def]) >>
  simp[] >> conj_tac
  >- gvs[fn_has_code_def, emitted_blocks_def] >>
  irule compile_assign_value_memory_same_open >>
  goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >> simp[]
QED

Theorem body_decl_normal_landing[local]:
  !ctx func c cx es' s sb ce lctx.
  stmt_state_rel ctx func c cx es' s /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ~block_is_terminated sb /\ cenv_top_ext ce c es'.scopes ==>
  stmt_lands lctx sb (INL ()) s /\
  cenv_top_ext ce c (es' with gas_obs := []).scopes /\
  stmt_state_rel ctx func c cx (es' with gas_obs := []) s
Proof
  rpt gen_tac >> strip_tac >> simp[stmt_lands_def] >>
  drule msg_gas_state_frame >>
  disch_then (qspecl_then [`s.vs_gas_readings`, `s.vs_inst_idx`, `[]`] mp_tac) >>
  simp[NoAsms]
QED

Theorem body_annassign_name_mem:
  !d tops bindings ctx func cenv cx env env' ret_ty lctx RetQ id typ source_id es.
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AnnAssign id typ (Name typ source_id)) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (AnnAssign id typ (Name typ source_id)) = SOME env' /\
    stmt_exprs_ok cenv (AnnAssign id typ (Name typ source_id)) /\
    call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ (Name typ source_id))) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    ~is_word_type typ /\ 0 < type_memory_bytes cenv typ ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AnnAssign id typ (Name typ source_id)))
      (eval_stmt cx (AnnAssign id typ (Name typ source_id))) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  drule_all body_annassign_name_prepare >> strip_tac >>
  `0 < type_memory_bytes cenv' typ` by decide_tac >>
  drule_all body_annassign_name_code >> strip_tac >>
  `STRING #"%" (toString sa.cs_next_var) = STRING #"%" (toString sa.cs_next_var)` by simp[] >>
  drule_all body_annassign_name_path >> strip_tac >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL ()`, `es'`, `OK t`] >>
  simp[gas_marked_exec_def, gas_marked_path_def] >>
  qspecl_then [`ctx`, `func`, `cenv'`, `cx`, `es'`, `t`, `sb`, `cenv`, `lctx`]
    mp_tac body_decl_normal_landing >>
  impl_tac >- gvs[] >>
  strip_tac >> gvs[] >>
  disj1_tac >>
  qpat_x_assum `stmt_state_rel ctx func cenv' cx (es with scopes := _) t` mp_tac >>
  rpt (qpat_x_assum `stmt_state_rel _ _ _ _ _ _` kall_tac) >>
  strip_tac >> drule msg_gas_state_frame >>
  disch_then (qspecl_then [`t.vs_gas_readings`, `t.vs_inst_idx`, `[]`] mp_tac) >>
  simp[NoAsms, Excl "stmt_state_rel_gas_obs"]
QED
