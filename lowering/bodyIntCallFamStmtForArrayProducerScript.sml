(* The Array callback, instantiated at the concrete resource endpoint. *)
Theory bodyIntCallFamStmtForArrayProducer
Ancestors
  bodyIntCallFamStmtForArrayIterations bodyIntCallFamStmtForArrayRound
  bodyIntCallFamStmtForArrayResources bodyIntCallJointContract
  stmtSimForArrayLoop stmtSimDeclCompose stmtForRangeMemoryRound
  stmtSimProps stmtSimDefs compileEnv loweringPosts exprSimMemDefs
  venomState venomExecSemantics venomInst vyperState vyperInterpreter
  finite_map list rich_list arithmetic bodySimDeclCases

Theorem intcall_array_producer_round:
  array_for_code fp.jc_func ce bc
    (if fp.jc_ret_ty = NoneT then BaseT BoolT else fp.jc_ret_ty)
    stmts id fty tv (LENGTH vs) stride (Var ip)
    p sz aa idx dv ov ep nv cond exit bod incr j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  intcall_stmts_producer fp stmts /\ intcall_frame_ok fp /\
  intcall_joint_res fp ce env es sc cc /\
  array_loop_inv fp.jc_ctx fp.jc_func ce fp.jc_cx
    (\ee. lookup_scopes name ee.scopes = SOME snapshot)
    vs id idx (Var ip) arrbase p dst sz aa cond sc k es cc /\
  k < LENGTH vs /\ LENGTH vs < dimword (:256) /\
  declare_local ce id fty sd = (bc,sd') /\ ce.ce_alloca_locals /\
  FLOOKUP ce.ce_vars id = NONE /\ id NOTIN FDOM env.var_types /\
  evaluate_type (get_tenv fp.jc_cx) fty = SOME tv /\
  value_has_type tv (EL k vs) /\ val_wf tv (EL k vs) /\
  type_memory_bytes ce fty < 2 ** 64 /\
  w2n arrbase + k * stride < dimword (:256) /\
  sc.cs_next_var <= sb0.cs_next_var /\ local_ptrs_reserved ce sb1 /\
  (!x. not_fresh_at sc x ==> not_fresh_at sa x /\
       not_fresh_at sb0 x /\ x <> dv /\ x <> ov /\ x <> ep /\ x <> idx /\ x <> nv) /\
  not_fresh_at sb0 idx /\ not_fresh_at sb0 p /\ not_fresh_at sb0 ip /\
  (!op. fp.jc_reserved op ==> op <> Var dv /\ op <> Var idx /\ op <> Var nv) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  lookup_block sb0.cs_current_bb fp.jc_func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  (!s. array_loop_inv fp.jc_ctx fp.jc_func ce fp.jc_cx
      (\ee. lookup_scopes name ee.scopes = SOME snapshot)
      vs id idx (Var ip) arrbase p dst sz aa bod sc k es s ==>
    val_in_memory tv (EL k vs) (w2n arrbase + k * stride) s.vs_memory /\
    ret_pc_ok bc sb0 s) /\
  (!x z. bc.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> ep) /\
  body_inv fp.jc_tops fp.jc_ctx bc fp.jc_cx /\
  supported_program fp.jc_tops /\ get_module_code fp.jc_cx NONE = SOME fp.jc_tops /\
  supported_stmts fp.jc_tops bindings stmts /\
  (!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) stmts ==>
    occurs_abi_decode_target target fp.jc_tops) /\
  type_stmts (extend_local env id fty F) fp.jc_ret_ty stmts = SOME env_b /\
  IS_SOME (type_stmts ((extend_local env id fty F) with bare_global_assignable := FEMPTY)
    fp.jc_ret_ty stmts) /\
  EVERY (stmt_exprs_ok bc) stmts /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_stmts stmts) /\
  call_evaluation_safe fp.jc_cx (int_calls_stmts stmts) /\
  stmts_env bc (InLoop exit incr)
    (if fp.jc_ret_ty = NoneT then BaseT BoolT else fp.jc_ret_ty) stmts sb0 = (ce_b,sb1) /\
  FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\ name <> id /\
  iterator_unmodified (Array (Name aty name)) stmts /\
  ~supported_stmts_expr_exists expr_internal_call_root stmts /\
  gas_admissible (eval_for fp.jc_cx tv id stmts (DROP k vs)) (stmt_res_ok lctx) es ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (ignore_bind (push_scope_with_var id tv (EL k vs))
      (finally (try (ignore_bind (eval_stmts fp.jc_cx stmts) (return F))
                     handle_loop_exception) pop_scope))
    (es,cc)
    (\res ee u. ?broke. res = INL broke /\ u.vs_inst_idx = 0 /\ ~u.vs_halted /\
      intcall_joint_res fp ce env ee sc u /\
      (!x z. not_fresh_at sc x /\ lookup_var x cc = SOME z ==> lookup_var x u = SOME z) /\
      (!aid b. FLOOKUP cc.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
      cc.vs_alloca_next <= u.vs_alloca_next /\ (broke ==> u.vs_current_bb = exit) /\
      (~broke ==> array_loop_inv fp.jc_ctx fp.jc_func ce fp.jc_cx
        (\ee. lookup_scopes name ee.scopes = SOME snapshot)
        vs id idx (Var ip) arrbase p dst sz aa cond sc (k+1) ee u))
    (\res ee r. ?ex. res = INR ex /\ intcall_stmt_exit fp (INR ex) ee r)
Proof
  strip_tac >>
  `(!scs. not_local_ptr ce scs dv) /\ dv <> idx /\ dv <> p /\ ip <> dv` by
    (fs[array_for_code_def] >> metis_tac[]) >>
  drule array_for_code_condition >> strip_tac >>
  `not_local_ptr ce es.scopes dv /\
   (!op. fp.jc_reserved op ==> op <> Var dv)` by metis_tac[] >>
  `?next. gas_marked_path F fp.jc_ctx fp.jc_func cc 0 (OK next) /\
    intcall_joint_res fp ce env es sc next /\
    array_loop_inv fp.jc_ctx fp.jc_func ce fp.jc_cx
      (\ee. lookup_scopes name ee.scopes = SOME snapshot)
      vs id idx (Var ip) arrbase p dst sz aa
      (if k = LENGTH vs then exit else bod) sc k es next /\
    (!x. x <> dv ==> lookup_var x next = lookup_var x cc) /\
    next.vs_allocas = cc.vs_allocas /\
    next.vs_alloca_next = cc.vs_alloca_next /\
    next.vs_memory = cc.vs_memory /\ next.vs_labels = cc.vs_labels` by
    (irule intcall_array_condition_entry >> simp[] >> metis_tac[]) >>
  `array_loop_inv fp.jc_ctx fp.jc_func ce fp.jc_cx
    (\ee. lookup_scopes name ee.scopes = SOME snapshot)
    vs id idx (Var ip) arrbase p dst sz aa bod sc k es next` by gvs[] >>
  `array_entry_inputs fp.jc_ctx fp.jc_func ce bc fp.jc_cx es next id p sz dst
    aa tv (EL k vs) fty (get_tenv fp.jc_cx) sa sb0 idx (Var ip) arrbase k stride
    ov ep j3 j4 bb sb0` by suspend "inputs" >>
  `local_ptrs_reserved bc sb0` by fs[array_for_code_def] >>
  `!x. not_fresh_at sc x ==> not_fresh_at sa x /\ x <> ov /\ x <> ep`
    by metis_tac[] >>
  drule_all intcall_array_copy_entry_frame >> strip_tac >>
  suspend "body"
QED
Resume intcall_array_producer_round[inputs]:
  `val_in_memory tv (EL k vs) (w2n arrbase + k * stride) next.vs_memory /\
   ret_pc_ok bc sb0 next` by metis_tac[] >>
  fs[array_entry_inputs_def, array_for_code_def, array_loop_inv_def,
     ALL_DISTINCT, eval_operand_def] >>
  `cenv_top_ext ce bc (FEMPTY::es.scopes)` by
    (drule cenv_top_ext_declare_local >>
     disch_then (qspecl_then [`FEMPTY`, `es.scopes`] mp_tac) >> simp[]) >>
  rpt conj_tac >> metis_tac[]
QED
Resume intcall_array_producer_round[body]:
  `gas_admissible (eval_stmts fp.jc_cx stmts)
     (stmt_res_ok (InLoop exit incr))
     (es with scopes := (FEMPTY |+ (id,
       <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes)` by
    (qpat_x_assum `gas_admissible _ _ _` mp_tac >>
     simp[Once rich_listTheory.DROP_CONS_EL] >>
     disch_then (mp_then Any mp_tac for_round_body_admissible) >> simp[]) >>
  `cenv_top_ext ce bc ((FEMPTY |+ (id,
     <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes)` by
    (drule cenv_top_ext_declare_local >>
     disch_then (qspecl_then [`FEMPTY |+ (id,
       <|assignable := F; type := tv; value := EL k vs; popped := []|>)`,
       `es.scopes`] mp_tac) >> fs[array_loop_inv_def]) >>
  irule gas_outcome_zero_prefix >>
  qexists_tac `next` >> simp[] >>
  irule gas_outcome_zero_prefix >>
  qexists_tac `s2` >> simp[] >>
  irule gas_outcome_post_mono >>
  (let
     val th = SPEC_ALL (SRULE [LET_THM] intcall_array_round_at_body)
     val v = first (fn t => fst (dest_var t) = "vs") (free_vars (concl th))
     val thv = INST_TYPE (match_type (type_of v) ``:value list``) th
   in irule_at Any thv end) >> simp[] >>
  qhdtm_assum `array_for_code` (irule_at Any) >> simp[] >>
  qpat_assum `array_loop_inv _ _ _ _ _ vs id idx _ arrbase p dst sz aa cond sc k es cc`
    (irule_at Any) >> simp[] >>
  qpat_assum `type_stmts _ _ _ = SOME env_b` (irule_at Any) >> simp[] >>
  qhdtm_assum `supported_stmts` (irule_at Any) >> simp[] >>
  qhdtm_assum `iterator_unmodified` (irule_at Any) >> simp[] >>
  conj_tac >- (fs[array_entry_inputs_def, array_for_code_def, eval_operand_def] >> metis_tac[]) >>
  conj_tac >- (fs[array_entry_inputs_def, array_for_code_def, eval_operand_def] >> metis_tac[]) >>
  conj_tac >- (fs[array_entry_inputs_def, array_for_code_def] >> metis_tac[]) >>
  conj_tac >- fs[array_loop_inv_def] >>
  conj_tac >- fs[array_loop_inv_def] >>
  reverse conj_tac >- (rpt gen_tac >> strip_tac >> qexists_tac `broke` >> simp[]) >>
  suspend "producer"
QED
Resume intcall_array_producer_round[producer]:
  irule gas_outcome_post_mono >>
  qhdtm_x_assum `intcall_stmts_producer`
    (irule_at Any o SRULE [intcall_stmts_producer_def]) >>
  simp[] >>
  qhdtm_assum `stmts_env` (irule_at Any) >> simp[] >>
  qpat_assum `type_stmts _ _ _ = SOME env_b` (irule_at Any) >> simp[] >>
  qhdtm_assum `supported_stmts` (irule_at Any) >> simp[] >>
  conj_tac >- fs[array_for_code_def] >>
  conj_tac >- fs[array_for_code_def] >>
  conj_tac >- fs[array_for_code_def] >>
  rpt gen_tac >> strip_tac >>
  rename1 `intcall_joint_res fp ce_end env_end ee sb1 t` >>
  qexistsl_tac [`ce_end`, `env_end`] >> simp[]
QED
Finalise intcall_array_producer_round
