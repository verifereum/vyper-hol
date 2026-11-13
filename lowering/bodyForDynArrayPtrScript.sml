Theory bodyForDynArrayPtr
Ancestors forPtrArrayFrag bodyPtrPreds bodyPtrDefs bodySimDeclCases
  stmtSimForArray exprSimHypsDefs exprSimHyps bodySim bodyExprPreFacts
  vyperAST vyperInterpreter vyperState vyperValue vyperTyping
  vyperTypeSystem vyperTypeInvariants vyperTypeValues
  supportedStmts supportedStmtTraverse allocLimits compileVyper
  vyperTypeCallGraph exprLoweringProps finite_map list vyperTypeCallStackSoundness
  bodyDynArraySource whitelistForIterDynFrag forPtrDynArraySource forPtrDynArrayEntry
  forPtrDynArrayLoop stmtLowering stmtLoweringMono compileEnv stmtSimProps
  loweringStateRelDefs stmtSimDefs loweringPosts fragExec
  whitelistForIterDynLoop stmtSimForArrayFrag stmtSimForArrayLoop
  forPtrArrayInvariant venomState gasSummaryComposePtr gasOutcomeInitialObsPtr
  forPtrArraySource forPtrArrayEntry
Libs monadsyntax

val _ = Parse.hide "body";

Theorem body_for_dynarray_name_ptr:
  (!tenv s'' tyv t s3 vs t' s4 x t''.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' = (INL tyv,t) /\
     eval_iterator cx (Array (Name (ArrayT typ (Dynamic cap)) name)) s3 = (INL vs,t') /\
     check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s4 = (INL x,t'') ==>
     body_for_ptr_ok cx tyv id body vs) /\
  (!tenv s'' tyv t.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' = (INL tyv,t) ==>
     body_iterator_ptr_ok cx (Array (Name (ArrayT typ (Dynamic cap)) name))) ==>
  body_stmt_ptr_ok cx (For id typ (Array (Name (ArrayT typ (Dynamic cap)) name)) n body)
Proof
  rw[body_stmt_ptr_ok_def] >>
  `cap <= n` by
    fs[supported_stmt_def, supported_iterator_def] >>
  drule_all dynarray_name_source_ready >> strip_tac >> gvs[] >>
  rename1 `evaluate_type (get_tenv cx) typ = SOME tv` >>
  rename1 `lookup_scopes name es.scopes = SOME snapshot` >>
  rename1 `snapshot.value = ArrayV (DynArrayV vs)` >>
  `body_for_ptr_ok cx tv id body (MAP Value vs)` by
    (qpat_x_assum `!s3 vs t' s4 t''. _` mp_tac >>
     simp[check_def, assert_def, compatible_bound_def, return_def] >>
     disch_then irule >> simp[] >>
     qexistsl_tac [`es with gas_obs := es.gas_obs`, `es with gas_obs := es.gas_obs`] >> simp[]) >>
  `supported_stmts tops bindings body /\
   ~supported_stmts_expr_exists expr_internal_call_root body` by
    fs[supported_stmt_def] >>
  `!target. supported_stmts_expr_exists
      (expr_abi_decode_target_root target) body ==>
      occurs_abi_decode_target target tops` by
    fs[supported_stmt_expr_exists_def] >>
  `name <> id` by metis_tac[optionTheory.NOT_NONE_SOME] >>
  `cenv.ce_alloca_locals /\ supported_program tops /\
   get_module_code cx NONE = SOME tops` by fs[body_inv_def] >>
  `stmts_exprs_ok (cenv with ce_var_type updated_by (id =+ SOME typ)) body /\
   type_memory_bytes cenv typ < 2 ** 64` by
    fs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
       stmts_exprs_ok_thm, alloc_limits_stmt_def, stmt_valued_return_def] >>
  `call_evaluation_safe cx (int_calls_stmts body)` by
    (fs[int_calls_stmt_def] >> metis_tac[call_evaluation_safe_append_right]) >>
  `type_memory_bytes cenv typ = type_memory_size tv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `type_memory_bytes cenv typ + 64 < dimword (:256)` by
    (fs[wordsTheory.dimword_def] >> decide_tac) >>
  suspend "compile"
QED

Resume body_for_dynarray_name_ptr[compile]:
  simp[stmt_frag_ptr_def] >>
  map_every qx_gen_tac [`st`, `st'`, `s0`, `G0`, `tn0`, `cenv'`] >> strip_tac >>
  `compile_stmt cenv lctx ret_ty
    (For id typ (Array (Name (ArrayT typ (Dynamic cap)) name)) n body) st = ((),st')` by
    (gvs[stmt_env_def, declare_stmt_local_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, AllCaseEqs()] >> pairarg_tac >> gvs[]) >>
  `!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z` by simp[] >>
  `!c lc sa sb. compile_stmts c lc ret_ty body sa = ((),sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var` by
    (rpt gen_tac >> strip_tac >>
     drule (SIMP_RULE std_ss [cs_mono_def] (cj 2 compile_stmt_cs_mono)) >> simp[]) >>
  drule_all compile_for_dynarray_code_ready >> strip_tac >>
  suspend "entry"
QED

Resume body_for_dynarray_name_ptr[entry]:
  drule_all for_dynarray_local_resources_ptr >> strip_tac >>
  rename1 `lookup_var dp s0 = SOME arr_base` >>
  `ptr_covers G0 tn0 dp s0 32 /\
   ptr_covers G0 tn0 dp s0 (LENGTH vs * type_memory_size tv)` by
    (fs[ptr_covers_def] >> decide_tac) >>
  `MEM ainst (fn_insts func)` by
    (irule lookup_block_fn_insts >>
     qpat_assum `lookup_block st.cs_current_bb _ = _` (irule_at (Pos hd)) >> simp[]) >>
  `not_local_ptr cenv es.scopes p` by
    (`bc.ce_imm_alloca = cenv.ce_imm_alloca /\ local_ptrs_reserved bc sa /\
      FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes cenv typ)) /\
      (!name. name <> id ==> FLOOKUP bc.ce_vars name = FLOOKUP cenv.ce_vars name)` by
       fs[dynarray_for_code_def, compile_env_component_equality] >>
     drule_all array_allocation_safe >> simp[]) >>
  `ALL_DISTINCT [lv;p;idx;g;vld;dp]` by
    (fs[ALL_DISTINCT, MEM] >> metis_tac[]) >>
  `!x q. cenv.ce_return_pc = SOME (PtrVar (Var x) q) ==> not_fresh_at st x` by
    fs[ret_pc_ok_def] >>
  `type_memory_bytes cenv typ < dimword (:256)` by decide_tac >>
  `lookup_block s0.vs_current_bb func.fn_blocks = SOME
    <|bb_label := st.cs_current_bb; bb_instructions := st.cs_current_insts ++
      [mk_inst st.cs_next_id MLOAD [Var dp] [lv];
       mk_inst (st.cs_next_id + 1) ALLOCA [Lit (n2w (type_memory_bytes cenv typ))] [p];
       mk_inst (st.cs_next_id + 2) JMP [Label entry] []]|>` by simp[] >>
  qpat_x_assum `ainst = _` SUBST_ALL_TAC >>
  `?dst t H un.
    for_array_inv_ptr ctx func cenv cx vs tv id idx dp arr_base p dst
      (type_memory_bytes cenv typ)
      (mk_inst (st.cs_next_id + 1) ALLOCA [Lit (n2w (type_memory_bytes cenv typ))] [p])
      cond st s0 G0 tn0 d name snapshot 0 es H un t /\
    lookup_var lv t = SOME (n2w (LENGTH vs)) /\
    FLOOKUP H lv = NONE /\ op_taint un (Var lv) = {} /\
    gas_path_ptr (cx_dead cx) 0 ctx func PG G0 tn0 s0 0 H un (OK t)` by
    (irule for_dynarray_code_initialize_ptr >> simp[] >>
     goal_assum (drule_at (Pat `lookup_block entry _ = _`)) >>
     simp[] >> qexistsl_tac [`st.cs_next_id + 2`, `st.cs_next_id`] >>
     fs[ALL_DISTINCT, MEM] >> metis_tac[]) >>
  suspend "counted"
QED

Resume body_for_dynarray_name_ptr[counted]:
  `!j. j < LENGTH vs ==> value_has_type tv (EL j vs) /\ val_wf tv (EL j vs)` by
    (metis_tac[dynarray_elements_typed]) >>
  `!j. j < LENGTH vs ==>
    w2n arr_base + 32 + j * type_memory_bytes cenv typ < dimword (:256)` by
    (rpt strip_tac >>
     `j * type_memory_size tv <= LENGTH vs * type_memory_size tv` by simp[] >>
     simp[]) >>
  `compile_stmts bc (InLoop exit incr) ret_ty body sb0 = ((),sb1)` by
    fs[dynarray_for_code_def] >>
  `cs_extends sb0 sb1 /\ sb0.cs_next_var <= sb1.cs_next_var` by metis_tac[] >>
  drule array_body_compiler_env >> strip_tac >>
  suspend "callback"
QED

Resume body_for_dynarray_name_ptr[callback]:
  qabbrev_tac `P = \ei. expr_sim_inv cenv cx env ei /\ lookup_scopes id ei.scopes = NONE` >>
  `!j ei. j < LENGTH vs /\ P ei /\
    lookup_scopes name ei.scopes = SOME snapshot /\ lookup_scopes id ei.scopes = NONE ==>
    stmt_frag_ptr d ctx PG func cx (InLoop exit incr) RetQ bc
      (stmts_env bc (InLoop exit incr) ret_ty body) (eval_stmts cx body)
      (ei with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL j vs; popped := []|>)) :: ei.scopes;
        gas_obs := []|>)` by
    (rpt strip_tac >> qpat_x_assum `P ei` mp_tac >> simp[Abbr `P`] >> strip_tac >>
     `body_stmts_ptr_ok cx body` by
       (fs[body_for_ptr_ok_def] >> first_x_assum irule >>
        Cases_on `vs` >> gvs[read_result_def, return_def]) >>
     `value_has_type tv (EL j vs)` by metis_tac[] >>
     `expr_sim_inv cenv cx env (ei with gas_obs := [])` by simp[] >>
     drule_all forPtrArraySemanticTheory.for_array_body_fragment_ptr >>
     disch_then (qspecl_then [`incr`, `exit`] mp_tac) >> simp[]) >>
  `!j ei obs ee. j < LENGTH vs /\ P ei /\
    (do push_scope_with_var id tv (EL j vs);
        finally (try (do eval_stmts cx body; return F od)
          handle_loop_exception) pop_scope od) (ei with gas_obs := obs) = (INL F,ee) ==>
    P ee` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `P ei` mp_tac >> simp[Abbr `P`] >> strip_tac >>
     `value_has_type tv (EL j vs)` by metis_tac[] >>
     `expr_sim_inv cenv cx env (ei with gas_obs := obs)` by simp[] >>
     drule_all forPtrArraySemanticTheory.for_array_round_semantic >> simp[]) >>
  suspend "resources"
QED

Resume body_for_dynarray_name_ptr[resources]:
  `!j ei H un u. j < LENGTH vs /\
    for_array_inv_ptr ctx func cenv cx vs tv id idx dp arr_base p dst
      (type_memory_bytes cenv typ)
      (mk_inst (st.cs_next_id + 1) ALLOCA [Lit (n2w (type_memory_bytes cenv typ))] [p])
      bod st s0 G0 tn0 d name snapshot j ei H un u ==>
    ptr_covers H un dp u (32+(j+1)*type_memory_bytes cenv typ) /\
    (!m. mem_agree_outside un.t_mem u.vs_memory m ==>
      val_in_memory tv (EL j vs) (w2n arr_base+32+j*type_memory_bytes cenv typ) m)` by
    (rpt gen_tac >> disch_then strip_assume_tac >>
     gnvs[for_array_inv_ptr_def, array_loop_inv_def, eval_operand_def] >>
     RULE_L_ASSUM_TAC CONJUNCTS >>
     qpat_x_assum `stmt_state_rel ctx func cenv cx es s0` kall_tac >>
     qpat_x_assum `stmt_state_rel ctx func cenv cx es t` kall_tac >>
     drule_all for_dynarray_local_resources_ptr >> disch_then strip_assume_tac >>
     gnvs[] >>
     `type_memory_size tv * (j+1) + 32 <= sz` by
       (`SUC j * type_memory_size tv <= LENGTH vs * type_memory_size tv` by simp[] >>
        qpat_x_assum `SUC j * _ <= _` mp_tac >>
        pure_rewrite_tac[arithmeticTheory.MULT_CLAUSES] >> simp[arithmeticTheory.RIGHT_ADD_DISTRIB] >>
        decide_tac) >>
     fs[ptr_covers_def] >> decide_tac) >>
  suspend "invoke"
QED

Resume body_for_dynarray_name_ptr[invoke]:
  `!ei. lookup_scopes name ei.scopes = SOME snapshot /\
    lookup_scopes id ei.scopes = NONE ==> not_local_ptr bc (FEMPTY :: ei.scopes) p` by
    (rpt strip_tac >>
     `local_ptrs_reserved bc sa /\
      FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes cenv typ))` by
       fs[dynarray_for_code_def] >>
     fs[not_local_ptr_def, local_ptrs_reserved_def, lookup_scopes_def] >>
     metis_tac[optionTheory.NOT_NONE_SOME]) >>
  `same_frame cenv bc` by
    (drule_then irule bodySimDeclCasesTheory.declare_local_same_frame >> simp[]) >>
  `fn_has_code sb0 sb1 func /\ ~bc.ce_is_ctor` by
    (fs[dynarray_for_code_def, same_frame_def] >>
     qpat_x_assum `bc with <|ce_vars := _; ce_dynarray_capacity := _; ce_var_type := _|> = cenv`
       mp_tac >> simp[compile_env_component_equality] >> metis_tac[]) >>
  drule_all fn_has_code_start >> strip_tac >>
  `!x. not_fresh_at st x ==> x <> dv /\ x <> ov /\ x <> tot /\ x <> ep /\ x <> idx /\ x <> nv` by metis_tac[] >>
  `!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) \/
    cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at st x` by
    (fs[ret_pc_ok_def] >> metis_tac[]) >>
  `FLOOKUP (extend_local env id typ F).var_types name = SOME (ArrayT typ (Dynamic cap))` by
    simp[vyperTypeSystemTheory.extend_local_def, FLOOKUP_UPDATE] >>
  `!j. j < LENGTH vs ==> value_has_type tv (EL j vs) /\ val_wf tv (EL j vs) /\
    w2n arr_base+32+j*type_memory_bytes cenv typ < dimword (:256)` by metis_tac[] >>
  `LENGTH vs < dimword (:256)` by decide_tac >>
  `gas_admissible (eval_for cx tv id body (MAP Value vs)) (stmt_res_ok lctx) es` by
    (fs[gasContextTheory.gas_admissible_def] >> rpt gen_tac >> strip_tac >>
     qpat_x_assum `!gs res es'. _` (qspec_then `gs` mp_tac) >>
     simp[Once evaluate_def, lift_option_type_def, lift_option_def, bind_return,
       bind_def, ignore_bind_def, compatible_bound_def, check_def, assert_def, return_def]) >>
  `P es` by simp[Abbr `P`] >>
  `not_fresh_at sa lv` by metis_tac[] >>
  `st.cs_next_var <= sa.cs_next_var` by
    (spose_not_then assume_tac >>
     `not_fresh_at st (STRING #"%" (toString sa.cs_next_var))` by
       (simp[not_fresh_at_def] >> decide_tac) >>
     `not_fresh_at sa (STRING #"%" (toString sa.cs_next_var))` by metis_tac[] >>
     pop_assum mp_tac >> rewrite_tac[not_fresh_at_def] >>
     disch_then (qspec_then `sa.cs_next_var` mp_tac) >> simp[]) >>
  `sa.cs_next_var <= sb0.cs_next_var` by
    (qpat_assum `dynarray_for_code _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [dynarray_for_code_def]) >>
     mp_tac (Q.SPECL [`cenv`, `Var ep`, `Var p`, `type_memory_bytes cenv typ`,
       `LocMemory`, `F`, `typ`, `typ`, `sa`] (cj 6 ci_mono_stmt_helpers)) >>
     simp[ci_mono_def]) >>
  `gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_for cx tv id body (MAP Value vs)) (es,t,H,un)
    (\res ee gf tf u. res = INL () /\
      for_array_done_ptr ctx func cenv cx exit st s0 G0 tn0 d ee gf tf u)
    (\res ee gt r. ?ex. res = INR ex /\
      !tail. stmt_exit_ptr RetQ (ee with gas_obs := tail) (INR ex) gt r)` by
    (drule (Q.INST
       [`env` |-> `extend_local env id typ F`, `elem` |-> `typ`,
        `bound` |-> `Dynamic cap`, `aty` |-> `ArrayT typ (Dynamic cap)`,
        `env'` |-> `env_b`]
       dynarray_code_loop_counted_ptr) >>
     disch_then (irule o SIMP_RULE list_ss [] o Q.INST [`k` |-> `0`] o SPEC_ALL) >>
     simp[] >>
     conj_tac >- (goal_assum (drule_at Any) >> fs[dynarray_for_code_def]) >>
     conj_tac >- (goal_assum (drule_at Any) >> fs[dynarray_for_code_def] >> metis_tac[]) >>
     conj_tac >- (qexists_tac `lctx` >> simp[]) >>
     conj_tac >- (qexistsl_tac [`bindings`, `tops`] >> simp[]) >>
     qexistsl_tac [`P`, `arr_base`, `cap`, `dst`, `env`, `env_b`, `name`,
       `ret_ty`, `snapshot`, `typ`] >>
     qpat_assum `type_memory_bytes cenv typ = type_memory_size tv`
       (fn th => SUBST_ALL_TAC (SYM th)) >>
     fs[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "compose"
QED

Resume body_for_dynarray_name_ptr[compose]:
  `cenv' = cenv` by
    (gvs[stmt_env_def, declare_stmt_local_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, AllCaseEqs()] >> pairarg_tac >> gvs[]) >>
  drule_all gas_outcome_ptr_prefix >> disch_tac >>
  drule (iffRL (Q.INST [`gs` |-> `[]`] gas_outcome_ptr_initial_obs)) >> disch_tac >>
  `!msg. assert T msg = return ()` by
    simp[FUN_EQ_THM, vyperStateTheory.assert_def, return_def] >>
  `gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_stmt cx (For id typ (Array (Name (ArrayT typ (Dynamic cap)) name)) n body))
    (es,s0,G0,tn0)
    (\res ee gf tf u. res = INL () /\
      for_array_done_ptr ctx func cenv cx exit st s0 G0 tn0 d ee gf tf u)
    (\res ee gt r. ?ex. res = INR ex /\
      !tail. stmt_exit_ptr RetQ (ee with gas_obs := tail) (INR ex) gt r)` by
    (simp[Once evaluate_def, lift_option_type_def, lift_option_def, bind_return] >>
     irule for_values_prefix_outcome_ptr >> simp[] >>
     simp[compatible_bound_def, check_def, ignore_bind_def, bind_return]) >>
  irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >> simp[NoAsms] >>
  conj_tac >- suspend "post" >>
  rpt gen_tac >> strip_tac >> fs[]
QED

Resume body_for_dynarray_name_ptr[post]:
  rpt gen_tac >> strip_tac >>
  drule_all for_array_done_stmt_post_ptr >>
  disch_then (qspec_then `lctx` strip_assume_tac) >> gvs[]
QED

Finalise body_for_dynarray_name_ptr

