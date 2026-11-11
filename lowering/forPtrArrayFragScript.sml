(* Public fixed-array fragment: semantic readiness is separate from the
   checked target entry and from the source-typing predicate in the rounds. *)
Theory forPtrArrayFrag
Ancestors forPtrArrayLoop forPtrArrayEntry forPtrArraySource forPtrArraySemantic
  forPtrElement forPtrArrayInvariant stmtSimForArrayFrag stmtSimForArrayLoop
  stmtSimForArray bodyPtrPreds bodyPtrDefs bodySim bodyExprPreFacts
  exprSimWordArgs exprSimHypsDefs stmtLowering stmtLoweringMono compileEnv loweringStateRelDefs
  exprLoweringProps loweringPosts stmtSimProps stmtSimDefs stmtFragPtr
  gasSummaryComposePtr gasOutcomeInitialObsPtr fragExec finite_map list valueEncoding
  vyperState vyperInterpreter
Libs monadsyntax

Theorem compile_for_array_frag_ptr:
  body_stmts_ptr_ok cx stmts /\ body_inv tops ctx cenv cx /\
  supported_stmts tops bindings stmts /\
  (!target. supported_stmts_expr_exists
    (expr_abi_decode_target_root target) stmts ==>
    occurs_abi_decode_target target tops) /\
  expr_sim_inv cenv cx env es /\
  ce_locals_declared cenv env /\ locals_alloc_ok cenv env /\
  id NOTIN FDOM env.var_types /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  type_stmts (extend_local env id et F) ty stmts = SOME env_b /\
  EVERY (stmt_exprs_ok cenv) stmts /\
  type_memory_bytes cenv et < 2 ** 64 /\
  type_memory_bytes cenv et = type_memory_size tv /\
  type_memory_bytes cenv et + 64 < dimword (:256) /\
  call_evaluation_safe cx (int_calls_stmts stmts) /\
  frame_ret_ok_ptr d ctx PG func cx RetQ cenv ty /\
  well_typed_expr env (Name (ArrayT et (Fixed (LENGTH vs))) name) /\
  FLOOKUP env.var_types name = SOME (ArrayT et (Fixed (LENGTH vs))) /\
  iterator_unmodified (Array (Name (ArrayT et (Fixed (LENGTH vs))) name)) stmts /\
  ~supported_stmts_expr_exists expr_internal_call_root stmts /\
  lookup_scopes name es.scopes = SOME snapshot /\
  snapshot.type = ArrayTV tv (Fixed (LENGTH vs)) /\
  value_has_type snapshot.type snapshot.value /\ well_formed_type_value snapshot.type /\
  snapshot.value = ArrayV (SArrayV kvs) /\
  vs = array_elements (ArrayTV tv (Fixed (LENGTH vs))) (SArrayV kvs) /\
  LENGTH vs < dimword (:256) /\
  (!gs. eval_iterator cx (Array (Name (ArrayT et (Fixed (LENGTH vs))) name))
    (es with gas_obs := gs) = (INL vs, es with gas_obs := gs)) ==>
  stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
    (stmt_env cenv lctx ty
      (For id et (Array (Name (ArrayT et (Fixed (LENGTH vs))) name)) (LENGTH vs) stmts))
    (eval_stmt cx
      (For id et (Array (Name (ArrayT et (Fixed (LENGTH vs))) name)) (LENGTH vs) stmts)) es
Proof
  strip_tac >> simp[stmt_frag_ptr_def] >>
  map_every qx_gen_tac [`st`, `st'`, `s0`, `G0`, `tn0`, `cenv'`] >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> Cases_on `_0` >>
  suspend "entry"
QED

Resume compile_for_array_frag_ptr[entry]:
  qpat_x_assum `cs' = st'` SUBST_ALL_TAC >>
  qpat_x_assum `cenv = cenv'` (SUBST_ALL_TAC o SYM) >>
  `cenv.ce_alloca_locals` by fs[body_inv_def, IgnAsm `vs = _`] >>
  drule_all for_array_name_source_ptr >> disch_then (qspec_then `st` strip_assume_tac) >>
  `lookup_scopes id es.scopes = NONE` by metis_tac[forPtrSourceScopesTheory.expr_sim_inv_absent_local] >>
  `name <> id` by metis_tac[optionTheory.NOT_NONE_SOME] >>
  `!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z` by
    (fs[ce_locals_declared_def, IgnAsm `vs = _`] >> metis_tac[]) >>
  `!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var` by
    (rpt gen_tac >> strip_tac >>
     drule (SIMP_RULE std_ss [cs_mono_def] (cj 2 compile_stmt_cs_mono)) >> simp[]) >>
  drule_all compile_for_array_code_ready_framed >> strip_tac >>
  suspend "loop"
QED

Resume compile_for_array_frag_ptr[loop]:
  `tv' = tv /\ entry = snapshot` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `tv' = tv` SUBST_ALL_TAC >>
  qpat_x_assum `entry = snapshot` SUBST_ALL_TAC >>
  rename1 `lookup_var bp s0 = SOME arr_base` >>
  `ptr_covers G0 tn0 bp s0 (LENGTH vs * type_memory_size tv)` by
    (fs[bodyPtrDefsTheory.ptr_covers_def, IgnAsm `vs = _`] >> decide_tac) >>
  `type_memory_bytes cenv et < dimword (:256)` by decide_tac >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0 /\
   ghost_inv d cenv cx (es with gas_obs := []) G0 tn0 s0` by
    simp[ghost_inv_gas_obs, IgnAsm `vs = _`] >>
  `lookup_block s0.vs_current_bb func.fn_blocks = SOME
    <|bb_label := st.cs_current_bb; bb_instructions := st.cs_current_insts ++
      [ainst; mk_inst (st.cs_next_id + 1) JMP [Label entry'] []]|>` by
    simp[IgnAsm `vs = _`] >>
  drule_all for_array_code_initialize_ptr >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  suspend "counted"
QED

Resume compile_for_array_frag_ptr[counted]:
  `!j. j < LENGTH vs ==> value_has_type tv (EL j vs) /\ val_wf tv (EL j vs)` by
    (rpt gen_tac >> strip_tac >>
     `value_has_type (ArrayTV tv (Fixed (LENGTH vs))) (ArrayV (SArrayV kvs)) /\
      well_formed_type_value (ArrayTV tv (Fixed (LENGTH vs)))` by
       fs[IgnAsm `vs = _`] >>
     drule_all fixed_array_elements_typed >>
     strip_tac >> metis_tac[]) >>
  suspend "static"
QED

Resume compile_for_array_frag_ptr[static]:
  `!j. j < LENGTH vs ==> w2n arr_base + j * type_memory_bytes cenv et < dimword (:256)` by
    (rpt strip_tac >>
     `j * type_memory_size tv <= LENGTH vs * type_memory_size tv` by simp[] >>
     simp[IgnAsm `vs = _`] >> decide_tac) >>
  `compile_stmts bc (InLoop exit incr) ty stmts sb0 = ((),sb1)` by
    fs[array_for_code_def, IgnAsm `vs = _`] >>
  `cs_extends sb0 sb1 /\ sb0.cs_next_var <= sb1.cs_next_var` by metis_tac[] >>
  drule array_body_compiler_env >> strip_tac >>
  suspend "layout"
QED

Resume compile_for_array_frag_ptr[layout]:
  `!ei. lookup_scopes name ei.scopes = SOME snapshot /\ lookup_scopes id ei.scopes = NONE ==>
    not_local_ptr bc (FEMPTY :: ei.scopes) p'` by
    (rpt strip_tac >>
     `local_ptrs_reserved bc sa /\ FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p') (type_memory_bytes cenv et))` by
       fs[array_for_code_def, IgnAsm `vs = _`] >>
     fs[not_local_ptr_def, local_ptrs_reserved_def, lookup_scopes_def,
       IgnAsm `vs = _`] >> metis_tac[optionTheory.NOT_NONE_SOME]) >>
  suspend "callback"
QED

Resume compile_for_array_frag_ptr[callback]:
  qabbrev_tac `P = \ei. expr_sim_inv cenv cx env ei /\ lookup_scopes id ei.scopes = NONE` >>
  `!j ei. j < LENGTH vs /\
    P ei /\
    lookup_scopes name ei.scopes = SOME snapshot /\ lookup_scopes id ei.scopes = NONE ==>
    stmt_frag_ptr d ctx PG func cx (InLoop exit incr) RetQ bc
      (stmts_env bc (InLoop exit incr) ty stmts) (eval_stmts cx stmts)
      (ei with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL j vs; popped := []|>)) :: ei.scopes;
        gas_obs := []|>)` by
    (rpt strip_tac >> qpat_x_assum `P ei` mp_tac >> simp[Abbr `P`] >> strip_tac >>
     `value_has_type tv (EL j vs)` by metis_tac[] >>
     `expr_sim_inv cenv cx env (ei with gas_obs := [])` by simp[] >>
     drule_all for_array_body_fragment_ptr >>
     disch_then (qspecl_then [`incr`, `exit`] mp_tac) >> simp[IgnAsm `vs = _`]) >>
  suspend "preserve"
QED

Resume compile_for_array_frag_ptr[preserve]:
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    fs[body_inv_def, IgnAsm `vs = _`] >>
  `!j ei obs ee. j < LENGTH vs /\
    P ei /\
    (do push_scope_with_var id tv (EL j vs);
        finally (try (do eval_stmts cx stmts; return F od)
          handle_loop_exception) pop_scope od) (ei with gas_obs := obs) = (INL F,ee) ==>
    P ee` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `P ei` mp_tac >> simp[Abbr `P`] >> strip_tac >>
     `value_has_type tv (EL j vs)` by metis_tac[] >>
     `expr_sim_inv cenv cx env (ei with gas_obs := obs)` by simp[] >>
     drule_all for_array_round_semantic >> simp[IgnAsm `vs = _`]) >>
  suspend "invoke"
QED

Resume compile_for_array_frag_ptr[invoke]:
  `same_frame cenv bc` by
    (drule_then irule bodySimDeclCasesTheory.declare_local_same_frame >> simp[IgnAsm `vs = _`]) >>
  `fn_has_code sb0 sb1 func /\ ~bc.ce_is_ctor` by
    (fs[array_for_code_def, same_frame_def, IgnAsm `vs = _`] >>
     qpat_x_assum `bc with <|ce_vars := _; ce_dynarray_capacity := _; ce_var_type := _|> = cenv`
       mp_tac >> simp[compile_env_component_equality] >> metis_tac[]) >>
  drule_all fn_has_code_start >> strip_tac >>
  `!x. not_fresh_at st x ==> not_fresh_at sa x /\ x <> dv /\ x <> ov /\ x <> ep /\ x <> idx /\ x <> nv` by metis_tac[] >>
  suspend "returns"
QED

Resume compile_for_array_frag_ptr[returns]:
  `!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) \/
    cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at st x` by
    (fs[ret_pc_ok_def, IgnAsm `vs = _`] >> metis_tac[]) >>
  `FLOOKUP (extend_local env id et F).var_types name =
    SOME (ArrayT et (Fixed (LENGTH vs)))` by simp[vyperTypeSystemTheory.extend_local_def, FLOOKUP_UPDATE, IgnAsm `vs = _`] >>
  `!j. j < LENGTH vs ==> value_has_type tv (EL j vs) /\ val_wf tv (EL j vs) /\
    w2n arr_base + j * type_memory_bytes cenv et < dimword (:256)` by metis_tac[] >>
  `gas_admissible (eval_for cx tv id stmts vs) (stmt_res_ok lctx) es` by
    (irule for_array_source_admissible >> goal_assum (drule_at Any) >>
     simp[IgnAsm `vs = _`] >> qexists_tac `name` >> simp[IgnAsm `vs = _`]) >>
  `P es` by simp[Abbr `P`, IgnAsm `vs = _`] >>
  drule array_code_loop_counted_ptr >> disch_then drule >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then (drule_at (Pat `type_stmts _ _ _ = _`)) >>
  disch_then (drule_at (Pat `snapshot.type = _`)) >>
  disch_then (drule_all o SIMP_RULE list_ss []) >>
  strip_tac >> suspend "compose"
QED

Resume compile_for_array_frag_ptr[compose]:
  drule_all gas_outcome_ptr_prefix >> disch_tac >>
  drule (iffRL (Q.INST [`gs` |-> `[]`] gas_outcome_ptr_initial_obs)) >> disch_tac >>
  drule_all (SIMP_RULE bool_ss [] (Q.INST [`n` |-> `LENGTH vs`] for_array_source_prefix_ptr)) >>
  disch_tac >> irule gas_outcome_ptr_conseq >>
  goal_assum (drule_at Any) >> simp[NoAsms] >>
  conj_tac >- suspend "post" >>
  rpt gen_tac >> strip_tac >> fs[]
QED

Resume compile_for_array_frag_ptr[post]:
  rpt gen_tac >> strip_tac >>
  drule_all for_array_done_stmt_post_ptr >>
  disch_then (qspec_then `lctx` strip_assume_tac) >>
  qpat_x_assum `vs = _` kall_tac >> gvs[]
QED

Finalise compile_for_array_frag_ptr
