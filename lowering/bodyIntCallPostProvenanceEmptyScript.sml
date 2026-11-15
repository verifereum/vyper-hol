(* Empty values own the allocation on their initialized execution witness. *)
Theory bodyIntCallPostProvenanceEmpty
Ancestors
  bodyIntCallProducerInterface exprSimAggregates exprSimBufferEmptyExec
  exprSimAggregateLayout exprSimBuffer exprSimHyps exprSimHypsDefs exprSimDefs
  exprSimProps loweringStateRelDefs
  aggregateCountedOutcome aggregateCountedOutcomeFacts exprLoweringProps loweringPosts
  gasOutcome gasSummary gasContext fragGasMode fragGasPath
  vyperInterpreter vyperState vyperAST compileEnv vyperTypeSystem
  vyperTypeBuiltins vyperContext exprLowering
Libs monadsyntax

Theorem intcall_empty_outcome:
  expr_body_pre cenv cx env (TypeBuiltin ann Empty ty args) es /\
  compile_expr cenv (expr_type (TypeBuiltin ann Empty ty args))
    (TypeBuiltin ann Empty ty args) sa = (vv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (eval_expr cx (TypeBuiltin ann Empty ty args)) expr_vv_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (eval_expr cx (TypeBuiltin ann Empty ty args)) (es,s0)
    (\res ee t. ?tv. res = INL tv /\
      vv_post ctx func cenv cx (TypeBuiltin ann Empty ty args)
        es sa sb s0 ee tv vv t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      intcall_vv_provenance cenv cx (expr_type (TypeBuiltin ann Empty ty args))
        sa sb ee tv vv t)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `ann = ty /\ args = []` by
    gvs[expr_body_pre_def, well_typed_expr_def, type_builtin_result_ok_def,
        well_typed_type_builtin_args_def, type_builtin_args_length_ok_def] >>
  gvs[] >> rename1 `TypeBuiltin ty Empty ty []` >>
  Cases_on `is_word_type ty` >- suspend "word" >>
  `?tvt. evaluate_type (get_tenv cx) ty = SOME tvt` by
    (drule expr_body_pre_type_evaluates >> simp[expr_type_def, optionTheory.IS_SOME_EXISTS]) >>
  `!gs. eval_expr cx (TypeBuiltin ty Empty ty []) (es with gas_obs := gs) =
    (INL (Value (default_value tvt)), es with gas_obs := gs)` by
    simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
         assert_def, return_def, raise_def, lift_sum_def,
         type_builtin_args_length_ok_def, evaluate_type_builtin_def,
         Once evaluate_def] >>
  gvs[compile_expr_type_builtin_dispatch, Once compile_expr_def,
      comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `type_memory_bytes cenv ty < dimword (:256)` by
    (fs[expr_body_pre_def, allocLimitsTheory.alloc_limits_expr_def] >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  drule_all empty_type_buffer_size >> strip_tac >>
  drule_all compile_builtin_empty_complex_run >> strip_tac >>
  drule_all empty_complex_gas_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  suspend "package"
QED

Resume intcall_empty_outcome[word]:
  `expr_vv_sim ctx func cenv cx (expr_type (TypeBuiltin ty Empty ty []))
    (TypeBuiltin ty Empty ty []) es` by
    (irule (SRULE [expr_vv_case_def] (Q.SPEC `F` compile_empty_case)) >>
     goal_assum (drule_at Any)) >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_vv_sim_def] >>
  disch_then drule_all >> strip_tac >>
  gvs[compile_expr_type_builtin_dispatch, Once compile_expr_def, comp_return_def,
      expr_type_def] >>
  drule counted_outcome_conseq >> disch_then irule >>
  simp[intcall_vv_provenance_word]
QED

Resume intcall_empty_outcome[package]:
  `stmt_state_rel ctx func cenv cx (es with gas_obs := [])
     (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`t.vs_gas_readings`,
       `LENGTH sb.cs_current_insts`, `[]`] mp_tac) >> simp[NoAsms]) >>
  simp[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INL (Value (default_value tvt))`, `es`,
    `OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)`] >>
  conj_tac >- simp[gas_marked_exec_def, gas_marked_path_def] >>
  simp[] >> conj_tac >- suspend "post" >>
  suspend "provenance"
QED

Resume intcall_empty_outcome[post]:
  once_rewrite_tac[GSYM (Q.INST [`gs` |-> `[]`] vv_post_initial_gas)] >>
  drule_all empty_type_default_memory >> strip_tac >>
  irule (SRULE [vyperASTTheory.expr_type_def]
    (Q.INST [`e` |-> `TypeBuiltin ty Empty ty []`,
             `p` |-> `base_ptr buf`] (SPEC_ALL buffer_memory_vv_post))) >>
  goal_assum (drule_at Any) >>
  simp[contextTheory.base_ptr_def, valueEncodingProofsTheory.val_wf_default_value_proof] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!name b len. local_region _ _ _ _ _ _ ==> _ \/ _` drule >>
      strip_tac >> first_x_assum irule >> decide_tac) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!aid b len. _ ==> regions_disjoint _ _ b len` drule >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def] >> strip_tac >>
      first_x_assum irule >> decide_tac) >>
  drule_all expr_sim_inv_memory_size >> strip_tac >>
  simp[val_footprint_le, valueEncodingProofsTheory.val_wf_default_value_proof] >>
  rpt strip_tac >>
  `local_region cenv es.scopes s0 n lb lsz` by
    (irule exprSimPropsTheory.local_region_frame >> conj_tac
     >- (qexists_tac `func` >> gvs[stmt_state_rel_def, state_rel_def]) >>
     qexistsl [`sa`, `es.scopes`, `t`] >> simp[]) >>
  qpat_x_assum `!name b len. local_region _ _ s0 _ _ _ ==> _` drule >>
  simp[arithmeticTheory.ADD_COMM]
QED

Resume intcall_empty_outcome[provenance]:
  simp[intcall_vv_provenance_def, expr_type_def, contextTheory.base_ptr_def] >>
  rpt strip_tac >>
  gvs[read_result_def, return_def] >> disj1_tac >>
  qexistsl_tac [`sa.cs_next_id`, `w2n w`, `type_memory_bytes cenv ty`] >>
  simp[] >> conj_tac
  >- (drule_all expr_sim_inv_memory_size >> strip_tac >>
      simp[val_footprint_le, valueEncodingProofsTheory.val_wf_default_value_proof]) >>
  rpt strip_tac >>
  `local_region cenv es.scopes s0 n lb lsz` by
    (irule local_region_frame >> conj_tac
     >- (qexists_tac `func` >> gvs[stmt_state_rel_def, state_rel_def]) >>
     qexistsl [`sa`, `es.scopes`, `t`] >>
     gvs[local_region_def, venomStateTheory.lookup_var_def]) >>
  qpat_x_assum `!name b len. local_region _ _ s0 _ _ _ ==> _` drule >> simp[]
QED

Finalise intcall_empty_outcome
