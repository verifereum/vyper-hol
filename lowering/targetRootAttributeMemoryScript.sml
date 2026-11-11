(* Counted target roots and field extension. *)
Theory targetRootAttributeMemory
Ancestors
  targetMemoryContracts exprSimPopNestedStorageFrame
  targetPlaceSim targetPlaceSimDefs exprSimDefs loweringPosts
  vyperTypeSystem exprLowering compileEnv stmtSimProps
  vyperInterpreter vyperState vyperEvalMisc loweringStateRelDefs
  venomState valueEncoding exprSimHypsDefs exprLoweringProps
  gasContext fragExec
  gasOutcome gasSummary fragGasMode fragGasPath
Libs
  pairLib

Theorem target_name_memory:
  target_pre cenv cx env (NameTarget id) es /\
  type_place_target env (NameTarget id) = SOME vt /\
  compile_get_target_ptr compile_expr cenv (NameTarget id) sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (eval_base_place cx (NameTarget id)) target_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (eval_base_place cx (NameTarget id)) (es,s0)
    (\res ee t. ?pv. res = INL pv /\
      target_post ctx func cenv cx es sa sb s0 ee pv vt op t /\
      (!tr slot tv. pv = PlaceR (StoragePlace tr slot tv) ==>
        slots_in_range (get_storage cx ee tr) (w2n slot) tv /\
        storage_read_live cx tr (get_storage cx ee tr) slot tv) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
    (\res ee r. expr_exit res r)
Proof
  rw[target_pre_def] >>
  qpat_x_assum `type_place_target _ _ = _` mp_tac >>
  simp[Once well_typed_expr_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_all expr_sim_inv_local >> strip_tac >>
  `cenv.ce_var_type id = SOME ty` by fs[expr_sim_inv_def] >>
  qpat_x_assum `compile_get_target_ptr _ _ _ _ = _` mp_tac >>
  simp[compile_get_target_ptr_def, comp_return_def] >> strip_tac >> gvs[] >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
     simp[NoAsms]) >>
  simp[gas_outcome_def, gas_summary_at_def] >> qexists `[]` >> disj1_tac >>
  qexistsl [`INL (PlaceR (MemoryPlace id []))`, `es`, `OK s0`] >>
  conj_tac
  >- simp[gas_marked_exec_def, gas_marked_path_def, gas_path_rules,
          fragGasPathMemTheory.gas_path_mem_rules,
          Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
          type_check_def, assert_def, return_def] >>
  simp[exit_result_def] >>
  `?b. lookup_var p s0 = SOME b` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >> metis_tac[]) >>
  `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
  simp[target_post_def, value_type_place_def] >>
  simp[eval_operand_def, place_ptr_rel_def, mem_path_offset_def,
       place_readable_def, read_place_def, bind_def, get_scopes_def,
       lift_option_type_def, return_def, lift_sum_def, read_memory_path_def,
       evaluate_subscripts_def, wordsTheory.WORD_ADD_0]
QED
