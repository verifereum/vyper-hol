(* A retained Name prefix and a counted index execution. *)
Theory bodyPtrSubscriptNamedIndex
Ancestors
  bodyPtrSubscriptNamedRoot bodyPtrSubscriptIndexExecution
  exprSimNameValue argsTailPtr gasSummaryComposePtr gasExemptCert
  vyperInterpreter vyperState fragGasPathPtr bodyPtrDefs loweringPosts
  exprLoweringProps compileEnv venomState context exprSimDefs
  gasSummary fragGasPath fragGasMode gasStorage vyperStorageTrace
  vyperStorageFootprint

Theorem named_prefix_counted[local]:
  lookup_scopes id es.scopes = SOME entry /\ ~s0.vs_halted /\
  storage_trace_frame (next (PlaceR (MemoryPlace id []))) /\
  gas_outcome_ptr D tops (ctx,func) PG cx st0
    (next (PlaceR (MemoryPlace id [])))
    (es with gas_obs := [],s0,G0,tn0) Q R ==>
  gas_outcome_ptr D tops (ctx,func) PG cx st0
    (bind (eval_expr cx (Name ann id)) next) (es,s0,G0,tn0) Q R
Proof
  strip_tac >> irule gas_outcome_ptr_bind_normal >>
  qexistsl_tac [`G0`, `[]`, `es`, `s0`, `tn0`,
                `PlaceR (MemoryPlace id [])`] >>
  conj_tac
  >- (rpt strip_tac >>
      irule gas_exempt_cert_bind_result >> BETA_TAC >>
      goal_assum (drule_at Any) >> simp[] >>
      simp[gas_marked_exec_def, gas_marked_path_def, gas_path_rules,
           Once evaluate_def, bind_def, get_scopes_def, return_def,
           type_check_def, assert_def, check_def, ignore_bind_def]) >>
  simp[gas_marked_exec_def, gas_marked_path_def, gas_path_rules,
       gas_path_ptr_rules,
       Once evaluate_def, bind_def, get_scopes_def, return_def,
       type_check_def, assert_def, check_def, ignore_bind_def]
QED

Theorem named_root_index_execution:
  expr_body_pre cenv cx env (Name ann id) es /\
  compile_expr cenv bty (Name ann id) sa = (vv,sb) /\
  expr_sim_ptr d ctx PG func cenv cx ty idx (es with gas_obs := []) /\
  lower_value compile_expr cenv ty idx sb = (op,sk) /\
  fn_has_code sb sk func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sb /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sb x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sb x) /\
  gas_admissible (bind (eval_expr cx idx) (read_result cx)) expr_res_ok
    (es with gas_obs := []) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv H d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_ptr (\H. cx_dead H cx) (cx_tops cx) (ctx,func) PG cx st0
    (bind (eval_expr cx (Name ann id))
      (\base. bind (bind (eval_expr cx idx) (read_result cx))
        (\v. return (base,v)))) (es,s0,G0,tn0)
    (\H res ee G tn t. ?p sz w v.
      res = INL (PlaceR (MemoryPlace id []),v) /\
      vv = LocatedValue ann (mk_ptr (Var p) LocMemory) /\
      expr_post H ctx func cenv cx idx (es with gas_obs := []) sb sk s0 ee v op t /\
      t.vs_current_bb = sk.cs_current_bb /\
      t.vs_inst_idx = LENGTH sk.cs_current_insts /\
      ghost_inv H d cenv cx ee G tn t /\
      ptr_val_ok cx (post_value_type cenv idx) v op G tn t /\
      (~is_word_type (post_value_type cenv idx) ==> ptr_buf_ok cenv idx op G t) /\
      ghost_kept cenv (es with gas_obs := []) sb G0 tn0 s0 G tn /\
      FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
      lookup_var p t = SOME w /\
      (!entry. lookup_scopes id ee.scopes = SOME entry ==>
        ptr_covers G tn p t sz /\
        val_in_memory entry.type entry.value (w2n w) t.vs_memory /\
        (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
          val_in_memory entry.type entry.value (w2n w) mem)))
    (\H res ee gt r. expr_exit res r)
Proof
  strip_tac >>
  `storage_trace_frame (bind (eval_expr cx idx) (read_result cx))` by
    (irule storage_trace_frame_bind_all >>
     simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  reverse (Cases_on `?H. valid_horizon cx st0 H es.storage_trace`)
  >- (rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
      irule gas_bad_storage_at_initial >>
      fs[storage_trace_domain_def] >>
      irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame] >> gen_tac >>
      irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_return]) >>
  pop_assum (qx_choose_then `H0` assume_tac) >>
  `stmt_state_rel H0 ctx func cenv cx es s0 /\
   ghost_inv H0 d cenv cx es G0 tn0 s0` by
    (qpat_x_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (qspec_then `H0` mp_tac) >> simp[]) >>
  drule_all named_root_preparation >> strip_tac >>
  drule compile_name_value_ptr >>
  disch_then (qspecl_then [`bty`, `sa`, `ann`] assume_tac) >> gvs[] >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s0 /\
     storage_well_formed_on cx (es with gas_obs := []) (FST H) /\
     ghost_inv H d cenv cx (es with gas_obs := []) G0 tn0 s0` by
    (gen_tac >> strip_tac >>
     qpat_x_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       drule >> strip_tac >>
     rpt conj_tac
     >- first_assum ACCEPT_TAC
     >- (`storage_well_formed_on cx (es with gas_obs := []) (FST H) <=>
          storage_well_formed_on cx es (FST H)` by
           (irule storage_well_formed_on_backends >> simp[]) >>
         asm_rewrite_tac[]) >>
     gvs[ghost_inv_def] >> first_assum ACCEPT_TAC) >>
  irule named_prefix_counted >>
  conj_tac
  >- (BETA_TAC >> irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_return]) >>
  simp[] >>
  drule expr_sim_ptr_local_refresh >> simp[] >>
  disch_then drule_all >> strip_tac >>
  irule gas_outcome_ptr_return_map >>
  goal_assum (drule_at Any) >> simp[] >>
  reverse conj_tac
  >- (rpt gen_tac >> Cases_on `rr` >> Cases_on `r` >> simp[expr_exit_def] >>
      rename1 `expr_exit (INR exc) _` >> Cases_on `exc` >> simp[expr_exit_def] >>
      rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def]) >>
  rpt strip_tac >> gvs[] >>
  qexists_tac `a` >> simp[] >>
  first_x_assum drule_all >> simp[]
QED
