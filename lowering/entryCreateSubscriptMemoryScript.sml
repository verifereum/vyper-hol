(* Scoped fixed-memory selection on the run chosen by the scalar producer. *)
Theory entryCreateSubscriptMemory
Ancestors
  entryCreateSubscriptMemoryBind entryCreateSubscriptArrayRun
  bodyFullSubscriptArrayMemory bodyFullTargetArraySuffix arrayAbortItinerary
  entryCreateImmSubscriptIntervals fragExec exprSimArrayIndex exprLoweringProps
  bodyFullSubscriptArrayCodeBounds venomState ptrDiscipline
  compileEnv entryCreateFocusSpec

Definition fixed_memory_selector_run_def[local]:
  fixed_memory_selector_run a m b s r <=>
    (?u v. run_inst_seq (emitted_insts a m) s = OK u /\
           run_inst_seq (emitted_insts m b)
             (u with vs_inst_idx := LENGTH m.cs_current_insts) = OK v /\
           r = OK (v with vs_inst_idx := LENGTH b.cs_current_insts)) \/
    (?t. r = Abort Revert_abort t /\ array_bounds_native_run a m s F t)
End

Theorem fixed_memory_selector_observed[local]:
  fixed_memory_scalar_observer fixed_memory_selector_run
Proof
  simp[fixed_memory_scalar_observer_def] >> rpt gen_tac >> strip_tac >>
  rename1 `array_bounds_check idx (Lit (n2w n)) sgn a = ((),m)` >>
  `eval_operand (Lit (n2w n)) s = SOME (n2w n) /\
   op_taint tn (Lit (n2w n)) = {} /\ op_prov G (Lit (n2w n)) = NONE /\
   (!x. Lit (n2w n) = Var x ==> not_fresh_at a x)` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  drule_all array_tail_scalar_uniform_observed >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`t`,`H`,`tm`] >> simp[] >>
  Cases_on `idx_in_range sgn iw (n2w n)` >> gvs[fixed_memory_selector_run_def] >>
  gvs[array_abort_itinerary_def,array_bounds_native_run_def] >>
  qexistsl_tac [`raw`,`LENGTH pre + LENGTH a.cs_current_insts`] >>
  pure_rewrite_tac[rich_listTheory.APPEND_ASSOC_CONS, GSYM listTheory.APPEND_ASSOC] >>
  drule_then (fn th => simp[th,run_inst_seq_def]) run_inst_seq_append
QED

Theorem fixed_memory_selector_scope[local]:
  framed_memory_selector_scope fixed_memory_selector_run
Proof
  simp[framed_memory_selector_scope_def] >> rpt gen_tac >> strip_tac >>
  rename1 `emit_op ADD [bop; Var off] sm = (Var out,sb)` >>
  `array_elem_ptr bop idx F (word_scale LocMemory) sz sc = (Var out,sb)` by
    simp[array_elem_ptr_def,comp_bind_def,comp_return_def] >>
  drule array_elem_selector_code >> strip_tac >>
  drule array_bounds_selector_code >> strip_tac >>
  qpat_x_assum `fixed_memory_selector_run _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [fixed_memory_selector_run_def])
  >- (gvs[] >> irule array_selector_ok_scope_itinerary >> simp[] >>
      qexistsl_tac [`st2`,`sc`,`u`,`t`] >>
      `t with vs_inst_idx := LENGTH st2.cs_current_insts = t` by
        fs[create_operand_at_def,venom_state_component_equality] >>
      `emitted_insts st2 st2 = []` by simp[emitted_insts_def] >>
      simp[run_inst_seq_def]) >>
  gvs[] >> irule array_bounds_oob_scope >>
  qpat_assum `gas_origin_ptr_path _ _ [] _` (irule_at Any) >>
  qpat_assum `array_bounds_check _ _ _ _ = _` (irule_at Any) >> simp[]
QED

Theorem fixed_memory_selector_inventory[local]:
  framed_memory_selector_inventory
Proof
  simp[framed_memory_selector_inventory_def] >> rpt strip_tac >>
  irule array_selector_visit_inventory >> simp[] >>
  qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_array_subscript_split,comp_bind_def,comp_return_def,
       comp_ignore_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
  fs[oneTheory.one] >>
  drule array_bounds_selector_code >> strip_tac >>
  drule array_elem_selector_code >> strip_tac >>
  irule array_selector_code_join >> metis_tac[]
QED

Theorem fixed_memory_interval_bind[local]:
  framed_memory_interval_bind (:'a) (:'b)
Proof
  rewrite_tac[framed_memory_interval_bind_def] >> rpt gen_tac >>
  MATCH_ACCEPT_TAC create_selected_bind_at_interval
QED

Theorem create_framed_memory_subscript_at:
  immutable_scoped_bind_law (:eval_result) (:eval_result) /\
  immutable_replay_bind_law (:eval_result) (:eval_result) /\
  immutable_scoped_bind_law (:value) (:eval_result) /\
  immutable_replay_bind_law (:value) (:eval_result) /\
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  ~subscript_reads_base cx e1 e2 /\ ~copies_subscript_base ce e1 e2 /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre ce cx env (Subscript ann e1 e2) es /\
  expr_type e1 = ArrayT et (Fixed n) /\
  place_type ce e1 = ValPT (ArrayT et (Fixed n)) /\
  post_value_type ce e1 = expr_type e1 /\
  (!t res t'. eval_expr cx e2 t = (INL res,t') ==>
     t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
  (!t tr slot vt t'. eval_expr cx e1 t <> (INL (PlaceR (StoragePlace tr slot vt)),t')) /\
  (!rt. evaluate_type (get_tenv cx) et = SOME rt ==> dynarray_free rt) /\
  (!ty' st. vv_location (FST (compile_expr ce ty' e1 st)) = SOME LocMemory) /\
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx ty (Subscript ann e1 e2)
    es (st0,sa,sb,sha,shb,vv,s0,G0,tn0) /\ create_layout sa sb /\
  (!sm shm bvv.
    expr_body_pre ce cx env e1 es /\
    expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx ty e1
      es (st0,sa,sm,sha,shm,bvv,s0,G0,tn0) /\ create_layout sa sm ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
      (cx_tops cx) cx st0 sa sm (eval_expr cx e1) (es,s0,G0,tn0)
      (expr_vv_sim_full_post (DF,lo,d,ctx,f) ce cx e1 (es,sa,sm,s0,bvv,G0,tn0))
      (create_operand_exit_post ctx cx) /\
    create_operand_cut sa sm (gas_explicit_sites ctx shctx) ctx f tops cx st0
      (eval_expr cx e1) (es,s0)) /\
  (!gs tv mid s G1 tn1 sm shm st2 sh2 iop.
    eval_expr cx e1 (es with gas_obs := gs) = (INL tv,mid) /\
    body_const_cells_agree [(NONE,tops)] cx env mid /\ expr_body_pre ce cx env e2 mid /\
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx ty e2
      mid (st0,sm,st2,shm,sh2,iop,s,G1,tn1) /\ create_layout sm st2 ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
      (cx_tops cx) cx st0 sm st2 (bind (eval_expr cx e2) (read_result cx)) (mid,s,G1,tn1)
      (expr_sim_full_post (DF,lo,d,ctx,f) ce cx e2 (mid,sm,st2,s,iop,G1,tn1))
      (create_operand_exit_post ctx cx) /\
    create_operand_cut sm st2 (gas_explicit_sites ctx shctx) ctx f tops cx st0
      (bind (eval_expr cx e2) (read_result cx)) (mid,s)) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
    (cx_tops cx) cx st0 sa sb (eval_expr cx (Subscript ann e1 e2)) (es,s0,G0,tn0)
    (expr_vv_sim_full_post (DF,lo,d,ctx,f) ce cx (Subscript ann e1 e2) (es,sa,sb,s0,vv,G0,tn0))
    (create_operand_exit_post ctx cx) /\
  create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx f tops cx st0
    (eval_expr cx (Subscript ann e1 e2)) (es,s0)
Proof
  strip_tac >> irule create_framed_memory_subscript_from_selection >>
  simp[fixed_memory_selector_inventory,fixed_memory_interval_bind] >>
  conj_tac >-
    (qexists_tac `fixed_memory_selector_run` >>
     simp[fixed_memory_selector_scope,framed_memory_selection_observed,
          fixed_memory_selector_observed]) >>
  qexistsl_tac [`env`,`sha`,`shb`,`shf`,`ty`] >> simp[] >>
  conj_tac >- (qpat_assum `!sm shm bvv. _ ==> _ /\ _` ACCEPT_TAC) >>
  qpat_assum `!gs tv mid s G1 tn1 sm shm st2 sh2 iop. _ ==> _ /\ _` ACCEPT_TAC
QED
