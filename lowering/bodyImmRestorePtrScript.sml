(* The immutable callback preserves caller resources through its actual
   old-register frame; no memory-taint equality is required. *)
Theory bodyImmRestorePtr
Ancestors
  forPtrRangeCallback forPtrArrayFinish forPtrAllocationFrame forPtrScope gasSummaryComposePtr
  bodyPtrDefs stmtFragPtr stmtSimProps loweringPosts loweringStateRelDefs
  stmtSimAugAssignPlaceMemory fragGasPathPtr
  compileEnv venomState ptrDiscipline finite_map words

Theorem immutable_body_callback_ptr:
  stmt_frag_ptr d ctx PG func cx (InLoop exit incr) RetQ bc
    (stmts_env bc (InLoop exit incr) ty stmts) (eval_stmts cx stmts) es /\
  stmts_env bc (InLoop exit incr) ty stmts sb0 = (bc',sb1) /\
  fn_has_code sb0 sb1 func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved bc sb0 /\ ~block_is_terminated sb0 /\
  ~ctx_has_dalloca ctx /\ ~bc.ce_is_ctor /\ ret_pc_ok bc sb0 s0 /\
  (!x z. bc.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at sb0 x) /\
  gas_admissible (eval_stmts cx stmts) (stmt_res_ok (InLoop exit incr)) es /\
  stmt_state_rel ctx func bc cx es s0 /\ ghost_inv d bc cx es G0 tn0 s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sb0.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sb0.cs_current_insts /\
  not_fresh_at sb0 p /\ not_fresh_at sb0 idx /\
  (!x. lvo = Var x ==> not_fresh_at sb0 x) /\
  ptr_covers G0 tn0 p s0 sz /\ lookup_var idx s0 = SOME counter /\
  FLOOKUP G0 idx = NONE /\ op_taint tn0 (Var idx) = {} /\
  eval_operand lvo s0 = SOME len /\ op_prov G0 lvo = NONE /\ op_taint tn0 lvo = {} ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG (eval_stmts cx stmts)
    (es,s0,G0,tn0)
    (\res ee G tn t. ((?c3.
      stmt_lands (InLoop exit incr) sb1 res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb1 /\ c3 = bc') /\
      cenv_top_ext bc c3 ee.scopes /\ stmt_state_rel ctx func c3 cx ee t /\
      ghost_inv d c3 cx ee G tn t /\
      (!x w. not_fresh_at sb0 x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!x. not_fresh_at sb0 x ==> FLOOKUP G x = FLOOKUP G0 x /\
        op_taint tn (Var x) = op_taint tn0 (Var x))) /\
      ptr_covers G tn p t sz /\ lookup_var idx t = SOME counter /\
      FLOOKUP G idx = NONE /\ op_taint tn (Var idx) = {} /\
      eval_operand lvo t = SOME len /\ op_prov G lvo = NONE /\ op_taint tn lvo = {}) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b))
    (\res ee gt r. !tail. stmt_exit_ptr RetQ (ee with gas_obs := tail) res gt r)
Proof
  strip_tac >>
  qpat_x_assum `stmt_frag_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[stmt_frag_ptr_def] >> disch_then drule_all >> strip_tac >>
  drule gas_outcome_ptr_allocation_frame >> strip_tac >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [gas_outcome_ptr_def, gas_summary_ptr_at_def] >>
  rpt strip_tac >> qexists_tac `marks`
  >- (disj1_tac >>
      rename1 `gas_path_ptr _ _ _ _ _ _ _ s0 _ G tn r` >>
      `t.vs_labels = s0.vs_labels` by
        (drule gas_path_ptr_erase >> strip_tac >>
         drule aug_place_path_labels >> simp[]) >>
      goal_assum (drule_at Any) >> simp[] >>
      `ptr_covers G tn p t sz` by
        (irule callback_old_pointer_coverage >>
         goal_assum (drule_at Any) >> metis_tac[]) >>
      simp[] >> Cases_on `lvo` >>
      gvs[eval_operand_def, op_prov_def, op_taint_def] >> metis_tac[])
  >- (disj1_tac >> goal_assum (drule_at Any) >>
      qexistsl_tac [`res`, `es_end`] >> simp[]) >>
  disj2_tac >> metis_tac[]
QED
