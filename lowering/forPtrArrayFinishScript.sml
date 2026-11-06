(* Array callback resources are recovered using only the actual older-variable
   frame. Memory taint may change arbitrarily during the source body. *)
Theory forPtrArrayFinish
Ancestors forPtrArrayInvariant forPtrRangeCallback stmtSimForArrayLoop
  stmtFragPtr compileEnv bodyPtrDefs loweringPosts finite_map
  forPtrAllocationFrame gasSummaryComposePtr stmtSimProps stmtLowering

Theorem for_array_callback_control_ptr:
  array_for_code func cenv bc ty stmts id et tv n stride (Var bp)
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  sa.cs_next_var <= sb0.cs_next_var /\
  ptr_covers G0 tn0 p s0 sz /\ ptr_covers G0 tn0 bp s0 extent /\
  lookup_var idx s0 = SOME counter /\
  FLOOKUP G0 idx = NONE /\ op_taint tn0 (Var idx) = {} /\
  (!x w. not_fresh_at sb0 x /\ lookup_var x s0 = SOME w ==>
    lookup_var x t = SOME w) /\
  (!x. not_fresh_at sb0 x ==> FLOOKUP G x = FLOOKUP G0 x /\
    op_taint tn (Var x) = op_taint tn0 (Var x)) ==>
  ptr_covers G tn p t sz /\ ptr_covers G tn bp t extent /\
  lookup_var idx t = SOME counter /\
  FLOOKUP G idx = NONE /\ op_taint tn (Var idx) = {}
Proof
  strip_tac >>
  `not_fresh_at sa p /\ not_fresh_at sa bp /\ not_fresh_at sa idx` by
    fs[array_for_code_def] >>
  `not_fresh_at sb0 p /\ not_fresh_at sb0 bp /\ not_fresh_at sb0 idx` by
    metis_tac[not_fresh_at_mono] >>
  conj_tac
  >- (irule callback_old_pointer_coverage >> goal_assum (drule_at Any) >>
      metis_tac[]) >>
  conj_tac
  >- (irule callback_old_pointer_coverage >> goal_assum (drule_at Any) >>
      metis_tac[]) >>
  metis_tac[]
QED

Theorem for_array_callback_contract_ptr:
  array_for_code func cenv bc ty stmts id et tv n stride (Var bp)
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  sa.cs_next_var <= sb0.cs_next_var /\
  stmt_frag_ptr d ctx PG func cx (InLoop exit_lbl incr_lbl) RetQ bc
    (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts) es /\
  stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts sb0 = (bc',sb1) /\
  ~ctx_has_dalloca ctx /\ ~bc.ce_is_ctor /\ ret_pc_ok bc sb0 s0 /\
  (!x z. bc.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at sb0 x) /\
  gas_admissible (eval_stmts cx stmts) (stmt_res_ok (InLoop exit_lbl incr_lbl)) es /\
  stmt_state_rel ctx func bc cx es s0 /\ ghost_inv d bc cx es G0 tn0 s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sb0.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sb0.cs_current_insts /\
  ptr_covers G0 tn0 p s0 sz /\ ptr_covers G0 tn0 bp s0 extent /\
  lookup_var idx s0 = SOME counter /\
  FLOOKUP G0 idx = NONE /\ op_taint tn0 (Var idx) = {} ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG (eval_stmts cx stmts)
    (es,s0,G0,tn0)
    (\res ee G tn t. ((?c3.
      stmt_lands (InLoop exit_lbl incr_lbl) sb1 res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb1 /\ c3 = bc') /\
      cenv_top_ext bc c3 ee.scopes /\ stmt_state_rel ctx func c3 cx ee t /\
      ghost_inv d c3 cx ee G tn t /\
      (!x w. not_fresh_at sb0 x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!x. not_fresh_at sb0 x ==> FLOOKUP G x = FLOOKUP G0 x /\
        op_taint tn (Var x) = op_taint tn0 (Var x))) /\
      ptr_covers G tn p t sz /\ ptr_covers G tn bp t extent /\
      lookup_var idx t = SOME counter /\ FLOOKUP G idx = NONE /\
      op_taint tn (Var idx) = {}) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b))
    (\res ee gt r. !tail. stmt_exit_ptr RetQ (ee with gas_obs := tail) res gt r)
Proof
  strip_tac >> ho_match_mp_tac gas_outcome_ptr_allocation_frame >>
  `fn_has_code sb0 sb1 func /\ local_ptrs_reserved bc sb0 /\
   ~block_is_terminated sb0 /\ fn_inst_ids_distinct func` by fs[array_for_code_def] >>
  qpat_x_assum `stmt_frag_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[stmt_frag_ptr_def] >> disch_then drule_all >> strip_tac >>
  irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` kall_tac >>
  reverse conj_tac >- simp[] >> rpt gen_tac >>
  simp_tac bool_ss [] >> strip_tac >>
  irule for_array_callback_control_ptr >> goal_assum (drule_at Any) >> metis_tac[]
QED

(* Arbitrary head scopes serve both preparation and cleanup. *)
Theorem for_array_code_top_ext_ptr:
  array_for_code func cenv bc ty stmts id et tv n stride saved_base
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  lookup_scopes id rest = NONE ==>
  cenv_top_ext cenv bc (sc :: rest)
Proof
  strip_tac >> fs[array_for_code_def, cenv_top_ext_def] >>
  rpt strip_tac >> `n' = id` by metis_tac[] >> gvs[] >> metis_tac[]
QED
