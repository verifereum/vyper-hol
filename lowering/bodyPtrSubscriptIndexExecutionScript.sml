(* One counted index execution refreshes every retained named-local root. *)
Theory bodyPtrSubscriptIndexExecution
Ancestors
  bodyPtrSubscriptIndexRefresh bodyPtrDefs gasSummaryComposePtr loweringPosts

Theorem expr_sim_ptr_local_refresh:
  expr_sim_ptr d ctx PG func cenv cx ty idx es /\
  lower_value compile_expr cenv ty idx sa = (op, sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx idx) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\
  ghost_inv d cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx, func) PG
    (bind (eval_expr cx idx) (read_result cx)) (es, s0, G0, tn0)
    (\res ee G tn t. ?v. res = INL v /\
      expr_post ctx func cenv cx idx es sa sb s0 ee v op t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx ee G tn t /\
      ptr_val_ok cx (post_value_type cenv idx) v op G tn t /\
      (~is_word_type (post_value_type cenv idx) ==> ptr_buf_ok cenv idx op G t) /\
      ghost_kept cenv es sa G0 tn0 s0 G tn /\
      (!name p sz w.
        FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
        lookup_var p s0 = SOME w ==>
        lookup_var p t = SOME w /\
        (!entry. lookup_scopes name ee.scopes = SOME entry ==>
          ptr_covers G tn p t sz /\
          val_in_memory entry.type entry.value (w2n w) t.vs_memory /\
          (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
            val_in_memory entry.type entry.value (w2n w) mem))))
    (\res ee gt r. expr_exit res r)
Proof
  rpt strip_tac >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_sim_ptr_def] >>
  disch_then drule_all >> strip_tac >>
  irule gas_outcome_ptr_conseq >>
  goal_assum (drule_at Any) >>
  simp[] >>
  rpt strip_tac >> qexists_tac `v` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  conj_tac >- (drule_all expr_post_local_pointer >> simp[]) >>
  gen_tac >> strip_tac >>
  conj_tac >- (drule_all ghost_inv_local_coverage >> simp[]) >>
  conj_tac >- (drule_all expr_post_local_representation >> simp[]) >>
  gen_tac >> strip_tac >>
  drule_all expr_post_local_robust_representation >> simp[]
QED
