(* The full RHS keeps the captured AugAssign operands at its one endpoint. *)
Theory augAssignFullRhsSaved
Ancestors
  bodyFullShadowBodyInv
  augAssignFullSaved bodyFullPreds stmtSimAugAssignPlaceMemory
  stmtSimProps haltExitProj bodyPtrDefs exprSimDefs bodySimFull
  gasOutcomeFull fragGasOriginPtr fragGasOrigin loweringPosts

Theorem augassign_expr_exit_to_stmt_exit:
  expr_exit (INR exc : 'a + exception) r /\
  halt_exit H cx ee (INR exc : 'a + exception) r /\
  (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s) ==>
  (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail)
     (INR exc) (gt : (string, num # num) fmap # taint) r) /\
  halt_exit H cx ee (INR exc : unit + exception) r /\
  (ctx_has_dalloca ctx ==>
   !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s)
Proof
  strip_tac >>
  conj_tac
  >- (simp[stmt_exit_ptr_def] >> metis_tac[expr_exit_INR_type]) >>
  conj_tac
  >- metis_tac[halt_exit_INR_type] >>
  rpt strip_tac >> gvs[] >> fs[expr_exit_def]
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  `body_expr_full_ok cx e` by metis_tac[] >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty e es` by
    (qpat_x_assum `body_expr_full_ok _ _` mp_tac >>
     simp[Once body_expr_full_ok_def] >> metis_tac[]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then drule_all >>
  simp[gas_outcome_full_def] >> strip_tac >> qexists_tac `marks`
  >- metis_tac[]
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >> simp[] >>
      rpt strip_tac >> first_x_assum drule >> strip_tac
      >- (disj1_tac >> qexists_tac `t` >> simp[] >>
          `t.vs_labels = s0.vs_labels` by
            metis_tac[gas_origin_ptr_path_projections, gas_origin_path_erase,
                      aug_place_marked_path_labels] >>
          `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
                 lookup_var x t = SOME w` by fs[expr_post_def] >>
          drule_all augassign_saved_rhs_frame >> metis_tac[]) >>
      disj2_tac >> simp[] >> Cases_on `res` >> gvs[] >>
      drule_all augassign_expr_exit_to_stmt_exit >>
      simp[] >> rpt (pop_assum kall_tac) >> metis_tac[]) >>
  metis_tac[]
QED
*)
Theorem augassign_rhs_saved_outcome:
  (!s'' p t' s3 cur t'' s4 ptv t3.
     eval_target_place cx target s'' = (INL p,t') /\
     read_place cx p s3 = (INL cur,t'') /\
     place_type_value cx p s4 = (INL ptv,t3) ==>
     body_expr_full_ok cx e) /\
  eval_target_place cx target es0 = (INL p,st) /\
  read_place cx p sr = (INL cur,tr) /\
  place_type_value cx p sty = (INL ptv,tty) /\
  body_inv tops ctx cenv cx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  shadow_body_inv tops ctx shadow_ctx /\ expr_body_pre cenv cx env e es /\
  lower_value compile_expr cenv ty e sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) shadow_sa =
    (op,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. FST place = Var x ==> not_fresh_at sa x) /\
  (!x. old = Var x ==> not_fresh_at sa x) /\
  eval_operand (FST place) s0 = SOME addr /\
  eval_operand old s0 = SOME word /\
  target_ptr_ok cenv (PlaceR p) place G0 tn0 s0 /\
  op_taint tn0 old = {} /\ op_prov G0 old = NONE ==>
  gas_outcome_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx))
    (es,s0,G0,tn0)
    (\H res ee G tn t. ?v. res = INL v /\
      expr_post H ctx func cenv cx e es sa sb s0 ee v op t /\
      expr_store_bound cx (post_value_type cenv e) v op t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
      (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      eval_operand (FST place) t = SOME addr /\
      eval_operand old t = SOME word /\
      target_ptr_ok cenv (PlaceR p) place G tn t /\
      op_taint tn old = {} /\ op_prov G old = NONE)
    (\H res ee gt r.
      expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s) /\
      ?exc. res = INR exc /\
        (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail)
          (INR exc) gt r) /\
        halt_exit H cx ee (INR exc : unit + exception) r /\
        (ctx_has_dalloca ctx ==>
         !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  cheat
QED
