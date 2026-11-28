(* Retain canonical unwrap's whole-buffer bound through the joint read. *)
Theory bodyFullConvertChildRead
Ancestors
  gasOutcomeFullBindMods
  bodyFullOfVV bodySimFull gasOutcomeFull exprSimDefs loweringPosts
  contextRawReachable ptrDiscipline unitTransformDefs

Theorem expr_sim_full_of_vv_post_buffer_exit:
  (is_word_type (post_value_type cenv e) ==> is_word_type (expr_type e)) /\
  (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
        ~is_word_type (post_value_type cenv e) ==>
        type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
        type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
  (!gs tv ee v. eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\
     read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es ==>
  !st0 sa sb shadow_sa shadow_sb op s0 G0 tn0.
    lower_value compile_expr cenv ty e sa = (op,sb) /\
    lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) shadow_sa = (op,shadow_sb) /\
    gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
    MEM shadow_func shadow_ctx.ctx_functions /\ fn_has_code sa sb func /\
    fn_has_code shadow_sa shadow_sb shadow_func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
    (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
    return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s0 /\ storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
      (\H res ee G tn t. ?v. res = INL v /\
        expr_post H ctx func cenv cx e es sa sb s0 ee v op t /\
        expr_store_bound cx (post_value_type cenv e) v op t /\
        t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
        ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
        (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G t) /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
        (~is_word_type (post_value_type cenv e) ==>
         !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
                eval_operand op t = SOME w ==>
                type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= t.vs_alloca_next))
      (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  strip_tac >> rpt strip_tac >>
  mp_tac (SPEC_ALL expr_sim_full_of_vv_with_buffer) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qspecl_then
    [`st0`,`sa`,`sb`,`shadow_sa`,`shadow_sb`,`op`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  irule gas_outcome_full_mods_post_mono >>
  goal_assum (drule_at Any) >> simp[] >>
  rpt strip_tac >> qexists_tac `v` >> simp[]
QED
