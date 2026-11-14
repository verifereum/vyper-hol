(* Joint evaluation of the scalar arguments of ECRecover. *)
Theory bodyFullBuiltinPrecompileRecoveryArgs
Ancestors
  bodyFullWordArgs exprSimPrecompiles exprSimSource list

(* Original application anchors typing; the suffix post uses its own start. *)
Theorem ecrecover_args_suffix_full:
  !todo DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty
    ann args done entry es st0 sa sm shadow_sa shadow_sm xs s0 G0 tn0.
    expr_body_pre cenv cx env (Builtin ann ECRecover args) entry /\
    args = done ++ todo /\ body_exprs_full_ok cx todo /\
    body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
    lower_word_args cenv (\e. ty) todo sa = (xs,sm) /\
    lower_word_args cenv (\e. ty) (MAP gas_shadow_expr todo) shadow_sa =
      (xs,shadow_sm) /\
    gas_shadow_state sa shadow_sa /\ gas_shadow_state sm shadow_sm /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
    MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s0 /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome_full
      (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (eval_exprs cx todo) (es,s0,G0,tn0)
      (\H rr mid G tn t. ?vs. rr = INL vs /\
        typed_args_post H ctx func cenv cx es sa s0 mid todo xs vs t /\
        t.vs_current_bb = sm.cs_current_bb /\
        t.vs_inst_idx = LENGTH sm.cs_current_insts /\
        alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv cx mid G tn t /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
        EVERY (\x. op_taint tn x = {}) xs)
      (\H rr mid gt r. wb_args_exit rr r)
Proof
  rpt gen_tac >> strip_tac >>
  irule lower_word_args_sim_full >> simp[] >> rpt conj_tac
  >- (qexistsl_tac [`shadow_func`, `shadow_sa`, `shadow_sm`, `ty`] >> simp[])
  >- (qexists_tac `tops` >> simp[]) >>
  qexists_tac `env` >> simp[] >>
  rpt strip_tac
  >- (drule expr_body_pre_builtin_arg >>
      disch_then (qspecl_then [`e`, `ee`] mp_tac) >> simp[]) >>
  drule ecrecover_pre_types >> simp[EVERY_MEM] >> metis_tac[]
QED
