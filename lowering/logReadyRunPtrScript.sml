(* Adapt conditional readiness to the existing counted argument evaluator. *)
Theory logReadyRunPtr
Ancestors logArgsRunPtr logArgsPtr bodyPtrDefs exprSimDefs stmtSimLogArgs
  gasSummaryComposePtr exprSimHypsDefs vyperInterpreter vyperState list

Theorem compile_log_eval_all_gas_ptr:
  !args d ctx PG func cenv cx Inv es sa xs sb s0 G0 tn0 env env0 es0.
    log_args_ready_ptr d ctx PG func cenv cx Inv args /\ Inv es /\
    (!s gs. Inv s ==> Inv (s with gas_obs := gs)) /\
    EVERY supported_scalar_type (MAP expr_type args) /\
    compile_log_eval_all cenv args sa = (xs,sb) /\
    gas_admissible (eval_exprs cx args)
      (\r. !exc. r = INR exc ==> expr_res_ok (INR exc : value + exception)) es /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    expr_sim_inv cenv cx env0 es0 /\ well_typed_exprs env args /\
    (!id t. FLOOKUP env.var_types id = SOME t ==>
       ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
    stmt_state_rel ctx func cenv cx es s0 /\ ghost_inv d cenv cx es G0 tn0 s0 /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
      (eval_exprs cx args) (es,s0,G0,tn0)
      (\res ee G tn t. ?vs. res = INL vs /\
         log_args_post ctx func cenv cx es sa sb s0 ee xs vs t /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts /\
         LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
                               value_has_type tv v) (MAP expr_type args) vs /\
         EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sb z) /\
                    (!lab. FST p <> Label lab)) xs /\
         ghost_inv d cenv cx ee G tn t /\
         LIST_REL (\p v. ptr_val_ok cx (SND p) v (FST p) G tn t) xs vs /\
         LIST_REL (\e p. ~is_word_type (expr_type e) ==>
           ptr_buf_ok cenv e (FST p) G t) args xs /\
         ghost_kept cenv es sa G0 tn0 s0 G tn)
      (\res ee gt r. expr_exit res r)
Proof
  rpt gen_tac >> strip_tac >> irule compile_log_eval_all_ptr >>
  simp[] >> rpt conj_tac
  >- (qexists_tac `\tail s. log_args_ready_ptr d ctx PG func cenv cx Inv tail /\ Inv s` >>
      simp[] >> rpt gen_tac >> strip_tac >> conj_tac
      >- (drule_all log_args_ready_ptr_cons >> simp[]) >>
      rpt strip_tac >> drule_all log_args_ready_ptr_tail >> simp[]) 
  >- (qexists_tac `env` >> simp[]) >>
  qexistsl_tac [`env0`, `es0`] >> simp[]
QED
