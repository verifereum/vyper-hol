(* Counted statement simulations over the actual source action. *)
Theory stmtSimDefs
Ancestors
  exprSimDefs loweringPosts gasOutcome gasContext allocaHistory
  stmtLowering compileEnv loweringSlice vyperInterpreter vyperState
  venomState venomExecSemantics

Definition stmt_res_ok_def:
  stmt_res_ok lctx (res : unit + exception) <=>
    res = INL () \/
    (?m. res = INR (Error (RuntimeError m))) \/
    (?d. res = INR (Error (RevertData d))) \/
    (?str. res = INR (AssertException str)) \/
    (?v. res = INR (ReturnException v)) \/
    ((res = INR BreakException \/ res = INR ContinueException) /\
     ?ex inc. lctx = InLoop ex inc)
End

Definition stmt_exit_def:
  stmt_exit RetQ es' (res : unit + exception) r <=>
    expr_exit res r \/
    ?v. res = INR (ReturnException v) /\
        RetQ v (es' with scopes := []) r
End

Definition stmt_post_def:
  stmt_post ctx func cx lctx cenv cenv' sa sb s0 res ee t <=>
    ?cenv''.
      stmt_lands lctx sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv') /\
      cenv_top_ext cenv cenv'' ee.scopes /\
      stmt_state_rel ctx func cenv'' cx ee t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP t.vs_allocas aid = SOME b)
End

Definition stmt_framed_frag_def:
  stmt_framed_frag Frame ctx func cx lctx RetQ cenv
    (m : compile_env compiler) source es <=>
    !sa sb s0 cenv'.
      m sa = (cenv', sb) /\ fn_has_code sa sb func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      ret_pc_ok cenv sa s0 /\ ~block_is_terminated sa /\
      gas_admissible source (stmt_res_ok lctx) es /\
      Frame s0 /\ stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome F (cx_tops cx) (ctx, func) source (es, s0)
        (stmt_post ctx func cx lctx cenv cenv' sa sb s0)
        (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
End

Definition stmt_frag_def:
  stmt_frag ctx func cx lctx RetQ cenv m source es <=>
    stmt_framed_frag (K T) ctx func cx lctx RetQ cenv m source es
End

Definition stmt_frag_mem_def:
  stmt_frag_mem d ctx func cx lctx RetQ cenv
    (m : compile_env compiler) source es <=>
    !sa sb s0 cenv'.
      m sa = (cenv', sb) /\ fn_has_code sa sb func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      ret_pc_ok cenv sa s0 /\ ~block_is_terminated sa /\
      gas_admissible source (stmt_res_ok lctx) es /\
      return_buf_frame d cenv sa s0 /\
      stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\
      ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome T (cx_tops cx) (ctx, func) source (es, s0)
        (\res ee t. ?cenv''.
          stmt_lands lctx sb res t /\ ~t.vs_halted /\
          (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv') /\
          cenv_top_ext cenv cenv'' ee.scopes /\
          stmt_state_rel ctx func cenv'' cx ee t /\
          (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
                 lookup_var x t = SOME w) /\
          (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                   FLOOKUP t.vs_allocas aid = SOME b) /\
          return_buf_frame d cenv'' sb t /\ alloca_history func t /\
          s0.vs_alloca_next <= t.vs_alloca_next)
        (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
End

Definition alloca_prefix_def:
  alloca_prefix cap (s:venom_state) <=>
    cap <= s.vs_alloca_next /\
    !aid b n. FLOOKUP s.vs_allocas aid = SOME (b,n) ==> cap <= b
End

Theorem stmt_exit_loop_ctl:
  !RetQ es rr.
    ~stmt_exit RetQ es (INL ()) rr /\
    ~stmt_exit RetQ es (INR BreakException) rr /\
    ~stmt_exit RetQ es (INR ContinueException) rr
Proof
  rw[stmt_exit_def] >> Cases_on `rr` >> simp[expr_exit_def]
QED
