(* Instantiate the linked statement fragment at the concrete lock-success run. *)
Theory bodySelectedLockedBodyRunMods
Ancestors
  bodySelectedLockedBodyOutcomeMods bodyFullPostsMods gasOutcomeFullPostMods

Theorem selected_locked_body_run_mods:
  stmt_frag_full_mods (DF,lo,d,ctx,shadow_ctx,PGc,callee,shadow_callee)
    p NoLoop RetQ body_ce
    (stmts_env body_ce NoLoop ret b)
    (stmts_env (gas_shadow_env T body_ce) NoLoop ret
      (MAP gas_shadow_stmt b))
    (eval_stmts p ss) locked /\
  body_ce.ce_modules = mods /\
  (stmts_env body_ce NoLoop ret b) a = (out,z) /\
  (stmts_env (gas_shadow_env T body_ce) NoLoop ret
    (MAP gas_shadow_stmt b)) aS = (gas_shadow_env T out,zS) /\
  gas_shadow_state a aS /\ gas_shadow_state z zS /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function callee shadow_callee /\
  MEM callee ctx.ctx_functions /\ MEM shadow_callee shadow_ctx.ctx_functions /\
  fn_has_code a z callee /\ fn_has_code aS zS shadow_callee /\
  (!H. dead_lo_ok_mods H (DF H) lo body_ce p) /\
  fn_inst_ids_distinct callee /\ local_ptrs_reserved body_ce a /\
  ret_pc_ok body_ce a at_body /\
  (!x sz. body_ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at a x) /\
  ~block_is_terminated a /\
  gas_admissible (eval_stmts p ss) (stmt_res_ok NoLoop) locked /\
  return_buf_frame d body_ce a at_body /\
  return_buf_sep d body_ce locked at_body /\
  alloca_history callee at_body /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp at_body) /\
  (!fn inst s. frag_reachable ctx callee at_body fn inst s ==>
     dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon p st0 H locked.storage_trace ==>
    stmt_state_rel H ctx callee body_ce p locked at_body /\
    immutable_frame_mods callee body_ce p locked at_body /\
    storage_well_formed_on p locked (FST H) /\
    ghost_inv_at_mods (DF H) lo d body_ce p locked Gl tnl at_body) /\
  ~at_body.vs_halted /\ at_body.vs_current_bb = a.cs_current_bb /\
  at_body.vs_inst_idx = LENGTH a.cs_current_insts ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,PGc)
    mods p st0 (eval_stmts p ss) (locked,at_body,Gl,tnl)
    (\H res ee G tn t. ?cenv''.
      stmt_lands NoLoop z res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated z /\ cenv'' = out) /\
      cenv_top_ext body_ce cenv'' ee.scopes /\
      stmt_state_rel H ctx callee cenv'' p ee t /\
      immutable_frame_mods callee cenv'' p ee t /\
      storage_well_formed_on p ee (FST H) /\
      return_buf_frame d cenv'' z t /\ alloca_history callee t /\
      return_buf_sep d cenv'' ee t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      at_body.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv'' p ee G tn t /\
      (!x w. not_fresh_at a x /\ lookup_var x at_body = SOME w ==>
              lookup_var x t = SOME w) /\
      (!aid b0. FLOOKUP at_body.vs_allocas aid = SOME b0 ==>
                 FLOOKUP t.vs_allocas aid = SOME b0) /\
      (!x. not_fresh_at a x ==>
           FLOOKUP G x = FLOOKUP Gl x /\
           op_taint tn (Var x) = op_taint tnl (Var x)) /\
      alloca_frame body_ce locked a at_body cenv'' ee t /\
      (!aid off sz i.
         FLOOKUP at_body.vs_allocas aid = SOME (off,sz) /\ aid < a.cs_next_id /\
         (!n b0 sz0. local_region body_ce locked.scopes at_body n b0 sz0 ==>
                        off + sz <= b0 \/ b0 + sz0 <= off) /\
         off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tnl.t_mem))
    (\H res ee gt r.
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H p ee res r /\
      (ctx_has_dalloca ctx ==>
         !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==>
                 allocas_below_fmp s))
Proof
  strip_tac >>
  qpat_x_assum `stmt_frag_full_mods _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[stmt_frag_full_mods_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `body_ce.ce_modules = mods` (rewrite_tac o single) >>
  qpat_x_assum `!st0 sa sb shadow_sa shadow_sb s0 G0 tn0 cenv'. _`
    (qspecl_then [`st0`,`a`,`z`,`aS`,`zS`,`at_body`,`Gl`,`tnl`,`out`] drule_all) >>
  rpt strip_tac >>
  qpat_assum `body_ce.ce_modules = mods` (rewrite_tac o single o SYM) >>
  first_assum ACCEPT_TAC
QED
