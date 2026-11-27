(* Instantiate the linked locked-body fragment at the selected callee input. *)
Theory bodySelectedLockedBodyOutcomeMods
Ancestors
  bodySelectedLockedFragMods

(* The selected fragment theorem packages the linked checker, scope, cell,
   return-frame and replay premises.  Keep this adapter at the reached lock
   boundary; compiler interval and prefix execution facts are supplied by the
   surrounding callee cut. *)
Theorem selected_locked_body_outcome_mods:
  body_stmts_full_ok_mods mods exps p b /\
  contract_inv mods exps ctx body_ce p /\
  module_body_inv mods src tops body_ce p /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  supported_stmts tops bindings b /\
  (!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) b ==>
            EXISTS (occurs_abi_decode_target target o SND) mods) /\
  body_const_cells_agree_mods mods p env locked /\
  expr_sim_inv_mods mods body_ce p env locked /\
  ce_locals_declared body_ce env /\
  locals_alloc_ok body_ce env /\
  type_stmts env ret b = SOME env' /\
  stmts_exprs_ok body_ce b /\
  ~supported_stmts_expr_exists (unallocated_bare_global_root body_ce env) b /\
  (!key. MEM (vyperSubscriptOverlap$WriteAcc
                (vyperSubscriptOverlap$StateRef key))
             (vyperSubscriptOverlap$accesses_stmts b) /\
         IS_SOME (FLOOKUP env.bare_global_assignable key) ==>
         IS_SOME (FLOOKUP body_ce.ce_module_vars key)) /\
  call_evaluation_safe p (int_calls_stmts b) /\
  frame_ret_ok_full_mods mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    p RetQ body_ce ret /\
  (!gs. eval_stmts p b (locked with gas_obs := gs) =
        eval_stmts p ss (locked with gas_obs := gs)) ==>
  stmt_frag_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    p NoLoop RetQ body_ce
    (stmts_env body_ce NoLoop ret b)
    (stmts_env (gas_shadow_env T body_ce) NoLoop ret
      (MAP gas_shadow_stmt b))
    (eval_stmts p ss) locked
Proof
  strip_tac >> irule selected_locked_body_frag_mods >> rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (qexistsl_tac [`bindings`,`env`,`env'`,`exps`,`mods`,`src`,`tops`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
QED
