(* Apply the substituted body judgment at the selected locked entry. *)
Theory bodySelectedLockedFragMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods gasOutcomeFullMods gasExemptCertMods
  gasContext gasStorage vyperState vyperInterpreter

Theorem gas_outcome_full_mods_source_cong[local]:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source
    (es,s,G,tn) Q R /\
  (!gs. source' (es with gas_obs := gs) = source (es with gas_obs := gs)) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source'
    (es,s,G,tn) Q R
Proof
  rw[gas_outcome_full_mods_def, gas_bad_storage_at_def] >>
  qexists_tac `marks`
  >- (disj1_tac >> simp[] >>
      qexistsl_tac [`H`, `leaf`, `leaf_pg`, `leaf_g`, `leaf_tn`, `finish'`] >>
      simp[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`, `ee`, `r`, `G'`, `tn'`] >> simp[]) >>
  disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `leaf_pg`, `leaf_g`, `leaf_tn`, `finish'`] >>
  conj_tac
  >- (irule gas_exempt_cert_mods_source_cong >>
      qexists_tac `ignore_bind source (return ())` >>
      simp[ignore_bind_def, bind_def]) >>
  qexists_tac `H` >> simp[]
QED

Theorem stmt_frag_full_mods_source_cong[local]:
  stmt_frag_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx RetQ cenv m shadow_m source es /\
  (!gs. source' (es with gas_obs := gs) = source (es with gas_obs := gs)) ==>
  stmt_frag_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx RetQ cenv m shadow_m source' es
Proof
  rewrite_tac[stmt_frag_full_mods_def] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  `gas_admissible source (stmt_res_ok lctx) es` by
    (qpat_x_assum `gas_admissible source' _ _` mp_tac >>
     simp[gas_admissible_def]) >>
  irule gas_outcome_full_mods_source_cong >> qexists_tac `source` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `!st0 sa sb shadow_sa shadow_sb s0 G0 tn0 cenv'. _` irule >>
  asm_rewrite_tac[] >>
  qexistsl_tac [`shadow_sa`, `shadow_sb`] >> asm_rewrite_tac[]
QED

(* The selected frame already supplies typing, support and the unit-wide ABI
   exemption for b. Replay is required only at the locked state's gas tails. *)
Theorem selected_locked_body_frag_mods:
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
  (!key. MEM (vyperSubscriptOverlap$WriteAcc (vyperSubscriptOverlap$StateRef key))
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
    (stmts_env (gas_shadow_env T body_ce) NoLoop ret (MAP gas_shadow_stmt b))
    (eval_stmts p ss) locked
Proof
  strip_tac >>
  irule stmt_frag_full_mods_source_cong >> qexists_tac `eval_stmts p b` >>
  conj_tac >- simp[] >>
  qpat_x_assum `body_stmts_full_ok_mods _ _ _ _`
    (irule o REWRITE_RULE [body_stmts_full_ok_mods_def]) >>
  asm_rewrite_tac[] >> conj_tac
  >- (qexistsl_tac [`env`, `env'`] >> asm_rewrite_tac[]) >>
  qexistsl_tac [`bindings`, `src`, `tops`] >> asm_rewrite_tac[]
QED
