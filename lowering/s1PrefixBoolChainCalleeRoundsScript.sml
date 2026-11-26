(* Compose the reached statements at the locked callee body landing,
   then carry their request sites back through source cleanup and INVOKE. *)
Theory s1PrefixBoolChainCalleeRounds
Ancestors
  s1PrefixStmtsCons s1PrefixStmtZero stmtSimZero bodyFullStmtsCons
  s1PrefixIntCallCalleeLocked s1PrefixIntCallNoLockedRequest
  s1PrefixIntCallReturnPrefix s1PrefixDefs fragGasFocus
  bodyFullIntCallDefs vyperState vyperStorageFootprint list

(* The step supplies the head (which may itself be a loop) at its own
   environment. Only a normal landing carries readiness to the tail. *)
Triviality callee_stmts_from_step:
  (ctx_has_dalloca ctx /\ MEM callee ctx.ctx_functions ==>
    !bb. MEM bb callee.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!a rest ce es. ready (a::rest) ce es ==>
     stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,callee,sf) cx lctx RetQ ce
       (stmt_env ce lctx ty a)
       (stmt_env (gas_shadow_env T ce) lctx ty (gas_shadow_stmt a))
       (eval_stmt cx a) es /\
     stmt_frag_prefix (DF,lo,d,ctx,shadow_ctx,PG,callee,sf) cx lctx RetQ ce
       (stmt_env ce lctx ty a)
       (stmt_env (gas_shadow_env T ce) lctx ty (gas_shadow_stmt a))
       (eval_stmt cx a) es /\
     (!gs mid ce' sa sm.
        eval_stmt cx a (es with gas_obs := gs) = (INL (),mid) /\
        stmt_env ce lctx ty a sa = (ce',sm) /\
        cenv_top_ext ce ce' mid.scopes ==>
        ready rest ce' mid)) ==>
  !ss ce es. ready ss ce es ==>
    stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,callee,sf) cx lctx RetQ ce
      (stmts_env ce lctx ty ss)
      (stmts_env (gas_shadow_env T ce) lctx ty (MAP gas_shadow_stmt ss))
      (eval_stmts cx ss) es /\
    stmt_frag_prefix (DF,lo,d,ctx,shadow_ctx,PG,callee,sf) cx lctx RetQ ce
      (stmts_env ce lctx ty ss)
      (stmts_env (gas_shadow_env T ce) lctx ty (MAP gas_shadow_stmt ss))
      (eval_stmts cx ss) es
Proof
  strip_tac >> Induct_on `ss` >> simp[stmt_frag_nil_full,stmt_frag_nil_prefix] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!a rest ce es. _` (drule_then strip_assume_tac) >>
  conj_tac
  >- (irule (REWRITE_RULE [MAP] stmt_frag_full_cons_env) >> simp[] >> metis_tac[]) >>
  irule (REWRITE_RULE [MAP] stmt_frag_prefix_cons_env) >> simp[] >> metis_tac[]
QED

Theorem bool_chain_callee_rounds_prefix:
  pushed = cx with stk updated_by CONS (NONE,name) /\
  body_pg = MAP (op_prov G) arg_ops /\
  gas_invoke_entry (ctx,func) t callee entered /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,arg_ops) /\
  (!H. ptr_inst_ok (DF H) lo 0 ctx func G tn inst t) /\
  (ctx_has_dalloca ctx /\ MEM callee ctx.ctx_functions ==>
     !bb. MEM bb callee.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!locked. lock_if_nr cx nr (is_view_mut mut) es1 = (INL (),locked) /\
     storage_trace_domain cx st0 locked.storage_trace ==>
     ?ce at_body Gl tnl sa sb shadow_sa shadow_sb ce_end.
       ready compiled ce locked /\
       at_body.vs_gas_readings = entered.vs_gas_readings /\
       (!H. gas_origin_ptr_path
         (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,body_pg)
         (entered,FEMPTY,tn with t_var := FEMPTY) [] (OK at_body,Gl,tnl)) /\
       (!gs. eval_stmts pushed ss (locked with gas_obs := gs) =
             eval_stmts pushed compiled (locked with gas_obs := gs)) /\
       stmt_frag_full_pre (DF,lo,d,ctx,shadow_ctx,body_pg,callee,sf)
         pushed NoLoop RetQ ce
         (stmts_env ce NoLoop ty compiled)
         (stmts_env (gas_shadow_env T ce) NoLoop ty (MAP gas_shadow_stmt compiled))
         (eval_stmts pushed compiled) locked
         (st0,sa,sb,shadow_sa,shadow_sb,at_body,Gl,tnl,ce_end)) /\
  (!a rest ce es. ready (a::rest) ce es ==>
     stmt_frag_full (DF,lo,d,ctx,shadow_ctx,body_pg,callee,sf) pushed NoLoop RetQ ce
       (stmt_env ce NoLoop ty a)
       (stmt_env (gas_shadow_env T ce) NoLoop ty (gas_shadow_stmt a))
       (eval_stmt pushed a) es /\
     stmt_frag_prefix (DF,lo,d,ctx,shadow_ctx,body_pg,callee,sf) pushed NoLoop RetQ ce
       (stmt_env ce NoLoop ty a)
       (stmt_env (gas_shadow_env T ce) NoLoop ty (gas_shadow_stmt a))
       (eval_stmt pushed a) es /\
     (!gs mid ce' sa sm.
        eval_stmt pushed a (es with gas_obs := gs) = (INL (),mid) /\
        stmt_env ce NoLoop ty a sa = (ce',sm) /\
        cenv_top_ext ce ce' mid.scopes ==>
        ready rest ce' mid)) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (intcall_rest cx name mut nr ss prev rtv) (es1,t,G,tn)
Proof
  strip_tac >>
  qpat_x_assum `pushed = _` SUBST_ALL_TAC >>
  qpat_x_assum `body_pg = _` SUBST_ALL_TAC >>
  irule intcall_return_request_prefix >>
  qhdtm_assum `gas_invoke_entry` (irule_at Any) >>
  qpat_assum `decode_invoke _ = SOME _` (irule_at Any) >>
  qpat_assum `lookup_block _ _ = SOME _` (irule_at Any) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  Cases_on `?locked. lock_if_nr cx nr (is_view_mut mut) es1 = (INL (),locked) /\
                     storage_trace_domain cx st0 locked.storage_trace`
  >- suspend "locked" >>
  irule intcall_callee_no_locked_request_prefix >> conj_tac
  >~ [`~entered.vs_halted`]
  >- (qhdtm_assum `gas_invoke_entry` (strip_assume_tac o REWRITE_RULE [gas_invoke_entry_def]) >>
      gvs[]) >>
  qpat_assum `~(?locked. _ /\ _)` mp_tac >> metis_tac[oneTheory.one]
QED

Resume bool_chain_callee_rounds_prefix[locked]:
  fs[] >>
  qpat_assum `!locked. _ ==> _` (drule_all_then strip_assume_tac) >>
  irule intcall_callee_locked_request_prefix >>
  qexistsl_tac [`Gl`,`at_body`,`locked`,`tnl`] >> simp[] >>
  conj_tac
  >- fs[storage_trace_domain_def,valid_horizon_def,
        vyperFiniteStoragePreservationTheory.storage_well_formed_on_stk,
        vyperFiniteStoragePreservationTheory.storage_observations_ok_stk] >>
  qpat_assum `!a rest ce es. _` (mp_then Any mp_tac callee_stmts_from_step) >>
  simp[] >>
  disch_then (drule_then (mp_tac o cj 2)) >>
  simp[stmt_frag_prefix_def] >>
  disch_then (drule_then mp_tac) >>
  pure_rewrite_tac[gas_prefix_full_def] >>
  qpat_assum `!gs. eval_stmts _ ss _ = _` (pure_rewrite_tac o single) >>
  simp[NoAsms]
QED

Finalise bool_chain_callee_rounds_prefix
