(* Retain the CREATE-size clause when passing a body exit to composition. *)
Theory runtimeBodyComposeCreateSize
Ancestors
  gasOutcomeFull gasOutcomeFullMods createSizeExit
  bodyIntCallLockAbortExit bodyFullHashKeccakFixed bodyPtrDefs
  nonreentrantEntryPath transientLockPtr stateRelProj loweringStateRelDefs
  compileEnv emitHelperProps exprLoweringProps fragGasOriginPtr ptrDiscipline
  venomInst venomState words vyperAST

Theorem gas_outcome_full_record_create_size:
  gas_outcome_full (DF,lo,E,ctx,func,PG) tops cx st0 source (es,s,G,tn) Q
    (\H res ee gt r. create_size_exit_ok ctx res r /\ R H res ee gt r) <=>
  gas_outcome_full (DF,lo,E,ctx,func,PG) tops cx st0 source (es,s,G,tn) Q R
Proof
  `!p q. (p /\ p /\ q) <=> (p /\ q)` by metis_tac[] >>
  simp[gas_outcome_full_def]
QED

Theorem gas_outcome_full_mods_record_create_size:
  gas_outcome_full_mods (DF,lo,E,ctx,func,PG) mods cx st0 source (es,s,G,tn) Q
    (\H res ee gt r. create_size_exit_ok ctx res r /\ R H res ee gt r) <=>
  gas_outcome_full_mods (DF,lo,E,ctx,func,PG) mods cx st0 source (es,s,G,tn) Q R
Proof
  `!p q. (p /\ p /\ q) <=> (p /\ q)` by metis_tac[] >>
  simp[gas_outcome_full_mods_def]
QED

Theorem runtime_static_registration_lock_safe_suffix:
  compile_nonreentrant_lock global_nonreentrant_slot T (mut = View) sa = ((),sl) /\
  fn_has_code sa sl func /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  global_nonreentrant_slot < dimword (:256) /\
  stmt_state_rel ([],[global_nonreentrant_slot]) ctx func cenv cx es0 s0 /\
  ghost_inv ([],[global_nonreentrant_slot]) NONE cenv cx es0 G0 tn0 s0 /\
  tload (n2w global_nonreentrant_slot) s0 <> 1w /\
  mut <> View /\ cx.txn.is_static ==>
  ?u Gu tu. ~oversized_create_abort ctx (Abort ExHalt_abort u) /\
    !D E. gas_origin_ptr_path (D,0,E,ctx,func,[])
      (s0,G0,tn0) [] (Abort ExHalt_abort u,Gu,tu)
Proof
  strip_tac >>
  `s0.vs_call_ctx.cc_static` by
    (drule stateRelProjTheory.stmt_state_rel_state_rel >>
     disch_then (mp_tac o MATCH_MP stateRelProjTheory.state_rel_call_ctx_rel) >>
     simp[loweringStateRelDefsTheory.call_ctx_rel_def]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s0)` by
    (drule bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >> simp[]) >>
  `key_taint tn0.t_trans (n2w global_nonreentrant_slot) = {}` by
    (qpat_assum `ghost_inv _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_def]) >>
     drule transientLockPtrTheory.nonreentrant_slot_untainted >>
     disch_then (qspec_then `global_nonreentrant_slot` mp_tac) >>
     simp[key_taint_def, pred_setTheory.EXTENSION]) >>
  drule_all nonreentrantEntryPathTheory.compile_nonreentrant_lock_transient_prefix >>
  strip_tac >>
  `allocas_from 0 s0` by simp[allocas_from_def] >>
  `0 <= s0.vs_alloca_next` by simp[] >>
  (Q.SUBGOAL_THEN `tload (n2w global_nonreentrant_slot) s0 = 1w \/
      (~(mut = View) /\ s0.vs_call_ctx.cc_static)` ASSUME_TAC
   >- simp[]) >>
  drule_all (Q.INST [`lo` |-> `0`, `PG` |-> `[]`, `G` |-> `G0`]
    bodyIntCallLockAbortExitTheory.transient_lock_abort_origin_ptr_safe) >>
  simp[]
QED
