(* Bind the forced Uint2Str operand to the continuation only on success. *)
Theory bodyUint2StrReachedBindMods
Ancestors
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods
  bodyForcedStorageFrameMods[qualified] vyperStorageTrace vyperStorageFootprint
  vyperInterpreter vyperContext vyperState vyperAST exprSimHash
  exprSimDefs loweringPosts haltExitProj stmtSimProps
Libs monadsyntax

val uint2str_operand = ``bind (eval_expr cx e) (read_result cx)``;
val uint2str_next = ``\v (ee:evaluation_state).
  ((case builtin_result cx ee.accounts (BaseT (StringT n)) (Uint2Str n)
       [expr_type e] [v] of INL r => INL (Value r) | INR ex => INR ex),ee)``;

Theorem uint2str_reached_bind_mods:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    ^uint2str_operand (es,s0,G0,tn0)
    (\H res ee G tn t. ?v. res = INL v /\ P H v ee G tn t)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)) /\
  (!marks v ee G tn t.
     (!tail. ^uint2str_operand
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
       (INL v,ee with gas_obs := tail)) /\
     storage_trace_domain cx st0 ee.storage_trace /\
     ee.gas_obs = [] /\ ~t.vs_halted /\
     (!H. valid_horizon cx st0 H ee.storage_trace ==> P H v ee G tn t) ==>
     gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
       (^uint2str_next v) (ee,t,G,tn) Q
       (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
         (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (eval_expr cx (Builtin (BaseT (StringT n)) (Uint2Str n) [e])) (es,s0,G0,tn0) Q
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  strip_tac >>
  `eval_expr cx (Builtin (BaseT (StringT n)) (Uint2Str n) [e]) =
     bind ^uint2str_operand ^uint2str_next` by
    (irule eval_expr_unary_builtin_action >>
     simp[precompile_builtin_def, builtin_args_length_ok_def, is_self_codesize_def]) >>
  pop_assum SUBST1_TAC >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >- simp[storage_trace_frame_def]
  >- simp[bodyForcedStorageFrameModsTheory.bop_forced_storage_frame] >>
  qexists_tac `\H res ee G tn t.
    (?v. res = INL v /\ P H v ee G tn t) /\ ee.gas_obs = [] /\ ~t.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      goal_assum (drule_at Any) >> BETA_TAC >> simp[] >>
      rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def] >>
      strip_tac >>
      ONCE_REWRITE_TAC[INST_TYPE [beta |-> ``:value``] expr_exit_INR_type,
                       INST_TYPE [beta |-> ``:value``] halt_exit_INR_type] >> simp[]) >>
  qx_genl_tac [`marks`,`res`,`ee`,`G`,`tn`,`t`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then strip_assume_tac) >> gvs[] >>
  first_x_assum irule >> simp[] >> qexists_tac `marks` >> simp[]
QED
