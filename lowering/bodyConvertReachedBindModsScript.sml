(* Compose the forced bytestring operand with the reached Convert suffix. *)
Theory bodyConvertReachedBindMods
Ancestors
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState vyperAST
  exprSimConvert exprSimDefs loweringPosts haltExitProj stmtSimProps
Libs monadsyntax

val convert_operand = ``bind (eval_expr cx e) (read_result cx)``;
val convert_next = ``\v (ee:evaluation_state).
  (sum_CASE (convert_result cx (expr_type e) dst v) (\w. INL (Value w)) INR,ee)``;

(* Keep the operand's physical post schematic: the binding neither weakens
   its all-horizon facts nor depends on the chosen scalar suffix. *)
Theorem convert_reached_bind_mods:
  eval_expr cx (TypeBuiltin dst Convert dst [e]) =
    bind ^convert_operand ^convert_next /\
  storage_trace_frame ^convert_operand /\
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    ^convert_operand (es,s0,G0,tn0)
    (\H res ee G tn t. ?v. res = INL v /\ P H v ee G tn t)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)) /\
  (!marks v ee G tn t.
     (!tail. ^convert_operand
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
       (INL v,ee with gas_obs := tail)) /\
     storage_trace_domain cx st0 ee.storage_trace /\
     ee.gas_obs = [] /\ ~t.vs_halted /\
     (!H. valid_horizon cx st0 H ee.storage_trace ==> P H v ee G tn t) ==>
     gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
       (^convert_next v) (ee,t,G,tn) Q
       (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
         (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (eval_expr cx (TypeBuiltin dst Convert dst [e])) (es,s0,G0,tn0) Q
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  strip_tac >>
  qpat_x_assum `eval_expr _ (TypeBuiltin _ Convert _ _) = _` SUBST1_TAC >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >- simp[storage_trace_frame_def]
  >- first_assum ACCEPT_TAC >>
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
