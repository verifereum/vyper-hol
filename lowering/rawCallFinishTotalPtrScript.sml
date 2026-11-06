(* Total source normalization and counted finish assembly. *)
Theory rawCallFinishTotalPtr
Ancestors
  rawCallFinishStepPtr rawCallFinishCodePtr rawCallFinishSuffixPtr
  rawCallSourceDomainPtr rawCallSourceActionPtr gasSummary exprSimOperands
  exprLoweringProps bodyPtrDefs wordArgsPtr exprSimWordArgs
  emitHelperProps fragGasPathPtr

Theorem raw_call_take_gas_obs:
  take_call_outcome target data value_opt (es with gas_obs := tail) =
    (FST (take_call_outcome target data value_opt es),
     SND (take_call_outcome target data value_opt es) with gas_obs := tail)
Proof
  simp[vyperCallOutcomeTheory.take_call_outcome_def,
    vyperCallOutcomeTheory.call_outcome_request_def] >>
  Cases_on `es.outcomes` >> simp[] >> pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[]
QED

Theorem raw_call_adopt_gas_obs:
  adopt_call_outcome rq outcome (es with gas_obs := tail) =
    (FST (adopt_call_outcome rq outcome es),
     SND (adopt_call_outcome rq outcome es) with gas_obs := tail)
Proof
  simp[vyperCallOutcomeTheory.adopt_call_outcome_equation] >>
  Cases_on `rq.cr_static` >> Cases_on `outcome.co_success` >>
  Cases_on `rq.cr_kind = MessageCall` >> simp[]
QED

Theorem raw_call_prepared_source_total:
  stmt_state_rel ctx func cenv cx es s /\ expr_sim_inv cenv cx env es /\
  ~flags.rcf_is_delegate /\
  gas_admissible (eval_raw_call cx flags target data amount gas) expr_vv_res_ok es ==>
  ?rq outcome es1.
    take_call_outcome target data (if flags.rcf_is_static then NONE else SOME amount) es =
      (INL (rq,outcome),es1) /\
    (!tail. eval_raw_call cx flags target data amount gas (es with gas_obs := tail) =
      (if flags.rcf_revert_on_failure /\ ~outcome.co_success then
         INR (Error (RevertData outcome.co_returnData))
       else INL (Value (if flags.rcf_revert_on_failure then
         if flags.rcf_max_outsize = 0 then NoneV
         else BytesV (TAKE flags.rcf_max_outsize outcome.co_returnData)
       else if flags.rcf_max_outsize = 0 then BoolV outcome.co_success
       else ArrayV (TupleV [BoolV outcome.co_success;
         BytesV (TAKE flags.rcf_max_outsize outcome.co_returnData)]))),
       SND (adopt_call_outcome rq outcome es1) with gas_obs := tail))
Proof
  strip_tac >> drule raw_call_admissible_flags >> strip_tac >>
  drule_all raw_call_prepared_take_success >>
  disch_then (qspecl_then [`if flags.rcf_is_static then NONE else SOME amount`,
    `target`, `data`] strip_assume_tac) >>
  qexistsl_tac [`rq`, `outcome`, `ee`] >> simp[] >> gen_tac >>
  mp_tac (raw_call_source_oracle_action |> Q.INST [`es` |-> `es with gas_obs := tail`,
    `esf` |-> `es with gas_obs := tail`, `es1` |-> `ee with gas_obs := tail`,
    `value_opt` |-> `if flags.rcf_is_static then NONE else SOME amount`]) >>
  impl_tac >- (drule raw_call_prepared_source_domain >>
    disch_then (qspecl_then [`flags.rcf_is_static`, `amount`] strip_assume_tac) >>
    gvs[vyperInterpreterTheory.frame_call_value_def, vyperStateTheory.return_def,
      raw_call_take_gas_obs] >> metis_tac[]) >>
  simp[raw_call_adopt_gas_obs] >>
  Cases_on `flags.rcf_revert_on_failure /\ ~outcome.co_success` >> simp[]
QED


Theorem raw_call_case_emit_facts:
  (case (if stat then StaticCall else RegularCall) of
     RegularCall => emit_op CALL [gas_op;addr;value_op;dp;dl;op;rz_op]
   | DelegateCall => emit_op DELEGATECALL [gas_op;addr;dp;dl;op;rz_op]
   | StaticCall => emit_op STATICCALL [gas_op;addr;dp;dl;op;rz_op]) sa = (result,sc) /\
  fn_has_code sa sc func ==>
  ?out. result = Var out /\ ~not_fresh_at sa out
Proof
  Cases_on `stat` >> simp[] >> strip_tac >>
  drule_all raw_call_emit_code >> metis_tac[]
QED


Theorem raw_call_scalar_finish:
  compile_raw_call_finish addr dp dl gas_op value_op
    (if stat then StaticCall else RegularCall) 0 F ov op sa = (result,sb) /\
  fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel ctx func cenv cx es s /\
  eval_operand gas_op s = SOME gas /\ eval_operand addr s = SOME aw /\
  (~stat ==> eval_operand value_op s = SOME vw) /\
  eval_operand dp s = SOME ao /\ eval_operand dl s = SOME az /\ eval_operand op s = SOME 0w /\
  w2w aw = target /\ w2n (if stat then 0w else vw) =
    (case value_opt of NONE => 0 | SOME n => n) /\ stat = IS_NONE value_opt /\
  take_call_outcome target (read_memory (w2n ao) (w2n az) s) value_opt es = (INL (rq,outcome),es1) /\
  (!out. ~not_fresh_at sa out ==>
    access_ok 0 G func (mk_inst sa.cs_next_id (if stat then STATICCALL else CALL)
      (if stat then [gas_op;addr;dp;dl;op;Lit 0w]
       else [gas_op;addr;value_op;dp;dl;op;Lit 0w]) [out]) s /\
    taint_ok func tn (mk_inst sa.cs_next_id (if stat then STATICCALL else CALL)
      (if stat then [gas_op;addr;dp;dl;op;Lit 0w]
       else [gas_op;addr;value_op;dp;dl;op;Lit 0w]) [out]) s) /\
  allocas_from 0 s /\ ~ctx_has_dalloca ctx /\ stor_taint_ok cx tn s /\
  ~s.vs_halted /\ ~cenv.ce_is_ctor /\
  ghost_inv dep cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  is_word_type ty /\ type_memory_bytes cenv (lowered_value_type cenv e) = 0 ==>
  ?H un t. gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 H un (OK t) /\
    ptr_val_ok cx ty (BoolV outcome.co_success) result H un t /\ ptr_buf_ok cenv e result H t /\
    stmt_state_rel ctx func cenv cx (SND (adopt_call_outcome rq outcome es1)) t /\
    ghost_inv dep cenv cx (SND (adopt_call_outcome rq outcome es1)) H un t /\
    ghost_kept cenv es sa G tn s H un /\ wb_frame cenv es sa s t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted
Proof
  strip_tac >> drule_all raw_call_nonrevert_code_groups >> strip_tac >>
  fs[compileEnvTheory.comp_return_def] >>
  drule_all raw_call_case_emit_facts >> strip_tac >> fs[] >>
  mp_tac (raw_call_extracted_checked_full |> Q.INST
    [`protected` |-> `sa`, `d` |-> `dep`, `rz_op` |-> `Lit 0w`, `rz` |-> `0w`, `ro` |-> `0w`, `sc` |-> `sb`]) >>
  (impl_tac >- (simp[venomStateTheory.eval_operand_def, compileEnvTheory.regions_disjoint_def] >>
    metis_tac[fresh_not_local_ptr])) >> strip_tac >>
  `eval_operand (Var out) u = SOME (val_to_w256 (BoolV outcome.co_success))` by
    simp[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
      valueEncodingTheory.val_to_w256_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  `return (Var out) sb = (Var out,sb)` by simp[compileEnvTheory.comp_return_def] >>
  drule_all (raw_call_scalar_suffix |> Q.INST [`protected` |-> `sa`]) >> strip_tac >>
  qpat_x_assum `!PG. _` (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`H`, `un`, `u`] >> simp[] >>
  drule_all (cj 2 gas_path_ptr_rules) >> simp[]
QED

val () = if null (hyp raw_call_scalar_finish) then ()
  else raise Fail "scalar finish has kernel hypotheses";
