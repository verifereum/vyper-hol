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
  ?out. result = Var out /\ ~not_fresh_at sa out /\ not_fresh_at sc out
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
  eval_operand dp s = SOME ao /\ eval_operand dl s = SOME az /\ eval_operand op s = SOME ro /\
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
  local_ptrs_reserved cenv protected /\ ci_mono protected sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at protected x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at protected x) /\
  (!name a len. local_region cenv es.scopes s name a len ==>
    regions_disjoint (w2n ro) 0 a len) /\
  (!aid a len. aid < protected.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
    regions_disjoint (w2n ro) 0 a len) /\
  is_word_type ty ==>
  ?H un t. gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 H un (OK t) /\
    eval_operand result t = SOME (val_to_w256 (BoolV outcome.co_success)) /\
    ptr_val_ok cx ty (BoolV outcome.co_success) result H un t /\
    (~is_word_type ty ==> ptr_buf_ok cenv e result H t) /\
    stmt_state_rel ctx func cenv cx (SND (adopt_call_outcome rq outcome es1)) t /\
    ghost_inv dep cenv cx (SND (adopt_call_outcome rq outcome es1)) H un t /\
    ghost_kept cenv es protected G tn s H un /\ wb_frame cenv es protected s t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted
Proof
  strip_tac >> drule_all raw_call_nonrevert_code_groups >> strip_tac >>
  fs[compileEnvTheory.comp_return_def] >>
  drule_all raw_call_case_emit_facts >> strip_tac >> fs[] >>
  mp_tac (raw_call_extracted_checked_full |> Q.INST
    [`d` |-> `dep`, `rz_op` |-> `Lit 0w`, `rz` |-> `0w`, `sc` |-> `sb`]) >>
  (impl_tac >- (simp[venomStateTheory.eval_operand_def] >>
    fs[exprLoweringPropsTheory.ci_mono_def] >>
    metis_tac[fresh_not_local_ptr, freshWritesTheory.not_fresh_at_mono])) >> strip_tac >>
  `eval_operand (Var out) u = SOME (val_to_w256 (BoolV outcome.co_success))` by
    simp[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
      valueEncodingTheory.val_to_w256_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  `return (Var out) sb = (Var out,sb)` by simp[compileEnvTheory.comp_return_def] >>
  drule_all (raw_call_scalar_suffix |> Q.INST [`protected` |-> `protected`]) >> strip_tac >>
  qpat_x_assum `!protected e PG. _`
    (qspecl_then [`protected`, `e`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`H`, `un`, `u`] >> simp[] >>
  drule_all (cj 2 gas_path_ptr_rules) >> simp[]
QED

val () = if null (hyp raw_call_scalar_finish) then ()
  else raise Fail "scalar finish has kernel hypotheses";

(* Both oracle outcomes at zero capacity share the same checked edge. *)
Theorem raw_call_zero_reverting_finish:
  compile_raw_call_finish addr dp dl gas_op value_op
    (if stat then StaticCall else RegularCall) 0 T ov op sa = (result,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel ctx func cenv cx es s /\
  eval_operand gas_op s = SOME gas /\ eval_operand addr s = SOME aw /\
  (~stat ==> eval_operand value_op s = SOME vw) /\
  eval_operand dp s = SOME ao /\ eval_operand dl s = SOME az /\ eval_operand op s = SOME ro /\
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
  local_ptrs_reserved cenv protected /\ ci_mono protected sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at protected x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at protected x) /\
  (!name a len. local_region cenv es.scopes s name a len ==>
    regions_disjoint (w2n ro) 0 a len) /\
  (!aid a len. aid < protected.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
    regions_disjoint (w2n ro) 0 a len) /\
  LENGTH outcome.co_returnData < dimword(:256) /\
  type_memory_bytes cenv (lowered_value_type cenv e) = 0 ==>
  ?H un t. gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 H un
      (if outcome.co_success then OK t else Abort Revert_abort t) /\
    t.vs_returndata = outcome.co_returnData /\
    (if outcome.co_success then
      result = Lit 0w /\
      ptr_val_ok cx NoneT NoneV result H un t /\ ptr_buf_ok cenv e result H t /\
      stmt_state_rel ctx func cenv cx (SND (adopt_call_outcome rq outcome es1)) t /\
      ghost_inv dep cenv cx (SND (adopt_call_outcome rq outcome es1)) H un t /\
      ghost_kept cenv es protected G tn s H un /\ wb_frame cenv es protected s t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted
     else t.vs_halted)
Proof
  strip_tac >> drule_all raw_call_reverting_code_groups >> strip_tac >>
  drule_all raw_call_case_emit_facts >> strip_tac >> fs[] >>
  mp_tac (raw_call_extracted_checked_full |> Q.INST
    [`d` |-> `dep`, `rz_op` |-> `Lit 0w`, `rz` |-> `0w`]) >>
  (impl_tac >- (simp[venomStateTheory.eval_operand_def] >>
    fs[exprLoweringPropsTheory.ci_mono_def] >>
    metis_tac[fresh_not_local_ptr, freshWritesTheory.not_fresh_at_mono])) >> strip_tac >>
  `eval_operand (Var out) u = SOME (val_to_w256 (BoolV outcome.co_success))` by
    simp[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
      valueEncodingTheory.val_to_w256_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  `u.vs_returndata = outcome.co_returnData` by
    fs[venomStateTheory.update_var_def] >>
  `local_ptrs_reserved cenv sj /\
   (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sj x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sj x)` by
    (fs[compileEnvTheory.local_ptrs_reserved_def, exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS]) >>
  mp_tac (raw_call_reverting_suffix |> Q.INST
    [`n` |-> `0`, `ty` |-> `NoneT`, `s` |-> `u`, `sa` |-> `sj`, `sj` |-> `se`,
     `G` |-> `H`, `tn` |-> `un`, `flag` |-> `outcome.co_success`,
     `es` |-> `SND (adopt_call_outcome rq outcome es1)`]) >>
  impl_tac >- gvs[] >> strip_tac >>
  `gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 H' un'
    (if outcome.co_success then OK t' else Abort Revert_abort t')` by
    (drule_all (cj 2 gas_path_ptr_rules) >> simp[]) >>
  qexistsl_tac [`H'`, `un'`, `t'`] >> simp[] >>
  Cases_on `outcome.co_success` >> gvs[] >>
  drule_all (rawCallFinishBridgePtrTheory.oracle_taken_suffix_frames |>
    Q.INST [`sa` |-> `protected`] |>
    SIMP_RULE (srw_ss()) [exprLoweringPropsTheory.ci_mono_refl]) >> simp[]
QED

Theorem raw_call_positive_reverting_finish:
  compile_raw_call_finish addr dp dl gas_op value_op
    (if stat then StaticCall else RegularCall) n T (Var src) op sa = (result,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel ctx func cenv cx es s /\
  eval_operand gas_op s = SOME gas /\ eval_operand addr s = SOME aw /\
  (~stat ==> eval_operand value_op s = SOME vw) /\
  eval_operand dp s = SOME ao /\ eval_operand dl s = SOME az /\
  eval_operand op s = SOME (n2w (ob+32)) /\
  w2w aw = target /\ w2n (if stat then 0w else vw) =
    (case value_opt of NONE => 0 | SOME k => k) /\ stat = IS_NONE value_opt /\
  take_call_outcome target (read_memory (w2n ao) (w2n az) s) value_opt es = (INL (rq,outcome),es1) /\
  (!out. ~not_fresh_at sa out ==>
    access_ok 0 G func (mk_inst sa.cs_next_id (if stat then STATICCALL else CALL)
      (if stat then [gas_op;addr;dp;dl;op;Lit (n2w n)]
       else [gas_op;addr;value_op;dp;dl;op;Lit (n2w n)]) [out]) s /\
    taint_ok func tn (mk_inst sa.cs_next_id (if stat then STATICCALL else CALL)
      (if stat then [gas_op;addr;dp;dl;op;Lit (n2w n)]
       else [gas_op;addr;value_op;dp;dl;op;Lit (n2w n)]) [out]) s) /\
  allocas_from 0 s /\ ~ctx_has_dalloca ctx /\ stor_taint_ok cx tn s /\
  ~s.vs_halted /\ ~cenv.ce_is_ctor /\ ghost_inv dep cenv cx es G tn s /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv protected /\ ci_mono protected sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at protected x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at protected x) /\
  (!name a len. local_region cenv es.scopes s name a len ==> regions_disjoint ob capacity a len) /\
  (!id a len. id < protected.cs_next_id /\ FLOOKUP s.vs_allocas id = SOME (a,len) ==>
    regions_disjoint ob capacity a len) /\
  0 < n /\ n+32 <= capacity /\ ob+capacity < dimword(:256) /\
  lookup_var src s = SOME (n2w ob) /\ ptr_covers G tn src s capacity /\
  not_fresh_at sa src /\ FLOOKUP s.vs_allocas aid = SOME (ob,capacity) /\ aid < sa.cs_next_id /\
  LENGTH outcome.co_returnData < dimword(:256) /\ ~is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (BytesT (Dynamic n))) /\
  val_store_size (BaseTV (BytesT (Dynamic n))) (BytesV (TAKE n outcome.co_returnData)) <= capacity /\
  type_memory_bytes cenv (lowered_value_type cenv e) <= capacity ==>
  ?H un t. gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 H un
      (if outcome.co_success then OK t else Abort Revert_abort t) /\
    t.vs_returndata = outcome.co_returnData /\
    (if outcome.co_success then
      result = Var src /\ lookup_var src t = SOME (n2w ob) /\
      t.vs_allocas = s.vs_allocas /\
      (!name a len. local_region cenv
        (SND (adopt_call_outcome rq outcome es1)).scopes t name a len ==>
        regions_disjoint ob capacity a len) /\
      ptr_val_ok cx ty (BytesV (TAKE n outcome.co_returnData)) result H un t /\
      ptr_buf_ok cenv e result H t /\
      stmt_state_rel ctx func cenv cx (SND (adopt_call_outcome rq outcome es1)) t /\
      ghost_inv dep cenv cx (SND (adopt_call_outcome rq outcome es1)) H un t /\
      ghost_kept cenv es protected G tn s H un /\ wb_frame cenv es protected s t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted
     else t.vs_halted)
Proof
  strip_tac >> drule_all raw_call_reverting_code_groups >> strip_tac >>
  drule_all raw_call_case_emit_facts >> strip_tac >> fs[] >>
  `n < dimword(:256) /\ ob+32 < dimword(:256) /\ 32 <= capacity` by decide_tac >>
  mp_tac (raw_call_extracted_checked_full |> Q.INST
    [`d` |-> `dep`, `rz_op` |-> `Lit (n2w n)`, `rz` |-> `n2w n`, `ro` |-> `n2w (ob+32)`]) >>
  (impl_tac >- (simp[venomStateTheory.eval_operand_def] >>
    fs[exprLoweringPropsTheory.ci_mono_def, compileEnvTheory.regions_disjoint_def,
      wordsTheory.w2n_n2w] >>
    conj_tac >- metis_tac[fresh_not_local_ptr] >>
    conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
    conj_tac >> rpt strip_tac >> res_tac >> decide_tac)) >> strip_tac >>
  `src <> out` by metis_tac[] >>
  mp_tac (raw_call_allocated_suffix_ready |> Q.INST
    [`inst` |-> `mk_inst sa.cs_next_id (if stat then STATICCALL else CALL)
      (if stat then [gas_op;addr;dp;dl;op;Lit (n2w n)]
       else [gas_op;addr;value_op;dp;dl;op;Lit (n2w n)]) [out]`,
     `addr_op` |-> `addr`, `ao_op` |-> `dp`, `az_op` |-> `dl`, `ro_op` |-> `op`,
     `rz_op` |-> `Lit (n2w n)`, `cap` |-> `n`, `iid` |-> `sa.cs_next_id`,
     `flag` |-> `outcome.co_success`, `rd` |-> `outcome.co_returnData`,
     `ee` |-> `SND (adopt_call_outcome rq outcome es1)`]) >>
  impl_tac >- (drule rawCallMemoryFramePtrTheory.oracle_take_adoption_locals >>
    strip_tac >> gvs[venomStateTheory.eval_operand_def,
      venomStateTheory.update_var_def, wordsTheory.w2n_n2w] >> metis_tac[]) >> strip_tac >>
  `local_ptrs_reserved cenv sj /\
   (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sj x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sj x) /\
   ci_mono protected sn /\ not_fresh_at sn src` by
    (fs[compileEnvTheory.local_ptrs_reserved_def, exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS,
       compileEnvTheory.cs_extends_trans]) >>
  mp_tac (raw_call_reverting_suffix |> Q.INST
    [`s` |-> `u`, `sa` |-> `sj`, `sj` |-> `se`, `dst` |-> `src`, `a` |-> `n2w ob`,
     `G` |-> `H`, `tn` |-> `un`, `flag` |-> `outcome.co_success`,
     `es` |-> `SND (adopt_call_outcome rq outcome es1)`]) >>
  impl_tac >- (gvs[wordsTheory.w2n_n2w] >> strip_tac >> gvs[] >> metis_tac[]) >> strip_tac >>
  `gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 H' un'
    (if outcome.co_success then OK t' else Abort Revert_abort t')` by
    (drule_all (cj 2 gas_path_ptr_rules) >> simp[]) >>
  qexistsl_tac [`H'`, `un'`, `t'`] >> simp[] >>
  Cases_on `outcome.co_success` >> gvs[] >>
  drule_all (rawCallFinishBridgePtrTheory.oracle_taken_suffix_frames |>
    Q.INST [`sa` |-> `protected`] |>
    SIMP_RULE (srw_ss()) [exprLoweringPropsTheory.ci_mono_refl]) >> gvs[] >>
  strip_tac >>
  drule rawCallMemoryFramePtrTheory.oracle_take_adoption_locals >> strip_tac >>
  `!name a len. local_region cenv es.scopes s name a len <=>
    local_region cenv (SND (adopt_call_outcome rq outcome es1)).scopes t' name a len` by
    (irule wordArgsPtrTheory.wb_frame_local_regions >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem raw_call_positive_nonreverting_finish:
  compile_raw_call_finish addr dp dl gas_op value_op
    (if stat then StaticCall else RegularCall) n F (Var src) op sa = (result,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel ctx func cenv cx es s /\
  eval_operand gas_op s = SOME gas /\ eval_operand addr s = SOME aw /\
  (~stat ==> eval_operand value_op s = SOME vw) /\
  eval_operand dp s = SOME ao /\ eval_operand dl s = SOME az /\
  eval_operand op s = SOME (n2w (ob+32)) /\
  w2w aw = target /\ w2n (if stat then 0w else vw) =
    (case value_opt of NONE => 0 | SOME k => k) /\ stat = IS_NONE value_opt /\
  take_call_outcome target (read_memory (w2n ao) (w2n az) s) value_opt es = (INL (rq,outcome),es1) /\
  (!out. ~not_fresh_at sa out ==>
    access_ok 0 G func (mk_inst sa.cs_next_id (if stat then STATICCALL else CALL)
      (if stat then [gas_op;addr;dp;dl;op;Lit (n2w n)]
       else [gas_op;addr;value_op;dp;dl;op;Lit (n2w n)]) [out]) s /\
    taint_ok func tn (mk_inst sa.cs_next_id (if stat then STATICCALL else CALL)
      (if stat then [gas_op;addr;dp;dl;op;Lit (n2w n)]
       else [gas_op;addr;value_op;dp;dl;op;Lit (n2w n)]) [out]) s) /\
  allocas_from 0 s /\ ~ctx_has_dalloca ctx /\ stor_taint_ok cx tn s /\
  ~s.vs_halted /\ ~cenv.ce_is_ctor /\ ghost_inv dep cenv cx es G tn s /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv protected /\ ci_mono protected sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at protected x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at protected x) /\
  (!name a len. local_region cenv es.scopes s name a len ==> regions_disjoint ob capacity a len) /\
  (!id a len. id < protected.cs_next_id /\ FLOOKUP s.vs_allocas id = SOME (a,len) ==>
    regions_disjoint ob capacity a len) /\
  0 < n /\ n+32 <= capacity /\ ob+capacity < dimword(:256) /\
  capacity = 32+((n+31) DIV 32)*32 /\ 32+capacity < dimword(:256) /\
  lookup_var src s = SOME (n2w ob) /\ ptr_covers G tn src s capacity /\
  not_fresh_at sa src /\ FLOOKUP s.vs_allocas aid = SOME (ob,capacity) /\ aid < sa.cs_next_id /\
  LENGTH outcome.co_returnData < dimword(:256) /\ ~is_word_type bty /\
  evaluate_type (get_tenv cx) bty = SOME (BaseTV (BytesT (Dynamic n))) /\
  val_store_size (BaseTV (BytesT (Dynamic n))) (BytesV (TAKE n outcome.co_returnData)) <= capacity /\
  type_memory_bytes cenv (lowered_value_type cenv be) <= capacity /\
  ~is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))]) /\
  val_store_size (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))])
    (ArrayV (TupleV [BoolV outcome.co_success;BytesV (TAKE n outcome.co_returnData)])) <= 32+capacity /\
  type_memory_bytes cenv (lowered_value_type cenv e) <= 32+capacity ==>
  ?H un t. gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 H un (OK t) /\
    t.vs_returndata = outcome.co_returnData /\
    (?b ai. eval_operand result t = SOME (n2w b) /\
      FLOOKUP t.vs_allocas ai = SOME (b,32+capacity) /\
      sa.cs_next_id <= ai /\ ai < sb.cs_next_id /\
      (!name a len. local_region cenv
        (SND (adopt_call_outcome rq outcome es1)).scopes t name a len ==>
        regions_disjoint b (32+capacity) a len)) /\
    ptr_val_ok cx ty (ArrayV (TupleV [BoolV outcome.co_success;
      BytesV (TAKE n outcome.co_returnData)])) result H un t /\ ptr_buf_ok cenv e result H t /\
    stmt_state_rel ctx func cenv cx (SND (adopt_call_outcome rq outcome es1)) t /\
    ghost_inv dep cenv cx (SND (adopt_call_outcome rq outcome es1)) H un t /\
    ghost_kept cenv es protected G tn s H un /\ wb_frame cenv es protected s t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted
Proof
  strip_tac >> drule_all raw_call_nonrevert_code_groups >> strip_tac >>
  drule_all raw_call_case_emit_facts >> strip_tac >> fs[] >>
  `n < dimword(:256) /\ ob+32 < dimword(:256) /\ 32 <= capacity` by decide_tac >>
  mp_tac (raw_call_extracted_checked_full |> Q.INST
    [`d` |-> `dep`, `rz_op` |-> `Lit (n2w n)`, `rz` |-> `n2w n`, `ro` |-> `n2w (ob+32)`]) >>
  (impl_tac >- (simp[venomStateTheory.eval_operand_def] >>
    fs[exprLoweringPropsTheory.ci_mono_def, compileEnvTheory.regions_disjoint_def,
      wordsTheory.w2n_n2w] >>
    conj_tac >- metis_tac[fresh_not_local_ptr] >>
    conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
    conj_tac >> rpt strip_tac >> res_tac >> decide_tac)) >> strip_tac >>
  `src <> out` by metis_tac[] >>
  mp_tac (raw_call_allocated_suffix_ready |> Q.INST
    [`inst` |-> `mk_inst sa.cs_next_id (if stat then STATICCALL else CALL)
      (if stat then [gas_op;addr;dp;dl;op;Lit (n2w n)]
       else [gas_op;addr;value_op;dp;dl;op;Lit (n2w n)]) [out]`,
     `addr_op` |-> `addr`, `ao_op` |-> `dp`, `az_op` |-> `dl`, `ro_op` |-> `op`,
     `rz_op` |-> `Lit (n2w n)`, `cap` |-> `n`, `iid` |-> `sa.cs_next_id`,
     `flag` |-> `outcome.co_success`, `rd` |-> `outcome.co_returnData`,
     `ee` |-> `SND (adopt_call_outcome rq outcome es1)`]) >>
  impl_tac >- (drule rawCallMemoryFramePtrTheory.oracle_take_adoption_locals >>
    strip_tac >> gvs[venomStateTheory.eval_operand_def,
      venomStateTheory.update_var_def, wordsTheory.w2n_n2w] >> metis_tac[]) >> strip_tac >>
  mp_tac (raw_call_nonrevert_suffix |> Q.INST
    [`s` |-> `u`, `sa` |-> `sc`, `success` |-> `out`, `ncopy` |-> `capacity`,
     `aw` |-> `n2w ob`, `off` |-> `ob`, `len` |-> `capacity`,
     `G` |-> `H`, `tn` |-> `un`, `flag` |-> `outcome.co_success`,
     `es` |-> `SND (adopt_call_outcome rq outcome es1)`]) >>
  impl_tac >- (gvs[wordsTheory.w2n_n2w] >>
    conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  `gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 H' un' (OK t')` by
    (drule_all (cj 2 gas_path_ptr_rules) >> simp[]) >>
  qexistsl_tac [`H'`, `un'`, `t'`] >> simp[] >>
  drule_all (rawCallFinishBridgePtrTheory.oracle_taken_suffix_frames |>
    Q.INST [`sa` |-> `protected`] |>
    SIMP_RULE (srw_ss()) [exprLoweringPropsTheory.ci_mono_refl]) >> gvs[] >>
  strip_tac >> qexistsl_tac [`b`, `ai`] >>
  fs[venomStateTheory.eval_operand_def, exprLoweringPropsTheory.ci_mono_def] >>
  first_assum MATCH_ACCEPT_TAC
QED

(* Source normalization is supplied by raw_call_prepared_source_total before
   choosing one of the four finish branches.  Source gas is option-valued;
   the checked CALL gas operand is a word and is kept separate. *)
Theorem raw_call_scalar_finish_outcome:
  compile_raw_call_finish addr dp dl gas_op value_op
    (if stat then StaticCall else RegularCall) 0 F ov op sa = (result,sb) /\
  fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel ctx func cenv cx es s /\
  eval_operand gas_op s = SOME gas /\ eval_operand addr s = SOME aw /\
  (~stat ==> eval_operand value_op s = SOME vw) /\
  eval_operand dp s = SOME ao /\ eval_operand dl s = SOME az /\ eval_operand op s = SOME ro /\
  w2w aw = target /\ w2n (if stat then 0w else vw) =
    (case value_opt of NONE => 0 | SOME k => k) /\ stat = IS_NONE value_opt /\
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
  local_ptrs_reserved cenv protected /\ ci_mono protected sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at protected x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at protected x) /\
  (!name a len. local_region cenv es.scopes s name a len ==> regions_disjoint (w2n ro) 0 a len) /\
  (!aid a len. aid < protected.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
    regions_disjoint (w2n ro) 0 a len) /\
  is_word_type ty /\
  stat = flags.rcf_is_static /\ value_opt = (if flags.rcf_is_static then NONE else SOME amount) /\
  data = read_memory (w2n ao) (w2n az) s /\ flags.rcf_max_outsize = 0 /\ ~flags.rcf_revert_on_failure /\
  (!tail. eval_raw_call cx flags target data amount source_gas (es with gas_obs := tail) =
    (if flags.rcf_revert_on_failure /\ ~outcome.co_success then
       INR (Error (RevertData outcome.co_returnData))
     else INL (Value (if flags.rcf_revert_on_failure then
       if flags.rcf_max_outsize = 0 then NoneV
       else BytesV (TAKE flags.rcf_max_outsize outcome.co_returnData)
     else if flags.rcf_max_outsize = 0 then BoolV outcome.co_success
     else ArrayV (TupleV [BoolV outcome.co_success;
       BytesV (TAKE flags.rcf_max_outsize outcome.co_returnData)]))),
     SND (adopt_call_outcome rq outcome es1) with gas_obs := tail)) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_raw_call cx flags target data amount source_gas) (es,s,G,tn)
    (\res ee H un t. ?v. res = INL (Value v) /\
      v = BoolV outcome.co_success /\
      eval_operand result t = SOME (val_to_w256 v) /\
      ptr_val_ok cx ty v result H un t /\
      (~is_word_type ty ==> ptr_buf_ok cenv e result H t) /\
      stmt_state_rel ctx func cenv cx ee t /\ ghost_inv dep cenv cx ee H un t /\
      ghost_kept cenv es protected G tn s H un /\ wb_frame cenv es protected s t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted)
    (\res ee gt r. expr_exit res r)
Proof
  strip_tac >> drule_all raw_call_scalar_finish >>
  disch_then (qspecl_then [`e`, `PG`] strip_assume_tac) >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL (Value (BoolV outcome.co_success))`,
    `SND (adopt_call_outcome rq outcome es1)`, `H`, `un`, `OK t`] >>
  simp[gasSummaryTheory.gas_explicit_def, stmtFragPtrTheory.ghost_inv_gas_obs] >>
  metis_tac[]
QED

Theorem raw_call_zero_reverting_finish_outcome:
  compile_raw_call_finish addr dp dl gas_op value_op
    (if stat then StaticCall else RegularCall) 0 T ov op sa = (result,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel ctx func cenv cx es s /\
  eval_operand gas_op s = SOME gas /\ eval_operand addr s = SOME aw /\
  (~stat ==> eval_operand value_op s = SOME vw) /\
  eval_operand dp s = SOME ao /\ eval_operand dl s = SOME az /\ eval_operand op s = SOME ro /\
  w2w aw = target /\ w2n (if stat then 0w else vw) =
    (case value_opt of NONE => 0 | SOME k => k) /\ stat = IS_NONE value_opt /\
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
  local_ptrs_reserved cenv protected /\ ci_mono protected sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at protected x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at protected x) /\
  (!name a len. local_region cenv es.scopes s name a len ==> regions_disjoint (w2n ro) 0 a len) /\
  (!aid a len. aid < protected.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
    regions_disjoint (w2n ro) 0 a len) /\
  LENGTH outcome.co_returnData < dimword(:256) /\
  type_memory_bytes cenv (lowered_value_type cenv e) = 0 /\
  stat = flags.rcf_is_static /\ value_opt = (if flags.rcf_is_static then NONE else SOME amount) /\
  data = read_memory (w2n ao) (w2n az) s /\ flags.rcf_max_outsize = 0 /\ flags.rcf_revert_on_failure /\
  (!tail. eval_raw_call cx flags target data amount source_gas (es with gas_obs := tail) =
    (if flags.rcf_revert_on_failure /\ ~outcome.co_success then
       INR (Error (RevertData outcome.co_returnData))
     else INL (Value (if flags.rcf_revert_on_failure then
       if flags.rcf_max_outsize = 0 then NoneV
       else BytesV (TAKE flags.rcf_max_outsize outcome.co_returnData)
     else if flags.rcf_max_outsize = 0 then BoolV outcome.co_success
     else ArrayV (TupleV [BoolV outcome.co_success;
       BytesV (TAKE flags.rcf_max_outsize outcome.co_returnData)]))),
     SND (adopt_call_outcome rq outcome es1) with gas_obs := tail)) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_raw_call cx flags target data amount source_gas) (es,s,G,tn)
    (\res ee H un t. ?v. res = INL (Value v) /\
      v = NoneV /\
      result = Lit 0w /\
      ptr_val_ok cx NoneT v result H un t /\ ptr_buf_ok cenv e result H t /\
      stmt_state_rel ctx func cenv cx ee t /\ ghost_inv dep cenv cx ee H un t /\
      ghost_kept cenv es protected G tn s H un /\ wb_frame cenv es protected s t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted)
    (\res ee gt r. expr_exit res r)
Proof
  strip_tac >> drule_all raw_call_zero_reverting_finish >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`if outcome.co_success then INL (Value NoneV)
    else INR (Error (RevertData outcome.co_returnData))`,
    `SND (adopt_call_outcome rq outcome es1)`, `H`, `un`,
    `if outcome.co_success then OK t else Abort Revert_abort t`] >>
  Cases_on `outcome.co_success` >>
  gvs[gasSummaryTheory.gas_explicit_def, stmtFragPtrTheory.ghost_inv_gas_obs,
    fragExecTheory.exit_result_def, exprSimDefsTheory.expr_exit_def]
QED

Theorem raw_call_positive_reverting_finish_outcome:
  compile_raw_call_finish addr dp dl gas_op value_op
    (if stat then StaticCall else RegularCall) n T (Var src) op sa = (result,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel ctx func cenv cx es s /\
  eval_operand gas_op s = SOME gas /\ eval_operand addr s = SOME aw /\
  (~stat ==> eval_operand value_op s = SOME vw) /\
  eval_operand dp s = SOME ao /\ eval_operand dl s = SOME az /\
  eval_operand op s = SOME (n2w (ob+32)) /\
  w2w aw = target /\ w2n (if stat then 0w else vw) =
    (case value_opt of NONE => 0 | SOME k => k) /\ stat = IS_NONE value_opt /\
  take_call_outcome target (read_memory (w2n ao) (w2n az) s) value_opt es = (INL (rq,outcome),es1) /\
  (!out. ~not_fresh_at sa out ==>
    access_ok 0 G func (mk_inst sa.cs_next_id (if stat then STATICCALL else CALL)
      (if stat then [gas_op;addr;dp;dl;op;Lit (n2w n)]
       else [gas_op;addr;value_op;dp;dl;op;Lit (n2w n)]) [out]) s /\
    taint_ok func tn (mk_inst sa.cs_next_id (if stat then STATICCALL else CALL)
      (if stat then [gas_op;addr;dp;dl;op;Lit (n2w n)]
       else [gas_op;addr;value_op;dp;dl;op;Lit (n2w n)]) [out]) s) /\
  allocas_from 0 s /\ ~ctx_has_dalloca ctx /\ stor_taint_ok cx tn s /\
  ~s.vs_halted /\ ~cenv.ce_is_ctor /\ ghost_inv dep cenv cx es G tn s /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv protected /\ ci_mono protected sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at protected x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at protected x) /\
  (!name a len. local_region cenv es.scopes s name a len ==> regions_disjoint ob capacity a len) /\
  (!id a len. id < protected.cs_next_id /\ FLOOKUP s.vs_allocas id = SOME (a,len) ==>
    regions_disjoint ob capacity a len) /\
  0 < n /\ n+32 <= capacity /\ ob+capacity < dimword(:256) /\
  lookup_var src s = SOME (n2w ob) /\ ptr_covers G tn src s capacity /\
  not_fresh_at sa src /\ FLOOKUP s.vs_allocas aid = SOME (ob,capacity) /\ aid < sa.cs_next_id /\
  LENGTH outcome.co_returnData < dimword(:256) /\ ~is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (BytesT (Dynamic n))) /\
  val_store_size (BaseTV (BytesT (Dynamic n))) (BytesV (TAKE n outcome.co_returnData)) <= capacity /\
  type_memory_bytes cenv (lowered_value_type cenv e) <= capacity /\
  stat = flags.rcf_is_static /\ value_opt = (if flags.rcf_is_static then NONE else SOME amount) /\
  data = read_memory (w2n ao) (w2n az) s /\ n = flags.rcf_max_outsize /\ flags.rcf_revert_on_failure /\
  (!tail. eval_raw_call cx flags target data amount source_gas (es with gas_obs := tail) =
    (if flags.rcf_revert_on_failure /\ ~outcome.co_success then
       INR (Error (RevertData outcome.co_returnData))
     else INL (Value (if flags.rcf_revert_on_failure then
       if flags.rcf_max_outsize = 0 then NoneV
       else BytesV (TAKE flags.rcf_max_outsize outcome.co_returnData)
     else if flags.rcf_max_outsize = 0 then BoolV outcome.co_success
     else ArrayV (TupleV [BoolV outcome.co_success;
       BytesV (TAKE flags.rcf_max_outsize outcome.co_returnData)]))),
     SND (adopt_call_outcome rq outcome es1) with gas_obs := tail)) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_raw_call cx flags target data amount source_gas) (es,s,G,tn)
    (\res ee H un t. ?v. res = INL (Value v) /\
      v = BytesV (TAKE n outcome.co_returnData) /\
      result = Var src /\ lookup_var src t = SOME (n2w ob) /\
      t.vs_allocas = s.vs_allocas /\
      (!name a len. local_region cenv ee.scopes t name a len ==>
        regions_disjoint ob capacity a len) /\
      ptr_val_ok cx ty v result H un t /\ ptr_buf_ok cenv e result H t /\
      stmt_state_rel ctx func cenv cx ee t /\ ghost_inv dep cenv cx ee H un t /\
      ghost_kept cenv es protected G tn s H un /\ wb_frame cenv es protected s t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted)
    (\res ee gt r. expr_exit res r)
Proof
  strip_tac >> drule_all raw_call_positive_reverting_finish >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`if outcome.co_success then INL (Value (BytesV (TAKE n outcome.co_returnData)))
    else INR (Error (RevertData outcome.co_returnData))`,
    `SND (adopt_call_outcome rq outcome es1)`, `H`, `un`,
    `if outcome.co_success then OK t else Abort Revert_abort t`] >>
  Cases_on `outcome.co_success` >>
  gvs[gasSummaryTheory.gas_explicit_def, stmtFragPtrTheory.ghost_inv_gas_obs,
    fragExecTheory.exit_result_def, exprSimDefsTheory.expr_exit_def] >>
  first_assum MATCH_ACCEPT_TAC
QED

Theorem raw_call_positive_nonreverting_finish_outcome:
  compile_raw_call_finish addr dp dl gas_op value_op
    (if stat then StaticCall else RegularCall) n F (Var src) op sa = (result,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel ctx func cenv cx es s /\
  eval_operand gas_op s = SOME gas /\ eval_operand addr s = SOME aw /\
  (~stat ==> eval_operand value_op s = SOME vw) /\
  eval_operand dp s = SOME ao /\ eval_operand dl s = SOME az /\
  eval_operand op s = SOME (n2w (ob+32)) /\
  w2w aw = target /\ w2n (if stat then 0w else vw) =
    (case value_opt of NONE => 0 | SOME k => k) /\ stat = IS_NONE value_opt /\
  take_call_outcome target (read_memory (w2n ao) (w2n az) s) value_opt es = (INL (rq,outcome),es1) /\
  (!out. ~not_fresh_at sa out ==>
    access_ok 0 G func (mk_inst sa.cs_next_id (if stat then STATICCALL else CALL)
      (if stat then [gas_op;addr;dp;dl;op;Lit (n2w n)]
       else [gas_op;addr;value_op;dp;dl;op;Lit (n2w n)]) [out]) s /\
    taint_ok func tn (mk_inst sa.cs_next_id (if stat then STATICCALL else CALL)
      (if stat then [gas_op;addr;dp;dl;op;Lit (n2w n)]
       else [gas_op;addr;value_op;dp;dl;op;Lit (n2w n)]) [out]) s) /\
  allocas_from 0 s /\ ~ctx_has_dalloca ctx /\ stor_taint_ok cx tn s /\
  ~s.vs_halted /\ ~cenv.ce_is_ctor /\ ghost_inv dep cenv cx es G tn s /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv protected /\ ci_mono protected sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at protected x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at protected x) /\
  (!name a len. local_region cenv es.scopes s name a len ==> regions_disjoint ob capacity a len) /\
  (!id a len. id < protected.cs_next_id /\ FLOOKUP s.vs_allocas id = SOME (a,len) ==>
    regions_disjoint ob capacity a len) /\
  0 < n /\ n+32 <= capacity /\ ob+capacity < dimword(:256) /\
  capacity = 32+((n+31) DIV 32)*32 /\ 32+capacity < dimword(:256) /\
  lookup_var src s = SOME (n2w ob) /\ ptr_covers G tn src s capacity /\
  not_fresh_at sa src /\ FLOOKUP s.vs_allocas aid = SOME (ob,capacity) /\ aid < sa.cs_next_id /\
  LENGTH outcome.co_returnData < dimword(:256) /\ ~is_word_type bty /\
  evaluate_type (get_tenv cx) bty = SOME (BaseTV (BytesT (Dynamic n))) /\
  val_store_size (BaseTV (BytesT (Dynamic n))) (BytesV (TAKE n outcome.co_returnData)) <= capacity /\
  type_memory_bytes cenv (lowered_value_type cenv be) <= capacity /\
  ~is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))]) /\
  val_store_size (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))])
    (ArrayV (TupleV [BoolV outcome.co_success;BytesV (TAKE n outcome.co_returnData)])) <= 32+capacity /\
  type_memory_bytes cenv (lowered_value_type cenv e) <= 32+capacity /\
  stat = flags.rcf_is_static /\ value_opt = (if flags.rcf_is_static then NONE else SOME amount) /\
  data = read_memory (w2n ao) (w2n az) s /\ n = flags.rcf_max_outsize /\ ~flags.rcf_revert_on_failure /\
  (!tail. eval_raw_call cx flags target data amount source_gas (es with gas_obs := tail) =
    (if flags.rcf_revert_on_failure /\ ~outcome.co_success then
       INR (Error (RevertData outcome.co_returnData))
     else INL (Value (if flags.rcf_revert_on_failure then
       if flags.rcf_max_outsize = 0 then NoneV
       else BytesV (TAKE flags.rcf_max_outsize outcome.co_returnData)
     else if flags.rcf_max_outsize = 0 then BoolV outcome.co_success
     else ArrayV (TupleV [BoolV outcome.co_success;
       BytesV (TAKE flags.rcf_max_outsize outcome.co_returnData)]))),
     SND (adopt_call_outcome rq outcome es1) with gas_obs := tail)) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_raw_call cx flags target data amount source_gas) (es,s,G,tn)
    (\res ee H un t. ?v. res = INL (Value v) /\
      v = ArrayV (TupleV [BoolV outcome.co_success;BytesV (TAKE n outcome.co_returnData)]) /\
      (?b ai. eval_operand result t = SOME (n2w b) /\
        FLOOKUP t.vs_allocas ai = SOME (b,32+capacity) /\
        sa.cs_next_id <= ai /\ ai < sb.cs_next_id /\
        (!name a len. local_region cenv ee.scopes t name a len ==>
          regions_disjoint b (32+capacity) a len)) /\
      ptr_val_ok cx ty v result H un t /\ ptr_buf_ok cenv e result H t /\
      stmt_state_rel ctx func cenv cx ee t /\ ghost_inv dep cenv cx ee H un t /\
      ghost_kept cenv es protected G tn s H un /\ wb_frame cenv es protected s t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted)
    (\res ee gt r. expr_exit res r)
Proof
  strip_tac >> drule_all raw_call_positive_nonreverting_finish >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL (Value (ArrayV (TupleV [BoolV outcome.co_success;
    BytesV (TAKE n outcome.co_returnData)])))`,
    `SND (adopt_call_outcome rq outcome es1)`, `H`, `un`, `OK t`] >>
  gvs[gasSummaryTheory.gas_explicit_def, stmtFragPtrTheory.ghost_inv_gas_obs] >>
  qexistsl_tac [`b`, `ai`] >> simp[] >> first_assum MATCH_ACCEPT_TAC
QED
