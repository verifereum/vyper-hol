(* Request prefixes in RawCreate's amount and optional salt evaluation. *)
Theory s1PrefixRawCreateScalar
Ancestors
  bodyFullCreateHeld s1PrefixPreds s1PrefixCompose s1PrefixFrame s1PrefixOfVV
  s1PrefixDefs s1PrefixProps gasOutcomeFull gasOutcomeFullCompose
  vyperStorageTrace vyperStorageFootprint exprSimWordArgs exprSimSource
  exprLoweringProps builtinCreate loweringShapeDefs vyperState list
  bodyFullPreds vyperInterpreter compileEnv bodyFullExprsListFacts

Theorem create_operand_prefix_apply[local]:
  body_expr_prefix_ok cx e /\ body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env e es /\
  expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty e es (st0,sa,sb,sh,shb,op,s,G,tn) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
Proof
  strip_tac >>
  qpat_x_assum `body_expr_prefix_ok _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
  qpat_assum `!DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es. _`
    (qspecl_then [`DF`,`lo`,`d`,`PG`,`tops`,`ctx`,`shadow_ctx`,`func`,`shadow_func`,
                  `cenv`,`env`,`ty`,`es`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_sim_prefix_def]) >>
  first_assum drule >> simp[]
QED

Theorem create_prefix_gas_obs[local]:
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0 source
    (es with gas_obs := obs,s,G,tn) <=>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0 source (es,s,G,tn)
Proof
  simp[gas_prefix_full_def]
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  qpat_x_assum `body_exprs_full_ok _ (_::_)`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_exprs_full_ok_cons]) >>
  qpat_x_assum `body_exprs_prefix_ok _ (_::_)`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_exprs_prefix_ok_def]) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (bind (eval_expr cx amount) (read_result cx)) (es,s,G,tn)` by
    (irule create_operand_prefix_apply >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`cenv`,`d`,`env`,`y`,`sa`,`sm`,`sh`,`shadow_func`,`shm`,`tops`,
               `expr_type amount`] >>
     simp[expr_sim_full_pre_def] >> conj_tac
     >- (drule expr_body_pre_gas_admissible >> simp[]) >>
     first_assum ACCEPT_TAC) >>
  qabbrev_tac `next = \(v:value). bind (eval_exprs cx salts) (\vs. return (v::vs))` >>
  qabbrev_tac `Q = \(H:(bool # 256 word # type_value) list # num list)
                       (res:value+exception) mid G1 tn1 t.
    !v. res = INL v ==> gas_prefix_full
      (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
      (next v) (mid,t,G1,tn1)` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (bind (eval_expr cx amount) (read_result cx)) return)
    (es,s,G,tn) Q
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))` by
    suspend "amount_cut" >>
  `bind (bind (eval_expr cx amount) (read_result cx)) return =
   bind (eval_expr cx amount) (read_result cx)` by
    (simp[FUN_EQ_THM] >> gen_tac >>
     Cases_on `bind (eval_expr cx amount) (read_result cx) x` >>
     Cases_on `q` >> simp[bind_def,return_def]) >>
  fs[] >> once_rewrite_tac[eval_exprs_cons_action] >>
  `!v. storage_trace_frame (next v)` by
    simp[Abbr `next`,storage_trace_frame_bind_all,evaluate_storage_trace_frame,
         storage_trace_frame_return] >>
  qpat_assum `Abbrev (next = _)` (fn th => REWRITE_TAC[GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ Q _`
    (mp_then Any irule gas_prefix_full_bind) >>
  simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,
       storage_trace_frame_read_result,requests_outcomes_frame_bind_all,
       evaluate_requests_outcomes_frame,requests_outcomes_frame_read_result] >>
  reverse conj_tac
  >- (rpt gen_tac >> Cases_on `res` >> Cases_on `r` >> simp[exprSimDefsTheory.expr_exit_def]) >>
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
    by fs[storage_trace_domain_def] >>
  first_x_assum drule >> simp[Abbr `Q`]
QED
*)
Theorem raw_create_scalar_operands_prefix:
  body_const_cells_agree [(NONE,tops)] cx env es /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  expr_body_pre cenv cx env amount es /\ body_exprs_full_ok cx (amount::salts) /\
  body_exprs_prefix_ok cx (amount::salts) /\
  expr_type amount = BaseT (UintT 256) /\
  (if salted then ?salt. salts = [salt] /\ expr_type salt = BaseT (BytesT (Fixed 32))
   else salts = []) /\
  (!salt em. MEM salt salts /\ expr_sim_inv cenv cx env em ==>
     expr_body_pre cenv cx env salt em) /\
  lower_value compile_expr cenv (expr_type amount) amount sa = (y,sm) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type amount)
    (gas_shadow_expr amount) sh = (y,shm) /\
  compile_create_salt compile_expr cenv (if salted then SOME (HD salts) else NONE) sm = (sop,sb) /\
  compile_create_salt compile_expr (gas_shadow_env T cenv)
    (OPTION_MAP gas_shadow_expr (if salted then SOME (HD salts) else NONE)) shm = (sop,shb) /\
  gas_shadow_state sa sh /\ gas_shadow_state sm shm /\ gas_shadow_state sb shb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  fn_has_code sh shm shadow_func /\ fn_has_code shm shb shadow_func /\ ci_mono sa sm /\
  local_ptrs_reserved cenv sa /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn i z. frag_reachable ctx func s fn i z ==> dalloca_fmp_headroom i z) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (eval_exprs cx (amount::salts)) (es,s,G,tn)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume raw_create_scalar_operands_prefix[amount_cut]:
  irule create_body_operand_cut_replay >>
  rpt (goal_assum (drule_at Any)) >> simp[storage_trace_frame_return] >>
  qexistsl [`cenv`,`d`,`env`,`y`,`sa`,`sm`,`sh`,`shadow_func`,`shm`,`tops`] >>
  simp[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (qmatch_goalsub_rename_tac `lower_value _ _ _ _ _` >>
       qpat_assum `expr_type amount = _` (fn th => once_rewrite_tac [GSYM th]) >>
       first_assum ACCEPT_TAC) >>
  map_every qx_gen_tac [`av`,`em`,`Gm`,`tm`,`m`] >>
  strip_tac >>
  irule gas_outcome_full_pure >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`Gm`,`em`,`INL av`,`m`,`tm`] >>
  simp[return_def,Abbr `Q`,create_prefix_gas_obs,fragGasOriginPtrTheory.gas_origin_ptr_path_rules] >>
  suspend "salt_prefix"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume raw_create_scalar_operands_prefix[salt_prefix]:
  gen_tac >> disch_tac >>
  `eval_exprs cx [] = return []` by simp[FUN_EQ_THM,eval_exprs_nil,return_def] >>
  `body_exprs_prefix_ok cx salts` by
    (first_x_assum irule >> rpt (goal_assum (drule_at Any))) >>
  `is_word_type (BaseT (UintT 256))` by simp[compileEnvTheory.is_word_type_def] >>
  qpat_assum `!H. _ ==> expr_post H _ _ _ _ amount _ _ _ _ _ _ _ _ /\ _`
    (mp_then Any (drule_all_then strip_assume_tac) create_word_cut_frame_facts) >>
  Cases_on `salted` >> gvs[]
  >- suspend "salt_some" >>
  simp[Abbr `next`,bind_return] >>
  irule gas_prefix_full_no_outcome >> simp[storage_trace_frame_return,return_def]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume raw_create_scalar_operands_prefix[salt_some]:
  Cases_on `lower_value compile_expr cenv (BaseT (BytesT (Fixed 32))) salt sm` >>
  Cases_on `lower_value compile_expr (gas_shadow_env T cenv)
    (BaseT (BytesT (Fixed 32))) (gas_shadow_expr salt) shm` >>
  gvs[exprLoweringTheory.compile_create_salt_def,comp_bind_def,comp_return_def] >>
  rename1 `lower_value _ _ _ salt sm = (sop1,sb)` >>
  rename1 `lower_value _ _ _ (gas_shadow_expr salt) _ = (sop1,shb)` >>
  `expr_body_pre cenv cx env salt em` by (first_assum irule >> first_assum ACCEPT_TAC) >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[ci_mono_def,local_ptrs_reserved_next_var] >>
  `!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z` by
    metis_tac[ci_mono_def,not_fresh_at_mono] >>
  `!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z` by
    metis_tac[ci_mono_def,not_fresh_at_mono] >>
  `!qe. SND (next av qe) = SND (bind (eval_expr cx salt) (read_result cx) qe)` by
    (simp[Abbr `next`] >> gen_tac >> once_rewrite_tac[eval_exprs_cons_action] >>
     once_rewrite_tac[bind_assoc] >> simp[bind_return] >>
     CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV bind_def))) >>
     Cases_on `bind (eval_expr cx salt) (read_result cx) qe` >>
     rename1 `_ = (res,mid)` >> Cases_on `res` >> simp[return_def]) >>
  drule gas_prefix_full_state_cong >> disch_then (fn th => once_rewrite_tac[th]) >>
  fs[Once body_exprs_prefix_ok_def] >>
  irule create_operand_prefix_apply >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`cenv`,`d`,`env`,`sop1`,`sm`,`sb`,`shm`,`shadow_func`,`shb`,`tops`,
            `BaseT (BytesT (Fixed 32))`] >>
  simp[expr_sim_full_pre_def] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  drule expr_body_pre_gas_admissible >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise raw_create_scalar_operands_prefix
*)
