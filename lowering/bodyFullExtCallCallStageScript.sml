Theory bodyFullExtCallCallStage
Ancestors
  bodyFullExtCallPrecheck bodyFullExtCallDispatch exprLowering
  compileEnv pair stateRelProj loweringStateRelDefs vyperCallOutcomeProps
  venomExecSemantics venomInst venomState vyperInterpreter vyperState words
  bodyPtrDefs ptrDiscipline ptrSafeRun oracleCallStepPtr contextCodegenRel memLocDefs
  fragGasEmitCtrl fragGasOriginPtr fragExec memSafeRun instMemFrontier gasEvents gasCount
  pred_set list exprSimRawCallCalldata exprSimExtCallCase extCallOracleStep
  abiCallerAllocation exprLoweringProps emitHelperProps
  gasOutcomeFullCompose vyperStorageTrace vyperStorageFootprint exprSimDefs

Theorem extcall_call_intervals[local]:
  (if ret_type = NoneT /\ ~skip then compile_extcodesize_check addr
   else comp_return ()) sp = ((),s1) /\
  emit_op opc ops s1 = (success,s2) /\
  fresh_label "extcall_fail" s2 = (fail_lbl,s3) /\
  fresh_label "extcall_cont" s3 = (cont_lbl,s4) /\
  emit_inst JNZ [success;Label cont_lbl;Label fail_lbl] [] s4 = ((),s5) /\
  new_block fail_lbl s5 = (old_lbl,s6) /\
  emit_op RETURNDATASIZE [] s6 = (rds,s7) /\
  compile_alloc_buffer 0 s7 = (fail_buf,s8) /\
  emit_void RETURNDATACOPY [fail_buf.buf_operand;Lit 0w;rds] s8 = ((),s9) /\
  emit_inst REVERT [fail_buf.buf_operand;rds] [] s9 = ((),s10) /\
  new_block cont_lbl s10 = (u,sr) /\ fn_has_code sp sr func ==>
  fn_has_code sp s1 func /\ fn_has_code s1 s2 func /\
  fn_has_code s4 s5 func /\ fn_has_code s6 s10 func /\
  s4.cs_current_bb = s2.cs_current_bb /\ s4.cs_current_insts = s2.cs_current_insts /\
  s1.cs_next_var <= sr.cs_next_var /\ s1.cs_next_id <= sr.cs_next_id
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cs_extends sp s1` by
    (Cases_on `ret_type = NoneT /\ ~skip` >> gvs[comp_return_def] >>
     TRY (simp[cs_extends_refl] >> NO_TAC) >>
     `ci_mono sp (SND (compile_extcodesize_check addr sp))` by
       (rewrite_tac[compile_extcodesize_check_def] >>
        irule ci_mono_bind >> simp[ci_mono_emit_op,ci_mono_emit_void]) >>
     pop_assum mp_tac >> simp[ci_mono_def]) >>
  `ci_mono s1 s2` by (qspecl_then [`opc`,`ops`,`s1`] mp_tac ci_mono_emit_op >> simp[]) >>
  `ci_mono s2 s3 /\ ci_mono s3 s4` by
    (conj_tac >- (qspecl_then [`"extcall_fail"`,`s2`] mp_tac ci_mono_fresh_label >> simp[]) >>
     qspecl_then [`"extcall_cont"`,`s3`] mp_tac ci_mono_fresh_label >> simp[]) >>
  `ci_mono s4 s5` by
    (qspecl_then [`JNZ`,`[success;Label cont_lbl;Label fail_lbl]`,`[]`,`s4`] mp_tac ci_mono_emit_inst >> simp[]) >>
  `ci_mono s5 s6` by (qspecl_then [`fail_lbl`,`s5`] mp_tac ci_mono_new_block >> simp[]) >>
  `ci_mono s6 s7` by (qspecl_then [`RETURNDATASIZE`,`[]`,`s6`] mp_tac ci_mono_emit_op >> simp[]) >>
  `ci_mono s7 s8` by (qspecl_then [`0`,`s7`] mp_tac ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono s8 s9` by
    (qspecl_then [`RETURNDATACOPY`,`[fail_buf.buf_operand;Lit 0w;rds]`,`s8`] mp_tac ci_mono_emit_void >> simp[]) >>
  `ci_mono s9 s10` by
    (qspecl_then [`REVERT`,`[fail_buf.buf_operand;rds]`,`[]`,`s9`] mp_tac ci_mono_emit_inst >> simp[]) >>
  `ci_mono s10 sr` by (qspecl_then [`cont_lbl`,`s10`] mp_tac ci_mono_new_block >> simp[]) >>
  `ci_mono s6 s10` by (irule ci_mono_trans >> qexists_tac `s7` >> simp[] >>
    irule ci_mono_trans >> qexists_tac `s8` >> simp[] >> metis_tac[ci_mono_trans]) >>
  `ci_mono s6 sr /\ ci_mono s5 sr /\ ci_mono s4 sr /\ ci_mono s3 sr /\
   ci_mono s2 sr /\ ci_mono s1 sr` by
    (map_every (fn k => conj_asm1_tac >- (irule ci_mono_trans >> qexists_tac k >> simp[]))
      [`s10`,`s6`,`s5`,`s4`,`s3`] >>
     irule ci_mono_trans >> qexists_tac `s2` >> simp[]) >>
  `ci_mono s1 s4 /\ ci_mono s1 s6` by
    (conj_asm1_tac
     >- (irule ci_mono_trans >> qexists_tac `s2` >> simp[] >> metis_tac[ci_mono_trans]) >>
     irule ci_mono_trans >> qexists_tac `s4` >> simp[] >> metis_tac[ci_mono_trans]) >>
  imp_res_tac fresh_label_props >> fs[ci_mono_def] >>
  `cs_extends sp s4 /\ cs_extends sp s6` by metis_tac[cs_extends_trans] >>
  rpt conj_tac >> irule fn_has_code_mid >> simp[cs_extends_refl] >>
  qexistsl_tac [`sr`,`sp`] >> simp[cs_extends_refl]
QED

(* Split the call suffix without unfolding the individual code emitters. *)
Theorem extcall_call_layout:
  !ret_type skip addr_op is_static gas_op call_offset call_len buf_op ret_len
   value_op sp u sr.
  comp_ignore_bind
    (if ret_type = NoneT /\ ~skip then compile_extcodesize_check addr_op
     else comp_return ())
    (comp_bind
      (if is_static then emit_op STATICCALL
         [gas_op; addr_op; call_offset; call_len; buf_op; ret_len]
       else emit_op CALL
         [gas_op; addr_op; value_op; call_offset; call_len; buf_op; ret_len])
      (\success. comp_bind (fresh_label "extcall_fail") (\fail_lbl.
       comp_bind (fresh_label "extcall_cont") (\cont_lbl.
       comp_ignore_bind
         (emit_inst JNZ [success; Label cont_lbl; Label fail_lbl] [])
       (comp_ignore_bind (new_block fail_lbl)
       (comp_bind (emit_op RETURNDATASIZE []) (\rds.
       comp_bind (compile_alloc_buffer 0) (\fail_buf.
       comp_ignore_bind
         (emit_void RETURNDATACOPY [fail_buf.buf_operand; Lit 0w; rds])
       (comp_ignore_bind (emit_inst REVERT [fail_buf.buf_operand; rds] [])
         (new_block cont_lbl)))))))))) sp = (u,sr) ==>
  ?s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 success fail_lbl cont_lbl rds fail_buf old_lbl.
    (if ret_type = NoneT /\ ~skip then compile_extcodesize_check addr_op
     else comp_return ()) sp = ((),s1) /\
    emit_op (if is_static then STATICCALL else CALL)
      (if is_static then
         [gas_op; addr_op; call_offset; call_len; buf_op; ret_len]
       else
         [gas_op; addr_op; value_op; call_offset; call_len; buf_op; ret_len])
      s1 = (success,s2) /\
    fresh_label "extcall_fail" s2 = (fail_lbl,s3) /\
    fresh_label "extcall_cont" s3 = (cont_lbl,s4) /\
    emit_inst JNZ [success; Label cont_lbl; Label fail_lbl] [] s4 = ((),s5) /\
    new_block fail_lbl s5 = (old_lbl,s6) /\
    emit_op RETURNDATASIZE [] s6 = (rds,s7) /\
    compile_alloc_buffer 0 s7 = (fail_buf,s8) /\
    emit_void RETURNDATACOPY [fail_buf.buf_operand; Lit 0w; rds] s8 = ((),s9) /\
    emit_inst REVERT [fail_buf.buf_operand; rds] [] s9 = ((),s10) /\
    new_block cont_lbl s10 = (u,sr)
Proof
  rpt gen_tac >>
  pure_rewrite_tac[comp_ignore_bind_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  rpt (pure_once_rewrite_tac[comp_bind_def] >>
       pure_rewrite_tac[LET_THM] >> pairarg_tac >> simp[]) >>
  strip_tac >> gvs[new_block_def] >>
  rename1 `if stat then STATICCALL else CALL` >>
  Cases_on `stat` >> gvs[] >> metis_tac[]
QED

Theorem extcall_fetched_exhausted[local]:
  stmt_state_rel H ctx func cenv cx ee t /\
  exprSimHypsDefs$outcomes_accounts_typed ee.outcomes /\
  accounts_runtime_well_typed ee.accounts /\
  frame_call_value cx value_opt ee = (INL framed,ee) /\
  inst = mk_inst id (if stat then STATICCALL else CALL)
    (if stat then [gas;addr;off;len;buf;Lit (n2w cap)]
     else [gas;addr;value;off;len;buf;Lit (n2w cap)]) [out] /\
  eval_operand gas t = SOME gw /\ eval_operand addr t = SOME aw /\
  eval_operand value t = SOME vw /\
  eval_operand off t = SOME iw /\ eval_operand len t = SOME nw /\
  eval_operand buf t = SOME rw /\
  (!n. value_opt = SOME n ==> w2n vw = n) /\
  (value_opt = NONE ==> vw = 0w) ==>
  ((!tail. eval_ext_call_effects cx target calldata framed source_gas ee.accounts
      (ee with gas_obs := tail) =
      (INR (Error (RuntimeError "take_call_outcome")),ee with gas_obs := tail)) /\
   (!fuel. step_inst fuel ctx inst t = Abort ExHalt_abort (halt_state (set_returndata [] t)))) \/
  (?rq oc consumed. take_call_outcome (OPTION_BIND source_gas dest_NumV)
      target calldata framed ee = (INL (rq,oc),consumed))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ee.outcomes = SOME t.vs_outcomes` by
    (drule stateRelProjTheory.stmt_state_rel_state_rel >> fs[state_rel_def]) >>
  `IS_SOME ee.outcomes` by simp[] >>
  drule_all raw_call_typed_outcome >>
  disch_then (qspecl_then [`target`,`calldata`,`framed`,`OPTION_BIND source_gas dest_NumV`] strip_assume_tac)
  >- (disj1_tac >>
  `t.vs_outcomes = []` by fs[] >>
  conj_tac
  >- (gen_tac >>
      `take_call_outcome (OPTION_BIND source_gas dest_NumV) target calldata
         framed (ee with gas_obs := tail) =
         (INR (Error (RuntimeError "take_call_outcome")),ee with gas_obs := tail)` by
        (irule take_call_outcome_exhausted >> simp[]) >>
      simp[eval_ext_call_effects_def, vyperStateTheory.bind_def,
           vyperStateTheory.return_def]) >>
  `t.vs_call_ctx.cc_static = cx.txn.is_static` by
    (drule stateRelProjTheory.stmt_state_rel_state_rel >>
     disch_then (mp_tac o MATCH_MP stateRelProjTheory.state_rel_call_ctx_rel) >>
     simp[call_ctx_rel_def]) >>
  (* Rewrite only the two call clauses, not the unrelated dispatch cases. *)
  let
    fun is_call_clause th =
      let val opc = rhs (fst (dest_imp (snd (strip_forall (concl th)))))
      in aconv opc ``CALL`` orelse aconv opc ``STATICCALL`` end
    val call_clauses = List.filter is_call_clause (CONJUNCTS step_inst_base_opcode_eqs)
  in
    Cases_on `stat` >>
    gvs(call_clauses @ [mk_inst_def,step_inst_non_invoke,eval_operand_def]) >>
    TRY IF_CASES_TAC >> simp[exec_ext_call_abort_iff]
  end) >>
  disj2_tac >> metis_tac[]
QED

(* An exiting CALL or STATICCALL is a single zero-mark edge. Both early
   exits have this same certificate; neither executes the status branch. *)

Theorem extcall_fetched_abort_path[local]:
  inst = mk_inst id (if stat then STATICCALL else CALL)
    (if stat then [gas;addr;off;len;buf;Lit (n2w cap)]
     else [gas;addr;value;off;len;buf;Lit (n2w cap)]) [out] /\
  eval_operand gas t = SOME gw /\ eval_operand addr t = SOME aw /\
  eval_operand value t = SOME vw /\ eval_operand off t = SOME iw /\
  eval_operand len t = SOME nw /\ eval_operand buf t = SOME rw /\
  (nw <> 0w ==> ?p. off = Var p /\ ptr_covers G tn p t (w2n nw)) /\
  (n2w cap <> (0w:bytes32) ==>
     ?p. buf = Var p /\ ptr_covers G tn p t (w2n (n2w cap:bytes32))) /\
  EVERY (\op. op_taint tn op = {}) inst.inst_operands /\
  (!j. w2n iw <= j /\ j < w2n iw + w2n nw ==> j NOTIN tn.t_mem) /\
  (nw = 0w \/ w2n iw + w2n nw <= t.vs_alloca_next) /\
  (n2w cap = (0w:bytes32) \/ w2n rw + w2n (n2w cap:bytes32) <= t.vs_alloca_next) /\
  allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ ~t.vs_halted /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  (!fuel. step_inst fuel ctx inst t = Abort a u) ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) [] (Abort a u,G,tn)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `access_ok 0 G func inst t` by
    (irule oracleCallStepPtrTheory.call_access_ok_ptr >>
     Cases_on `stat` >> gvs[mk_inst_def, ptr_covers_def, eval_operand_def] >>
     rpt strip_tac >> first_x_assum drule >>
     strip_tac >> gvs[eval_operand_def] >> metis_tac[]) >>
  `access_ok lo G func inst t` by
    (qpat_x_assum `access_ok 0 _ _ _ _` mp_tac >>
     simp[access_ok_def] >> metis_tac[arithmeticTheory.LESS_ADD_NONZERO]) >>
  `taint_ok func tn inst t` by
    (irule oracleCallStepPtrTheory.call_taint_ok_ptr >>
     Cases_on `stat` >>
     gvs[mk_inst_def, source_memory_read_ranges_def, mem_read_ops_def,
         memory_range_of_operands_def, eval_operand_def]) >>
  `ptr_inst_ok D lo 0 ctx func G tn inst t` by simp[ptr_inst_ok_def] >>
  `mem_safe_step 0 ctx inst t` by
    (Cases_on `stat` >> simp[] >>
     simp[Once mem_safe_step_non_invoke] >>
     simp[below_frontier_CALL, below_frontier_STATICCALL, eval_operand_def,
          wordsTheory.w2n_eq_0] >>
     gvs[inst_dload_in_section_def, mk_inst_def, w2n_eq_0]) >>
  irule exit_inst_origin_ptr >> simp[exit_result_def] >>
  Cases_on `stat` >>
  gvs[mk_inst_def, exit_result_def, gas_events_step_def, gas_count_step_def]
QED

(* All errors before a successful take halt at the fetched instruction. *)
Theorem extcall_fetched_select[local]:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr value gas buf off len cap target value_opt calldata has_default
    default_op default_ty default_opt ee t /\
  inst = mk_inst sp.cs_next_id (if stat then STATICCALL else CALL)
    (if stat then [gas;addr;off;len;buf;Lit (n2w cap)]
     else [gas;addr;value;off;len;buf;Lit (n2w cap)]) [out] /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  EVERY (\p. op_taint tn p = {}) [addr;value;gas;buf;off;len] /\
  (!ao az. eval_operand off t = SOME ao /\ eval_operand len t = SOME az ==>
    (az <> 0w ==> (?p. off = Var p /\ ptr_covers G tn p t (w2n az)) /\
                  w2n ao + w2n az <= t.vs_alloca_next) /\
    (!j. w2n ao <= j /\ j < w2n ao + w2n az ==> j NOTIN tn.t_mem)) /\
  (cap <> 0 ==> ?p. buf = Var p /\ ptr_covers G tn p t cap) /\
  allocas_from lo t ==>
  ((?err. (!tail. bind (frame_call_value cx value_opt)
      (\framed. eval_ext_call_effects cx target calldata framed source_gas ee.accounts)
      (ee with gas_obs := tail) =
      (INR (Error (RuntimeError err)),ee with gas_obs := tail)) /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) []
      (Abort ExHalt_abort (halt_state (set_returndata [] t)),G,tn))) \/
  (?framed rq oc consumed. frame_call_value cx value_opt ee = (INL framed,ee) /\
    take_call_outcome (OPTION_BIND source_gas dest_NumV) target calldata framed ee =
      (INL (rq,oc),consumed))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_assum `extcall_request_ready`
    (strip_assume_tac o REWRITE_RULE [extcall_request_ready_def]) >>
  `stmt_state_rel H ctx func cenv cx ee t` by metis_tac[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx ee t`
       (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  `?gw. eval_operand gas t = SOME gw` by (Cases_on `eval_operand gas t` >> gs[]) >>
  `w2n (n2w cap : bytes32) = cap` by (simp[w2n_n2w] >> decide_tac) >>
  `w2n ro + cap <= t.vs_alloca_next` by
    (irule abi_caller_allocation_end >> conj_tac
     >- (drule stateRelProjTheory.stmt_state_rel_local_ptrs_alloca >> simp[]) >>
     qexistsl_tac [`buf_size`,`live`,`w2n ro`] >> simp[]) >>
  qpat_assum `!ao az. _ ==> _` drule_all >> strip_tac >>
  `EVERY (\p. op_taint tn p = {}) inst.inst_operands` by
    (Cases_on `stat` >> fs[mk_inst_def,op_taint_def]) >>
  `(!fuel. step_inst fuel ctx inst t = Abort ExHalt_abort (halt_state (set_returndata [] t))) ==>
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) []
      (Abort ExHalt_abort (halt_state (set_returndata [] t)),G,tn)` by
    (rpt strip_tac >>
     `az <> 0w ==> ?p. off = Var p /\ ptr_covers G tn p t (w2n az)` by metis_tac[] >>
     Q.SUBGOAL_THEN `az = 0w \/ w2n ao + w2n az <= t.vs_alloca_next` ASSUME_TAC
     >- (Cases_on `az = 0w` >> fs[]) >>
     `n2w cap <> (0w:bytes32) ==>
        ?p. buf = Var p /\ ptr_covers G tn p t (w2n (n2w cap:bytes32))` by
       (Cases_on `cap = 0` >- asm_simp_tac bool_ss [] >>
        strip_tac >>
        qpat_assum `w2n (n2w cap:bytes32) = cap` SUBST1_TAC >>
        qpat_assum `cap <> 0 ==> ?p. buf = Var p /\ ptr_covers G tn p t cap`
          (fn covers => qpat_assum `cap <> 0` (ACCEPT_TAC o MATCH_MP covers))) >>
     Q.SUBGOAL_THEN
       `n2w cap = (0w:bytes32) \/ w2n ro + w2n (n2w cap:bytes32) <= t.vs_alloca_next` ASSUME_TAC
     >- simp[Excl "w2n_n2w"] >>
     drule_all extcall_fetched_abort_path >> simp[]) >>
  reverse (Cases_on `cx.txn.is_static /\ value_opt <> NONE /\ value_opt <> SOME 0`)
  >- (`?framed. frame_call_value cx value_opt ee = (INL framed,ee)` by
        (Cases_on `cx.txn.is_static` >> fs[frame_call_value_def,vyperStateTheory.bind_def,
          vyperStateTheory.ignore_bind_def,vyperStateTheory.check_def,vyperStateTheory.assert_def,
          vyperStateTheory.return_def]) >>
      `!n. value_opt = SOME n ==> w2n vw = n` by (Cases_on `value_opt` >> gs[]) >>
      `(value_opt = NONE ==> vw = 0w)` by (Cases_on `value_opt` >> gs[w2n_eq_0]) >>
      drule_all extcall_fetched_exhausted >>
      disch_then (qspecl_then [`target`,`source_gas`,`calldata`] strip_assume_tac)
      >- (disj1_tac >> qexists_tac `"take_call_outcome"` >> simp[] >> gen_tac >>
          Cases_on `cx.txn.is_static` >>
          gvs[frame_call_value_def,vyperStateTheory.bind_def,vyperStateTheory.ignore_bind_def,
              vyperStateTheory.check_def,vyperStateTheory.assert_def,vyperStateTheory.return_def]) >>
      disj2_tac >> metis_tac[]) >>
  `value_opt = SOME (w2n vw) /\ vw <> 0w /\ ~stat` by
    (Cases_on `value_opt` >> gs[] >> metis_tac[w2n_eq_0]) >>
  `state_rel H func cenv cx ee t` by metis_tac[stateRelProjTheory.stmt_state_rel_state_rel] >>
  `inst.inst_opcode = CALL /\ inst.inst_operands = [gas;addr;value;off;len;buf;Lit (n2w cap)] /\
   eval_operand (Lit (n2w cap)) t = SOME (n2w cap)` by simp[mk_inst_def,eval_operand_def] >>
  `cx.txn.is_static` by fs[] >>
  drule_all call_static_value_abort >> strip_tac >>
  disj1_tac >> qexists_tac `"write in static context"` >> conj_tac
  >- (gen_tac >>
      `~(value_opt = NONE \/ value_opt = SOME 0)` by
        (qpat_assum `cx.txn.is_static /\ _ /\ _` mp_tac >> simp[NoAsms]) >>
      `frame_call_value cx value_opt (ee with gas_obs := tail) =
        (INR (Error (RuntimeError "write in static context")),ee with gas_obs := tail)` by
        (qpat_assum `cx.txn.is_static` (fn hs =>
         qpat_assum `~(value_opt = NONE \/ value_opt = SOME 0)` (fn hv =>
           simp[NoAsms,hs,hv,frame_call_value_def,vyperStateTheory.bind_def,
             vyperStateTheory.ignore_bind_def,vyperStateTheory.check_def,
             vyperStateTheory.assert_def,vyperStateTheory.raise_def]))) >>
      qpat_assum `frame_call_value _ _ (ee with gas_obs := tail) = _`
        (fn th => simp[NoAsms,vyperStateTheory.bind_def,th])) >>
  qpat_assum `(!fuel. step_inst fuel _ _ _ = _) ==> _` irule >>
  simp[step_inst_non_invoke]
QED

(* The code check changes neither saved operand observations nor the
   allocation frontier. Reuse the precheck's pointwise guarantees. *)
Theorem extcall_precheck_dispatch_operands[local]:
  EVERY (safe_operand sp) [addr;value;gas;buf;off;len;default_op] /\
  (!op. safe_operand sp op ==> eval_operand op t = eval_operand op s /\
    op_taint tn1 op = op_taint tn op /\
    (!x. op = Var x ==> FLOOKUP G1 x = FLOOKUP G x)) /\
  (!ty v op. safe_operand sp op /\ ptr_mem_ok cx ty v op G tn s ==>
    ptr_mem_ok cx ty v op G1 tn1 t) /\
  t.vs_alloca_next = s.vs_alloca_next /\ tn1.t_mem = tn.t_mem /\
  eval_operand gas s = SOME gw /\
  EVERY (\p. op_taint tn p = {}) [addr;value;gas;buf;off;len;default_op] /\
  (!ao az. eval_operand off s = SOME ao /\ eval_operand len s = SOME az ==>
    (az <> 0w ==> (?p. off = Var p /\ ptr_covers G tn p s (w2n az)) /\
                  w2n ao + w2n az <= s.vs_alloca_next) /\
    (!j. w2n ao <= j /\ j < w2n ao + w2n az ==> j NOTIN tn.t_mem)) /\
  (cap <> 0 ==> ?p. buf = Var p /\ ptr_covers G tn p s cap) /\
  (!dv. default_opt = SOME dv /\ ~is_word_type default_ty ==>
    ptr_mem_ok cx default_ty dv default_op G tn s /\
    (type_memory_bytes cenv default_ty <> 0 ==>
      (?p. default_op = Var p /\ ptr_covers G tn p s (type_memory_bytes cenv default_ty)) /\
      (!w. eval_operand default_op s = SOME w ==>
          w2n w + type_memory_bytes cenv default_ty <= s.vs_alloca_next))) ==>
  eval_operand gas t = SOME gw /\
  EVERY (\p. op_taint tn1 p = {}) [addr;value;gas;buf;off;len;default_op] /\
  (!ao az. eval_operand off t = SOME ao /\ eval_operand len t = SOME az ==>
    (az <> 0w ==> (?p. off = Var p /\ ptr_covers G1 tn1 p t (w2n az)) /\
                  w2n ao + w2n az <= t.vs_alloca_next) /\
    (!j. w2n ao <= j /\ j < w2n ao + w2n az ==> j NOTIN tn1.t_mem)) /\
  (cap <> 0 ==> ?p. buf = Var p /\ ptr_covers G1 tn1 p t cap) /\
  (!dv. default_opt = SOME dv /\ ~is_word_type default_ty ==>
    ptr_mem_ok cx default_ty dv default_op G1 tn1 t /\
    (type_memory_bytes cenv default_ty <> 0 ==>
      (?p. default_op = Var p /\ ptr_covers G1 tn1 p t (type_memory_bytes cenv default_ty)) /\
      (!w. eval_operand default_op t = SOME w ==>
          w2n w + type_memory_bytes cenv default_ty <= t.vs_alloca_next)))
Proof
  strip_tac >> fs[EVERY_DEF] >>
  `!p n. safe_operand sp (Var p) /\ ptr_covers G tn p s n ==>
      ptr_covers G1 tn1 p t n` by
    (rpt strip_tac >>
     qpat_assum `!op. safe_operand _ op ==> _` drule >>
     strip_tac >> gvs[eval_operand_def,ptr_covers_def]) >>
  `eval_operand off t = eval_operand off s /\ eval_operand len t = eval_operand len s /\
   eval_operand default_op t = eval_operand default_op s` by metis_tac[] >>
  simp[] >> rpt conj_tac
  >- (rpt strip_tac >> qpat_assum `!ao az. _ ==> _` drule_all >>
      strip_tac >> metis_tac[])
  >- (strip_tac >> qpat_assum `cap <> 0 ==> _` drule >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!dv. default_opt = SOME dv /\ _ ==> _` drule_all >>
  strip_tac >> metis_tac[]
QED

(* The two fresh labels are allocated between the call and the status
   branch. For dispatch, move only that counter before the call. *)
Theorem extcall_dispatch_label_cursor[local]:
  emit_op opc ops s1 = (success,s2) /\
  fresh_label "extcall_fail" s2 = (fail_lbl,s3) /\
  fresh_label "extcall_cont" s3 = (cont_lbl,s4) /\
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 s1 stat
    addr value gas buf off len cap target value_opt calldata has_default
    default_op default_ty default_opt ee t ==>
  emit_op opc ops (s1 with cs_next_label := s4.cs_next_label) = (success,s4) /\
    (s1 with cs_next_label := s4.cs_next_label).cs_next_var = s1.cs_next_var /\
    (s1 with cs_next_label := s4.cs_next_label).cs_next_id = s1.cs_next_id /\
    (!out. not_fresh_at (s1 with cs_next_label := s4.cs_next_label) out <=> not_fresh_at s1 out) /\
    extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 (s1 with cs_next_label :=
      s4.cs_next_label) stat
      addr value gas buf off len cap target value_opt calldata has_default
      default_op default_ty default_opt ee t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[not_fresh_at_def] >> conj_tac
  >- (qpat_x_assum `extcall_request_ready _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
      gvs[emitHelperTheory.emit_op_def,comp_ignore_bind_def,comp_bind_def,
          comp_return_def,emit_def,fresh_id_def,fresh_var_def,fresh_label_def,
          compile_state_component_equality]) >>
  qhdtm_x_assum `extcall_request_ready` mp_tac >>
  pure_rewrite_tac[extcall_request_ready_def,local_ptrs_reserved_def,
                   exprSafeOperandTheory.safe_operand_def,not_fresh_at_def,
                   EVERY_DEF,compile_state_accfupds] >>
  metis_tac[]
QED

(* A call suffix has no explicit gas readings. Choose its endpoint before
   testing the domain of the final trace. *)
Theorem extcall_call_landing[local]:
  ~s.vs_halted /\
  (!tail. source (ee with gas_obs := tail) = (res,ef with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H ef.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (r,Gf,tf) /\
    ((?z. r = OK z /\ Q H res (ef with gas_obs := []) Gf tf z) \/
     (exit_result r /\ expr_exit res r))) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0 source
    (ee,s,G,tn) Q (\H res es gt r. expr_exit res r)
Proof
  strip_tac >> Cases_on `storage_trace_domain cx st0 ef.storage_trace`
  >- (irule gas_outcome_full_intro >>
      qexistsl_tac [`Gf`,`ef`,`[]`,`r`,`res`,`tf`] >> simp[]) >>
  irule gas_outcome_full_bad_nil >> simp[]
QED

(* Replay the source precheck, and then reuse the instruction's source
   equation with the same tail. *)
Theorem extcall_call_source_replay[local]:
  ext_call_precheck_ok skip ret_type target ee.accounts ==>
  (do accounts <- get_accounts;
      check (ext_call_precheck_ok skip ret_type target accounts)
        "ExtCall target has no code";
      framed <- frame_call_value cx value_opt;
      rd <- eval_ext_call_effects cx target calldata framed source_gas accounts;
      k rd
   od) (ee with gas_obs := tail) =
  bind (bind (frame_call_value cx value_opt)
          (\framed. eval_ext_call_effects cx target calldata framed source_gas ee.accounts)) k
    (ee with gas_obs := tail)
Proof
  strip_tac >>
  simp[get_accounts_def, vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.check_def, vyperStateTheory.assert_def, vyperStateTheory.return_def] >>
  Cases_on `frame_call_value cx value_opt (ee with gas_obs := tail)` >> gvs[] >>
  rename1 `_ = (fr,es)` >> Cases_on `fr` >> simp[]
QED

Theorem extcall_frame_value_replay[local]:
  frame_call_value cx value_opt ee = (INL framed,ee) ==>
  !tail. frame_call_value cx value_opt (ee with gas_obs := tail) =
    (INL framed,ee with gas_obs := tail)
Proof
  disch_then (strip_assume_tac o MATCH_MP frame_call_value_success) >> gen_tac >>
  Cases_on `cx.txn.is_static` >>
  gvs[frame_call_value_def, vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
      vyperStateTheory.check_def, vyperStateTheory.assert_def, vyperStateTheory.return_def]
QED

Theorem extcall_call_stage_full:
  comp_ignore_bind
    (if ret_type = NoneT /\ ~skip then compile_extcodesize_check addr
     else comp_return ())
    (comp_bind
      (if stat then emit_op STATICCALL [gas;addr;off;len;buf;Lit (n2w cap)]
       else emit_op CALL [gas;addr;value;off;len;buf;Lit (n2w cap)])
      (\success. comp_bind (fresh_label "extcall_fail") (\fail_lbl.
       comp_bind (fresh_label "extcall_cont") (\cont_lbl.
       comp_ignore_bind (emit_inst JNZ [success;Label cont_lbl;Label fail_lbl] [])
       (comp_ignore_bind (new_block fail_lbl)
       (comp_bind (emit_op RETURNDATASIZE []) (\rds.
       comp_bind (compile_alloc_buffer 0) (\fail_buf.
       comp_ignore_bind
         (emit_void RETURNDATACOPY [fail_buf.buf_operand;Lit 0w;rds])
       (comp_ignore_bind (emit_inst REVERT [fail_buf.buf_operand;rds] [])
         (new_block cont_lbl)))))))))) sp = (u,sr) /\
  fn_has_code sp sr func /\ fn_inst_ids_distinct func /\
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr value gas buf off len cap target value_opt calldata has_default
    default_op default_ty default_opt ee s /\
  (IS_SOME default_opt /\ ~is_word_type default_ty ==>
    ?w aid tv. eval_operand default_op s = SOME w /\
      evaluate_type (get_tenv cx) default_ty = SOME tv /\
      FLOOKUP s.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
      aid < sp.cs_next_id) /\
  alloca_history func s /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  (!gw g. eval_operand gas s = SOME gw /\ OPTION_BIND source_gas dest_NumV = SOME g ==>
          g = w2n gw) /\
  EVERY (\p. op_taint tn p = {}) [addr;value;gas;buf;off;len;default_op] /\
  (!ao az. eval_operand off s = SOME ao /\ eval_operand len s = SOME az ==>
    (az <> 0w ==> (?p. off = Var p /\ ptr_covers G tn p s (w2n az)) /\
                  w2n ao + w2n az <= s.vs_alloca_next) /\
    (!j. w2n ao <= j /\ j < w2n ao + w2n az ==> j NOTIN tn.t_mem)) /\
  (cap <> 0 ==> ?p. buf = Var p /\ ptr_covers G tn p s cap) /\
  (!dv. default_opt = SOME dv /\ ~is_word_type default_ty ==>
    ptr_mem_ok cx default_ty dv default_op G tn s /\
    (type_memory_bytes cenv default_ty <> 0 ==>
      (?p. default_op = Var p /\ ptr_covers G tn p s (type_memory_bytes cenv default_ty)) /\
      (!w. eval_operand default_op s = SOME w ==>
          w2n w + type_memory_bytes cenv default_ty <= s.vs_alloca_next))) /\
  (!rd ee' z Gu tu.
    extcall_returned st0 ctx func cenv cx ret_type es sa s0 sr addr buf cap target
      has_default default_op default_ty default_opt rd ee' z /\
    (IS_SOME default_opt /\ ~is_word_type default_ty ==>
      ?w aid tv. eval_operand default_op z = SOME w /\
        evaluate_type (get_tenv cx) default_ty = SOME tv /\
        FLOOKUP z.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
        aid < sr.cs_next_id) /\
    alloca_history func z /\ allocas_from lo z /\
    lo <= z.vs_alloca_next /\ s0.vs_alloca_next <= z.vs_alloca_next /\
    (!H. valid_horizon cx st0 H ee'.storage_trace ==>
       ghost_inv_at (DF H) lo d cenv cx ee' Gu tu z) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tu /\
    EVERY (\p. op_taint tu p = {}) [addr;buf;default_op] /\
    (!dv. default_opt = SOME dv /\ ~is_word_type default_ty ==>
      ptr_mem_ok cx default_ty dv default_op Gu tu z /\
      (type_memory_bytes cenv default_ty <> 0 ==>
        ?p b sz w. default_op = Var p /\ FLOOKUP Gu p = SOME (b,sz) /\
          eval_operand default_op z = SOME w /\ b <= w2n w /\
          w2n w + type_memory_bytes cenv default_ty <= b + sz /\
          w2n w + type_memory_bytes cenv default_ty <= z.vs_alloca_next)) /\
    (cap <> 0 ==>
      ?p b sz w. buf = Var p /\ FLOOKUP Gu p = SOME (b,sz) /\
        eval_operand buf z = SOME w /\ b <= w2n w /\ w2n w + cap <= b + sz /\
        (!i. w2n w <= i /\ i < w2n w + MIN cap (LENGTH rd) ==> i NOTIN tu.t_mem)) ==>
    ?res r Gf tf.
      (!tail. k rd (ee' with gas_obs := tail) = (res,ee' with gas_obs := tail)) /\
      (!H. valid_horizon cx st0 H ee'.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (z,Gu,tu) [] (r,Gf,tf) /\
        ((?t. r = OK t /\ Q H res (ee' with gas_obs := []) Gf tf t) \/
         (exit_result r /\ expr_exit res r)))) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (do accounts <- get_accounts;
        check (ext_call_precheck_ok skip ret_type target accounts)
          "ExtCall target has no code";
        framed <- frame_call_value cx value_opt;
        rd <- eval_ext_call_effects cx target calldata framed source_gas accounts;
        k rd
     od) (ee,s,G,tn) Q (\H res es gt r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule extcall_call_layout >> strip_tac >>
  drule_all extcall_call_intervals >> strip_tac >>
  `~s.vs_halted /\ op_taint tn addr = {} /\
   EVERY (safe_operand sp) [addr;value;gas;buf;off;len;default_op] /\
   ?gw. eval_operand gas s = SOME gw` by
    (qhdtm_assum `extcall_request_ready`
       (strip_assume_tac o REWRITE_RULE [extcall_request_ready_def]) >>
     fs[EVERY_DEF] >> Cases_on `eval_operand gas s` >> gs[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> stor_taint_ok_at (DF H) tn s` by
    (rpt strip_tac >> qpat_assum `!H. _ ==> ghost_inv_at _ _ _ _ _ _ _ _ _`
       (drule_then (ACCEPT_TAC o cj 4 o REWRITE_RULE [ghost_inv_at_def]))) >>
  drule_all (Q.INST [`explicit` |-> `explicit`, `PG` |-> `PG`, `DF` |-> `DF`]
                    extcall_precheck_to_call) >>
  reverse (Cases_on `ext_call_precheck_ok skip ret_type target ee.accounts`)
  >- (disch_then (qspecl_then [`explicit`,`d`,`PG`] mp_tac) >>
      ASM_SIMP_TAC bool_ss [] >> strip_tac >>
      irule extcall_call_landing >> reverse conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`G1`,`ee`,`r`,`INR (Error (RuntimeError "ExtCall target has no code"))`,`tn1`] >>
      simp[get_accounts_def, vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
           vyperStateTheory.check_def, vyperStateTheory.assert_def, vyperStateTheory.raise_def,
           vyperStateTheory.return_def]) >>
  disch_then (qspecl_then [`explicit`,`d`,`PG`] mp_tac) >>
  ASM_SIMP_TAC bool_ss [] >> strip_tac >>
  qpat_x_assum `r = OK t` SUBST_ALL_TAC >>
  drule_all extcall_precheck_dispatch_operands >> strip_tac >>
  `sp.cs_next_id <= s1.cs_next_id` by
    (qpat_x_assum `(if ret_type = NoneT /\ ~skip then _ else _) sp = ((),s1)` mp_tac >>
     Cases_on `ret_type = NoneT /\ ~skip` >> simp[comp_return_def]
     >- (strip_tac >>
         `ci_mono sp (SND (compile_extcodesize_check addr sp))` by
           (rewrite_tac[compile_extcodesize_check_def] >>
            irule ci_mono_bind >> simp[ci_mono_emit_op,ci_mono_emit_void]) >>
         pop_assum mp_tac >> simp[ci_mono_def]) >>
     strip_tac >> simp[]) >>
  `IS_SOME default_opt /\ ~is_word_type default_ty ==>
    ?w aid tv. eval_operand default_op t = SOME w /\
      evaluate_type (get_tenv cx) default_ty = SOME tv /\
      FLOOKUP t.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
      aid < s1.cs_next_id` by
    (strip_tac >>
     qpat_assum `IS_SOME default_opt /\ ~is_word_type default_ty ==> _`
       (drule_all_then (qx_choosel_then [`w`,`aid`,`tv`] strip_assume_tac)) >>
     `safe_operand sp default_op` by
       (qpat_assum `EVERY (safe_operand sp) [addr;value;gas;buf;off;len;default_op]`
          (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
        disch_then (qspec_then `default_op` mp_tac) >>
        simp[NoAsms]) >>
     `eval_operand default_op t = eval_operand default_op s` by
       (qpat_assum `!p. safe_operand sp p ==> eval_operand p t = _ /\ _`
          (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
     qexistsl_tac [`w`,`aid`,`tv`] >> simp[] >> decide_tac) >>
  `EVERY (\p. op_taint tn1 p = {}) [addr;value;gas;buf;off;len]` by fs[EVERY_DEF] >>
  qabbrev_tac `inst = mk_inst s1.cs_next_id (if stat then STATICCALL else CALL)
    (if stat then [gas;addr;off;len;buf;Lit (n2w cap)]
     else [gas;addr;value;off;len;buf;Lit (n2w cap)]) [out]` >>
  qpat_assum `Abbrev (inst = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all (Q.INST [`source_gas` |-> `source_gas`, `explicit` |-> `explicit`,
                    `PG` |-> `PG`] extcall_fetched_select) >>
  disch_then (qspecl_then [`source_gas`,`explicit`,`PG`] strip_assume_tac)
  >- (irule extcall_call_landing >> reverse conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`G1`,`ee`,`Abort ExHalt_abort (halt_state (set_returndata [] t))`,
        `INR (Error (RuntimeError err))`,`tn1`] >>
      conj_tac
      >- (simp[extcall_call_source_replay] >> simp[Once vyperStateTheory.bind_def]) >>
      simp[exit_result_def,expr_exit_def] >> rpt strip_tac >>
      qpat_assum `!H. _ ==> gas_origin_ptr_path _ (s,G,tn) _ _` (drule_then assume_tac) >>
      irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
      goal_assum (drule_at Any) >> simp[]) >>
  drule_all extcall_dispatch_label_cursor >>
  SIMP_TAC bool_ss [LET_THM] >> strip_tac >>
  qabbrev_tac `p = s1 with cs_next_label := s4.cs_next_label` >>
  qpat_x_assum `success = Var out` SUBST_ALL_TAC >>
  `~not_fresh_at p out /\ p.cs_next_var <= sr.cs_next_var /\
   p.cs_next_id <= sr.cs_next_id` by simp[] >>
  `inst = mk_inst p.cs_next_id (if stat then STATICCALL else CALL)
    (if stat then [gas;addr;off;len;buf;Lit (n2w cap)]
     else [gas;addr;value;off;len;buf;Lit (n2w cap)]) [out]` by
    (qpat_assum `p.cs_next_id = _` (pure_rewrite_tac o single) >> first_assum ACCEPT_TAC) >>
  `s4.cs_current_bb = t.vs_current_bb /\ LENGTH s4.cs_current_insts = SUC t.vs_inst_idx`
    by metis_tac[] >>
  `IS_SOME default_opt /\ ~is_word_type default_ty ==>
    ?w aid tv. eval_operand default_op t = SOME w /\
      evaluate_type (get_tenv cx) default_ty = SOME tv /\
      FLOOKUP t.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
      aid < p.cs_next_id` by
    (qpat_assum `p.cs_next_id = s1.cs_next_id`
       (pure_rewrite_tac o single) >>
     first_assum ACCEPT_TAC) >>
  `s0.vs_alloca_next <= t.vs_alloca_next` by simp[] >>
  `!g. OPTION_BIND source_gas dest_NumV = SOME g ==> g = w2n gw` by
    (rpt strip_tac >> qpat_assum `!gw g. _ ==> _` drule_all >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 t`
    by (qpat_assum `_ ==> !H. _ ==> ghost_inv_at _ _ _ _ _ _ G1 tn1 t` mp_tac >> simp[]) >>
  drule_all extcall_dispatch_selected >>
  reverse (Cases_on `oc.co_success`)
  >- (disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
      ASM_SIMP_TAC bool_ss [] >> strip_tac >>
      irule extcall_call_landing >> reverse conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`Gf`,`consumed`,`Abort Revert_abort f`,
                    `INR (Error (RevertData oc.co_returnData))`,`tf`] >> conj_tac
      >- (drule extcall_frame_value_replay >> strip_tac >>
          gen_tac >> simp[extcall_call_source_replay] >>
          simp[vyperStateTheory.bind_def]) >>
      simp[exit_result_def,expr_exit_def] >> rpt strip_tac >>
      qpat_assum `!H. _ ==> _ /\ gas_origin_ptr_path _ (t,G1,tn1) _ _`
        (drule_then strip_assume_tac) >>
      qpat_assum `!H. _ ==> gas_origin_ptr_path _ (s,G,tn) _ _`
        (drule_then assume_tac) >>
      irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
      goal_assum (drule_at Any) >> simp[]) >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
  ASM_SIMP_TAC bool_ss [] >> strip_tac >>
  qpat_assum `!H. _ ==> _ /\ gas_origin_ptr_path _ (t,G1,tn1) _ _ /\ _`
    (assume_tac o cj 3) >>
  qpat_assum `!rd es z G tn. _ ==> ?res r Gf tf. _` drule_all >> strip_tac >>
  irule extcall_call_landing >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`Gf`,`ee'`,`r`,`res`,`tf`] >> conj_tac
  >- (drule extcall_frame_value_replay >> strip_tac >>
      gen_tac >> simp[extcall_call_source_replay] >>
      simp[vyperStateTheory.bind_def]) >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!H. _ ==> _ /\ gas_origin_ptr_path _ (t,G1,tn1) _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. _ ==> gas_origin_ptr_path _ (s,G,tn) _ _`
    (drule_then assume_tac) >>
  qpat_assum `!H. _ ==> gas_origin_ptr_path _ (z,Gu,tu) _ _ /\ _`
    (drule_then (CONJUNCTS_THEN assume_tac)) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
  goal_assum (drule_at Any) >>
  irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
  goal_assum (drule_at Any) >> first_assum ACCEPT_TAC
QED
