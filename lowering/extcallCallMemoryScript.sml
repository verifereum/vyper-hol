(* Counted oracle-call execution for typed external calls. *)
Theory extcallCallMemory
Ancestors
  rawCallOracleMemory rawCallFinishPathMemory exprSimExtCallCase exprSimMemDefs
  exprSimHash exprSimProps exprSafeOperand exprLoweringProps loweringPosts
  loweringStateRelDefs fragGasPathMem fragGasSeqMem allocaHistory
  exprLowering compileEnv emitHelper emitHelperProps
  vyperInterpreter vyperState vyperCallOutcome vyperCallOutcomeProps
  extCallOracle venomExecSemantics venomState venomInst words list rich_list

Theorem extcall_effects_outcome:
  IS_SOME es.outcomes /\
  take_call_outcome target data vo es = (INL (rq,oc),es1) ==>
  eval_ext_call_effects cx target data vo gas accounts es =
    (if oc.co_success then
       (INL oc.co_returnData,SND (adopt_call_outcome rq oc es1))
     else (INR (Error (RevertData oc.co_returnData)),es1))
Proof
  Cases_on `es.outcomes` >> simp[] >> strip_tac >>
  simp[eval_ext_call_effects_def, bind_def, ignore_bind_def,
       vyperStateTheory.return_def, raise_def] >>
  Cases_on `oc.co_success` >>
  simp[adopt_call_outcome_equation, vyperStateTheory.return_def, raise_def]
QED

Theorem extcall_effects_outcome_tail:
  IS_SOME es.outcomes /\
  take_call_outcome target data vo es = (INL (rq,oc),es1) ==>
  !tail. eval_ext_call_effects cx target data vo gas accounts
    (es with gas_obs := tail) =
    (if oc.co_success then
       (INL oc.co_returnData,SND (adopt_call_outcome rq oc es1) with gas_obs := tail)
     else (INR (Error (RevertData oc.co_returnData)),es1 with gas_obs := tail))
Proof
  strip_tac >> gen_tac >>
  `take_call_outcome target data vo (es with gas_obs := tail) =
     (INL (rq,oc),es1 with gas_obs := tail)` by
    (qpat_x_assum `take_call_outcome _ _ _ es = _` mp_tac >>
     Cases_on `es.outcomes` >>
     simp[take_call_outcome_def, take_request_outcome_def, call_outcome_request_def] >>
     pairarg_tac >> simp[] >> IF_CASES_TAC >> gvs[] >> rpt strip_tac >> gvs[]) >>
  mp_tac (Q.INST [`es` |-> `es with gas_obs := tail`,
    `es1` |-> `es1 with gas_obs := tail`] extcall_effects_outcome) >>
  simp[adopt_call_outcome_equation] >>
  Cases_on `rq.cr_static` >> simp[]
QED

Theorem extcall_default_memory_frame:
  extcall_default_ready cx ret has op ty opt s /\
  eval_operand op t = eval_operand op s /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!v tv w. opt = SOME v /\ ~is_word_type ty /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    eval_operand op s = SOME w ==>
    mem_bytes_at (w2n w) (val_footprint tv v) t.vs_memory =
      mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory) ==>
  extcall_default_ready cx ret has op ty opt t
Proof
  simp[extcall_default_ready_def] >> strip_tac >>
  simp[] >> conj_tac >- (Cases_on `opt` >> gvs[]) >>
  qx_gen_tac `v` >> strip_tac >>
  qpat_x_assum `!d. opt = SOME d ==> _` (qspec_then `v` mp_tac) >>
  simp[] >> strip_tac >>
  `expr_val_rel cx ty v op t` by
    (Cases_on `is_word_type ty`
     >- (gvs[expr_val_rel_def] >> metis_tac[]) >>
     qspecl_then [`cx`, `ty`, `v`, `op`, `s`, `t`, `w`, `tv`]
       mp_tac expr_val_rel_footprint_agree >>
     impl_tac >- (simp[] >> metis_tac[]) >> simp[]) >>
  qexistsl_tac [`tv`, `rtv`, `w`] >> simp[] >> rpt strip_tac >> gvs[] >> decide_tac
QED

Theorem extcall_default_call_frame[local]:
  extcall_default_ready cx ret has op ty opt s /\
  eval_operand op t = eval_operand op s /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  t.vs_memory = (write_memory_with_expansion dst data s).vs_memory /\
  LENGTH data <= cap /\
  (!v tv w. opt = SOME v /\ ~is_word_type ty /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    eval_operand op s = SOME w ==>
    regions_disjoint dst cap (w2n w) (val_footprint tv v)) ==>
  extcall_default_ready cx ret has op ty opt t
Proof
  strip_tac >> irule extcall_default_memory_frame >>
  qexists_tac `s` >> simp[] >> rpt strip_tac >>
  irule hash_write_memory_disjoint >>
  first_x_assum drule_all >> simp[regions_disjoint_def] >> decide_tac
QED

Theorem extcall_oracle_returned_mem:
  emit_op (if stat then STATICCALL else CALL)
    (if stat then [gas_op;addr_op;call_offset;call_len;buf_op;Lit (n2w cap)]
     else [gas_op;addr_op;value_op;call_offset;call_len;buf_op;Lit (n2w cap)])
    sp = (ok,sc) /\
  fn_has_code sp sc func /\ fn_inst_ids_distinct func /\
  extcall_request_ready ctx func cenv cx ret_type es sa s0 sp stat
    addr_op value_op gas_op buf_op call_offset call_len cap target value_opt
    calldata has_default default_op default_ty default_opt ee t /\
  alloca_history func t /\
  (!ao az. eval_operand call_offset t = SOME ao /\
     eval_operand call_len t = SOME az ==>
     w2n az = 0 \/ w2n ao + w2n az <= t.vs_alloca_next) /\
  take_call_outcome target calldata value_opt ee = (INL (rq,oc),ee1) ==>
  ?z. gas_path_mem ctx func t 0 (OK z) /\
    extcall_returned ctx func cenv cx ret_type es sa s0 sc addr_op buf_op cap target
      has_default default_op default_ty default_opt oc.co_returnData
      (SND (adopt_call_outcome rq oc ee1)) z /\
    alloca_history func z /\ z.vs_allocas = t.vs_allocas /\
    z.vs_alloca_next = t.vs_alloca_next /\
    eval_operand ok z = SOME (bool_to_word oc.co_success) /\
    (!p. safe_operand sp p ==> eval_operand p z = eval_operand p t)
Proof
  strip_tac >> fs[extcall_request_ready_def] >>
  rename1 `eval_operand addr_op t = SOME aw` >>
  rename1 `eval_operand value_op t = SOME vw` >>
  rename1 `eval_operand call_offset t = SOME ao` >>
  rename1 `eval_operand call_len t = SOME az` >>
  rename1 `eval_operand buf_op t = SOME ro` >>
  rename1 `FLOOKUP t.vs_allocas live = SOME (w2n ro,buf_size)` >>
  `?gw. eval_operand gas_op t = SOME gw` by (Cases_on `eval_operand gas_op t` >> gvs[]) >>
  `stat = IS_NONE value_opt /\
   w2n (if stat then 0w else vw) = (case value_opt of NONE => 0 | SOME n => n)` by
    (Cases_on `value_opt` >> gvs[]) >>
  `cap < dimword (:256)` by decide_tac >>
  `alloca_inv t` by fs[stmt_state_rel_def] >>
  `cap = 0 \/ w2n ro + cap <= t.vs_alloca_next` by
    (`w2n ro + buf_size <= t.vs_alloca_next` by
       (fs[venomMemDefsTheory.alloca_inv_def,
           venomMemDefsTheory.alloca_next_valid_def] >>
        qpat_x_assum `!aid base sz. _` (qspecl_then [`live`,`w2n ro`,`buf_size`] mp_tac) >>
        simp[] >> decide_tac) >> decide_tac) >>
  mp_tac (Q.INST [`initial` |-> `sa`, `initial_es` |-> `es`, `es` |-> `ee`,
    `es1` |-> `ee1`, `s` |-> `t`, `sa` |-> `sp`, `sb` |-> `sc`,
    `val_op` |-> `value_op`, `to_op` |-> `addr_op`, `op` |-> `buf_op`,
    `dp` |-> `call_offset`, `dl` |-> `call_len`, `outcome` |-> `oc`,
    `gas` |-> `gw`, `val_word` |-> `vw`] raw_call_oracle_run_mem) >>
  (impl_tac >- (fs[regions_disjoint_def] >> rpt conj_tac >> metis_tac[])) >>
  disch_then (qx_choose_then `after` (qx_choose_then `res` strip_assume_tac)) >>
  suspend "post"
QED

Resume extcall_oracle_returned_mem[post]:
  markerLib.RESUME_TAC >>
  `res.vs_memory = (write_memory_with_expansion (w2n (ro:bytes32))
    (TAKE cap oc.co_returnData) t).vs_memory` by
    (qpat_assum `res = update_var _ _ _` (fn th => once_rewrite_tac[th]) >>
     simp[update_var_def]) >>
  `eval_operand default_op res = eval_operand default_op t` by metis_tac[] >>
  `extcall_default_ready cx ret_type has_default default_op default_ty default_opt res` by
    (mp_tac (Q.INST [`ret` |-> `ret_type`, `has` |-> `has_default`,
       `op` |-> `default_op`, `ty` |-> `default_ty`, `opt` |-> `default_opt`,
       `s` |-> `t`, `t` |-> `res`, `dst` |-> `w2n (ro:bytes32)`,
       `data` |-> `TAKE cap oc.co_returnData`] extcall_default_call_frame) >>
     (impl_tac >- (simp[LENGTH_TAKE_EQ] >> rpt strip_tac >> metis_tac[])) >> simp[]) >>
  `LENGTH oc.co_returnData < dimword (:256)` by
    metis_tac[exprSimRawCallCalldataTheory.calldata_take_call_outcome_bound] >>
  `ee1.gas_obs = ee.gas_obs` by
    (drule take_call_outcome_frame >> disch_then (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `(SND (adopt_call_outcome rq oc ee1)).gas_obs = []` by
    (simp[adopt_call_outcome_equation] >> rw[]) >>
  `ci_mono sp sc` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `sp.cs_next_id <= sc.cs_next_id /\ sp.cs_next_var <= sc.cs_next_var` by
    fs[ci_mono_def] >>
  `local_ptrs_reserved cenv sc` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sp` >> simp[]) >>
  `safe_operand sc addr_op /\ safe_operand sc buf_op /\ safe_operand sc default_op` by
    (rpt conj_tac >> irule safe_operand_mono >> qexists_tac `sp` >> simp[]) >>
  `live < sc.cs_next_id` by decide_tac >>
  `extcall_default_ready cx ret_type has_default default_op default_ty default_opt
     (res with vs_inst_idx := LENGTH sc.cs_current_insts)` by
    (irule extcall_default_memory_frame >> qexists_tac `res` >>
     simp[eval_operand_def, lookup_var_def]) >>
  `?aid sz. sa.cs_next_id <= aid /\ aid < sc.cs_next_id /\ cap <= sz /\
      FLOOKUP t.vs_allocas aid = SOME (w2n (ro:bytes32),sz)` by
    (qexistsl_tac [`live`,`buf_size`] >> simp[]) >>
  `mem_bytes_at (w2n (ro:bytes32)) (LENGTH (TAKE cap oc.co_returnData)) res.vs_memory =
     TAKE cap oc.co_returnData` by
    (qpat_assum `res = update_var _ _ _` (fn th => once_rewrite_tac[th]) >>
     simp_tac (srw_ss()) [update_var_def] >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `res = update_var _ _ _` kall_tac >>
  qpat_x_assum `res.vs_memory = _` kall_tac >>
  qexists_tac `res with vs_inst_idx := LENGTH sc.cs_current_insts` >>
  simp[extcall_returned_def, stmt_state_rel_inst_idx,
       exprSimRawCallCalldataTheory.raw_call_wb_frame_inst_idx,
       instIdxIndepTheory.eval_op_inst_idx] >> fs[] >>
  rpt conj_tac >> simp[valueEncodingDefsTheory.mem_bytes_at_def] >>
  goal_assum (drule_at (Pat `FLOOKUP t.vs_allocas _ = SOME _`)) >> simp[]
QED

Finalise extcall_oracle_returned_mem

Theorem extcall_returned_jump:
  extcall_returned ctx func cenv cx ret es sa s0 sp addr buf cap target
    has def dty opt data ee s /\
  sr.cs_current_bb = lbl /\ sr.cs_current_insts = [] /\
  sp.cs_next_id <= sr.cs_next_id /\ sp.cs_next_var <= sr.cs_next_var ==>
  extcall_returned ctx func cenv cx ret es sa s0 sr addr buf cap target
    has def dty opt data ee (jump_to lbl s)
Proof
  strip_tac >> fs[extcall_returned_def] >>
  rename1 `FLOOKUP s.vs_allocas live = SOME (w2n ro,buf_size)` >>
  `extcall_default_ready cx ret has def dty opt (jump_to lbl s)` by
    (irule extcall_default_memory_frame >> qexists_tac `s` >>
     simp[jump_to_def, eval_operand_def, lookup_var_def]) >>
  `local_ptrs_reserved cenv sr` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sp` >> simp[]) >>
  `safe_operand sr addr /\ safe_operand sr buf /\ safe_operand sr def` by
    (rpt conj_tac >> irule safe_operand_mono >> qexists_tac `sp` >> simp[]) >>
  `sa.cs_next_var <= sr.cs_next_var /\ sa.cs_next_id <= sr.cs_next_id /\
   live < sr.cs_next_id` by decide_tac >>
  `wb_frame cenv es ee sa s0 (jump_to lbl s) = wb_frame cenv es ee sa s0 s` by
    simp_tac (srw_ss()) [wb_frame_def, locals_kept_def, popped_kept_def,
         local_region_def, lookup_var_def, jump_to_def] >>
  simp[stmt_state_rel_jump_to, jump_to_def, eval_operand_def, lookup_var_def] >>
  goal_assum (drule_at (Pat `FLOOKUP s.vs_allocas _ = SOME _`)) >> simp[]
QED
