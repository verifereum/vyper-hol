Theory bodyFullExtCallDispatch
Ancestors exprBopSimProps[qualified,ignore_grammar] exprSimProps[qualified,ignore_grammar]
  exprSimExtCallCase valueEncodingProps venomState allocaHistory
  abiStaticLoopBody exprLoweringProps exprSafeOperand compileEnv loweringPosts
  emitHelperProps words vyperCallOutcomeProps vyperCallOutcome
  vyperInterpreter vyperState fragGasEmitCtrl fragGasOriginPtr
  venomInst venomInstProps venomExecSemantics ptrDiscipline finite_map
  bodyFullRawCallCallOrigin fragGasOriginPtrLoop fragExec list bodyFullRawCallFailure exprSimRawCallCalldata emitHelper context rich_list
  bodyFullRawCallCallFrame bodyFullRawCallCallStorage bodyPtrDefs extCallStatusSteps
  ghostPcTransportPtr bodyFullShared memLocDefs codegenRel unitTransformDefs pred_set
  decoderGhostFramePtr contextCodegenRel loweringStateRelDefs
  vyperStorageTrace vyperStorageFootprint vyperFiniteStoragePreservation exprSimRawCall extCallOracleStep
  stateRelProj[qualified,ignore_grammar] venomMemDefs[qualified,ignore_grammar]
  bodyFullUnwrapRun[qualified,ignore_grammar] bodyPtrBopRepresentationFrame[qualified,ignore_grammar]

Theorem extcall_dispatch_default_bytes[local]:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr_op value_op gas_op buf_op call_offset call_len cap target value_opt
    calldata has_default default_op default_ty default_opt ee t /\
  eval_operand buf_op t = SOME ro /\
  v.vs_memory = (write_memory_with_expansion (w2n ro) (TAKE cap rd) t).vs_memory ==>
  !dv w tv. default_opt = SOME dv /\ ~is_word_type default_ty /\
    eval_operand default_op t = SOME w /\
    evaluate_type (get_tenv cx) default_ty = SOME tv ==>
    mem_bytes_at (w2n w) (val_footprint tv dv) v.vs_memory =
    mem_bytes_at (w2n w) (val_footprint tv dv) t.vs_memory
Proof
  rpt strip_tac >> fs[extcall_request_ready_def] >>
  irule write_memory_mem_bytes_at_disjoint >>
  fs[loweringStateRelDefsTheory.regions_disjoint_def, listTheory.LENGTH_TAKE_EQ] >>
  IF_CASES_TAC >> decide_tac
QED

(* The status branch itself changes only the program counter. The return
   window and the independently materialized default retain their frames. *)
Theorem extcall_dispatch_returned:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr_op value_op gas_op buf_op call_offset call_len cap target value_opt
    calldata has_default default_op default_ty default_opt ee t /\
  sp.cs_next_var <= sr.cs_next_var /\ sp.cs_next_id <= sr.cs_next_id /\
  new_block cont_lbl se = (old_lbl,sr) /\
  (?H:(bool # bytes32 # type_value) list # num list.
     stmt_state_rel H ctx func cenv cx ee' v) /\
  (!H. valid_horizon cx st0 H ee'.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee' v /\
       storage_well_formed_on cx ee' (FST H)) /\
  wb_frame cenv es ee' sa s0 v /\
  extcall_default_ready cx ret_type has_default default_op default_ty default_opt v /\
  ~v.vs_halted /\ v.vs_allocas = t.vs_allocas /\
  v.vs_alloca_next = t.vs_alloca_next /\ eval_operand buf_op t = SOME ro /\
  v.vs_memory = (write_memory_with_expansion (w2n ro) (TAKE cap rd) t).vs_memory /\
  v.vs_returndata = rd /\
  (!op. safe_operand sp op ==> eval_operand op v = eval_operand op t) /\
  alloca_history func v /\ s0.vs_alloca_next <= v.vs_alloca_next /\
  ee'.gas_obs = [] /\ accounts_runtime_well_typed ee'.accounts /\
  MAP FDOM es.scopes = MAP FDOM ee'.scopes /\ LENGTH rd < dimword (:256) ==>
  extcall_returned st0 ctx func cenv cx ret_type es sa s0 sr addr_op buf_op cap
    target has_default default_op default_ty default_opt rd ee'
    (jump_to cont_lbl (next_inst v)) /\
  alloca_history func (jump_to cont_lbl (next_inst v)) /\
  s0.vs_alloca_next <= (jump_to cont_lbl (next_inst v)).vs_alloca_next /\
  (!op. safe_operand sp op ==>
    eval_operand op (jump_to cont_lbl (next_inst v)) = eval_operand op t) /\
  (jump_to cont_lbl (next_inst v)).vs_allocas = t.vs_allocas /\
  (jump_to cont_lbl (next_inst v)).vs_alloca_next = t.vs_alloca_next /\
  (jump_to cont_lbl (next_inst v)).vs_memory =
    (write_memory_with_expansion (w2n ro) (TAKE cap rd) t).vs_memory /\
  (!dv w tv. default_opt = SOME dv /\ ~is_word_type default_ty /\
    eval_operand default_op t = SOME w /\
    evaluate_type (get_tenv cx) default_ty = SOME tv ==>
    mem_bytes_at (w2n w) (val_footprint tv dv)
      (jump_to cont_lbl (next_inst v)).vs_memory =
    mem_bytes_at (w2n w) (val_footprint tv dv) t.vs_memory)
Proof
  strip_tac >>
  `!op. eval_operand op (next_inst v) = eval_operand op v` by
    (Cases >> simp[next_inst_def, eval_operand_def, lookup_var_def]) >>
  `!dv w tv. default_opt = SOME dv /\ ~is_word_type default_ty /\
      eval_operand default_op t = SOME w /\ evaluate_type (get_tenv cx) default_ty = SOME tv ==>
      mem_bytes_at (w2n w) (val_footprint tv dv) v.vs_memory =
      mem_bytes_at (w2n w) (val_footprint tv dv) t.vs_memory` by
    (rpt strip_tac >> irule extcall_dispatch_default_bytes >> goal_assum drule >>
     metis_tac[]) >>
  reverse conj_tac
  >- gvs[eval_operand_jump_to_eq, alloca_history_def, jump_to_def, next_inst_def] >>
  simp[extcall_returned_def, stmt_state_rel_jump_to, next_inst_def,
       stmt_state_rel_inst_idx] >>
  conj_tac >- (qexists_tac `H` >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (gvs[wb_frame_def, locals_kept_def, popped_kept_def, jump_to_def,
          lookup_var_def] >> metis_tac[]) >>
  `extcall_default_ready cx ret_type has_default default_op default_ty
     default_opt (jump_to cont_lbl (v with vs_inst_idx := v.vs_inst_idx + 1))` by
    (gvs[extcall_default_ready_def, expr_val_rel_def, jump_to_def,
         eval_operand_def, lookup_var_def] >> metis_tac[]) >>
  fs[extcall_request_ready_def, new_block_def, jump_to_def] >>
  `local_ptrs_reserved cenv sr` by metis_tac[local_ptrs_reserved_next_var] >>
  `safe_operand sr addr_op /\ safe_operand sr buf_op /\ safe_operand sr default_op`
    by metis_tac[safe_operand_mono] >>
  simp[] >>
  gvs[write_memory_mem_bytes_at_same] >>
  qexistsl_tac [`live`, `buf_size`] >> simp[] >> decide_tac
QED

(* A successful take cannot have come from the exhausted outcome list. *)
Theorem extcall_dispatch_take_replay[local]:
  take_call_outcome gas_cap target calldata value_opt ee = (INL (rq,oc),consumed) ==>
  take_call_outcome gas_cap target calldata value_opt (ee with gas_obs := tail) =
    (INL (rq,oc),consumed with gas_obs := tail)
Proof
  strip_tac >> drule take_call_outcome_success >> strip_tac >>
  `os <> []` by (strip_tac >> gvs[take_call_outcome_exhausted]) >>
  `~(oc.co_success /\ ~rq.cr_static /\ ~accounts_runtime_well_typed oc.co_accounts)`
    by metis_tac[] >>
  `call_outcome_request target calldata value_opt (ee with gas_obs := tail) =
     call_outcome_request target calldata value_opt ee` by simp[call_outcome_request_def] >>
  mp_tac (Q.INST [`st` |-> `ee with gas_obs := tail`, `outcome` |-> `oc`]
    take_call_outcome_SOME) >>
  gvs[] >> simp[evaluation_state_component_equality]
QED

(* Failed calls consume the oracle result but do not adopt it. The gas
   observation list is untouched at this seam, even for an explicit cap. *)
Theorem extcall_dispatch_failed_source:
  take_call_outcome (OPTION_BIND gas dest_NumV) target calldata value_opt ee =
    (INL (rq,oc),consumed) /\ ~oc.co_success ==>
  !tail. eval_ext_call_effects cx target calldata value_opt gas ee.accounts
           (ee with gas_obs := tail) =
    (INR (Error (RevertData oc.co_returnData)), consumed with gas_obs := tail)
Proof
  strip_tac >> gen_tac >>
  `take_call_outcome (OPTION_BIND gas dest_NumV) target calldata value_opt
      (ee with gas_obs := tail) = (INL (rq,oc),consumed with gas_obs := tail)` by
    (irule extcall_dispatch_take_replay >> simp[]) >>
  Cases_on `ee.outcomes`
  >- gvs[take_call_outcome_NONE] >>
  simp[eval_ext_call_effects_def, return_def, bind_def, ignore_bind_def, raise_def]
QED

(* Execute the concrete call and its status branch at the same endpoint for
   every storage horizon. Only the input storage-taint check depends on D. *)
Theorem extcall_dispatch_status_path:
  inst.inst_opcode = (if stat then STATICCALL else CALL) /\
  inst.inst_operands = (if stat then [g;a;dp;dl;rp;rl] else [g;a;v;dp;dl;rp;rl]) /\
  inst.inst_outputs = [out] /\
  eval_operand dp s = SOME ao /\ eval_operand dl s = SOME az /\
  eval_operand rp s = SOME ro /\ eval_operand rl s = SOME rn /\
  (az <> 0w ==> ?p. dp = Var p /\ ptr_covers G tn p s (w2n az)) /\
  (rn <> 0w ==> ?p. rp = Var p /\ ptr_covers G tn p s (w2n rn)) /\
  EVERY (\p. op_taint tn p = {}) inst.inst_operands /\
  (!j. w2n ao <= j /\ j < w2n ao + w2n az ==> j NOTIN tn.t_mem) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  inst_mem_below_frontier inst s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  step_inst_base inst s = OK u /\
  u = update_var out (if success then 1w else 0w) t /\
  u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp /\
  u.vs_initial_fmp = s.vs_initial_fmp /\
  sj.cs_current_bb = s.vs_current_bb /\ LENGTH sj.cs_current_insts = SUC s.vs_inst_idx /\
  emit_inst JNZ [Var out; Label cont_lbl; Label fail_lbl] [] sj = ((),se) /\
  fn_has_code sj se func ==>
  !D. stor_taint_ok_at D tn s ==>
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (jump_to (if success then cont_lbl else fail_lbl) (next_inst u)),
       step_prov PG G inst u, step_taint inst s u tn)
Proof
  strip_tac >> mp_tac extcall_dispatch_status_edges >> simp[]
QED

Theorem extcall_dispatch_failure_path:
  new_block fail_lbl se = (old_lbl,sf) /\
  emit_op RETURNDATASIZE [] sf = (zop,sz) /\
  compile_alloc_buffer 0 sz = (rb,sp) /\
  emit_void RETURNDATACOPY [rb.buf_operand;Lit 0w;zop] sp = ((),sc) /\
  emit_inst REVERT [rb.buf_operand;zop] [] sc = ((),sb) /\
  fn_has_code sf sb func /\ ~u.vs_halted /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u /\
    u.vs_alloca_next + pending_alloca_size func u <= w2n u.vs_initial_fmp) /\
  allocas_from lo u /\ lo <= u.vs_alloca_next /\
  LENGTH u.vs_returndata < dimword (:256) ==>
  ?t Gf tnf. t.vs_returndata = u.vs_returndata /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (jump_to fail_lbl (next_inst u),G,tn) [] (Abort Revert_abort t,Gf,tnf)
Proof
  strip_tac >>
  qabbrev_tac `s = jump_to fail_lbl (next_inst u)` >>
  `s.vs_current_bb = sf.cs_current_bb /\
   s.vs_inst_idx = LENGTH sf.cs_current_insts` by
    gvs[Abbr `s`, jump_to_def, new_block_def, comp_bind_def,
        comp_return_def, comp_get_def, comp_set_def] >>
  `~s.vs_halted /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
   s.vs_returndata = u.vs_returndata` by
    (gvs[Abbr `s`, jump_to_def, next_inst_def, allocas_from_def] >> metis_tac[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp` by
    (qpat_assum `Abbrev (s = _)`
       (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp u /\ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[jump_to_def, next_inst_def, allocas_below_fmp_def, pending_alloca_size_def] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  `?t. run_inst_seq (emitted_insts sf sb) s = Abort Revert_abort t /\
       t.vs_returndata = s.vs_returndata` by
    (qpat_x_assum `emit_op RETURNDATASIZE _ _ = _` mp_tac >>
     qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     qpat_x_assum `emit_void RETURNDATACOPY _ _ = _` mp_tac >>
     qpat_x_assum `emit_inst REVERT _ _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, emit_op_def, emit_void_def, emit_inst_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_var_def, fresh_id_def, emit_def] >>
     rpt strip_tac >>
     qpat_x_assum `fn_has_code _ _ _` kall_tac >>
     map_every (fn p => qpat_x_assum p (SUBST_ALL_TAC o SYM o SRULE []))
       [`_ = zop`, `_ = sz`, `_ = rb`, `_ = sp`, `_ = sc`, `_ = sb`] >>
     simp[NoAsms, emitted_insts_def] >>
     PURE_REWRITE_TAC[GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND] >>
     qpat_assum `s.vs_returndata = _` (SUBST1_TAC o SYM) >>
     irule raw_call_revert_run >> simp[ASCIInumbersTheory.toString_11]) >>
  qexists_tac `t with vs_inst_idx := s.vs_inst_idx + 3` >>
  simp[] >> metis_tac[raw_call_failure_block_origin_ptr]
QED

(* Recover the concrete oracle execution and its allocation frame from the
   already selected instruction endpoint. No horizon selects a new state. *)
Theorem extcall_dispatch_physical_frame:
  inst.inst_opcode = (if stat then STATICCALL else CALL) /\
  inst.inst_operands = (if stat then [g;a;dp;dl;rp;rl] else [g;a;v;dp;dl;rp;rl]) /\
  inst.inst_outputs = [out] /\
  eval_operand g s = SOME gw /\ eval_operand a s = SOME aw /\
  eval_operand v s = SOME vw /\ eval_operand dp s = SOME ao /\
  eval_operand dl s = SOME az /\ eval_operand rp s = SOME ro /\
  eval_operand rl s = SOME rn /\ step_inst_base inst s = OK u ==>
  exec_ext_call inst s gw aw (if stat then 0w else vw) ao az ro rn
    (stat \/ s.vs_call_ctx.cc_static) = OK u /\
  u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
  u.vs_fmp = s.vs_fmp /\ u.vs_initial_fmp = s.vs_initial_fmp /\
  u.vs_labels = s.vs_labels /\ u.vs_immutables = s.vs_immutables
Proof
  strip_tac >>
  conj_asm1_tac
  >- (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
      Cases_on `stat` >> simp[step_inst_base_opcode_eqs] >>
      IF_CASES_TAC >> simp[]) >>
  qpat_x_assum `exec_ext_call _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  Cases_on `s.vs_outcomes = []` >> simp[exec_ext_call_def, update_var_def] >>
  disch_then (SUBST1_TAC o SYM) >> simp[]
QED

(* The actual return window, not its entire allocated capacity, is cleaned.
   The status variable is fresh for the compiler state owning the operands. *)
Theorem extcall_dispatch_write_ghost:
  inst.inst_opcode = (if stat then STATICCALL else CALL) /\
  inst.inst_operands = (if stat then [g;a;dp;dl;rp;rl] else [g;a;v;dp;dl;rp;rl]) /\
  inst.inst_outputs = [out] /\ ~not_fresh_at sp out /\
  eval_operand g s = SOME gw /\ eval_operand a s = SOME aw /\
  eval_operand v s = SOME vw /\ eval_operand dp s = SOME ao /\
  eval_operand dl s = SOME az /\ eval_operand rp s = SOME ro /\
  eval_operand rl s = SOME rn /\ step_inst_base inst s = OK u /\
  u.vs_vars = (update_var out word s).vs_vars /\
  u.vs_memory = (write_memory_with_expansion (w2n ro) (TAKE (w2n rn) u.vs_returndata) s).vs_memory /\
  (rn = 0w \/ lo <= w2n ro) /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
     regions_disjoint (w2n ro) (w2n rn) b sz) /\
  ee.scopes = es.scopes /\ local_ptrs_rel func cenv es.scopes s /\
  local_ptrs_reserved cenv sp /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sp x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sp x) ==>
  !D. ghost_inv_at D lo d cenv cx es G tn s ==>
    ghost_inv_at D lo d cenv cx ee (step_prov PG G inst u)
      (step_taint inst s u tn) (jump_to cont_lbl (next_inst u)) /\
    (step_taint inst s u tn).t_mem = tn.t_mem DIFF
      {j | w2n ro <= j /\ j < w2n ro + LENGTH (TAKE (w2n rn) u.vs_returndata)}
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> gen_tac >> strip_tac >>
  drule_all extcall_dispatch_physical_frame >> strip_tac >>
  `stor_taint_ok_at D tn s` by fs[ghost_inv_at_def] >>
  `stor_taint_ok_at D (step_taint inst s u tn) u` by
    (drule_at (Pat `exec_ext_call _ _ _ _ _ _ _ _ _ _ = _`)
       raw_call_exec_stor_taint_at >>
     disch_then (qspecl_then [`tn`,`D`] mp_tac) >>
     Cases_on `stat` >> simp[]) >>
  `!x. not_fresh_at sp x ==>
    FLOOKUP (step_prov PG G inst u) x = FLOOKUP G x /\
    op_taint (step_taint inst s u tn) (Var x) = op_taint tn (Var x) /\
    lookup_var x u = lookup_var x s` by
    (rpt strip_tac >> `x <> out` by metis_tac[] >>
     FIRST [irule step_prov_other_output, irule step_taint_other_output, all_tac] >>
     simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  `new_site_bytes s u = {}` by
    (simp[new_site_bytes_def, FLOOKUP_DEF, EXTENSION] >> metis_tac[]) >>
  `(step_taint inst s u tn).t_mem = tn.t_mem DIFF
     {j | w2n ro <= j /\ j < w2n ro + LENGTH (TAKE (w2n rn) u.vs_returndata)}` by
    (Cases_on `stat` >>
     simp[step_taint_def, mem_taint_def, step_writes_def,
          range_bytes_def, mem_write_ops_def, memory_range_of_operands_def,
          source_memory_write_ranges_def, written_taint_def, LENGTH_TAKE_EQ,
          EXTENSION, arithmeticTheory.MIN_DEF] >>
     Cases_on `w2n rn < LENGTH u.vs_returndata` >>
     Cases_on `w2n rn <= LENGTH u.vs_returndata` >> simp[] >>
     `w2n rn = LENGTH u.vs_returndata` by decide_tac >> simp[]) >> simp[] >>
  simp[ghost_inv_at_jump, next_inst_def, ghost_inv_at_inst_idx] >>
  irule raw_call_clean_write_ghost_at >> simp[] >>
  qexistsl_tac [`G`,`TAKE (w2n rn) u.vs_returndata`,`w2n ro`,`es`,`func`,`s`,`sp`,`tn`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!name b sz. local_region _ _ _ _ _ _ ==> _` drule >>
      simp[regions_disjoint_def, LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF] >>
      IF_CASES_TAC >> decide_tac) >>
  Cases_on `rn = 0w` >> gvs[]
QED

(* Taking the result does not change the current storage backend; adoption
   may extend the trace. Transport only backwards along these two cuts. *)
Theorem extcall_dispatch_adopted_source:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr_op value_op gas_op buf_op call_offset call_len cap target value_opt
    calldata has_default default_op default_ty default_opt ee t /\
  take_call_outcome (OPTION_BIND gas dest_NumV) target calldata framed_value ee =
    (INL (rq,oc),consumed) /\
  adopt_call_outcome rq oc consumed = (INL (),ee') /\ oc.co_success ==>
  ee'.scopes = ee.scopes /\ ee'.immutables = ee.immutables /\
  ee'.gas_obs = [] /\ accounts_runtime_well_typed ee'.accounts /\
  MAP FDOM es.scopes = MAP FDOM ee'.scopes /\
  LENGTH oc.co_returnData < dimword (:256) /\
  (!tail. eval_ext_call_effects cx target calldata framed_value gas ee.accounts
      (ee with gas_obs := tail) = (INL oc.co_returnData,ee' with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H ee'.storage_trace ==>
       valid_horizon cx st0 H ee.storage_trace /\
       storage_well_formed_on cx ee' (FST H))
Proof
  strip_tac >>
  drule raw_call_take_adopt_fields >> simp[] >> strip_tac >>
  drule take_call_outcome_frame >> strip_tac >>
  `consumed.gas_obs = ee.gas_obs /\ consumed.accounts = ee.accounts /\
   consumed.tStorage = ee.tStorage` by
    (qpat_assum `consumed = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `ee'.gas_obs = ee.gas_obs` by
    (drule adopt_call_outcome_frame >>
     disch_then (strip_assume_tac) >>
     qpat_assum `ee' = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  fs[extcall_request_ready_def] >>
  `accounts_runtime_well_typed ee'.accounts` by metis_tac[take_adopt_call_outcome_typed] >>
  `LENGTH oc.co_returnData < dimword (:256)` by metis_tac[calldata_take_call_outcome_bound] >>
  `!hz. valid_horizon cx st0 hz ee'.storage_trace ==>
       valid_horizon cx st0 hz ee.storage_trace /\
       storage_well_formed_on cx ee' (FST hz)` by
    (qx_gen_tac `hz` >> disch_tac >>
     `valid_horizon cx st0 hz consumed.storage_trace` by
       (qpat_assum `adopt_call_outcome _ _ _ = _`
          (mp_then (Pat `_ _ = (_,_)`) mp_tac valid_horizon_frame) >>
        simp[storage_trace_frame_adopt]) >>
     `valid_horizon cx st0 hz ee.storage_trace` by
       (qpat_assum `take_call_outcome _ _ _ _ _ = _`
          (mp_then (Pat `_ _ = (_,_)`) mp_tac valid_horizon_frame) >>
        simp[storage_trace_frame_take_call]) >>
     simp[] >>
     `storage_well_formed_on cx consumed (FST hz)` by
       metis_tac[storage_well_formed_on_backends] >>
     irule adopt_call_outcome_preserves_finite_storage >>
     simp[valid_horizon_def] >>
     conj_tac >- fs[valid_horizon_def] >>
     qexistsl_tac [`oc`, `INL ()`, `rq`, `consumed`] >> simp[]) >>
  simp[] >>
  gen_tac >>
  `take_call_outcome (OPTION_BIND gas dest_NumV) target calldata framed_value
      (ee with gas_obs := tail) = (INL (rq,oc),consumed with gas_obs := tail)` by
    (irule extcall_dispatch_take_replay >> simp[]) >>
  `adopt_call_outcome rq oc (consumed with gas_obs := tail) =
     (INL (),ee' with gas_obs := tail)` by
    (qpat_x_assum `adopt_call_outcome _ _ _ = _` mp_tac >>
     simp[adopt_call_outcome_equation] >>
     IF_CASES_TAC >> simp[] >> disch_then (SUBST1_TAC o SYM) >>
     simp[evaluation_state_component_equality]) >>
  Cases_on `ee.outcomes`
  >- gvs[take_call_outcome_NONE] >>
  simp[eval_ext_call_effects_def, return_def, bind_def, ignore_bind_def, raise_def]
QED

Theorem extcall_dispatch_instruction:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr value gas buf off len cap target value_opt calldata has_default
    default_op default_ty default_opt ee s /\
  emit_op (if stat then STATICCALL else CALL)
    (if stat then [gas;addr;off;len;buf;Lit (n2w cap)]
     else [gas;addr;value;off;len;buf;Lit (n2w cap)]) sp = (Var out,sj) /\
  inst = mk_inst sp.cs_next_id (if stat then STATICCALL else CALL)
    (if stat then [gas;addr;off;len;buf;Lit (n2w cap)]
     else [gas;addr;value;off;len;buf;Lit (n2w cap)]) [out] /\
  eval_operand gas s = SOME gw /\
  (!g. OPTION_BIND source_gas dest_NumV = SOME g ==> g = w2n gw) /\
  frame_call_value cx value_opt ee = (INL framed_value,ee) /\
  take_call_outcome (OPTION_BIND source_gas dest_NumV) target calldata framed_value ee =
    (INL (rq,oc),consumed) ==>
  ?u t ro. step_inst_base inst s = OK u /\
    u = update_var out (if oc.co_success then 1w else 0w) t /\
    t.vs_vars = s.vs_vars /\ ~u.vs_halted /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    u.vs_fmp = s.vs_fmp /\ u.vs_initial_fmp = s.vs_initial_fmp /\
    eval_operand buf s = SOME ro /\
    u.vs_memory = (write_memory_with_expansion (w2n ro)
                    (TAKE cap oc.co_returnData) s).vs_memory /\
    u.vs_returndata = oc.co_returnData /\
    (!p. safe_operand sp p ==> eval_operand p u = eval_operand p s) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx (SND (adopt_call_outcome rq oc consumed)) u)
Proof
  strip_tac >>
  qhdtm_assum `extcall_request_ready`
    (strip_assume_tac o REWRITE_RULE [extcall_request_ready_def]) >>
  drule frame_call_value_success >> strip_tac >>
  `(stat \/ cx.txn.is_static) = IS_NONE framed_value /\
   w2n (if stat then 0w else vw) = (case framed_value of NONE => 0 | SOME n => n)` by
    (Cases_on `value_opt` >> Cases_on `cx.txn.is_static` >> gvs[]) >>
  `w2n (n2w cap : bytes32) = cap` by (simp[w2n_n2w] >> decide_tac) >>
  `!name b sz. local_region cenv ee.scopes s name b sz ==>
    b + sz <= w2n ro \/ w2n ro + cap <= b` by
    (rpt strip_tac >> qpat_x_assum `!name b sz. _ ==> regions_disjoint _ _ _ _` drule >>
     simp[regions_disjoint_def, DISJ_COMM]) >>
  `(cenv.ce_is_ctor ==> !name tv v immoff.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc immoff) /\
     FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
     immoff + type_memory_size tv <= w2n ro \/ w2n ro + cap <= immoff)` by
    (rpt strip_tac >> qpat_x_assum `cenv.ce_is_ctor ==> _` drule >>
     disch_then drule_all >> simp[regions_disjoint_def, DISJ_COMM]) >>
  `!hz. valid_horizon cx st0 hz ee.storage_trace ==>
     ?t u. run_inst_seq (emitted_insts sp sj) s = OK u /\
       u = update_var (STRING #"%" (toString sp.cs_next_var)) (bool_to_word oc.co_success) t /\
       eval_operand (Var out) u = SOME (bool_to_word oc.co_success) /\
       stmt_state_rel hz ctx func cenv cx (SND (adopt_call_outcome rq oc consumed)) u /\
       t = s with <|vs_outcomes := t.vs_outcomes; vs_requests := t.vs_requests;
         vs_accounts := t.vs_accounts; vs_transient := t.vs_transient;
         vs_logs := t.vs_logs; vs_pending_deletions := t.vs_pending_deletions;
         vs_returndata := t.vs_returndata; vs_memory := t.vs_memory|> /\
       t.vs_memory = (write_memory_with_expansion (w2n ro)
                      (TAKE cap oc.co_returnData) s).vs_memory /\
       t.vs_returndata = oc.co_returnData /\
       mem_bytes_at (w2n ro) (LENGTH (TAKE cap oc.co_returnData)) t.vs_memory =
         TAKE cap oc.co_returnData` by
    (qx_gen_tac `hz` >> strip_tac >>
     `stmt_state_rel hz ctx func cenv cx ee s` by metis_tac[] >>
     `take_call_outcome (OPTION_BIND source_gas dest_NumV) (w2w aw)
         (read_memory (w2n ao) (w2n az) s) framed_value ee = (INL (rq,oc),consumed)` by metis_tac[] >>
     qpat_assum `w2n (n2w cap : bytes32) = cap` (fn h =>
       irule (PURE_REWRITE_RULE [h] (Q.INST [`cap` |-> `cap`] raw_call_oracle_emit_run_aged))) >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl_tac [`ao`,`aw`,`az`,`len`,`off`,`ee`,`gw`,
       `OPTION_BIND source_gas dest_NumV`,`gas`,`buf`,`stat`,`target`,`addr`,`value`,`vw`,`framed_value`] >>
     simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  qpat_assum `valid_horizon cx st0 H ee.storage_trace` (fn h =>
    qpat_assum `!hz. _ ==> ?t u. run_inst_seq _ _ = _ /\ _`
      (strip_assume_tac o C MATCH_MP h)) >>
  rename1 `run_inst_seq (emitted_insts sp sj) s = OK u` >>
  rename1 `u = update_var _ _ t` >>
  `!hz. valid_horizon cx st0 hz ee.storage_trace ==>
     stmt_state_rel hz ctx func cenv cx (SND (adopt_call_outcome rq oc consumed)) u` by
    (rpt strip_tac >>
     qpat_assum `!hz. _ ==> ?t u. run_inst_seq _ _ = _ /\ _`
       (drule_then strip_assume_tac) >> gvs[]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `out = STRING #"%" (toString sp.cs_next_var)` by
    (qpat_assum `Var out = Var _` mp_tac >> simp[NoAsms]) >>
  `emitted_insts sp sj = [inst]` by simp[] >>
  `step_inst_base inst s = OK u` by
    (qpat_assum `run_inst_seq _ _ = _` mp_tac >>
     qpat_assum `emitted_insts sp sj = [inst]` (fn th => PURE_REWRITE_TAC[th,run_inst_seq_def]) >>
     Cases_on `step_inst_base inst s` >> simp[NoAsms]) >>
  `t.vs_vars = s.vs_vars` by
    (qpat_assum `t = _` (fn th => PURE_ONCE_REWRITE_TAC[th]) >> simp[]) >>
  `!p. safe_operand sp p ==> eval_operand p u = eval_operand p s` by
    (Cases >> simp[eval_operand_def, safe_operand_def, not_fresh_at_def,
       lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
     rpt strip_tac >> IF_CASES_TAC >> simp[] >>
     first_x_assum (qspec_then `sp.cs_next_var` mp_tac) >> simp[]) >>
  qexistsl_tac [`u`,`t`,`ro`] >>
  simp[bool_to_word_def] >>
  qpat_assum `t = _` (fn th => PURE_ONCE_REWRITE_TAC[th]) >>
  Cases_on `oc.co_success` >> simp[update_var_def, bool_to_word_def]
QED

(* The failed status jump and REVERT share the oracle's physical returndata.
   The source consumes the result without adopting it. *)
Theorem extcall_dispatch_abort:
  take_call_outcome (OPTION_BIND gas dest_NumV) target calldata value_opt ee =
    (INL (rq,oc),consumed) /\ ~oc.co_success /\
  outcomes_accounts_typed ee.outcomes /\
  new_block fail_lbl se = (old_lbl,sf) /\
  emit_op RETURNDATASIZE [] sf = (zop,sz) /\
  compile_alloc_buffer 0 sz = (rb,sp) /\
  emit_void RETURNDATACOPY [rb.buf_operand;Lit 0w;zop] sp = ((),sc) /\
  emit_inst REVERT [rb.buf_operand;zop] [] sc = ((),sb) /\
  fn_has_code sf sb func /\ ~u.vs_halted /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u /\
    u.vs_alloca_next + pending_alloca_size func u <= w2n u.vs_initial_fmp) /\
  allocas_from lo u /\ lo <= u.vs_alloca_next /\
  u.vs_returndata = oc.co_returnData /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (jump_to fail_lbl (next_inst u)),Gu,tu)) ==>
  ?f Gf tf. f.vs_returndata = oc.co_returnData /\
    (!H. valid_horizon cx st0 H consumed.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
        (Abort Revert_abort f,Gf,tf)) /\
    (!tail. eval_ext_call_effects cx target calldata value_opt gas ee.accounts
      (ee with gas_obs := tail) =
      (INR (Error (RevertData oc.co_returnData)), consumed with gas_obs := tail))
Proof
  strip_tac >>
  `LENGTH u.vs_returndata < dimword (:256)` by
    (simp[] >> metis_tac[calldata_take_call_outcome_bound]) >>
  drule_all extcall_dispatch_failed_source >> disch_tac >>
  drule_all extcall_dispatch_failure_path >>
  disch_then (qspecl_then [`tu`,`explicit`,`PG`,`Gu`] strip_assume_tac) >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >> simp[] >>
  gen_tac >> disch_tac >>
  `valid_horizon cx st0 H ee.storage_trace` by
    (qpat_assum `take_call_outcome _ _ _ _ _ = _`
       (mp_then (Pat `_ _ = (_,_)`) mp_tac valid_horizon_frame) >>
     simp[storage_trace_frame_take_call]) >>
  irule gas_origin_ptr_path_trans >>
  qexistsl_tac [`Gu`,`jump_to fail_lbl (next_inst u)`,`tu`] >> simp[]
QED

Theorem extcall_dispatch_live_frame[local]:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr value gas buf off len cap target value_opt calldata has_default
    default_op default_ty default_opt ee s /\
  ~not_fresh_at sp out /\ u = update_var out w t /\
  t.vs_vars = s.vs_vars /\ u.vs_allocas = s.vs_allocas /\
  u.vs_alloca_next = s.vs_alloca_next /\ eval_operand buf s = SOME ro /\
  u.vs_memory = (write_memory_with_expansion (w2n ro) (TAKE cap rd) s).vs_memory /\
  (!p. safe_operand sp p ==> eval_operand p u = eval_operand p s) /\
  ee'.scopes = ee.scopes ==>
  wb_frame cenv es ee' sa s0 u /\
  extcall_default_ready cx ret_type has_default default_op default_ty default_opt u
Proof
  strip_tac >>
  `!dv w tv. default_opt = SOME dv /\ ~is_word_type default_ty /\
    eval_operand default_op s = SOME w /\ evaluate_type (get_tenv cx) default_ty = SOME tv ==>
    mem_bytes_at (w2n w) (val_footprint tv dv) u.vs_memory =
    mem_bytes_at (w2n w) (val_footprint tv dv) s.vs_memory` by
    (rpt strip_tac >> irule extcall_dispatch_default_bytes >>
     goal_assum drule >> metis_tac[]) >>
  qhdtm_assum `extcall_request_ready`
    (strip_assume_tac o REWRITE_RULE [extcall_request_ready_def]) >>
  conj_tac
  >- (`wb_frame cenv es ee sa s0 u` by
        (`t.vs_allocas = s.vs_allocas /\ t.vs_memory = u.vs_memory` by
           (qpat_assum `u = update_var _ _ _` (fn th => fs[th,update_var_def])) >>
         `~not_fresh_at sa out` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
         qpat_assum `u = update_var _ _ _` SUBST1_TAC >>
         `ro' = ro` by fs[] >>
         irule raw_call_oracle_frame >> simp[] >>
         qexistsl_tac [`w2n ro`,`TAKE cap rd`,`s`] >> simp[] >>
         `LENGTH (TAKE cap rd) <= cap` by simp[LENGTH_TAKE_EQ] >>
         conj_tac
         >- (rpt strip_tac >>
             qpat_assum `!name b sz. local_region _ es.scopes s0 _ _ _ ==> _` drule >>
             simp[regions_disjoint_def] >> decide_tac) >>
         rpt strip_tac >>
         qpat_assum `!aid b sz. _ ==> regions_disjoint _ _ _ _` drule_all >>
         simp[regions_disjoint_def] >> decide_tac) >>
      qpat_assum `wb_frame cenv es ee sa s0 u` mp_tac >>
      PURE_REWRITE_TAC[wb_frame_def,locals_kept_def,popped_kept_def] >>
      qpat_assum `ee'.scopes = ee.scopes` (fn th => REWRITE_TAC[th])) >>
  qpat_assum `extcall_default_ready _ _ _ _ _ _ s`
    (strip_assume_tac o REWRITE_RULE [extcall_default_ready_def]) >>
  `safe_operand sp default_op` by fs[] >>
  `eval_operand default_op u = eval_operand default_op s` by simp[] >>
  simp[extcall_default_ready_def] >> qx_gen_tac `d` >> disch_tac >>
  qpat_assum `!d. default_opt = SOME d ==> _` drule >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `tv` (qx_choose_then `rtv` (qx_choose_then `dw` strip_assume_tac)))) >>
  `expr_val_rel cx default_ty d default_op u` by
    (Cases_on `is_word_type default_ty`
     >- (`eval_operand default_op s = SOME (typed_val_to_w256 tv d)` by
           (irule exprBopSimPropsTheory.expr_val_rel_typed >>
            qexistsl_tac [`cx`,`default_ty`] >> simp[]) >>
         fs[expr_val_rel_def]) >>
     irule exprSimPropsTheory.expr_val_rel_footprint_agree >> simp[] >>
     metis_tac[]) >>
  gvs[]
QED

(* Assemble the return state's semantic frame from the adopted outcome.
   The witness for stmt_state_rel comes from the request's input horizon;
   the guarded relation at return uses backward trace transport. *)
Theorem extcall_dispatch_adopted_entry[local]:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr value gas buf off len cap target value_opt calldata has_default
    default_op default_ty default_opt ee s /\
  take_call_outcome (OPTION_BIND source_gas dest_NumV) target calldata framed_value ee =
    (INL (rq,oc),consumed) /\
  adopt_call_outcome rq oc consumed = (INL (),ee') /\ oc.co_success /\
  sp.cs_next_var <= sr.cs_next_var /\ sp.cs_next_id <= sr.cs_next_id /\
  new_block cont_lbl se = (old_lbl,sr) /\
  ~not_fresh_at sp out /\ u = update_var out 1w t /\ t.vs_vars = s.vs_vars /\
  ~u.vs_halted /\ u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
  alloca_history func u /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  eval_operand buf s = SOME ro /\
  u.vs_memory = (write_memory_with_expansion (w2n ro) (TAKE cap oc.co_returnData) s).vs_memory /\
  u.vs_returndata = oc.co_returnData /\
  (!p. safe_operand sp p ==> eval_operand p u = eval_operand p s) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func cenv cx ee' u) ==>
  extcall_returned st0 ctx func cenv cx ret_type es sa s0 sr addr buf cap target
    has_default default_op default_ty default_opt oc.co_returnData ee'
    (jump_to cont_lbl (next_inst u)) /\
  alloca_history func (jump_to cont_lbl (next_inst u)) /\
  s0.vs_alloca_next <= (jump_to cont_lbl (next_inst u)).vs_alloca_next /\
  (!p. safe_operand sp p ==>
    eval_operand p (jump_to cont_lbl (next_inst u)) = eval_operand p s) /\
  (jump_to cont_lbl (next_inst u)).vs_allocas = s.vs_allocas /\
  (jump_to cont_lbl (next_inst u)).vs_alloca_next = s.vs_alloca_next /\
  (!dv w tv. default_opt = SOME dv /\ ~is_word_type default_ty /\
    eval_operand default_op s = SOME w /\ evaluate_type (get_tenv cx) default_ty = SOME tv ==>
    mem_bytes_at (w2n w) (val_footprint tv dv) (jump_to cont_lbl (next_inst u)).vs_memory =
    mem_bytes_at (w2n w) (val_footprint tv dv) s.vs_memory) /\
  (!H. valid_horizon cx st0 H ee'.storage_trace ==> valid_horizon cx st0 H ee.storage_trace) /\
  (!tail. eval_ext_call_effects cx target calldata framed_value source_gas ee.accounts
    (ee with gas_obs := tail) = (INL oc.co_returnData,ee' with gas_obs := tail))
Proof
  strip_tac >>
  drule_all extcall_dispatch_adopted_source >> strip_tac >>
  drule_all extcall_dispatch_live_frame >> strip_tac >>
  Q.SUBGOAL_THEN
    `?H:(bool # bytes32 # type_value) list # num list. stmt_state_rel H ctx func cenv cx ee' u`
    ASSUME_TAC
  >- (qhdtm_assum `extcall_request_ready`
        (strip_assume_tac o REWRITE_RULE [extcall_request_ready_def]) >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H ee'.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee' u /\ storage_well_formed_on cx ee' (FST H)` by
    metis_tac[] >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by simp[] >>
  drule_all extcall_dispatch_returned >> simp[] >> metis_tac[]
QED

(* Packing supplies the clean input window and its pointer coverage. The
   output frontier and floor, in contrast, follow from its live allocation. *)
Theorem extcall_dispatch_counted_status[local]:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr value gas buf off len cap target value_opt calldata has_default
    default_op default_ty default_opt ee s /\
  inst = mk_inst sp.cs_next_id (if stat then STATICCALL else CALL)
    (if stat then [gas;addr;off;len;buf;Lit (n2w cap)]
     else [gas;addr;value;off;len;buf;Lit (n2w cap)]) [out] /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  sj.cs_current_bb = s.vs_current_bb /\ LENGTH sj.cs_current_insts = SUC s.vs_inst_idx /\
  emit_inst JNZ [Var out;Label cont_lbl;Label fail_lbl] [] sj = ((),se) /\
  fn_has_code sj se func /\
  EVERY (\p. op_taint tn p = {}) [addr;value;gas;buf;off;len] /\
  (!ao az. eval_operand off s = SOME ao /\ eval_operand len s = SOME az ==>
    (az <> 0w ==> (?p. off = Var p /\ ptr_covers G tn p s (w2n az)) /\
                  w2n ao + w2n az <= s.vs_alloca_next) /\
    (!j. w2n ao <= j /\ j < w2n ao + w2n az ==> j NOTIN tn.t_mem)) /\
  (cap <> 0 ==> ?p. buf = Var p /\ ptr_covers G tn p s cap) /\
  allocas_from lo s /\ alloca_history func s /\
  step_inst_base inst s = OK u /\
  u = update_var out (if success then 1w else 0w) t /\
  u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp /\
  u.vs_initial_fmp = s.vs_initial_fmp ==>
  alloca_history func u /\
  !H. valid_horizon cx st0 H ee.storage_trace /\ stor_taint_ok_at (DF H) tn s ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (jump_to (if success then cont_lbl else fail_lbl) (next_inst u)),
       step_prov PG G inst u, step_taint inst s u tn)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `inst.inst_opcode = (if stat then STATICCALL else CALL) /\
   inst.inst_operands = (if stat then [gas;addr;off;len;buf;Lit (n2w cap)]
     else [gas;addr;value;off;len;buf;Lit (n2w cap)]) /\ inst.inst_outputs = [out]`
    by simp[mk_inst_def] >>
  conj_tac
  >- (`step_inst 0 ctx inst s = OK u /\ ~is_terminator inst.inst_opcode` by
        (Cases_on `stat` >> simp[step_inst_non_invoke,is_terminator_def]) >>
      drule_all step_preserves_control_flow >> strip_tac >>
      metis_tac[alloca_history_frame]) >>
  qhdtm_assum `extcall_request_ready`
    (strip_assume_tac o REWRITE_RULE [extcall_request_ready_def]) >>
  `stmt_state_rel H ctx func cenv cx ee s` by metis_tac[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx ee s`
       (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  drule stateRelProjTheory.stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  `w2n (n2w cap : bytes32) = cap` by (simp[w2n_n2w] >> decide_tac) >>
  `eval_operand (Lit (n2w cap)) s = SOME (n2w cap)` by simp[eval_operand_def] >>
  `w2n ro + cap <= s.vs_alloca_next` by
    (fs[venomMemDefsTheory.alloca_inv_def,venomMemDefsTheory.alloca_next_valid_def] >>
     qpat_x_assum `!aid base sz. _ ==> _` drule >> decide_tac) >>
  qpat_assum `!ao az. eval_operand off s = _ /\ _ ==> _`
    (qspecl_then [`ao`,`az`] (fn th =>
      qpat_assum `eval_operand off s = SOME ao` (fn h1 =>
      qpat_assum `eval_operand len s = SOME az` (fn h2 =>
        strip_assume_tac (MATCH_MP th (CONJ h1 h2)))))) >>
  `inst_mem_below_frontier inst s` by
    (Cases_on `eval_operand gas s` >> Cases_on `stat` >>
     simp[inst_mem_below_frontier_def,source_memory_write_ranges_def,
       source_memory_read_ranges_def,mem_write_ops_def,mem_read_ops_def,
       memory_range_of_operands_def] >> Cases_on `az = 0w` >> fs[] >> decide_tac) >>
  `EVERY (\p. op_taint tn p = {}) inst.inst_operands` by
    (Cases_on `stat` >> fs[op_taint_def]) >>
  gen_tac >> strip_tac >>
  irule extcall_dispatch_status_path >>
  ASM_SIMP_TAC bool_ss [] >>
  rpt conj_tac
  >- (qexists_tac `bb` >> simp[NoAsms] >> metis_tac[])
  >- (qexistsl_tac [`addr`,`ao`,`az`,`len`,`off`,`gas`,`Lit (n2w cap)`,
                    `n2w cap`,`ro`,`buf`,`stat`,`value`] >>
      ASM_SIMP_TAC bool_ss [w2n_n2w] >> metis_tac[])
  >> qexistsl_tac [`out`,`se`,`sj`,`t`] >> ASM_SIMP_TAC bool_ss []
QED

(* Only the status output can change provenance or operand taint. The
   memory taint is reduced by the exact write, not by the buffer capacity. *)
Theorem extcall_dispatch_return_ghost[local]:
  inst.inst_outputs = [out] /\ ~not_fresh_at sp out /\
  sa.cs_next_var <= sp.cs_next_var /\
  EVERY (safe_operand sp) [addr;buf;default_op] /\
  EVERY (\p. op_taint tn p = {}) [addr;buf;default_op] /\
  (!p. safe_operand sp p ==> eval_operand p z = eval_operand p s) /\
  z.vs_alloca_next = s.vs_alloca_next /\
  eval_operand buf s = SOME ro /\
  (cap <> 0 ==> ?p. buf = Var p /\ ptr_covers G tn p s cap) /\
  (!dv. default_opt = SOME dv /\ ~is_word_type default_ty ==>
    ptr_mem_ok cx default_ty dv default_op G tn s /\
    (type_memory_bytes cenv default_ty <> 0 ==>
      (?p. default_op = Var p /\ ptr_covers G tn p s (type_memory_bytes cenv default_ty)) /\
      (!w. eval_operand default_op s = SOME w ==>
          w2n w + type_memory_bytes cenv default_ty <= s.vs_alloca_next))) /\
  extcall_default_ready cx ret_type has_default default_op default_ty default_opt s /\
  (!dv w tv. default_opt = SOME dv /\ ~is_word_type default_ty /\
    eval_operand default_op s = SOME w /\ evaluate_type (get_tenv cx) default_ty = SOME tv ==>
    mem_bytes_at (w2n w) (val_footprint tv dv) z.vs_memory =
    mem_bytes_at (w2n w) (val_footprint tv dv) s.vs_memory) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  Gu = step_prov PG G inst u /\ tu = step_taint inst s u tn /\
  tu.t_mem = tn.t_mem DIFF {j | w2n ro <= j /\ j < w2n ro + LENGTH (TAKE cap rd)} ==>
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
      (!i. w2n w <= i /\ i < w2n w + MIN cap (LENGTH rd) ==> i NOTIN tu.t_mem))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!x. not_fresh_at sp x ==>
      FLOOKUP Gu x = FLOOKUP G x /\ op_taint tu (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> `x <> out` by metis_tac[] >>
     simp[step_prov_other_output,step_taint_other_output]) >>
  `!p. safe_operand sp p ==> op_taint tu p = op_taint tn p /\
     (!x. p = Var x ==> FLOOKUP Gu x = FLOOKUP G x)` by
    (Cases >> simp[safe_operand_def,op_taint_def] >> metis_tac[op_taint_def]) >>
  `tu.t_mem SUBSET tn.t_mem` by simp[SUBSET_DEF] >>
  conj_tac
  >- (irule bodyFullUnwrapRunTheory.ghost_kept_at_clean_suffix >>
      qexistsl_tac [`G`,`tn`] >> simp[] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  fs[EVERY_DEF] >>
  `op_taint tu addr = {} /\ op_taint tu buf = {} /\ op_taint tu default_op = {}` by metis_tac[] >>
  ASM_SIMP_TAC bool_ss [] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qhdtm_assum `extcall_default_ready`
        (strip_assume_tac o REWRITE_RULE [extcall_default_ready_def]) >>
      qpat_assum `!d. default_opt = SOME d ==> _` drule >>
      disch_then (CONJUNCTS_THEN2 assume_tac
        (qx_choose_then `tv` (qx_choose_then `rtv` (qx_choose_then `dw` strip_assume_tac)))) >>
      conj_tac
      >- (irule bodyPtrBopRepresentationFrameTheory.bop_ptr_mem_ok_frame >>
          qexistsl_tac [`G`,`s`,`tn`,`tv`] >>
          fs[SUBSET_DEF] >> metis_tac[]) >>
      strip_tac >>
      `?p. default_op = Var p /\ ptr_covers G tn p s (type_memory_bytes cenv default_ty)`
        by metis_tac[] >>
      fs[ptr_covers_def,GSYM eval_operand_def] >> (gvs[])) >>
  strip_tac >>
  Q.SUBGOAL_THEN `?p. buf = Var p /\ ptr_covers G tn p s cap`
    (qx_choose_then `bp` (CONJUNCTS_THEN2 SUBST_ALL_TAC
       (STRIP_ASSUME_TAC o REWRITE_RULE [ptr_covers_def])))
  >- metis_tac[] >>
  gvs[eval_operand_def,listTheory.LENGTH_TAKE_EQ,arithmeticTheory.MIN_DEF]
QED

(* At the post-precheck CALL, select its physical successor once, then either
   forward the failed outcome or enter the return block with the live frame. *)
Theorem extcall_dispatch_selected:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr value gas buf off len cap target value_opt calldata has_default
    default_op default_ty default_opt ee s /\
  (IS_SOME default_opt /\ ~is_word_type default_ty ==>
    ?w aid tv. eval_operand default_op s = SOME w /\
      evaluate_type (get_tenv cx) default_ty = SOME tv /\
      FLOOKUP s.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
      aid < sp.cs_next_id) /\
  emit_op (if stat then STATICCALL else CALL)
    (if stat then [gas;addr;off;len;buf;Lit (n2w cap)]
     else [gas;addr;value;off;len;buf;Lit (n2w cap)]) sp = (Var out,sj) /\
  inst = mk_inst sp.cs_next_id (if stat then STATICCALL else CALL)
    (if stat then [gas;addr;off;len;buf;Lit (n2w cap)]
     else [gas;addr;value;off;len;buf;Lit (n2w cap)]) [out] /\
  ~not_fresh_at sp out /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  sj.cs_current_bb = s.vs_current_bb /\ LENGTH sj.cs_current_insts = SUC s.vs_inst_idx /\
  emit_inst JNZ [Var out;Label cont_lbl;Label fail_lbl] [] sj = ((),se) /\
  fn_has_code sj se func /\
  new_block fail_lbl se = (old_fail,sf) /\
  emit_op RETURNDATASIZE [] sf = (zop,sz) /\
  compile_alloc_buffer 0 sz = (rb,sb0) /\
  emit_void RETURNDATACOPY [rb.buf_operand;Lit 0w;zop] sb0 = ((),sc) /\
  emit_inst REVERT [rb.buf_operand;zop] [] sc = ((),sb) /\
  fn_has_code sf sb func /\
  new_block cont_lbl sb = (old_cont,sr) /\
  sp.cs_next_var <= sr.cs_next_var /\ sp.cs_next_id <= sr.cs_next_id /\
  eval_operand gas s = SOME gw /\
  (!g. OPTION_BIND source_gas dest_NumV = SOME g ==> g = w2n gw) /\
  frame_call_value cx value_opt ee = (INL framed_value,ee) /\
  take_call_outcome (OPTION_BIND source_gas dest_NumV) target calldata framed_value ee =
    (INL (rq,oc),consumed) /\
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
  allocas_from lo s /\ alloca_history func s /\
  lo <= s.vs_alloca_next /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> ghost_inv_at (DF H) lo d cenv cx ee G tn s) ==>
  if oc.co_success then
    ?ee' z Gu tu.
      adopt_call_outcome rq oc consumed = (INL (),ee') /\
      extcall_returned st0 ctx func cenv cx ret_type es sa s0 sr addr buf cap target
        has_default default_op default_ty default_opt oc.co_returnData ee' z /\
      (IS_SOME default_opt /\ ~is_word_type default_ty ==>
        ?w aid tv. eval_operand default_op z = SOME w /\
          evaluate_type (get_tenv cx) default_ty = SOME tv /\
          FLOOKUP z.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
          aid < sr.cs_next_id) /\
      (!H. valid_horizon cx st0 H ee'.storage_trace ==>
        valid_horizon cx st0 H ee.storage_trace /\
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gu,tu) /\
        ghost_inv_at (DF H) lo d cenv cx ee' Gu tu z) /\
      (!tail. eval_ext_call_effects cx target calldata framed_value source_gas ee.accounts
        (ee with gas_obs := tail) = (INL oc.co_returnData,ee' with gas_obs := tail)) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tu /\
      alloca_history func z /\ allocas_from lo z /\
      lo <= z.vs_alloca_next /\ s0.vs_alloca_next <= z.vs_alloca_next /\
      EVERY (\p. op_taint tu p = {}) [addr;buf;default_op] /\
      (!dv. default_opt = SOME dv /\ ~is_word_type default_ty ==>
        ptr_mem_ok cx default_ty dv default_op Gu tu z /\
        (type_memory_bytes cenv default_ty <> 0 ==>
          ?p b k w. default_op = Var p /\ FLOOKUP Gu p = SOME (b,k) /\
          eval_operand default_op z = SOME w /\ b <= w2n w /\
          w2n w + type_memory_bytes cenv default_ty <= b + k /\
          w2n w + type_memory_bytes cenv default_ty <= z.vs_alloca_next)) /\
      (cap <> 0 ==>
        ?p b k w. buf = Var p /\ FLOOKUP Gu p = SOME (b,k) /\
          eval_operand buf z = SOME w /\ b <= w2n w /\ w2n w + cap <= b + k /\
          (!i. w2n w <= i /\ i < w2n w + MIN cap (LENGTH oc.co_returnData) ==> i NOTIN tu.t_mem))
  else
    ?f Gf tf. f.vs_returndata = oc.co_returnData /\
      (!H. valid_horizon cx st0 H consumed.storage_trace ==>
        valid_horizon cx st0 H ee.storage_trace /\
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
          (Abort Revert_abort f,Gf,tf)) /\
      (!tail. eval_ext_call_effects cx target calldata framed_value source_gas ee.accounts
        (ee with gas_obs := tail) =
        (INR (Error (RevertData oc.co_returnData)),consumed with gas_obs := tail))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all extcall_dispatch_instruction >>
  disch_then (qx_choose_then `u` (qx_choose_then `t` (qx_choose_then `ro` strip_assume_tac))) >>
  `EVERY (\p. op_taint tn p = {}) [addr;value;gas;buf;off;len]` by fs[EVERY_DEF] >>
  drule_all extcall_dispatch_counted_status >>
  disch_then (qspecl_then [`explicit`,`PG`,`DF`] strip_assume_tac) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       stor_taint_ok_at (DF H) tn s` by
    (rpt strip_tac >> gvs[ghost_inv_at_def]) >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by (fs[allocas_from_def] >> (gvs[allocas_from_def])) >>
  reverse (Cases_on `oc.co_success`) >> simp[]
  >- (`outcomes_accounts_typed ee.outcomes` by fs[extcall_request_ready_def] >>
      `!H. valid_horizon cx st0 H ee.storage_trace ==>
          gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
            (OK (jump_to fail_lbl (next_inst u)),step_prov PG G inst u,step_taint inst s u tn)` by fs[] >>
      `?H:(bool # bytes32 # type_value) list # num list.
        stmt_state_rel H ctx func cenv cx ee s` by
        (qhdtm_assum `extcall_request_ready`
           (strip_assume_tac o REWRITE_RULE [extcall_request_ready_def]) >>
         rename1 `valid_horizon cx st0 h ee.storage_trace` >>
         qexists_tac `h` >>
         qpat_assum `!k. valid_horizon cx st0 k ee.storage_trace ==>
                       stmt_state_rel k ctx func cenv cx ee s /\ _`
           (qspec_then `h` mp_tac) >> simp[]) >>
      rename1 `stmt_state_rel entry_h ctx func cenv cx ee s` >>
      `ctx_has_dalloca ctx ==> allocas_below_fmp s /\
        s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp` by
        (strip_tac >> conj_tac
         >- (qpat_assum `stmt_state_rel entry_h ctx func cenv cx ee s`
               (mp_tac o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
             simp[]) >>
         qpat_assum `stmt_state_rel entry_h ctx func cenv cx ee s`
           (mp_tac o MATCH_MP stateRelProjTheory.stmt_state_rel_fmp_room) >>
         qpat_assum `ctx_has_dalloca ctx` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> simp[fmp_room_def] >> decide_tac) >>
      `ctx_has_dalloca ctx ==> allocas_below_fmp u /\
        u.vs_alloca_next + pending_alloca_size func u <= w2n u.vs_initial_fmp` by
        (PURE_REWRITE_TAC [allocas_below_fmp_def, pending_alloca_size_def] >>
         map_every (fn field => qpat_assum field (PURE_REWRITE_TAC o single))
           [`u.vs_allocas = s.vs_allocas`, `u.vs_alloca_next = s.vs_alloca_next`,
            `u.vs_fmp = s.vs_fmp`, `u.vs_initial_fmp = s.vs_initial_fmp`] >>
         qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s /\ _`
           (ACCEPT_TAC o PURE_REWRITE_RULE [allocas_below_fmp_def, pending_alloca_size_def])) >>
      drule_all extcall_dispatch_abort >> strip_tac >>
      qexistsl_tac [`f`,`Gf`,`tf`] >> simp[] >>
      rpt strip_tac >>
      qpat_assum `take_call_outcome _ _ _ _ _ = _`
        (mp_then (Pat `_ _ = (_,_)`) mp_tac valid_horizon_frame) >>
      simp[storage_trace_frame_take_call]) >>
  `?ea. adopt_call_outcome rq oc consumed = (INL (),ea)` by
    (Cases_on `adopt_call_outcome rq oc consumed` >> drule adopt_call_outcome_frame >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func cenv cx ea u` by fs[] >>
  `u = update_var out 1w t` by simp[] >>
  drule_all extcall_dispatch_adopted_entry >> strip_tac >>
  qabbrev_tac `z = jump_to cont_lbl (next_inst u)` >>
  qabbrev_tac `Gu = step_prov PG G inst u` >>
  qabbrev_tac `tu = step_taint inst s u tn` >>
  `ea.scopes = ee.scopes` by (drule_all extcall_dispatch_adopted_source >> simp[]) >>
  `inst.inst_opcode = (if stat then STATICCALL else CALL) /\
   inst.inst_operands = (if stat then [gas;addr;off;len;buf;Lit (n2w cap)]
     else [gas;addr;value;off;len;buf;Lit (n2w cap)]) /\ inst.inst_outputs = [out]`
    by simp[mk_inst_def] >>
  `u.vs_vars = (update_var out 1w s).vs_vars` by fs[update_var_def] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
      ghost_inv_at (DF H) lo d cenv cx ea Gu tu z /\
      tu.t_mem = tn.t_mem DIFF {j | w2n ro <= j /\ j < w2n ro + LENGTH (TAKE cap oc.co_returnData)}` by
    (qx_gen_tac `h` >> disch_tac >>
     `ghost_inv_at (DF h) lo d cenv cx ee G tn s` by simp[] >>
     qhdtm_assum `extcall_request_ready`
       (strip_assume_tac o REWRITE_RULE [extcall_request_ready_def]) >>
     `stmt_state_rel h ctx func cenv cx ee s` by metis_tac[] >>
     drule stateRelProjTheory.stmt_state_rel_local_ptrs_alloca >> strip_tac >>
     `w2n (n2w cap : bytes32) = cap` by (simp[w2n_n2w] >> decide_tac) >>
     `eval_operand (Lit (n2w cap)) s = SOME (n2w cap)` by simp[eval_operand_def] >>
     `ro' = ro` by fs[] >>
     `lo <= w2n ro` by
       (qpat_assum `FLOOKUP s.vs_allocas live = _` mp_tac >>
        qpat_assum `allocas_from lo s` mp_tac >>
        metis_tac[allocas_from_def]) >>
     `(!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sp x) /\
      (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sp x)`
       by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     Q.SUBGOAL_THEN `n2w cap = (0w:bytes32) \/ lo <= w2n ro` ASSUME_TAC
     >- simp[] >>
     `u.vs_memory =
        (write_memory_with_expansion (w2n ro) (TAKE (w2n (n2w cap : bytes32)) u.vs_returndata) s).vs_memory`
       by simp[] >>
     `!n b k. local_region cenv ee.scopes s n b k ==>
               regions_disjoint (w2n ro) (w2n (n2w cap : bytes32)) b k`
       by (simp[] >> metis_tac[]) >>
     drule_all (Q.INST [`es` |-> `ee:evaluation_state`, `ee` |-> `ea:evaluation_state`]
                extcall_dispatch_write_ghost) >>
     disch_then (qspecl_then [`cont_lbl`,`PG`] mp_tac) >>
     simp[Abbr `z`,Abbr `Gu`,Abbr `tu`]) >>
  qhdtm_assum `extcall_request_ready`
    (strip_assume_tac o REWRITE_RULE [extcall_request_ready_def]) >>
  `tu.t_mem = tn.t_mem DIFF {j | w2n ro <= j /\ j < w2n ro + LENGTH (TAKE cap oc.co_returnData)}` by
    (qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> ghost_inv_at _ _ _ _ _ ea _ _ _ /\ _` drule >> simp[]) >>
  `EVERY (safe_operand sp) [addr;buf;default_op] /\
   EVERY (\p. op_taint tn p = {}) [addr;buf;default_op]` by fs[EVERY_DEF] >>
  `Gu = step_prov PG G inst u /\ tu = step_taint inst s u tn` by simp[Abbr `Gu`,Abbr `tu`] >>
  drule_all extcall_dispatch_return_ghost >> strip_tac >>
  `op_taint tu addr = {} /\ op_taint tu buf = {} /\ op_taint tu default_op = {}` by
    (qpat_assum `EVERY (\p. op_taint tu p = {}) _` mp_tac >> simp[EVERY_DEF,NoAsms]) >>
  `allocas_from lo z` by
    (qpat_assum `z.vs_allocas = s.vs_allocas` (fn th => rewrite_tac [allocas_from_def,th]) >>
     qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  `lo <= z.vs_alloca_next` by ASM_SIMP_TAC bool_ss [] >>
  `IS_SOME default_opt /\ ~is_word_type default_ty ==>
    ?w aid tv. eval_operand default_op z = SOME w /\
      evaluate_type (get_tenv cx) default_ty = SOME tv /\
      FLOOKUP z.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
      aid < sr.cs_next_id` by
    (strip_tac >>
     qpat_assum `IS_SOME default_opt /\ ~is_word_type default_ty ==> _`
       (drule_all_then strip_assume_tac) >>
     `safe_operand sp default_op` by
       (qpat_assum `EVERY (safe_operand sp) [addr;buf;default_op]`
          (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
        disch_then (qspec_then `default_op` mp_tac) >>
        simp[NoAsms]) >>
     `eval_operand default_op z = eval_operand default_op s` by
       (qpat_assum `!p. safe_operand sp p ==> eval_operand p z = _`
          (drule_then ACCEPT_TAC)) >>
     qexistsl_tac [`w`,`aid`,`tv`] >> simp[] >> decide_tac) >>
  qexistsl_tac [`ea`,`z`,`Gu`,`tu`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qx_gen_tac `h` >> disch_tac >>
      `valid_horizon cx st0 h ee.storage_trace` by
        (qpat_assum `!H. valid_horizon _ _ H ea.storage_trace ==> _` drule >> simp[]) >>
      `stor_taint_ok_at (DF h) tn s` by
        (qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> stor_taint_ok_at _ _ _` irule >>
         first_assum ACCEPT_TAC) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac
      >- (qpat_assum `!H. _ /\ stor_taint_ok_at _ _ _ ==> gas_origin_ptr_path _ _ _ _`
            drule_all >>
          qpat_assum `Abbrev (z = _)` (fn th =>
            qpat_assum `oc.co_success` (fn hs =>
              SIMP_TAC bool_ss [REWRITE_RULE [markerTheory.Abbrev_def] th,hs]))) >>
      qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> ghost_inv_at _ _ _ _ _ ea _ _ _ /\ _`
        (irule o cj 1) >>
      first_assum ACCEPT_TAC) >>
  qpat_assum `cap <> 0 ==> ?p b sz w. _` mp_tac >>
  SIMP_TAC bool_ss [arithmeticTheory.ADD_COMM]
QED

Theorem extcall_dispatch_selected_steps:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr value gas buf off len cap target value_opt calldata has_default
    default_op default_ty default_opt ee s /\
  (IS_SOME default_opt /\ ~is_word_type default_ty ==>
    ?w aid tv. eval_operand default_op s = SOME w /\
      evaluate_type (get_tenv cx) default_ty = SOME tv /\
      FLOOKUP s.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
      aid < sp.cs_next_id) /\
  emit_op (if stat then STATICCALL else CALL)
    (if stat then [gas;addr;off;len;buf;Lit (n2w cap)]
     else [gas;addr;value;off;len;buf;Lit (n2w cap)]) sp = (Var out,sj) /\
  inst = mk_inst sp.cs_next_id (if stat then STATICCALL else CALL)
    (if stat then [gas;addr;off;len;buf;Lit (n2w cap)]
     else [gas;addr;value;off;len;buf;Lit (n2w cap)]) [out] /\
  ~not_fresh_at sp out /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  sj.cs_current_bb = s.vs_current_bb /\
  LENGTH sj.cs_current_insts = SUC s.vs_inst_idx /\
  emit_inst JNZ [Var out;Label cont_lbl;Label fail_lbl] [] sj = ((),se) /\
  fn_has_code sj se func /\
  new_block fail_lbl se = (old_fail,sf) /\
  emit_op RETURNDATASIZE [] sf = (zop,sz) /\
  compile_alloc_buffer 0 sz = (rb,sb0) /\
  emit_void RETURNDATACOPY [rb.buf_operand;Lit 0w;zop] sb0 = ((),sc) /\
  emit_inst REVERT [rb.buf_operand;zop] [] sc = ((),sb) /\
  fn_has_code sf sb func /\
  new_block cont_lbl sb = (old_cont,sr) /\
  sp.cs_next_var <= sr.cs_next_var /\
  sp.cs_next_id <= sr.cs_next_id /\
  eval_operand gas s = SOME gw /\
  (!g. OPTION_BIND source_gas dest_NumV = SOME g ==> g = w2n gw) /\
  frame_call_value cx value_opt ee = (INL framed_value,ee) /\
  take_call_outcome (OPTION_BIND source_gas dest_NumV) target calldata framed_value ee =
    (INL (rq,oc),consumed) /\
  EVERY (\p. op_taint tn p = {}) [addr;value;gas;buf;off;len;default_op] /\
  (!ao az. eval_operand off s = SOME ao /\
    eval_operand len s = SOME az ==>
    (az <> 0w ==> (?p. off = Var p /\
      ptr_covers G tn p s (w2n az)) /\
      w2n ao + w2n az <= s.vs_alloca_next) /\
    (!j. w2n ao <= j /\
      j < w2n ao + w2n az ==> j NOTIN tn.t_mem)) /\
  (cap <> 0 ==> ?p. buf = Var p /\
    ptr_covers G tn p s cap) /\
  (!dv. default_opt = SOME dv /\ ~is_word_type default_ty ==>
    ptr_mem_ok cx default_ty dv default_op G tn s /\
    (type_memory_bytes cenv default_ty <> 0 ==>
      (?p. default_op = Var p /\
        ptr_covers G tn p s (type_memory_bytes cenv default_ty)) /\
      (!w. eval_operand default_op s = SOME w ==>
        w2n w + type_memory_bytes cenv default_ty <= s.vs_alloca_next))) /\
  allocas_from lo s /\ alloca_history func s /\
  lo <= s.vs_alloca_next /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx ee G tn s) ==>
  if oc.co_success then
    ?ee' z Gu tu.
      adopt_call_outcome rq oc consumed = (INL (),ee') /\
      extcall_returned st0 ctx func cenv cx ret_type es sa s0 sr addr buf cap target
        has_default default_op default_ty default_opt oc.co_returnData ee' z /\
      (IS_SOME default_opt /\ ~is_word_type default_ty ==>
        ?w aid tv. eval_operand default_op z = SOME w /\
          evaluate_type (get_tenv cx) default_ty = SOME tv /\
          FLOOKUP z.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
          aid < sr.cs_next_id) /\
      (!H. valid_horizon cx st0 H ee'.storage_trace ==>
        valid_horizon cx st0 H ee.storage_trace /\
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
          (OK z,Gu,tu) /\
        ghost_inv_at (DF H) lo d cenv cx ee' Gu tu z) /\
      (!tail. eval_ext_call_effects cx target calldata framed_value source_gas ee.accounts
        (ee with gas_obs := tail) = (INL oc.co_returnData,ee' with gas_obs := tail)) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tu /\
      alloca_history func z /\ allocas_from lo z /\
      lo <= z.vs_alloca_next /\ s0.vs_alloca_next <= z.vs_alloca_next /\
      EVERY (\p. op_taint tu p = {}) [addr;buf;default_op] /\
      (!dv. default_opt = SOME dv /\ ~is_word_type default_ty ==>
        ptr_mem_ok cx default_ty dv default_op Gu tu z /\
        (type_memory_bytes cenv default_ty <> 0 ==>
          ?p b k w. default_op = Var p /\ FLOOKUP Gu p = SOME (b,k) /\
            eval_operand default_op z = SOME w /\ b <= w2n w /\
            w2n w + type_memory_bytes cenv default_ty <= b + k /\
            w2n w + type_memory_bytes cenv default_ty <= z.vs_alloca_next)) /\
      (cap <> 0 ==>
        ?p b k w. buf = Var p /\ FLOOKUP Gu p = SOME (b,k) /\
          eval_operand buf z = SOME w /\ b <= w2n w /\ w2n w + cap <= b + k /\
          (!i. w2n w <= i /\ i < w2n w + MIN cap (LENGTH oc.co_returnData) ==> i NOTIN tu.t_mem))
  else
    ?f Gf tf. f.vs_returndata = oc.co_returnData /\
      (!H. valid_horizon cx st0 H consumed.storage_trace ==>
        valid_horizon cx st0 H ee.storage_trace /\
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
          (Abort Revert_abort f,Gf,tf)) /\
      (!tail. eval_ext_call_effects cx target calldata framed_value source_gas ee.accounts
        (ee with gas_obs := tail) =
        (INR (Error (RevertData oc.co_returnData)),consumed with gas_obs := tail))
Proof
  (MATCH_ACCEPT_TAC extcall_dispatch_selected)
QED
