(* Selected CALL and status jump on the same physical and linked cursors. *)
Theory bodyExtDispatchSelectedMods
Ancestors
  bodyFullExtCallDispatch bodyExtStatusWriteFrameMods bodyExtStatusWriteGhostMods
  bodyFullHashKeccakFixed[qualified,ignore_grammar] bodyInvSplit bodyFullPostsMods
  bodyFullShadowBodyInv
  exprBopSimProps[qualified,ignore_grammar] exprSimProps[qualified,ignore_grammar]
  exprSimExtCallCase valueEncodingProps venomState allocaHistory
  abiStaticLoopBody exprLoweringProps exprSafeOperand compileEnv loweringPosts
  emitHelperProps words vyperCallOutcomeProps vyperCallOutcome
  vyperInterpreter vyperState fragGasEmitCtrl fragGasOriginPtr
  venomInst venomInstProps venomExecSemantics ptrDiscipline finite_map
  bodyFullRawCallCallOrigin fragGasOriginPtrLoop fragExec list bodyFullRawCallFailure exprSimRawCallCalldata emitHelper context rich_list
  bodyFullRawCallCallFrame bodyFullRawCallCallStorage bodyPtrDefs
  ghostPcTransportPtr bodyFullShared memLocDefs codegenRel unitTransformDefs pred_set
  decoderGhostFramePtr contextCodegenRel loweringStateRelDefs
  vyperStorageTrace vyperStorageFootprint vyperFiniteStoragePreservation exprSimRawCall extCallOracleStep
  stateRelProj[qualified,ignore_grammar] venomMemDefs[qualified,ignore_grammar]
  bodyFullUnwrapRun[qualified,ignore_grammar] bodyPtrBopRepresentationFrame[qualified,ignore_grammar]

Theorem selected_status_counted[local]:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr value gas buf off len cap target value_opt calldata has_default
    default_op default_ty default_opt ee s /\
  inst.inst_opcode = (if stat then STATICCALL else CALL) /\
  inst.inst_operands = (if stat then [gas;addr;off;len;buf;Lit (n2w cap)]
                       else [gas;addr;value;off;len;buf;Lit (n2w cap)]) /\
  inst.inst_outputs = [out] /\
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
  alloca_history func u /\ u.vs_data_section = s.vs_data_section /\
  !D. stor_taint_ok_at D tn s ==>
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (jump_to (if success then cont_lbl else fail_lbl) (next_inst u)),
       step_prov PG G inst u, step_taint inst s u tn)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `step_inst 0 ctx inst s = OK u /\ ~is_terminator inst.inst_opcode` by
    (Cases_on `stat` >> simp[step_inst_non_invoke,is_terminator_def]) >>
  conj_tac
  >- (drule_all step_preserves_control_flow >> strip_tac >>
      irule alloca_history_frame >> qexists_tac `s` >> simp[]) >>
  conj_tac >- drule_all_then ACCEPT_TAC venomInstPropsTheory.step_preserves_data_section >>
  qhdtm_assum `extcall_request_ready`
    (strip_assume_tac o REWRITE_RULE [extcall_request_ready_def]) >>
  `stmt_state_rel H ctx func cenv cx ee s` by simp[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (drule_then ACCEPT_TAC bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
  drule stateRelProjTheory.stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  `cap < dimword (:256)` by decide_tac >>
  `w2n (n2w cap : bytes32) = cap` by (simp[w2n_n2w] >> decide_tac) >>
  `eval_operand (Lit (n2w cap)) s = SOME (n2w cap)` by simp[eval_operand_def] >>
  `w2n ro + cap <= s.vs_alloca_next` by
    (fs[venomMemDefsTheory.alloca_inv_def,venomMemDefsTheory.alloca_next_valid_def] >>
     qpat_x_assum `!aid base sz. _ ==> _` drule >> decide_tac) >>
  qpat_assum `!ao az. eval_operand off s = SOME ao /\ _ ==> _` (drule_all_then strip_assume_tac) >>
  `inst_mem_below_frontier inst s` by
    (Cases_on `eval_operand gas s` >> Cases_on `stat` >>
     simp[inst_mem_below_frontier_def,source_memory_write_ranges_def,
       source_memory_read_ranges_def,mem_write_ops_def,mem_read_ops_def,
       memory_range_of_operands_def] >> Cases_on `az = 0w` >> fs[] >> decide_tac) >>
  `EVERY (\p. op_taint tn p = {}) inst.inst_operands` by
    (Cases_on `stat` >> fs[op_taint_def]) >>
  gen_tac >> strip_tac >>
  irule extcall_dispatch_status_path >> ASM_SIMP_TAC bool_ss [] >>
  rpt conj_tac
  >- (qexists_tac `bb` >> simp[NoAsms] >> metis_tac[]) 
  >- (qexistsl_tac [`addr`,`ao`,`az`,`len`,`off`,`gas`,`Lit (n2w cap)`,
                    `n2w cap`,`ro`,`buf`,`stat`,`value`] >>
      ASM_SIMP_TAC bool_ss [w2n_n2w] >> metis_tac[])
  >> qexistsl_tac [`out`,`se`,`sj`,`t`] >> ASM_SIMP_TAC bool_ss []
QED

Theorem selected_default_bytes[local]:
  regions_disjoint (w2n (ro:bytes32)) cap (w2n (w:bytes32)) (val_footprint tv dv) /\
  u.vs_memory = (write_memory_with_expansion (w2n ro) (TAKE cap rd) s).vs_memory ==>
  mem_bytes_at (w2n w) (val_footprint tv dv) u.vs_memory =
  mem_bytes_at (w2n w) (val_footprint tv dv) s.vs_memory
Proof
  strip_tac >> simp[] >> irule write_memory_mem_bytes_at_disjoint >>
  fs[regions_disjoint_def,LENGTH_TAKE_EQ] >> IF_CASES_TAC >> decide_tac
QED

Theorem selected_live_frame[local]:
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
  qhdtm_assum `extcall_request_ready`
    (strip_assume_tac o REWRITE_RULE [extcall_request_ready_def]) >>
  `ro' = ro` by fs[] >>
  `!dv dw tv. default_opt = SOME dv /\ ~is_word_type default_ty /\
      eval_operand default_op s = SOME dw /\ evaluate_type (get_tenv cx) default_ty = SOME tv ==>
      mem_bytes_at (w2n dw) (val_footprint tv dv) u.vs_memory =
      mem_bytes_at (w2n dw) (val_footprint tv dv) s.vs_memory` by
    (rpt strip_tac >> irule selected_default_bytes >>
     qexistsl [`cap`,`rd`,`ro`] >> simp[] >>
     qpat_assum `!d w tv. default_opt = SOME d /\ _ ==> _`
       (qspecl_then [`dv`,`dw`,`tv`] mp_tac) >> fs[]) >>
  conj_tac
  >- (`wb_frame cenv es ee sa s0 u` by
        (`t.vs_allocas = s.vs_allocas /\ t.vs_memory = u.vs_memory` by
           (qpat_assum `u = update_var _ _ _` (fn th => fs[th,update_var_def])) >>
         `~not_fresh_at sa out` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
         qpat_assum `u = update_var _ _ _` SUBST1_TAC >>
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
  simp[extcall_default_ready_def] >> qx_gen_tac `dv` >> disch_tac >>
  qpat_assum `!dv. default_opt = SOME dv ==> _` drule >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `tv` (qx_choose_then `rtv` (qx_choose_then `dw` strip_assume_tac)))) >>
  `expr_val_rel cx default_ty dv default_op u` by
    (Cases_on `is_word_type default_ty`
     >- (`eval_operand default_op s = SOME (typed_val_to_w256 tv dv)` by
           (irule exprBopSimPropsTheory.expr_val_rel_typed >>
            qexistsl_tac [`cx`,`default_ty`] >> simp[]) >>
         fs[expr_val_rel_def]) >>
     irule exprSimPropsTheory.expr_val_rel_footprint_agree >> simp[] >>
     metis_tac[]) >>
  gvs[]
QED

(* A live allocation row is used for every observed module, with its actual
   ALLOCA instruction; the copied length can be smaller than its capacity. *)
Theorem selected_write_separation[local]:
  immutable_frame_mods func cenv cx ee s /\ eval_operand buf s = SOME ro /\
  (cenv.ce_is_ctor /\ cap <> 0 ==> ?i w n.
    MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
    eval_operand buf s = SOME w /\ FLOOKUP s.vs_allocas i.inst_id = SOME (w2n w,n) /\
    cap <= n) /\ cenv.ce_is_ctor /\ TAKE cap rd <> [] ==>
  !src tops name tv v off.
    ALOOKUP cenv.ce_modules src = SOME tops /\
    FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
             | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
    regions_disjoint (w2n ro) (LENGTH (TAKE cap rd)) off (type_memory_size tv)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cap <> 0` by (strip_tac >> fs[]) >>
  qpat_x_assum `cenv.ce_is_ctor /\ cap <> 0 ==> _` (drule_all_then strip_assume_tac) >>
  `w = ro` by fs[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `immutable_frame_mods _ _ _ _ _`
    (assume_tac o CONJUNCT2 o REWRITE_RULE [immutable_frame_mods_def]) >>
  fs[immutable_alloca_sep_mods_def] >>
  qpat_x_assum `!src tops. ALOOKUP _ _ = SOME _ ==> _` drule >>
  simp[immutable_alloca_sep_def] >> strip_tac >>
  qpat_x_assum `!name tv v off. _ ==> _` (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!inst b sz. _ ==> _` (drule_all_then mp_tac) >>
  simp[regions_disjoint_def] >>
  `LENGTH (TAKE cap rd) <= cap` by simp[LENGTH_TAKE_EQ] >> decide_tac
QED

Theorem selected_return_ghost[local]:
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
      fs[ptr_covers_def,GSYM eval_operand_def] >> gvs[]) >>
  strip_tac >>
  Q.SUBGOAL_THEN `?p. buf = Var p /\ ptr_covers G tn p s cap`
    (qx_choose_then `bp` (CONJUNCTS_THEN2 SUBST_ALL_TAC
       (STRIP_ASSUME_TAC o REWRITE_RULE [ptr_covers_def])))
  >- metis_tac[] >>
  gvs[eval_operand_def,LENGTH_TAKE_EQ,arithmeticTheory.MIN_DEF]
QED

Theorem selected_abort_room[local]:
  stmt_state_rel H ctx func cenv cx ee s /\
  u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
  u.vs_fmp = s.vs_fmp /\ u.vs_initial_fmp = s.vs_initial_fmp ==>
  ctx_has_dalloca ctx ==> allocas_below_fmp u /\
    u.vs_alloca_next + pending_alloca_size func u <= w2n u.vs_initial_fmp
Proof
  strip_tac >> disch_tac >> conj_tac
  >- (`allocas_below_fmp s` by
        drule_all_then ACCEPT_TAC bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >>
      fs[allocas_below_fmp_def] >> first_assum ACCEPT_TAC) >>
  drule stateRelProjTheory.stmt_state_rel_fmp_room >>
  simp[fmp_room_def,pending_alloca_size_def] >> decide_tac
QED

Theorem extcall_dispatch_selected_mods:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr value gas buf off len cap target value_opt calldata has_default
    default_op default_ty default_opt ee s /\
  immutable_frame_mods func cenv cx ee s /\
  (cenv.ce_is_ctor /\ cap <> 0 ==> ?i w n.
    MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
    eval_operand buf s = SOME w /\ FLOOKUP s.vs_allocas i.inst_id = SOME (w2n w,n) /\
    cap <= n) /\
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
  (!H. valid_horizon cx st0 H ee.storage_trace ==> ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s) ==>
  if oc.co_success then
    ?ee' z Gu tu.
      adopt_call_outcome rq oc consumed = (INL (),ee') /\
      extcall_returned st0 ctx func cenv cx ret_type es sa s0 sr addr buf cap target
        has_default default_op default_ty default_opt oc.co_returnData ee' z /\
      immutable_frame_mods func cenv cx ee' z /\
      (IS_SOME default_opt /\ ~is_word_type default_ty ==>
        ?w aid tv. eval_operand default_op z = SOME w /\
          evaluate_type (get_tenv cx) default_ty = SOME tv /\
          FLOOKUP z.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
          aid < sr.cs_next_id) /\
      (!H. valid_horizon cx st0 H ee'.storage_trace ==>
        valid_horizon cx st0 H ee.storage_trace /\
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gu,tu) /\
        ghost_inv_at_mods (DF H) lo d cenv cx ee' Gu tu z) /\
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
  `inst.inst_opcode = (if stat then STATICCALL else CALL) /\
   inst.inst_operands = (if stat then [gas;addr;off;len;buf;Lit (n2w cap)]
     else [gas;addr;value;off;len;buf;Lit (n2w cap)]) /\ inst.inst_outputs = [out]`
    by simp[mk_inst_def] >>
  `EVERY (\p. op_taint tn p = {}) [addr;value;gas;buf;off;len]` by fs[EVERY_DEF] >>
  drule_all (Q.INST [`success` |-> `oc.co_success`] selected_status_counted) >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qhdtm_assum `extcall_request_ready`
    (strip_assume_tac o REWRITE_RULE [extcall_request_ready_def]) >>
  `stmt_state_rel H ctx func cenv cx ee s` by simp[] >>
  `!h. valid_horizon cx st0 h ee.storage_trace ==> stor_taint_ok_at (DF h) tn s` by
    (gen_tac >> strip_tac >>
     `ghost_inv_at_mods (DF h) lo d cenv cx ee G tn s` by
       (first_x_assum (drule_then ACCEPT_TAC)) >>
     qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >> first_assum ACCEPT_TAC) >>
  reverse (Cases_on `oc.co_success`) >> simp[]
  >- suspend "abort" >>
  `?ea. adopt_call_outcome rq oc consumed = (INL (),ea)` by
    (Cases_on `adopt_call_outcome rq oc consumed` >> drule adopt_call_outcome_frame >> simp[]) >>
  drule_all extcall_dispatch_adopted_source >> strip_tac >>
  `!h. valid_horizon cx st0 h ee.storage_trace ==> stmt_state_rel h ctx func cenv cx ea u` by fs[] >>
  `u = update_var out 1w t` by simp[] >>
  drule_all selected_live_frame >> strip_tac >>
  `!h. valid_horizon cx st0 h ea.storage_trace ==>
       stmt_state_rel h ctx func cenv cx ea u /\ storage_well_formed_on cx ea (FST h)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!h. valid_horizon _ _ h ea.storage_trace ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  Q.SUBGOAL_THEN
    `?h:(bool # bytes32 # type_value) list # num list. stmt_state_rel h ctx func cenv cx ea u`
    ASSUME_TAC >- (qexists_tac `H` >> simp[]) >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by simp[] >>
  drule_all extcall_dispatch_returned >> strip_tac >>
  qabbrev_tac `z = jump_to cont_lbl (next_inst u)` >>
  qabbrev_tac `Gu = step_prov PG G inst u` >>
  qabbrev_tac `tu = step_taint inst s u tn` >>
  `immutable_frame_mods func cenv cx ea z` by suspend "immutable" >>
  `!h. valid_horizon cx st0 h ee.storage_trace ==>
      ghost_inv_at_mods (DF h) lo d cenv cx ea Gu tu z /\
      tu.t_mem = tn.t_mem DIFF {j | w2n ro <= j /\ j < w2n ro + LENGTH (TAKE cap oc.co_returnData)}` by
    suspend "ghost" >>
  suspend "pack"
QED

Resume extcall_dispatch_selected_mods[abort]:
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by
    (conj_tac
     >- (qpat_assum `u.vs_allocas = s.vs_allocas`
           (fn th => pure_rewrite_tac[allocas_from_def,th]) >>
         qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
     simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u /\
    u.vs_alloca_next + pending_alloca_size func u <= w2n u.vs_initial_fmp` by
    (drule (REWRITE_RULE [GSYM AND_IMP_INTRO] selected_abort_room) >>
     disch_then (qspec_then `u` mp_tac) >> simp[]) >>
  `!h. valid_horizon cx st0 h ee.storage_trace ==>
       gas_origin_ptr_path (DF h,lo,explicit,ctx,func,PG) (s,G,tn) []
         (OK (jump_to fail_lbl (next_inst u)),step_prov PG G inst u,step_taint inst s u tn)` by
    (gen_tac >> disch_tac >>
     `stor_taint_ok_at (DF h) tn s` by (first_x_assum (drule_then ACCEPT_TAC)) >>
     qpat_assum `!D. stor_taint_ok_at D tn s ==> _` (qspec_then `DF h` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     qpat_assum `~oc.co_success` (fn th => pure_rewrite_tac[th,COND_CLAUSES]) >>
     disch_then ACCEPT_TAC) >>
  drule_all extcall_dispatch_abort >> strip_tac >>
  qexistsl_tac [`f`,`Gf`,`tf`] >> simp[] >>
  rpt strip_tac >>
  qpat_assum `take_call_outcome _ _ _ _ _ = _`
    (mp_then (Pat `_ _ = (_,_)`) mp_tac valid_horizon_frame) >>
  simp[storage_trace_frame_take_call]
QED

Resume extcall_dispatch_selected_mods[immutable]:
  `!x. not_fresh_at sp x ==> lookup_var x z = lookup_var x s` by
    (rpt strip_tac >> `x <> out` by metis_tac[] >>
     simp[Abbr `z`,jump_to_def,next_inst_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE]) >>
  `z.vs_data_section = s.vs_data_section` by
    (simp_tac (srw_ss()) [Abbr `z`,jump_to_def,next_inst_def] >> first_assum ACCEPT_TAC) >>
  irule (INST_TYPE [``:'a`` |-> ``:256``] extcall_status_write_immutable_frame_mods) >>
  qexistsl [`cap`,`ee`,`oc.co_returnData`,`ro`,`s`,`sp`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >-
    (strip_tac >> rpt gen_tac >> strip_tac >>
     irule selected_write_separation >>
     qpat_assum `immutable_frame_mods func cenv cx ee s` (irule_at Any) >>
     qpat_assum `eval_operand buf s = SOME ro` (irule_at Any) >>
     qpat_assum `ALOOKUP cenv.ce_modules _ = SOME _` (irule_at Any) >>
     qpat_assum `FLOOKUP cenv.ce_module_vars _ = SOME (ImmutableLoc _)` (irule_at Any) >>
     qpat_assum `FLOOKUP (case ALOOKUP ee.immutables _ of _ => _ | _ => _) _ = SOME _`
       (irule_at Any) >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[]
QED

Resume extcall_dispatch_selected_mods[ghost]:
  qx_gen_tac `h` >> disch_tac >>
  `ghost_inv_at_mods (DF h) lo d cenv cx ee G tn s` by simp[] >>
  drule stateRelProjTheory.stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  `w2n (n2w cap : bytes32) = cap` by (simp[w2n_n2w] >> decide_tac) >>
  `eval_operand (Lit (n2w cap)) s = SOME (n2w cap)` by simp[eval_operand_def] >>
  `ro' = ro` by fs[] >>
  `lo <= w2n ro` by
    (qpat_assum `FLOOKUP s.vs_allocas live = _` mp_tac >>
     qpat_assum `allocas_from lo s` mp_tac >> metis_tac[allocas_from_def]) >>
  `(!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sp x) /\
   (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sp x)`
    by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `u.vs_vars = (update_var out 1w s).vs_vars` by fs[update_var_def] >>
  Q.SUBGOAL_THEN `n2w cap = (0w:bytes32) \/ lo <= w2n ro` ASSUME_TAC
  >- (disj2_tac >> first_assum ACCEPT_TAC) >>
  `u.vs_memory =
     (write_memory_with_expansion (w2n ro) (TAKE (w2n (n2w cap : bytes32)) u.vs_returndata) s).vs_memory`
    by simp[] >>
  `!n b k. local_region cenv ee.scopes s n b k ==>
            regions_disjoint (w2n ro) (w2n (n2w cap : bytes32)) b k`
    by (simp[] >> metis_tac[]) >>
  drule_all (Q.INST [`es` |-> `ee:evaluation_state`, `ee` |-> `ea:evaluation_state`]
             extcall_dispatch_write_ghost_mods) >>
  disch_then (qspecl_then [`cont_lbl`,`PG`] mp_tac) >>
  simp[Abbr `z`,Abbr `Gu`,Abbr `tu`]
QED

Resume extcall_dispatch_selected_mods[pack]:
  `tu.t_mem = tn.t_mem DIFF {j | w2n ro <= j /\ j < w2n ro + LENGTH (TAKE cap oc.co_returnData)}` by
    (qpat_assum `!h. valid_horizon _ _ h ee.storage_trace ==> ghost_inv_at_mods _ _ _ _ _ ea _ _ _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `EVERY (safe_operand sp) [addr;buf;default_op] /\
   EVERY (\p. op_taint tn p = {}) [addr;buf;default_op]` by fs[EVERY_DEF] >>
  `Gu = step_prov PG G inst u /\ tu = step_taint inst s u tn` by simp[Abbr `Gu`,Abbr `tu`] >>
  drule_all selected_return_ghost >> strip_tac >>
  `allocas_from lo z` by
    (qpat_assum `z.vs_allocas = s.vs_allocas`
       (fn th => pure_rewrite_tac[allocas_from_def,th]) >>
     qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  `IS_SOME default_opt /\ ~is_word_type default_ty ==>
    ?w aid tv. eval_operand default_op z = SOME w /\
      evaluate_type (get_tenv cx) default_ty = SOME tv /\
      FLOOKUP z.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
      aid < sr.cs_next_id` by
    (strip_tac >> qpat_assum `IS_SOME default_opt /\ ~is_word_type default_ty ==> _`
       (drule_all_then strip_assume_tac) >>
     `safe_operand sp default_op` by
       (qpat_assum `EVERY (safe_operand sp) [addr;buf;default_op]` mp_tac >>
        simp_tac (srw_ss()) [EVERY_DEF]) >>
     qexistsl_tac [`w`,`aid`,`tv`] >> simp[] >> decide_tac) >>
  qexistsl_tac [`ea`,`z`,`Gu`,`tu`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qx_gen_tac `h` >> disch_tac >>
      `valid_horizon cx st0 h ee.storage_trace` by
        (qpat_assum `!h. valid_horizon _ _ h ea.storage_trace ==> valid_horizon _ _ h ee.storage_trace /\ _`
           (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      reverse conj_tac
      >- (qpat_assum `!h. valid_horizon _ _ h ee.storage_trace ==> ghost_inv_at_mods _ _ _ _ _ ea _ _ _ /\ _`
            (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
      `stor_taint_ok_at (DF h) tn s` by (first_x_assum (drule_then ACCEPT_TAC)) >>
      qpat_assum `!D. stor_taint_ok_at D tn s ==> _` (qspec_then `DF h` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      qpat_assum `oc.co_success` (fn th => pure_rewrite_tac[th,COND_CLAUSES]) >>
      qpat_assum `Abbrev (z = _)`
        (fn th => pure_once_rewrite_tac[REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
      disch_then ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qpat_assum `z.vs_alloca_next = s.vs_alloca_next`
        (fn th => pure_rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qpat_assum `EVERY (\p. op_taint tu p = {}) [addr;buf;default_op]` mp_tac >>
      simp_tac (srw_ss()) [EVERY_DEF]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `cap <> 0 ==> ?p b sz w. buf = Var p /\ _` mp_tac >>
  simp_tac (srw_ss()) [arithmeticTheory.ADD_COMM]
QED

Finalise extcall_dispatch_selected_mods
