(*
 * Paired-prefix extension for the N16 opcode family (DELEGATECALL; CREATE; CREATE2).
 *)
Theory concretizePtrCreateFamily
Ancestors
  concretizePtrStorageReadProducer concretizePtrRequestHistory
  concretizePtrMloadRecovery concretizePtrPairedPrefix concretizePtrChronologicalHistory
  concretizePtrStructuralTranscript concretizePtrStructuralTrace concretizePtrDeletedGapHistory
  concretizePtrOrdinaryNext concretizePtrLedgerProbe concretizePtrLedgerAlignment
  concretizePtrSourceOwnership concretizePtrTaggedSupport concretizePtrReturnTransport
  concretizePtrActivationChronology concretizePtrHistoricalWriteClassification
  concretizePtrExactWriteTransport concretizePtrBufferCopyContent
  concretizePtrValueTransport concretizePtrPrefixLedger concretizePtrBytes concretizePtrPairedFields
  concretizePtrComparisonTransport concretizePtrPairedPrefixProbe
  venomMemProps regularCallEmitSim
  concretizeStepStructure concretizeStepShape concretizeStepRetpc concretizeStageShape
  concretizePtrOperationalOpcodes concretizePtrDeletedGaps concretizePtrExecutedCoverage
  concretizePtrAllocationSize unitLabelMapIdentity frameViewFacts
  venomInstProofs opcodeClass venomWf cfgWf memSafeRun
  regularMemorySim o1PassContract unitShapeDefs contextCodegenRel memLocDefs
  pointerConfinedDefs venomInst
  concretizePtrTaintContent ptrDiscipline venomState venomCallOracleDefs
  concretizePtrOpaqueRetpc concretizePtrSharedFields extCallOracle venomExecSemantics list words pred_set arithmetic

Theorem ptr_create_family_current_stores[local]:
  ptr_history_content tn s t /\ tn.t_stor = {} /\ tn.t_trans = {} ==>
  s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient
Proof
  strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    (fs[ptr_history_content_def, ptr_taint_content_def,
        ptr_taint_control_def, concretizePtrOpaqueRetpcTheory.ptr_core_shared_def,
        concretizePtrSharedFieldsTheory.ptr_shared_fields_def]) >>
  `contract_storage s = contract_storage t /\
   contract_transient s = contract_transient t` by
    (fs[ptr_history_content_def, ptr_taint_content_def] >>
     fs[storage_agree_except_def, key_taint_def, contract_storage_def,
        contract_transient_def, word_agree_except_bits,
        FUN_EQ_THM, fcpTheory.CART_EQ]) >>
  fs[ptr_history_content_def, ptr_taint_content_def,
     contract_storage_def, contract_transient_def,
     vfmStateTheory.lookup_account_def] >>
  conj_tac
  >- (simp[FUN_EQ_THM] >> qx_gen_tac `addr` >>
      ` (s.vs_accounts addr).storage = (t.vs_accounts addr).storage` by
        (Cases_on `addr = s.vs_call_ctx.cc_address` >> gvs[]) >>
      qpat_x_assum `!a. _ with storage := _ = _`
        (qspec_then `addr` mp_tac) >>
      simp[vfmStateTheory.account_state_component_equality]) >>
  simp[FUN_EQ_THM] >> metis_tac[]
QED

Theorem ptr_create_family_request[local]:
  ptr_history_content tn s t /\ tn.t_stor = {} /\ tn.t_trans = {} /\
  read_memory (w2n off) (w2n sz) s = read_memory (w2n ot) (w2n sz) t ==>
  venom_create_request s value off sz salt =
  venom_create_request t value ot sz salt
Proof
  strip_tac >> drule_all ptr_create_family_current_stores >>
  simp[venom_create_request_def]
QED

Theorem ptr_create_family_completion[local]:
  ptr_history_content tn s t /\ tn.t_stor = {} /\ tn.t_trans = {} /\
  consume_create_outcome rq s = (w,u) /\
  consume_create_outcome rq t = (v,z) ==>
  w = v /\ u.vs_returndata = z.vs_returndata /\ ptr_history_content tn u z
Proof
  strip_tac >>
  drule_all ptr_create_family_current_stores >> strip_tac >>
  `ptr_request_history (record_request rq s.vs_requests)
     (record_request rq t.vs_requests)` by
    (irule ptr_request_record >> fs[ptr_history_content_def]) >>
  fs[ptr_history_content_def, ptr_taint_content_def, ptr_taint_control_def,
     ptr_core_shared_def, ptr_shared_fields_def] >>
  gvs[consume_create_outcome_eq] >>
  simp[ptr_history_content_def, ptr_taint_content_def, ptr_taint_control_def,
       ptr_core_shared_def, ptr_shared_fields_def,
       contract_storage_def, contract_transient_def,
       storage_agree_except_def, word_agree_except_def]
QED

Theorem ptr_create_family_call_completion[local]:
  ptr_history_content tn s t /\ tn.t_stor = {} /\ tn.t_trans = {} /\
  consume_call_outcome rq ro rz s = (w,u) /\
  consume_call_outcome rq rt rz t = (v,z) ==>
  w = v /\ u.vs_returndata = z.vs_returndata /\ ptr_history_content tn u z
Proof
  strip_tac >>
  drule_all ptr_create_family_current_stores >> strip_tac >>
  `ptr_request_history (record_request rq s.vs_requests)
     (record_request rq t.vs_requests)` by
    (irule ptr_request_record >> fs[ptr_history_content_def]) >>
  fs[ptr_history_content_def, ptr_taint_content_def, ptr_taint_control_def,
     ptr_core_shared_def, ptr_shared_fields_def] >>
  gvs[consume_call_outcome_eq] >>
  simp[ptr_history_content_def, ptr_taint_content_def, ptr_taint_control_def,
       ptr_core_shared_def, ptr_shared_fields_def,
       contract_storage_def, contract_transient_def,
       storage_agree_except_def, word_agree_except_def]
QED

Theorem ptr_create_family_delegate_request[local]:
  ptr_history_content tn s t /\ tn.t_stor = {} /\ tn.t_trans = {} /\
  read_memory (w2n ao) (w2n az) s = read_memory (w2n at) (w2n az) t ==>
  venom_call_request s addr 0w ao az F = venom_call_request t addr 0w at az F
Proof
  strip_tac >> drule_all ptr_create_family_current_stores >> strip_tac >>
  fs[ptr_history_content_def, ptr_taint_content_def, ptr_taint_control_def,
     ptr_core_shared_def, ptr_shared_fields_def] >>
  simp[venom_call_request_def]
QED

Theorem ptr_create_family_execution[local]:
  ptr_history_content tn s t /\ tn.t_stor = {} /\ tn.t_trans = {} /\
  read_memory (w2n off) (w2n sz) s = read_memory (w2n ot) (w2n sz) t /\
  exec_create inst t value ot sz salt = OK z ==>
  ?u. exec_create inst s value off sz salt = OK u /\
      u.vs_returndata = z.vs_returndata /\ ptr_history_content tn u z /\
      (!out. inst.inst_outputs = [out] ==> lookup_var out u = lookup_var out z)
Proof
  strip_tac >>
  `venom_create_request s value off sz salt = venom_create_request t value ot sz salt` by
    (irule ptr_create_family_request >> metis_tac[]) >>
  qpat_x_assum `exec_create _ _ _ _ _ _ = OK _` mp_tac >>
  simp[exec_create_def, AllCaseEqs(), Excl "consume_create_outcome_eq"] >>
  strip_tac >> gvs[Excl "consume_create_outcome_eq"] >>
  Cases_on `consume_create_outcome (venom_create_request t value ot sz salt) s` >>
  Cases_on `consume_create_outcome (venom_create_request t value ot sz salt) t` >>
  gvs[Excl "consume_create_outcome_eq"] >>
  drule_all ptr_create_family_completion >>
  simp[ptr_history_content_update_var, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem ptr_create_family_mixed_execution[local]:
  ptr_mixed_vars births positions TG tn f g s t /\
  ptr_history_content tn s t /\ tn.t_stor = {} /\ tn.t_trans = {} /\
  read_memory (w2n off) (w2n sz) s = read_memory (w2n ot) (w2n sz) t /\
  MEM inst.inst_opcode [CREATE; CREATE2] /\
  inst.inst_outputs = [out] /\ ~retpc_var f out /\
  exec_create inst t value ot sz salt = OK z ==>
  ?u. exec_create inst s value off sz salt = OK u /\
      ptr_history_content tn u z /\
      ptr_mixed_vars births positions (step_prov PT TG inst u)
        (step_taint inst s u tn) f g u z
Proof
  strip_tac >>
  `venom_create_request s value off sz salt = venom_create_request t value ot sz salt` by
    (irule ptr_create_family_request >> metis_tac[]) >>
  qpat_x_assum `exec_create _ _ _ _ _ _ = OK _` mp_tac >>
  simp[exec_create_def, AllCaseEqs(), Excl "consume_create_outcome_eq"] >>
  strip_tac >> gvs[Excl "consume_create_outcome_eq"] >>
  Cases_on `consume_create_outcome (venom_create_request t value ot sz salt) s` >>
  Cases_on `consume_create_outcome (venom_create_request t value ot sz salt) t` >>
  gvs[Excl "consume_create_outcome_eq"] >>
  `q = q' /\ ptr_history_content tn r r'` by
    (drule_all ptr_create_family_completion >> simp[]) >>
  gvs[Excl "consume_create_outcome_eq"] >>
  simp[ptr_history_content_update_var] >>
  `ptr_mixed_vars births positions TG tn f g r r'` by
    (irule ptr_mixed_vars_fields >>
     rpt (goal_assum (drule_at Any)) >>
     qpat_x_assum `consume_create_outcome _ s = _` mp_tac >>
     qpat_x_assum `consume_create_outcome _ t = _` mp_tac >>
     simp[consume_create_outcome_eq] >> rpt strip_tac >> gvs[]) >>
  drule ptr_mixed_vars_update >> disch_then irule >> simp[] >>
  fs[MEM] >>
  simp[step_prov_def, out_prov_def, set_prov_def,
       step_taint_def, set_var_taint_def, out_taint_def,
       finite_mapTheory.FLOOKUP_DRESTRICT, finite_mapTheory.FLOOKUP_UPDATE,
       op_taint_def, concretizePtrValueTransportTheory.ptr_value_transport_def] >>
  rpt strip_tac >> fs[ptr_mixed_vars_def, op_taint_def, word_agree_except_def]
QED

Theorem ptr_create_family_delegate_mixed_execution[local]:
  ptr_mixed_vars births positions TG tn f g s t /\
  ptr_history_content tn s t /\ tn.t_stor = {} /\ tn.t_trans = {} /\
  read_memory (w2n ao) (w2n az) s = read_memory (w2n at) (w2n az) t /\
  inst.inst_opcode = DELEGATECALL /\ inst.inst_outputs = [out] /\ ~retpc_var f out /\
  exec_delegatecall inst t (gas:bytes32) (addr:bytes32) (at:bytes32) (az:bytes32)
    (rt:bytes32) (rz:bytes32) = OK z ==>
  ?u. exec_delegatecall inst s gas addr (ao:bytes32) az (ro:bytes32) rz = OK u /\
      u.vs_returndata = z.vs_returndata /\ ptr_history_content tn u z /\
      ptr_mixed_vars births positions (step_prov PT TG inst u)
        (step_taint inst s u tn) f g u z
Proof
  strip_tac >>
  `venom_call_request s addr 0w ao az F = venom_call_request t addr 0w at az F` by
    (irule ptr_create_family_delegate_request >> metis_tac[]) >>
  qpat_x_assum `exec_delegatecall _ _ _ _ _ _ _ _ = OK _` mp_tac >>
  Cases_on `consume_call_outcome (venom_call_request t addr 0w at az F with
    cr_kind := DelegateMessageCall) (w2n rt) (w2n rz) t` >>
  Cases_on `consume_call_outcome (venom_call_request t addr 0w at az F with
    cr_kind := DelegateMessageCall) (w2n ro) (w2n rz) s` >>
  rename1 `consume_call_outcome _ (w2n rt) _ t = (wt,zt)` >>
  rename1 `consume_call_outcome _ (w2n ro) _ s = (ws,us)` >>
  simp[exec_delegatecall_def, AllCaseEqs(), Excl "consume_call_outcome_eq"] >>
  strip_tac >> gvs[exec_delegatecall_def, Excl "consume_call_outcome_eq"] >>
  `ws = wt /\ us.vs_returndata = zt.vs_returndata /\ ptr_history_content tn us zt` by
    (drule_all ptr_create_family_call_completion >> simp[]) >>
  gvs[Excl "consume_call_outcome_eq"] >>
  `ptr_mixed_vars births positions TG tn f g us zt` by
    (irule ptr_mixed_vars_fields >>
     rpt (goal_assum (drule_at Any)) >>
     qpat_x_assum `consume_call_outcome _ _ _ s = _` mp_tac >>
     qpat_x_assum `consume_call_outcome _ _ _ t = _` mp_tac >>
     simp[consume_call_outcome_eq] >> rpt strip_tac >> gvs[]) >>
  drule ptr_mixed_vars_update >> disch_then irule >> simp[] >>
  simp[step_prov_def, out_prov_def, set_prov_def,
       step_taint_def, set_var_taint_def, out_taint_def,
       finite_mapTheory.FLOOKUP_DRESTRICT, finite_mapTheory.FLOOKUP_UPDATE,
       op_taint_def, concretizePtrValueTransportTheory.ptr_value_transport_def] >>
  rpt strip_tac >> fs[ptr_mixed_vars_def, op_taint_def, word_agree_except_def]
QED

Theorem ptr_create_family_taint[local]:
  taint_ok fn tn inst s /\ MEM inst.inst_opcode [DELEGATECALL; CREATE; CREATE2] ==>
  tn.t_stor = {} /\ tn.t_trans = {} /\
  (!off len j. MEM (off,len) (source_memory_read_ranges inst s) /\ j < len ==>
     off + j NOTIN tn.t_mem) /\
  (!op. MEM op inst.inst_operands ==> op_taint tn op = {})
Proof
  strip_tac >> fs[MEM] >>
  gvs[taint_ok_def, about_to_revert_def] >>
  (conj_tac
   >- (rpt strip_tac >>
       qpat_x_assum `!off len i. _`
         (qspecl_then [`off`, `len`, `off+j`] mp_tac) >> simp[]) >>
   rpt strip_tac >>
   qpat_x_assum `!op. _` (qspec_then `op` mp_tac) >> simp[])
QED

Theorem ptr_create_family_endpoint_taint[local]:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ptr_discipline lo C vs ==>
  taint_ok a.po_fn a.po_taint a.po_inst a.po_state
Proof
  strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def]) >>
  fs[ptr_discipline_def] >> metis_tac[]
QED

Theorem ptr_create_family_input_bytes[local]:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  MEM a.po_inst.inst_opcode [DELEGATECALL; CREATE; CREATE2] /\
  ~in_revert_forward a.po_fn a.po_state /\
  mem_read_ops a.po_inst = SOME ops /\ inst_read_op a.po_inst = SOME ops.iao_ofst /\
  MEM ops.iao_ofst a.po_inst.inst_operands /\
  eval_operand ops.iao_ofst a.po_state = SOME x /\
  eval_operand ops.iao_ofst at.po_state = SOME y /\
  MEM (w2n x,n) (source_memory_read_ranges a.po_inst a.po_state) /\
  ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {} (SOME x) (SOME y) ==>
  read_memory (w2n x) n a.po_state = read_memory (w2n y) n at.po_state
Proof
  strip_tac >>
  `taint_ok a.po_fn a.po_taint a.po_inst a.po_state` by
    (irule ptr_create_family_endpoint_taint >> rpt (goal_assum (drule_at Any))) >>
  `!j. j < n ==> w2n x + j NOTIN a.po_taint.t_mem` by
    (drule_all ptr_create_family_taint >> strip_tac >> metis_tac[]) >>
  simp[read_memory_def, venom_returndata_read_byte] >>
  irule LIST_EQ >> simp[EL_GENLIST] >> rpt strip_tac >>
  `a.po_inst.inst_opcode <> ASSIGN` by fs[MEM] >>
  irule (SIMP_RULE (srw_ss()) [arithmeticTheory.ADD_COMM]
    (SPEC_ALL ptr_paired_read_range_masked_bytes)) >>
  simp[] >>
  conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
  conj_tac >- (qexists_tac `n` >> simp[]) >>
  goal_assum (drule_at (Pat `ptr_paired_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem ptr_create_family_scalar_provenance[local]:
  ptr_use_ok P pv inst /\
  (!v tag. FLOOKUP TG v = SOME tag ==> v IN pv) /\
  ((inst.inst_opcode = CREATE /\ inst.inst_operands = [vop;off;sz]) \/
   (inst.inst_opcode = CREATE2 /\ inst.inst_operands = [vop;off;sz;salt])) ==>
  op_prov TG vop = NONE /\ op_prov TG sz = NONE /\
  (inst.inst_opcode = CREATE2 ==> op_prov TG salt = NONE)
Proof
  strip_tac >>
  `!v. MEM (Var v) (vop::sz::(if inst.inst_opcode = CREATE2 then [salt] else [])) ==>
     v NOTIN pv` by
    (rpt strip_tac >>
     fs[ptr_use_ok_def, is_pointer_preserving_op_def,
        mem_write_ops_def, mem_read_ops_def] >>
     qpat_x_assum `!v. _ ==> _ /\ _` (qspec_then `v` mp_tac) >>
     gvs[] >> rpt strip_tac >> gvs[] >>
     fs[AllCaseEqs()] >> gvs[]) >>
  rpt conj_tac >> rpt strip_tac >>
  Cases_on `vop` >> Cases_on `sz` >> Cases_on `salt` >>
  gvs[op_prov_def] >> metis_tac[optionTheory.option_CASES]
QED

Theorem ptr_create_family_operand_transport[local]:
  ptr_mixed_vars births positions TG tn f g s t /\
  s.vs_labels = t.vs_labels /\
  EVERY (ptr_nonopaque_operand f) inst.inst_operands /\
  taint_ok f tn inst s /\ ptr_use_ok P pv inst /\
  (!v tag. FLOOKUP TG v = SOME tag ==> v IN pv) /\
  ((inst.inst_opcode = CREATE /\ inst.inst_operands = [vop;off;sz]) \/
   (inst.inst_opcode = CREATE2 /\ inst.inst_operands = [vop;off;sz;salt])) /\
  eval_operand vop t = SOME v /\ eval_operand off t = SOME y /\
  eval_operand sz t = SOME n ==>
  ?x. eval_operand vop s = SOME v /\ eval_operand off s = SOME x /\
      eval_operand sz s = SOME n /\
      ptr_lookup_transport births positions (op_prov TG off) {} (SOME x) (SOME y) /\
      (inst.inst_opcode = CREATE2 ==> eval_operand salt s = eval_operand salt t)
Proof
  strip_tac >>
  `op_prov TG vop = NONE /\ op_prov TG sz = NONE /\
   (inst.inst_opcode = CREATE2 ==> op_prov TG salt = NONE)` by
    (irule ptr_create_family_scalar_provenance >> metis_tac[]) >>
  `MEM inst.inst_opcode [DELEGATECALL; CREATE; CREATE2]` by simp[] >>
  `!op. MEM op inst.inst_operands ==> op_taint tn op = {}` by
    (drule_all ptr_create_family_taint >> strip_tac >> simp[]) >>
  `!op. MEM op inst.inst_operands ==>
    ptr_lookup_transport births positions (op_prov TG op) (op_taint tn op)
      (eval_operand op s) (eval_operand op t)` by
    (rpt strip_tac >> irule ptr_mixed_vars_eval >>
     simp[] >> qexistsl_tac [`f`,`g`] >> gvs[EVERY_MEM] >> metis_tac[]) >>
  `ptr_lookup_transport births positions NONE {} (eval_operand vop s) (SOME v) /\
   ptr_lookup_transport births positions NONE {} (eval_operand sz s) (SOME n) /\
   ptr_lookup_transport births positions (op_prov TG off) {}
     (eval_operand off s) (SOME y)` by
    (gvs[] >> metis_tac[]) >>
  Cases_on `eval_operand vop s` >> Cases_on `eval_operand sz s` >>
  Cases_on `eval_operand off s` >>
  gvs[concretizePtrValueTransportTheory.ptr_lookup_transport_def,
      concretizePtrValueTransportTheory.ptr_value_transport_scalar_empty] >>
  qpat_x_assum `!op. _ ==> (case eval_operand op s of NONE => _ | SOME a => _)`
    (qspec_then `salt` mp_tac) >>
  Cases_on `eval_operand salt s` >> Cases_on `eval_operand salt t` >>
  gvs[concretizePtrValueTransportTheory.ptr_lookup_transport_def,
      concretizePtrValueTransportTheory.ptr_value_transport_scalar_empty]
QED

Theorem ptr_create_family_delegate_scalar_provenance[local]:
  ptr_use_ok P pv inst /\
  (!v tag. FLOOKUP TG v = SOME tag ==> v IN pv) /\
  inst.inst_opcode = DELEGATECALL /\
  inst.inst_operands = [gas;addr;off;sz;ret;rsz] ==>
  op_prov TG gas = NONE /\ op_prov TG addr = NONE /\
  op_prov TG sz = NONE /\ op_prov TG rsz = NONE
Proof
  strip_tac >>
  `!v. MEM (Var v) [gas;addr;sz;rsz] ==> v NOTIN pv` by
    (rpt strip_tac >>
     fs[ptr_use_ok_def, is_pointer_preserving_op_def, mem_write_ops_def, mem_read_ops_def] >>
     qpat_x_assum `!v. _ ==> _ /\ _` (qspec_then `v` mp_tac) >>
     gvs[] >> rpt strip_tac >> gvs[] >> fs[AllCaseEqs()] >> gvs[]) >>
  rpt conj_tac >>
  map_every Cases_on [`gas`,`addr`,`sz`,`rsz`] >>
  gvs[op_prov_def] >> metis_tac[optionTheory.option_CASES]
QED

Theorem ptr_create_family_delegate_operand_transport[local]:
  ptr_mixed_vars births positions TG tn f g s t /\
  s.vs_labels = t.vs_labels /\
  EVERY (ptr_nonopaque_operand f) inst.inst_operands /\
  taint_ok f tn inst s /\ ptr_use_ok P pv inst /\
  (!v tag. FLOOKUP TG v = SOME tag ==> v IN pv) /\
  inst.inst_opcode = DELEGATECALL /\ inst.inst_operands = [gas;addr;off;sz;ret;rsz] /\
  eval_operand gas t = SOME gv /\ eval_operand addr t = SOME av /\
  eval_operand off t = SOME ov /\ eval_operand sz t = SOME zv /\
  eval_operand ret t = SOME rv /\ eval_operand rsz t = SOME rzv ==>
  ?x r. eval_operand gas s = SOME gv /\ eval_operand addr s = SOME av /\
    eval_operand off s = SOME x /\ eval_operand sz s = SOME zv /\
    eval_operand ret s = SOME r /\ eval_operand rsz s = SOME rzv /\
    ptr_lookup_transport births positions (op_prov TG off) {} (SOME x) (SOME ov) /\
    ptr_lookup_transport births positions (op_prov TG ret) {} (SOME r) (SOME rv)
Proof
  strip_tac >>
  `op_prov TG gas = NONE /\ op_prov TG addr = NONE /\
   op_prov TG sz = NONE /\ op_prov TG rsz = NONE` by
    (irule ptr_create_family_delegate_scalar_provenance >> metis_tac[]) >>
  `MEM inst.inst_opcode [DELEGATECALL; CREATE; CREATE2]` by simp[] >>
  `!op. MEM op inst.inst_operands ==> op_taint tn op = {}` by
    (drule_all ptr_create_family_taint >> strip_tac >> simp[]) >>
  `!op. MEM op inst.inst_operands ==>
    ptr_lookup_transport births positions (op_prov TG op) (op_taint tn op)
      (eval_operand op s) (eval_operand op t)` by
    (rpt strip_tac >> irule ptr_mixed_vars_eval >>
     simp[] >> qexistsl_tac [`f`,`g`] >> gvs[EVERY_MEM] >> metis_tac[]) >>
  `ptr_lookup_transport births positions NONE {} (eval_operand gas s) (SOME gv) /\
   ptr_lookup_transport births positions NONE {} (eval_operand addr s) (SOME av) /\
   ptr_lookup_transport births positions NONE {} (eval_operand sz s) (SOME zv) /\
   ptr_lookup_transport births positions NONE {} (eval_operand rsz s) (SOME rzv) /\
   ptr_lookup_transport births positions (op_prov TG off) {} (eval_operand off s) (SOME ov) /\
   ptr_lookup_transport births positions (op_prov TG ret) {} (eval_operand ret s) (SOME rv)` by
    (gvs[] >> metis_tac[]) >>
  map_every Cases_on [`eval_operand gas s`,`eval_operand addr s`,`eval_operand sz s`,
    `eval_operand rsz s`,`eval_operand off s`,`eval_operand ret s`] >>
  gvs[concretizePtrValueTransportTheory.ptr_lookup_transport_def,
      concretizePtrValueTransportTheory.ptr_value_transport_scalar_empty]
QED

Theorem ptr_create_family_delegate_endpoint_execution[local]:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\ mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  a.po_inst.inst_opcode = DELEGATECALL /\ ptr_use_ok P pv a.po_inst /\
  (!v tag. FLOOKUP TG v = SOME tag ==> v IN pv) /\
  EVERY (ptr_nonopaque_operand a.po_fn) a.po_inst.inst_operands /\
  a.po_inst.inst_outputs = [out] /\ ~retpc_var a.po_fn out /\
  ~in_revert_forward a.po_fn a.po_state /\
  step_inst fuel C' a.po_inst at.po_state = OK t' ==>
  ?s'. step_inst 0 C a.po_inst a.po_state = OK s' /\
    s'.vs_returndata = t'.vs_returndata /\ ptr_history_content a.po_taint s' t' /\
    ptr_mixed_vars births positions (step_prov PT TG a.po_inst s')
      (step_taint a.po_inst a.po_state s' a.po_taint) a.po_fn at.po_fn s' t'
Proof
  strip_tac >> drule ptr_paired_prefix_endpoint >> strip_tac >>
  `taint_ok a.po_fn a.po_taint a.po_inst a.po_state` by
    (irule ptr_create_family_endpoint_taint >> rpt (goal_assum (drule_at Any))) >>
  `MEM a.po_inst.inst_opcode [DELEGATECALL; CREATE; CREATE2]` by simp[] >>
  `a.po_taint.t_stor = {} /\ a.po_taint.t_trans = {}` by
    (drule_all ptr_create_family_taint >> simp[]) >>
  `ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
      a.po_state at.po_state /\
   ptr_history_content a.po_taint a.po_state at.po_state /\
   a.po_state.vs_labels = at.po_state.vs_labels` by
    (fs[ptr_paired_sample_def] >> metis_tac[ptr_history_content_labels]) >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[step_inst_non_invoke] >> PURE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[] >> PURE_REWRITE_TAC[opcode_case_def] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  `?x r. eval_operand gas_op a.po_state = SOME gas /\
    eval_operand addr_op a.po_state = SOME addr /\
    eval_operand ao_op a.po_state = SOME x /\ eval_operand as_op a.po_state = SOME as_ /\
    eval_operand ro_op a.po_state = SOME r /\ eval_operand rs_op a.po_state = SOME rs /\
    ptr_lookup_transport births positions (op_prov TG ao_op) {} (SOME x) (SOME ao) /\
    ptr_lookup_transport births positions (op_prov TG ro_op) {} (SOME r) (SOME ro)` by
    (irule ptr_create_family_delegate_operand_transport >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `read_memory (w2n x) (w2n as_) a.po_state =
   read_memory (w2n ao) (w2n as_) at.po_state` by
    (irule ptr_create_family_input_bytes >>
     simp[] >> conj_tac
     >- gvs[source_memory_read_ranges_def, mem_read_ops_def,
            memory_range_of_operands_def, eval_operands_def] >>
     goal_assum (drule_at (Pat `ptr_paired_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     rpt (goal_assum (drule_at Any)) >>
     qexists_tac `<|iao_ofst := ao_op; iao_size := SOME as_op;
                    iao_max_size := SOME as_op|>` >>
     gvs[mem_read_ops_def, concretizeMemLocDefsTheory.inst_read_op_def,
         source_memory_read_ranges_def, eval_operands_def]) >>
  simp[] >>
  irule (INST_TYPE [alpha |-> ``:num``, ``:'d`` |-> ``:256``,
                    ``:'g`` |-> ``:256``]
    ptr_create_family_delegate_mixed_execution) >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  qexistsl_tac [`ao`,`ro`,`at.po_state`] >> simp[]
QED

Theorem ptr_create_family_endpoint_execution[local]:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  MEM a.po_inst.inst_opcode [CREATE; CREATE2] /\
  ptr_use_ok P pv a.po_inst /\
  (!v tag. FLOOKUP TG v = SOME tag ==> v IN pv) /\
  EVERY (ptr_nonopaque_operand a.po_fn) a.po_inst.inst_operands /\
  a.po_inst.inst_outputs = [out] /\ ~retpc_var a.po_fn out /\
  ~in_revert_forward a.po_fn a.po_state /\
  step_inst fuel C' a.po_inst at.po_state = OK t' ==>
  ?s'. step_inst 0 C a.po_inst a.po_state = OK s' /\
    ptr_history_content a.po_taint s' t' /\
    ptr_mixed_vars births positions (step_prov PT TG a.po_inst s')
      (step_taint a.po_inst a.po_state s' a.po_taint)
      a.po_fn at.po_fn s' t'
Proof
  strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  `taint_ok a.po_fn a.po_taint a.po_inst a.po_state` by
    (irule ptr_create_family_endpoint_taint >> rpt (goal_assum (drule_at Any))) >>
  `MEM a.po_inst.inst_opcode [DELEGATECALL; CREATE; CREATE2]` by fs[MEM] >>
  `a.po_taint.t_stor = {} /\ a.po_taint.t_trans = {}` by
    (drule_all ptr_create_family_taint >> simp[]) >>
  `ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
      a.po_state at.po_state /\
   ptr_history_content a.po_taint a.po_state at.po_state /\
   a.po_state.vs_labels = at.po_state.vs_labels` by
    (fs[ptr_paired_sample_def] >> metis_tac[ptr_history_content_labels]) >>
  `a.po_state.vs_call_ctx = at.po_state.vs_call_ctx` by
    fs[ptr_history_content_def, ptr_taint_content_def, ptr_taint_control_def,
       ptr_core_shared_def, ptr_shared_fields_def] >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  gvs[MEM] >>
  simp[step_inst_non_invoke] >> PURE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[] >> PURE_REWRITE_TAC[opcode_case_def] >>
  simp[AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  `?saltop.
    (a.po_inst.inst_opcode = CREATE /\
     a.po_inst.inst_operands = [val_op;off_op;sz_op]) \/
    (a.po_inst.inst_opcode = CREATE2 /\
     a.po_inst.inst_operands = [val_op;off_op;sz_op;saltop])` by metis_tac[] >> gs[] >>
  `?x. eval_operand val_op a.po_state = SOME value /\
       eval_operand off_op a.po_state = SOME x /\
       eval_operand sz_op a.po_state = SOME sz /\
       ptr_lookup_transport births positions (op_prov TG off_op) {}
         (SOME x) (SOME offset) /\
       (a.po_inst.inst_opcode = CREATE2 ==>
         eval_operand saltop a.po_state = eval_operand saltop at.po_state)` by
    (irule ptr_create_family_operand_transport >>
     rpt (goal_assum (drule_at Any)) >> simp[] >>
     conj_tac >- (qexistsl_tac [`P`,`pv`] >> simp[]) >>
     qexistsl_tac [`a.po_fn`,`at.po_fn`,`a.po_taint`] >> simp[]) >>
  `read_memory (w2n x) (w2n sz) a.po_state =
   read_memory (w2n offset) (w2n sz) at.po_state` by
    (irule ptr_create_family_input_bytes >>
     simp[] >> conj_tac
     >- gvs[source_memory_read_ranges_def, mem_read_ops_def,
            memory_range_of_operands_def, eval_operands_def] >>
     goal_assum (drule_at (Pat `ptr_paired_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     rpt (goal_assum (drule_at Any)) >>
     qexists_tac `<|iao_ofst := off_op; iao_size := SOME sz_op;
                    iao_max_size := SOME sz_op|>` >>
     gvs[mem_read_ops_def, concretizeMemLocDefsTheory.inst_read_op_def, source_memory_read_ranges_def,
         eval_operands_def]) >>
  gvs[eval_operands_def] >>
  irule (INST_TYPE [alpha |-> ``:num``] ptr_create_family_mixed_execution) >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  qexistsl_tac [`offset`,`at.po_state`] >> simp[]
QED

Theorem ptr_paired_prefix_create_successor[local]:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  MEM a.po_inst.inst_opcode [CREATE; CREATE2] /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt ==>
  ?z TG'.
    TG' = step_prov PT TG a.po_inst z.po_state /\
    ptr_paired_prefix R lp positions lo vs C C'
      (h ++ [z]) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      tokens registry births PT TG' saved entries
      (H ++ [(tokens,registry,births,PT,TG',saved,entries)]) calls ws
Proof
  strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def]) >>
  `MEM a.po_fn C.ctx_functions` by (drule_all ptr_frame_sizes >> simp[]) >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> metis_tac[]) >>
  `MEM a.po_inst (fn_insts a.po_fn) /\ inst_wf a.po_inst` by
    (`MEM a.po_inst (fn_insts a.po_fn)` by
       (fs[active_inst_def, fn_insts_MEM] >> metis_tac[MEM_EL]) >>
     fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def,
        wf_function_def, fn_inst_wf_def, EVERY_MEM, fn_insts_MEM] >> metis_tac[]) >>
  `?out. a.po_inst.inst_outputs = [out]` by
    (fs[MEM] >> gvs[inst_wf_def, listTheory.LENGTH_EQ_NUM_compute]) >>
  `a.po_inst.inst_opcode <> ALLOCA /\ a.po_inst.inst_opcode <> NOP /\
   a.po_inst.inst_opcode <> INVOKE /\ a.po_inst.inst_opcode <> ASSIGN /\
   a.po_inst.inst_opcode <> PHI /\ a.po_inst.inst_opcode <> RETPC_PARAM /\
   ~is_terminator a.po_inst.inst_opcode` by (fs[MEM] >> simp[is_terminator_def]) >>
  `~retpc_var a.po_fn out` by
    (irule noncopy_output_not_retpc >>
     conj_tac >- fs[EVERY_MEM] >> qexists_tac `a.po_inst` >> simp[]) >>
  `at.po_inst = a.po_inst` by simp[concretize_positions_unchanged] >>
  `ALL_DISTINCT (fn_labels a.po_fn)` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
  `~in_revert_forward a.po_fn a.po_state` by
    (fs[in_revert_forward_def, active_inst_def] >> rpt strip_tac >>
     `lookup_block a.po_state.vs_current_bb a.po_fn.fn_blocks = SOME bb` by
       (irule venomExecProofsTheory.MEM_lookup_block >> fs[fn_labels_def]) >>
     gvs[] >>
     `get_instruction bb a.po_state.vs_inst_idx = SOME a.po_inst` by
       simp[get_instruction_def] >>
     drule_all memSafeRunTheory.revert_forward_at_opcode >> fs[MEM]) >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def,
        EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >> metis_tac[]) >>
  `EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) C.ctx_functions` by
    (fs[ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  `!v tag. FLOOKUP TG v = SOME tag ==> v IN fn_pv P a.po_fn` by
    (rpt strip_tac >> irule ptr_source_tagged_var_support >>
     rpt (goal_assum (drule_at Any))) >>
  `fn_ptr_ok P a.po_fn /\ opaque_use_ok a.po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM] >> metis_tac[]) >>
  `ptr_use_ok P (fn_pv P a.po_fn) a.po_inst` by
    (fs[fn_ptr_ok_def] >> metis_tac[]) >>
  `EVERY (ptr_nonopaque_operand a.po_fn) a.po_inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> simp[] >> fs[MEM]) >>
  qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality] >>
  strip_tac >> gvs[Excl "MEM"] >>
  IF (qpat_assum `step_inst _ _ _ _ = OK _` (K all_tac)) all_tac
    (qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
     simp[step_inst_non_invoke] >> strip_tac >>
     drule step_inst_base_intret_opcodes >> fs[MEM]) >>
  `?post. step_inst 0 C a.po_inst a.po_state = OK post /\
    ptr_history_content a.po_taint post s' /\
    ptr_mixed_vars births positions (step_prov PT TG a.po_inst post)
      (step_taint a.po_inst a.po_state post a.po_taint) a.po_fn at.po_fn post s'` by
    (irule ptr_create_family_endpoint_execution >>
     rpt (goal_assum (drule_at Any)) >> simp[] >>
     conj_tac >- metis_tac[] >>
     conj_tac >- (qexistsl_tac [`P`,`fn_pv P a.po_fn`] >> simp[]) >>
     goal_assum (drule_at (Pat `ptr_paired_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `is_ext_call_op a.po_inst.inst_opcode` by (fs[MEM] >> simp[is_ext_call_op_def]) >>
  qpat_assum `step_inst 0 C _ _ = OK post`
    (mp_then Any mp_tac venomInstProofsTheory.step_ext_call_preserves) >>
  simp[] >> strip_tac >>
  qpat_assum `step_inst fuel C' _ _ = OK s'`
    (mp_then Any mp_tac venomInstProofsTheory.step_ext_call_preserves) >>
  simp[] >> strip_tac >>
  `?i. active_inst a.po_fn i (post with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    (`EVERY bb_well_formed a.po_fn.fn_blocks` by
       (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
     irule ptr_ordinary_next_active >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  qabbrev_tac `z = ptr_ledger_next a i post` >>
  qexists_tac `z` >>
  `ALL_DISTINCT (fn_labels at.po_fn)` by
    (fs[concretizePtrPairedFieldsTheory.ptr_paired_code_def] >> metis_tac[fn_labels_def, concretize_positions_labels]) >>
  drule ptr_paired_stage_local_allocas >>
  disch_then (qspecl_then [`o1_walk_view rpolicy 2`,`rpolicy`] mp_tac) >>
  simp[] >> strip_tac >>
  `ptr_paired_sample positions z zt
     (tokens,registry,births,PT,step_prov PT TG a.po_inst z.po_state,saved,entries)` by
    (simp[ptr_paired_sample_def, Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >>
     (reverse conj_tac
      >- (irule ptr_history_content_masks >> goal_assum (drule_at Any) >>
          fs[MEM] >> simp[step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def])) >>
     gvs[step_prov_def, out_prov_def] >>
     irule ptr_mixed_vars_fields >> rpt (goal_assum (drule_at Any)) >>
     simp[step_taint_def]) >>
  `ptr_paired_params positions z zt
     (tokens,registry,births,PT,step_prov PT TG a.po_inst z.po_state,saved,entries)` by
    (fs[concretizePtrPairedFieldsTheory.ptr_paired_params_def,
        Abbr `z`, ptr_ledger_next_def, ptr_observe_def]) >>
  drule ptr_paired_prefix_ordinary_nonwrite >> disch_then irule >>
  simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def, ptr_tagged_step_def] >>
  fs[MEM] >> simp[step_prov_def, out_prov_def, step_writes_def,
       range_bytes_def, codegenRelTheory.source_memory_write_ranges_def] >>
  qexistsl_tac [`0`,`post`] >> simp[]
QED

Theorem ptr_create_family_delegate_structural_successor[local]:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  a.po_inst.inst_opcode = DELEGATECALL /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt ==>
  ?z TG'.
    TG' = step_prov PT TG a.po_inst z.po_state /\
    ptr_structural_transcript R vs C C' (h ++ [z]) z (ht ++ [zt]) zt
      (done ++ [LENGTH h - 1]) tokens registry births PT TG' saved entries
      (H ++ [(tokens,registry,births,PT,TG',saved,entries)]) /\
    ptr_paired_sample positions z zt (tokens,registry,births,PT,TG',saved,entries) /\
    ptr_paired_params positions z zt (tokens,registry,births,PT,TG',saved,entries) /\
    ptr_paired_code R lp positions z.po_fn zt.po_fn /\
    ptr_paired_cursor lp z zt /\
    z.po_stack = a.po_stack /\ zt.po_stack = at.po_stack /\
    z.po_state.vs_returndata = zt.po_state.vs_returndata /\
    ptr_tagged_chrono_step C (HD tokens) a z PT TG saved PT TG' saved
Proof
  strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def]) >>
  `MEM a.po_fn C.ctx_functions` by (drule_all ptr_frame_sizes >> simp[]) >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> metis_tac[]) >>
  `MEM a.po_inst (fn_insts a.po_fn) /\ inst_wf a.po_inst` by
    (`MEM a.po_inst (fn_insts a.po_fn)` by
       (fs[active_inst_def, fn_insts_MEM] >> metis_tac[MEM_EL]) >>
     fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def,
        wf_function_def, fn_inst_wf_def, EVERY_MEM, fn_insts_MEM] >> metis_tac[]) >>
  `?out. a.po_inst.inst_outputs = [out]` by
    gvs[inst_wf_def, listTheory.LENGTH_EQ_NUM_compute] >>
  `a.po_inst.inst_opcode <> ALLOCA /\ a.po_inst.inst_opcode <> NOP /\
   a.po_inst.inst_opcode <> INVOKE /\ a.po_inst.inst_opcode <> ASSIGN /\
   a.po_inst.inst_opcode <> PHI /\ a.po_inst.inst_opcode <> RETPC_PARAM /\
   ~is_terminator a.po_inst.inst_opcode` by simp[is_terminator_def] >>
  `~retpc_var a.po_fn out` by
    (irule noncopy_output_not_retpc >>
     conj_tac >- fs[EVERY_MEM] >> qexists_tac `a.po_inst` >> simp[]) >>
  `at.po_inst = a.po_inst` by simp[concretize_positions_unchanged] >>
  `ALL_DISTINCT (fn_labels a.po_fn)` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
  `~in_revert_forward a.po_fn a.po_state` by
    (fs[in_revert_forward_def, active_inst_def] >> rpt strip_tac >>
     `lookup_block a.po_state.vs_current_bb a.po_fn.fn_blocks = SOME bb` by
       (irule venomExecProofsTheory.MEM_lookup_block >> fs[fn_labels_def]) >>
     gvs[] >>
     `get_instruction bb a.po_state.vs_inst_idx = SOME a.po_inst` by
       simp[get_instruction_def] >>
     drule_all memSafeRunTheory.revert_forward_at_opcode >> simp[]) >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def,
        EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >> metis_tac[]) >>
  `EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) C.ctx_functions` by
    (fs[ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  `!v tag. FLOOKUP TG v = SOME tag ==> v IN fn_pv P a.po_fn` by
    (rpt strip_tac >> irule ptr_source_tagged_var_support >>
     rpt (goal_assum (drule_at Any))) >>
  `fn_ptr_ok P a.po_fn /\ opaque_use_ok a.po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM] >> metis_tac[]) >>
  `ptr_use_ok P (fn_pv P a.po_fn) a.po_inst` by
    (fs[fn_ptr_ok_def] >> metis_tac[]) >>
  `EVERY (ptr_nonopaque_operand a.po_fn) a.po_inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> simp[]) >>
  qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality] >>
  strip_tac >> gvs[Excl "MEM"] >>
  IF (qpat_assum `step_inst _ _ _ _ = OK _` (K all_tac)) all_tac
    (qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
     simp[step_inst_non_invoke] >> strip_tac >>
     drule step_inst_base_intret_opcodes >> simp[]) >>
  `?post. step_inst 0 C a.po_inst a.po_state = OK post /\
    post.vs_returndata = s'.vs_returndata /\
    ptr_history_content a.po_taint post s' /\
    ptr_mixed_vars births positions (step_prov PT TG a.po_inst post)
      (step_taint a.po_inst a.po_state post a.po_taint) a.po_fn at.po_fn post s'` by
    (irule ptr_create_family_delegate_endpoint_execution >>
     rpt (goal_assum (drule_at Any)) >> simp[] >>
     conj_tac >- metis_tac[] >>
     conj_tac >- (qexistsl_tac [`P`,`fn_pv P a.po_fn`] >> simp[]) >>
     goal_assum (drule_at (Pat `ptr_paired_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `is_ext_call_op a.po_inst.inst_opcode` by simp[is_ext_call_op_def] >>
  qpat_assum `step_inst 0 C _ _ = OK post`
    (mp_then Any mp_tac venomInstProofsTheory.step_ext_call_preserves) >>
  simp[] >> strip_tac >>
  qpat_assum `step_inst fuel C' _ _ = OK s'`
    (mp_then Any mp_tac venomInstProofsTheory.step_ext_call_preserves) >>
  simp[] >> strip_tac >>
  `?i. active_inst a.po_fn i (post with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    (`EVERY bb_well_formed a.po_fn.fn_blocks` by
       (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
     irule ptr_ordinary_next_active >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  qabbrev_tac `z = ptr_ledger_next a i post` >>
  qexists_tac `z` >> simp[] >>
  `ALL_DISTINCT (fn_labels at.po_fn)` by
    (fs[concretizePtrPairedFieldsTheory.ptr_paired_code_def] >> metis_tac[fn_labels_def, concretize_positions_labels]) >>
  drule ptr_paired_stage_local_allocas >>
  disch_then (qspecl_then [`o1_walk_view rpolicy 2`,`rpolicy`] mp_tac) >>
  simp[] >> strip_tac >>
  `ptr_paired_sample positions z zt
     (tokens,registry,births,PT,step_prov PT TG a.po_inst z.po_state,saved,entries)` by
    (simp[ptr_paired_sample_def, Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >>
     (reverse conj_tac
      >- (irule ptr_history_content_masks >> goal_assum (drule_at Any) >>
          simp[step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def])) >>
     gvs[step_prov_def, out_prov_def] >>
     irule ptr_mixed_vars_fields >> rpt (goal_assum (drule_at Any)) >>
     simp[step_taint_def]) >>
  `ptr_paired_params positions z zt
     (tokens,registry,births,PT,step_prov PT TG a.po_inst z.po_state,saved,entries)` by
    (fs[concretizePtrPairedFieldsTheory.ptr_paired_params_def,
        Abbr `z`, ptr_ledger_next_def, ptr_observe_def]) >>
  `ptr_tagged_chrono_step C (HD tokens) a z PT TG saved
     PT (step_prov PT TG a.po_inst z.po_state) saved` by
    ( `ptr_tagged_step (HD tokens) PT TG a.po_inst post =
       step_prov PT TG a.po_inst z.po_state` by
        simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def,
             ptr_tagged_step_def, step_prov_def, out_prov_def] >>
      `~is_terminator a.po_inst.inst_opcode /\
       a.po_inst.inst_opcode <> INVOKE` by simp[] >>
      qpat_assum `step_inst 0 C _ _ = OK post`
        (mp_then (Pat `step_inst _ _ _ _ = _`) mp_tac
          (cj 1 ptr_tagged_chrono_step_rules)) >>
      simp[] >> disch_then drule >> strip_tac >>
      `ptr_observe a.po_stack a.po_params a.po_prov a.po_taint
         a.po_fn a.po_inst a.po_state = a` by
        simp[NoAsms, ptr_observe_def, ptr_observation_component_equality] >>
      fs[Abbr `z`, ptr_ledger_next_def] >> metis_tac[]) >>
  conj_tac
  >- (drule ptr_ownership_overlay_fixed >> strip_tac >>
      drule (cj 3 ptr_structural_transcript_rules) >>
      disch_then drule >> disch_then drule >>
      simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def,
           ptr_activation_tokens_def, ptr_activation_registry_def]) >>
  simp[] >> conj_tac
  >- simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >>
  conj_tac
  >- (drule ptr_ordinary_next_cursor >> disch_then irule >>
      simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def]) >>
  simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def]
QED

Theorem ptr_create_family_delegate_written_byte[local]:
  exec_delegatecall inst s gas addr ao az ro rz = OK t /\
  j < MIN (w2n rz) (LENGTH t.vs_returndata) ==>
  read_byte (w2n ro + j) t.vs_memory = EL j t.vs_returndata
Proof
  strip_tac >>
  qpat_x_assum `exec_delegatecall _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[exec_delegatecall_def, AllCaseEqs()] >> strip_tac >>
  gvs[update_var_def] >>
  simp[read_byte_write_memory_with_expansion, LENGTH_TAKE_EQ, EL_TAKE,
       MIN_DEF] >> gvs[MIN_DEF]
QED

Theorem ptr_create_family_delegate_chrono_operands[local]:
  a.po_inst.inst_opcode = DELEGATECALL /\ ptr_chrono_step C a z ==>
  ?gas_op addr_op ao_op az_op ro_op rz_op gas addr ao az ro rz post.
    a.po_inst.inst_operands = [gas_op;addr_op;ao_op;az_op;ro_op;rz_op] /\
    eval_operand gas_op a.po_state = SOME gas /\
    eval_operand addr_op a.po_state = SOME addr /\
    eval_operand ao_op a.po_state = SOME ao /\
    eval_operand az_op a.po_state = SOME az /\
    eval_operand ro_op a.po_state = SOME ro /\
    eval_operand rz_op a.po_state = SOME rz /\
    exec_delegatecall a.po_inst a.po_state gas addr ao az ro rz = OK post /\
    z.po_state = post with vs_inst_idx := SUC a.po_state.vs_inst_idx
Proof
  strip_tac >> qpat_x_assum `ptr_chrono_step _ _ _` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality, is_terminator_def] >>
  strip_tac >> gvs[] >>
  IF (qpat_assum `step_inst _ _ _ _ = OK _` (K all_tac)) all_tac
    (qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
     simp[step_inst_non_invoke] >> strip_tac >>
     drule step_inst_base_intret_opcodes >> simp[]) >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >> PURE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[] >> PURE_REWRITE_TAC[opcode_case_def] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  rpt (goal_assum (drule_at Any))
QED

Theorem ptr_create_family_delegate_chrono_written_byte[local]:
  a.po_inst.inst_opcode = DELEGATECALL /\ ptr_chrono_step C a z /\
  a.po_inst.inst_operands = [gas_op;addr_op;ao_op;az_op;ro_op;rz_op] /\
  eval_operand ro_op a.po_state = SOME ro /\
  eval_operand rz_op a.po_state = SOME rz /\
  j < MIN (w2n rz) (LENGTH z.po_state.vs_returndata) ==>
  read_byte (w2n ro+j) z.po_state.vs_memory = EL j z.po_state.vs_returndata
Proof
  strip_tac >> drule_all ptr_create_family_delegate_chrono_operands >>
  strip_tac >> gvs[] >>
  drule ptr_create_family_delegate_written_byte >>
  disch_then (qspec_then `j` mp_tac) >> simp[ADD_COMM]
QED

Theorem ptr_create_family_delegate_write_certificate[local]:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  a.po_inst.inst_opcode = DELEGATECALL /\ at.po_inst = a.po_inst /\
  ptr_chrono_step C a z /\ ptr_chrono_step C' at zt /\
  z.po_state.vs_returndata = zt.po_state.vs_returndata /\
  range_bytes (step_writes a.po_inst a.po_state z.po_state) <> {} ==>
  ?rho. ptr_paired_write lo positions C C' (h ++ [z]) (ht ++ [zt])
    (done ++ [LENGTH h - 1])
    (H ++ [(tokens,registry,births,PT,TG',saved,entries)])
    (LENGTH h - 1,LENGTH ht - 1,rho)
Proof
  strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def]) >>
  `MEM a.po_fn C.ctx_functions` by (drule_all ptr_frame_sizes >> simp[]) >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> metis_tac[]) >>
  `~in_revert_forward a.po_fn a.po_state` by
    (`ALL_DISTINCT (fn_labels a.po_fn)` by
       (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
     qpat_x_assum `active_inst a.po_fn a.po_inst a.po_state` mp_tac >>
     simp[active_inst_def] >> strip_tac >>
     `lookup_block a.po_state.vs_current_bb a.po_fn.fn_blocks = SOME bb` by
       (irule venomExecProofsTheory.MEM_lookup_block >> fs[fn_labels_def]) >>
     `get_instruction bb a.po_state.vs_inst_idx = SOME a.po_inst` by
       simp[get_instruction_def] >>
     simp[in_revert_forward_def] >> strip_tac >>
     drule_all memSafeRunTheory.revert_forward_at_opcode >> simp[]) >>
  `access_ok lo a.po_prov a.po_fn a.po_inst a.po_state /\
   taint_ok a.po_fn a.po_taint a.po_inst a.po_state` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  `fn_ptr_ok P a.po_fn` by fs[EVERY_MEM] >>
  `EVERY (\fn. EVERY inst_wf (fn_insts fn)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, fn_inst_wf_def,
        EVERY_MEM, fn_insts_MEM] >> metis_tac[]) >>
  `EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions` by
    (fs[ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  `!v tag. FLOOKUP TG v = SOME tag ==> v IN fn_pv P a.po_fn` by
    (rpt strip_tac >> irule ptr_source_tagged_var_support >>
     rpt (goal_assum (drule_at Any))) >>
  `opaque_use_ok a.po_fn /\ MEM a.po_inst (fn_insts a.po_fn)` by
    (conj_tac
     >- (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM] >> metis_tac[]) >>
     fs[active_inst_def, fn_insts_MEM] >> metis_tac[MEM_EL]) >>
  `ptr_use_ok P (fn_pv P a.po_fn) a.po_inst` by
    (fs[fn_ptr_ok_def] >> metis_tac[]) >>
  `EVERY (ptr_nonopaque_operand a.po_fn) a.po_inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> simp[]) >>
  `ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
    a.po_state at.po_state /\ a.po_state.vs_labels = at.po_state.vs_labels` by
    (fs[ptr_paired_sample_def] >> metis_tac[ptr_history_content_labels]) >>
  qpat_assum `ptr_chrono_step C' at zt`
    (mp_then (Pat `ptr_chrono_step _ _ _`) mp_tac
      ptr_create_family_delegate_chrono_operands) >>
  simp[] >> strip_tac >>
  rename1 `a.po_inst.inst_operands = [gas_op;addr_op;ao_op;az_op;ro_op;rz_op]` >>
  `?x r. eval_operand gas_op a.po_state = SOME gas /\
    eval_operand addr_op a.po_state = SOME addr /\
    eval_operand ao_op a.po_state = SOME x /\ eval_operand az_op a.po_state = SOME az /\
    eval_operand ro_op a.po_state = SOME r /\ eval_operand rz_op a.po_state = SOME rz /\
    ptr_lookup_transport births positions (op_prov TG ao_op) {} (SOME x) (SOME ao) /\
    ptr_lookup_transport births positions (op_prov TG ro_op) {} (SOME r) (SOME ro)` by
    (irule ptr_create_family_delegate_operand_transport >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `!j. j < MIN (w2n rz) (LENGTH z.po_state.vs_returndata) ==>
    read_byte (w2n r+j) z.po_state.vs_memory =
    read_byte (w2n ro+j) zt.po_state.vs_memory` by
    (rpt strip_tac >>
     `read_byte (w2n r+j) z.po_state.vs_memory = EL j z.po_state.vs_returndata` by
       (irule ptr_create_family_delegate_chrono_written_byte >>
        rpt (goal_assum (drule_at Any)) >> simp[]) >>
     `read_byte (w2n ro+j) zt.po_state.vs_memory = EL j zt.po_state.vs_returndata` by
       (qpat_assum `exec_delegatecall _ at.po_state _ _ _ _ _ _ = OK post`
          (mp_then Any mp_tac ptr_create_family_delegate_written_byte) >>
        disch_then (qspec_then `j` mp_tac) >>
        gvs[]) >> simp[]) >>
  suspend "classify"
QED
Resume ptr_create_family_delegate_write_certificate[classify]:
  `0 < LENGTH h` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_end >> strip_tac >> Cases_on `h` >> gvs[]) >>
  drule ptr_structural_trace_embedding >> strip_tac >>
  drule ptr_structural_trace_target >> strip_tac >>
  drule ptr_chrono_history_end >> strip_tac >>
  `SUC (LENGTH h - 1) = LENGTH h /\ SUC (LENGTH done) = LENGTH ht /\
   LENGTH ht - 1 = LENGTH done` by decide_tac >>
  `EL (LENGTH done) ht = at` by
    (qpat_x_assum `LAST ht = at` mp_tac >> simp[LAST_EL, PRE_SUB1]) >>
  `ptr_stage_placements C' positions` by fs[ptr_paired_prefix_def] >>
  qpat_assum `ptr_structural_transcript R vs C C' h a ht at done tokens registry births PT TG saved entries H`
    (mp_tac o MATCH_MP ptr_structural_transcript_endpoint) >> strip_tac >>
  `EL (LENGTH h - 1) H = (tokens,registry,births,PT,TG,saved,entries)` by
    (`H <> []` by (Cases_on `H` >> gvs[]) >>
     qpat_x_assum `LAST H = _` mp_tac >> simp[LAST_EL, PRE_SUB1]) >>
  `EL (LENGTH h - 1) h = a` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_end >> strip_tac >>
     qpat_x_assum `LAST h = a` mp_tac >> simp[LAST_EL, PRE_SUB1]) >>
  `0 < w2n rz` by
    (qpat_x_assum `range_bytes _ <> {}` mp_tac >>
     simp[step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
          range_bytes_def, pred_setTheory.EXTENSION, MIN_DEF] >>
     rpt strip_tac >> gvs[] >> decide_tac) >>
  qabbrev_tac `ops = <|iao_ofst := ro_op; iao_size := NONE; iao_max_size := SOME rz_op|>` >>
  `(op_prov TG ops.iao_ofst = NONE /\
    op_taint (EL (LENGTH h - 1) h).po_taint ops.iao_ofst = {} /\ w2n r + w2n rz <= lo) \/
   (?dv token bid db sb pb. ops.iao_ofst = Var dv /\ FLOOKUP TG dv = SOME (token,bid) /\
    FLOOKUP (EL (LENGTH h - 1) h).po_prov dv = SOME (db,sb) /\
    FLOOKUP positions (Allocation bid) = SOME (pb,sb) /\ db <= w2n r /\
    w2n r + w2n rz <= db+sb /\ pb+sb < dimword(:256))` by
    (irule (Q.INST [`ops` |-> `ops`] (SPEC_ALL ptr_historical_write_classification)) >>
     simp[Abbr `ops`, mem_write_ops_def, codegenRelTheory.source_memory_write_ranges_def] >>
     conj_tac >- (Cases_on `rz = 0w` >> gvs[]) >>
     conj_tac >- (qexists_tac `a.po_fn` >> simp[]) >>
     rpt (goal_assum (drule_at Any)) >> simp[])
  >- suspend "fixed" >>
  suspend "owned"
QED
Resume ptr_create_family_delegate_write_certificate[fixed]:
  fs[Abbr `ops`] >>
  `SUC (LENGTH h - 1) = LENGTH h` by decide_tac >>
  `ro = r` by
    (gvs[ptr_lookup_transport_def, ptr_value_transport_def] >>
     gvs[word_agree_except_bits, fcpTheory.CART_EQ]) >>
  qexists_tac `\x:num. x` >>
  simp[ptr_paired_write_def, EL_APPEND_EQN] >>
  reverse conj_tac
  >- (simp[ptr_paired_write_owner_def, step_writes_def,
        codegenRelTheory.source_memory_write_ranges_def, range_bytes_def] >>
      rpt strip_tac >> disj1_tac >> fs[MIN_DEF] >> decide_tac) >>
  simp[ptr_ledger_write_pair_def, is_terminator_def, ptr_bytes_agree_def,
       step_writes_def, codegenRelTheory.source_memory_write_ranges_def, range_bytes_def] >>
  rpt strip_tac >>
  rename1 `read_byte b z.po_state.vs_memory = _` >>
  `b = w2n r + (b-w2n r) /\
   b-w2n r < w2n rz /\ b-w2n r < LENGTH z.po_state.vs_returndata` by
    (fs[MIN_DEF] >> decide_tac) >>
  qpat_x_assum `!j. j < w2n rz /\ _ ==> _` (qspec_then `b-w2n r` mp_tac) >>
  simp[ADD_COMM]
QED
Resume ptr_create_family_delegate_write_certificate[owned]:
  fs[Abbr `ops`] >>
  `SUC (LENGTH h - 1) = LENGTH h` by decide_tac >>
  `MEM token tokens` by
    (drule_all ptr_source_ownership_live_prov >> simp[]) >>
  `FLOOKUP births (token,bid) = SOME (db,sb)` by
    (drule_all ptr_source_ownership_prov_erases >>
     simp[ptr_ledger_erases_def] >> strip_tac >>
     first_x_assum (qspec_then `dv` mp_tac) >> gvs[]) >>
  `ro = r - n2w db + n2w pb` by
    gvs[ptr_lookup_transport_def, ptr_value_transport_def, op_prov_def] >>
  `w2n ro = pb + (w2n r - db)` by
    (irule ptr_closed_relocation_value >> simp[] >> qexists_tac `sb` >> simp[] >> decide_tac) >>
  qpat_x_assum `ro = r - n2w db + n2w pb` kall_tac >>
  qexists_tac `\b:num. pb + (b-db)` >>
  simp[ptr_paired_write_def, EL_APPEND_EQN] >>
  reverse conj_tac
  >- (simp[ptr_paired_write_owner_def, step_writes_def,
        codegenRelTheory.source_memory_write_ranges_def, range_bytes_def] >>
      rpt strip_tac >> disj2_tac >>
      rename1 `b < w2n r + _` >>
      qexistsl_tac [`token`,`bid`,`db`,`sb`,`pb`,`b-db`] >> simp[] >>
      fs[MIN_DEF] >> decide_tac) >>
  simp[ptr_ledger_write_pair_def, is_terminator_def] >>
  conj_tac
  >- (simp[step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
        range_bytes_def] >> rpt strip_tac >> decide_tac) >>
  simp[ptr_bytes_agree_def, step_writes_def,
       codegenRelTheory.source_memory_write_ranges_def, range_bytes_def] >>
  rpt strip_tac >> rename1 `read_byte b z.po_state.vs_memory = _` >>
  `b = w2n r + (b-w2n r) /\ b-w2n r < w2n rz /\
   b-w2n r < LENGTH z.po_state.vs_returndata /\
   pb + (b-db) = w2n ro + (b-w2n r)` by
    (fs[MIN_DEF] >> decide_tac) >>
  qpat_x_assum `!j. j < w2n rz /\ _ ==> _` (qspec_then `b-w2n r` mp_tac) >>
  simp[ADD_COMM]
QED
Finalise ptr_create_family_delegate_write_certificate

Theorem ptr_paired_prefix_delegate_successor[local]:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  a.po_inst.inst_opcode = DELEGATECALL /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt ==>
  ?z TG' ws'. TG' = step_prov PT TG a.po_inst z.po_state /\
    ptr_paired_prefix R lp positions lo vs C C'
      (h ++ [z]) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      tokens registry births PT TG' saved entries
      (H ++ [(tokens,registry,births,PT,TG',saved,entries)]) calls ws'
Proof
  strip_tac >> drule_all ptr_create_family_delegate_structural_successor >> strip_tac >>
  qexistsl_tac [`z`,`TG'`] >> gvs[] >>
  Cases_on `range_bytes (step_writes a.po_inst a.po_state z.po_state) = {}`
  >- (qexists_tac `ws` >> irule concretizePtrPairedNextAttachTheory.ptr_paired_prefix_nonwrite_attach >>
      rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `at.po_inst = a.po_inst` by simp[concretize_positions_unchanged] >>
  `ptr_chrono_step C a z` by (drule ptr_tagged_chrono_step_projection >> simp[]) >>
  drule_all ptr_create_family_delegate_write_certificate >>
  disch_then (qspec_then `step_prov PT TG a.po_inst z.po_state` mp_tac) >>
  disch_then (qx_choose_then `reloc` assume_tac) >>
  qexists_tac `ws ++ [(LENGTH h - 1,LENGTH ht - 1,reloc)]` >>
  suspend "attach"
QED
Resume ptr_paired_prefix_delegate_successor[attach]:
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  `LAST h = a` by metis_tac[ptr_chrono_history_end] >>
  `EVERY (\n. SUC n < LENGTH h) done` by
    (qpat_assum `ptr_structural_transcript _ _ _ _ (h ++ _) _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     disch_then (strip_assume_tac o MATCH_MP ptr_structural_transcript_erasure) >>
     drule ptr_structural_trace_embedding >>
     simp[concretizePtrEventEmbeddingTheory.ptr_event_embedding_def, EVERY_EL] >> strip_tac >>
     gen_tac >> strip_tac >>
     qpat_x_assum `!i j. _` (qspecl_then [`n`,`LENGTH done`] mp_tac) >>
     simp[EL_APPEND_EQN] >> fs[ptr_paired_prefix_def, ptr_paired_samples_def,
       ptr_sample_list_def] >> decide_tac) >>
  `LENGTH ht = SUC (LENGTH done)` by
    (drule ptr_structural_trace_embedding >>
     simp[concretizePtrEventEmbeddingTheory.ptr_event_embedding_def]) >>
  `LENGTH ht - 1 = LENGTH done` by decide_tac >>
  fs[ptr_paired_prefix_def] >>
  conj_tac >- (irule ptr_paired_samples_pair >> simp[]) >>
  conj_tac >- (irule ptr_paired_alignment_pair >> simp[]) >>
  conj_tac >- (irule ptr_paired_callers_retained >> simp[] >>
    fs[ptr_paired_samples_def, ptr_sample_list_def] >> qexistsl_tac [`a`,`at`] >> simp[]) >>
  irule ptr_paired_writes_pair >> simp[] >>
  fs[ptr_paired_samples_def, ptr_sample_list_def]
QED
Finalise ptr_paired_prefix_delegate_successor

Theorem ptr_paired_create_prefix_normalize:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  LIST_REL (ptr_paired_code R lp positions) C.ctx_functions C'.ctx_functions /\
  EVERY (\f. fn_inst_wf f /\ retpc_shape_ok f /\ opaque_use_ok f /\
    first_block_no_phi f /\ EVERY bb_well_formed f.fn_blocks /\
    ALL_DISTINCT (fn_labels f) /\
    (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions /\
  EVERY (\g. ALL_DISTINCT (fn_labels g)) C'.ctx_functions /\
  (!f g. ptr_paired_code R lp positions f g ==> g.fn_name = f.fn_name) /\
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  a.po_inst.inst_opcode <> NOP /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt /\ MEM a.po_inst.inst_opcode [DELEGATECALL; CREATE; CREATE2] ==>
  ?delta z tokens' registry' births' PT' TG' saved' entries' snapshots calls' ws'.
    delta <> [] /\ LENGTH snapshots = LENGTH delta /\
    ptr_paired_prefix R lp positions lo vs C C'
      (h ++ delta) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      tokens' registry' births' PT' TG' saved' entries'
      (H ++ snapshots) calls' ws' /\
    z.po_inst.inst_opcode <> NOP /\
    zt.po_inst = concretize_inst_with_positions (lp z.po_fn) z.po_inst
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?z TG' ws'. TG' = step_prov PT TG a.po_inst z.po_state /\
    ptr_paired_prefix R lp positions lo vs C C'
      (h ++ [z]) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      tokens registry births PT TG' saved entries
      (H ++ [(tokens,registry,births,PT,TG',saved,entries)]) calls ws'` by
    (Cases_on `a.po_inst.inst_opcode = DELEGATECALL`
     >- (drule_all ptr_paired_prefix_delegate_successor >> metis_tac[]) >>
     `MEM a.po_inst.inst_opcode [CREATE; CREATE2]` by fs[] >>
     drule_all ptr_paired_prefix_create_successor >> metis_tac[]) >>
  `fn_inst_wf z.po_fn` by
    (qpat_assum `ptr_paired_prefix _ _ _ _ _ _ _ (_ ++ [_]) _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac ptr_paired_prefix_transcript) >> strip_tac >>
     drule ptr_structural_transcript_erasure >> strip_tac >>
     drule ptr_structural_trace_source >> strip_tac >>
     drule ptr_chrono_history_reachable >> strip_tac >>
     fs[ptr_observation_reachable_def] >>
     drule ptr_frame_context_membership >> strip_tac >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  qpat_assum `ptr_paired_prefix _ _ _ _ _ _ _ (_ ++ [_]) _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_then Any mp_tac ptr_paired_prefix_normalize) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`[z] ++ delta`, `ptr_gap_scan bb (LENGTH delta) z`,
    `tokens`, `registry`, `births`, `PT`, `TG'`, `saved`, `entries`,
    `[(tokens,registry,births,PT,TG',saved,entries)] ++ snapshots`, `calls`, `ws'`] >>
  simp[APPEND_ASSOC, ptr_gap_scan_fields]
QED

