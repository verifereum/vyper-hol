(*
 * Paired-prefix extension for the N16 opcode family (DELEGATECALL; CREATE; CREATE2).
 *)
Theory concretizePtrCreateFamily
Ancestors
  concretizePtrStorageReadProducer concretizePtrRequestHistory
  concretizePtrTaintContent ptrDiscipline venomState venomCallOracleDefs
  concretizePtrOpaqueRetpc concretizePtrSharedFields extCallOracle venomExecSemantics list words pred_set

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

Theorem ptr_create_family_delegate_state[local]:
  ptr_history_content tn s t /\ tn.t_stor = {} /\ tn.t_trans = {} ==>
  make_venom_delegatecall_state s target gas data code static =
  make_venom_delegatecall_state t target gas data code static
Proof
  strip_tac >> drule_all ptr_create_family_current_stores >> strip_tac >>
  fs[ptr_history_content_def, ptr_taint_content_def, ptr_taint_control_def,
     ptr_core_shared_def, ptr_shared_fields_def] >>
  simp[make_venom_delegatecall_state_def, venom_to_tx_params_def]
QED

Theorem ptr_create_family_delegate_extract[local]:
  ptr_history_content tn s t /\ tn.t_stor = {} /\ tn.t_trans = {} /\
  extract_venom_result s output ro rz result = SOME (w,u) /\
  extract_venom_result t output rt rz result = SOME (v,z) ==>
  w = v /\ u.vs_returndata = z.vs_returndata /\ ptr_history_content tn u z
Proof
  strip_tac >> drule_all ptr_create_family_current_stores >> strip_tac >>
  fs[ptr_history_content_def, ptr_taint_content_def, ptr_taint_control_def,
     ptr_core_shared_def, ptr_shared_fields_def] >>
  gvs[extract_venom_result_def, AllCaseEqs()] >>
  Cases_on `result'`
  >- (gvs[] >>
      simp[ptr_history_content_def, ptr_taint_content_def, ptr_taint_control_def,
           ptr_core_shared_def, ptr_shared_fields_def,
           contract_storage_def, contract_transient_def,
           storage_agree_except_def, word_agree_except_def]) >>
  Cases_on `y` >> gvs[] >>
  simp[ptr_history_content_def, ptr_taint_content_def, ptr_taint_control_def,
       ptr_core_shared_def, ptr_shared_fields_def,
       contract_storage_def, contract_transient_def,
       storage_agree_except_def, word_agree_except_def]
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
  cheat
QED

