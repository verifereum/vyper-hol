(* Request observations at non-call exceptional endpoints. *)
Theory o1LowerDloadRequestEndpoints
Ancestors
  o1LowerDloadRunnerEndpoints o1LowerDloadShared
  o1LowerDloadJointRelation o1LowerDloadAbortResult
  o1LowerDloadExceptional o1LowerDloadJointIdentity o1LowerDloadUnchangedFetch
  ptrDiscipline venomExecSemantics venomState opcodeClass list

Theorem step_inst_abort_requests:
  step_inst fuel C inst s = Abort reason s1 /\
  inst.inst_opcode <> INVOKE ==> s1.vs_requests = s.vs_requests
Proof
  strip_tac >>
  drule step_inst_abort_opcodes >> strip_tac >>
  gvs[step_inst_non_invoke] >>
  qpat_x_assum `step_inst_base inst s = _` mp_tac >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[exec_create_abort_iff, AllCaseEqs(), halt_state_def,
       set_returndata_def, exec_write2_def, eval_operands_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  gvs[exec_ext_call_def, AllCaseEqs()] >> pairarg_tac >> gvs[]
QED

Theorem ld_joint_requests:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts ==>
  LIST_REL (request_agree_except D) s.vs_requests t.vs_requests
Proof
  simp[ld_joint_boundary_def, ld_shared_agree_def]
QED

(* Matching non-call aborts need no additional state invariant: neither
   instruction has yet consumed an external outcome. *)
Theorem ld_runner_abort_endpoint_requests:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\
  o1_ctx_shape C /\ ptr_discipline lo C vs /\ opaque_use_ok fn /\
  active_inst fn inst s /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel C inst s = Abort reason s1 ==>
  ?fn' bb' t1. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    exec_block fuel C' bb' t = Abort reason t1 /\
    dead_result_rel D (Abort reason s1) (Abort reason t1) /\
    LIST_REL (request_agree_except D) s1.vs_requests t1.vs_requests
Proof
  strip_tac >>
  `?t1. step_inst fuel C' inst t = Abort reason t1` by
    (Cases_on `inst.inst_opcode = REVERT`
     >- metis_tac[ld_joint_revert_result] >>
     Cases_on `MEM inst.inst_opcode [ASSERT; ASSERT_UNREACHABLE]`
     >- metis_tac[ld_joint_assert_abort] >>
     Cases_on `MEM inst.inst_opcode [RETURNDATACOPY; CREATE; CREATE2]`
     >- (drule_all ld_joint_ordinary_abort >> simp[]) >>
     Cases_on `MEM inst.inst_opcode [SSTORE; TSTORE; LOG; SELFDESTRUCT; CALL]`
     >- (drule_all ld_joint_static_abort >> simp[]) >>
     `inst.inst_opcode = INVALID` by
       (drule step_inst_abort_opcodes >> rpt strip_tac >> gvs[]) >>
     qpat_x_assum `step_inst fuel C inst s = _` mp_tac >>
     simp[step_inst_non_invoke] >>
     asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >> simp[]) >>
  `s1.vs_requests = s.vs_requests /\ t1.vs_requests = t.vs_requests` by
    metis_tac[step_inst_abort_requests] >>
  `~MEM inst.inst_opcode [DLOAD; DLOADBYTES]` by
    (drule step_inst_abort_opcodes >> rpt strip_tac >> gvs[]) >>
  drule_all ld_joint_unchanged_fetch >> strip_tac >>
  qexistsl_tac [`fn'`, `bb'`, `t1`] >>
  simp[Once exec_block_def, dead_result_rel_def] >>
  metis_tac[ld_joint_requests]
QED
