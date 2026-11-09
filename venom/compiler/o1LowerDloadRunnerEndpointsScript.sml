(* Terminal endpoints retain the runner's original boundary witnesses. *)
Theory o1LowerDloadRunnerEndpoints
Ancestors
  o1LowerDloadRunner o1LowerDloadUnchangedFetch o1LowerDloadBranchExec
  o1LowerDloadForwardInversion contextCodegenRel
  o1LowerDloadJointReturn o1LowerDloadHaltResult o1LowerDloadAbortResult
  o1LowerDloadJointIdentity o1LowerDloadExceptional
  o1LowerDloadRunnerBoundary o1LowerDloadJointRelation o1PassContract
  ptrDiscipline venomExecSemantics venomInstProps venomInst opcodeClass list gasEvents

val ldPacket = fst (strip_comb (fst (dest_imp
  (concl ld_runner_packet_terminates))));

Theorem ld_runner_branch_endpoint:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\
  o1_ctx_shape C /\ ptr_discipline lo C vs /\ opaque_use_ok fn /\
  active_inst fn inst s /\ ~s.vs_halted /\
  is_terminator inst.inst_opcode /\ step_inst fuel C inst s = OK s1 ==>
  ?fn' bb' r'. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    exec_block fuel C' bb' t = r' /\
    gas_events_block fuel C' fn'.fn_name bb' t = [] /\
    ^ldPacket stk PG fn a U HP ts s.vs_call_ctx.cc_address (OK s1) r'
Proof
  strip_tac >> drule_all ld_terminator_ok_branch >> strip_tac >>
  drule_all ld_joint_branch_step >>
  disch_then (qspec_then `fuel` strip_assume_tac) >>
  `~MEM inst.inst_opcode [DLOAD; DLOADBYTES]` by fs[] >>
  drule_all ld_joint_unchanged_fetch >> strip_tac >>
  `~t.vs_halted` by fs[ld_joint_boundary_def, ld_joint_frame_def, ld_joint_local_fields_def] >>
  `s1.vs_call_ctx = s.vs_call_ctx` by metis_tac[ld_step_ok_call_ctx] >>
  qexistsl_tac [`fn'`,`bb'`,`OK t1`] >> simp[] >> conj_tac
  >- (simp[Once exec_block_def]) >>
  conj_tac
  >- (simp[Once gas_events_block_def, gas_events_step_def] >>
      fs[is_terminator_def]) >>
  simp[] >> qexistsl_tac [`fuel`,`inst`,`s`,`t`,`n`,`G`,`tn`,`B`,`H`,`sites`,`X`] >>
  fs[]
QED

Theorem ld_runner_ret_endpoint:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\
  o1_ctx_shape C /\ ptr_discipline lo C vs /\ opaque_use_ok fn /\
  active_inst fn inst s /\ inst.inst_opcode = RET /\
  step_inst fuel C inst s = IntRet ir s1 ==>
  ?fn' bb' r'. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    exec_block fuel C' bb' t = r' /\
    gas_events_block fuel C' fn'.fn_name bb' t = [] /\
    ^ldPacket stk PG fn a U HP ts s.vs_call_ctx.cc_address (IntRet ir s1) r'
Proof
  strip_tac >> drule_all ld_joint_ret_step >> strip_tac >>
  `~MEM inst.inst_opcode [DLOAD; DLOADBYTES]` by simp[] >>
  drule_all ld_joint_unchanged_fetch >> strip_tac >>
  qexistsl_tac [`fn'`,`bb'`,`IntRet jr t`] >> simp[] >> conj_tac
  >- (simp[Once exec_block_def]) >>
  conj_tac >- simp[Once gas_events_block_def, gas_events_step_def] >>
  simp[] >> qexistsl_tac [`fuel`,`inst`,`n`,`G`,`tn`,`B`,`H`,`sites`,`X`] >>
  simp[]
QED

Theorem ld_runner_halt_endpoint:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\
  o1_ctx_shape C /\ ptr_discipline lo C vs /\ taint_within D C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  (?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME inst) /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel C inst s = Halt s1 ==>
  ?fn' bb' r'. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    exec_block fuel C' bb' t = r' /\
    gas_events_block fuel C' fn'.fn_name bb' t = [] /\
    ^ldPacket stk PG fn a U HP ts s.vs_call_ctx.cc_address (Halt s1) r'
Proof
  strip_tac >>
  drule_all (SIMP_RULE bool_ss [PULL_EXISTS] ld_joint_halt_result) >> strip_tac >>
  `~MEM inst.inst_opcode [DLOAD; DLOADBYTES]` by
    (drule step_inst_halt_opcodes >> rpt strip_tac >> gvs[]) >>
  drule_all ld_joint_unchanged_fetch >> strip_tac >>
  `inst.inst_opcode <> GAS` by
    (drule step_inst_halt_opcodes >> rpt strip_tac >> gvs[]) >>
  qexistsl_tac [`fn'`,`bb'`,`Halt t1`] >>
  simp[Once exec_block_def, Once gas_events_block_def, gas_events_step_def]
QED

Theorem ld_runner_abort_endpoint:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\
  o1_ctx_shape C /\ ptr_discipline lo C vs /\ opaque_use_ok fn /\
  active_inst fn inst s /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel C inst s = Abort reason s1 ==>
  ?fn' bb' r'. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    exec_block fuel C' bb' t = r' /\
    gas_events_block fuel C' fn'.fn_name bb' t = [] /\
    ^ldPacket stk PG fn a U HP ts s.vs_call_ctx.cc_address (Abort reason s1) r'
Proof
  strip_tac >>
  `?t1. step_inst fuel C' inst t = Abort reason t1 /\
        dead_result_rel D (Abort reason s1) (Abort reason t1)` by
    (Cases_on `inst.inst_opcode = REVERT`
     >- (drule_all ld_joint_revert_result >> simp[]) >>
     Cases_on `MEM inst.inst_opcode [ASSERT; ASSERT_UNREACHABLE]`
     >- (drule_all ld_joint_assert_abort >> simp[]) >>
     Cases_on `MEM inst.inst_opcode [RETURNDATACOPY; CREATE; CREATE2]`
     >- (drule_all ld_joint_ordinary_abort >> simp[dead_result_rel_def]) >>
     Cases_on `MEM inst.inst_opcode [SSTORE; TSTORE; LOG; SELFDESTRUCT; CALL]`
     >- (drule_all ld_joint_static_abort >> simp[dead_result_rel_def]) >>
     `inst.inst_opcode = INVALID` by
       (drule step_inst_abort_opcodes >> rpt strip_tac >> gvs[]) >>
     qpat_x_assum `step_inst fuel C inst s = _` mp_tac >>
     simp[step_inst_non_invoke] >>
     asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
     strip_tac >> gvs[dead_result_rel_def]) >>
  `~MEM inst.inst_opcode [DLOAD; DLOADBYTES]` by
    (drule step_inst_abort_opcodes >> rpt strip_tac >> gvs[]) >>
  drule_all ld_joint_unchanged_fetch >> strip_tac >>
  `inst.inst_opcode <> GAS` by
    (drule step_inst_abort_opcodes >> rpt strip_tac >> gvs[]) >>
  qexistsl_tac [`fn'`,`bb'`,`Abort reason t1`] >>
  simp[Once exec_block_def, Once gas_events_block_def, gas_events_step_def]
QED

Theorem ld_runner_forward_abort_endpoint:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\ active_inst fn inst s /\
  inst.inst_opcode = RETURNDATACOPY /\ in_revert_forward fn s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  exec_block fuel C bb s = Abort reason s1 ==>
  ?fn' bb' r'. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    exec_block fuel C' bb' t = r' /\
    gas_events_block fuel C' fn'.fn_name bb' t = [] /\
    gas_events_block fuel C fn.fn_name bb s = [] /\
    ^ldPacket stk PG fn a U HP ts s.vs_call_ctx.cc_address (Abort reason s1) r'
Proof
  strip_tac >> drule_all ld_joint_forward_abort_result >> strip_tac >>
  qexistsl_tac [`fn'`,`bb'`,`Abort reason t1`] >> simp[]
QED

Theorem ld_runner_forward_endpoint:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\ active_inst fn inst s /\
  inst.inst_opcode = RETURNDATACOPY /\ in_revert_forward fn s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  exec_block fuel C bb s = r /\ terminates r ==>
  ?fn' bb' r'. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    exec_block fuel C' bb' t = r' /\
    gas_events_block fuel C' fn'.fn_name bb' t = [] /\
    gas_events_block fuel C fn.fn_name bb s = [] /\
    ^ldPacket stk PG fn a U HP ts s.vs_call_ctx.cc_address r r'
Proof
  strip_tac >>
  `revert_forward_at bb s.vs_inst_idx` by fs[in_revert_forward_def] >>
  drule_all revert_forward_at_terminates_abort >> strip_tac >> gvs[] >>
  drule_all ld_runner_forward_abort_endpoint >> simp[]
QED

(* Integrity check: a closed export must not inherit proof-local assumptions. *)
val _ = List.app (fn (name, th) =>
  if null (hyp th) then print ("HYP AUDIT " ^ name ^ " count=0\n")
  else raise Fail ("Nonempty kernel hypotheses: " ^ name))
  [("ld_runner_branch_endpoint", ld_runner_branch_endpoint),
   ("ld_runner_ret_endpoint", ld_runner_ret_endpoint),
   ("ld_runner_halt_endpoint", ld_runner_halt_endpoint),
   ("ld_runner_abort_endpoint", ld_runner_abort_endpoint),
   ("ld_runner_forward_abort_endpoint", ld_runner_forward_abort_endpoint),
   ("ld_runner_forward_endpoint", ld_runner_forward_endpoint),
   ("assign_suffix_no_halt", assign_suffix_no_halt),
   ("revert_forward_at_no_halt", revert_forward_at_no_halt),
   ("revert_forward_at_terminates_abort", revert_forward_at_terminates_abort)];
