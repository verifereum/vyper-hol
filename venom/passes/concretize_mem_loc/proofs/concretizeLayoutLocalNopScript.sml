Theory concretizeLayoutLocalNop
Ancestors concretizeLayoutLocalOffset frameRelocationLocal frameRelocationDemand
  frameRelocationTaintOrder frameRelocationCopyTaint frameRelocationMemory concretizeLayoutReaderContext
  frameRelocationEnvironment frameRelocationBinding frameJointDemand frameJointTrace
  frameJointTransition frameResolvedTrace frameJointTaint frameOriginUpdates
  ptrDiscipline venomExecSemantics venomWf codegenRel finite_map pred_set list

Theorem nop_execution[local]:
  inst.inst_opcode = NOP ==> step_inst_base inst s = OK s
Proof
  strip_tac >> pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def]
QED

Theorem nop_ghosts[local]:
  inst.inst_opcode = NOP /\ inst.inst_outputs = [] ==>
  step_prov PG G inst post = G /\ step_taint inst s s tn = tn /\
  step_writes inst s post = []
Proof
  strip_tac >>
  `new_site_bytes s s = {}` by (irule new_site_bytes_unchanged >> simp[]) >>
  simp[step_prov_def, out_prov_def, set_prov_def, step_taint_def,
       mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       written_taint_def, range_bytes_def, store_taint_def, adopt_reset_def,
       imm_taint_def, out_taint_def, set_var_taint_def, taint_component_equality] >>
  rpt CASE_TAC >> simp[fmap_eq_flookup, FLOOKUP_DRESTRICT]
QED

Theorem concretize_nop_local_complete:
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  joint_trace vs0 C q0 es qs q /\ c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = NOP /\
  step_inst_base inst s = OK post /\
  relocation_env s t /\ relocation_reader_context s t /\
  local_rel (\u. F)
    (guarded_ptr (retpc_var fn)
      (activation_lookup (0:num) (concretize_positions C')
        (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
    (guarded_bytes (retpc_var fn) rv tn)
    (joint_relocation_demand lo (concretize_positions C') q0 es qs c)
    (\s t. dead_result_rel D (Halt s) (Halt t)) s t /\
  relocation_taint_le
    (joint_relocation_demand lo (concretize_positions C') q0 es qs c) tn un ==>
  step_inst_base inst t = OK t /\
    local_rel (\u. F)
      (guarded_ptr (retpc_var fn)
        (activation_lookup (0:num) (concretize_positions C')
          (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
      (guarded_bytes (retpc_var fn) rv (step_taint inst s post tn))
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (\s t. dead_result_rel D (Halt s) (Halt t)) post t /\
    step_prov PG (SND o_f rv) inst post = SND o_f rv /\
    relocation_taint_le
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (step_taint inst s post tn) (step_taint inst t t un) /\
    relocation_env post t /\ relocation_reader_context post t /\
    step_taint inst s post tn = tn /\ step_taint inst t t un = un
Proof
  strip_tac >>
  `inst_wf inst` by
    (fs[o1PassContractTheory.o1_fn_shape_def, fn_inst_wf_def,
        venomInstTheory.fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >> metis_tac[]) >>
  `inst.inst_outputs = []` by
    (qpat_x_assum `inst_wf inst` mp_tac >>
     simp[inst_wf_def, venomInstTheory.opcode_case_def]) >>
  `post = s` by (drule nop_execution >> disch_then (qspec_then `s` mp_tac) >> simp[]) >>
  `!a b. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a b ==>
         joint_relocation_demand lo (concretize_positions C') q0 es qs c a b` by
    (rpt strip_tac >> irule joint_relocation_demand_retained >>
     goal_assum (drule_at Any) >>
     simp[joint_writes_def, nop_ghosts, range_bytes_def] >> metis_tac[]) >>
  gvs[nop_execution, nop_ghosts] >> conj_tac
  >- (fs[local_rel_def, demand_agree_def] >> metis_tac[]) >>
  fs[relocation_taint_le_def, demand_taint_def] >> metis_tac[]
QED

val _ = if null (hyp concretize_nop_local_complete) then ()
        else raise Fail "NOP export has hypotheses";
val _ = export_theory();
