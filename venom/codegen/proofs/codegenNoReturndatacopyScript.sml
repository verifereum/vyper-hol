(* Opcode provenance for context plans. *)
Theory codegenNoReturndatacopy
Ancestors
  stackPlanGen stackPlanOps stackPlanTypes asmIR venomInst planWf prefixSim
  list rich_list arithmetic finite_map venomFnInstsProofs livenessTransferProofs
  planEmissionProps contextPlanEmissionProps

val _ = Parse.hide "cp";

Theorem venom_name_returndatacopy[local]:
  venom_to_evm_name opc = SOME "RETURNDATACOPY" <=> opc = RETURNDATACOPY
Proof
  Cases_on `opc` >> simp[venom_to_evm_name_def]
QED

Theorem generate_emit_ops_no_returndatacopy[local]:
  generate_emit_ops inst topics ps = (ops, ps') /\
  inst.inst_opcode <> RETURNDATACOPY ==>
  ~MEM (SOEmit "RETURNDATACOPY") ops
Proof
  strip_tac >> CCONTR_TAC >> fs[] >>
  drule generate_emit_ops_origin >>
  disch_then (qspec_then `SOEmit "RETURNDATACOPY"` mp_tac) >>
  simp[plan_admin_op_def, venom_name_returndatacopy]
QED

Theorem generate_regular_inst_plan_no_returndatacopy[local]:
  generate_regular_inst_plan liveness dfg cfg fn inst live halting term cur ps =
    (ops, ps') /\ inst.inst_opcode <> RETURNDATACOPY ==>
  ~MEM (SOEmit "RETURNDATACOPY") ops
Proof
  strip_tac >>
  `EVERY (\op. op <> SOEmit "RETURNDATACOPY") ops` suffices_by
    (simp[EVERY_MEM] >> metis_tac[]) >>
  drule generate_regular_inst_plan_preserves >>
  disch_then (qspec_then `\op. op <> SOEmit "RETURNDATACOPY"` mp_tac) >>
  impl_tac >- (conj_tac
    >- (Cases >> simp[plan_admin_op_def]) >>
    rpt gen_tac >> strip_tac >>
    drule_all generate_emit_ops_no_returndatacopy >>
    simp[EVERY_MEM] >> metis_tac[]) >> simp[]
QED

Theorem generate_inst_plan_no_returndatacopy[local]:
  generate_inst_plan liveness dfg cfg fn inst live halting term cur ps =
    SOME (ops, ps') /\ inst.inst_opcode <> RETURNDATACOPY ==>
  ~MEM (SOEmit "RETURNDATACOPY") ops
Proof
  simp[generate_inst_plan_def] >> rpt IF_CASES_TAC >> simp[] >>
  gvs[generate_offset_plan_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
  >- metis_tac[generate_phi_plan_admin, plan_admin_no_emit] >>
  drule_all generate_regular_inst_plan_no_returndatacopy >> simp[]
QED

Theorem generate_context_plan_no_returndatacopy:
  !ctx cp. generate_context_plan ctx = SOME cp /\
  (!fn inst. MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) ==>
             inst.inst_opcode <> RETURNDATACOPY) ==>
  ~MEM (SOEmit "RETURNDATACOPY") (context_plan_ops cp)
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `generate_context_plan ctx0 = SOME cplan` >>
  `EVERY (\op. op <> SOEmit "RETURNDATACOPY") (context_plan_ops cplan)`
    suffices_by (simp[EVERY_MEM] >> metis_tac[]) >>
  mp_tac (Q.INST [`P` |-> `\op. op <> SOEmit "RETURNDATACOPY"`,
                  `Q` |-> `\inst. inst.inst_opcode <> RETURNDATACOPY`,
                  `ctx` |-> `ctx0`, `cp` |-> `cplan`]
    generate_context_plan_insts_preserves) >>
  impl_tac
  >- (simp[revert_postamble_def, EVERY_MEM] >> rpt strip_tac >>
      metis_tac[generate_inst_plan_no_returndatacopy,
                prepare_params_plan_admin, clean_stack_plan_admin,
                plan_admin_no_emit]) >>
  simp[]
QED
