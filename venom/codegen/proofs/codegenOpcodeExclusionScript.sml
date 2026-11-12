(* Opcode provenance across mechanical plan lowering. *)
Theory codegenOpcodeExclusion
Ancestors codegen planExec asmIR stackPlanTypes list rich_list
  planEmissionProps contextPlanEmissionProps unitShapeDefs stackPlanGen venomInst

Theorem exec_stack_op_no_forbidden:
  (!name. op = SOEmit name ==>
    ~MEM name ["CREATE"; "CREATE2"; "DELEGATECALL"; "SELFDESTRUCT"]) ==>
  !name. MEM (AsmOp name) (exec_stack_op fmp op) ==>
    ~MEM name ["CREATE"; "CREATE2"; "DELEGATECALL"; "SELFDESTRUCT"]
Proof
  Cases_on `op` >> simp[exec_stack_op_def, MEM_REPLICATE]
  >- (rename1 `SOPush opd` >> Cases_on `opd` >> simp[exec_stack_op_def])
  >- (rename1 `swap_name k` >> qspec_then `k` assume_tac swap_name_prefix >>
      rpt conj_tac >> strip_tac >> gvs[])
  >> rename1 `dup_name k` >> qspec_then `k` assume_tac dup_name_prefix >>
  rpt conj_tac >> strip_tac >> gvs[]
QED

Theorem execute_plan_no_forbidden:
  (!name. MEM (SOEmit name) ops ==>
    ~MEM name ["CREATE"; "CREATE2"; "DELEGATECALL"; "SELFDESTRUCT"]) ==>
  !name. MEM (AsmOp name) (execute_plan fmp ops) ==>
    ~MEM name ["CREATE"; "CREATE2"; "DELEGATECALL"; "SELFDESTRUCT"]
Proof
  simp[execute_plan_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >>
  drule_at (Pat `MEM (AsmOp _) _`) exec_stack_op_no_forbidden >>
  simp[] >> metis_tac[]
QED

Theorem data_segment_asm_no_op:
  !segs name. ~MEM (AsmOp name) (data_segment_asm segs)
Proof
  simp[data_segment_asm_def, data_section_asm_def,
       MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >> Cases_on `di` >> gvs[]
QED

Theorem codegen_assembly_no_forbidden_conditional:
  generate_context_plan unit.cu_context = SOME cp /\
  codegen_assembly rpolicy unit = SOME prog /\
  (!name. MEM (SOEmit name) (context_plan_ops cp) ==>
    ~MEM name ["CREATE"; "CREATE2"; "DELEGATECALL"; "SELFDESTRUCT"]) ==>
  !name. MEM (AsmOp name) prog ==>
    ~MEM name ["CREATE"; "CREATE2"; "DELEGATECALL"; "SELFDESTRUCT"]
Proof
  strip_tac >> drule execute_plan_no_forbidden >>
  disch_then (qspec_then `cp.cp_initial_fmp` assume_tac) >>
  qpat_x_assum `codegen_assembly _ _ = _` mp_tac >>
  simp[codegen_assembly_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  simp[data_segment_asm_no_op]
QED

Theorem context_plan_no_forbidden:
  generate_context_plan ctx = SOME cp /\
  EVERY (\fn. EVERY (\inst.
    ~MEM inst.inst_opcode [CREATE; CREATE2; DELEGATECALL; SELFDESTRUCT])
    (fn_insts fn)) ctx.ctx_functions ==>
  !name. MEM (SOEmit name) (context_plan_ops cp) ==>
    ~MEM name ["CREATE"; "CREATE2"; "DELEGATECALL"; "SELFDESTRUCT"]
Proof
  strip_tac >>
  `EVERY (\op. !name. op = SOEmit name ==>
    ~MEM name ["CREATE"; "CREATE2"; "DELEGATECALL"; "SELFDESTRUCT"])
    (context_plan_ops cp)` suffices_by (simp[EVERY_MEM] >> metis_tac[]) >>
  irule generate_context_plan_insts_preserves >>
  simp[revert_postamble_def] >> rpt conj_tac
  >- (rpt strip_tac >> drule clean_stack_plan_admin >>
      simp[EVERY_MEM] >> metis_tac[plan_admin_op_def])
  >- (rpt strip_tac >> drule prepare_params_plan_admin >>
      simp[EVERY_MEM] >> metis_tac[plan_admin_op_def])
  >> qexistsl [`\inst. ~MEM inst.inst_opcode
                   [CREATE; CREATE2; DELEGATECALL; SELFDESTRUCT]`, `ctx`] >>
  simp[] >> rpt strip_tac >> drule generate_inst_plan_no_forbidden >>
  simp[EVERY_MEM] >> metis_tac[]
QED

Theorem codegen_assembly_no_forbidden_opcodes:
  generate_context_plan unit.cu_context = SOME cp /\
  codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit ==>
  !name. MEM (AsmOp name) prog ==>
    ~MEM name ["CREATE"; "CREATE2"; "DELEGATECALL"; "SELFDESTRUCT"]
Proof
  strip_tac >>
  `EVERY (\fn. EVERY (\inst.
     ~MEM inst.inst_opcode [CREATE; CREATE2; DELEGATECALL; SELFDESTRUCT])
     (fn_insts fn)) unit.cu_context.ctx_functions` by
    (gvs[unit_shape_ok_def, fn_shape_ok_def, inst_shape_ok_def, EVERY_MEM] >>
     metis_tac[]) >>
  metis_tac[context_plan_no_forbidden,
            codegen_assembly_no_forbidden_conditional]
QED
