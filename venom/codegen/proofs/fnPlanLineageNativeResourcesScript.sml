Theory fnPlanLineageNativeResources
Ancestors
  fnPlanLineageCallers fnPlanLineageSetup fnPlanLineagePath
  fnPlanLineageNativeOrigins stackPlanGen venomWf
  venomInst passSharedDefs removeUnusedSsaProofs list rich_list finite_map bag

(* Live resource accounting is independent of chronological origin support. *)
Definition native_live_boundary_def:
  native_live_boundary fn bb i ps <=>
    (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i) ==>
      LIST_ELEM_COUNT (Var v) ps.ps_stack +
        (if Var v IN FDOM ps.ps_spilled then 1 else 0) <= 1)
End

Theorem native_live_boundary_coverage:
  native_live_boundary fn bb i ps /\
  MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i) ==>
  MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled
Proof
  simp[native_live_boundary_def]
QED

Theorem native_live_boundary_count:
  native_live_boundary fn bb i ps /\
  MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i) ==>
  LIST_ELEM_COUNT (Var v) ps.ps_stack +
    (if Var v IN FDOM ps.ps_spilled then 1 else 0) <= 1
Proof
  simp[native_live_boundary_def]
QED

Theorem native_live_boundary_operands:
  !fn bb i ps.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    i < LENGTH bb.bb_instructions /\ native_live_boundary fn bb i ps ==>
    !v. MEM (Var v) (compute_operands (EL i bb.bb_instructions)) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >> gvs[native_live_boundary_def] >>
  metis_tac[analyzed_computed_operand_demand]
QED

Theorem native_regular_live_boundary_step:
  !fn bb i ps dfg cfg halting term ops qs.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    i < LENGTH bb.bb_instructions /\
    (EL i bb.bb_instructions).inst_opcode <> JMP /\
    (EL i bb.bb_instructions).inst_opcode <> PHI /\
    native_live_boundary fn bb i ps /\
    (!v. MEM v (EL i bb.bb_instructions).inst_outputs ==>
      ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled) /\
    generate_regular_inst_plan (liveness_analyze fn) dfg cfg fn
      (EL i bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i))
      halting term bb.bb_label ps = (ops,qs) ==>
    native_live_boundary fn bb (SUC i) qs
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH (compute_operands (EL i bb.bb_instructions)) <= 16` by
    (gvs[codegen_ready_fn_def, EVERY_MEM, codegen_ready_inst_def] >>
     metis_tac[EL_MEM]) >>
  `ALL_DISTINCT (EL i bb.bb_instructions).inst_outputs` by
    (irule codegen_ready_inst_outputs_distinct >> qexists_tac `fn` >>
     simp[fn_insts_def, removeUnusedSsaProofsTheory.fn_insts_blocks_flat,
       MEM_FLAT, MEM_MAP] >> metis_tac[EL_MEM]) >>
  `!v. MEM (Var v) (compute_operands (EL i bb.bb_instructions)) \/
      (MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) /\
       ~MEM v (EL i bb.bb_instructions).inst_outputs) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by
    (gvs[native_live_boundary_def] >> metis_tac[analyzed_computed_operand_demand]) >>
  `EVERY (\v. ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled /\
    ~MEM (Var v) (compute_operands (EL i bb.bb_instructions)))
    (EL i bb.bb_instructions).inst_outputs` by
    (simp[EVERY_MEM] >> metis_tac[]) >>
  `!v. MEM v (operand_vars (compute_operands (EL i bb.bb_instructions)) ++
      live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) ==>
    LIST_ELEM_COUNT (Var v) ps.ps_stack +
      (if Var v IN FDOM ps.ps_spilled then 1 else 0) <= 1` by
    (rpt strip_tac >>
     Cases_on `MEM v (EL i bb.bb_instructions).inst_outputs`
     >- (`~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled` by metis_tac[] >>
         `LIST_ELEM_COUNT (Var v) ps.ps_stack = 0` by
           metis_tac[LIST_ELEM_COUNT_MEM, arithmeticTheory.GREATER_DEF,
             arithmeticTheory.NOT_ZERO_LT_ZERO] >> simp[]) >>
     `MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i)` by
       (irule analyzed_computed_operand_demand >>
        gvs[MEM_APPEND, reorderSimTheory.input_mem_operand_vars, MEM_operand_vars_eq_Var]) >>
     gvs[native_live_boundary_def]) >>
  simp_tac bool_ss [native_live_boundary_def] >> conj_tac
  >- (rpt strip_tac >> drule_all native_regular_live_lower >> simp[]) >>
  rpt strip_tac >>
  drule_at (Pat `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    native_regular_next_live_upper >>
  simp[MEM_APPEND, reorderSimTheory.input_mem_operand_vars, MEM_operand_vars_eq_Var]
QED

Theorem native_inst_live_boundary_step:
  !fn bb i ps dfg cfg halting term ops qs.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    i < LENGTH bb.bb_instructions /\
    (EL i bb.bb_instructions).inst_opcode <> JMP /\
    (EL i bb.bb_instructions).inst_opcode <> PHI /\
    ~is_param_opcode (EL i bb.bb_instructions).inst_opcode /\
    native_live_boundary fn bb i ps /\
    (!v. MEM v (EL i bb.bb_instructions).inst_outputs ==>
      ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled) /\
    generate_inst_plan (liveness_analyze fn) dfg cfg fn
      (EL i bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i))
      halting term bb.bb_label ps = SOME (ops,qs) ==>
    native_live_boundary fn bb (SUC i) qs
Proof
  rpt gen_tac >> strip_tac >>
  `inst_wf (EL i bb.bb_instructions)` by
    (gvs[codegen_ready_fn_def, fn_inst_wf_def, EVERY_MEM] >> metis_tac[EL_MEM]) >>
  Cases_on `(EL i bb.bb_instructions).inst_opcode = OFFSET`
  >- (drule_all inst_wf_offset_shape >> strip_tac >>
      `~MEM (Var out) ps.ps_stack /\ Var out NOTIN FDOM ps.ps_spilled` by
        metis_tac[MEM] >>
      `!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) /\ v <> out ==>
        MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i)` by
        (rpt strip_tac >> irule analyzed_computed_operand_demand >> simp[]) >>
      gvs[generate_inst_plan_def, generate_offset_plan_def,
        stackModelTheory.stack_push_def, SNOC_APPEND] >>
      simp_tac bool_ss [native_live_boundary_def] >> conj_tac
      >- (gvs[native_live_boundary_def] >> qx_gen_tac `w` >> strip_tac >>
          Cases_on `w = out` >> simp[] >> metis_tac[]) >>
      qx_gen_tac `w` >> strip_tac >> Cases_on `w = out`
      >- (gvs[] >>
          `LIST_ELEM_COUNT (Var out) ps.ps_stack = 0` by
            (qpat_x_assum `~MEM (Var out) ps.ps_stack` mp_tac >>
             simp_tac std_ss [GSYM LIST_ELEM_COUNT_MEM, arithmeticTheory.GREATER_DEF]) >>
          simp[reorderSimTheory.elem_count_append, LIST_ELEM_COUNT_THM]) >>
      `MEM w (live_vars_at (liveness_analyze fn) bb.bb_label i)` by metis_tac[] >>
      gvs[native_live_boundary_def, reorderSimTheory.elem_count_append,
        LIST_ELEM_COUNT_THM]) >>
  Cases_on `(EL i bb.bb_instructions).inst_opcode = NOP`
  >- (`(EL i bb.bb_instructions).inst_outputs = []` by gvs[inst_wf_def] >>
      `!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) ==>
        MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i)` by
        (rpt strip_tac >> irule analyzed_computed_operand_demand >> simp[]) >>
      gvs[generate_inst_plan_def, native_live_boundary_def]) >>
  irule native_regular_live_boundary_step >> goal_assum (drule_at Any) >>
  gvs[generate_inst_plan_def, AllCaseEqs()] >>
  goal_assum (drule_at Any) >> simp[]
QED
