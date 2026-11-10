Theory fnPlanLineageNativeResources
Ancestors
  fnPlanLineageCallers fnPlanLineageSetup fnPlanLineagePath
  fnPlanLineageNativeOrigins fnPlanLineagePhiLiveBudget fnPlanLineageEdge stackPlanGen venomWf
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

(* PHI demand is next-live minus the freshly defined output, not the union
   of incoming alternatives. Physical selection remains an explicit input. *)
Theorem native_phi_live_demand_step:
  !fn bb i ps dfg cfg halt term ops qs out dist.
    (EL i bb.bb_instructions).inst_opcode = PHI /\
    (EL i bb.bb_instructions).inst_outputs = [out] /\
    stack_get_phi_depth
      (FILTER is_var_operand (EL i bb.bb_instructions).inst_operands) ps.ps_stack = SOME dist /\
    ~MEM (Var out) ps.ps_stack /\ Var out NOTIN FDOM ps.ps_spilled /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) /\ v <> out ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) /\ v <> out ==>
      LIST_ELEM_COUNT (Var v) ps.ps_stack +
        (if Var v IN FDOM ps.ps_spilled then 1 else 0) <= 1) /\
    generate_inst_plan (liveness_analyze fn) dfg cfg fn (EL i bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) halt term bb.bb_label ps =
      SOME (ops,qs) ==>
    native_live_boundary fn bb (SUC i) qs
Proof
  rpt gen_tac >> strip_tac >>
  gvs[generate_inst_plan_def, is_pre_codegen_opcode_def] >>
  drule_at (Pat `generate_phi_plan _ _ _ _ = _`) generate_phi_plan_live_budget >>
  disch_then (qspecl_then [`out`, `dist`] mp_tac) >> simp[] >>
  simp[native_live_boundary_def]
QED

Theorem native_phi_live_boundary_step:
  !fn bb i ps dfg cfg halt term ops qs out dist.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    i < LENGTH bb.bb_instructions /\
    (EL i bb.bb_instructions).inst_opcode = PHI /\
    (EL i bb.bb_instructions).inst_outputs = [out] /\
    stack_get_phi_depth
      (FILTER is_var_operand (EL i bb.bb_instructions).inst_operands) ps.ps_stack = SOME dist /\
    ~MEM (Var out) ps.ps_stack /\ Var out NOTIN FDOM ps.ps_spilled /\
    native_live_boundary fn bb i ps /\
    generate_inst_plan (liveness_analyze fn) dfg cfg fn (EL i bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) halt term bb.bb_label ps =
      SOME (ops,qs) ==>
    native_live_boundary fn bb (SUC i) qs
Proof
  rpt gen_tac >> strip_tac >>
  `!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) /\ v <> out ==>
    MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i)` by
    (rpt strip_tac >> irule analyzed_computed_operand_demand >> simp[]) >>
  drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    native_phi_live_demand_step >>
  disch_then (qspecl_then [`out`, `dist`] mp_tac) >>
  gvs[native_live_boundary_def] >> metis_tac[]
QED

(* A covered suffix consumes the complete unit resource budget for an item.
   No restriction is imposed on other items in the residual prefix. *)
Theorem resource_suffix_cancel:
  !x prefix suffix spills.
    MEM x suffix /\
    LIST_ELEM_COUNT x (prefix ++ suffix) +
      (if x IN FDOM spills then 1 else 0) <= 1 ==>
    ~MEM x prefix /\ x NOTIN FDOM spills /\
    LIST_ELEM_COUNT x suffix = 1
Proof
  rpt gen_tac >>
  simp[LIST_ELEM_COUNT_THM, GSYM LIST_ELEM_COUNT_MEM] >>
  Cases_on `x IN FDOM spills` >> simp[] >> decide_tac
QED

Theorem native_live_boundary_suffix_exclusion:
  !fn bb i ps prefix suffix.
    native_live_boundary fn bb i ps /\ ps.ps_stack = prefix ++ suffix /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i) ==>
      MEM (Var v) suffix) ==>
    !v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i) ==>
      ~MEM (Var v) prefix /\ Var v NOTIN FDOM ps.ps_spilled /\
      LIST_ELEM_COUNT (Var v) suffix = 1
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  drule_all native_live_boundary_count >> strip_tac >>
  irule resource_suffix_cancel >> simp[] >> gvs[]
QED

Theorem native_join_edge_residual:
  codegen_ready_fn fn /\ cfg_reachable_of (cfg_analyze fn) pred /\
  lookup_block pred fn.fn_blocks = SOME pb /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl) /\
  generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb before = SOME (ops,after) /\
  native_live_boundary fn pb (LENGTH pb.bb_instructions) after ==>
  ?prefix. after.ps_stack = prefix ++ MAP Var
      (input_vars_from pred bb.bb_instructions (live_vars_at (liveness_analyze fn) lbl 0)) /\
    DISJOINT (set prefix) (set (MAP Var
      (input_vars_from pred bb.bb_instructions (live_vars_at (liveness_analyze fn) lbl 0)))) /\
    after.ps_spilled = FEMPTY
Proof
  strip_tac >> drule_all generate_block_plan_join_edge_suffix >> strip_tac >>
  drule_all analyzed_join_edge_spilled_empty >> strip_tac >>
  drule_all ready_join_edge_terminator >> strip_tac >>
  `pb.bb_label = pred` by metis_tac[venomExecPropsTheory.lookup_block_label] >>
  `set (live_vars_at (liveness_analyze fn) pred (LENGTH pb.bb_instructions)) =
   set (input_vars_from pred bb.bb_instructions (live_vars_at (liveness_analyze fn) lbl 0))` by
    metis_tac[fnPlanLineageLivenessTheory.analyzed_live_out_jmp] >>
  `!v. MEM v (live_vars_at (liveness_analyze fn) pb.bb_label (LENGTH pb.bb_instructions)) ==>
    MEM (Var v) (MAP Var (input_vars_from pred bb.bb_instructions
      (live_vars_at (liveness_analyze fn) lbl 0)))` by
    (gvs[pred_setTheory.EXTENSION, MEM_MAP] >> metis_tac[]) >>
  `!v. MEM v (live_vars_at (liveness_analyze fn) pb.bb_label (LENGTH pb.bb_instructions)) ==>
    ~MEM (Var v) prefix` by metis_tac[native_live_boundary_suffix_exclusion] >>
  qexists_tac `prefix` >> simp[] >>
  simp[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION, MEM_MAP] >>
  metis_tac[]
QED
