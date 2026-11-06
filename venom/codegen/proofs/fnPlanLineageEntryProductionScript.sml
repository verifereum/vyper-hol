Theory fnPlanLineageEntryProduction
Ancestors
  fnPlanLineageCallers fnPlanLineageSetup fnPlanLineagePath
  stackPlanGen venomWf venomInst passSharedDefs removeUnusedProofs removeUnusedSsaProofs list rich_list finite_map bag

(* Chronological origins include dead definitions retained by native emission.
   They are deliberately independent of the liveness set. *)
Definition prefix_inventory_origins_def:
  prefix_inventory_origins bb i ps <=>
    !v. MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled ==>
      ?j. j < i /\ j < LENGTH bb.bb_instructions /\
        MEM v (EL j bb.bb_instructions).inst_outputs
End

Definition entry_boundary_resources_def:
  entry_boundary_resources fn bb i ps <=>
    prefix_inventory_origins bb i ps /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i) ==>
      LIST_ELEM_COUNT (Var v) ps.ps_stack +
        (if Var v IN FDOM ps.ps_spilled then 1 else 0) <= 1)
End

Theorem prefix_inventory_outputs_fresh:
  !fn bb i ps v.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
    i < LENGTH bb.bb_instructions /\ prefix_inventory_origins bb i ps /\
    MEM v (EL i bb.bb_instructions).inst_outputs ==>
    ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  `ssa_form fn` by gvs[codegen_ready_fn_def] >>
  gvs[prefix_inventory_origins_def] >>
  CCONTR_TAC >> gvs[] >>
  `?j. j < i /\ j < LENGTH bb.bb_instructions /\
    MEM v (EL j bb.bb_instructions).inst_outputs` by metis_tac[] >>
  `i = j` by metis_tac[ssa_form_position] >> decide_tac
QED

Theorem initialized_entry_boundary_resources:
  !fn ch growth spill_base lbl_ctr ps.
    codegen_ready_fn fn /\ fn.fn_blocks <> [] /\
    ps = SND (prepare_params_plan (liveness_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)) ==>
    entry_boundary_resources fn (HD fn.fn_blocks)
      (LENGTH (get_params (HD fn.fn_blocks).bb_instructions)) ps
Proof
  rpt gen_tac >> strip_tac >>
  drule_all native_parameter_inventory >>
  disch_then (qspecl_then [`ch`, `growth`, `spill_base`, `lbl_ctr`] strip_assume_tac) >>
  `MEM (HD fn.fn_blocks) fn.fn_blocks` by
    (Cases_on `fn.fn_blocks` >> gvs[]) >>
  `fn_reachable fn (HD fn.fn_blocks).bb_label` by
    (Cases_on `fn.fn_blocks` >>
     gvs[fn_reachable_def, fn_entry_label_def, entry_block_def] >>
     metis_tac[relationTheory.RTC_REFL]) >>
  `LENGTH (get_params (HD fn.fn_blocks).bb_instructions) <=
    LENGTH (HD fn.fn_blocks).bb_instructions` by
    (drule_all ready_block_parameter_suffix >>
     disch_then (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]) >>
  simp_tac bool_ss [entry_boundary_resources_def] >>
  conj_tac
  >- (simp_tac bool_ss [prefix_inventory_origins_def] >>
      rpt strip_tac >>
      `MEM v (live_vars_at (liveness_analyze fn) (HD fn.fn_blocks).bb_label
        (LENGTH (get_params (HD fn.fn_blocks).bb_instructions)))` by
        (gvs[pred_setTheory.EXTENSION, MEM_MAP] >> metis_tac[]) >>
      drule_at (Pat `MEM _ (live_vars_at _ _ _)`) interval_live_origin >>
      disch_then (qspec_then `0` mp_tac) >>
      simp[fnPlanLineageDemandTheory.analyzed_hd_live_empty] >>
      strip_tac >> qexists_tac `k` >> simp[] >> decide_tac) >>
  conj_tac
  >- (gvs[pred_setTheory.EXTENSION, MEM_MAP] >> metis_tac[]) >>
  gvs[] >> metis_tac[fnPlanLineageInventoryTheory.all_distinct_elem_count_le_one]
QED

Theorem entry_regular_boundary_step:
  !fn bb i ps dfg cfg halting term ops qs.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    i < LENGTH bb.bb_instructions /\
    (EL i bb.bb_instructions).inst_opcode <> JMP /\
    (EL i bb.bb_instructions).inst_opcode <> PHI /\
    entry_boundary_resources fn bb i ps /\
    generate_regular_inst_plan (liveness_analyze fn) dfg cfg fn
      (EL i bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i))
      halting term bb.bb_label ps = (ops,qs) ==>
    entry_boundary_resources fn bb (SUC i) qs
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH (compute_operands (EL i bb.bb_instructions)) <= 16` by
    (gvs[codegen_ready_fn_def, EVERY_MEM, codegen_ready_inst_def] >>
     metis_tac[EL_MEM]) >>
  `ALL_DISTINCT (EL i bb.bb_instructions).inst_outputs` by
    (irule codegen_ready_inst_outputs_distinct >>
     qexists_tac `fn` >>
     simp[fn_insts_def, removeUnusedSsaProofsTheory.fn_insts_blocks_flat,
       MEM_FLAT, MEM_MAP] >> metis_tac[EL_MEM]) >>
  `prefix_inventory_origins bb i ps` by gvs[entry_boundary_resources_def] >>
  `!v. MEM (Var v) (compute_operands (EL i bb.bb_instructions)) \/
      (MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) /\
       ~MEM v (EL i bb.bb_instructions).inst_outputs) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by
    (gvs[entry_boundary_resources_def] >>
     metis_tac[analyzed_computed_operand_demand]) >>
  `!v. MEM v (EL i bb.bb_instructions).inst_outputs ==>
    ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled` by
    metis_tac[prefix_inventory_outputs_fresh] >>
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
     gvs[entry_boundary_resources_def]) >>
  simp_tac bool_ss [entry_boundary_resources_def] >>
  conj_tac
  >- (simp_tac bool_ss [prefix_inventory_origins_def] >> rpt strip_tac >>
      drule_at (Pat `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
        native_regular_variable_origins >> simp[] >>
      disch_tac >>
      `MEM v (EL i bb.bb_instructions).inst_outputs \/
       MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by metis_tac[] >>
      (Cases_on `MEM v (EL i bb.bb_instructions).inst_outputs`
       >- (qexists_tac `i` >> simp[])) >>
      `?j. j < i /\ j < LENGTH bb.bb_instructions /\
        MEM v (EL j bb.bb_instructions).inst_outputs` by
        metis_tac[prefix_inventory_origins_def] >>
      qexists_tac `j` >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> drule_all native_regular_live_lower >> simp[]) >>
  rpt strip_tac >>
  drule_at (Pat `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    native_regular_next_live_upper >>
  simp[MEM_APPEND, reorderSimTheory.input_mem_operand_vars, MEM_operand_vars_eq_Var]
QED

Theorem entry_inst_boundary_step:
  !fn bb i ps dfg cfg halting term ops qs.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    i < LENGTH bb.bb_instructions /\
    (EL i bb.bb_instructions).inst_opcode <> JMP /\
    (EL i bb.bb_instructions).inst_opcode <> PHI /\
    ~is_param_opcode (EL i bb.bb_instructions).inst_opcode /\
    entry_boundary_resources fn bb i ps /\
    generate_inst_plan (liveness_analyze fn) dfg cfg fn
      (EL i bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i))
      halting term bb.bb_label ps = SOME (ops,qs) ==>
    entry_boundary_resources fn bb (SUC i) qs
Proof
  rpt gen_tac >> strip_tac >>
  `inst_wf (EL i bb.bb_instructions)` by
    (gvs[codegen_ready_fn_def, fn_inst_wf_def, EVERY_MEM] >> metis_tac[EL_MEM]) >>
  Cases_on `(EL i bb.bb_instructions).inst_opcode = OFFSET`
  >- (drule_all inst_wf_offset_shape >> strip_tac >>
      `prefix_inventory_origins bb i ps` by gvs[entry_boundary_resources_def] >>
      `~MEM (Var out) ps.ps_stack /\ Var out NOTIN FDOM ps.ps_spilled` by
        (irule prefix_inventory_outputs_fresh >>
         qexistsl_tac [`bb`, `fn`, `i`] >> simp[]) >>
      `!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) /\ v <> out ==>
        MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i)` by
        (rpt strip_tac >> irule analyzed_computed_operand_demand >> simp[]) >>
      gvs[generate_inst_plan_def, generate_offset_plan_def,
        stackModelTheory.stack_push_def, SNOC_APPEND] >>
      simp_tac bool_ss [entry_boundary_resources_def] >>
      conj_tac
      >- (simp[prefix_inventory_origins_def, MEM_APPEND] >>
          qx_gen_tac `w` >> Cases_on `w = out`
          >- (rpt strip_tac >> qexists_tac `i` >> simp[]) >>
          rpt strip_tac >>
          `?j. j < i /\ j < LENGTH bb.bb_instructions /\
            MEM w (EL j bb.bb_instructions).inst_outputs` by
            metis_tac[prefix_inventory_origins_def] >>
          qexists_tac `j` >> simp[]) >>
      conj_tac
      >- (gvs[entry_boundary_resources_def] >> qx_gen_tac `w` >> strip_tac >>
          Cases_on `w = out` >> simp[] >> metis_tac[]) >>
      qx_gen_tac `w` >> strip_tac >> Cases_on `w = out`
      >- (gvs[] >>
          `LIST_ELEM_COUNT (Var out) ps.ps_stack = 0` by
            (qpat_x_assum `~MEM (Var out) ps.ps_stack` mp_tac >>
             simp_tac std_ss [GSYM LIST_ELEM_COUNT_MEM, arithmeticTheory.GREATER_DEF]) >>
          simp[reorderSimTheory.elem_count_append, LIST_ELEM_COUNT_THM]) >>
      `MEM w (live_vars_at (liveness_analyze fn) bb.bb_label i)` by metis_tac[] >>
      gvs[entry_boundary_resources_def, reorderSimTheory.elem_count_append,
        LIST_ELEM_COUNT_THM]) >>
  Cases_on `(EL i bb.bb_instructions).inst_opcode = NOP`
  >- (`(EL i bb.bb_instructions).inst_outputs = []` by gvs[inst_wf_def] >>
      `!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) ==>
        MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i)` by
        (rpt strip_tac >> irule analyzed_computed_operand_demand >> simp[]) >>
      gvs[generate_inst_plan_def, entry_boundary_resources_def] >>
      gvs[prefix_inventory_origins_def] >> rpt strip_tac >>
      `?j. j < i /\ j < LENGTH bb.bb_instructions /\
        MEM v (EL j bb.bb_instructions).inst_outputs` by metis_tac[] >>
      qexists_tac `j` >> simp[]) >>
  irule entry_regular_boundary_step >>
  goal_assum (drule_at Any) >>
  gvs[generate_inst_plan_def, AllCaseEqs()] >>
  goal_assum (drule_at Any) >> simp[]
QED
