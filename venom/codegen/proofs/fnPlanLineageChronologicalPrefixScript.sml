Theory fnPlanLineageChronologicalPrefix
Ancestors
  fnPlanLineageNativeResources fnPlanLineageNativeOrigins
  fnPlanLineageEntryProduction fnPlanLineagePath stackPlanGen venomWf venomInst
  list rich_list finite_map

Theorem native_chronological_step:
  !fn visited bb i ps dfg cfg halting term ops qs.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    ~MEM bb.bb_label visited /\ i < LENGTH bb.bb_instructions /\
    (EL i bb.bb_instructions).inst_opcode <> JMP /\
    (EL i bb.bb_instructions).inst_opcode <> PHI /\
    ~is_param_opcode (EL i bb.bb_instructions).inst_opcode /\
    (!v. MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled ==>
      (?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
        MEM v di.inst_outputs /\ MEM db.bb_label visited) \/
      (?di. MEM di (TAKE i bb.bb_instructions) /\ MEM v di.inst_outputs)) /\
    native_live_boundary fn bb i ps /\
    generate_inst_plan (liveness_analyze fn) dfg cfg fn (EL i bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i))
      halting term bb.bb_label ps = SOME (ops,qs) ==>
    (!v. MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled ==>
      (?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
        MEM v di.inst_outputs /\ MEM db.bb_label visited) \/
      (?di. MEM di (TAKE (SUC i) bb.bb_instructions) /\ MEM v di.inst_outputs)) /\
    native_live_boundary fn bb (SUC i) qs
Proof
  rpt gen_tac >> strip_tac >>
  `ssa_form fn` by gvs[codegen_ready_fn_def] >>
  `EVERY (\v. ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled)
     (EL i bb.bb_instructions).inst_outputs` by
    (irule chronological_origin_output_fresh >> simp[] >> qexistsl_tac [`fn`, `visited`] >> simp[] >> metis_tac[]) >>
  `!v. MEM v (EL i bb.bb_instructions).inst_outputs ==>
     ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled` by gvs[EVERY_MEM] >>
  `LENGTH (compute_operands (EL i bb.bb_instructions)) <= 16` by
    (gvs[codegen_ready_fn_def, EVERY_MEM, codegen_ready_inst_def] >> metis_tac[EL_MEM]) >>
  `inst_wf (EL i bb.bb_instructions)` by
    (gvs[codegen_ready_fn_def, fn_inst_wf_def, EVERY_MEM] >> metis_tac[EL_MEM]) >>
  `((EL i bb.bb_instructions).inst_opcode = PHI \/
    (EL i bb.bb_instructions).inst_opcode = OFFSET) ==>
    (EL i bb.bb_instructions).inst_outputs <> []` by
    (strip_tac >> drule_all inst_wf_offset_shape >> strip_tac >> simp[]) >>
  `!v. MEM (Var v) (compute_operands (EL i bb.bb_instructions)) ==>
    MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by
    metis_tac[native_live_boundary_operands] >>
  reverse conj_tac
  >- (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
        native_inst_live_boundary_step >> simp[]) >>
  drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    native_position_variable_origins >> simp[] >>
  disch_then (qspec_then `\v. ?db di. MEM db fn.fn_blocks /\
    MEM di db.bb_instructions /\ MEM v di.inst_outputs /\ MEM db.bb_label visited` mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem native_chronological_prefix:
  !k fn visited bb n ps dfg cfg halting qs.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    ~MEM bb.bb_label visited /\ n + k <= LENGTH bb.bb_instructions /\
    (!v. MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled ==>
      (?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
        MEM v di.inst_outputs /\ MEM db.bb_label visited) \/
      (?di. MEM di (TAKE n bb.bb_instructions) /\ MEM v di.inst_outputs)) /\
    native_live_boundary fn bb n ps /\
    (!j. n <= j /\ j < n+k ==>
      (EL j bb.bb_instructions).inst_opcode <> JMP /\
      (EL j bb.bb_instructions).inst_opcode <> PHI /\
      ~is_param_opcode (EL j bb.bb_instructions).inst_opcode) /\
    native_inst_prefix (liveness_analyze fn) dfg cfg fn bb.bb_label halting
      n (LENGTH bb.bb_instructions) (DROP n bb.bb_instructions) ps k qs ==>
    (!v. MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled ==>
      (?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
        MEM v di.inst_outputs /\ MEM db.bb_label visited) \/
      (?di. MEM di (TAKE (n+k) bb.bb_instructions) /\ MEM v di.inst_outputs)) /\
    native_live_boundary fn bb (n+k) qs
Proof
  Induct_on `k`
  >- (rpt gen_tac >> simp[native_inst_prefix_zero] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `native_inst_prefix _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[Once native_inst_prefix_cases] >> strip_tac >> gvs[] >>
  `n + k <= LENGTH bb.bb_instructions` by decide_tac >>
  `!j. n <= j /\ j < n+k ==>
    (EL j bb.bb_instructions).inst_opcode <> JMP /\
    (EL j bb.bb_instructions).inst_opcode <> PHI /\
    ~is_param_opcode (EL j bb.bb_instructions).inst_opcode` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!j. n <= j /\ j < n + SUC k ==> _`
       (qspec_then `j` mp_tac) >>
     (impl_tac >- decide_tac) >> simp[]) >>
  first_x_assum (qspecl_then [`fn`, `visited`, `bb`, `n`] mp_tac) >>
  disch_then (drule_at (Pat `native_inst_prefix _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[arithmeticTheory.ADD_COMM] >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `n + k < LENGTH bb.bb_instructions` by decide_tac >>
  `inst = EL (n+k) bb.bb_instructions` by
    (qpat_x_assum `DROP k (DROP n _) = _` mp_tac >>
     simp[DROP_DROP, arithmeticTheory.ADD_COMM, DROP_CONS_EL] >>
     strip_tac >> gvs[]) >>
  `rest = [] ==> LENGTH bb.bb_instructions = SUC (n+k)` by
    (strip_tac >>
     qpat_x_assum `DROP k (DROP n _) = _` (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >>
     simp[DROP_DROP, LENGTH_DROP] >> decide_tac) >>
  ` (if rest = [] then live_vars_at (liveness_analyze fn) bb.bb_label (LENGTH bb.bb_instructions)
      else live_vars_at (liveness_analyze fn) bb.bb_label (k + (n + 1))) =
     live_vars_at (liveness_analyze fn) bb.bb_label (SUC (n+k))` by
    (Cases_on `rest = []` >> simp[] >> AP_TERM_TAC >> decide_tac) >>
  gvs[] >>
  qpat_x_assum `!j. n <= j /\ j < n + SUC k ==> _`
    (qspec_then `k+n` mp_tac) >>
  (impl_tac >- decide_tac) >> strip_tac >>
  drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    native_chronological_step >>
  disch_then (qspec_then `visited` mp_tac) >>
  simp[arithmeticTheory.ADD_CLAUSES, arithmeticTheory.ADD_COMM] >>
  disch_then irule >> first_assum ACCEPT_TAC
QED

Theorem native_phi_prefix_inventory_origins:
  !k insts ps qs P lv dfg cfg fn lbl halt n total.
    EVERY (\inst. inst.inst_opcode = PHI /\ inst.inst_outputs <> [])
      (TAKE k insts) /\ k <= LENGTH insts /\
    (!v. MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled ==> P v) /\
    native_inst_prefix lv dfg cfg fn lbl halt n total insts ps k qs ==>
    !v. MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled ==>
      P v \/ ?di. MEM di (TAKE k insts) /\ MEM v di.inst_outputs
Proof
  Induct_on `k`
  >- (simp[native_inst_prefix_zero] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `native_inst_prefix _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[Once native_inst_prefix_cases] >> strip_tac >> gvs[] >>
  `k < LENGTH insts` by decide_tac >>
  `inst = EL k insts` by
    (qpat_x_assum `DROP k insts = _` mp_tac >>
     simp[DROP_CONS_EL] >> strip_tac >> gvs[]) >>
  `TAKE (SUC k) insts = TAKE k insts ++ [inst]` by
    simp[rich_listTheory.TAKE_SUC] >>
  `EVERY (\inst. inst.inst_opcode = PHI /\ inst.inst_outputs <> [])
      (TAKE k insts) /\ inst.inst_opcode = PHI /\ inst.inst_outputs <> []` by
    gvs[listTheory.EVERY_APPEND] >>
  `!v. MEM (Var v) ps'.ps_stack \/ Var v IN FDOM ps'.ps_spilled ==>
    P v \/ ?di. MEM di (TAKE k insts) /\ MEM v di.inst_outputs` by
    (qpat_x_assum `!insts ps qs P lv dfg cfg fn lbl halt n total. _` mp_tac >>
     disch_then (drule_at (Pat `native_inst_prefix _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     disch_then (qspec_then `P` mp_tac) >> simp[] >> metis_tac[]) >>
  gvs[generate_inst_plan_def] >>
  drule fnPlanLineagePhiInventoryTheory.generate_phi_plan_inventory_origins >>
  strip_tac >> rpt strip_tac >>
  first_x_assum (qspec_then `Var v` mp_tac) >> simp[] >>
  Cases_on `(EL k insts).inst_outputs` >> gvs[] >>
  metis_tac[listTheory.MEM_APPEND, listTheory.MEM]
QED

Theorem native_phi_worker_chronological_origins:
  !fn bb visited ps qs k lv dfg cfg lbl halt n total.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
    k <= LENGTH (collect_phis bb.bb_instructions) /\
    (!v. MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled ==>
      ?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
        MEM v di.inst_outputs /\ MEM db.bb_label visited) /\
    native_inst_prefix lv dfg cfg fn lbl halt n total (non_param_insts bb) ps k qs ==>
    !v. MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled ==>
      (?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
        MEM v di.inst_outputs /\ MEM db.bb_label visited) \/
      (?di. MEM di (TAKE k bb.bb_instructions) /\ MEM v di.inst_outputs)
Proof
  rpt gen_tac >> strip_tac >>
  qspec_then `bb` (qx_choose_then `tail` assume_tac) non_param_insts_phi_prefix >>
  qspec_then `bb.bb_instructions` (qx_choose_then `rest` assume_tac)
    fnPlanLineageLivenessTheory.collect_phis_prefix >>
  `TAKE k (non_param_insts bb) = TAKE k (collect_phis bb.bb_instructions) /\
   TAKE k bb.bb_instructions = TAKE k (collect_phis bb.bb_instructions)` by
    metis_tac[listTheory.TAKE_APPEND1] >>
  `k <= LENGTH (non_param_insts bb)` by
    (qpat_x_assum `non_param_insts bb = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
     simp[] >> decide_tac) >>
  `EVERY (\inst. inst.inst_opcode = PHI /\ inst.inst_outputs <> [])
    (TAKE k (non_param_insts bb))` by
    (simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
     `MEM inst (collect_phis bb.bb_instructions)` by metis_tac[rich_listTheory.MEM_TAKE] >>
     `inst.inst_opcode = PHI /\ MEM inst bb.bb_instructions` by
       metis_tac[livenessTransferProofsTheory.collect_phis_mem] >>
     `inst_wf inst` by
       (gvs[codegen_ready_fn_def, fn_inst_wf_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
     gvs[inst_wf_def] >> Cases_on `inst.inst_outputs` >> gvs[]) >>
  drule_at (Pat `native_inst_prefix _ _ _ _ _ _ _ _ _ _ _ _`)
    native_phi_prefix_inventory_origins >>
  disch_then (qspec_then `\v. ?db di. MEM db fn.fn_blocks /\
    MEM di db.bb_instructions /\ MEM v di.inst_outputs /\ MEM db.bb_label visited` mp_tac) >>
  simp[] >> disch_tac >> gen_tac >> disch_tac >>
  first_x_assum irule >> conj_tac >- first_assum ACCEPT_TAC >> simp[]
QED

Theorem native_phi_worker_output_fresh:
  !fn bb visited ps qs k lv dfg cfg lbl halt n total.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
    ~MEM bb.bb_label visited /\ k < LENGTH (collect_phis bb.bb_instructions) /\
    (!v. MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled ==>
      ?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
        MEM v di.inst_outputs /\ MEM db.bb_label visited) /\
    native_inst_prefix lv dfg cfg fn lbl halt n total (non_param_insts bb) ps k qs ==>
    EVERY (\v. ~MEM (Var v) qs.ps_stack /\ Var v NOTIN FDOM qs.ps_spilled)
      (EL k (non_param_insts bb)).inst_outputs
Proof
  rpt gen_tac >> strip_tac >>
  `k <= LENGTH (collect_phis bb.bb_instructions)` by decide_tac >>
  `!v. MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled ==>
      (?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
        MEM v di.inst_outputs /\ MEM db.bb_label visited) \/
      (?di. MEM di (TAKE k bb.bb_instructions) /\ MEM v di.inst_outputs)` by
    (drule_at (Pat `native_inst_prefix _ _ _ _ _ _ _ _ _ _ _ _`)
       native_phi_worker_chronological_origins >>
     disch_then (qspec_then `visited` mp_tac) >> simp[] >>
     disch_tac >> gen_tac >> disch_tac >> first_x_assum irule >>
     conj_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  qspec_then `bb` (qx_choose_then `tail` assume_tac) non_param_insts_phi_prefix >>
  qspec_then `bb.bb_instructions` (qx_choose_then `rest` assume_tac)
    fnPlanLineageLivenessTheory.collect_phis_prefix >>
  `EL k (non_param_insts bb) = EL k bb.bb_instructions` by
    metis_tac[listTheory.EL_APPEND_EQN] >>
  `k < LENGTH bb.bb_instructions` by
    (qpat_x_assum `bb.bb_instructions = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
     simp[] >> decide_tac) >>
  `ssa_form fn` by gvs[codegen_ready_fn_def] >>
  simp[] >> irule chronological_origin_output_fresh >> metis_tac[]
QED

Theorem native_phi_worker_live_step:
  !fn bb visited ps qs rs k dfg cfg halt inst rest ops dist out.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    ~MEM bb.bb_label visited /\ k < LENGTH (collect_phis bb.bb_instructions) /\
    (!v. MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled ==>
      ?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
        MEM v di.inst_outputs /\ MEM db.bb_label visited) /\
    native_inst_prefix (liveness_analyze fn) dfg cfg fn bb.bb_label halt
      (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
      (non_param_insts bb) ps k qs /\
    DROP k (non_param_insts bb) = inst::rest /\
    inst.inst_outputs = [out] /\
    stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) qs.ps_stack = SOME dist /\
    native_live_boundary fn bb (LENGTH (get_params bb.bb_instructions) + k) qs /\
    generate_inst_plan (liveness_analyze fn) dfg cfg fn inst
      (if rest = [] then live_vars_at (liveness_analyze fn) bb.bb_label (LENGTH bb.bb_instructions)
       else live_vars_at (liveness_analyze fn) bb.bb_label
         (k + LENGTH (get_params bb.bb_instructions) + 1)) halt
      (case rest of [] => F | h::t => is_terminator h.inst_opcode)
      bb.bb_label qs = SOME (ops,rs) ==>
    native_live_boundary fn bb (LENGTH (get_params bb.bb_instructions) + SUC k) rs
Proof
  rpt gen_tac >> strip_tac >>
  `k < LENGTH (non_param_insts bb)` by
    (qspec_then `bb` (qx_choose_then `tail` assume_tac) non_param_insts_phi_prefix >>
     gvs[] >> decide_tac) >>
  `inst = EL k (non_param_insts bb)` by
    (qpat_x_assum `DROP k _ = _` mp_tac >> simp[DROP_CONS_EL] >> strip_tac >> gvs[]) >>
  `inst = EL (LENGTH (get_params bb.bb_instructions) + k) bb.bb_instructions` by
    metis_tac[fnPlanLineageCallersTheory.ready_block_suffix_index] >>
  `inst.inst_opcode = PHI` by
    (qspec_then `bb` (qx_choose_then `tail` assume_tac) non_param_insts_phi_prefix >>
     `MEM inst (collect_phis bb.bb_instructions)` by
       metis_tac[listTheory.EL_APPEND_EQN, listTheory.EL_MEM] >>
     metis_tac[livenessTransferProofsTheory.collect_phis_mem]) >>
  `EVERY (\v. ~MEM (Var v) qs.ps_stack /\ Var v NOTIN FDOM qs.ps_spilled)
    inst.inst_outputs` by
    (drule_at (Pat `native_inst_prefix _ _ _ _ _ _ _ _ _ _ _ _`)
       native_phi_worker_output_fresh >>
     disch_then (qspec_then `visited` mp_tac) >> simp[] >>
     (impl_tac >- first_assum ACCEPT_TAC) >> gvs[]) >>
  `LENGTH (get_params bb.bb_instructions) + k < LENGTH bb.bb_instructions` by
    (drule_all fnPlanLineageCallersTheory.ready_block_parameter_suffix >>
     disch_then (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]) >>
  `(if rest = [] then live_vars_at (liveness_analyze fn) bb.bb_label (LENGTH bb.bb_instructions)
    else live_vars_at (liveness_analyze fn) bb.bb_label
      (k + LENGTH (get_params bb.bb_instructions) + 1)) =
    live_vars_at (liveness_analyze fn) bb.bb_label
      (SUC (LENGTH (get_params bb.bb_instructions) + k))` by
    (irule fnPlanLineageCallersTheory.ready_block_suffix_next_live >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  gvs[] >>
  qpat_x_assum `EL _ bb.bb_instructions = EL _ (non_param_insts bb)`
    (fn th => rule_assum_tac (REWRITE_RULE [GSYM th])) >>
  drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    native_phi_live_boundary_step >>
  disch_then (qspecl_then [`out`, `dist`] mp_tac) >>
  simp[arithmeticTheory.ADD_CLAUSES]
QED
