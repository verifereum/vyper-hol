Theory fnPlanLineageChronologicalPrefix
Ancestors
  fnPlanLineageNativeResources fnPlanLineageNativeOrigins fnPlanLineageNativeTerminal
  fnPlanLineageEntryProduction fnPlanLineagePath fnPlanLineageCallers
  fnPlanLineagePhiLiveBudget fnPlanLineageLiveness stackPlanGen venomWf venomInst
  list rich_list finite_map callLayoutDefs

(* Native origins at a boundary exclude definitions throughout a later interval.
   This says nothing about chronological freshness on runtime revisits. *)
Theorem chronological_origin_interval_outputs_fresh:
  !fn visited bb a j ps.
    ssa_form fn /\ MEM bb fn.fn_blocks /\ ~MEM bb.bb_label visited /\
    a <= j /\ j < LENGTH bb.bb_instructions /\
    (!v. MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled ==>
      (?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
        MEM v di.inst_outputs /\ MEM db.bb_label visited) \/
      (?di. MEM di (TAKE a bb.bb_instructions) /\ MEM v di.inst_outputs)) ==>
    !k. a <= k /\ k <= j ==>
      EVERY (\v. ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled)
        (EL k bb.bb_instructions).inst_outputs
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  irule chronological_origin_output_fresh >> simp[] >>
  qexistsl_tac [`fn`, `visited`] >> simp[] >>
  rpt strip_tac >>
  `set (TAKE a bb.bb_instructions) SUBSET set (TAKE k bb.bb_instructions)` by
    (`TAKE a bb.bb_instructions = TAKE a (TAKE k bb.bb_instructions)` by
       simp[rich_listTheory.TAKE_TAKE_T] >>
     pop_assum SUBST1_TAC >> irule LIST_TO_SET_TAKE) >>
  gvs[pred_setTheory.SUBSET_DEF] >> metis_tac[]
QED

Theorem native_ordinary_interval_residual_exclusion:
  !fn visited bb a j ps prefix suffix.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    ~MEM bb.bb_label visited /\ a <= j /\ j < LENGTH bb.bb_instructions /\
    (!v. MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled ==>
      (?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
        MEM v di.inst_outputs /\ MEM db.bb_label visited) \/
      (?di. MEM di (TAKE a bb.bb_instructions) /\ MEM v di.inst_outputs)) /\
    native_live_boundary fn bb a ps /\ ps.ps_stack = prefix ++ suffix /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label a) ==>
      MEM (Var v) suffix) ==>
    EVERY (\v. ~MEM (Var v) prefix)
      (live_vars_at (liveness_analyze fn) bb.bb_label a) /\
    (!k. a <= k /\ k <= j ==>
      EVERY (\v. ~MEM (Var v) prefix) (EL k bb.bb_instructions).inst_outputs) /\
    EVERY (\v. ~MEM (Var v) prefix)
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC j) ++
       (EL j bb.bb_instructions).inst_outputs) /\
    (!v. MEM (Var v) (compute_operands (EL j bb.bb_instructions)) ==>
      ~MEM (Var v) prefix)
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (\v. ~MEM (Var v) prefix)
     (live_vars_at (liveness_analyze fn) bb.bb_label a)` by
    (simp[EVERY_MEM] >> metis_tac[native_live_boundary_suffix_exclusion]) >>
  `ssa_form fn` by gvs[codegen_ready_fn_def] >>
  `!k. a <= k /\ k <= j ==>
     EVERY (\v. ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled)
       (EL k bb.bb_instructions).inst_outputs` by
    (gen_tac >> strip_tac >>
     irule chronological_origin_interval_outputs_fresh >>
     qexistsl_tac [`a`, `fn`, `j`, `visited`] >> gvs[MEM_APPEND] >> metis_tac[]) >>
  `!k. a <= k /\ k <= j ==>
     EVERY (\v. ~MEM (Var v) prefix) (EL k bb.bb_instructions).inst_outputs` by
    (gvs[EVERY_MEM, MEM_APPEND] >> metis_tac[]) >>
  simp[] >> conj_tac
  >- (drule_all ordinary_interval_prefix_exclusion >> simp[]) >>
  rpt strip_tac >> drule_all interval_computed_query_origin >>
  gvs[EVERY_MEM] >> metis_tac[arithmeticTheory.LESS_IMP_LESS_OR_EQ]
QED

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

(* Exact copies from fnFrameCleanStackTheory: importing the frame theory here
   would pull the frame simulation back into planner-only resource leaves. *)
Theorem mark_dead_stack_mem:
  !retained stk op.
    MEM op (mark_dead_stack retained stk) ==>
    op = dead_stack_marker \/ MEM op stk
Proof
  simp[mark_dead_stack_def, MEM_MAP] >> metis_tac[]
QED

Theorem clean_stack_plan_inventory:
  !ps liveness cfg fn bb ops ps'.
    clean_stack_plan liveness cfg fn bb ps = (ops, ps') ==>
    !op. MEM op ps'.ps_stack \/ op IN FDOM ps'.ps_spilled ==>
      op = dead_stack_marker \/ MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> simp[clean_stack_plan_def] >>
  Cases_on `cfg_preds_of cfg bb.bb_label`
  >- (simp[] >> rpt strip_tac >> gvs[]) >> simp[] >>
  Cases_on `t` >> simp[]
  >- (IF_CASES_TAC
      >- (simp[] >> rpt strip_tac >> gvs[]) >>
      Cases_on `lookup_block h fn.fn_blocks`
      >- (simp[] >> rpt strip_tac >> gvs[]) >> simp[] >>
      qmatch_goalsub_abbrev_tac `if guard then _ else _` >>
      IF_CASES_TAC
      >- (strip_tac >> gvs[MEM_MAP] >> metis_tac[]) >>
      IF_CASES_TAC
      >- (pairarg_tac >> strip_tac >> gvs[] >>
          metis_tac[mark_dead_stack_mem,
            fnPlanLineageInventoryTheory.popmany_plan_inventory_subset]) >>
      metis_tac[fnPlanLineageInventoryTheory.popmany_plan_inventory_subset]) >>
  strip_tac >> gvs[]
QED

Theorem clean_stack_plan_chronological_support:
  !fn visited ps lv cfg bb ops qs.
    chronological_support fn visited ps /\
    clean_stack_plan lv cfg fn bb ps = (ops,qs) ==>
    chronological_support fn visited qs
Proof
  rpt gen_tac >> strip_tac >>
  drule clean_stack_plan_inventory >> strip_tac >>
  gvs[chronological_support_def] >> rpt strip_tac >>
  `MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by
    (first_x_assum (qspec_then `Var v` mp_tac) >>
     simp[dead_stack_marker_def] >> metis_tac[]) >>
  metis_tac[]
QED

(* Exact copy of fnBlockStepHelpersTheory.nonentry_block_no_params;
   planner leaves must not import frame-step helper theories. *)
Theorem nonentry_block_no_params:
  !fn lbl bb.
    canonical_param_prefix fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
    bb <> HD fn.fn_blocks ==>
    get_params bb.bb_instructions = [] /\
    non_param_insts bb = bb.bb_instructions
Proof
  rpt gen_tac >> strip_tac >>
  drule venomExecPropsTheory.lookup_block_MEM >> strip_tac >>
  `no_param_insts bb.bb_instructions` by
    (Cases_on `fn.fn_blocks` >> gvs[canonical_param_prefix_def, EVERY_MEM]) >>
  gvs[no_param_insts_def] >>
  conj_tac >- (Cases_on `bb.bb_instructions` >> gvs[get_params_def]) >>
  simp[non_param_insts_def, FILTER_EQ_ID, EVERY_MEM]
QED

Theorem ready_unique_nonentry_worker_shape:
  !fn lbl bb.
    codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
    bb <> HD fn.fn_blocks /\ LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1 ==>
    get_params bb.bb_instructions = [] /\
    non_param_insts bb = bb.bb_instructions /\
    bb.bb_instructions <> [] /\
    (!i. i < LENGTH bb.bb_instructions ==>
      (EL i bb.bb_instructions).inst_opcode <> PHI /\
      ~is_param_opcode (EL i bb.bb_instructions).inst_opcode) /\
    (!i. i < PRE (LENGTH bb.bb_instructions) ==>
      (EL i bb.bb_instructions).inst_opcode <> JMP)
Proof
  rpt gen_tac >> strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `canonical_param_prefix fn /\ bb_well_formed bb` by
    (gvs[codegen_ready_fn_def, wf_function_def] >> metis_tac[]) >>
  drule_all nonentry_block_no_params >> strip_tac >> simp[] >>
  `collect_phis bb.bb_instructions = []` by
    (gvs[codegen_ready_fn_def, phis_at_joins_def, EVERY_MEM] >>
     first_x_assum (qspec_then `bb` mp_tac) >>
     `bb.bb_label = lbl` by metis_tac[venomExecPropsTheory.lookup_block_label] >> simp[NULL_EQ]) >>
  `no_param_insts bb.bb_instructions` by
    (Cases_on `fn.fn_blocks` >> gvs[canonical_param_prefix_def, EVERY_MEM]) >>
  conj_tac >- gvs[bb_well_formed_def] >> conj_tac
  >- (rpt strip_tac
      >- metis_tac[well_formed_no_collected_phi] >>
      gvs[no_param_insts_def, EVERY_MEM] >> metis_tac[EL_MEM]) >>
  rpt strip_tac >> CCONTR_TAC >> gvs[bb_well_formed_def] >>
  qpat_x_assum `!i. _ /\ is_terminator _ ==> _` (qspec_then `i` mp_tac) >>
  simp[is_terminator_def] >> decide_tac
QED

Theorem unique_nonentry_cleaned_prefix:
  !fn pred pred_bb lbl bb visited after incoming clean_ops cleaned dfg k qs.
    codegen_ready_fn fn /\ cfg_reachable_of (cfg_analyze fn) pred /\
    fn_reachable fn bb.bb_label /\ lookup_block pred fn.fn_blocks = SOME pred_bb /\
    lookup_block lbl fn.fn_blocks = SOME bb /\ bb <> HD fn.fn_blocks /\
    MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
    LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1 /\ ~MEM bb.bb_label visited /\
    chronological_support fn visited after /\
    native_live_boundary fn pred_bb (LENGTH pred_bb.bb_instructions) after /\
    incoming.ps_stack = after.ps_stack /\ incoming.ps_spilled = after.ps_spilled /\
    clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb incoming = (clean_ops,cleaned) /\
    k <= PRE (LENGTH bb.bb_instructions) /\
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) cleaned k qs ==>
    (!v. MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled ==>
      (?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
        MEM v di.inst_outputs /\ MEM db.bb_label visited) \/
      (?di. MEM di (TAKE k bb.bb_instructions) /\ MEM v di.inst_outputs)) /\
    native_live_boundary fn bb k qs
Proof
  rpt gen_tac >> strip_tac >>
  drule_all ready_unique_nonentry_worker_shape >> strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `chronological_support fn visited incoming` by
    metis_tac[chronological_support_physical_cong] >>
  `chronological_support fn visited cleaned` by
    metis_tac[clean_stack_plan_chronological_support] >>
  `native_live_boundary fn bb 0 cleaned` by
    (drule_all analyzed_single_pred_physical_clean_live_boundary >> simp[]) >>
  `!j. 0 <= j /\ j < k ==>
    (EL j bb.bb_instructions).inst_opcode <> JMP /\
    (EL j bb.bb_instructions).inst_opcode <> PHI /\
    ~is_param_opcode (EL j bb.bb_instructions).inst_opcode` by
    (rpt strip_tac >> `j < PRE (LENGTH bb.bb_instructions) /\
      j < LENGTH bb.bb_instructions` by decide_tac >> metis_tac[]) >>
  gvs[chronological_support_def] >>
  qspec_then `k` mp_tac
    (INST_TYPE [alpha |-> ``:cfg_analysis``] native_chronological_prefix) >>
  disch_then (qspecl_then [`fn`, `visited`, `bb`, `0`] mp_tac) >>
  simp[] >> disch_then irule >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem native_chronological_terminal_step:
  !fn visited bb dfg ps ops qs.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    ~MEM bb.bb_label visited /\ bb.bb_instructions <> [] /\
    (LAST bb.bb_instructions).inst_opcode <> PHI /\
    ~is_param_opcode (LAST bb.bb_instructions).inst_opcode /\
    (!v. MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled ==>
      (?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
        MEM v di.inst_outputs /\ MEM db.bb_label visited) \/
      (?di. MEM di (TAKE (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions) /\
        MEM v di.inst_outputs)) /\
    native_live_boundary fn bb (PRE (LENGTH bb.bb_instructions)) ps /\
    generate_inst_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (LAST bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (LENGTH bb.bb_instructions))
      (bb_is_halting bb) F bb.bb_label ps = SOME (ops,qs) ==>
    chronological_support fn (bb.bb_label::visited) qs /\
    native_live_boundary fn bb (LENGTH bb.bb_instructions) qs
Proof
  rpt gen_tac >> strip_tac >>
  `SUC (PRE (LENGTH bb.bb_instructions)) = LENGTH bb.bb_instructions /\
   PRE (LENGTH bb.bb_instructions) < LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> gvs[]) >>
  `EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions = LAST bb.bb_instructions` by
    metis_tac[LAST_EL] >>
  Cases_on `(LAST bb.bb_instructions).inst_opcode = JMP`
  >- (drule_all native_terminal_jmp_live_boundary >> disch_tac >>
      drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
        native_terminal_jmp_variable_origins >> simp[] >> disch_tac >>
      simp[chronological_support_def] >> rpt strip_tac >>
      `MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by metis_tac[] >>
      gvs[] >> metis_tac[rich_listTheory.MEM_TAKE]) >>
  qspecl_then [`fn`, `visited`, `bb`, `PRE (LENGTH bb.bb_instructions)`] mp_tac
    (INST_TYPE [alpha |-> ``:cfg_analysis``] native_chronological_step) >>
  simp[] >>
  disch_then (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  simp[chronological_support_def] >> rpt strip_tac >>
  metis_tac[]
QED

Theorem unique_nonentry_cleaned_worker_exit:
  !fn pred pred_bb lbl bb visited after incoming clean_ops cleaned dfg ops qs.
    codegen_ready_fn fn /\ cfg_reachable_of (cfg_analyze fn) pred /\
    fn_reachable fn bb.bb_label /\ lookup_block pred fn.fn_blocks = SOME pred_bb /\
    lookup_block lbl fn.fn_blocks = SOME bb /\ bb <> HD fn.fn_blocks /\
    MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
    LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1 /\ ~MEM bb.bb_label visited /\
    chronological_support fn visited after /\
    native_live_boundary fn pred_bb (LENGTH pred_bb.bb_instructions) after /\
    incoming.ps_stack = after.ps_stack /\ incoming.ps_spilled = after.ps_spilled /\
    clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb incoming = (clean_ops,cleaned) /\
    generate_block_insts_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) 0 (non_param_insts bb) cleaned = SOME (ops,qs) ==>
    chronological_support fn (bb.bb_label::visited) qs /\
    native_live_boundary fn bb (LENGTH bb.bb_instructions) qs
Proof
  rpt gen_tac >> strip_tac >>
  drule_all ready_unique_nonentry_worker_shape >> strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label
    (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
    (LENGTH bb.bb_instructions) (non_param_insts bb) cleaned 0 cleaned` by
    metis_tac[native_inst_prefix_rules] >>
  drule_at (Pat `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _`)
    native_worker_terminal_prefix >>
  disch_then (qspecl_then [`non_param_insts bb`, `cleaned`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[DROP_0, arithmeticTheory.ADD_CLAUSES])) >>
  strip_tac >>
  `(!v. MEM (Var v) before.ps_stack \/ Var v IN FDOM before.ps_spilled ==>
      (?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
        MEM v di.inst_outputs /\ MEM db.bb_label visited) \/
      (?di. MEM di (TAKE (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions) /\
        MEM v di.inst_outputs)) /\
    native_live_boundary fn bb (PRE (LENGTH bb.bb_instructions)) before` by
    (irule unique_nonentry_cleaned_prefix >> goal_assum (drule_at Any) >>
     gvs[] >> metis_tac[]) >>
  `PRE (LENGTH bb.bb_instructions) < LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> gvs[]) >>
  `EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions = LAST bb.bb_instructions` by
    metis_tac[LAST_EL] >>
  `~is_param_opcode (LAST bb.bb_instructions).inst_opcode /\
   (LAST bb.bb_instructions).inst_opcode <> PHI` by metis_tac[] >>
  irule native_chronological_terminal_step >> goal_assum (drule_at Any) >>
  gvs[] >> metis_tac[]
QED

Theorem unique_nonentry_block_exit:
  !fn pred pred_bb lbl bb visited after incoming dfg ops qs.
    codegen_ready_fn fn /\ cfg_reachable_of (cfg_analyze fn) pred /\
    fn_reachable fn bb.bb_label /\ lookup_block pred fn.fn_blocks = SOME pred_bb /\
    lookup_block lbl fn.fn_blocks = SOME bb /\ bb <> HD fn.fn_blocks /\
    MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
    LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1 /\ ~MEM bb.bb_label visited /\
    chronological_support fn visited after /\
    native_live_boundary fn pred_bb (LENGTH pred_bb.bb_instructions) after /\
    incoming.ps_stack = after.ps_stack /\ incoming.ps_spilled = after.ps_spilled /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb incoming =
      SOME (ops,qs) ==>
    chronological_support fn (bb.bb_label::visited) qs /\
    native_live_boundary fn bb (LENGTH bb.bb_instructions) qs
Proof
  rpt gen_tac >> strip_tac >>
  `bb.bb_label = lbl` by metis_tac[venomExecPropsTheory.lookup_block_label] >>
  qpat_x_assum `generate_block_plan _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_block_plan_def] >> pairarg_tac >>
  simp[AllCaseEqs()] >> strip_tac >>
  metis_tac[unique_nonentry_cleaned_worker_exit]
QED

Theorem incoming_join_native_phi_live_prefix:
  !k fn entry lbl bb pred pb dfg ps0 ops ps visited qs.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    fn_reachable fn lbl /\ lbl <> entry /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    lookup_block pred fn.fn_blocks = SOME pb /\
    MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
    1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl) /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb ps0 = SOME (ops,ps) /\
    chronological_support fn visited ps /\ ~MEM bb.bb_label visited /\
    native_live_boundary fn bb (LENGTH (get_params bb.bb_instructions)) ps /\
    k <= LENGTH (collect_phis bb.bb_instructions) /\
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) ps k qs ==>
    native_live_boundary fn bb (LENGTH (get_params bb.bb_instructions) + k) qs
Proof
  Induct >- simp[native_inst_prefix_zero] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `native_inst_prefix _ _ _ _ _ _ _ _ _ _ (SUC _) _` mp_tac >>
  simp[Once native_inst_prefix_cases] >> strip_tac >>
  `k <= LENGTH (collect_phis bb.bb_instructions) /\
   k < LENGTH (collect_phis bb.bb_instructions)` by decide_tac >>
  `native_live_boundary fn bb (LENGTH (get_params bb.bb_instructions) + k) ps'` by
    (first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `bb.bb_label = lbl /\ MEM bb fn.fn_blocks` by
    metis_tac[venomExecPropsTheory.lookup_block_label, venomExecPropsTheory.lookup_block_MEM] >>
  `!v. MEM (Var v) ps.ps_stack ==>
    ?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
      MEM v di.inst_outputs /\ MEM db.bb_label visited` by
    gvs[chronological_support_def] >>
  `?dist w. stack_get_phi_depth
      (FILTER is_var_operand (EL k (collect_phis bb.bb_instructions)).inst_operands)
      ps'.ps_stack = SOME dist /\
    stack_peek dist ps'.ps_stack = Var w /\
    MEM (Var w) (EL k (collect_phis bb.bb_instructions)).inst_operands` by
    (irule incoming_join_native_phi_prefix_selection >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     goal_assum (drule_at (Pat `native_inst_prefix _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)) >>
     simp[] >> metis_tac[]) >>
  qspec_then `bb` (qx_choose_then `tail` assume_tac) non_param_insts_phi_prefix >>
  `inst = EL k (non_param_insts bb)` by
    (qpat_x_assum `DROP k _ = _` mp_tac >> simp[DROP_CONS_EL] >> strip_tac >> gvs[]) >>
  `inst = EL k (collect_phis bb.bb_instructions)` by
    metis_tac[EL_APPEND_EQN] >>
  `MEM inst (collect_phis bb.bb_instructions)` by metis_tac[EL_MEM] >>
  `inst.inst_opcode = PHI /\ MEM inst bb.bb_instructions` by
    metis_tac[livenessTransferProofsTheory.collect_phis_mem] >>
  `inst_wf inst` by
    (gvs[codegen_ready_fn_def, fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `?out. inst.inst_outputs = [out]` by
    (qpat_x_assum `inst_wf inst` mp_tac >>
     simp[inst_wf_def, GSYM LENGTH_EQ_1]) >>
  qpat_x_assum `!fn entry lbl bb pred pb dfg ps0 ops ps visited qs. _` kall_tac >>
  qpat_x_assum `bb.bb_label = lbl` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `inst = EL k (collect_phis _)` (SUBST_ALL_TAC o SYM) >>
  rule_assum_tac (PURE_REWRITE_RULE [arithmeticTheory.ADD_ASSOC]) >>
  irule (INST_TYPE [alpha |-> ``:cfg_analysis``]
    (PURE_REWRITE_RULE [arithmeticTheory.ADD_ASSOC] native_phi_worker_live_step)) >>
  ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
  goal_assum (drule_at Any) >>
  fs[chronological_support_def] >>
  qexistsl_tac [`cfg_analyze fn`, `dfg`, `dist`, `bb_is_halting bb`, `ops'`,
    `ps`, `ps'`, `visited`] >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem incoming_join_native_phi_protected_prefix:
  !k fn entry lbl bb pred pb dfg ps0 ops ps visited qs.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    fn_reachable fn lbl /\ lbl <> entry /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    lookup_block pred fn.fn_blocks = SOME pb /\
    cfg_reachable_of (cfg_analyze fn) pred /\
    MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
    1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl) /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb ps0 = SOME (ops,ps) /\
    chronological_support fn visited ps /\ ~MEM bb.bb_label visited /\
    native_live_boundary fn pb (LENGTH pb.bb_instructions) ps /\
    k <= LENGTH (collect_phis bb.bb_instructions) /\
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) ps k qs ==>
    !v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
          (LENGTH (collect_phis bb.bb_instructions))) /\
      EVERY (\inst. ~MEM v (inst_defs inst)) (DROP k (collect_phis bb.bb_instructions)) ==>
      LIST_ELEM_COUNT (Var v) qs.ps_stack +
        (if Var v IN FDOM qs.ps_spilled then 1 else 0) = 1
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >>
      gvs[native_inst_prefix_zero] >> rpt strip_tac >>
      `bb.bb_label = lbl /\ MEM bb fn.fn_blocks` by
        metis_tac[venomExecPropsTheory.lookup_block_label, venomExecPropsTheory.lookup_block_MEM] >>
      `MEM lbl (cfg_analyze fn).cfg_dfs_pre` by
        (gvs[codegen_ready_fn_def] >>
         metis_tac[removeUnusedSsaProofsTheory.fn_reachable_in_cfg_dfs_pre]) >>
      `phi_block_ready (liveness_analyze fn) bb` by
        (Cases_on `collect_phis bb.bb_instructions` >> gvs[]
         >- (gvs[phi_block_ready_def, phi_uses_disjoint_def]) >>
         `~NULL (collect_phis bb.bb_instructions)` by simp[] >>
         gvs[codegen_ready_fn_def, phi_operands_ready_def, EVERY_MEM] >>
         metis_tac[listTheory.NULL_EQ]) >>
      `((MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
        LIST_ELEM_COUNT (Var v) ps.ps_stack +
          (if Var v IN FDOM ps.ps_spilled then 1 else 0) <= 1)` by
        (irule analyzed_join_live_through_physical_seed >>
         goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
      Cases_on `Var v IN FDOM ps.ps_spilled` >> gvs[GSYM LIST_ELEM_COUNT_MEM]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `native_inst_prefix _ _ _ _ _ _ _ _ _ _ (SUC _) _` mp_tac >>
  simp[Once native_inst_prefix_cases] >> strip_tac >>
  `k <= LENGTH (collect_phis bb.bb_instructions) /\
   k < LENGTH (collect_phis bb.bb_instructions)` by decide_tac >>
  `!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
          (LENGTH (collect_phis bb.bb_instructions))) /\
       EVERY (\inst. ~MEM v (inst_defs inst)) (DROP k (collect_phis bb.bb_instructions)) ==>
       LIST_ELEM_COUNT (Var v) ps'.ps_stack +
         (if Var v IN FDOM ps'.ps_spilled then 1 else 0) = 1` by
    (metis_tac[]) >>
  `bb.bb_label = lbl /\ MEM bb fn.fn_blocks` by
    metis_tac[venomExecPropsTheory.lookup_block_label, venomExecPropsTheory.lookup_block_MEM] >>
  `!v. MEM (Var v) ps.ps_stack ==>
    ?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
      MEM v di.inst_outputs /\ MEM db.bb_label visited` by gvs[chronological_support_def] >>
  `?dist w. stack_get_phi_depth
      (FILTER is_var_operand (EL k (collect_phis bb.bb_instructions)).inst_operands)
      ps'.ps_stack = SOME dist /\ stack_peek dist ps'.ps_stack = Var w /\
      MEM (Var w) (EL k (collect_phis bb.bb_instructions)).inst_operands` by
    (irule incoming_join_native_phi_prefix_selection >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     goal_assum (drule_at (Pat `native_inst_prefix _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)) >>
     simp[] >> metis_tac[]) >>
  qspec_then `bb` (qx_choose_then `tail` assume_tac) non_param_insts_phi_prefix >>
  `inst = EL k (non_param_insts bb)` by
    (qpat_x_assum `DROP k _ = _` mp_tac >> simp[DROP_CONS_EL] >> strip_tac >> gvs[]) >>
  `inst = EL k (collect_phis bb.bb_instructions)` by metis_tac[EL_APPEND_EQN] >>
  `MEM inst (collect_phis bb.bb_instructions)` by metis_tac[EL_MEM] >>
  `inst.inst_opcode = PHI /\ MEM inst bb.bb_instructions` by
    metis_tac[livenessTransferProofsTheory.collect_phis_mem] >>
  `inst_wf inst` by
    (gvs[codegen_ready_fn_def, fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `?out. inst.inst_outputs = [out]` by
    (qpat_x_assum `inst_wf inst` mp_tac >> simp[inst_wf_def, GSYM LENGTH_EQ_1]) >>
  `EVERY (\v. ~MEM (Var v) ps'.ps_stack /\ Var v NOTIN FDOM ps'.ps_spilled)
      inst.inst_outputs` by
    (drule_at (Pat `native_inst_prefix _ _ _ _ _ _ _ _ _ _ _ _`)
      native_phi_worker_output_fresh >>
     disch_then (qspec_then `visited` mp_tac) >> simp[] >>
     (impl_tac >- gvs[chronological_support_def]) >>
     gvs[]) >>
  `bb <> HD fn.fn_blocks` by
    (Cases_on `fn.fn_blocks` >> gvs[fn_entry_label_def, entry_block_def] >>
     strip_tac >> gvs[]) >>
  `get_params bb.bb_instructions = [] /\ non_param_insts bb = bb.bb_instructions` by
    (qspecl_then [`fn`, `lbl`, `bb`] mp_tac nonentry_block_no_params >>
     simp[] >> (impl_tac >- gvs[codegen_ready_fn_def]) >> simp[]) >>
  `k < LENGTH (non_param_insts bb)` by
    (qpat_x_assum `non_param_insts bb = _ ++ _`
       (mp_tac o Q.AP_TERM `LENGTH`) >> simp[] >> decide_tac) >>
  qspecl_then [`fn`, `bb`, `liveness_analyze fn`] mp_tac ready_block_suffix_next_live >>
  disch_then drule_all >> strip_tac >>
  qpat_x_assum `!fn entry lbl bb pred pb dfg ps0 ops ps visited qs. _` kall_tac >>
  rpt strip_tac >>
  `MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k))` by
    (irule analyzed_phi_protected_demand >> simp[] >> metis_tac[]) >>
  `v <> out ==> EVERY (\inst. ~MEM v (inst_defs inst)) (DROP k (collect_phis bb.bb_instructions))` by
    (qspecl_then [`collect_phis bb.bb_instructions`, `k`, `v`] mp_tac
       phi_protected_demand_step >> simp[] >> gvs[inst_defs_def] >> metis_tac[]) >>
  `generate_phi_plan inst (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k))
     (bb_is_halting bb) ps' = (ops',qs)` by
    (qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[generate_inst_plan_def] >> gvs[]) >>
  `LIST_ELEM_COUNT (Var v) qs.ps_stack + (if Var v IN FDOM qs.ps_spilled then 1 else 0) =
     LIST_ELEM_COUNT (Var v) ps'.ps_stack + (if Var v IN FDOM ps'.ps_spilled then 1 else 0) +
       (if v = out then 1 else 0)` by
    (irule generate_phi_plan_live_count >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `LIST_ELEM_COUNT (Var out) ps'.ps_stack = 0 /\ Var out NOTIN FDOM ps'.ps_spilled` by
    (gvs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac) >>
  Cases_on `v = out`
  >- (gvs[] >>
      qpat_x_assum `!v. MEM v _ /\ EVERY _ _ ==> _` (qspec_then `out` mp_tac) >> simp[]) >>
  `LIST_ELEM_COUNT (Var v) ps'.ps_stack + (if Var v IN FDOM ps'.ps_spilled then 1 else 0) = 1` by metis_tac[] >>
  gvs[]
QED

Theorem incoming_join_native_phi_boundary:
  !fn entry lbl bb pred pb dfg ps0 ops ps visited qs.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    fn_reachable fn lbl /\ lbl <> entry /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    lookup_block pred fn.fn_blocks = SOME pb /\
    cfg_reachable_of (cfg_analyze fn) pred /\
    MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
    1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl) /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb ps0 = SOME (ops,ps) /\
    chronological_support fn visited ps /\ ~MEM bb.bb_label visited /\
    native_live_boundary fn pb (LENGTH pb.bb_instructions) ps /\
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) ps
      (LENGTH (collect_phis bb.bb_instructions)) qs ==>
    native_live_boundary fn bb (LENGTH (collect_phis bb.bb_instructions)) qs
Proof
  rpt gen_tac >> strip_tac >>
  `!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
        (LENGTH (collect_phis bb.bb_instructions))) ==>
      LIST_ELEM_COUNT (Var v) qs.ps_stack +
        (if Var v IN FDOM qs.ps_spilled then 1 else 0) = 1` by
    (drule_at (Pat `native_inst_prefix _ _ _ _ _ _ _ _ _ _ _ _`)
       incoming_join_native_phi_protected_prefix >> simp[] >> metis_tac[]) >>
  simp[native_live_boundary_def] >> rpt strip_tac >> first_x_assum drule >>
  Cases_on `Var v IN FDOM qs.ps_spilled` >> simp[GSYM LIST_ELEM_COUNT_MEM]
QED

Theorem native_inst_prefix_split:
  !k p lv dfg cfg fn lbl halt n total xs ps qs.
    native_inst_prefix lv dfg cfg fn lbl halt n total xs ps (p+k) qs ==>
    ?mid. native_inst_prefix lv dfg cfg fn lbl halt n total xs ps p mid /\
      native_inst_prefix lv dfg cfg fn lbl halt (n+p) total (DROP p xs) mid k qs
Proof
  Induct
  >- (rpt strip_tac >> qexists_tac `qs` >> fs[native_inst_prefix_zero]) >>
  rpt gen_tac >> rename1 `native_inst_prefix lv dfg cfg fn lbl halt n len xs ps _ qs` >>
  rewrite_tac[arithmeticTheory.ADD_CLAUSES] >> strip_tac >>
  qpat_x_assum `native_inst_prefix _ _ _ _ _ _ _ _ _ _ (SUC _) _` mp_tac >>
  simp[Once native_inst_prefix_cases] >> strip_tac >>
  `?mid. native_inst_prefix lv dfg cfg fn lbl halt n len xs ps p mid /\
     native_inst_prefix lv dfg cfg fn lbl halt (n+p) len (DROP p xs) mid k ps'` by
    metis_tac[arithmeticTheory.ADD_COMM] >>
  qexists_tac `mid` >> conj_tac >- first_assum ACCEPT_TAC >>
  irule (cj 2 native_inst_prefix_rules) >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`inst`, `ops`, `rest`] >>
  `k + (n + p) + 1 = k + (n + (p + 1))` by decide_tac >>
  simp[rich_listTheory.DROP_DROP_T]
QED

Theorem collect_phis_prefix_index:
  !xs i. i < LENGTH xs /\
    (!j. j <= i ==> (EL j xs).inst_opcode = PHI) ==>
    i < LENGTH (collect_phis xs)
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  `h.inst_opcode = PHI` by
    (qpat_x_assum `!j. j <= i ==> _` (qspec_then `0` mp_tac) >> simp[]) >>
  Cases_on `i` >> simp[livenessDefsTheory.collect_phis_def] >>
  first_x_assum irule >> gvs[] >> rpt strip_tac >>
  qpat_x_assum `!j. j <= SUC n ==> _` (qspec_then `SUC j` mp_tac) >> simp[]
QED

Theorem well_formed_phi_worker_shape:
  !bb. bb_well_formed bb ==>
    LENGTH (collect_phis bb.bb_instructions) <= PRE (LENGTH bb.bb_instructions) /\
    (!i. LENGTH (collect_phis bb.bb_instructions) <= i /\
      i < LENGTH bb.bb_instructions ==>
      (EL i bb.bb_instructions).inst_opcode <> PHI) /\
    (LAST bb.bb_instructions).inst_opcode <> PHI /\
    (!i. i < PRE (LENGTH bb.bb_instructions) ==>
      (EL i bb.bb_instructions).inst_opcode <> JMP)
Proof
  rpt gen_tac >> strip_tac >>
  `!i. i < LENGTH bb.bb_instructions /\
      (EL i bb.bb_instructions).inst_opcode = PHI ==>
      i < LENGTH (collect_phis bb.bb_instructions)` by
    (rpt strip_tac >> irule collect_phis_prefix_index >> simp[] >>
     rpt strip_tac >> Cases_on `j = i` >- simp[] >>
     gvs[bb_well_formed_def] >> metis_tac[arithmeticTheory.LESS_OR_EQ]) >>
  `bb.bb_instructions <> [] /\
    (LAST bb.bb_instructions).inst_opcode <> PHI` by
    (gvs[bb_well_formed_def] >> CCONTR_TAC >>
     gvs[is_terminator_def]) >>
  `PRE (LENGTH bb.bb_instructions) < LENGTH bb.bb_instructions /\
    EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions = LAST bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> gvs[LAST_EL]) >>
  `LENGTH (collect_phis bb.bb_instructions) <= LENGTH bb.bb_instructions` by
    (qspec_then `bb.bb_instructions` (qx_choose_then `rest` assume_tac) collect_phis_prefix >>
     pop_assum (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]) >>
  `LENGTH (collect_phis bb.bb_instructions) <> LENGTH bb.bb_instructions` by
    (strip_tac >>
     qspec_then `bb.bb_instructions` (qx_choose_then `rest` assume_tac) collect_phis_prefix >>
     `rest = []` by
       (qpat_x_assum `bb.bb_instructions = _ ++ rest`
          (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]) >>
     `MEM (LAST bb.bb_instructions) (collect_phis bb.bb_instructions)` by
       metis_tac[APPEND_NIL, rich_listTheory.LAST_MEM] >>
     metis_tac[livenessTransferProofsTheory.collect_phis_mem]) >>
  conj_tac >- decide_tac >> conj_tac >- metis_tac[arithmeticTheory.NOT_LESS] >>
  simp[] >> rpt strip_tac >> CCONTR_TAC >>
  gvs[bb_well_formed_def] >>
  qpat_x_assum `!i. _ /\ is_terminator _ ==> _` (qspec_then `i` mp_tac) >>
  simp[is_terminator_def] >> decide_tac
QED

Theorem native_phi_prefix_physical_transport:
  !k lv dfg cfg fn lbl halt n len xs ps qs incoming.
    native_inst_prefix lv dfg cfg fn lbl halt n len xs ps k qs /\
    EVERY (\inst. inst.inst_opcode = PHI) (TAKE k xs) /\
    incoming.ps_stack = ps.ps_stack /\ incoming.ps_spilled = ps.ps_spilled ==>
    ?result. native_inst_prefix lv dfg cfg fn lbl halt n len xs incoming k result /\
      result.ps_stack = qs.ps_stack /\ result.ps_spilled = qs.ps_spilled
Proof
  Induct >- (simp[native_inst_prefix_zero] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `native_inst_prefix _ _ _ _ _ _ _ _ _ _ (SUC _) _` mp_tac >>
  simp[Once native_inst_prefix_cases] >> strip_tac >>
  `k < LENGTH xs /\ inst = EL k xs` by
    (`k < LENGTH xs` by
       (qpat_x_assum `DROP k xs = _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[] >> decide_tac) >>
     qpat_x_assum `DROP k xs = _` mp_tac >> simp[DROP_CONS_EL]) >>
  `EVERY (\inst. inst.inst_opcode = PHI) (TAKE k xs) /\ inst.inst_opcode = PHI` by
    (qpat_x_assum `EVERY _ (TAKE (SUC k) xs)` mp_tac >>
     simp[rich_listTheory.TAKE_SUC_BY_TAKE, EVERY_SNOC]) >>
  `?mid. native_inst_prefix lv dfg cfg fn lbl halt n len xs incoming k mid /\
      mid.ps_stack = ps'.ps_stack /\ mid.ps_spilled = ps'.ps_spilled` by
    (first_x_assum irule >> metis_tac[]) >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_inst_plan_def, is_pre_codegen_opcode_def] >> strip_tac >>
  Cases_on `generate_phi_plan inst
    (if rest = [] then live_vars_at lv lbl len else live_vars_at lv lbl (k+n+1)) halt mid` >>
  qexists_tac `r` >> reverse conj_tac
  >- (drule_all fnPlanLineagePhiTemporalTheory.generate_phi_plan_physical_cong >>
      disch_then (qspecl_then [`inst`,
        `if rest = [] then live_vars_at lv lbl len else live_vars_at lv lbl (k+n+1)`, `halt`] mp_tac) >>
      gvs[]) >>
  irule (cj 2 native_inst_prefix_rules) >>
  goal_assum (drule_at Any) >> simp[generate_inst_plan_def, is_pre_codegen_opcode_def] >>
  gvs[]
QED

Theorem incoming_join_native_ordinary_prefix:
  !fn entry lbl bb pred pb dfg ps0 ops ps visited incoming k qs.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    cfg_reachable_of (cfg_analyze fn) pred /\
    fn_reachable fn lbl /\ lbl <> entry /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    lookup_block pred fn.fn_blocks = SOME pb /\
    MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
    1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl) /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb ps0 = SOME (ops,ps) /\
    chronological_support fn visited ps /\ ~MEM bb.bb_label visited /\
    native_live_boundary fn pb (LENGTH pb.bb_instructions) ps /\
    LENGTH (collect_phis bb.bb_instructions) <= k /\
    k <= PRE (LENGTH bb.bb_instructions) /\
    incoming.ps_stack = ps.ps_stack /\ incoming.ps_spilled = ps.ps_spilled /\
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) incoming k qs ==>
    (!v. MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled ==>
      (?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
        MEM v di.inst_outputs /\ MEM db.bb_label visited) \/
      (?di. MEM di (TAKE k bb.bb_instructions) /\ MEM v di.inst_outputs)) /\
    native_live_boundary fn bb k qs
Proof
  rpt gen_tac >> strip_tac >>
  `bb.bb_label = lbl /\ MEM bb fn.fn_blocks` by
    metis_tac[venomExecPropsTheory.lookup_block_label, venomExecPropsTheory.lookup_block_MEM] >>
  `bb <> HD fn.fn_blocks` by
    (Cases_on `fn.fn_blocks` >> gvs[fn_entry_label_def, entry_block_def] >> metis_tac[]) >>
  `canonical_param_prefix fn /\ bb_well_formed bb` by
    (gvs[codegen_ready_fn_def, wf_function_def] >> metis_tac[]) >>
  drule_all nonentry_block_no_params >> strip_tac >>
  drule well_formed_phi_worker_shape >> strip_tac >>
  `no_param_insts bb.bb_instructions` by
    (Cases_on `fn.fn_blocks` >> gvs[canonical_param_prefix_def, EVERY_MEM]) >>
  qabbrev_tac `p = LENGTH (collect_phis bb.bb_instructions)` >>
  `k = p + (k-p)` by decide_tac >>
  `?mid. native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
      (bb_is_halting bb) 0 (LENGTH bb.bb_instructions) bb.bb_instructions incoming p mid /\
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
      (bb_is_halting bb) p (LENGTH bb.bb_instructions) (DROP p bb.bb_instructions) mid (k-p) qs` by
    (qspecl_then [`k-p`, `p`] mp_tac
       (INST_TYPE [alpha |-> ``:cfg_analysis``] native_inst_prefix_split) >>
     simp[] >> disch_then drule >> simp[]) >>
  `EVERY (\inst. inst.inst_opcode = PHI) (TAKE p bb.bb_instructions)` by
    (`TAKE p bb.bb_instructions = collect_phis bb.bb_instructions` by
       (qspec_then `bb.bb_instructions` (qx_choose_then `tail` mp_tac) collect_phis_prefix >>
        disch_then (mp_tac o Q.AP_TERM `TAKE p`) >> simp[Abbr `p`, TAKE_LENGTH_APPEND]) >>
     simp[EVERY_MEM] >> metis_tac[livenessTransferProofsTheory.collect_phis_mem]) >>
  `?shadow. native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
      (bb_is_halting bb) 0 (LENGTH bb.bb_instructions) bb.bb_instructions ps p shadow /\
      shadow.ps_stack = mid.ps_stack /\ shadow.ps_spilled = mid.ps_spilled` by
    (irule (INST_TYPE [alpha |-> ``:cfg_analysis``] native_phi_prefix_physical_transport) >>
     simp[] >> qexists_tac `incoming` >> simp[]) >>
  `native_live_boundary fn bb p shadow` by
    (simp[Abbr `p`] >> irule incoming_join_native_phi_boundary >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     goal_assum (drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)) >>
     simp[] >>
     goal_assum (drule_at (Pat `native_inst_prefix _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     metis_tac[]) >>
  `native_live_boundary fn bb p mid` by gvs[native_live_boundary_def] >>
  `!v. MEM (Var v) mid.ps_stack \/ Var v IN FDOM mid.ps_spilled ==>
      (?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
        MEM v di.inst_outputs /\ MEM db.bb_label visited) \/
      (?di. MEM di (TAKE p bb.bb_instructions) /\ MEM v di.inst_outputs)` by
    (rpt strip_tac >>
     irule (INST_TYPE [alpha |-> ``:cfg_analysis``] native_phi_worker_chronological_origins) >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     simp[] >> goal_assum (drule_at (Pat `native_inst_prefix _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     simp[Abbr `p`] >> gvs[chronological_support_def] >> metis_tac[]) >>
  qspec_then `k-p` mp_tac
    (INST_TYPE [alpha |-> ``:cfg_analysis``] native_chronological_prefix) >>
  disch_then (qspecl_then [`fn`, `visited`, `bb`, `p`] mp_tac) >>
  simp[] >> disch_then irule >> conj_tac
  >- (gvs[no_param_insts_def, EVERY_MEM] >> rpt strip_tac >>
      `j < LENGTH bb.bb_instructions` by decide_tac >> metis_tac[EL_MEM]) >>
  goal_assum (drule_at (Pat `native_inst_prefix _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> first_assum ACCEPT_TAC
QED

Theorem incoming_join_native_worker_exit:
  !fn entry lbl bb pred pb dfg ps0 ops ps visited incoming chunks qs.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    cfg_reachable_of (cfg_analyze fn) pred /\
    fn_reachable fn lbl /\ lbl <> entry /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    lookup_block pred fn.fn_blocks = SOME pb /\
    MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
    1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl) /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb ps0 = SOME (ops,ps) /\
    chronological_support fn visited ps /\ ~MEM bb.bb_label visited /\
    native_live_boundary fn pb (LENGTH pb.bb_instructions) ps /\
    incoming.ps_stack = ps.ps_stack /\ incoming.ps_spilled = ps.ps_spilled /\
    generate_block_insts_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) 0 (non_param_insts bb) incoming = SOME (chunks,qs) ==>
    chronological_support fn (bb.bb_label::visited) qs /\
    native_live_boundary fn bb (LENGTH bb.bb_instructions) qs
Proof
  rpt gen_tac >> strip_tac >>
  `bb.bb_label = lbl /\ MEM bb fn.fn_blocks` by
    metis_tac[venomExecPropsTheory.lookup_block_label, venomExecPropsTheory.lookup_block_MEM] >>
  `bb <> HD fn.fn_blocks` by
    (Cases_on `fn.fn_blocks` >> gvs[fn_entry_label_def, entry_block_def] >> metis_tac[]) >>
  `canonical_param_prefix fn /\ bb_well_formed bb` by
    (gvs[codegen_ready_fn_def, wf_function_def] >> metis_tac[]) >>
  drule_all nonentry_block_no_params >> strip_tac >>
  drule well_formed_phi_worker_shape >> strip_tac >>
  `bb.bb_instructions <> []` by gvs[bb_well_formed_def] >>
  `no_param_insts bb.bb_instructions` by
    (Cases_on `fn.fn_blocks` >> gvs[canonical_param_prefix_def, EVERY_MEM]) >>
  `native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
    (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
    (LENGTH bb.bb_instructions) (non_param_insts bb) incoming 0 incoming` by
    metis_tac[native_inst_prefix_rules] >>
  drule_at (Pat `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _`)
    native_worker_terminal_prefix >>
  disch_then (qspecl_then [`non_param_insts bb`, `incoming`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[DROP_0, arithmeticTheory.ADD_CLAUSES]) >> strip_tac >> gvs[] >>
  `(!v. MEM (Var v) before.ps_stack \/ Var v IN FDOM before.ps_spilled ==>
      (?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
        MEM v di.inst_outputs /\ MEM db.bb_label visited) \/
      (?di. MEM di (TAKE (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions) /\
        MEM v di.inst_outputs)) /\
    native_live_boundary fn bb (PRE (LENGTH bb.bb_instructions)) before` by
    (irule incoming_join_native_ordinary_prefix >> simp[] >>
     goal_assum (drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)) >>
     simp[] >> goal_assum (drule_at (Pat `native_inst_prefix _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     metis_tac[]) >>
  `~is_param_opcode (LAST bb.bb_instructions).inst_opcode` by
    (gvs[no_param_insts_def, EVERY_MEM] >> metis_tac[rich_listTheory.LAST_MEM]) >>
  irule native_chronological_terminal_step >> simp[] >>
  goal_assum (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >> first_assum ACCEPT_TAC
QED

Theorem incoming_join_native_block_exit:
  !fn entry lbl bb pred pb dfg ps0 ops ps visited incoming block_ops qs.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    cfg_reachable_of (cfg_analyze fn) pred /\
    fn_reachable fn lbl /\ lbl <> entry /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    lookup_block pred fn.fn_blocks = SOME pb /\
    MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
    1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl) /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb ps0 = SOME (ops,ps) /\
    chronological_support fn visited ps /\ ~MEM bb.bb_label visited /\
    native_live_boundary fn pb (LENGTH pb.bb_instructions) ps /\
    incoming.ps_stack = ps.ps_stack /\ incoming.ps_spilled = ps.ps_spilled /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb incoming =
      SOME (block_ops,qs) ==>
    chronological_support fn (bb.bb_label::visited) qs /\
    native_live_boundary fn bb (LENGTH bb.bb_instructions) qs
Proof
  rpt gen_tac >> strip_tac >>
  `bb.bb_label = lbl /\ bb <> HD fn.fn_blocks` by
    (imp_res_tac venomExecPropsTheory.lookup_block_label >>
     Cases_on `fn.fn_blocks` >> gvs[fn_entry_label_def, entry_block_def] >> metis_tac[]) >>
  `LENGTH (cfg_preds_of (cfg_analyze fn) lbl) <> 1` by decide_tac >>
  qpat_x_assum `generate_block_plan _ _ _ _ bb incoming = _` mp_tac >>
  simp[generate_block_plan_def, AllCaseEqs()] >> strip_tac >>
  metis_tac[incoming_join_native_worker_exit]
QED

Theorem incoming_nonentry_block_exit:
  !fn entry lbl bb pred pb dfg ps0 ops ps visited incoming block_ops qs.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    cfg_reachable_of (cfg_analyze fn) pred /\
    fn_reachable fn lbl /\ lbl <> entry /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    lookup_block pred fn.fn_blocks = SOME pb /\
    MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb ps0 = SOME (ops,ps) /\
    chronological_support fn visited ps /\ ~MEM bb.bb_label visited /\
    native_live_boundary fn pb (LENGTH pb.bb_instructions) ps /\
    incoming.ps_stack = ps.ps_stack /\ incoming.ps_spilled = ps.ps_spilled /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb incoming =
      SOME (block_ops,qs) ==>
    chronological_support fn (bb.bb_label::visited) qs /\
    native_live_boundary fn bb (LENGTH bb.bb_instructions) qs
Proof
  rpt gen_tac >> strip_tac >>
  `bb.bb_label = lbl /\ bb <> HD fn.fn_blocks` by
    (imp_res_tac venomExecPropsTheory.lookup_block_label >>
     Cases_on `fn.fn_blocks` >> gvs[fn_entry_label_def, entry_block_def] >> metis_tac[]) >>
  Cases_on `LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1`
  >- metis_tac[unique_nonentry_block_exit] >>
  `MEM pred (cfg_preds_of (cfg_analyze fn) lbl)` by
    metis_tac[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond] >>
  `1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl)` by
    (Cases_on `cfg_preds_of (cfg_analyze fn) lbl` >> gvs[] >>
     rename1 `tail <> []` >> Cases_on `tail` >> gvs[]) >>
  metis_tac[incoming_join_native_block_exit]
QED
