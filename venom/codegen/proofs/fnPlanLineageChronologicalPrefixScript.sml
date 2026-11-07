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
