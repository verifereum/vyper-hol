Theory fnPlanLineageNativeOrigins
Ancestors
  fnPlanLineageSetup fnPlanLineagePhiInventory stackPlanGen stackModel
  list rich_list
Libs
  finite_mapTheory pred_setTheory

(* Native dispatch only transports old resources or current definitions.
   Operand availability is an explicit premise, not a consequence of SOME. *)
Theorem native_inst_variable_origins:
  !lv dfg cfg fn inst next halt term lbl ps ops qs.
    inst.inst_opcode <> JMP /\
    LENGTH (compute_operands inst) <= 16 /\
    ((inst.inst_opcode = PHI \/ inst.inst_opcode = OFFSET) ==>
      inst.inst_outputs <> []) /\
    (!v. MEM (Var v) (compute_operands inst) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    generate_inst_plan lv dfg cfg fn inst next halt term lbl ps = SOME (ops,qs)
    ==>
    !v. MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled \/
      MEM v inst.inst_outputs
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_inst_plan_def] >>
  Cases_on `is_pre_codegen_opcode inst.inst_opcode` >> simp[] >>
  Cases_on `inst.inst_opcode = INVOKE /\ ~invoke_operands_wf inst` >> simp[] >>
  Cases_on `inst.inst_opcode = PHI`
  >- (simp[] >> strip_tac >>
      drule generate_phi_plan_inventory_origins >>
      `MEM (HD inst.inst_outputs) inst.inst_outputs` by
        (Cases_on `inst.inst_outputs` >> gvs[]) >>
      disch_tac >> gen_tac >> strip_tac >>
      first_x_assum (qspec_then `Var v` mp_tac) >> simp[] >>
      strip_tac >> gvs[]) >>
  Cases_on `inst.inst_opcode = OFFSET`
  >- (simp[generate_offset_plan_def] >>
      Cases_on `EL 1 inst.inst_operands` >> simp[] >> strip_tac >> gvs[] >>
      simp[stack_push_def] >>
      `MEM (HD inst.inst_outputs) inst.inst_outputs` by
        (Cases_on `inst.inst_outputs` >> gvs[]) >>
      metis_tac[]) >>
  Cases_on `is_param_opcode inst.inst_opcode` >> simp[]
  >- (strip_tac >> gvs[] >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = NOP` >> simp[]
  >- (strip_tac >> gvs[] >> metis_tac[]) >>
  strip_tac >>
  drule_at (Pat `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    native_regular_variable_origins >> simp[] >> metis_tac[]
QED

(* Arbitrary incoming origins make this usable for both entry prefixes and
   visited-block chronology, without asserting either invariant globally. *)
Theorem native_position_variable_origins:
  !P lv dfg cfg fn bb i next halt term lbl ps ops qs.
    i < LENGTH bb.bb_instructions /\
    (EL i bb.bb_instructions).inst_opcode <> JMP /\
    LENGTH (compute_operands (EL i bb.bb_instructions)) <= 16 /\
    (((EL i bb.bb_instructions).inst_opcode = PHI \/
      (EL i bb.bb_instructions).inst_opcode = OFFSET) ==>
      (EL i bb.bb_instructions).inst_outputs <> []) /\
    (!v. MEM (Var v) (compute_operands (EL i bb.bb_instructions)) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    (!v. MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled ==>
      P v \/ ?di. MEM di (TAKE i bb.bb_instructions) /\ MEM v di.inst_outputs) /\
    generate_inst_plan lv dfg cfg fn (EL i bb.bb_instructions)
      next halt term lbl ps = SOME (ops,qs)
    ==>
    !v. MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled ==>
      P v \/ ?di. MEM di (TAKE (SUC i) bb.bb_instructions) /\
        MEM v di.inst_outputs
Proof
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    native_inst_variable_origins >> simp[] >> disch_tac >>
  `TAKE (SUC i) bb.bb_instructions =
    TAKE i bb.bb_instructions ++ [EL i bb.bb_instructions]` by
    simp[TAKE_SUC] >>
  rpt strip_tac >>
  `MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled \/
    MEM v (EL i bb.bb_instructions).inst_outputs` by metis_tac[] >>
  metis_tac[MEM_APPEND, MEM]
QED

(* Compile-time support is independent of physical counts and allocator state. *)
Definition chronological_support_def:
  chronological_support fn visited ps <=>
    !v. MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled ==>
      ?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
        MEM v di.inst_outputs /\ MEM db.bb_label visited
End

Theorem chronological_support_mono:
  !fn visited visited' ps.
    chronological_support fn visited ps /\ set visited SUBSET set visited' ==>
    chronological_support fn visited' ps
Proof
  rw[chronological_support_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem chronological_support_physical_cong:
  !fn visited ps qs.
    ps.ps_stack = qs.ps_stack /\ ps.ps_spilled = qs.ps_spilled ==>
    (chronological_support fn visited ps <=> chronological_support fn visited qs)
Proof
  simp[chronological_support_def]
QED

Theorem chronological_support_saved_reset:
  !fn visited visited' saved current.
    chronological_support fn visited saved /\ set visited SUBSET set visited' ==>
    chronological_support fn visited'
      (current with <|ps_stack := saved.ps_stack; ps_spilled := saved.ps_spilled|>)
Proof
  rpt strip_tac >> drule_all chronological_support_mono >>
  simp[chronological_support_def]
QED
