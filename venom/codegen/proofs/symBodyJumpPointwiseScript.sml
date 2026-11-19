(* Paired symbolic jump prefixes, independent of global function simulation. *)
Theory symBodyJumpPointwise
Ancestors
  symFrameControlOwn symFnSimSpec fnBlockBodyClasses fnBlockBodySteps
  fnBlockBodyHelpers contextCodegenRelProps fnBlockPlanStaticRegion
  fnPlanLineageEntryProduction codegenSymRel codegenSymOwnRel fnAliasStep
  frameRel contextCodegenRel codegenRel unitShapeDefs venomExecSemantics
  venomState venomInst asmSymBridge asmSymSem

Theorem sym_body_jmp_prefix_pointwise:
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = JMP /\ step_inst fuel ctx inst vs = OK vs1 /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  code_end_offset_ok Inv ctx /\
  sym_unit_static_ok unit /\ asm_static_wf prog /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  asm_data_env_lo_ok lo prog env own /\ vs.vs_code = own /\
  (?target. inst.inst_operands = [Label target] /\ inst.inst_outputs = [] /\
    is_terminator inst.inst_opcode /\ MEM target (get_successors inst)) /\
  (!t. MEM t (get_successors inst) ==> MEM (AsmLabel t) prog) /\
  sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps as ss ==>
  ?n as1 ss1 t off.
    asm_steps lo o2pc prog n as = AsmOK as1 /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss1 /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps_after vs1 as1 /\
    sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps_after as1 ss1 /\
    (!at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
      operand_val (frame_view fn ra vs1) lo at =
      operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)) /\
    is_terminator inst.inst_opcode /\ MEM t (get_successors inst) /\
    vs1 = jump_to t vs /\
    FLOOKUP lo t = SOME off /\ FLOOKUP o2pc off = SOME as1.as_pc
Proof
  strip_tac >> drule body_inv_facts_reloc >> strip_tac >>
  drule_all body_inv_inst_reloc >> strip_tac >>
  drule_all body_inv_step_reloc >> strip_tac >>
  drule_all body_inv_static_reloc >> strip_tac >>
  drule body_inv_equiv_reloc >> disch_then drule >> disch_then drule >> strip_tac >>
  drule_all body_terminator_last_reloc >> strip_tac >>
  drule_all body_succ_placed_reloc >> strip_tac >>
  `MEM (AsmLabel target) prog` by metis_tac[] >>
  `pending_inventory_wf
    (MAP Var (input_vars_from bb.bb_label tbb.bb_instructions
      (live_vars_at liveness target 0))) ps` by metis_tac[] >>
  `!op at. MEM op (MAP Var (input_vars_from bb.bb_label tbb.bb_instructions
      (live_vars_at liveness target 0))) /\
      (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) /\ operand_equiv dfg op at ==>
      operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at` by
    (match_mp_tac mem_operand_equiv >> conj_tac
      >- metis_tac[pending_inventory_wf_owned] >> gvs[body_inv_reloc_def]) >>
  `!off. MEM (SORestore off) (FST (restore_spilled_plan
      (MAP Var (input_vars_from bb.bb_label tbb.bb_instructions
        (live_vars_at liveness target 0))) ps)) ==> off < dimword (:256)` by
    (rpt strip_tac >> drule_all jmp_plan_restore_ops >> simp[]) >>
  qhdtm_assum `body_inv_reloc`
    (strip_assume_tac o REWRITE_RULE [body_inv_reloc_def]) >>
  `fn_shape_ok fn` by
    (gvs[unit_shape_ok_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  `?n as1 ss1. asm_steps lo (build_offset_to_pc prog) prog n as = AsmOK as1 /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
    as1.as_pc = tpc /\ vs1 = jump_to target vs /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss1 /\
    sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps' as1 ss1` by
    (irule (INST_TYPE [alpha |-> ``:cfg_analysis``] sym_jmp_frame_sim_deep_own) >> simp[] >>
     conj_tac >- metis_tac[] >>
     conj_tac >- ((qexists `r` >> simp[] >> (metis_tac[]))) >>
     qexistsl [`spill_base`, `bb.bb_label`, `cfg`, `fuel`, `inst`,
       `bb_is_halting bb`, `liveness`,
       `k + 1 < LENGTH bb.bb_instructions /\
        is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode`,
       `live_vars_at liveness bb.bb_label (k + 1)`, `ops`, `ps`] >>
     gvs[] >> metis_tac[]) >>
  `!at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
      operand_val (frame_view fn ra vs1) lo at =
      operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)` by
    ((match_mp_tac (INST_TYPE [alpha |-> ``:cfg_analysis``] alias_step_preserve) >>
     qexistsl [`fuel`, `ctx`, `liveness`, `cfg`, `inst`,
       `live_vars_at liveness bb.bb_label (k + 1)`, `bb_is_halting bb`,
       `k + 1 < LENGTH bb.bb_instructions /\
        is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode`,
       `bb.bb_label`, `ps`, `ops`, `vs`] >> gvs[] >> (metis_tac[INST_TYPE [alpha |-> ``:cfg_analysis``] alias_step_preserve]))) >>
  qexistsl [`n`, `as1`, `ss1`, `target`, `toff`] >> gvs[] >> metis_tac[]
QED

Theorem sym_body_jnz_prefix_pointwise:
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = JNZ /\ step_inst fuel ctx inst vs = OK vs1 /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  code_end_offset_ok Inv ctx /\
  sym_unit_static_ok unit /\ asm_static_wf prog /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  asm_data_env_lo_ok lo prog env own /\ vs.vs_code = own /\
  (?c l1 l2. inst.inst_operands = [c; Label l1; Label l2] /\
    inst.inst_outputs = [] /\ ~is_label_operand c /\
    is_terminator inst.inst_opcode /\ MEM c (compute_operands inst) /\
    MEM l1 (get_successors inst) /\ MEM l2 (get_successors inst)) /\
  (!c l1 l2. inst.inst_operands = [c; Label l1; Label l2] ==>
    eval_operand c vs = eval_operand c (frame_view fn ra vs)) /\
  (!t. MEM t (get_successors inst) ==> MEM (AsmLabel t) prog) /\
  sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps as ss ==>
  ?n as1 ss1 t off.
    asm_steps lo o2pc prog n as = AsmOK as1 /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss1 /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps_after vs1 as1 /\
    sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps_after as1 ss1 /\
    (!at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
      operand_val (frame_view fn ra vs1) lo at =
      operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)) /\
    is_terminator inst.inst_opcode /\ MEM t (get_successors inst) /\
    vs1 = jump_to t vs /\
    FLOOKUP lo t = SOME off /\ FLOOKUP o2pc off = SOME as1.as_pc
Proof
  strip_tac >> drule body_inv_facts_reloc >> strip_tac >>
  drule_all body_inv_inst_reloc >> strip_tac >>
  drule_all body_inv_step_reloc >> strip_tac >>
  drule_all body_inv_static_reloc >> strip_tac >>
  drule body_inv_equiv_reloc >> disch_then drule >> disch_then drule >> strip_tac >>
  `eval_operand c vs = operand_val (frame_view fn ra vs) lo c` by metis_tac[] >>
  drule_all body_terminator_last_reloc >> strip_tac >>
  `?off1 pc1. FLOOKUP lo l1 = SOME off1 /\ off1 < dimword (:256) /\
    FLOOKUP o2pc off1 = SOME pc1 /\ MEM (AsmLabel l1) prog` by
    (qpat_assum `MEM l1 (get_successors inst)`
       (mp_then (Pat `MEM t (get_successors inst)`) mp_tac body_succ_placed_reloc) >>
     disch_then drule >> simp[] >> strip_tac >>
     qexistsl [`toff`, `tpc`] >> simp[]) >>
  `?off2 pc2. FLOOKUP lo l2 = SOME off2 /\ off2 < dimword (:256) /\
    FLOOKUP o2pc off2 = SOME pc2 /\ MEM (AsmLabel l2) prog` by
    (qpat_assum `MEM l2 (get_successors inst)`
       (mp_then (Pat `MEM t (get_successors inst)`) mp_tac body_succ_placed_reloc) >>
     disch_then drule >> simp[] >> strip_tac >>
     qexistsl [`toff`, `tpc`] >> simp[]) >>
  qhdtm_assum `body_inv_reloc`
    (strip_assume_tac o REWRITE_RULE [body_inv_reloc_def]) >>
  `fn_shape_ok fn` by
    (gvs[unit_shape_ok_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  `?n as1 ss1. asm_steps lo (build_offset_to_pc prog) prog n as = AsmOK as1 /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
    ((vs1 = jump_to l1 vs /\ as1.as_pc = pc1) \/
     (vs1 = jump_to l2 vs /\ as1.as_pc = pc2)) /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss1 /\
    sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps' as1 ss1` by
    (irule (INST_TYPE [alpha |-> ``:cfg_analysis``] sym_jnz_frame_sim_deep_own) >>
     simp[] >>
     conj_tac >- metis_tac[] >>
     conj_tac >- metis_tac[] >>
     conj_tac >- (qexists `r` >> simp[] >> metis_tac[]) >>
     qexistsl [`spill_base`, `bb.bb_label`, `cfg`, `c`, `fuel`, `inst`,
       `bb_is_halting bb`, `liveness`,
       `k + 1 < LENGTH bb.bb_instructions /\
        is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode`,
       `live_vars_at liveness bb.bb_label (k + 1)`, `ops`, `ps`] >>
     gvs[] >> metis_tac[]) >>
  `!at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
      operand_val (frame_view fn ra vs1) lo at =
      operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)` by
    (match_mp_tac (INST_TYPE [alpha |-> ``:cfg_analysis``] alias_step_preserve) >>
     qexistsl [`fuel`, `ctx`, `liveness`, `cfg`, `inst`,
       `live_vars_at liveness bb.bb_label (k + 1)`, `bb_is_halting bb`,
       `k + 1 < LENGTH bb.bb_instructions /\
        is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode`,
       `bb.bb_label`, `ps`, `ops`, `vs`] >> gvs[] >> metis_tac[]) >>
  qexistsl [`n`, `as1`, `ss1`] >> gvs[] >> metis_tac[]
QED
