Theory requestCutOrdinaryHalt
Ancestors
  fnFramePrefixDriver fnFramePrefix fnFrameDeepHalt
  fnFrameSymbolicReady fnFrameSymbolicPrefix symFrameControl symBlockBody fnBlockBodySteps fnBlockBodyClasses
  fnBlockBody unitShapeDefs codegenSymRel asmSem dftGasRequestObservation
  blockSimHelpers opcodeClass codegenRel contextCodegenRel venomExecSemantics venomInst
  asmIR asmSymSem finalizerContract planExec venomState finite_map words list
Libs
  stepInstBaseLib

Theorem request_cut_halt_requests[local]:
  inst.inst_opcode <> INVOKE /\ step_inst fuel C inst s = Halt post ==>
  post.vs_requests = s.vs_requests
Proof
  strip_tac >> drule step_inst_halt_opcodes >> gvs[step_inst_non_invoke] >>
  strip_tac >>
  stepInstBaseLib.with_opcode_clause (fn cs =>
    gvs (cs @ [AllCaseEqs(), set_returndata_def]))
QED

(* Extend the selected codegen prefix through an ordinary halting instruction. *)
Theorem request_cut_active_halt_terminal[local]:
  active_frame_plan_reloc lo rp unit cpl prog fn s ast ra rest mem0 /\
  active_inst fn inst s /\ inst.inst_opcode <> INVOKE /\
  source_memory_reads_disjoint cpl inst s /\
  step_inst fuel unit.cu_context inst s = Halt post ==>
  ?n out.
    asm_steps lo (build_offset_to_pc prog) prog n ast = AsmHalt out /\
    out.as_requests = s.vs_requests
Proof
  pure_rewrite_tac[active_frame_plan_reloc_def] >> strip_tac >>
  drule_all body_plan_active_inst_reloc >> strip_tac >>
  drule_all body_plan_inv_inst_reloc >> strip_tac >>
  drule body_plan_inv_facts_reloc >> strip_tac >>
  drule_all body_operands_le_16 >> strip_tac >>
  drule_all body_plan_inv_step_reloc >> strip_tac >>
  drule_all body_plan_inv_static_reloc >> strip_tac >>
  drule body_plan_inv_equiv_reloc >> disch_then drule >> disch_then drule >> strip_tac >>
  `!e. step_inst fuel unit.cu_context inst s <> Error e` by simp[] >>
  drule body_plan_inv_label_resolve_reloc >> disch_then drule >>
  disch_then drule >> disch_then drule >> disch_then drule >> strip_tac >>
  qhdtm_assum `body_plan_inv_reloc`
    (strip_assume_tac o REWRITE_RULE [body_plan_inv_reloc_def]) >>
  qspecl_then
    [`fuel`, `unit.cu_context`, `cpl`, `lo`, `build_offset_to_pc prog`, `prog`,
     `liveness`, `dfg`, `cfg`, `fn`, `inst`,
     `live_vars_at liveness bb.bb_label (k + 1)`, `bb_is_halting bb`,
     `k + 1 < LENGTH bb.bb_instructions /\
      is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode`,
     `bb.bb_label`, `spill_base`, `ps`, `s`, `ast`, `ops`, `ps'`, `r`, `ra`, `rest`,
     `mem0`] mp_tac gen_inst_halt_frame_sim_deep_reloc >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  disch_then (qspec_then `post` mp_tac) >> simp[] >> strip_tac >>
  drule_all request_cut_halt_requests >> strip_tac >>
  fs[venom_asm_terminal_rel_def] >> metis_tac[]
QED

Theorem request_cut_normal_halt_terminal:
  normal_frame_plan rp unit cpl prog vs0 es
    (JointConfig stk PG G tn fn inst s oms om hs hist) ast /\
  active_inst fn inst s /\ inst.inst_opcode <> INVOKE /\
  source_memory_reads_disjoint cpl inst s /\
  step_inst fuel unit.cu_context inst s = Halt post ==>
  ?n out.
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
       prog n ast = AsmHalt out /\
    out.as_requests = s.vs_requests
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~is_param_opcode inst.inst_opcode` by
    (drule step_inst_halt_opcodes >> rpt strip_tac >> gvs[is_param_opcode_def]) >>
  drule_all normal_frame_plan_active >>
  disch_then (qx_choosel_then [`m`, `mid`, `saved`, `ra`, `rest`, `mem0`]
    strip_assume_tac) >>
  qpat_x_assum `active_frame_plan _ _ _ _ _ _ _ _ _ _`
    (assume_tac o REWRITE_RULE [GSYM active_frame_plan_reloc_specialize]) >>
  drule_all request_cut_active_halt_terminal >>
  disch_then (qx_choosel_then [`n`, `out`] strip_assume_tac) >>
  qexistsl_tac [`m + n`, `out`] >>
  metis_tac[asm_steps_compose_halt]
QED

Theorem request_cut_symbolic_active_halt_terminal[local]:
  active_frame_symbolic_plan env rp unit cpl prog fn s ast
    ra rest mem0 ret srest labs0 ss /\
  focus_s7_symbolic_context unit prog /\
  active_inst fn inst s /\ inst.inst_opcode <> INVOKE /\
  source_memory_reads_disjoint cpl inst s /\
  context_source_memory_writes_disjoint cpl inst s /\
  step_inst fuel unit.cu_context inst s = Halt post ==>
  ?n out.
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
       prog n ast = AsmHalt out /\
    sym_terminal (sym_steps prog env n ss) /\ out.as_requests = s.vs_requests
Proof
  pure_rewrite_tac[active_frame_symbolic_plan_def, focus_s7_symbolic_context_def] >>
  strip_tac >>
  drule_all body_plan_active_inst >> strip_tac >>
  drule_all body_plan_inv_inst >> strip_tac >>
  drule body_plan_inv_facts >> strip_tac >>
  drule_all body_plan_inv_static >> strip_tac >>
  drule_all body_plan_inv_step >> strip_tac >>
  drule_all body_operands_le_16 >> strip_tac >>
  `!e. step_inst fuel unit.cu_context inst s <> Error e` by simp[] >>
  drule body_plan_inv_label_resolve >> disch_then drule >>
  disch_then drule >> disch_then drule >> disch_then drule >> strip_tac >>
  drule body_plan_inv_equiv >> disch_then drule >> disch_then drule >> strip_tac >>
  qhdtm_assum `body_plan_inv` (strip_assume_tac o REWRITE_RULE [body_plan_inv_def]) >>
  `fn_shape_ok fn` by fs[unit_shape_ok_def, EVERY_MEM] >>
  qspecl_then
    [`fuel`, `unit.cu_context`, `cpl`, `SND (compute_label_offsets prog)`,
     `build_offset_to_pc prog`, `prog`, `liveness`, `dfg`, `cfg`, `fn`, `inst`,
     `live_vars_at liveness bb.bb_label (k + 1)`, `bb_is_halting bb`,
     `k + 1 < LENGTH bb.bb_instructions /\
      is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode`,
     `bb.bb_label`, `spill_base`, `ps`, `s`, `ast`, `ops`, `ps'`, `r`, `ra`, `rest`,
     `mem0`, `env`, `ret`, `srest`, `labs0`, `ss`] mp_tac sym_halt_frame_sim_deep >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  disch_then (qspec_then `post` mp_tac) >> simp[] >> strip_tac >>
  drule_all request_cut_halt_requests >> strip_tac >>
  fs[venom_asm_terminal_rel_def] >> metis_tac[]
QED

Theorem request_cut_symbolic_normal_halt_terminal:
  normal_frame_symbolic_plan env rp unit cpl prog vs0 es
    (JointConfig stk PG G tn fn inst s oms om hs hist) ast ss /\
  focus_s7_symbolic_context unit prog /\
  active_inst fn inst s /\ inst.inst_opcode <> INVOKE /\
  source_memory_reads_disjoint cpl inst s /\
  context_source_memory_writes_disjoint cpl inst s /\
  step_inst fuel unit.cu_context inst s = Halt post ==>
  ?n out.
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
       prog n ast = AsmHalt out /\
    sym_terminal (sym_steps prog env n ss) /\ out.as_requests = s.vs_requests
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~is_param_opcode inst.inst_opcode` by
    (drule step_inst_halt_opcodes >> rpt strip_tac >> gvs[is_param_opcode_def]) >>
  drule_all normal_frame_symbolic_plan_active >>
  disch_then (qx_choosel_then [`m`, `ready`, `rss`, `ra`, `rest`, `mem0`, `ret`, `srest`, `labs0`]
    strip_assume_tac) >>
  drule_all request_cut_symbolic_active_halt_terminal >>
  disch_then (qx_choosel_then [`n`, `out`] strip_assume_tac) >>
  qexistsl_tac [`m + n`, `out`] >>
  simp[sym_steps_add] >>
  metis_tac[asm_steps_compose_halt]
QED

Theorem request_cut_symbolic_halt_prefix:
  sym_steps prog env prefix (sym_init a0) = SymOK ss /\
  normal_frame_symbolic_plan env rp unit cpl prog vs0 es
    (JointConfig stk PG G tn fn inst s oms om hs hist) ast ss /\
  focus_s7_symbolic_context unit prog /\
  active_inst fn inst s /\ inst.inst_opcode <> INVOKE /\
  source_memory_reads_disjoint cpl inst s /\
  context_source_memory_writes_disjoint cpl inst s /\
  step_inst fuel unit.cu_context inst s = Halt post ==>
  label_disciplined env prog a0 /\
  ?n out.
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
       prog n ast = AsmHalt out /\ out.as_requests = s.vs_requests
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (qx_choosel_then [`n`, `out`] (map_every assume_tac o CONJUNCTS))
    request_cut_symbolic_normal_halt_terminal >>
  reverse conj_tac >- (qexistsl_tac [`n`, `out`] >> asm_rewrite_tac[]) >>
  `sym_terminal (sym_steps prog env (prefix + n) (sym_init a0))` by
    simp[sym_steps_add] >>
  drule sym_steps_terminal_run >> disch_then (qspec_then `0` mp_tac) >>
  simp[] >> strip_tac >>
  irule sym_terminal_disciplined >>
  fs[focus_s7_symbolic_context_def] >> qexists_tac `prefix + n` >> simp[]
QED
