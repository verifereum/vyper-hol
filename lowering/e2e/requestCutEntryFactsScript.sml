Theory requestCutEntryFacts
Ancestors
  requestCutLabels e2eProducers o1SymStaticPipeline o1PipelineCorrect
  venomPipelineDriverProps codegenAsmStaticWf codegenAsmProgOk
  asmFinalizerPrefixStatic fnFrameSymbolicPrefix codegenEntrySim
  codegenSymRel codegenEntryRel contextRawReachable contextCodegenRel
  asmOptimizer o1PassLift o1PassContract unitShapeDefs venomState venomInst
  finite_map words list asmRelocDataEnv fnPlanPlaceRevertPostamble
  asmOptFinalizerOwn asmSymOwnCode asmSymBridge codegenLabelDisciplined codegenAsmOpt

Theorem raw_visit_function_member:
  !initial C f i s. raw_reachable initial C f i s ==> MEM f C.ctx_functions
Proof
  ho_match_mp_tac raw_reachable_ind >> rpt strip_tac >> metis_tac[lookup_function_MEM]
QED

Theorem request_cut_entry_facts:
  o1PipelineCorrect$o1_pipeline rp unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
  unit_shape_ok out.po_unit /\
  generate_context_plan out.po_unit.cu_context = SOME cpl /\
  codegen_assembly rp out.po_unit = SOME prog /\
  fin IN accepted_finalizers /\ fin rp prog = SOME prog' /\
  (fin = asm_opt_finalizer ==>
    label_flow_ok out.po_unit.cu_context /\
    EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
      ds.ds_items) unit.cu_data_segment) /\
  (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
    ~MEM (Label "runtime_begin") inst.inst_operands) /\
  codegen_asm_entry_rel cpl prog v (entry_asm_state v es) /\
  w2n v.vs_initial_fmp <= w2n fmp ==>
  fmp_variant_room (SOME fmp) out.po_unit.cu_context v /\
  codegen_ready out.po_unit.cu_context /\ asm_frame_prog_ok prog' /\
  (fin = asm_opt_finalizer ==> focus_s7_symbolic_context out.po_unit prog) /\
  (!fn inst l. MEM fn out.po_unit.cu_context.ctx_functions /\
    MEM inst (fn_insts fn) /\ inst.inst_opcode <> PHI /\
    MEM (Label l) (compute_operands inst) ==>
    IS_SOME (FLOOKUP (SND (compute_label_offsets prog)) l)) /\
  (!fn inst s i l. raw_reachable v out.po_unit.cu_context fn inst s /\
    MEM i (fn_insts fn) /\ i.inst_opcode <> PHI /\
    MEM (Label l) (compute_operands i) ==> IS_SOME (FLOOKUP s.vs_labels l))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `v.vs_initial_fmp = n2w cpl.cp_initial_fmp` by fs[codegen_asm_entry_rel_def] >>
  `!eom. max_live_eom out.po_unit.cu_context = SOME eom ==> eom <= w2n v.vs_initial_fmp` by
    metis_tac[generate_context_plan_eom_room] >>
  `fmp_variant_room (SOME fmp) out.po_unit.cu_context v` by
    (rewrite_tac[fmp_variant_room_def] >> metis_tac[]) >>
  `codegen_ready out.po_unit.cu_context` by
    (qpat_assum `o1PipelineCorrect$o1_pipeline _ _ = _`
      (assume_tac o REWRITE_RULE [o1PipelineCorrectTheory.o1_pipeline_def]) >>
     drule run_venom_pipeline_success_boundary >> simp[]) >>
  `~(?fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) /\
       MEM (Label "runtime_begin") inst.inst_operands)` by metis_tac[] >>
  drule o1_pipeline_runtime_reference_reflects >> simp[] >> strip_tac >>
  `!fn inst l. MEM fn out.po_unit.cu_context.ctx_functions /\
     MEM inst (fn_insts fn) /\ inst.inst_opcode <> PHI /\
     MEM (Label l) (compute_operands inst) ==>
     IS_SOME (FLOOKUP (SND (compute_label_offsets prog)) l)` by
    (match_mp_tac request_cut_compute_labels_bound >> metis_tac[]) >>
  `fin = asm_opt_finalizer ==> focus_s7_symbolic_context out.po_unit prog` by
    (strip_tac >> gvs[] >> simp[focus_s7_symbolic_context_def] >>
     `sym_unit_static_ok out.po_unit` by metis_tac[o1_pipeline_sym_unit_static_ok] >>
     metis_tac[codegen_asm_static_wf]) >>
  `asm_frame_prog_ok prog'` by
    (Cases_on `fin = asm_opt_finalizer`
     >- (fs[focus_s7_symbolic_context_def] >> metis_tac[finalizer_prefix_static]) >>
     `fin = K SOME` by fs[accepted_finalizers_def] >>
     gvs[] >> metis_tac[codegen_assembly_frame_prog_ok]) >>
  simp[] >> rpt strip_tac
  >~ [`IS_SOME (FLOOKUP (SND (compute_label_offsets prog)) l)`]
  >- metis_tac[] >>
  `MEM fn out.po_unit.cu_context.ctx_functions` by metis_tac[raw_visit_function_member] >>
  drule raw_reachable_labels >> disch_then SUBST1_TAC >>
  fs[codegen_asm_entry_rel_def] >> metis_tac[optionTheory.IS_SOME_MAP]
QED

Theorem request_cut_entry_facts_own:
  o1PipelineCorrect$o1_pipeline rp unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
  unit_shape_ok out.po_unit /\
  generate_context_plan out.po_unit.cu_context = SOME cpl /\
  codegen_assembly rp out.po_unit = SOME prog /\
  fin IN accepted_finalizers /\ fin rp prog = SOME prog' /\
  (fin = asm_opt_finalizer ==>
    focus_s7_symbolic_context_own T out.po_unit prog /\
    asm_data_env_lo_ok (lo_reloc prog prog') prog (asm_data_env prog' v.vs_code) v.vs_code) /\
  (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
    ~MEM (Label "runtime_begin") inst.inst_operands) /\
  codegen_asm_entry_rel_reloc (lo_reloc prog prog') cpl prog v (entry_asm_state v es) /\
  w2n v.vs_initial_fmp <= w2n fmp ==>
  fmp_variant_room (SOME fmp) out.po_unit.cu_context v /\
  codegen_ready out.po_unit.cu_context /\ asm_frame_prog_ok prog' /\
  (!fn inst l. MEM fn out.po_unit.cu_context.ctx_functions /\
    MEM inst (fn_insts fn) /\ inst.inst_opcode <> PHI /\
    MEM (Label l) (compute_operands inst) ==>
    IS_SOME (FLOOKUP (SND (compute_label_offsets prog)) l)) /\
  (!fn inst s i l. raw_reachable v out.po_unit.cu_context fn inst s /\
    MEM i (fn_insts fn) /\ i.inst_opcode <> PHI /\
    MEM (Label l) (compute_operands i) ==> IS_SOME (FLOOKUP s.vs_labels l))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `v.vs_initial_fmp = n2w cpl.cp_initial_fmp` by fs[codegen_asm_entry_rel_reloc_def] >>
  `!eom. max_live_eom out.po_unit.cu_context = SOME eom ==> eom <= w2n v.vs_initial_fmp` by
    metis_tac[generate_context_plan_eom_room] >>
  `fmp_variant_room (SOME fmp) out.po_unit.cu_context v` by
    (rewrite_tac[fmp_variant_room_def] >> metis_tac[]) >>
  `codegen_ready out.po_unit.cu_context` by
    (qpat_assum `o1PipelineCorrect$o1_pipeline _ _ = _`
      (assume_tac o REWRITE_RULE [o1PipelineCorrectTheory.o1_pipeline_def]) >>
     drule run_venom_pipeline_success_boundary >> simp[]) >>
  `~(?fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) /\
       MEM (Label "runtime_begin") inst.inst_operands)` by metis_tac[] >>
  drule o1_pipeline_runtime_reference_reflects >> simp[] >> strip_tac >>
  `!fn inst l. MEM fn out.po_unit.cu_context.ctx_functions /\
     MEM inst (fn_insts fn) /\ inst.inst_opcode <> PHI /\
     MEM (Label l) (compute_operands inst) ==>
     IS_SOME (FLOOKUP (SND (compute_label_offsets prog)) l)` by
    (match_mp_tac request_cut_compute_labels_bound >> metis_tac[]) >>
  `asm_frame_prog_ok prog'` by
    (Cases_on `fin = asm_opt_finalizer`
     >- (fs[] >>
         `asm_static_wf prog` by fs[focus_s7_symbolic_context_own_def] >>
         drule asm_opt_finalizer_refines_own >>
         asm_rewrite_tac[asm_refines_own_def] >>
         metis_tac[asm_static_wf_frame_prog_ok]) >>
     `fin = K SOME` by fs[accepted_finalizers_def] >>
     gvs[] >> metis_tac[codegen_assembly_frame_prog_ok]) >>
  `!fn inst l. MEM fn out.po_unit.cu_context.ctx_functions /\
     MEM inst (fn_insts fn) /\ inst.inst_opcode <> PHI /\
     MEM (Label l) (compute_operands inst) ==>
     IS_SOME (FLOOKUP (lo_reloc prog prog') l)` by
    (Cases_on `fin = asm_opt_finalizer`
     >- (fs[] >>
         mp_tac (Q.INST [`unit` |-> `out.po_unit`] request_cut_compute_header) >>
         (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[])) >>
         strip_tac >> rpt strip_tac >>
         `MEM (AsmDataHeader l) prog` by metis_tac[] >>
         qpat_assum `asm_data_env_lo_ok _ _ _ _`
           (qspecl_then [`l`] mp_tac o REWRITE_RULE [asm_data_env_lo_ok_def]) >>
         asm_rewrite_tac[] >> strip_tac >> simp[]) >>
     `fin = K SOME` by fs[accepted_finalizers_def] >>
     gvs[combinTheory.K_THM, lo_reloc_refl] >> first_assum ACCEPT_TAC) >>
  simp[] >> rpt strip_tac
  >~ [`IS_SOME (FLOOKUP (SND (compute_label_offsets prog)) l)`]
  >- metis_tac[] >>
  `MEM fn out.po_unit.cu_context.ctx_functions` by metis_tac[raw_visit_function_member] >>
  drule raw_reachable_labels >> disch_then SUBST1_TAC >>
  fs[codegen_asm_entry_rel_reloc_def] >> metis_tac[optionTheory.IS_SOME_MAP]
QED
