Theory concretizePtrPairedCallEntry
Ancestors
  concretizePtrPairedEntry concretizePtrPairedFields concretizePtrValueSelection
  o1PassLift analysisSimProofsBase unitShapeDefs passSimulationProps
  passSharedDefs passSimulationDefs
  concretizePtrPairedPrefix concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrDeletedGapHistory
  concretizePtrChronologicalHistory concretizePtrSourceOwnership
  concretizePtrOpaqueRetpc concretizePtrSharedFields concretizePtrValueTransport
  concretizePtrRequestHistory
  concretizeStepStructure concretizeStepShape concretizeStepCallChecks
  concretizeStepRetpc concretizeStageShape concretizeStepContract
  contextCodegenRel unitLabelMapIdentity venomInst o1PassContract
  ptrDiscipline venomExecSemantics venomExecProofs venomWf venomState list finite_map

Theorem ptr_owned_invoke_restrictions:
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  ptr_discipline lo C vs0 /\ opaque_use_ok a.po_fn /\
  a.po_inst.inst_opcode = INVOKE /\
  decode_invoke a.po_inst = SOME (nm,ops) ==>
  EVERY (ptr_nonopaque_operand a.po_fn) ops /\
  MAP (op_taint a.po_taint) ops = REPLICATE (LENGTH ops) {}
Proof
  strip_tac >>
  drule ptr_gap_ownership_history >> strip_tac >>
  drule ptr_chrono_history_reachable >> strip_tac >>
  gvs[ptr_observation_reachable_def] >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> rpt strip_tac >> gvs[]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_MEM] >>
     metis_tac[lookup_block_MEM, MEM_EL]) >>
  `taint_ok a.po_fn a.po_taint a.po_inst a.po_state` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  `a.po_inst.inst_operands = Label nm :: ops` by
    (gvs[decode_invoke_def, AllCaseEqs()]) >>
  conj_tac
  >- (`~MEM a.po_inst.inst_opcode [ASSIGN; PHI; RET; RETFMP; DRET]` by simp[] >>
      drule_all ptr_nonopaque_instruction_operands >> simp[]) >>
  `EVERY (\op. op_taint a.po_taint op = {}) ops` by
    (gvs[EVERY_MEM, taint_ok_def] >> metis_tac[]) >>
  pop_assum mp_tac >>
  qpat_x_assum `decode_invoke _ = _` kall_tac >>
  qpat_x_assum `a.po_inst.inst_operands = _` kall_tac >>
  Induct_on `ops` >> simp[]
QED

Theorem ptr_paired_invoke_args:
  ptr_paired_prefix R lp positions lo vs0 C Ct
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ptr_discipline lo C vs0 /\ opaque_use_ok a.po_fn /\
  a.po_inst.inst_opcode = INVOKE /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  decode_invoke at.po_inst = SOME (nm,ops) /\
  eval_operands ops at.po_state = SOME argst ==>
  decode_invoke a.po_inst = SOME (nm,ops) /\
  EVERY (ptr_nonopaque_operand a.po_fn) ops /\
  MAP (op_taint a.po_taint) ops = REPLICATE (LENGTH ops) {} /\
  ?args. eval_operands ops a.po_state = SOME args /\
    ptr_args_transport births positions (MAP (op_prov TG) ops)
      (REPLICATE (LENGTH args) {}) args argst
Proof
  strip_tac >>
  `at.po_inst = a.po_inst` by simp[concretize_positions_unchanged] >>
  `decode_invoke a.po_inst = SOME (nm,ops)` by metis_tac[] >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  drule_all ptr_owned_invoke_restrictions >> strip_tac >>
  simp[] >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  `a.po_state.vs_labels = at.po_state.vs_labels` by
    (fs[ptr_paired_sample_def] >> metis_tac[ptr_history_content_labels]) >>
  `ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
    a.po_state at.po_state` by fs[ptr_paired_sample_def] >>
  drule_all ptr_mixed_vars_eval_operands >>
  Cases_on `eval_operands ops a.po_state` >> simp[] >>
  strip_tac >> drule ptr_args_transport_lengths >> simp[] >>
  strip_tac >> gvs[]
QED

Theorem ptr_setup_no_phi_entry:
  first_block_no_phi f /\ setup_callee f args s = SOME cs ==>
  enters_block f cs cs /\ (!u. enters_block f cs u ==> u = cs)
Proof
  simp[setup_callee_def] >> strip_tac >> gvs[AllCaseEqs()] >>
  `lookup_block (HD f.fn_blocks).bb_label f.fn_blocks = SOME (HD f.fn_blocks)` by
    (Cases_on `f.fn_blocks` >> gvs[lookup_block_def, FIND_def, INDEX_FIND_def]) >>
  fs[first_block_no_phi_def] >>
  simp[enters_block_def, eval_phis_no_phis, no_phis_phi_prefix_length_zero]
QED

Theorem ptr_paired_invoke_entry:
  ptr_paired_prefix R lp positions lo vs0 C Ct
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ptr_discipline lo C vs0 /\ opaque_use_ok a.po_fn /\
  a.po_inst.inst_opcode = INVOKE /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  decode_invoke at.po_inst = SOME (nm,ops) /\
  eval_operands ops at.po_state = SOME argst /\
  LIST_REL (ptr_paired_code R lp positions) C.ctx_functions Ct.ctx_functions /\
  (!f g. ptr_paired_code R lp positions f g ==> g.fn_name = f.fn_name) /\
  EVERY (\f. first_block_no_phi f /\ fn_inst_wf f /\
    EVERY bb_well_formed f.fn_blocks /\ ALL_DISTINCT (fn_labels f) /\
    (!inst. MEM inst (fn_insts f) /\ inst.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP (lp f) (Allocation inst.inst_id)))) C.ctx_functions /\
  EVERY (\g. ALL_DISTINCT (fn_labels g)) Ct.ctx_functions /\
  lookup_function nm Ct.ctx_functions = SOME g /\
  setup_callee g argst at.po_state = SOME ct /\ enters_block g ct ct' /\
  active_inst g it ct' ==>
  ?f args cs cs' i.
    lookup_function nm C.ctx_functions = SOME f /\
    ptr_paired_code R lp positions f g /\
    eval_operands ops a.po_state = SOME args /\
    ptr_args_transport births positions (MAP (op_prov TG) ops)
      (REPLICATE (LENGTH args) {}) args argst /\
    setup_callee f args a.po_state = SOME cs /\ enters_block f cs cs' /\
    active_inst f i cs' /\ ptr_history_content (a.po_taint with t_var := FEMPTY) cs' ct' /\
    ptr_mixed_vars births positions FEMPTY entry_taint f g cs' ct' /\
    ptr_args_transport births positions (MAP (op_prov TG) ops)
      (REPLICATE (LENGTH args) {}) cs'.vs_params ct'.vs_params /\
    ptr_paired_cursor lp
      (a with <|po_fn := f; po_inst := i; po_state := cs'|>)
      (at with <|po_fn := g; po_inst := it; po_state := ct'|>)
Proof
  strip_tac >> drule_all ptr_paired_invoke_args >> strip_tac >>
  `?f. lookup_function nm C.ctx_functions = SOME f /\
    ptr_paired_code R lp positions f g` by
    (drule_all list_rel_lookup_function >> disch_then (qspec_then `nm` mp_tac) >>
     Cases_on `lookup_function nm C.ctx_functions` >> simp[]) >>
  `MEM f C.ctx_functions /\ MEM g Ct.ctx_functions` by
    metis_tac[venomInstTheory.lookup_function_MEM] >>
  `first_block_no_phi f /\ fn_inst_wf f /\
    EVERY bb_well_formed f.fn_blocks /\ ALL_DISTINCT (fn_labels f) /\
    (!inst. MEM inst (fn_insts f) /\ inst.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP (lp f) (Allocation inst.inst_id))) /\
    ALL_DISTINCT (fn_labels g)` by (fs[EVERY_MEM] >> metis_tac[]) >>
  `NULL f.fn_blocks = NULL g.fn_blocks /\
    (HD f.fn_blocks).bb_label = (HD g.fn_blocks).bb_label` by
    (fs[ptr_paired_code_def, concretize_positions_blocks] >>
     Cases_on `f.fn_blocks` >> simp[concretize_positions_block_label]) >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  `ptr_history_content a.po_taint a.po_state at.po_state` by fs[ptr_paired_sample_def] >>
  drule_all ptr_history_content_setup >>
  disch_then (qspec_then `args` strip_assume_tac) >>
  `~NULL f.fn_blocks` by
    (fs[setup_callee_def, AllCaseEqs()]) >>
  `first_block_no_phi g` by
    (qpat_x_assum `ptr_paired_code R lp positions f g` mp_tac >>
     simp[ptr_paired_code_def] >> strip_tac >>
     gvs[first_block_no_phi_def, concretize_positions_blocks] >>
     Cases_on `f.fn_blocks` >>
     gvs[clear_nops_block_def, block_map_transform_def,
         EVERY_FILTER, EVERY_MAP, EVERY_MEM, MEM_FILTER, MEM_MAP] >>
     metis_tac[concretize_positions_phi]) >>
  `enters_block f cs cs /\ ct' = ct` by
    metis_tac[ptr_setup_no_phi_entry] >>
  gvs[] >>
  `ptr_mixed_vars births positions FEMPTY entry_taint f g cs ct` by
    (irule ptr_mixed_vars_setup >> simp[] >>
     conj_tac
     >- (fs[ptr_paired_code_def, retpc_var_def] >>
         qpat_assum `g.fn_blocks = _`
           (mp_then Any mp_tac concretize_blocks_copy_phi) >>
         simp[concretize_positions_copy_phi]) >>
     metis_tac[]) >>
  `ptr_args_transport births positions (MAP (op_prov TG) ops)
    (REPLICATE (LENGTH args) {}) cs.vs_params ct.vs_params` by
    (`NULL f.fn_blocks = NULL g.fn_blocks` by simp[] >>
     drule_all ptr_setup_callee_transport >> metis_tac[]) >>
  `cs.vs_current_bb = ct.vs_current_bb /\ cs.vs_prev_bb = ct.vs_prev_bb` by
    (qpat_x_assum `setup_callee f _ _ = _` mp_tac >>
     qpat_x_assum `setup_callee g _ _ = _` mp_tac >>
     simp[setup_callee_def] >> rpt strip_tac >> gvs[AllCaseEqs()]) >>
  `?i. active_inst f i cs /\ ptr_paired_cursor lp
    (a with <|po_fn := f; po_inst := i; po_state := cs|>)
    (at with <|po_fn := g; po_inst := it; po_state := ct|>)` by
    (mp_tac (ptr_paired_entry_cursor |> SPEC_ALL |>
       INST_TYPE [alpha |-> ``:num``] |>
       Q.INST [`a` |-> `a with <|po_fn := f; po_state := cs|>`,
               `at` |-> `at with <|po_fn := g; po_inst := it; po_state := ct|>`] |>
       GEN_ALL) >>
     simp[] >> disch_then irule >> metis_tac[]) >>
  qexistsl_tac [`cs`,`i`] >> simp[]
QED
