Theory concretizePtrPairedRoot
Ancestors passTransform
  concretizePtrPairedPrefixProbe concretizePtrMixedPhi
  concretizePtrPairedPrefix concretizePtrStructuralTranscript concretizePtrActivationBirths
  concretizePtrChronologicalHistory o1PassContract
  venomInst contextCodegenRel venomExecProofs venomExecSemantics
  concretizePtrPairedFields concretizeStepStructure passSharedProps
  concretizeMemLocDefs unitLabelMapIdentity passSharedDefs passSimulationProps
  passSimulationDefs venomWf venomInstProps concretizePtrLedgerAlignment
  concretizePtrOpaqueRetpc concretizePtrSharedFields concretizePtrValueTransport
  concretizePtrRequestHistory
  unitShapeDefs ptrDiscipline venomState finite_map
  list rich_list arithmetic

(* Inverting a singleton excludes the snoc constructor because its
   predecessor history is nonempty. *)
Theorem ptr_chrono_root_inversion:
  ptr_chrono_history vs0 C [a] a ==>
  ?name lbl s1 inst.
    C.ctx_entry = SOME name /\
    lookup_function name C.ctx_functions = SOME a.po_fn /\
    fn_entry_label a.po_fn = SOME lbl /\
    enters_block a.po_fn
      (vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                   vs_inst_idx := 0 |>) s1 /\
    active_inst a.po_fn inst s1 /\
    a = ptr_observe [] [] FEMPTY entry_taint a.po_fn inst s1
Proof
  simp[Once ptr_chrono_history_cases] >> rpt strip_tac >>
  gvs[ptr_observe_def] >>
  drule ptr_chrono_history_end >> simp[]
QED

Theorem ptr_chrono_source_root:
  C.ctx_entry = SOME name /\
  lookup_function name C.ctx_functions = SOME f /\
  fn_entry_label f = SOME lbl /\ first_block_no_phi f /\
  (HD f.fn_blocks).bb_instructions <> [] ==>
  ?a. ptr_chrono_history vs0 C [a] a /\ a.po_fn = f /\
    a.po_state = (vs0 with <| vs_prev_bb := NONE;
      vs_current_bb := lbl; vs_inst_idx := 0 |>) /\
    a.po_stack = [] /\ a.po_params = [] /\ a.po_prov = FEMPTY /\
    a.po_taint = entry_taint /\
    a.po_inst = HD (HD f.fn_blocks).bb_instructions
Proof
  strip_tac >>
  `f.fn_blocks <> []` by
    (Cases_on `f.fn_blocks` >> gvs[fn_entry_label_def, entry_block_def]) >>
  `lbl = (HD f.fn_blocks).bb_label` by
    gvs[fn_entry_label_def, entry_block_def, NULL_EQ] >>
  qexists_tac `ptr_observe [] [] FEMPTY entry_taint f
    (HD (HD f.fn_blocks).bb_instructions)
    (vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>)` >>
  simp[ptr_observe_def] >>
  rewrite_tac[GSYM ptr_observe_def] >>
  irule ptr_chrono_history_entry >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (simp[active_inst_def] >> qexists_tac `HD f.fn_blocks` >>
      Cases_on `f.fn_blocks` >> gvs[] >>
      Cases_on `h.bb_instructions` >> gvs[]) >>
  qexists_tac `lbl` >> simp[enters_block_def] >>
  qexists_tac `HD f.fn_blocks` >>
  qexists_tac `vs0 with <| vs_prev_bb := NONE;
    vs_current_bb := lbl; vs_inst_idx := 0 |>` >>
  gvs[first_block_no_phi_def, eval_phis_no_phis,
      no_phis_phi_prefix_length_zero] >>
  Cases_on `f.fn_blocks` >> gvs[lookup_block_def, FIND_def, INDEX_FIND_def]
QED

Theorem ptr_paired_root_target_state:
  ptr_chrono_history vs0 Ct [at] at /\
  ptr_paired_code R lp positions f at.po_fn /\ first_block_no_phi f ==>
  ?lbl. fn_entry_label f = SOME lbl /\
    at.po_state = (vs0 with <| vs_prev_bb := NONE;
      vs_current_bb := lbl; vs_inst_idx := 0 |>)
Proof
  strip_tac >> drule ptr_chrono_root_inversion >> strip_tac >>
  fs[ptr_paired_code_def] >>
  `f.fn_blocks <> []` by
    (Cases_on `f.fn_blocks` >> gvs[fn_entry_label_def, entry_block_def]) >>
  `lbl = (HD f.fn_blocks).bb_label` by
    gvs[fn_entry_label_def, entry_block_def, NULL_EQ] >>
  `lookup_block lbl f.fn_blocks = SOME (HD f.fn_blocks)` by
    (Cases_on `f.fn_blocks` >> gvs[lookup_block_def, FIND_def, INDEX_FIND_def]) >>
  `lookup_block lbl at.po_fn.fn_blocks = SOME
    (clear_nops_block (block_map_transform
      (concretize_inst_with_positions (lp f)) (HD f.fn_blocks)))` by
    (simp[concretize_positions_blocks, lookup_block_map,
          concretize_positions_block_label] >> metis_tac[]) >>
  qpat_x_assum `enters_block _ _ _` mp_tac >>
  simp[enters_block_def] >> strip_tac >> gvs[] >>
  `EVERY (\i. i.inst_opcode <> PHI)
    (clear_nops_block (block_map_transform
      (concretize_inst_with_positions (lp f)) (HD f.fn_blocks))).bb_instructions` by
    (fs[first_block_no_phi_def, clear_nops_block_def, block_map_transform_def,
        EVERY_FILTER, EVERY_MAP, EVERY_MEM, concretize_positions_phi] >>
     simp[MEM_FILTER, MEM_MAP] >> metis_tac[concretize_positions_phi]) >>
  gvs[eval_phis_no_phis, no_phis_phi_prefix_length_zero, ptr_observe_def] >>
  qpat_x_assum `at = _` SUBST1_TAC >> simp[]
QED

(* This is the missing root cursor supplier, not an assumed cursor. *)
Theorem ptr_paired_root_cursor:
  ptr_paired_code R lp positions f g /\
  ALL_DISTINCT (fn_labels g) /\
  fn_inst_wf f /\
  (!inst. MEM inst (fn_insts f) /\ inst.inst_opcode = ALLOCA ==>
    IS_SOME (FLOOKUP (lp f) (Allocation inst.inst_id))) /\
  f.fn_blocks <> [] /\
  a.po_fn = f /\ at.po_fn = g /\
  a.po_state.vs_current_bb = (HD f.fn_blocks).bb_label /\
  at.po_state.vs_current_bb = (HD f.fn_blocks).bb_label /\
  a.po_state.vs_prev_bb = at.po_state.vs_prev_bb /\
  a.po_state.vs_inst_idx = 0 /\ at.po_state.vs_inst_idx = 0 /\
  a.po_inst = HD (HD f.fn_blocks).bb_instructions /\
  active_inst g at.po_inst at.po_state ==>
  ptr_paired_cursor lp a at
Proof
  strip_tac >>
  `MEM (HD f.fn_blocks) f.fn_blocks` by
    (Cases_on `f.fn_blocks` >> gvs[]) >>
  drule ptr_ledger_alignment_function >>
  disch_then (qspec_then `lp f` mp_tac) >> strip_tac >>
  `MEM bbt g.fn_blocks` by fs[ptr_paired_code_def] >>
  `lookup_block at.po_state.vs_current_bb g.fn_blocks = SOME bbt` by
    (irule MEM_lookup_block >> gvs[fn_labels_def]) >>
  `at.po_state.vs_inst_idx < LENGTH bbt.bb_instructions /\
   at.po_inst = EL at.po_state.vs_inst_idx bbt.bb_instructions` by
    (fs[active_inst_def] >>
     `lookup_block at.po_state.vs_current_bb g.fn_blocks = SOME bb` by
       (irule MEM_lookup_block >> gvs[fn_labels_def]) >> gvs[]) >>
  `LENGTH bbt.bb_instructions = LENGTH indices /\
   EL 0 indices < LENGTH (HD f.fn_blocks).bb_instructions` by
    metis_tac[ptr_ledger_alignment_cursor] >>
  `lookup_block (HD f.fn_blocks).bb_label g.fn_blocks = SOME bbt` by metis_tac[] >>
  simp[ptr_paired_cursor_def] >>
  qexistsl_tac [`HD f.fn_blocks`,`indices`] >> simp[] >>
  conj_tac
  >- (Cases_on `f.fn_blocks` >> gvs[lookup_block_def, FIND_def, INDEX_FIND_def]) >>
  rpt strip_tac >> irule ptr_paired_covered_gap >>
  conj_tac
  >- (fs[fn_inst_wf_def, EVERY_MEM, fn_insts_def, fn_insts_blocks_def,
         MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  qexistsl_tac [`indices`,`0`,`lp f`,`bbt.bb_instructions`] >>
  simp[] >> rpt strip_tac >> first_x_assum irule >>
  Cases_on `f.fn_blocks` >> gvs[fn_insts_def, fn_insts_blocks_def]
QED


Theorem ptr_paired_root:
  ptr_chrono_history vs0 Ct [at] at /\ at.po_stack = [] /\
  C.ctx_entry = SOME name /\ lookup_function name C.ctx_functions = SOME f /\
  ptr_paired_code R lp positions f at.po_fn /\
  ptr_stage_placements Ct positions /\ vs0.vs_vars = FEMPTY /\
  first_block_no_phi f /\ fn_inst_wf f /\
  (HD f.fn_blocks).bb_instructions <> [] /\
  ALL_DISTINCT (fn_labels at.po_fn) /\
  (!inst. MEM inst (fn_insts f) /\ inst.inst_opcode = ALLOCA ==>
    IS_SOME (FLOOKUP (lp f) (Allocation inst.inst_id))) ==>
  ?a. ptr_chrono_history vs0 C [a] a /\ a.po_fn = f /\
    ptr_paired_prefix R lp positions lo vs0 C Ct [a] a [at] at [] [0]
      (FEMPTY |+ (0,f)) (ptr_birth_lift 0 a.po_state.vs_allocas)
      [] FEMPTY [] (FEMPTY |+ (0,0))
      [([0],FEMPTY |+ (0,f),ptr_birth_lift 0 a.po_state.vs_allocas,
        [],FEMPTY,[],FEMPTY |+ (0,0))] [] []
Proof
  strip_tac >> drule_all ptr_paired_root_target_state >> strip_tac >>
  drule_all ptr_chrono_source_root >>
  disch_then (qspec_then `vs0` strip_assume_tac) >>
  `f.fn_blocks <> []` by
    (Cases_on `f.fn_blocks` >> gvs[fn_entry_label_def, entry_block_def]) >>
  `lbl = (HD f.fn_blocks).bb_label` by
    gvs[fn_entry_label_def, entry_block_def, NULL_EQ] >>
  `active_inst at.po_fn at.po_inst at.po_state` by
    (qpat_assum `ptr_chrono_history vs0 Ct [at] at`
       (mp_then Any strip_assume_tac ptr_chrono_root_inversion) >>
     qpat_x_assum `at = _` SUBST1_TAC >> simp[ptr_observe_def]) >>
  `ptr_paired_cursor lp a at` by
    (drule ptr_paired_root_cursor >> simp[] >>
     disch_then irule >> simp[]) >>
  `ptr_mixed_vars (ptr_birth_lift (0:num) a.po_state.vs_allocas) positions
     FEMPTY entry_taint f at.po_fn a.po_state at.po_state /\
   ptr_history_content entry_taint a.po_state at.po_state` by
    (`!x. retpc_var f x <=> retpc_var at.po_fn x` by
       metis_tac[ptr_paired_code_retpc] >>
     simp[ptr_mixed_vars_def, ptr_opaque_env_def, lookup_var_def,
          ptr_lookup_transport_def, ptr_core_shared_def, ptr_shared_fields_def]) >>
  qexists_tac `a` >> simp[ptr_paired_prefix_def] >>
  conj_tac
  >- (`R a.po_fn at.po_fn` by fs[ptr_paired_code_def] >>
      drule_all ptr_structural_transcript_root >> simp[]) >>
  simp[ptr_paired_samples_def, ptr_sample_list_def, ptr_paired_sample_def,
       ptr_paired_alignment_def, ptr_paired_params_def,
       ptr_paired_callers_def, ptr_paired_writes_def] >> gvs[] >>
  metis_tac[]
QED

Theorem ptr_paired_root_normalized:
  ptr_chrono_history vs0 Ct [at] at /\ at.po_stack = [] /\
  C.ctx_entry = SOME name /\ lookup_function name C.ctx_functions = SOME f /\
  ptr_paired_code R lp positions f at.po_fn /\
  ptr_stage_placements Ct positions /\ vs0.vs_vars = FEMPTY /\
  first_block_no_phi f /\ fn_inst_wf f /\
  (HD f.fn_blocks).bb_instructions <> [] /\
  ALL_DISTINCT (fn_labels at.po_fn) /\
  (!inst. MEM inst (fn_insts f) /\ inst.inst_opcode = ALLOCA ==>
    IS_SOME (FLOOKUP (lp f) (Allocation inst.inst_id))) ==>
  ?a bb n delta snapshots.
    ptr_chrono_history vs0 C [a] a /\ a.po_fn = f /\
    lookup_block a.po_state.vs_current_bb f.fn_blocks = SOME bb /\
    LENGTH delta = n /\ LENGTH snapshots = n /\
    ptr_paired_prefix R lp positions lo vs0 C Ct
      ([a] ++ delta) (ptr_gap_scan bb n a) [at] at [] [0]
      (FEMPTY |+ (0,f)) (ptr_birth_lift 0 a.po_state.vs_allocas)
      [] FEMPTY [] (FEMPTY |+ (0,0))
      ([([0],FEMPTY |+ (0,f),ptr_birth_lift 0 a.po_state.vs_allocas,
        [],FEMPTY,[],FEMPTY |+ (0,0))] ++ snapshots) [] [] /\
    (ptr_gap_scan bb n a).po_inst.inst_opcode <> NOP /\
    at.po_inst = concretize_inst_with_positions (lp f)
      (ptr_gap_scan bb n a).po_inst /\
    (ptr_gap_scan bb n a).po_prov = a.po_prov /\
    (ptr_gap_scan bb n a).po_taint = a.po_taint
Proof
  strip_tac >> drule_all ptr_paired_root >>
  disch_then (qspec_then `lo` strip_assume_tac) >>
  drule ptr_paired_prefix_normalize >> simp[] >> strip_tac >>
  qexistsl_tac [`a`,`bb`,`delta`,`snapshots`] >> simp[]
QED
