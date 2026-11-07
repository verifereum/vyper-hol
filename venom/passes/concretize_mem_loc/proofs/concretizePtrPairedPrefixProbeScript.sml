Theory concretizePtrPairedPrefixProbe
Ancestors
  concretizePtrPairedPrefix concretizePtrPairedFields concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrActivationChronology concretizePtrActivationBirths
  concretizePtrValueTransport concretizePtrOpaqueRetpc
  concretizePtrValueSelection concretizePtrAffineTransport concretizePtrRequestHistory
  concretizePtrTaintContent
  concretizePtrOwnedAssignPrefix concretizePtrSharedFields
  concretizePtrChronologicalHistory concretizePtrRuntimeTotality
  concretizePtrLayoutOutput staticLayoutCompletionProofs staticLayoutAllocatorProofs
  concretizeMemLocDefs
  concretizePtrDeletedGapHistory concretizePtrSourceOwnership
  concretizePtrLedgerAlignment concretizeStepStructure
  makeSsaHelper o1PassContract unitTransformDefs
  contextCodegenRel ptrDiscipline venomExecSemantics lowerDloadDefs
  venomState list rich_list finite_map words passSharedDefs

(* The raw total relation cannot represent arbitrary root parameters. *)
Theorem ptr_args_empty_tags_params_empty:
  ptr_args_transport births positions [] masks xs ys ==> xs = []
Proof
  simp[ptr_args_transport_def]
QED

Theorem ptr_paired_root_params:
  a.po_state.vs_params = at.po_state.vs_params ==>
  ptr_paired_params positions a at
    (tokens,registry,births,[],TG,saved,entries)
Proof
  simp[concretizePtrPairedFieldsTheory.ptr_paired_params_def]
QED

Theorem ptr_run_state_ok_params_unrestricted:
  o1_run_state_ok vs ==> o1_run_state_ok (vs with vs_params := params)
Proof
  simp[o1_run_state_ok_def, o1_initial_state_ok_def, code_layout_valid_def]
QED

Theorem ptr_paired_root_param_prov:
  inst.inst_opcode = PARAM ==> out_prov [] TG inst s' = NONE
Proof
  strip_tac >> simp[out_prov_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `h` >> simp[] >> Cases_on `t` >> simp[]
QED

Theorem ptr_paired_root_param_transport:
  ptr_vars_transport births positions TG tn s t /\
  s.vs_params = t.vs_params /\
  inst.inst_opcode = PARAM /\ inst.inst_operands = [Lit idx] /\
  inst.inst_outputs = [out] /\ w2n idx < LENGTH s.vs_params ==>
  ?s' t'. step_inst fuel C inst s = OK s' /\
    step_inst fuel Ct inst t = OK t' /\
    ptr_vars_transport births positions (step_prov [] TG inst s')
      (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `w2n idx < LENGTH t.vs_params` by metis_tac[] >>
  qexistsl_tac [`update_var out (EL (w2n idx) s.vs_params) s`,
               `update_var out (EL (w2n idx) t.vs_params) t`] >>
  drule_all ptr_param_step >> disch_then (fn th => simp[th]) >>
  simp[step_prov_def, out_prov_def] >>
  irule ptr_vars_transport_update >> rpt (goal_assum (drule_at Any)) >>
  simp[step_taint_def, out_taint_def, eval_operand_def,
    ptr_value_transport_scalar_empty] >>
  qexists_tac `{}` >> simp[ptr_value_transport_scalar_empty]
QED

(* Administrative gaps leave runtime parameters unchanged, for either branch
   of the repaired parameter relation. *)
Theorem ptr_paired_gap_scan_params:
  ptr_paired_params positions a at
    (tokens,registry,births,PT,TG,saved,entries) ==>
  ptr_paired_params positions (ptr_gap_scan bb n a) at
    (tokens',registry',births,PT,TG',saved',entries')
Proof
  simp[concretizePtrPairedFieldsTheory.ptr_paired_params_def,
    ptr_gap_scan_fields]
QED

Theorem ptr_paired_cursor_normalize:
  ptr_paired_cursor local_positions a at /\
  lookup_block a.po_state.vs_current_bb a.po_fn.fn_blocks = SOME bb ==>
  ?n. ptr_paired_cursor local_positions (ptr_gap_scan bb n a) at /\
    (ptr_gap_scan bb n a).po_state.vs_inst_idx =
      a.po_state.vs_inst_idx + n /\
    !k. a.po_state.vs_inst_idx <= k /\
      k < a.po_state.vs_inst_idx + n ==>
      (EL k bb.bb_instructions).inst_opcode = NOP
Proof
  simp[concretizePtrPairedFieldsTheory.ptr_paired_cursor_def] >>
  rpt strip_tac >>
  gvs[] >>
  qexists_tac `EL at.po_state.vs_inst_idx indices - a.po_state.vs_inst_idx` >>
  `a.po_state.vs_inst_idx +
    (EL at.po_state.vs_inst_idx indices - a.po_state.vs_inst_idx) =
    EL at.po_state.vs_inst_idx indices` by decide_tac >>
  simp[ptr_gap_scan_fields] >>
  qexists_tac `indices` >> simp[] >>
  Cases_on `a.po_state.vs_inst_idx = EL at.po_state.vs_inst_idx indices`
  >- simp[ptr_gap_scan_def] >>
  `0 < EL at.po_state.vs_inst_idx indices - a.po_state.vs_inst_idx` by decide_tac >>
  simp[ptr_gap_scan_fields]
QED

Theorem ptr_paired_cursor_owned_scan:
  ptr_paired_cursor local_positions a at /\
  lookup_block a.po_state.vs_current_bb a.po_fn.fn_blocks = SOME bb /\
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved ==>
  ?n delta. LENGTH delta = n /\
    ptr_source_ownership vs0 C (h ++ delta) (ptr_gap_scan bb n a)
      tokens registry births PT (ptr_gap_tag_scan bb n a PT TG) saved /\
    ptr_paired_cursor local_positions (ptr_gap_scan bb n a) at
Proof
  simp[concretizePtrPairedFieldsTheory.ptr_paired_cursor_def] >>
  rpt strip_tac >> gvs[] >>
  `EL at.po_state.vs_inst_idx indices < LENGTH bb.bb_instructions` by
    (drule concretizePtrLedgerAlignmentTheory.ptr_ledger_alignment_cursor >>
     strip_tac >> gvs[]) >>
  `?delta. LENGTH delta = EL at.po_state.vs_inst_idx indices - a.po_state.vs_inst_idx /\
    ptr_source_ownership vs0 C (h ++ delta)
      (ptr_gap_scan bb (EL at.po_state.vs_inst_idx indices - a.po_state.vs_inst_idx) a)
      tokens registry births PT
      (ptr_gap_tag_scan bb (EL at.po_state.vs_inst_idx indices - a.po_state.vs_inst_idx) a PT TG) saved` by
    (irule ptr_gap_ownership_scan >> simp[] >>
     `bb.bb_label = a.po_state.vs_current_bb` by
       metis_tac[lookup_block_label] >> simp[]) >>
  qexists_tac `delta` >>
  `a.po_state.vs_inst_idx + LENGTH delta = EL at.po_state.vs_inst_idx indices` by decide_tac >>
  simp[ptr_gap_scan_fields] >>
  qexists_tac `indices` >> simp[] >>
  Cases_on `a.po_state.vs_inst_idx = EL at.po_state.vs_inst_idx indices`
  >- simp[ptr_gap_scan_def] >>
  `0 < EL at.po_state.vs_inst_idx indices - a.po_state.vs_inst_idx` by decide_tac >>
  simp[ptr_gap_scan_fields]
QED

Theorem ptr_paired_gap_scan_sample:
  fn_inst_wf a.po_fn /\ MEM bb a.po_fn.fn_blocks /\
  a.po_inst = EL a.po_state.vs_inst_idx bb.bb_instructions /\
  a.po_state.vs_inst_idx + n < LENGTH bb.bb_instructions /\
  (!q. a.po_state.vs_inst_idx <= q /\ q < a.po_state.vs_inst_idx + n ==>
    (EL q bb.bb_instructions).inst_opcode = NOP) /\
  ptr_paired_sample positions a at
    (tokens,registry,births,PT,TG,saved,entries) ==>
  ptr_paired_sample positions (ptr_gap_scan bb n a) at
    (tokens,registry,births,PT,ptr_gap_tag_scan bb n a PT TG,saved,entries)
Proof
  simp[ptr_paired_sample_def] >> strip_tac >>
  `ptr_gap_tag_scan bb n a PT TG = TG /\
   (ptr_gap_scan bb n a).po_prov = a.po_prov /\
   (ptr_gap_scan bb n a).po_taint = a.po_taint` by
    (irule ptr_assign_prefix_gap_ghosts >> simp[]) >>
  conj_tac
  >- (simp[ptr_gap_scan_fields] >> irule ptr_mixed_vars_fields >>
      goal_assum (drule_at Any) >> simp[ptr_gap_scan_fields]) >>
  gvs[ptr_gap_scan_fields, ptr_history_content_def, ptr_taint_content_def,
      ptr_taint_control_def, ptr_core_shared_def, ptr_shared_fields_def,
      contract_storage_def, contract_transient_def]
QED

Theorem ptr_paired_cursor_nop_next:
  ptr_paired_cursor lp a at /\ a.po_inst.inst_opcode = NOP /\
  lookup_block a.po_state.vs_current_bb a.po_fn.fn_blocks = SOME bb ==>
  ptr_paired_cursor lp (ptr_gap_next bb a) at /\
  SUC a.po_state.vs_inst_idx < LENGTH bb.bb_instructions
Proof
  simp[ptr_paired_cursor_def] >> rpt gen_tac >> strip_tac >> gvs[] >>
  drule ptr_ledger_alignment_cursor >> strip_tac >>
  `at.po_state.vs_inst_idx < LENGTH bbt.bb_instructions` by gvs[] >>
  first_x_assum drule >> strip_tac >>
  `a.po_state.vs_inst_idx < EL at.po_state.vs_inst_idx indices` by
    (Cases_on `a.po_state.vs_inst_idx = EL at.po_state.vs_inst_idx indices`
     >- (gvs[] >> metis_tac[concretize_positions_nop]) >> decide_tac) >>
  reverse conj_tac >- decide_tac >>
  simp[ptr_gap_next_fields] >> qexists_tac `indices` >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem ptr_paired_prefix_gap_next:
  !W. ptr_paired_prefix R lp positions lo vs0 C Ct
    h a ht at done tokens registry births PT TG saved entries H calls W /\
  fn_inst_wf a.po_fn /\
  lookup_block a.po_state.vs_current_bb a.po_fn.fn_blocks = SOME bb /\
  a.po_inst.inst_opcode = NOP ==>
  ptr_paired_prefix R lp positions lo vs0 C Ct
    (h ++ [ptr_gap_next bb a]) (ptr_gap_next bb a) ht at done
    tokens registry births PT (step_prov PT TG a.po_inst a.po_state) saved entries
    (H ++ [(tokens,registry,births,PT,step_prov PT TG a.po_inst a.po_state,saved,entries)]) calls W
Proof
  gen_tac >> strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule_all ptr_paired_cursor_nop_next >> strip_tac >>
  `MEM bb a.po_fn.fn_blocks /\ bb.bb_label = a.po_state.vs_current_bb /\
    a.po_inst = EL a.po_state.vs_inst_idx bb.bb_instructions` by
    (qpat_x_assum `ptr_paired_cursor lp a at` mp_tac >>
     simp[ptr_paired_cursor_def] >> rpt strip_tac >> gvs[] >>
     metis_tac[lookup_block_label]) >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  drule ptr_ownership_overlay_fixed >> strip_tac >>
  `ptr_tagged_chrono_step C (HD tokens) a (ptr_gap_next bb a)
    PT TG saved PT (step_prov PT TG a.po_inst a.po_state) saved` by
    (irule ptr_gap_tagged_next >> simp[]) >>
  `ptr_activation_tokens h a (ptr_gap_next bb a) tokens = tokens /\
   ptr_activation_registry h a (ptr_gap_next bb a) registry = registry /\
   ptr_birth_overlay (HD tokens) (ptr_gap_next bb a).po_state.vs_allocas births = births` by
    simp[ptr_activation_tokens_def, ptr_activation_registry_def, ptr_gap_next_fields] >>
  drule ptr_paired_prefix_gap >>
  disch_then (qspecl_then [`saved`,`ptr_gap_next bb a`,
    `step_prov PT TG a.po_inst a.po_state`,`PT`] mp_tac) >>
  simp[ptr_gap_next_fields] >> disch_then irule >> conj_tac
  >- gvs[ptr_paired_params_def, ptr_gap_next_fields] >>
  qpat_assum `a.po_inst = _` (fn th => once_rewrite_tac[GSYM th]) >>
  irule (PURE_REWRITE_RULE [ptr_gap_scan_def, ptr_gap_tag_scan_def]
    (Q.INST [`n` |-> `SUC 0`] (SPEC_ALL ptr_paired_gap_scan_sample))) >>
  simp[] >> rpt strip_tac >>
  `q = a.po_state.vs_inst_idx` by decide_tac >> metis_tac[]
QED


Theorem ptr_paired_prefix_gap_scan:
  !n a h TG H.
  ptr_paired_prefix R lp positions lo vs0 C Ct
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  fn_inst_wf a.po_fn /\
  lookup_block a.po_state.vs_current_bb a.po_fn.fn_blocks = SOME bb /\
  a.po_state.vs_inst_idx + n < LENGTH bb.bb_instructions /\
  (!q. a.po_state.vs_inst_idx <= q /\ q < a.po_state.vs_inst_idx + n ==>
    (EL q bb.bb_instructions).inst_opcode = NOP) ==>
  ?delta snapshots. LENGTH delta = n /\ LENGTH snapshots = n /\
    ptr_paired_prefix R lp positions lo vs0 C Ct
      (h ++ delta) (ptr_gap_scan bb n a) ht at done tokens registry births PT
      (ptr_gap_tag_scan bb n a PT TG) saved entries (H ++ snapshots) calls ws
Proof
  Induct
  >- (rpt strip_tac >> qexistsl_tac [`[]`,`[]`] >>
      simp[ptr_gap_scan_def, ptr_gap_tag_scan_def]) >>
  rpt gen_tac >> strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  `a.po_inst = EL a.po_state.vs_inst_idx bb.bb_instructions` by
    (gvs[ptr_paired_cursor_def]) >>
  `a.po_inst.inst_opcode = NOP` by
    (first_x_assum (qspec_then `a.po_state.vs_inst_idx` mp_tac) >> simp[]) >>
  drule_all ptr_paired_prefix_gap_next >> strip_tac >>
  first_x_assum (qspecl_then [`ptr_gap_next bb a`,`h ++ [ptr_gap_next bb a]`,
    `step_prov PT TG a.po_inst a.po_state`,
    `H ++ [(tokens,registry,births,PT,step_prov PT TG a.po_inst a.po_state,saved,entries)]`] mp_tac) >>
  simp[ptr_gap_next_fields, arithmeticTheory.ADD_CLAUSES] >>
  strip_tac >>
  qexistsl_tac [`ptr_gap_next bb a :: delta`,
    `(tokens,registry,births,PT,step_prov PT TG a.po_inst a.po_state,saved,entries) :: snapshots`] >>
  simp[ptr_gap_scan_def, ptr_gap_tag_scan_def] >>
  pop_assum mp_tac >> pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[]
QED

(* A missing layout entry can delete an ALLOCA, not only a source NOP.
   This tests the proposed initial cursor interface, not the task theorem. *)
Theorem ptr_paired_root_deleted_alloca_obstruction:
  i.inst_opcode = ALLOCA /\ i.inst_outputs = [out] /\
  t.inst_opcode = STOP ==>
  EVERY (\inst. inst.inst_opcode <> PHI) [i;t] /\
  ptr_ledger_block_alignment FEMPTY [i;t] [t] [1] /\
  (!indices. ptr_ledger_block_alignment FEMPTY [i;t] [t] indices ==>
    ~(!k. k < EL 0 indices ==>
      (EL k [i;t]).inst_opcode = NOP))
Proof
  strip_tac >>
  `COUNT_LIST 2 = [0;1]` by EVAL_TAC >>
  simp[concretizePtrPrefixLedgerTheory.ptr_ledger_block_alignment_def,
    concretize_positions_missing, concretize_positions_unchanged,
    mk_nop_inst_def]
QED

(* Production completion fills even dead source ALLOCAs. The layout witness,
   rather than the unconstrained paired-code relation, carries coverage. *)
Theorem ptr_paired_production_coverage:
  fn.fn_eom = NONE /\
  concretize_function_fuel_in_context fuel ctx reserved fn = SOME fn' ==>
  ?layout. fn' = apply_context_concretize_layout ctx layout fn /\
    !inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP layout.cl_positions (Allocation inst.inst_id))
Proof
  strip_tac >> drule_all ptr_fresh_layout_representation >> strip_tac >>
  qexists_tac `layout` >> simp[] >> rpt strip_tac >>
  drule_all static_alloca_items_ALLOCA_exact >> strip_tac >>
  Cases_on `fn_needs_liveness_allocation fn \/ imported_mems_used ctx fn <> []`
  >- (gvs[] >> drule_all complete_alloc_positions_with_imports_success >>
      strip_tac >> drule ptr_mk_layout_positions >> strip_tac >>
      gvs[] >> metis_tac[optionTheory.IS_SOME_EXISTS]) >>
  gvs[] >> drule complete_alloc_positions_success >> strip_tac >>
  drule ptr_mk_layout_positions >> strip_tac >>
  gvs[] >> metis_tac[optionTheory.IS_SOME_EXISTS]
QED

Theorem ptr_paired_covered_gap:
  ptr_ledger_block_alignment positions src tgt indices /\
  EVERY inst_wf src /\
  (!inst. MEM inst src /\ inst.inst_opcode = ALLOCA ==>
    IS_SOME (FLOOKUP positions (Allocation inst.inst_id))) /\
  j < LENGTH indices /\ i < EL j indices /\
  (j = 0 \/ EL (j-1) indices < i) ==>
  (EL i src).inst_opcode = NOP
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `LENGTH tgt = LENGTH indices /\ EL j indices < LENGTH src` by
    metis_tac[ptr_ledger_alignment_cursor] >>
  `i < LENGTH src` by decide_tac >>
  `MEM (EL i src) src` by simp[EL_MEM] >>
  `inst_wf (EL i src)` by gvs[EVERY_MEM] >>
  `(concretize_inst_with_positions positions (EL i src)).inst_opcode = NOP`
    by metis_tac[ptr_ledger_alignment_gap] >>
  Cases_on `(EL i src).inst_opcode = ALLOCA`
  >- (`IS_SOME (FLOOKUP positions (Allocation (EL i src).inst_id))` by
        metis_tac[] >>
      `LENGTH (EL i src).inst_outputs = 1` by
        gvs[venomWfTheory.inst_wf_def] >>
      Cases_on `(EL i src).inst_outputs` >> gvs[] >>
      Cases_on `FLOOKUP positions (Allocation (EL i src).inst_id)` >>
      gvs[concretize_inst_with_positions_def, mk_assign_inst_def] >>
      metis_tac[optionTheory.IS_SOME_DEF]) >>
  gvs[concretize_positions_unchanged]
QED

(* Setup copies the final runtime argument into the return-PC token even
   when that argument is an ordinary relocated pointer. *)
Theorem ptr_paired_call_last_arg_obstruction:
  ~NULL f.fn_blocks ==>
  ptr_args_transport (FEMPTY |+ ((0,0),(1,1)))
    (FEMPTY |+ (Allocation 0,(2,1))) [SOME (0,0)] [{}]
    [1w] [2w] /\
  ?cs ct. setup_callee f [1w] s = SOME cs /\
    setup_callee f [2w] s = SOME ct /\ ~ptr_shared_fields cs ct
Proof
  strip_tac >> conj_tac
  >- (simp[ptr_args_transport_def, ptr_value_transport_def, FLOOKUP_UPDATE] >>
      wordsLib.WORD_DECIDE_TAC) >>
  simp[setup_callee_def, ptr_shared_fields_def]
QED

Theorem ptr_paired_prefix_normalize:
  ptr_paired_prefix R lp positions lo vs0 C Ct
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  fn_inst_wf a.po_fn ==>
  ?bb n delta snapshots.
    lookup_block a.po_state.vs_current_bb a.po_fn.fn_blocks = SOME bb /\
    LENGTH delta = n /\ LENGTH snapshots = n /\
    ptr_paired_prefix R lp positions lo vs0 C Ct
      (h ++ delta) (ptr_gap_scan bb n a) ht at done tokens registry births PT
      TG saved entries (H ++ snapshots) calls ws /\
    (ptr_gap_scan bb n a).po_inst.inst_opcode <> NOP /\
    at.po_inst = concretize_inst_with_positions (lp a.po_fn)
      (ptr_gap_scan bb n a).po_inst /\
    (ptr_gap_scan bb n a).po_prov = a.po_prov /\
    (ptr_gap_scan bb n a).po_taint = a.po_taint
Proof
  strip_tac >> drule ptr_paired_prefix_endpoint >> strip_tac >>
  qpat_x_assum `ptr_paired_cursor lp a at` mp_tac >>
  simp[ptr_paired_cursor_def] >> strip_tac >>
  drule ptr_ledger_alignment_cursor >> strip_tac >>
  `at.po_state.vs_inst_idx < LENGTH bbt.bb_instructions` by gvs[] >>
  first_x_assum drule >> strip_tac >>
  qmatch_asmsub_abbrev_tac `EL j indices < LENGTH bb.bb_instructions` >>
  qabbrev_tac `n = EL j indices - a.po_state.vs_inst_idx` >>
  `a.po_state.vs_inst_idx + n = EL j indices` by
    (simp[Abbr `n`] >> decide_tac) >>
  `?delta snapshots. LENGTH delta = n /\ LENGTH snapshots = n /\
    ptr_paired_prefix R lp positions lo vs0 C Ct
      (h ++ delta) (ptr_gap_scan bb n a) ht at done tokens registry births PT
      (ptr_gap_tag_scan bb n a PT TG) saved entries (H ++ snapshots) calls ws` by
    (irule ptr_paired_prefix_gap_scan >> simp[] >> metis_tac[]) >>
  `ptr_gap_tag_scan bb n a PT TG = TG /\
   (ptr_gap_scan bb n a).po_prov = a.po_prov /\
   (ptr_gap_scan bb n a).po_taint = a.po_taint` by
    (irule ptr_assign_prefix_gap_ghosts >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`bb`,`delta`,`snapshots`] >> simp[] >>
  Cases_on `n = 0`
  >- (gvs[ptr_gap_scan_def] >> metis_tac[concretize_positions_nop]) >>
  `0 < n` by decide_tac >>
  simp[ptr_gap_scan_fields] >> metis_tac[concretize_positions_nop]
QED

(* Candidate certificate probes: endpoint facts are inputs, not semantic
   preservation claims. There is only one sample-list implementation. *)
Theorem ptr_content_sample_list_root_probe[local]:
  ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
    a.po_state at.po_state /\
  ptr_history_content a.po_taint a.po_state at.po_state ==>
  ptr_sample_list
    (\a at (tokens,registry,births,PT,TG,saved,entries).
      ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
        a.po_state at.po_state /\
      ptr_history_content a.po_taint a.po_state at.po_state)
    [a] [at] [] [(tokens,registry,births,PT,TG,saved,entries)]
Proof
  strip_tac >> irule ptr_sample_list_root >> simp[]
QED

Theorem ptr_content_sample_list_gap_probe[local]:
  ptr_sample_list
    (\a at (tokens,registry,births,PT,TG,saved,entries).
      ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
        a.po_state at.po_state /\
      ptr_history_content a.po_taint a.po_state at.po_state)
    h ht done H /\
  ptr_mixed_vars births positions TG b.po_taint b.po_fn
    (EL (LENGTH done) ht).po_fn b.po_state
    (EL (LENGTH done) ht).po_state /\
  ptr_history_content b.po_taint b.po_state
    (EL (LENGTH done) ht).po_state ==>
  ptr_sample_list
    (\a at (tokens,registry,births,PT,TG,saved,entries).
      ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
        a.po_state at.po_state /\
      ptr_history_content a.po_taint a.po_state at.po_state)
    (h ++ [b]) ht done
    (H ++ [(tokens,registry,births,PT,TG,saved,entries)])
Proof
  strip_tac >> irule ptr_sample_list_gap >> simp[]
QED

Theorem ptr_content_sample_list_pair_probe[local]:
  ptr_sample_list
    (\a at (tokens,registry,births,PT,TG,saved,entries).
      ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
        a.po_state at.po_state /\
      ptr_history_content a.po_taint a.po_state at.po_state)
    h ht done H /\
  ptr_mixed_vars births positions TG b.po_taint b.po_fn bt.po_fn
    b.po_state bt.po_state /\
  ptr_history_content b.po_taint b.po_state bt.po_state ==>
  ptr_sample_list
    (\a at (tokens,registry,births,PT,TG,saved,entries).
      ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
        a.po_state at.po_state /\
      ptr_history_content a.po_taint a.po_state at.po_state)
    (h ++ [b]) (ht ++ [bt]) (done ++ [LENGTH h - 1])
    (H ++ [(tokens,registry,births,PT,TG,saved,entries)])
Proof
  strip_tac >> irule ptr_sample_list_pair >> simp[]
QED
