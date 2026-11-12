(* Total body boundaries after selected returns; selected next calls need not
   survive the ordinary instruction-location action. *)
Theory functionInlinerSelectedContinuation
Ancestors
  functionInlinerLiveSelected functionInlinerLiveEdges
  functionInlinerReturnCoordinates functionInlinerEntryHandoff
  functionInlinerSelectedParameterDescriptors functionInlinerParameterLocations
  functionInlinerOccurrences functionInlinerLocation functionInlinerActivation
  functionInlinerPairedSelection functionInlinerRoutedProvenance functionInlinerEnvelopes
  functionInlinerRouteKeys functionInlinerLiveInvariant functionInlinerOperationalCuts
  functionInlinerParameterAncestry functionInlinerParameterSavedReads
  functionInlinerFrame functionInlinerSimulation
  functionInlinerSiteLayout functionInlinerReachableCuts functionInlinerDefs venomInst list

Theorem inline_parameter_boundary_path_append:
  !path fn l j mid ml mj rest root rl rj.
    inline_parameter_boundary_path path fn l j mid ml mj /\
    inline_parameter_boundary_path rest mid ml mj root rl rj ==>
    inline_parameter_boundary_path (path ++ rest) fn l j root rl rj
Proof
  Induct >> simp[inline_parameter_boundary_path_def] >>
  rpt strip_tac >> goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem inline_selected_site_successor_boundary:
  inline_site_edit_valid e /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
  e.ise_index < LENGTH bb.bb_instructions /\
  ~MEM e.ise_return (fn_labels e.ise_caller) ==>
  inline_parameter_boundary (InlineKeep e) e.ise_caller e.ise_block
    (SUC e.ise_index) e.ise_final e.ise_return 0
Proof
  strip_tac >>
  `SUC e.ise_index <= LENGTH bb.bb_instructions` by decide_tac >>
  drule_all inline_keep_boundary_produce >>
  simp[inline_keep_boundary_def, arithmeticTheory.ADD1]
QED

Theorem inline_invoke_prefix_length_suc:
  get_instruction cb j = SOME inst /\ inst.inst_opcode = INVOKE ==>
  LENGTH (FST (inline_cell_prefix e bb cb (SUC j))) =
    SUC (LENGTH (FST (inline_cell_prefix e bb cb j)))
Proof
  strip_tac >>
  `j < LENGTH cb.bb_instructions` by gvs[get_instruction_def] >>
  drule inline_cell_prefix_suc >>
  disch_then (qspecl_then [`e`, `bb`] assume_tac) >>
  gvs[get_instruction_def, inline_cell_focus_def, clone_instruction_def,
      rewrite_inline_inst_def, is_param_opcode_def]
QED

Theorem inline_keep_successor_boundary:
  inline_site_edit_valid e /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
  e.ise_index < LENGTH bb.bb_instructions /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  lookup_block l e.ise_caller.fn_blocks = SOME cb /\
  get_instruction cb j = SOME inst /\
  inline_choice_location (InlineKeep e)
    <|il_block := l; il_phase := InlineAtInstruction j; il_counter := k|> =
    SOME <|il_block := ml; il_phase := InlineAtInstruction mj; il_counter := next|> ==>
  inline_parameter_boundary (InlineKeep e) e.ise_caller l (SUC j)
    e.ise_final ml (SUC mj)
Proof
  strip_tac >>
  `SUC j <= LENGTH cb.bb_instructions` by gvs[get_instruction_def] >>
  drule_all inline_keep_boundary_produce >>
  gvs[inline_choice_location_def, inline_keep_boundary_def] >>
  Cases_on `l = e.ise_block` >> gvs[] >>
  Cases_on `e.ise_index < j` >> gvs[] >>
  simp[arithmeticTheory.ADD1] >> strip_tac >> gvs[]
QED

Theorem inline_enter_invoke_successor_boundary:
  inline_site_edit_valid e /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  ~MEM (STRCAT e.ise_prefix l) (fn_labels e.ise_caller) /\
  STRCAT e.ise_prefix l <> e.ise_return /\
  lookup_block l e.ise_callee.fn_blocks = SOME cb /\
  get_instruction cb j = SOME inst /\ inst.inst_opcode = INVOKE /\
  inline_choice_location (InlineEnter e)
    <|il_block := l; il_phase := InlineAtInstruction j; il_counter := k|> =
    SOME <|il_block := ml; il_phase := InlineAtInstruction mj; il_counter := next|> ==>
  inline_parameter_boundary (InlineEnter e) e.ise_callee l (SUC j)
    e.ise_final ml (SUC mj)
Proof
  strip_tac >>
  `SUC j <= LENGTH cb.bb_instructions` by gvs[get_instruction_def] >>
  drule_all inline_enter_boundary_produce >>
  drule_all inline_invoke_prefix_length_suc >>
  gvs[inline_choice_location_def, inline_cell_prefix_def]
QED

Theorem inline_residual_invoke_successor_path:
  !cert root p fn l j orig outcome.
    inline_call_incidence cert root p fn l j orig outcome ==>
    !C n loc inst k.
      inline_annotated_origin C n root cert /\
      outcome = InlineResidual loc inst /\ loc.il_phase = InlineAtInstruction k ==>
      ?path. inline_routed_leaf cert root p fn path /\
        inline_parameter_boundary_path path fn l (SUC j)
          root loc.il_block (SUC k)
Proof
  ho_match_mp_tac inline_call_incidence_strongind >> rpt conj_tac >> simp[]
  >- (rpt strip_tac >> qexists `[]` >>
      simp[inline_parameter_boundary_path_def, inline_routed_leaf_rules]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  drule inline_annotated_origin_edit_elim >> simp[] >> strip_tac >>
  `?i. loc.il_phase = InlineAtInstruction i` by
    metis_tac[inline_call_incidence_residual_phase] >>
  qpat_x_assum `!C n k. _`
    (qspecl_then [`C`, `e.ise_state.is_inline_count`, `i`] mp_tac) >>
  simp[] >> strip_tac >>
  drule_all inline_annotated_edit_fetch_facts >> strip_tac
  >- (qexists `path ++ [InlineKeep e]` >>
      conj_tac >- metis_tac[inline_routed_leaf_rules] >>
      irule inline_parameter_boundary_path_append >>
      goal_assum (drule_at Any) >>
      simp[inline_parameter_boundary_path_def] >>
      `?cb current. lookup_block loc.il_block e.ise_caller.fn_blocks = SOME cb /\
        get_instruction cb i = SOME current` by
        (drule inline_call_incidence_residual_fetch >>
         disch_then (qspecl_then [`C`, `e.ise_state.is_inline_count`, `loc`, `inst`] mp_tac) >>
         simp[inline_fetched_fields_def] >> metis_tac[]) >>
      `loc = <|il_block := loc.il_block; il_phase := InlineAtInstruction i;
        il_counter := loc.il_counter|>` by simp[inline_location_component_equality] >>
      `loc' = <|il_block := loc'.il_block; il_phase := InlineAtInstruction k;
        il_counter := loc'.il_counter|>` by simp[inline_location_component_equality] >>
      irule inline_keep_successor_boundary >> metis_tac[]) >>
  qexists `path ++ [InlineEnter e]` >>
  conj_tac >- metis_tac[inline_routed_leaf_rules] >>
  irule inline_parameter_boundary_path_append >> goal_assum (drule_at Any) >>
  simp[inline_parameter_boundary_path_def] >>
  `?cb current. lookup_block loc.il_block e.ise_callee.fn_blocks = SOME cb /\
    get_instruction cb i = SOME current /\ current.inst_opcode = INVOKE` by
    (drule inline_call_incidence_residual_fetch >>
     disch_then (qspecl_then [`C`, `e.ise_state.is_inline_count`, `loc`, `inst`] mp_tac) >>
     simp[inline_fetched_fields_def] >> strip_tac >> gvs[] >>
     `inst.inst_opcode = INVOKE` by metis_tac[inline_call_incidence_residual_phase] >>
     gvs[inline_inst_fields_def]) >>
  `MEM loc.il_block (fn_labels e.ise_callee)` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM,
      venomExecPropsTheory.lookup_block_label, fn_labels_def, MEM_MAP] >>
  `loc = <|il_block := loc.il_block; il_phase := InlineAtInstruction i;
    il_counter := loc.il_counter|>` by simp[inline_location_component_equality] >>
  `loc' = <|il_block := loc'.il_block; il_phase := InlineAtInstruction k;
    il_counter := loc'.il_counter|>` by simp[inline_location_component_equality] >>
  irule inline_enter_invoke_successor_boundary >> metis_tac[]
QED

Theorem inline_parameter_boundary_key[local]:
  inline_parameter_boundary (inline_choice_key c) fn l j root rl rj <=>
  inline_parameter_boundary c fn l j root rl rj
Proof
  Cases_on `c` >> simp[inline_choice_key_def, inline_parameter_boundary_def,
    inline_keep_boundary_def, inline_cell_prefix_def]
QED

Theorem inline_parameter_boundary_path_key[local]:
  !path fn l j root rl rj.
    inline_parameter_boundary_path (MAP inline_choice_key path) fn l j root rl rj <=>
    inline_parameter_boundary_path path fn l j root rl rj
Proof
  Induct >> simp[inline_parameter_boundary_path_def, inline_parameter_boundary_key]
QED

Theorem inline_parameter_boundary_path_keys[local]:
  MAP inline_choice_key path = MAP inline_choice_key path' /\
  inline_parameter_boundary_path path' fn l j root rl rj ==>
  inline_parameter_boundary_path path fn l j root rl rj
Proof
  metis_tac[inline_parameter_boundary_path_key]
QED

Theorem inline_selected_continuation_boundary:
  inline_annotated_origin C n root cert /\
  inline_call_incidence cert root p fn l j call (InlineSelected u q e zipper) /\
  inline_parameter_boundary_path zipper e.ise_final e.ise_return 0 root
    (inline_path_rename zipper e.ise_return) 0 ==>
  ?path. inline_routed_leaf cert root p fn path /\
    inline_parameter_boundary_path path fn l (SUC j) root
      (inline_path_rename zipper e.ise_return) 0
Proof
  strip_tac >> drule inline_selected_paired_separation >> simp[] >>
  disch_then drule >> strip_tac >>
  drule inline_residual_invoke_successor_path >>
  disch_then (qspecl_then [`C`, `e.ise_state.is_inline_count`, `src`, `current`,
    `e.ise_index`] mp_tac) >> simp[] >> strip_tac >>
  `MAP inline_choice_key path = MAP inline_choice_key path'` by
    metis_tac[inline_routed_leaf_key_unique] >>
  `inline_parameter_boundary_path path fn l (SUC j) e.ise_caller
     e.ise_block (SUC e.ise_index)` by
    metis_tac[inline_parameter_boundary_path_keys] >>
  qpat_x_assum `inline_parameter_boundary_path path' _ _ _ _ _ _` kall_tac >>
  qexists `path ++ [InlineKeep e] ++ zipper` >>
  conj_tac >- metis_tac[] >>
  irule inline_parameter_boundary_path_append >> goal_assum (drule_at Any) >>
  irule inline_parameter_boundary_path_append >>
  goal_assum (drule_at Any) >>
  simp[inline_parameter_boundary_path_def] >>
  irule inline_selected_site_successor_boundary >>
  metis_tac[inline_annotated_edit_fetch_facts]
QED

Theorem inline_live_stack_source_index:
  inline_live_stack C cert root ((p,a,route,snap)::rest) frame ==>
  inline_live_stack C cert root
    ((p,a,route,snap with ils_state := snap.ils_state with vs_inst_idx := i)::rest) frame
Proof
  strip_tac >> fs[inline_live_stack_def] >>
  `inline_owner_storage cert
     ((p,a,route,snap with ils_state := snap.ils_state with vs_inst_idx := i)::rest)
     (frame with ipf_state := frame.ipf_state with vs_inst_idx := frame.ipf_state.vs_inst_idx)` by
    (irule inline_owner_storage_index >> simp[]) >>
  gvs[inline_live_stack_def, inline_parameter_owners_cons,
    inline_shared_frame_def, inline_caller_residual_def,
    stateFrameTheory.execution_frame_def,
    fetch "venomState" "venom_state_component_equality",
    fetch "functionInlinerActivation" "inline_physical_frame_component_equality"] >>
  metis_tac[inline_parameter_saved_reads_head_replace]
QED
