(* Coordinate witnesses retained by the selected return layout. *)
Theory functionInlinerReturnCoordinates
Ancestors
  functionInlinerReturnAdapterLayout functionInlinerReturnPrefix
  functionInlinerRouteKeys functionInlinerParameterReady
  functionInlinerReachableCuts functionInlinerActivation functionInlinerLocation
  functionInlinerSiteLayout functionInlinerParameterLocations
  functionInlinerParameterPropagation functionInlinerRoutedProvenance
  functionInlinerOccurrences functionInlinerDefs venomInst list

Theorem inline_path_key_location:
  !path loc. inline_path_location (MAP inline_choice_key path) loc =
    inline_path_location path loc
Proof
  Induct >> simp[inline_path_location_def] >> rpt gen_tac >>
  Cases_on `loc` >> Cases_on `h` >>
  simp[inline_location_step_def, inline_choice_key_def,
       inline_choice_location_def, GSYM inline_path_location_def]
QED

Theorem inline_adapter_choice_coordinates:
  inline_annotated_origin ctx e.ise_state.is_inline_count e.ise_caller a /\
  inline_annotated_origin ctx e.ise_state.is_inline_count e.ise_callee b /\
  inline_site_edit_valid e /\
  ((choice = InlineKeep e /\ fn = e.ise_caller) \/
   (choice = InlineEnter e /\ fn = e.ise_callee)) /\
  inline_adapter_interval fn l start assigns target /\
  inline_parameter_boundary choice fn l start e.ise_final ml mj ==>
  !counter. ?next.
    inline_choice_location choice
      <|il_block := l; il_phase := InlineAtInstruction start; il_counter := counter|> =
    SOME <|il_block := ml; il_phase := InlineAtInstruction mj; il_counter := next|>
Proof
  strip_tac >> drule_all inline_annotated_edit_fetch_facts >> strip_tac >>
  `(EL e.ise_index bb.bb_instructions).inst_opcode = INVOKE` by
    (`ALL_DISTINCT (fn_labels e.ise_caller)` by
       metis_tac[inline_annotated_origin_labels] >>
     gvs[inline_site_edit_valid_def] >>
     drule_all functionInlinerWfTheory.find_invoke_site_lookup >> gvs[]) >>
  gvs[]
  >- (`l = e.ise_block ==> start <> e.ise_index` by
        (strip_tac >>
         `!i. i < LENGTH assigns + 1 ==> start+i <> e.ise_index` by
           (gen_tac >> disch_tac >> irule inline_adapter_excludes_split >> metis_tac[]) >>
         first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
      gvs[inline_parameter_boundary_def, inline_keep_boundary_def] >>
      rpt strip_tac >> qexists `counter` >>
      simp[inline_choice_location_def] >> IF_CASES_TAC >> gvs[]) >>
  gvs[inline_parameter_boundary_def] >> rpt strip_tac >>
  qexists `SND (inline_cell_prefix e bb cb start)` >>
  simp[inline_choice_location_def, inline_cell_prefix_def]
QED

Theorem inline_adapter_path_coordinates:
  !path fn root l start assigns target ml mj.
  inline_annotated_choice_path ctx path fn root /\
  MEM target (fn_labels fn) /\
  inline_adapter_interval fn l start assigns target /\
  inline_parameter_boundary_path path fn l start root ml mj ==>
  !counter. ?next.
    inline_path_location path
      (SOME <|il_block := l; il_phase := InlineAtInstruction start; il_counter := counter|>) =
    SOME <|il_block := ml; il_phase := InlineAtInstruction mj; il_counter := next|>
Proof
  Induct >- simp[inline_annotated_choice_path_def,
    inline_parameter_boundary_path_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `inline_annotated_choice_path _ _ _ _` mp_tac >>
  simp[inline_annotated_choice_path_def] >> strip_tac >>
  `?il ij. inline_adapter_interval e.ise_final il ij
      (MAP (inline_adapter_choice_fields h) assigns) (inline_choice_rename h target) /\
    inline_parameter_boundary h fn l start e.ise_final il ij` by
    metis_tac[inline_adapter_choice_transport] >>
  `MEM (inline_choice_rename h target) (fn_labels e.ise_final)` by
    (drule_all inline_annotated_edit_fetch_facts >> strip_tac >>
     metis_tac[inline_adapter_choice_label]) >>
  `inline_parameter_boundary_path path e.ise_final il ij root ml mj` by
    (gvs[inline_parameter_boundary_path_def] >>
     metis_tac[inline_parameter_boundary_functional]) >>
  `!counter. ?next. inline_choice_location h
      <|il_block := l; il_phase := InlineAtInstruction start; il_counter := counter|> =
    SOME <|il_block := il; il_phase := InlineAtInstruction ij; il_counter := next|>` by
    (irule inline_adapter_choice_coordinates >> metis_tac[]) >>
  gen_tac >> first_x_assum (qspec_then `counter` strip_assume_tac) >>
  first_x_assum drule >> disch_then drule >> disch_then drule >>
  disch_then drule >> disch_then (qspec_then `next` strip_assume_tac) >>
  gvs[] >>
  pure_rewrite_tac[inline_path_location_def, FOLDL, inline_location_step_def] >>
  simp[GSYM inline_path_location_def] >> metis_tac[]
QED
