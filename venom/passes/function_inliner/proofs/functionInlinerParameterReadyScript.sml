(* Source-success eligibility and execution at produced parameter locations. *)
Theory functionInlinerParameterReady
Ancestors
  functionInlinerParameterLocations functionInlinerParameterTokenExecution
  functionInlinerParameterSequential functionInlinerParameterCorrespondence
  functionInlinerContract functionInlinerCuts functionInlinerEnvelopes
  functionInlinerEntryParameters functionInlinerOccurrences
  functionInlinerActivation functionInlinerReachableCuts functionInlinerLocation
  functionInlinerSiteLayout functionInlinerRoutedProvenance functionInlinerNamespace
  functionInlinerSelectedParameterDescriptors functionInlinerPairedSelection
  functionInlinerOperational venomExecProofs callLayoutDefs unitShapeDefs
  cfgTransformProps venomExecSemantics venomState venomInst words list pred_set

Theorem inline_parameter_source_success:
  param_inst_at k src /\ k < dimword (:256) /\
  step_inst fuel C src s = OK s' ==>
  ?x. src.inst_operands = [Lit (n2w k)] /\ src.inst_outputs = [x] /\
    ~is_terminator src.inst_opcode /\
    (if src.inst_opcode = RETPC_PARAM then
       s' = update_var x s.vs_return_pc_token s
     else MEM src.inst_opcode [PARAM; FMP_PARAM] /\
       k < LENGTH s.vs_params /\ s' = update_var x (EL k s.vs_params) s)
Proof
  simp[param_inst_at_def, is_param_opcode_def] >> rpt strip_tac >>
  Cases_on `src.inst_outputs` >> gvs[LENGTH_EQ_NUM_compute] >>
  gvs[is_param_opcode_iff] >> simp[is_terminator_def] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[Once step_inst_def, step_inst_base_def, AllCaseEqs()]
QED

Theorem inline_entry_parameter_keep[local]:
  inline_annotated_origin C e.ise_state.is_inline_count e.ise_caller a /\
  inline_annotated_origin C e.ise_state.is_inline_count e.ise_callee b /\
  inline_site_edit_valid e /\
  (inline_entry_function a).fn_blocks = entry::rest /\
  entry.bb_instructions = params ++ tail /\ param_insts_from 0 params /\
  k < LENGTH params ==>
  inline_cell_frame (KeepCell e)
    (inline_make_cell e.ise_caller entry.bb_label k (inline_inst_fields (EL k params)))
    (inline_make_cell e.ise_final entry.bb_label k (inline_inst_fields (EL k params)))
Proof
  strip_tac >>
  qpat_assum `inline_annotated_origin _ _ e.ise_caller a`
    (mp_then Any mp_tac inline_annotated_entry_parameter_prefix) >>
  disch_then (qspecl_then [`entry`,`rest`,`params`,`tail`] mp_tac) >>
  simp[] >> strip_tac >>
  drule_all inline_annotated_edit_fetch_facts >> strip_tac >>
  `ALL_DISTINCT (fn_labels e.ise_caller)` by
    metis_tac[inline_annotated_origin_labels] >>
  `(EL e.ise_index bb.bb_instructions).inst_opcode = INVOKE` by
    (gvs[inline_site_edit_valid_def] >>
     drule_all functionInlinerWfTheory.find_invoke_site_lookup >>
     strip_tac >> gvs[]) >>
  `LENGTH ps = LENGTH params` by metis_tac[LENGTH_MAP] >>
  `~(entry.bb_label = e.ise_block /\ e.ise_index <= k)` by
    (strip_tac >> gvs[] >>
     `e.ise_index < LENGTH ps` by decide_tac >>
     drule_all inline_parameter_prefix_no_invoke >> gvs[EL_APPEND_EQN]) >>
  `inline_inst_fields (EL k ps) = inline_inst_fields (EL k params)` by
    metis_tac[EL_MAP] >>
  `(EL k ps).inst_opcode <> PHI` by metis_tac[inline_parameter_prefix_no_invoke] >>
  simp[inline_cell_frame_def, inline_make_cell_def] >>
  qexists `EL k ps` >>
  simp[get_instruction_def, EL_APPEND_EQN, inline_edit_repair_def] >>
  Cases_on `entry.bb_label = e.ise_block` >> gvs[]
QED

Theorem inline_entry_parameter_cell_transport[local]:
  !C n intermediate b. inline_annotated_origin C n intermediate b ==>
  !entry rest params tail k.
    (inline_entry_function b).fn_blocks = entry::rest /\
    entry.bb_instructions = params ++ tail /\ param_insts_from 0 params /\
    k < LENGTH params ==>
    ?prefix frames.
      inline_routed_leaf b intermediate (inline_entry_address b)
        (inline_entry_function b) prefix /\
      EVERY (\choice. ?e. choice = InlineKeep e) prefix /\
      inline_cell_zipper
        (inline_make_cell (inline_entry_function b) entry.bb_label k
          (inline_inst_fields (EL k params))) frames
        (inline_make_cell intermediate entry.bb_label k (inline_inst_fields (EL k params))) /\
      MAP (\(tag,next). inline_cell_choice tag) frames = prefix /\
      EVERY (\(tag,next). !e. tag <> SelectedJump e) frames /\
      inline_cell_at
        (inline_make_cell intermediate entry.bb_label k (inline_inst_fields (EL k params)))
Proof
  ho_match_mp_tac inline_annotated_origin_strongind >> rpt conj_tac
  >- (rpt strip_tac >> qexistsl [`[]`,`[]`] >>
      simp[inline_entry_address_def, inline_entry_function_def,
           inline_routed_leaf_rules, inline_cell_at_def, inline_make_cell_def,
           inline_fetched_fields_def] >>
      qexistsl [`entry`,`EL k params`] >>
      gvs[inline_entry_function_def, lookup_block_def, FIND_thm,
          get_instruction_def, EL_APPEND_EQN])
  >- metis_tac[] >>
  map_every qx_gen_tac [`C`,`n`,`caller`,`callee`,`ist`,`result`,`ist'`,`a`,`b`] >>
  strip_tac >> rpt gen_tac >>
  simp[inline_entry_function_def, inline_entry_address_def] >> strip_tac >>
  qpat_x_assum `!entry rest params tail k. (inline_entry_function a).fn_blocks = _ /\ _ ==> _`
    (qspecl_then [`entry`,`rest`,`params`,`tail`,`k`] mp_tac) >>
  simp[] >> strip_tac >>
  drule inline_one_site_edit_exists >> strip_tac >>
  `inline_cell_frame (KeepCell e)
    (inline_make_cell caller entry.bb_label k (inline_inst_fields (EL k params)))
    (inline_make_cell result entry.bb_label k (inline_inst_fields (EL k params)))` by
    (gvs[] >> drule_all inline_entry_parameter_keep >> simp[]) >>
  qexists `frames ++ [(KeepCell e, inline_make_cell result entry.bb_label k
      (inline_inst_fields (EL k params)))]` >>
  simp[EVERY_APPEND, MAP_APPEND, inline_cell_choice_def, inline_cell_zipper_last] >>
  metis_tac[inline_routed_leaf_rules, inline_cell_frame_sound]
QED

Theorem inline_selected_entry_route_lift[local]:
  !cert root p fn l j orig outcome.
    inline_call_incidence cert root p fn l j orig outcome ==>
    !C n u q e zipper.
      inline_annotated_origin C n root cert /\
      outcome = InlineSelected u q e zipper ==>
      ?b. inline_annotated_origin C e.ise_state.is_inline_count e.ise_callee b /\
        !prefix. inline_routed_leaf b e.ise_callee (inline_entry_address b)
          (inline_entry_function b) prefix ==>
          inline_routed_leaf cert root q (inline_entry_function b)
            (prefix ++ [InlineEnter e] ++ zipper)
Proof
  ho_match_mp_tac inline_call_incidence_strongind >> rpt conj_tac >> simp[] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  drule inline_annotated_origin_edit_elim >> simp[] >> strip_tac
  >- (qexists `b` >> simp[] >> rpt strip_tac >>
      metis_tac[inline_routed_leaf_rules]) >>
  first_x_assum drule >> strip_tac >> goal_assum (drule_at Any) >> simp[] >>
  rpt strip_tac >> pure_rewrite_tac[APPEND_ASSOC] >>
  metis_tac[inline_routed_leaf_rules]
QED

Theorem inline_selected_entry_token_transport[local]:
  inline_annotated_origin C n root cert /\
  inline_call_incidence cert root p fn l j orig (InlineSelected u q e zipper) /\
  inline_namespace_leaf_at cert q sigma child /\
  child.fn_blocks = entry::rest /\ entry.bb_instructions = params ++ tail /\
  param_insts_from 0 params /\ k < LENGTH params /\
  (EL k params).inst_opcode = RETPC_PARAM ==>
  ?frames out.
    inline_cell_zipper
      (inline_make_cell child entry.bb_label k (inline_inst_fields (EL k params)))
      frames out /\
    inline_routed_leaf cert root q child
      (MAP (\(tag,next). inline_cell_choice tag) frames) /\
    EVERY (\(tag,next). !edit. tag <> SelectedJump edit) frames /\
    out.ic_function = root /\ inline_cell_at out
Proof
  strip_tac >> drule inline_selected_entry_route_lift >> simp[] >>
  disch_then drule >> strip_tac >>
  `child = inline_entry_function b` by
    (drule inline_annotated_entry_route >> strip_tac >>
     qpat_x_assum `!prefix. inline_routed_leaf b _ _ _ _ ==> _` drule >>
     strip_tac >> drule inline_routed_leaf_namespace >> strip_tac >>
     gvs[inline_namespace_leaf_at_def] >>
     imp_res_tac inline_namespace_node_same_address >>
     qpat_x_assum `InlineNamespaceLeaf child = InlineNamespaceLeaf (inline_entry_function b)` mp_tac >>
     simp[NoAsms]) >>
  `(inline_entry_function b).fn_blocks = entry::rest` by metis_tac[] >>
  qpat_assum `inline_annotated_origin _ _ e.ise_callee b`
    (mp_then Any mp_tac inline_entry_parameter_cell_transport) >>
  disch_then (qspecl_then [`entry`,`rest`,`params`,`tail`,`k`] mp_tac) >>
  simp[] >> strip_tac >>
  `?suffix out.
    inline_cell_zipper
      (inline_make_cell e.ise_callee entry.bb_label k (inline_inst_fields (EL k params)))
      suffix out /\
    MAP (\(tag,next). inline_cell_choice tag) suffix = InlineEnter e::zipper /\
    EVERY (\(tag,next). !edit. tag <> SelectedJump edit) suffix /\
    out.ic_function = root /\ inline_cell_at out` by
    (drule inline_selected_token_lineage >> simp[] >> disch_then drule >>
     disch_then (qspec_then
       `inline_make_cell e.ise_callee entry.bb_label k (inline_inst_fields (EL k params))`
       mp_tac) >>
     simp[inline_make_cell_def, inline_inst_fields_def] >> metis_tac[]) >>
  qexistsl [`frames ++ suffix`,`out`] >>
  simp[inline_cell_zipper_append, MAP_APPEND, EVERY_APPEND] >>
  conj_tac >- metis_tac[] >>
  metis_tac[APPEND_ASSOC, APPEND]
QED
