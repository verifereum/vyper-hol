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
  functionInlinerParameterPropagation functionInlinerSelectedParameterReads
  functionInlinerParameterLineage functionInlinerParameterSavedReads
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

Theorem inline_entry_parameter_tail_coordinates[local]:
  inline_annotated_origin C n intermediate b /\
  (inline_entry_function b).fn_blocks = entry::rest /\
  entry.bb_instructions = params ++ tail /\ param_insts_from 0 params /\
  k < LENGTH params /\
  inline_annotated_choice_path C path intermediate root /\
  inline_parameter_boundary_path path intermediate entry.bb_label 0 root ml mj /\
  inline_cell_zipper
    (inline_make_cell intermediate entry.bb_label k (inline_inst_fields (EL k params)))
    frames out /\ MAP (\(tag,next). inline_cell_choice tag) frames = path ==>
  out.ic_function = root /\ out.ic_block = ml /\ out.ic_index = mj+k
Proof
  strip_tac >> drule inline_annotated_entry_parameter_prefix >>
  disch_then (qspecl_then [`entry`,`rest`,`params`,`tail`] mp_tac) >>
  simp[] >> strip_tac >>
  `inline_parameter_interval intermediate entry.bb_label 0 (LENGTH params)` by
    (simp[inline_parameter_interval_def] >>
     rpt strip_tac >> disj1_tac >>
     qspecl_then [`ps`,`0`,`k'`] mp_tac param_insts_from_el >>
     simp[param_inst_at_def, EL_APPEND_EQN]) >>
  drule_all inline_parameter_interval_transport >> simp[] >> strip_tac >>
  `ml' = ml /\ mj' = mj` by
    metis_tac[inline_parameter_boundary_path_functional] >>
  `inline_fetched_fields intermediate entry.bb_label k (inline_inst_fields (EL k params))` by
    (drule_all inline_parameter_prefix_fetch >>
     simp[inline_fetched_fields_def, get_instruction_def, EL_APPEND_EQN] >>
     metis_tac[EL_MAP]) >>
  qpat_x_assum `!k fields. _ ==> ?frames d. _` drule_all >>
  strip_tac >>
  `out.ic_function = d.ic_function /\ out.ic_block = d.ic_block /\
   out.ic_index = d.ic_index` by
    (irule inline_parameter_zipper_unique >>
     qpat_assum `inline_cell_zipper _ frames out` (irule_at Any) >>
     qpat_assum `inline_cell_zipper _ frames' d` (irule_at Any) >>
     simp[inline_make_cell_def] >>
     qpat_assum `inline_parameter_interval intermediate _ 0 _` (irule_at Any) >>
     qexistsl [`root`,`k`,`C`] >> simp[]) >> simp[]
QED

Theorem inline_selected_entry_token_transport[local]:
  inline_annotated_origin C n root cert /\
  inline_call_incidence cert root p fn l j orig (InlineSelected u q e zipper) /\
  inline_namespace_leaf_at cert q sigma child /\
  child.fn_blocks = entry::rest /\ entry.bb_instructions = params ++ tail /\
  param_insts_from 0 params /\ k < LENGTH params /\
  (EL k params).inst_opcode = RETPC_PARAM /\
  inline_parameter_boundary_path (InlineEnter e::zipper)
    e.ise_callee entry.bb_label 0 root ml mj ==>
  ?frames out.
    inline_cell_zipper
      (inline_make_cell child entry.bb_label k (inline_inst_fields (EL k params)))
      frames out /\
    inline_routed_leaf cert root q child
      (MAP (\(tag,next). inline_cell_choice tag) frames) /\
    EVERY (\(tag,next). !edit. tag <> SelectedJump edit) frames /\
    out.ic_function = root /\ inline_cell_at out /\
    out.ic_block = ml /\ out.ic_index = mj+k
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
  `inline_annotated_choice_path C (InlineEnter e::zipper) e.ise_callee root` by
    (drule inline_selected_paired_separation >> simp[] >> disch_then drule >>
     strip_tac >> simp[inline_annotated_choice_path_def] >>
     metis_tac[inline_selected_annotated_choice_path]) >>
  `out.ic_function = root /\ out.ic_block = ml /\ out.ic_index = mj+k` by
    (irule inline_entry_parameter_tail_coordinates >>
     qpat_assum `inline_cell_zipper _ suffix out` (irule_at Any) >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  qexistsl [`frames ++ suffix`,`out`] >>
  simp[inline_cell_zipper_append, MAP_APPEND, EVERY_APPEND] >>
  conj_tac >- metis_tac[] >>
  metis_tac[APPEND_ASSOC, APPEND]
QED

Theorem inline_selected_entry_token_storage[local]:
  inliner_input_ok C /\ inline_annotated_origin C n root cert /\
  inline_call_incidence cert root p fn l j orig (InlineSelected u q e zipper) /\
  inline_namespace_leaf_at cert q sigma child /\
  child.fn_blocks = entry::rest /\ entry.bb_instructions = params ++ tail /\
  param_insts_from 0 params /\ k < LENGTH params /\
  (EL k params).inst_opcode = RETPC_PARAM /\
  (EL k params).inst_operands = [Lit idx] /\
  (EL k params).inst_outputs = [x] /\ ca.ia_function = child /\
  inline_parameter_boundary_path (InlineEnter e::zipper)
    e.ise_callee entry.bb_label 0 root ml mj /\
  inline_parameter_ancestry C cert root
    (inline_parameter_owners ((q,ca,route,snap)::entries)) /\
  inline_parameter_saved_reads ((q,ca,route,snap)::entries) /\
  inline_owner_storage cert ((q,ca,route,snap)::entries) frame /\
  MEM x (cfgTransform$fn_all_vars child) /\ retpc_var child x ==>
  ?bb inst t.
    lookup_block ml root.fn_blocks = SOME bb /\
    get_instruction bb (mj+k) = SOME inst /\
    ~is_terminator inst.inst_opcode /\
    step_inst tfuel Tctx inst frame.ipf_state = OK t /\
    inline_owner_storage cert
      ((q,ca,route,snap with <|ils_state := update_var x
          snap.ils_state.vs_return_pc_token snap.ils_state;
        ils_defined := x INSERT snap.ils_defined|>)::entries)
      (frame with ipf_state := t) /\
    inline_parameter_saved_reads
      ((q,ca,route,snap with <|ils_state := update_var x
          snap.ils_state.vs_return_pc_token snap.ils_state;
        ils_defined := x INSERT snap.ils_defined|>)::entries)
Proof
  strip_tac >> drule_all inline_selected_entry_token_transport >> strip_tac >>
  `inline_namespace_leaf_at cert q route.ir_rename child` by
    (drule inline_owner_storage_member >> simp[] >> metis_tac[MEM]) >>
  `inline_path_rename (MAP (\(tag,next). inline_cell_choice tag) frames) =
    route.ir_rename` by
    (drule inline_routed_leaf_namespace >>
     simp[inline_namespace_leaf_at_def] >> strip_tac >>
     gvs[inline_namespace_leaf_at_def] >>
     metis_tac[inline_namespace_node_rename_unique]) >>
  `INJ route.ir_rename (x INSERT snap.ils_defined) UNIV` by
    (gvs[inline_namespace_leaf_at_def] >>
     drule inline_namespace_node_injective >>
     simp[INJ_DEF] >> metis_tac[]) >>
  `inline_cell_at (inline_make_cell child entry.bb_label k
    (inline_inst_fields (EL k params)))` by
    (simp[inline_cell_at_def, inline_make_cell_def, inline_fetched_fields_def] >>
     qexistsl [`entry`,`EL k params`] >>
     simp[lookup_block_def, FIND_thm, get_instruction_def, EL_APPEND_EQN]) >>
  `inline_cell_var_action frames x = route.ir_rename x` by
    simp[inline_cell_var_action_path] >>
  `(inline_make_cell child entry.bb_label k
    (inline_inst_fields (EL k params))).ic_fields = (RETPC_PARAM,[Lit idx],[x])` by
    simp[inline_make_cell_def, inline_inst_fields_def] >>
  gvs[] >>
  qpat_assum `inline_cell_zipper _ frames out`
    (mp_then (Pat `inline_cell_zipper c frames out`) mp_tac
      inline_token_fetched_storage) >>
  simp[] >> strip_tac >>
  `FST out.ic_fields = RETPC_PARAM \/ FST out.ic_fields = ASSIGN` by
    (drule functionInlinerTokenLineageTheory.inline_token_zipper_first_consumption >>
     simp[] >> strip_tac >- simp[] >>
     `EVERY (\(tag,next). !e. tag <> SelectedJump e) before /\
      EVERY (\(tag,next). !e. tag <> SelectedJump e) after` by
       gvs[EVERY_APPEND] >>
     drule_all inline_token_consumed_fields >> simp[]) >>
  gvs[inline_cell_at_def, inline_fetched_fields_def, inline_inst_fields_def] >>
  `inst.inst_opcode = RETPC_PARAM \/ inst.inst_opcode = ASSIGN` by
    metis_tac[pairTheory.FST] >>
  simp[is_terminator_def] >> metis_tac[]
QED

Theorem inline_entry_parameter_metadata[local]:
  inliner_input_ok C /\ MEM child C.ctx_functions /\
  child.fn_blocks = entry::rest /\ entry.bb_instructions = params ++ tail /\
  param_insts_from 0 params /\ k < LENGTH params /\
  (EL k params).inst_outputs = [x] ==>
  k < dimword (:256) /\ MEM x (cfgTransform$fn_all_vars child) /\
  (retpc_var child x <=> (EL k params).inst_opcode = RETPC_PARAM)
Proof
  strip_tac >>
  `LENGTH (fn_entry_insts child) < dimword (:256) /\ retpc_shape_ok child` by
    (fs[inliner_input_ok_def, EVERY_MEM] >> metis_tac[]) >>
  `MEM (EL k params) (fn_insts child)` by
    (simp[fn_insts_def, fn_insts_blocks_def] >> metis_tac[MEM_EL]) >>
  `is_param_opcode (EL k params).inst_opcode` by
    (drule_all param_insts_from_el >> simp[param_inst_at_def]) >>
  conj_tac >- (gvs[fn_entry_insts_def, entry_block_def] >> decide_tac) >>
  conj_tac
  >- (simp[cfgTransformTheory.fn_all_vars_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
      disj1_tac >> disj1_tac >> qexists `EL k params` >> simp[] >>
      metis_tac[MEM_EL]) >>
  eq_tac
  >- (strip_tac >> fs[retpc_shape_ok_def] >>
      qpat_x_assum `!inst x. MEM inst (fn_insts child) /\ MEM x inst.inst_outputs /\ _ ==> _`
        (qspecl_then [`EL k params`,`x`] mp_tac) >>
      gvs[is_param_opcode_iff]) >>
  strip_tac >> simp[retpc_var_def] >>
  irule copy_phi_var_seed >> qexists `EL k params` >> simp[]
QED

Theorem inline_selected_entry_ordinary_storage[local]:
  inline_annotated_origin C n root cert /\
  inline_call_incidence cert root p fn l j orig (InlineSelected u q e zipper) /\
  inline_namespace_leaf_at cert q sigma child /\
  child.fn_blocks = entry::rest /\ entry.bb_instructions = params ++ tail /\
  param_insts_from 0 params /\ k < LENGTH params /\
  inline_parameter_boundary_path (InlineEnter e::zipper)
    e.ise_callee entry.bb_label 0 root ml mj /\
  inline_owner_storage cert ((q,ca,route,snap)::entries) frame /\
  ca.ia_function = child /\ MEM (p,pa,proute,psnap) entries /\
  pa.ia_function = fn /\ orig.inst_operands = Label nm::ops /\
  eval_operands ops psnap.ils_state = SOME vals /\
  setup_callee child vals psnap.ils_state = SOME cs /\
  EVERY (\op. !v. op = Var v ==>
    MEM v (cfgTransform$fn_all_vars fn) /\ ~retpc_var fn v) ops /\
  k < LENGTH ops /\ snap.ils_state.vs_params = cs.vs_params /\
  MEM (EL k params).inst_opcode [PARAM; FMP_PARAM] /\
  (EL k params).inst_operands = [Lit idx] /\ w2n idx = k /\
  (EL k params).inst_outputs = [x] /\
  step_inst fuel C (EL k params) snap.ils_state = OK s' /\
  MEM x (cfgTransform$fn_all_vars child) /\ ~retpc_var child x /\
  INJ route.ir_rename (x INSERT snap.ils_defined) UNIV ==>
  ?bb inst t.
    lookup_block ml root.fn_blocks = SOME bb /\
    get_instruction bb (mj+k) = SOME inst /\ inst.inst_opcode = ASSIGN /\
    step_inst tfuel Tctx inst frame.ipf_state = OK t /\
    inline_owner_storage cert
      ((q,ca,route,snap with <|ils_state := s';
        ils_defined := x INSERT snap.ils_defined|>)::entries)
      (frame with ipf_state := t)
Proof
  strip_tac >>
  `k < LENGTH (rotate_invoke_ops orig.inst_operands)` by
    simp[functionInlinerDefsTheory.rotate_invoke_ops_def] >>
  drule_all inline_selected_parameter_descriptor_exists >> strip_tac >>
  `d.ic_block = ml /\ d.ic_index = mj+k` by
    (drule_all inline_selected_parameter_interval >> strip_tac >>
     `ml' = ml /\ mj' = mj` by
       metis_tac[inline_parameter_boundary_path_functional] >>
     metis_tac[]) >>
  drule inline_selected_parameter_descriptor_fetch >> strip_tac >>
  drule inline_selected_parameter_fetched_step >>
  simp[] >> disch_then drule_all >> strip_tac >> gvs[]
QED

(* One successful source parameter step constructs the physical step at its
   produced interval coordinate.  The archived caller may differ from the
   current suspended snapshot; saved_reads supplies precisely its reads. *)
Theorem inline_selected_parameter_ready_step:
  inliner_input_ok C /\ inline_annotated_origin C n root cert /\
  inline_call_incidence cert root p fn l j orig (InlineSelected u q e zipper) /\
  inline_namespace_leaf_at cert q sigma child /\ ca.ia_function = child /\
  child.fn_blocks = entry::rest /\ entry.bb_instructions = params ++ tail /\
  param_insts_from 0 params /\ k < LENGTH params /\
  inline_parameter_boundary_path (InlineEnter e::zipper)
    e.ise_callee entry.bb_label 0 root ml mj /\
  inline_original_child C cfuel pa.ia_id occurrence orig saved r ca cr /\
  pa.ia_function = fn /\
  inline_owner_storage cert
    ((q,ca,route,snap)::(p,pa,proute,psnap)::entries) frame /\
  inline_parameter_saved_reads
    ((q,ca,route,snap)::(p,pa,proute,psnap)::entries) /\
  inline_parameter_ancestry C cert root
    (inline_parameter_owners ((q,ca,route,snap)::(p,pa,proute,psnap)::entries)) /\
  snap.ils_state.vs_params = ca.ia_entry.vs_params /\
  snap.ils_state.vs_return_pc_token = ca.ia_entry.vs_return_pc_token /\
  snap.ils_state.vs_inst_idx = k /\ frame.ipf_state.vs_current_bb = ml /\
  frame.ipf_state.vs_inst_idx = mj+k /\
  step_inst fuel C (EL k params) snap.ils_state = OK s' ==>
  ?x bb inst t.
    (EL k params).inst_outputs = [x] /\
    lookup_block frame.ipf_state.vs_current_bb root.fn_blocks = SOME bb /\
    get_instruction bb frame.ipf_state.vs_inst_idx = SOME inst /\
    ~is_terminator inst.inst_opcode /\
    step_inst tfuel Tctx inst frame.ipf_state = OK t /\
    inline_owner_storage cert
      ((q,ca,route,snap with <|ils_state := s' with vs_inst_idx := SUC k;
        ils_defined := x INSERT snap.ils_defined|>)::(p,pa,proute,psnap)::entries)
      (frame with ipf_state := t with vs_inst_idx := mj+SUC k) /\
    inline_parameter_saved_reads
      ((q,ca,route,snap with <|ils_state := s' with vs_inst_idx := SUC k;
        ils_defined := x INSERT snap.ils_defined|>)::(p,pa,proute,psnap)::entries) /\
    inline_parameter_ancestry C cert root
      (inline_parameter_owners
        ((q,ca,route,snap with <|ils_state := s' with vs_inst_idx := SUC k;
          ils_defined := x INSERT snap.ils_defined|>)::(p,pa,proute,psnap)::entries)) /\
    s'.vs_params = snap.ils_state.vs_params /\
    s'.vs_return_pc_token = snap.ils_state.vs_return_pc_token
Proof
  strip_tac >>
  `?path. inline_routed_leaf cert root q child path` by
    metis_tac[inline_annotated_origin_routed_leaf] >>
  `MEM child C.ctx_functions` by metis_tac[inline_routed_leaf_source_member] >>
  `param_inst_at k (EL k params)` by
    (drule_all param_insts_from_el >> simp[]) >>
  `?x. (EL k params).inst_outputs = [x]` by
    (fs[param_inst_at_def] >> gvs[listTheory.LENGTH_EQ_NUM_compute]) >>
  drule_all inline_entry_parameter_metadata >> strip_tac >>
  drule_all inline_parameter_source_success >> strip_tac >>
  `x' = x` by gvs[] >> pop_assum SUBST_ALL_TAC >>
  `?bb inst t.
    lookup_block ml root.fn_blocks = SOME bb /\
    get_instruction bb (mj+k) = SOME inst /\
    ~is_terminator inst.inst_opcode /\
    step_inst tfuel Tctx inst frame.ipf_state = OK t /\
    inline_owner_storage cert
      ((q,ca,route,snap with <|ils_state := s';
        ils_defined := x INSERT snap.ils_defined|>)::(p,pa,proute,psnap)::entries)
      (frame with ipf_state := t)` by
    (Cases_on `(EL k params).inst_opcode = RETPC_PARAM`
     >- (fs[] >>
         drule_at (Pat `inline_call_incidence cert root p fn l j orig outcome`)
           inline_selected_entry_token_storage >>
         disch_then (drule_at (Pat `param_insts_from 0 params`)) >>
         disch_then (drule_at (Pat `inline_owner_storage cert entries frame`)) >>
         simp[] >> metis_tac[]) >>
     fs[] >>
     `?edge nm ops.
       ca.ia_parent = SOME edge /\ orig.inst_opcode = INVOKE /\
       decode_invoke orig = SOME (nm,ops) /\
       eval_operands ops saved = SOME edge.ipe_args /\
       setup_callee child edge.ipe_args saved = SOME ca.ia_entry` by
       metis_tac[inline_original_child_def] >>
     `orig.inst_operands = Label nm::ops` by
       gvs[decode_invoke_def, AllCaseEqs()] >>
     `inline_parameter_saved_pair (q,ca,route,snap) (p,pa,proute,psnap)` by
       fs[inline_parameter_saved_reads_def] >>
     `eval_operands ops psnap.ils_state = SOME edge.ipe_args` by
       (drule_all inline_parameter_saved_pair_operands >>
        disch_then (qspec_then `ops` mp_tac) >>
        fs[inline_original_child_def]) >>
     `?cs. setup_callee child edge.ipe_args psnap.ils_state = SOME cs` by
       simp[setup_callee_def] >>
     `snap.ils_state.vs_params = cs.vs_params /\ k < LENGTH ops` by
       (imp_res_tac setup_callee_frame >> drule_all eval_operands_length >>
        strip_tac >> gvs[]) >>
     drule inline_call_incidence_source >> strip_tac >>
     `MEM fn C.ctx_functions` by
       metis_tac[inline_annotated_origin_routed_leaf, inline_routed_leaf_source_member] >>
     `MEM orig (fn_insts fn)` by
       (gvs[get_instruction_def] >>
        metis_tac[EL_MEM, lookup_block_MEM, unitLabelMapIdentityTheory.fn_insts_MEM]) >>
     `EVERY (\op. !v. op = Var v ==>
       MEM v (cfgTransform$fn_all_vars fn) /\ ~retpc_var fn v) ops` by
       (irule inline_call_operand_namespace >> metis_tac[]) >>
     `inline_namespace_leaf_at cert q route.ir_rename child` by
       (drule inline_owner_storage_member >> simp[] >> metis_tac[MEM]) >>
     `INJ route.ir_rename (x INSERT snap.ils_defined) UNIV` by
       (gvs[inline_namespace_leaf_at_def] >>
        drule inline_namespace_node_injective >> simp[INJ_DEF] >> metis_tac[]) >>
     drule_at (Pat `inline_call_incidence cert root p fn l j orig outcome`)
       inline_selected_entry_ordinary_storage >>
     disch_then (drule_at (Pat `param_insts_from 0 params`)) >>
     disch_then (drule_at (Pat `inline_owner_storage cert entries frame`)) >>
     disch_then (drule_at (Pat `src.inst_operands = [Lit idx]`)) >>
     disch_then (drule_at (Pat `setup_callee child vals psnap.ils_state = SOME cs`)) >>
     simp[] >> strip_tac >>
     first_x_assum (drule_at (Pat `step_inst fuel C src s = OK s'`)) >>
     simp[] >> metis_tac[is_terminator_def]) >>
  `inline_parameter_saved_reads
    ((q,ca,route,snap with <|ils_state := s';
      ils_defined := x INSERT snap.ils_defined|>)::(p,pa,proute,psnap)::entries)` by
    (irule inline_parameter_saved_reads_head_replace >> goal_assum (drule_at Any)) >>
  drule_all inline_parameter_sequential_control >>
  disch_then (qspecl_then [`mj+SUC k`,`SUC k`] mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl [`inst`,`t`] >> simp[] >>
  Cases_on `(EL k params).inst_opcode = RETPC_PARAM` >>
  gvs[update_var_def]
QED
