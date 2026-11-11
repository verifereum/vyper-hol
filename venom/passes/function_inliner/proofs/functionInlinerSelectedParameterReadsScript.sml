(* Reads of produced ordinary parameter adapters use the suspended caller. *)
Theory functionInlinerSelectedParameterReads
Ancestors
  functionInlinerSelectedParameterDescriptors functionInlinerOperationalCuts
  functionInlinerParameterLineage functionInlinerStackSupports
  functionInlinerRoutedProvenance functionInlinerDefs venomExecProofs
  functionInlinerEnvelopes functionInlinerCuts venomExecSemantics
  functionInlinerOccurrences functionInlinerSiteLayout functionInlinerFrame
  functionInlinerActivation venomState venomInst list rich_list combin

Theorem inline_namespace_node_rename_unique:
  !cert p rho sub. inline_namespace_node_at cert p rho sub ==>
    !sigma other. inline_namespace_node_at cert p sigma other ==> rho = sigma
Proof
  ho_match_mp_tac inline_namespace_node_at_ind >> rpt conj_tac >>
  simp[inline_namespace_node_edit] >> rpt strip_tac >> gvs[]
  >- (Cases_on `cert` >> gvs[inline_namespace_node_edit]) >>
  metis_tac[]
QED

Theorem inline_owner_storage_member:
  inline_owner_storage cert entries frame /\ MEM (p,a,route,snap) entries ==>
  inline_tracked_snapshot a.ia_function a route snap frame /\
  inline_namespace_leaf_at cert p route.ir_rename a.ia_function
Proof
  simp[inline_owner_storage_def, inline_address_stack_def,
    inline_suspended_observations_def, inline_erase_addresses_def,
    EVERY_MAP, EVERY_MEM, inline_address_entry_def] >>
  rpt strip_tac
  >- (qpat_x_assum `!e. MEM e (MAP SND entries) ==> _`
        (qspec_then `(a,route,snap)` mp_tac) >>
      simp[MEM_MAP] >> metis_tac[pairTheory.SND]) >>
  qpat_x_assum `!e. MEM e entries ==> _`
    (qspec_then `(p,a,route,snap)` mp_tac) >>
  simp[inline_address_entry_def]
QED

Theorem inline_call_operand_fold_singleton:
  !path op lab. (!l. op <> Label l) ==>
  FOLDL (\ops choice. case choice of InlineKeep e => ops
    | InlineEnter e => MAP (clone_operand e.ise_prefix (fn_labels e.ise_callee)) ops)
    [op] path = [inline_rename_operand (inline_path_rename path) lab op]
Proof
  rpt strip_tac >> irule LIST_EQ >>
  simp[inline_call_operand_fold_length] >>
  qspec_then `path` (qspecl_then [`[op]`, `0`, `lab`] mp_tac)
    inline_call_operand_fold_value >> simp[]
QED

Theorem inline_selected_parameter_argument_read:
  inline_selected_parameter_descriptor ctx n cert root p fn l j orig
    u q e zipper child entry rest params tail k c mid frames d /\
  inline_owner_storage cert entries frame /\
  MEM (p,pa,proute,psnap) entries /\ pa.ia_function = fn /\
  orig.inst_operands = Label nm::ops /\
  eval_operands ops psnap.ils_state = SOME vals /\
  setup_callee child vals psnap.ils_state = SOME cs /\
  EVERY (\op. !v. op = Var v ==>
    MEM v (cfgTransform$fn_all_vars fn) /\ ~retpc_var fn v) ops /\
  k < LENGTH ops ==>
  eval_operands (FST (SND d.ic_fields)) frame.ipf_state =
    SOME [EL k cs.vs_params]
Proof
  strip_tac >> drule_all inline_owner_storage_member >> strip_tac >> gvs[] >>
  drule_all inline_tracked_call_argument_read >>
  disch_then (qspecl_then [`nm`, `I`] assume_tac) >>
  gvs[inline_selected_parameter_descriptor_def] >>
  `EVERY (\op. !name. op <> Label name) ops` by
    (`EVERY (\op. IS_SOME (eval_operand op psnap.ils_state)) ops` by
       simp[GSYM eval_operands_IS_SOME_EVERY] >>
     fs[inline_tracked_snapshot_def, EVERY_MEM] >>
     rpt strip_tac >> gvs[] >>
     qpat_x_assum `!op. MEM op ops ==> IS_SOME _`
       (qspec_then `Label name` mp_tac) >> simp[eval_operand_def]) >>
  `?actual. current.inst_operands = Label nm::actual` by
    (qpat_assum `inline_call_incidence a _ _ _ _ _ _ _`
       (mp_tac o MATCH_MP inline_call_incidence_residual_target) >>
     disch_then (qspecl_then [`ctx`, `e.ise_state.is_inline_count`, `src`, `current`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  `current.inst_operands = (EL e.ise_index bb.bb_instructions).inst_operands` by
    (drule inline_call_incidence_residual_fetch >>
     disch_then (qspecl_then [`ctx`, `e.ise_state.is_inline_count`, `src`, `current`] mp_tac) >>
     simp[inline_fetched_fields_def, inline_inst_fields_def, get_instruction_def] >>
     rpt strip_tac >> gvs[]) >>
  drule_all inline_selected_argument_lineage >> strip_tac >>
  `inline_path_rename path' = inline_path_rename path` by
    (imp_res_tac inline_routed_leaf_namespace >>
     gvs[inline_namespace_leaf_at_def] >>
     metis_tac[inline_namespace_node_rename_unique]) >>
  `proute.ir_rename = inline_path_rename
    (path ++ [InlineKeep e] ++ MAP (\(tag,next). inline_cell_choice tag) frames)` by
    (imp_res_tac inline_routed_leaf_namespace >>
     gvs[inline_namespace_leaf_at_def] >>
     metis_tac[inline_namespace_node_rename_unique]) >>
  first_x_assum (qspecl_then [`[]`, `k`, `I`] mp_tac) >>
  simp[inline_cell_var_action_path, inline_path_rename_append,
    inline_path_rename_def, inline_choice_rename_def, o_DEF] >>
  disch_tac >>
  `!name. EL k (rotate_invoke_ops current.inst_operands) <> Label name` by
    (Cases_on `EL k (rotate_invoke_ops current.inst_operands)` >>
     gvs[inline_rename_operand_def] >>
     `!name. EL k ops <> Label name` by gvs[EVERY_EL] >>
     Cases_on `EL k ops` >>
     gvs[rotate_invoke_ops_def, EL_APPEND_EQN, inline_rename_operand_def]) >>
  qpat_assum `current.inst_operands = (EL _ _).inst_operands`
    (fn th => rewrite_tac[GSYM th]) >>
  qspec_then `MAP (\(tag,next). inline_cell_choice tag) frames`
    (qspecl_then [`EL k (rotate_invoke_ops current.inst_operands)`, `I`] mp_tac)
    inline_call_operand_fold_singleton >>
  impl_tac >- simp[] >> disch_then SUBST1_TAC >>
  gvs[functionInlinerReachableCutsTheory.inline_cell_var_action_def,
    functionInlinerReachableCutsTheory.inline_cell_label_action_def,
    inline_path_rename_append, inline_path_rename_def, inline_choice_rename_def,
    inline_rename_operand_def, eval_operands_def, o_DEF] >>
  `!name. EL k ops <> Label name` by gvs[EVERY_EL] >>
  Cases_on `EL k ops` >>
  gvs[rotate_invoke_ops_def, EL_APPEND_EQN,
    functionInlinerReachableCutsTheory.inline_cell_var_action_def,
    functionInlinerReachableCutsTheory.inline_cell_label_action_def,
    inline_rename_operand_def] >>
  Cases_on `EL k actual` >>
  gvs[inline_rename_operand_def,
    functionInlinerReachableCutsTheory.inline_cell_var_action_def,
    functionInlinerReachableCutsTheory.inline_cell_label_action_def]
QED

Theorem inline_selected_parameter_output_rename:
  inline_selected_parameter_descriptor ctx n cert root p fn l j orig
    u q e zipper child entry rest params tail k c mid frames d /\
  inline_namespace_leaf_at cert q sigma child ==>
  SND (SND d.ic_fields) = MAP sigma (EL k params).inst_outputs
Proof
  strip_tac >> gvs[inline_selected_parameter_descriptor_def] >>
  `inline_namespace_node_at
    (InlineNamespaceEdit e.ise_state e.ise_caller e.ise_callee a b)
    (T::inline_entry_address b) (STRCAT e.ise_prefix o I)
    (InlineNamespaceLeaf (inline_entry_function b))` by
    (fs[inline_site_edit_valid_def] >>
     simp[inline_namespace_node_edit, GSYM inline_namespace_leaf_at_def] >>
     qexists `I` >> simp[inline_entry_leaf]) >>
  drule_all inline_namespace_node_append >> strip_tac >>
  gvs[inline_namespace_leaf_at_def] >>
  `sigma = inline_path_rename (MAP (\(tag,next). inline_cell_choice tag) frames) o
     (STRCAT e.ise_prefix o I)` by
    (irule inline_namespace_node_rename_unique >> metis_tac[APPEND_ASSOC, APPEND]) >>
  simp[MAP_MAP_o]
QED

Theorem inline_selected_parameter_fetched_step:
  inline_selected_parameter_descriptor ctx n cert root p fn l j orig
    u q e zipper child entry rest params tail k c mid frames d /\
  inline_owner_storage cert ((q,ca,route,snap)::entries) frame /\
  ca.ia_function = child /\ MEM (p,pa,proute,psnap) entries /\
  pa.ia_function = fn /\ orig.inst_operands = Label nm::ops /\
  eval_operands ops psnap.ils_state = SOME vals /\
  setup_callee child vals psnap.ils_state = SOME cs /\
  EVERY (\op. !v. op = Var v ==>
    MEM v (cfgTransform$fn_all_vars fn) /\ ~retpc_var fn v) ops /\
  k < LENGTH ops /\ snap.ils_state.vs_params = cs.vs_params /\
  src = EL k params /\ MEM src.inst_opcode [PARAM; FMP_PARAM] /\
  src.inst_operands = [Lit idx] /\ words$w2n idx = k /\
  src.inst_outputs = [x] /\ step_inst fuel C src snap.ils_state = OK s' /\
  MEM x (cfgTransform$fn_all_vars child) /\ ~retpc_var child x /\
  INJ route.ir_rename (x INSERT snap.ils_defined) UNIV ==>
  ?bb dst t.
    lookup_block d.ic_block root.fn_blocks = SOME bb /\
    get_instruction bb d.ic_index = SOME dst /\
    step_inst tfuel Tctx dst frame.ipf_state = OK t /\
    inline_owner_storage cert
      ((q,ca,route,snap with <|ils_state := s';
        ils_defined := x INSERT snap.ils_defined|>)::entries)
      (frame with ipf_state := t)
Proof
  strip_tac >>
  `eval_operands (FST (SND d.ic_fields)) frame.ipf_state =
     SOME [EL k cs.vs_params]` by
    (irule inline_selected_parameter_argument_read >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[MEM]) >>
  `inline_namespace_leaf_at cert q route.ir_rename child` by
    (drule inline_owner_storage_member >> simp[] >> metis_tac[MEM]) >>
  drule_all inline_selected_parameter_output_rename >> strip_tac >>
  drule inline_selected_parameter_descriptor_fetch >> strip_tac >>
  `s' = update_var x (EL k cs.vs_params) snap.ils_state` by
    (qpat_x_assum `step_inst fuel C src snap.ils_state = OK s'` mp_tac >>
     simp[Once step_inst_def] >>
     gvs[step_inst_base_def, AllCaseEqs()]) >>
  qexistsl_tac [`bb`, `inst`, `update_var (route.ir_rename x)
    (EL k cs.vs_params) frame.ipf_state`] >>
  simp[] >> conj_tac
  >- (qpat_x_assum `eval_operands _ frame.ipf_state = SOME _` mp_tac >>
      Cases_on `FST (SND d.ic_fields)` >>
      simp[eval_operands_def, AllCaseEqs()] >>
      Cases_on `t` >> simp[eval_operands_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      simp[Once step_inst_def, step_inst_base_def]) >>
  `inline_annotated_origin ctx n root cert` by
    gvs[inline_selected_parameter_descriptor_def] >>
  `INJ route.ir_rename (set (MAP FST [(x,EL k cs.vs_params)]) UNION
    snap.ils_defined) UNIV` by simp[pred_setTheory.INSERT_UNION_EQ] >>
  `EVERY (\(y,v). MEM y (cfgTransform$fn_all_vars ca.ia_function) /\
    ~retpc_var ca.ia_function y) [(x,EL k cs.vs_params)]` by simp[] >>
  drule_all inline_owner_storage_writes >> simp[pred_setTheory.INSERT_UNION_EQ]
QED

(* Source-only eligibility; target reads and storage are not part of it. *)
Definition inline_selected_parameter_source_step_def:
  inline_selected_parameter_source_step ctx n cert root p fn q child ca route
    entries pa proute psnap nm ops vals cs fuel C d snap next_snap <=>
  ?l j orig u e zipper entry rest params tail k c mid frames src idx x s'.
    inline_selected_parameter_descriptor ctx n cert root p fn l j orig
      u q e zipper child entry rest params tail k c mid frames d /\
    ca.ia_function = child /\ MEM (p,pa,proute,psnap) entries /\
    pa.ia_function = fn /\ orig.inst_operands = Label nm::ops /\
    eval_operands ops psnap.ils_state = SOME vals /\
    setup_callee child vals psnap.ils_state = SOME cs /\
    EVERY (\op. !v. op = Var v ==>
      MEM v (cfgTransform$fn_all_vars fn) /\ ~retpc_var fn v) ops /\
    k < LENGTH ops /\ snap.ils_state.vs_params = cs.vs_params /\
    src = EL k params /\ MEM src.inst_opcode [PARAM; FMP_PARAM] /\
    src.inst_operands = [Lit idx] /\ words$w2n idx = k /\
    src.inst_outputs = [x] /\ step_inst fuel C src snap.ils_state = OK s' /\
    MEM x (cfgTransform$fn_all_vars child) /\ ~retpc_var child x /\
    INJ route.ir_rename (x INSERT snap.ils_defined) UNIV /\
    next_snap = snap with <|ils_state := s'; ils_defined := x INSERT snap.ils_defined|>
End

Theorem inline_selected_parameter_source_step_storage:
  inline_owner_storage cert ((q,ca,route,snap)::entries) frame /\
  inline_selected_parameter_source_step ctx n cert root p fn q child ca route
    entries pa proute psnap nm ops vals cs fuel C d snap next_snap ==>
  ?bb dst t.
    lookup_block d.ic_block root.fn_blocks = SOME bb /\
    get_instruction bb d.ic_index = SOME dst /\
    step_inst tfuel Tctx dst frame.ipf_state = OK t /\
    inline_owner_storage cert ((q,ca,route,next_snap)::entries)
      (frame with ipf_state := t)
Proof
  simp[inline_selected_parameter_source_step_def] >> rpt strip_tac >>
  gvs[] >> irule inline_selected_parameter_fetched_step >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Definition inline_selected_parameter_source_steps_def:
  (inline_selected_parameter_source_steps ctx n cert root p fn q child ca route
    entries pa proute psnap nm ops vals cs fuel C [] snap final_snap <=>
    final_snap = snap) /\
  (inline_selected_parameter_source_steps ctx n cert root p fn q child ca route
    entries pa proute psnap nm ops vals cs fuel C (d::ds) snap final_snap <=>
    ?next_snap.
      inline_selected_parameter_source_step ctx n cert root p fn q child ca route
        entries pa proute psnap nm ops vals cs fuel C d snap next_snap /\
      inline_selected_parameter_source_steps ctx n cert root p fn q child ca route
        entries pa proute psnap nm ops vals cs fuel C ds next_snap final_snap)
End

(* This sequence records actual fetched steps, not adjacent-PC execution. *)
Definition inline_parameter_fetched_steps_def:
  (inline_parameter_fetched_steps tfuel Tctx root [] frame final_frame <=>
    final_frame = frame) /\
  (inline_parameter_fetched_steps tfuel Tctx root (d::ds) frame final_frame <=>
    ?bb dst t.
      lookup_block d.ic_block root.fn_blocks = SOME bb /\
      get_instruction bb d.ic_index = SOME dst /\
      step_inst tfuel Tctx dst frame.ipf_state = OK t /\
      inline_parameter_fetched_steps tfuel Tctx root ds
        (frame with ipf_state := t) final_frame)
End

Theorem inline_selected_parameter_prefix_storage:
  !cells snap frame final_snap.
  inline_owner_storage cert ((q,ca,route,snap)::entries) frame /\
  inline_selected_parameter_source_steps ctx n cert root p fn q child ca route
    entries pa proute psnap nm ops vals cs fuel C cells snap final_snap ==>
  ?final_frame.
    inline_parameter_fetched_steps tfuel Tctx root cells frame final_frame /\
    inline_owner_storage cert ((q,ca,route,final_snap)::entries) final_frame
Proof
  Induct >> simp[inline_selected_parameter_source_steps_def,
    inline_parameter_fetched_steps_def] >> rpt strip_tac >>
  drule_all inline_selected_parameter_source_step_storage >>
  disch_then (qspecl_then [`tfuel`, `Tctx`] strip_assume_tac) >>
  first_x_assum drule >> disch_then drule >> strip_tac >>
  goal_assum (drule_at Any) >> metis_tac[]
QED
