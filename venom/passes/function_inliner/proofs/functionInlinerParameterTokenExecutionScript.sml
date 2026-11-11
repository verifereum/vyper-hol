(* Execution of opaque parameters uses syntax for survivors and archived
   caller reads for consumed tokens. *)
Theory functionInlinerParameterTokenExecution
Ancestors
  functionInlinerParameterTokenSurvival functionInlinerParameterTokenAlignment
  functionInlinerParameterSavedReads functionInlinerSelectedParameterReads
  functionInlinerOperationalCuts functionInlinerTokenLineage
  functionInlinerReachableCuts functionInlinerActivation
  functionInlinerParameterAncestry functionInlinerPairedSelection
  functionInlinerParameterLineage functionInlinerOccurrences functionInlinerDefs
  functionInlinerRoutedProvenance functionInlinerLocation
  functionInlinerCuts functionInlinerFrame venomExecProofs combin
  functionInlinerEnvelopes functionInlinerSiteLayout
  functionInlinerStackSupports venomState
  venomExecSemantics venomInst list

Theorem inline_token_survivor_storage:
  inline_owner_storage cert ((p,a,route,snap)::entries) frame /\
  inline_parameter_saved_reads ((p,a,route,snap)::entries) /\
  inline_annotated_origin C n root cert /\
  inline_cell_at c /\ inline_cell_zipper c frames d /\
  c.ic_fields = (RETPC_PARAM,[Lit idx],[x]) /\
  EVERY (\(tag,next). !e. tag <> SelectedJump e) frames /\
  FST d.ic_fields = RETPC_PARAM /\
  inline_cell_var_action frames x = route.ir_rename x /\
  MEM x (cfgTransform$fn_all_vars a.ia_function) /\ retpc_var a.ia_function x /\
  INJ route.ir_rename (x INSERT snap.ils_defined) UNIV ==>
  ?bb inst t.
    lookup_block d.ic_block d.ic_function.fn_blocks = SOME bb /\
    get_instruction bb d.ic_index = SOME inst /\
    step_inst tfuel Tctx inst frame.ipf_state = OK t /\
    inline_owner_storage cert
      ((p,a,route,snap with <|ils_state := update_var x
          snap.ils_state.vs_return_pc_token snap.ils_state;
        ils_defined := x INSERT snap.ils_defined|>)::entries)
      (frame with ipf_state := t) /\
    inline_parameter_saved_reads
      ((p,a,route,snap with <|ils_state := update_var x
          snap.ils_state.vs_return_pc_token snap.ils_state;
        ils_defined := x INSERT snap.ils_defined|>)::entries)
Proof
  strip_tac >> drule_all inline_token_zipper_survivor_step >>
  disch_then (qspecl_then [`frame.ipf_state`, `tfuel`, `Tctx`] strip_assume_tac) >>
  qexistsl_tac [`bb`, `inst`,
    `update_var (route.ir_rename x) frame.ipf_state.vs_return_pc_token frame.ipf_state`] >>
  simp[] >> conj_tac
  >- (irule inline_owner_storage_opaque_write >> metis_tac[]) >>
  irule inline_parameter_saved_reads_head_replace >> metis_tac[]
QED

Theorem inline_parameter_owners_adjacent_lift:
  inline_parameter_owners entries = younger ++ [(q,child);(p,pa)] ++ older ==>
  ?prefix croute csnap proute psnap rest.
    entries = prefix ++ (q,child,croute,csnap)::(p,pa,proute,psnap)::rest
Proof
  simp[inline_parameter_owners_def, MAP_EQ_APPEND, MAP_EQ_CONS,
       MAP_EQ_NIL, pairTheory.EXISTS_PROD] >> rpt strip_tac >>
  gvs[] >> metis_tac[APPEND_ASSOC]
QED

Theorem inline_token_consumption_live_alignment:
  inline_annotated_origin C n root cert /\
  inline_parameter_ancestry C cert root
    (inline_parameter_owners ((p,a,route,snap)::entries)) /\
  inline_parameter_saved_reads ((p,a,route,snap)::entries) /\
  inline_owner_storage cert ((p,a,route,snap)::entries) frame /\
  inline_routed_leaf cert root p a.ia_function path /\
  MAP inline_choice_key path =
    MAP inline_choice_key (MAP (\(tag,next). inline_cell_choice tag) frames) /\
  inline_cell_zipper c frames out /\
  frames = before ++ [(EnterCell consuming 0,next)] ++ after /\
  inline_token_consumes consuming incoming next ==>
  ?prefix q child pp pa rest fuel occurrence call saved r cr l j u e zipper parentpath
    proute psnap croute csnap.
    (p,a,route,snap)::entries =
      prefix ++ (q,child,croute,csnap)::(pp,pa,proute,psnap)::rest /\
    inline_original_child C fuel pa.ia_id occurrence call saved r child cr /\
    inline_call_incidence cert root pp pa.ia_function l j call
      (InlineSelected u q e zipper) /\
    inline_edit_key consuming = inline_edit_key e /\
    MAP inline_choice_key (MAP (\(tag,next). inline_cell_choice tag) after) =
      MAP inline_choice_key zipper /\
    inline_routed_leaf cert root pp pa.ia_function
      (parentpath ++ [InlineKeep e] ++ zipper) /\
    inline_tracked_snapshot pa.ia_function pa proute psnap frame /\
    (!op. eval_operand op saved = eval_operand op psnap.ils_state) /\
    (!ops. eval_operands ops saved = eval_operands ops psnap.ils_state)
Proof
  strip_tac >> drule_all inline_token_consumption_stored_alignment >> strip_tac >>
  `inline_parameter_owners ((p,a,route,snap)::entries) =
     younger ++ [(q,child);(pp,pa)] ++ older` by simp[] >>
  drule inline_parameter_owners_adjacent_lift >> strip_tac >>
  metis_tac[inline_parameter_saved_reads_live_parent]
QED

(* The current counter belongs to the consuming edit.  Include the appended
   literal return-PC argument as well as user arguments. *)
Theorem inline_selected_rotated_argument_read:
  inline_annotated_origin C n root cert /\
  inline_call_incidence cert root p fn l j orig (InlineSelected u q e zipper) /\
  inline_tracked_snapshot fn pa proute psnap frame /\
  inline_namespace_leaf_at cert p proute.ir_rename fn /\
  orig.inst_operands = Label nm::ops /\
  eval_operands ops psnap.ils_state = SOME vals /\
  setup_callee child vals psnap.ils_state = SOME cs /\
  EVERY (\op. !v. op = Var v ==>
    MEM v (cfgTransform$fn_all_vars fn) /\ ~retpc_var fn v) ops /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
  k < LENGTH (rotate_invoke_ops (EL e.ise_index bb.bb_instructions).inst_operands) ==>
  ?w. eval_operand
    (inline_rename_operand (inline_path_rename zipper) I
      (EL k (rotate_invoke_ops (EL e.ise_index bb.bb_instructions).inst_operands)))
    frame.ipf_state = SOME w
Proof
  strip_tac >>
  drule inline_selected_paired_separation >> simp[] >> disch_then drule >>
  simp[] >> strip_tac >>
  `EVERY (\op. !name. op <> Label name) ops` by
    (`EVERY (\op. IS_SOME (eval_operand op psnap.ils_state)) ops` by
       simp[GSYM eval_operands_IS_SOME_EVERY] >>
     fs[inline_tracked_snapshot_def, EVERY_MEM] >> rpt strip_tac >> gvs[] >>
     qpat_x_assum `!op. MEM op ops ==> IS_SOME _`
       (qspec_then `Label name` mp_tac) >> simp[eval_operand_def]) >>
  `?actual. current.inst_operands = Label nm::actual` by
    (drule inline_call_incidence_residual_target >>
     disch_then (qspecl_then [`C`, `e.ise_state.is_inline_count`, `src`, `current`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  `current.inst_operands = (EL e.ise_index bb.bb_instructions).inst_operands` by
    (drule inline_call_incidence_residual_fetch >>
     disch_then (qspecl_then [`C`, `e.ise_state.is_inline_count`, `src`, `current`] mp_tac) >>
     simp[inline_fetched_fields_def, inline_inst_fields_def, get_instruction_def] >>
     rpt strip_tac >> gvs[]) >>
  drule_all inline_selected_argument_lineage >> strip_tac >>
  `inline_path_rename path' = inline_path_rename path` by
    (imp_res_tac inline_routed_leaf_namespace >>
     gvs[inline_namespace_leaf_at_def] >>
     metis_tac[inline_namespace_node_rename_unique]) >>
  `proute.ir_rename = inline_path_rename (path ++ [InlineKeep e] ++ zipper)` by
    (imp_res_tac inline_routed_leaf_namespace >>
     gvs[inline_namespace_leaf_at_def] >>
     metis_tac[inline_namespace_node_rename_unique]) >>
  `k <= LENGTH ops` by gvs[rotate_invoke_ops_def] >>
  first_x_assum (qspecl_then [`[]`, `k`, `I`] mp_tac) >> simp[] >>
  simp[functionInlinerReachableCutsTheory.inline_cell_var_action_def,
    functionInlinerReachableCutsTheory.inline_cell_label_action_def] >>
  disch_tac >>
  Cases_on `k < LENGTH ops`
  >- (`!name. EL k ops <> Label name` by gvs[EVERY_EL] >>
      `eval_operand
         (inline_rename_operand proute.ir_rename I
           (EL k (rotate_invoke_ops (Label nm::ops)))) frame.ipf_state =
         SOME (EL k cs.vs_params)` by
        (irule inline_tracked_call_argument_read >> metis_tac[]) >>
      Cases_on `EL k ops` >>
      gvs[rotate_invoke_ops_def, EL_APPEND_EQN, inline_rename_operand_def,
        inline_path_rename_append, inline_path_rename_def,
        inline_choice_rename_def, o_DEF] >>
      Cases_on `EL k actual` >> gvs[inline_rename_operand_def,
        functionInlinerReachableCutsTheory.inline_cell_var_action_def,
        functionInlinerReachableCutsTheory.inline_cell_label_action_def]) >>
  `k = LENGTH ops` by decide_tac >>
  gvs[rotate_invoke_ops_def, EL_APPEND_EQN, inline_rename_operand_def,
      eval_operand_def]
QED

Theorem inline_token_archived_argument_read:
  inliner_input_ok C /\ inline_annotated_origin C n root cert /\
  inline_call_incidence cert root p pa.ia_function l j call
    (InlineSelected u q e zipper) /\
  inline_routed_leaf cert root p pa.ia_function path /\
  inline_original_child C fuel pa.ia_id occurrence call saved r child cr /\
  inline_parameter_saved_reads
    (prefix ++ (q,child,croute,csnap)::(p,pa,proute,psnap)::rest) /\
  inline_owner_storage cert
    (prefix ++ (q,child,croute,csnap)::(p,pa,proute,psnap)::rest) frame /\
  inline_edit_key consuming = inline_edit_key e /\
  MAP inline_choice_key (MAP (\(tag,next). inline_cell_choice tag) after) =
    MAP inline_choice_key zipper /\
  lookup_block consuming.ise_block consuming.ise_caller.fn_blocks = SOME bb /\
  k < LENGTH (rotate_invoke_ops
    (EL consuming.ise_index bb.bb_instructions).inst_operands) ==>
  ?w. eval_operand
    (inline_rename_operand (inline_cell_var_action after)
      (inline_cell_label_action after)
      (EL k (rotate_invoke_ops
        (EL consuming.ise_index bb.bb_instructions).inst_operands)))
    frame.ipf_state = SOME w
Proof
  strip_tac >> drule_all inline_parameter_saved_reads_live_parent >> strip_tac >>
  `inline_namespace_leaf_at cert p proute.ir_rename pa.ia_function` by
    (drule functionInlinerSelectedParameterReadsTheory.inline_owner_storage_member >>
     simp[]) >>
  `MEM pa.ia_function C.ctx_functions` by
    metis_tac[inline_routed_leaf_source_member] >>
  `MEM call (fn_insts pa.ia_function)` by
    (drule inline_call_incidence_source >> strip_tac >>
     gvs[get_instruction_def] >>
     metis_tac[EL_MEM, lookup_block_MEM, unitLabelMapIdentityTheory.fn_insts_MEM]) >>
  `?edge nm ops. call.inst_opcode = INVOKE /\
     decode_invoke call = SOME (nm,ops) /\
     eval_operands ops saved = SOME edge.ipe_args /\
     setup_callee child.ia_function edge.ipe_args saved = SOME child.ia_entry` by
    metis_tac[inline_original_child_def] >>
  `call.inst_operands = Label nm::ops` by
    gvs[decode_invoke_def, AllCaseEqs()] >>
  `EVERY (\op. !v. op = Var v ==>
      MEM v (cfgTransform$fn_all_vars pa.ia_function) /\
      ~retpc_var pa.ia_function v) ops` by
    (irule inline_call_operand_namespace >> metis_tac[]) >>
  `?cs. setup_callee child.ia_function edge.ipe_args psnap.ils_state = SOME cs` by
    (gvs[setup_callee_def] >> metis_tac[]) >>
  drule inline_edit_key_equal_projections >> strip_tac >>
  `inline_cell_var_action after = inline_path_rename zipper` by
    (simp[inline_cell_var_action_path, FUN_EQ_THM] >>
     metis_tac[inline_path_keys_equal_rename]) >>
  `?w. eval_operand
    (inline_rename_operand (inline_path_rename zipper) I
      (EL k (rotate_invoke_ops (EL e.ise_index bb.bb_instructions).inst_operands)))
    frame.ipf_state = SOME w` by
    (irule inline_selected_rotated_argument_read >> metis_tac[]) >>
  `frame.ipf_state.vs_labels = FEMPTY` by
    (fs[inline_tracked_snapshot_def] >>
     metis_tac[inline_snapshot_anchor_empty_labels]) >>
  Cases_on `EL k (rotate_invoke_ops (EL e.ise_index bb.bb_instructions).inst_operands)` >>
  gvs[inline_rename_operand_def, eval_operand_def]
QED

Theorem inline_token_consumption_operand_read:
  inliner_input_ok C /\ inline_annotated_origin C n root cert /\
  inline_parameter_ancestry C cert root
    (inline_parameter_owners ((p,a,route,snap)::entries)) /\
  inline_parameter_saved_reads ((p,a,route,snap)::entries) /\
  inline_owner_storage cert ((p,a,route,snap)::entries) frame /\
  inline_routed_leaf cert root p a.ia_function path /\
  MAP inline_choice_key path =
    MAP inline_choice_key (MAP (\(tag,next). inline_cell_choice tag) frames) /\
  inline_cell_zipper c frames out /\
  frames = before ++ [(EnterCell consuming 0,next)] ++ after /\
  inline_token_consumes consuming incoming next ==>
  ?w. eval_operands
    (MAP (inline_rename_operand (inline_cell_var_action after)
      (inline_cell_label_action after)) (FST (SND next.ic_fields)))
    frame.ipf_state = SOME [w]
Proof
  strip_tac >> drule_all inline_token_consumption_live_alignment >> strip_tac >>
  gvs[inline_token_consumes_def] >>
  simp[eval_operands_def, AllCaseEqs()] >>
  irule inline_token_archived_argument_read >> metis_tac[]
QED
