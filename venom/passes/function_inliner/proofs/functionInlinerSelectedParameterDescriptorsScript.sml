(* Produced parameter adapters at a particular selected call incidence. *)
Theory functionInlinerSelectedParameterDescriptors
Ancestors
  functionInlinerPairedSelection functionInlinerParameterPropagation
  functionInlinerTokenLineage functionInlinerSelectedParameters
  functionInlinerEntryParameters functionInlinerParameterLineage
  functionInlinerOccurrences functionInlinerEnvelopes functionInlinerLocation
  functionInlinerReachableCuts functionInlinerRoutedProvenance
  functionInlinerDefs functionInlinerSiteLayout functionInlinerActivation
  callLayoutDefs venomInst list rich_list combin

Theorem inline_annotated_choice_path_append:
  !path fn mid rest root.
    inline_annotated_choice_path ctx path fn mid /\
    inline_annotated_choice_path ctx rest mid root ==>
    inline_annotated_choice_path ctx (path ++ rest) fn root
Proof
  Induct >> simp[inline_annotated_choice_path_def] >>
  rpt strip_tac >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem inline_selected_annotated_choice_path:
  !cert root p fn l j orig outcome.
    inline_call_incidence cert root p fn l j orig outcome ==>
    !ctx n u q e zipper.
      inline_annotated_origin ctx n root cert /\
      outcome = InlineSelected u q e zipper ==>
      inline_annotated_choice_path ctx zipper e.ise_final root
Proof
  ho_match_mp_tac inline_call_incidence_strongind >> rpt conj_tac >> simp[] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  drule inline_annotated_origin_edit_elim >> simp[] >> strip_tac
  >- simp[inline_annotated_choice_path_def] >>
  first_x_assum drule >> strip_tac >>
  irule inline_annotated_choice_path_append >> goal_assum (drule_at Any) >>
  simp[inline_annotated_choice_path_def] >> metis_tac[]
QED

Theorem inline_namespace_node_append:
  !cert p rho sub.
    inline_namespace_node_at cert p rho sub ==>
    !q sigma leaf. inline_namespace_node_at sub q sigma leaf ==>
      inline_namespace_node_at cert (p ++ q) (rho o sigma) leaf
Proof
  ho_match_mp_tac inline_namespace_node_at_ind >> rpt conj_tac >>
  rpt strip_tac >> simp[] >>
  metis_tac[inline_namespace_node_at_rules, combinTheory.o_ASSOC]
QED

Theorem inline_namespace_node_same_address:
  !cert p rho sub. inline_namespace_node_at cert p rho sub ==>
    !sigma other. inline_namespace_node_at cert p sigma other ==> other = sub
Proof
  ho_match_mp_tac inline_namespace_node_at_ind >> rpt conj_tac >>
  simp[inline_namespace_node_edit] >> rpt strip_tac >> gvs[]
  >- (Cases_on `cert` >> gvs[inline_namespace_node_edit]) >>
  metis_tac[]
QED

Theorem inline_selected_child_identity:
  !cert u rho e a b q sigma child.
  inline_namespace_node_at cert u (rho:string -> string)
    (InlineNamespaceEdit e.ise_state e.ise_caller e.ise_callee a b) /\
  q = u ++ [T] ++ inline_entry_address b /\
  inline_namespace_leaf_at cert q sigma child ==>
  child = inline_entry_function b
Proof
  rpt strip_tac >>
  `inline_namespace_node_at
     (InlineNamespaceEdit e.ise_state e.ise_caller e.ise_callee a b)
     (T::inline_entry_address b)
     (STRCAT (inline_prefix e.ise_state.is_inline_count) o I)
     (InlineNamespaceLeaf (inline_entry_function b))` by
    (simp[inline_namespace_node_edit, GSYM inline_namespace_leaf_at_def] >>
     qexists `I` >> simp[inline_entry_leaf]) >>
  drule_all inline_namespace_node_append >> strip_tac >>
  gvs[inline_namespace_leaf_at_def] >>
  rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  imp_res_tac inline_namespace_node_same_address >>
  qpat_x_assum `InlineNamespaceLeaf child = InlineNamespaceLeaf (inline_entry_function b)` mp_tac >>
  simp[NoAsms]
QED

Theorem inline_residual_rotated_length:
  inline_call_incidence cert root p fn l j orig (InlineResidual loc inst) /\
  inline_annotated_origin ctx n root cert ==>
  LENGTH (rotate_invoke_ops inst.inst_operands) =
  LENGTH (rotate_invoke_ops orig.inst_operands)
Proof
  strip_tac >>
  `?target args actual. orig.inst_operands = Label target::args /\
    inst.inst_operands = Label target::actual` by
    metis_tac[inline_call_incidence_residual_target] >>
  drule inline_call_incidence_residual_routing >> simp[] >> strip_tac >>
  `LENGTH inst.inst_operands = LENGTH orig.inst_operands` by
    metis_tac[inline_call_operand_fold_length] >>
  gvs[rotate_invoke_ops_def] >> (qpat_x_assum `Label target::actual = _` (mp_tac o AP_TERM ``LENGTH:operand list -> num``) >> simp[])
QED

Definition inline_selected_parameter_descriptor_def:
  inline_selected_parameter_descriptor ctx n cert root p fn l j orig
    u q e zipper child entry rest params tail k c mid frames d <=>
  ?a b oldp src current path bb cb ps post.
    inline_annotated_origin ctx n root cert /\
    inline_call_incidence cert root p fn l j orig (InlineSelected u q e zipper) /\
    inline_site_edit_valid e /\
    inline_annotated_origin ctx e.ise_state.is_inline_count e.ise_caller a /\
    inline_annotated_origin ctx e.ise_state.is_inline_count e.ise_callee b /\
    inline_call_incidence a e.ise_caller oldp fn l j orig
      (InlineResidual src current) /\
    src.il_block = e.ise_block /\ src.il_phase = InlineAtInstruction e.ise_index /\
    inline_namespace_node_at cert u (inline_path_rename zipper)
      (InlineNamespaceEdit e.ise_state e.ise_caller e.ise_callee a b) /\
    p = u ++ [F] ++ oldp /\ q = u ++ [T] ++ inline_entry_address b /\
    inline_routed_leaf a e.ise_caller oldp fn path /\
    inline_routed_leaf cert root p fn (path ++ [InlineKeep e] ++ zipper) /\
    child = inline_entry_function b /\ child.fn_blocks = entry::rest /\
    entry.bb_instructions = params ++ tail /\ param_insts_from 0 params /\
    k < LENGTH params /\
    lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
    k < LENGTH (rotate_invoke_ops (EL e.ise_index bb.bb_instructions).inst_operands) /\
    lookup_block entry.bb_label e.ise_callee.fn_blocks = SOME cb /\
    cb.bb_instructions = ps ++ post /\
    MAP inline_inst_fields ps = MAP inline_inst_fields params /\
    param_insts_from 0 ps /\
    c = inline_make_cell e.ise_callee entry.bb_label k
      (inline_inst_fields (EL k params)) /\
    inline_cell_frame (EnterCell e 0) c mid /\
    SND (inline_cell_prefix e bb cb k) = k /\
    mid.ic_fields =
      (ASSIGN, [EL k (rotate_invoke_ops
        (EL e.ise_index bb.bb_instructions).inst_operands)],
       MAP (STRCAT e.ise_prefix) (EL k params).inst_outputs) /\
    inline_cell_zipper mid frames d /\
    MAP (\(tag,next). inline_cell_choice tag) frames = zipper /\
    d.ic_function = root /\ inline_cell_at d /\
    d.ic_fields = (ASSIGN,
      FOLDL (\ops choice. case choice of
        InlineKeep e => ops
      | InlineEnter e => MAP (clone_operand e.ise_prefix (fn_labels e.ise_callee)) ops)
        (FST (SND mid.ic_fields)) zipper,
      MAP (inline_path_rename zipper) (SND (SND mid.ic_fields)))
End

Theorem inline_selected_parameter_descriptor_projection:
  inline_selected_parameter_descriptor ctx n cert root p fn l j orig
    u q e zipper child entry rest params tail k c mid frames d ==>
  inline_cell_frame (EnterCell e 0) c mid /\
  inline_cell_zipper mid frames d /\
  MAP (\(tag,next). inline_cell_choice tag) frames = zipper /\
  d.ic_function = root /\ inline_cell_at d /\ FST d.ic_fields = ASSIGN
Proof
  simp[inline_selected_parameter_descriptor_def] >> rpt strip_tac >> simp[]
QED

Theorem inline_selected_parameter_descriptor_fetch:
  inline_selected_parameter_descriptor ctx n cert root p fn l j orig
    u q e zipper child entry rest params tail k c mid frames d ==>
  ?bb inst. lookup_block d.ic_block root.fn_blocks = SOME bb /\
    get_instruction bb d.ic_index = SOME inst /\
    inst.inst_opcode = ASSIGN /\
    inst.inst_operands = FST (SND d.ic_fields) /\
    inst.inst_outputs = SND (SND d.ic_fields)
Proof
  strip_tac >> drule inline_selected_parameter_descriptor_projection >>
  simp[inline_cell_at_def, inline_fetched_fields_def, inline_inst_fields_def] >>
  rpt strip_tac >> qexistsl_tac [`bb`, `inst`] >> simp[] >>
  qpat_x_assum `(_,_,_) = d.ic_fields` (assume_tac o SYM) >> gvs[]
QED

Theorem inline_selected_parameter_descriptor_exists:
  inline_annotated_origin ctx n root cert /\
  inline_call_incidence cert root p fn l j orig (InlineSelected u q e zipper) /\
  inline_namespace_leaf_at cert q sigma child /\
  child.fn_blocks = entry::rest /\ entry.bb_instructions = params ++ tail /\
  param_insts_from 0 params /\ k < LENGTH params /\
  k < LENGTH (rotate_invoke_ops orig.inst_operands) ==>
  ?c mid frames d.
    inline_selected_parameter_descriptor ctx n cert root p fn l j orig
      u q e zipper child entry rest params tail k c mid frames d
Proof
  strip_tac >>
  drule inline_selected_paired_separation >> simp[] >>
  disch_then drule >> simp[] >> strip_tac >>
  `child = inline_entry_function b` by metis_tac[inline_selected_child_identity] >>
  drule_all inline_annotated_edit_fetch_facts >> strip_tac >>
  `inline_fetched_fields e.ise_caller e.ise_block e.ise_index
     (inline_inst_fields current)` by
    (drule inline_call_incidence_residual_fetch >> simp[] >>
     disch_then drule >> simp[]) >>
  `inline_inst_fields (EL e.ise_index bb.bb_instructions) = inline_inst_fields current` by
    gvs[inline_fetched_fields_def, get_instruction_def] >>
  `LENGTH (rotate_invoke_ops current.inst_operands) =
   LENGTH (rotate_invoke_ops orig.inst_operands)` by
    metis_tac[inline_residual_rotated_length] >>
  `k < LENGTH (rotate_invoke_ops
     (EL e.ise_index bb.bb_instructions).inst_operands)` by
    gvs[inline_inst_fields_def] >>
  `?cb ps post c mid.
    lookup_block entry.bb_label e.ise_callee.fn_blocks = SOME cb /\
    cb.bb_instructions = ps ++ post /\
    MAP inline_inst_fields ps = MAP inline_inst_fields params /\
    param_insts_from 0 ps /\
    c = inline_make_cell e.ise_callee entry.bb_label k
      (inline_inst_fields (EL k params)) /\
    inline_cell_frame (EnterCell e 0) c mid /\
    SND (inline_cell_prefix e bb cb k) = k /\
    mid.ic_fields = (ASSIGN, [EL k (rotate_invoke_ops
      (EL e.ise_index bb.bb_instructions).inst_operands)],
      MAP (STRCAT e.ise_prefix) (EL k params).inst_outputs)` by
    metis_tac[inline_entry_parameter_emits] >>
  `inline_annotated_choice_path ctx zipper mid.ic_function root` by
    (`mid.ic_function = e.ise_final` by
       (qpat_assum `inline_cell_frame (EnterCell e 0) c mid`
          (mp_tac o REWRITE_RULE [inline_cell_frame_def]) >>
        rpt strip_tac >> gvs[inline_make_cell_def]) >>
     simp[] >> metis_tac[inline_selected_annotated_choice_path]) >>
  `inline_cell_at mid` by metis_tac[inline_cell_frame_sound] >>
  drule_all inline_assign_path_produce >> strip_tac >>
  qexistsl_tac [`c`, `mid`, `frames`, `d`] >>
  simp[inline_selected_parameter_descriptor_def] >>
  metis_tac[]
QED

Theorem inline_token_keep_produce:
  inline_annotated_origin ctx e.ise_state.is_inline_count e.ise_caller a /\
  inline_annotated_origin ctx e.ise_state.is_inline_count e.ise_callee b /\
  inline_site_edit_valid e /\ c.ic_function = e.ise_caller /\
  inline_cell_at c /\ FST c.ic_fields = RETPC_PARAM ==>
  ?d. inline_cell_frame (KeepCell e) c d /\
    d.ic_function = e.ise_final /\ inline_cell_at d /\ FST d.ic_fields = RETPC_PARAM
Proof
  strip_tac >> drule_all inline_annotated_edit_fetch_facts >> strip_tac >>
  `?source. lookup_block e.ise_block e.ise_caller.fn_blocks = SOME source /\
    e.ise_index < LENGTH source.bb_instructions /\
    (EL e.ise_index source.bb_instructions).inst_opcode = INVOKE` by
    metis_tac [inline_site_edit_valid_def, functionInlinerWfTheory.find_invoke_site_lookup, inline_annotated_origin_labels] >>
  `c.ic_block <> e.ise_block \/ c.ic_index <> e.ise_index` by
    (gvs[inline_cell_at_def, inline_fetched_fields_def, get_instruction_def,
         inline_inst_fields_def] >> rpt strip_tac >> gvs[] >>
     `FST c.ic_fields = INVOKE` by metis_tac[pairTheory.FST] >> gvs[]) >>
  `?d. inline_cell_frame (KeepCell e) c d` by
    metis_tac[inline_keep_cell_produce] >>
  qexists `d` >> simp[] >>
  `inline_cell_at d /\ FST d.ic_fields = RETPC_PARAM` by
    metis_tac[inline_cell_frame_sound, inline_token_keep_survives] >> simp[] >>
  qpat_x_assum `inline_cell_frame _ _ _` mp_tac >>
  simp[inline_cell_frame_def] >> rpt strip_tac >> gvs[inline_make_cell_def]
QED

Theorem inline_token_enter_produce:
  inline_annotated_origin ctx e.ise_state.is_inline_count e.ise_caller a /\
  inline_annotated_origin ctx e.ise_state.is_inline_count e.ise_callee b /\
  inline_site_edit_valid e /\ c.ic_function = e.ise_callee /\
  inline_cell_at c /\ FST c.ic_fields = RETPC_PARAM ==>
  ?d. inline_cell_frame (EnterCell e 0) c d /\
    d.ic_function = e.ise_final /\ inline_cell_at d /\
    (FST d.ic_fields = RETPC_PARAM \/ FST d.ic_fields = ASSIGN)
Proof
  strip_tac >> drule_all inline_annotated_edit_fetch_facts >> strip_tac >>
  `?cb inst. lookup_block c.ic_block e.ise_callee.fn_blocks = SOME cb /\
    get_instruction cb c.ic_index = SOME inst /\
    inline_inst_fields inst = c.ic_fields` by
    metis_tac[inline_cell_at_def, inline_fetched_fields_def] >>
  `MEM c.ic_block (fn_labels e.ise_callee)` by
    (simp[fn_labels_def, MEM_MAP] >>
     metis_tac[venomExecPropsTheory.lookup_block_MEM,
               venomExecPropsTheory.lookup_block_label]) >>
  `inst.inst_opcode = RETPC_PARAM` by
    (gvs[inline_inst_fields_def] >> metis_tac[pairTheory.FST]) >>
  `0 < LENGTH (FST (inline_cell_focus e bb cb c.ic_index))` by
    (gvs[inline_cell_focus_def, get_instruction_def, inline_inst_fields_def,
         clone_instruction_def, rewrite_inline_inst_def, is_param_opcode_def] >>
     Cases_on `SND (inline_cell_prefix e bb cb c.ic_index) <
       LENGTH (rotate_invoke_ops (EL e.ise_index bb.bb_instructions).inst_operands)` >>
     simp[]) >>
  `?d. inline_cell_frame (EnterCell e 0) c d` by
    (irule inline_enter_cell_produce >> simp[] >> metis_tac[]) >>
  qexists `d` >> simp[] >>
  `inline_cell_at d` by metis_tac[inline_cell_frame_sound] >> simp[] >>
  `FST d.ic_fields = RETPC_PARAM \/ FST d.ic_fields = ASSIGN` by
    (drule_all inline_token_enter_cases >> rpt strip_tac >> simp[]) >> simp[] >>
  qpat_x_assum `inline_cell_frame _ _ _` mp_tac >>
  simp[inline_cell_frame_def] >> rpt strip_tac >> gvs[inline_make_cell_def]
QED

Theorem inline_token_or_assign_frame_produce:
  inline_annotated_origin ctx e.ise_state.is_inline_count e.ise_caller a /\
  inline_annotated_origin ctx e.ise_state.is_inline_count e.ise_callee b /\
  inline_site_edit_valid e /\ inline_cell_at c /\
  (FST c.ic_fields = RETPC_PARAM \/ FST c.ic_fields = ASSIGN) ==>
  (c.ic_function = e.ise_caller ==>
    ?d. inline_cell_frame (KeepCell e) c d /\
      d.ic_function = e.ise_final /\ inline_cell_at d /\
      (FST d.ic_fields = RETPC_PARAM \/ FST d.ic_fields = ASSIGN)) /\
  (c.ic_function = e.ise_callee ==>
    ?d. inline_cell_frame (EnterCell e 0) c d /\
      d.ic_function = e.ise_final /\ inline_cell_at d /\
      (FST d.ic_fields = RETPC_PARAM \/ FST d.ic_fields = ASSIGN))
Proof
  strip_tac
  >- metis_tac[inline_token_keep_produce, inline_token_enter_produce] >>
  `c.ic_fields = (ASSIGN,FST (SND c.ic_fields),SND (SND c.ic_fields))` by
    metis_tac[pairTheory.PAIR] >>
  metis_tac[inline_assign_keep_produce, inline_assign_enter_produce, pairTheory.FST]
QED

Theorem inline_token_path_produce:
  !path c root.
    inline_annotated_choice_path ctx path c.ic_function root /\
    inline_cell_at c /\
    (FST c.ic_fields = RETPC_PARAM \/ FST c.ic_fields = ASSIGN) ==>
    ?frames d.
      inline_cell_zipper c frames d /\
      MAP (\(tag,next). inline_cell_choice tag) frames = path /\
      EVERY (\(tag,next). !e. tag <> SelectedJump e) frames /\
      d.ic_function = root /\ inline_cell_at d /\
      (FST d.ic_fields = RETPC_PARAM \/ FST d.ic_fields = ASSIGN)
Proof
  Induct >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac assume_tac))
  >- (qexistsl_tac [`[]`, `c`] >>
      gvs[inline_annotated_choice_path_def, inline_cell_zipper_def]) >>
  qpat_x_assum `inline_annotated_choice_path _ _ _ _` mp_tac >>
  simp[inline_annotated_choice_path_def] >> strip_tac >> gnvs[]
  >- (drule_all inline_token_or_assign_frame_produce >> simp[] >> strip_tac >>
      first_x_assum (qspec_then `d` mp_tac) >> simp[] >>
      disch_then (qspec_then `root` mp_tac) >> simp[] >> strip_tac >>
      qexistsl_tac [`(KeepCell e,d)::frames`, `d'`] >>
      simp[inline_cell_zipper_def, inline_cell_choice_def]) >>
  drule_all inline_token_or_assign_frame_produce >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  first_x_assum (qspec_then `d` mp_tac) >> simp[] >>
  disch_then (qspec_then `root` mp_tac) >> simp[] >> strip_tac >>
  qexistsl_tac [`(EnterCell e 0,d)::frames`, `d'`] >>
  simp[inline_cell_zipper_def, inline_cell_choice_def]
QED

Theorem inline_selected_token_lineage:
  inline_call_incidence cert root p fn l j orig (InlineSelected u q e zipper) /\
  inline_annotated_origin ctx n root cert /\
  c.ic_function = e.ise_callee /\ inline_cell_at c /\
  FST c.ic_fields = RETPC_PARAM ==>
  ?frames d.
    inline_cell_zipper c frames d /\
    MAP (\(tag,next). inline_cell_choice tag) frames = InlineEnter e::zipper /\
    EVERY (\(tag,next). !edit. tag <> SelectedJump edit) frames /\
    d.ic_function = root /\ inline_cell_at d /\
    (FST d.ic_fields = RETPC_PARAM \/
     ?before consuming incoming next after.
       frames = before ++ [(EnterCell consuming 0,next)] ++ after /\
       inline_cell_zipper c before incoming /\
       FST incoming.ic_fields = RETPC_PARAM /\
       EVERY (\(tag,cell). FST cell.ic_fields = RETPC_PARAM) before /\
       inline_cell_frame (EnterCell consuming 0) incoming next /\
       inline_token_consumes consuming incoming next /\
       inline_cell_zipper next after d /\
       inline_cell_at incoming /\ inline_cell_at next)
Proof
  strip_tac >>
  drule inline_selected_paired_separation >> simp[] >>
  disch_then drule >> strip_tac >>
  `inline_annotated_choice_path ctx zipper e.ise_final root` by
    metis_tac[inline_selected_annotated_choice_path] >>
  `inline_annotated_choice_path ctx (InlineEnter e::zipper) c.ic_function root` by
    (simp[inline_annotated_choice_path_def] >> metis_tac[]) >>
  `?frames d. inline_cell_zipper c frames d /\
      MAP (\(tag,next). inline_cell_choice tag) frames = InlineEnter e::zipper /\
      EVERY (\(tag,next). !edit. tag <> SelectedJump edit) frames /\
      d.ic_function = root /\ inline_cell_at d` by
    metis_tac[inline_token_path_produce] >>
  qexistsl_tac [`frames`, `d`] >> simp[] >>
  metis_tac[inline_token_zipper_first_consumption]
QED
