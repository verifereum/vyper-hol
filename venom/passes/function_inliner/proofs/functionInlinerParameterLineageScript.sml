(* Static operand lineage for parameter adapters, before any execution claim. *)
Theory functionInlinerParameterLineage
Ancestors
  functionInlinerReachableCuts functionInlinerOccurrences functionInlinerFrame
  functionInlinerDefs functionInlinerRoutedProvenance functionInlinerLocation
  functionInlinerActivation list rich_list combin

Theorem inline_cell_var_action_path:
  !frames v. inline_cell_var_action frames v =
    inline_path_rename (MAP (\(tag,next). inline_cell_choice tag) frames) v
Proof
  Induct >> simp[inline_cell_var_action_def, inline_path_rename_def] >>
  qx_gen_tac `h` >> PairCases_on `h` >> gen_tac >> Cases_on `h0` >>
  simp[inline_cell_var_action_def, inline_cell_choice_def,
    inline_path_rename_def, inline_choice_rename_def, o_DEF]
QED

(* Labels need their own conditional action.  Successful call arguments are
   values, so this boundary deliberately handles Var and Lit, not Label. *)
Theorem inline_call_operand_fold_value:
  !path ops k lab.
  k < LENGTH ops /\ (!l. EL k ops <> Label l) ==>
  EL k (FOLDL (\ops c. case c of
    InlineKeep e => ops
  | InlineEnter e => MAP (clone_operand e.ise_prefix (fn_labels e.ise_callee)) ops)
      ops path) = inline_rename_operand (inline_path_rename path) lab (EL k ops)
Proof
  Induct >> simp[inline_path_rename_def] >-
    (rpt strip_tac >> Cases_on `EL k ops` >> gvs[inline_rename_operand_def]) >>
  Cases_on `h` >> rpt strip_tac >> simp[FOLDL] >-
    (first_x_assum drule >>
     `inline_choice_rename (InlineKeep i) = I` by
       simp[FUN_EQ_THM, inline_choice_rename_def] >>
     simp[inline_path_rename_def]) >>
  first_x_assum (qspecl_then
    [`MAP (clone_operand i.ise_prefix (fn_labels i.ise_callee)) ops`, `k`, `lab`] mp_tac) >>
  simp[EL_MAP, inline_path_rename_def, inline_choice_rename_def, o_DEF] >>
  Cases_on `EL k ops` >> gvs[clone_operand_def, inline_rename_operand_def]
QED

Theorem inline_call_operand_fold_length:
  !path ops.
  LENGTH (FOLDL (\ops c. case c of
    InlineKeep e => ops
  | InlineEnter e => MAP (clone_operand e.ise_prefix (fn_labels e.ise_callee)) ops)
      ops path) = LENGTH ops
Proof
  Induct >> simp[] >> Cases_on `h` >> simp[]
QED

(* The route is computed from the original call's path followed by the
   later edit choices.  It is not assumed to be an identity or one prefix. *)
Theorem inline_selected_argument_lineage:
  inline_call_incidence cert root p fn l j orig (InlineResidual loc inst) /\
  orig.inst_operands = Label nm::ops /\
  inst.inst_operands = Label current_nm::actual /\
  EVERY (\op. !name. op <> Label name) ops ==>
  ?path. inline_routed_leaf cert root p fn path /\
    LENGTH actual = LENGTH ops /\
    !frames k lab. k <= LENGTH ops ==>
    inline_rename_operand (inline_cell_var_action frames)
      (inline_cell_label_action frames)
      (EL k (rotate_invoke_ops inst.inst_operands)) =
    inline_rename_operand
      (inline_path_rename (path ++ MAP (\(tag,next). inline_cell_choice tag) frames))
      lab (EL k (rotate_invoke_ops orig.inst_operands))
Proof
  strip_tac >> drule inline_call_incidence_residual_routing >> simp[] >> strip_tac >>
  `LENGTH actual = LENGTH ops` by
    (qpat_x_assum `Label current_nm::actual = _` (mp_tac o AP_TERM ``LENGTH:operand list -> num``) >>
     simp[inline_call_operand_fold_length]) >>
  qexists `path` >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  rpt strip_tac >>
  qpat_assum `inst.inst_operands = Label current_nm::actual`
    (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `orig.inst_operands = Label nm::ops`
    (fn th => pure_rewrite_tac[th]) >>
  Cases_on `k < LENGTH ops`
  >- (`!name. EL k ops <> Label name` by
        (gvs[EVERY_EL] >> metis_tac[]) >>
      `EL k actual = inline_rename_operand (inline_path_rename path) lab (EL k ops)` by
        (qspec_then `path` (qspecl_then [`orig.inst_operands`, `SUC k`, `lab`] mp_tac)
          inline_call_operand_fold_value >> simp[] >>
         qpat_assum `Label current_nm::actual = _`
           (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
      simp[rotate_invoke_ops_def, EL_APPEND_EQN] >>
      Cases_on `EL k ops` >> gvs[inline_rename_operand_def,
        inline_path_rename_append, o_DEF, inline_cell_var_action_path]) >>
  `k = LENGTH ops` by decide_tac >>
  simp[rotate_invoke_ops_def, EL_APPEND_EQN, inline_rename_operand_def]
QED

(* This is the unmodified canonical-prefix case only.  The count formula is
   explicit; a CURRENT prefix containing earlier replacements is not assumed
   to retain the original physical slot. *)
Theorem inline_canonical_first_parameter_slot:
  param_insts_from 0 params /\ cb.bb_instructions = params ++ tail /\
  j < LENGTH params /\ j < LENGTH args /\
  SND (inline_cell_prefix e bb cb j) = MIN j (LENGTH args) ==>
  SND (inline_cell_prefix e bb cb j) = j /\
  (clone_instruction e.ise_prefix (fn_labels e.ise_callee)
    (EL j cb.bb_instructions)).inst_operands = [Lit (n2w j)]
Proof
  strip_tac >> drule_all callLayoutDefsTheory.param_insts_from_el >>
  simp[callLayoutDefsTheory.param_inst_at_def] >> strip_tac >>
  simp[arithmeticTheory.MIN_DEF, EL_APPEND_EQN, clone_instruction_def, clone_operand_def]
QED

(* Selection remembers its residual call before the separating edit; later
   Keep/Enter choices act on the caller route too, not only on the child. *)
Theorem inline_selected_call_lineage:
  !cert root p fn l j orig outcome.
  inline_call_incidence cert root p fn l j orig outcome ==>
  !u q e zipper. outcome = InlineSelected u q e zipper ==>
  ?prior oldp src current path.
    inline_call_incidence prior e.ise_caller oldp fn l j orig
      (InlineResidual src current) /\
    src.il_block = e.ise_block /\ src.il_phase = InlineAtInstruction e.ise_index /\
    inline_routed_leaf prior e.ise_caller oldp fn path /\
    inline_routed_leaf cert root p fn (path ++ [InlineKeep e] ++ zipper)
Proof
  ho_match_mp_tac inline_call_incidence_strongind >> rpt conj_tac >> simp[]
  >- (rpt strip_tac >> drule inline_call_incidence_residual_routing >> simp[] >>
      strip_tac >>
      goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >>
      metis_tac[inline_routed_leaf_rules])
  >- (rpt strip_tac >>
      goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >>
      metis_tac[inline_routed_leaf_rules, APPEND_ASSOC]) >>
  rpt strip_tac >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >>
  metis_tac[inline_routed_leaf_rules, APPEND_ASSOC]
QED
