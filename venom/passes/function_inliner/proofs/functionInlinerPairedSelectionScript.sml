(* Separation witnesses are extracted together from one incidence derivation. *)
Theory functionInlinerPairedSelection
Ancestors
  functionInlinerParameterLineage functionInlinerOccurrences
  functionInlinerEnvelopes functionInlinerRoutedProvenance functionInlinerLocation
  functionInlinerActivation list combin

Theorem inline_selected_paired_separation:
  !cert root p fn l j orig outcome.
    inline_call_incidence cert root p fn l j orig outcome ==>
    !ctx n u q e zipper.
      inline_annotated_origin ctx n root cert /\
      outcome = InlineSelected u q e zipper ==>
      inline_site_edit_valid e /\
      ?a b oldp src current path.
        inline_annotated_origin ctx e.ise_state.is_inline_count e.ise_caller a /\
        inline_annotated_origin ctx e.ise_state.is_inline_count e.ise_callee b /\
        inline_call_incidence a e.ise_caller oldp fn l j orig
          (InlineResidual src current) /\
        src.il_block = e.ise_block /\
        src.il_phase = InlineAtInstruction e.ise_index /\
        inline_namespace_node_at cert u (inline_path_rename zipper)
          (InlineNamespaceEdit e.ise_state e.ise_caller e.ise_callee a b) /\
        p = u ++ [F] ++ oldp /\
        q = u ++ [T] ++ inline_entry_address b /\
        inline_routed_leaf a e.ise_caller oldp fn path /\
        inline_routed_leaf cert root p fn (path ++ [InlineKeep e] ++ zipper)
Proof
  ho_match_mp_tac inline_call_incidence_strongind >> rpt conj_tac >> simp[] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  drule inline_annotated_origin_edit_elim >> simp[] >> strip_tac
  >- (drule inline_call_incidence_residual_routing >> simp[] >> strip_tac >>
      qexistsl_tac [`cert`, `b`, `loc`, `inst`, `path`] >>
      simp[inline_path_rename_def, inline_namespace_node_at_rules] >>
      metis_tac[inline_routed_leaf_rules, inline_namespace_node_at_rules])
  >> first_x_assum drule >> strip_tac >> simp[] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  simp[inline_path_rename_append, inline_path_rename_def,
    inline_choice_rename_def, inline_namespace_node_edit, o_DEF, SF ETA_ss]
  >- (qexistsl_tac [`b'`, `current`] >> simp[] >>
      gvs[cj 2 inline_routed_leaf_rules, APPEND_ASSOC])
  >> qexistsl_tac [`b`, `current`] >> simp[] >>
  conj_tac
  >- (qexists `inline_path_rename zipper` >> simp[] >>
      fs[inline_site_edit_valid_def])
  >> gvs[cj 3 inline_routed_leaf_rules, APPEND_ASSOC]
QED
