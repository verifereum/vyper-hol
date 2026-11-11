(* Route representatives agree after erasing unused context fields. *)
Theory functionInlinerRouteKeys
Ancestors functionInlinerRoutedProvenance functionInlinerActivation list

Definition inline_edit_key_def:
  inline_edit_key e = e with <|ise_before := ARB; ise_after := ARB|>
End

Definition inline_choice_key_def:
  inline_choice_key (InlineKeep e) = InlineKeep (inline_edit_key e) /\
  inline_choice_key (InlineEnter e) = InlineEnter (inline_edit_key e)
End

Theorem inline_site_edit_key_unique:
  inline_site_edit_valid e /\ inline_site_edit_valid d /\
  e.ise_caller = d.ise_caller /\ e.ise_callee = d.ise_callee /\
  e.ise_state = d.ise_state ==> inline_edit_key e = inline_edit_key d
Proof
  simp[inline_site_edit_valid_def, inline_edit_key_def,
       inline_site_edit_component_equality] >>
  rpt strip_tac >> gvs[]
QED

Theorem inline_routed_leaf_key_unique:
  !cert root p fn path.
    inline_routed_leaf cert root p fn path ==>
    !root' fn' path'. inline_routed_leaf cert root' p fn' path' ==>
      MAP inline_choice_key path = MAP inline_choice_key path'
Proof
  ho_match_mp_tac inline_routed_leaf_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[Once inline_routed_leaf_cases]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `inline_routed_leaf (InlineNamespaceEdit _ _ _ _ _) _ _ _ _`
    (mp_tac o ONCE_REWRITE_RULE [inline_routed_leaf_cases]) >>
  strip_tac >> gvs[inline_choice_key_def] >>
  `inline_edit_key e = inline_edit_key e'` by
    (irule inline_site_edit_key_unique >> simp[]) >>
  simp[] >> first_x_assum irule >> goal_assum (drule_at Any)
QED

Theorem inline_edit_key_fields[simp]:
  (inline_edit_key e).ise_caller = e.ise_caller /\
  (inline_edit_key e).ise_callee = e.ise_callee /\
  (inline_edit_key e).ise_state = e.ise_state /\
  (inline_edit_key e).ise_final = e.ise_final /\
  (inline_edit_key e).ise_next = e.ise_next /\
  (inline_edit_key e).ise_block = e.ise_block /\
  (inline_edit_key e).ise_index = e.ise_index /\
  (inline_edit_key e).ise_prefix = e.ise_prefix /\
  (inline_edit_key e).ise_return = e.ise_return
Proof simp[inline_edit_key_def]
QED

Theorem inline_edit_key_valid[simp]:
  inline_site_edit_valid (inline_edit_key e) <=> inline_site_edit_valid e
Proof simp[inline_site_edit_valid_def]
QED

Theorem inline_choice_key_tags[simp]:
  (inline_choice_key (InlineKeep e) = InlineKeep d <=> inline_edit_key e = d) /\
  (inline_choice_key (InlineEnter e) = InlineEnter d <=> inline_edit_key e = d) /\
  inline_choice_key (InlineKeep e) <> InlineEnter d /\
  inline_choice_key (InlineEnter e) <> InlineKeep d
Proof simp[inline_choice_key_def]
QED

Theorem inline_choice_key_rename[simp]:
  inline_choice_rename (inline_choice_key c) = inline_choice_rename c
Proof Cases_on `c` >> simp[inline_choice_key_def, inline_choice_rename_def, FUN_EQ_THM]
QED

Theorem inline_path_key_rename[simp]:
  !path. inline_path_rename (MAP inline_choice_key path) = inline_path_rename path
Proof Induct >> simp[inline_path_rename_def]
QED

Theorem inline_path_keys_append:
  MAP inline_choice_key (prefix ++ suffix) =
    MAP inline_choice_key prefix ++ MAP inline_choice_key suffix
Proof simp[]
QED

Theorem inline_path_keys_suffix:
  MAP inline_choice_key (prefix ++ [c] ++ suffix) = keys ==>
  ?before after. keys = before ++ [inline_choice_key c] ++ after /\
    before = MAP inline_choice_key prefix /\
    after = MAP inline_choice_key suffix
Proof simp[]
QED
