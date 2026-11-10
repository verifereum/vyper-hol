(* Static provenance only: addresses descend outward-in, paths run inward-out. *)
Theory functionInlinerRoutedProvenance
Ancestors
  functionInlinerActivation functionInlinerEnvelopes functionInlinerSiteLayout
  functionInlinerDefs list combin

Theorem inline_one_site_edit_exists:
  inline_one_site caller callee ist = SOME (final,next) ==>
  ?e. inline_site_edit_valid e /\
      e.ise_caller = caller /\ e.ise_callee = callee /\
      e.ise_state = ist /\ e.ise_final = final /\ e.ise_next = next /\
      e.ise_prefix = inline_prefix ist.is_inline_count
Proof
  strip_tac >>
  Cases_on `find_invoke_site callee.fn_name caller.fn_blocks`
  >- gvs[inline_one_site_def] >>
  PairCases_on `x` >>
  qexists `<|ise_before := ARB; ise_after := ARB;
    ise_caller := caller; ise_callee := callee; ise_state := ist;
    ise_final := final; ise_next := next; ise_block := x0; ise_index := x1;
    ise_prefix := inline_prefix ist.is_inline_count;
    ise_return := return_block_label (inline_prefix ist.is_inline_count)
                     ist.is_label_counter|>` >>
  simp[inline_site_edit_valid_def]
QED

Definition inline_path_rename_def:
  (inline_path_rename [] = (I:string -> string)) /\
  (inline_path_rename (c::cs) = inline_path_rename cs o inline_choice_rename c)
End

Theorem inline_path_rename_append:
  !p q. inline_path_rename (p ++ q) = inline_path_rename q o inline_path_rename p
Proof
  Induct >> simp[inline_path_rename_def, FUN_EQ_THM, o_DEF]
QED

Inductive inline_routed_leaf:
  (!fn. inline_routed_leaf (InlineNamespaceLeaf fn) fn [] fn []) /\
  (!ist caller callee a b e p fn path.
    inline_routed_leaf a caller p fn path /\ inline_site_edit_valid e /\
    e.ise_caller = caller /\ e.ise_callee = callee /\ e.ise_state = ist ==>
    inline_routed_leaf (InlineNamespaceEdit ist caller callee a b)
      e.ise_final (F::p) fn (path ++ [InlineKeep e])) /\
  (!ist caller callee a b e p fn path.
    inline_routed_leaf b callee p fn path /\ inline_site_edit_valid e /\
    e.ise_caller = caller /\ e.ise_callee = callee /\ e.ise_state = ist ==>
    inline_routed_leaf (InlineNamespaceEdit ist caller callee a b)
      e.ise_final (T::p) fn (path ++ [InlineEnter e]))
End

Theorem inline_routed_leaf_namespace:
  !cert root p fn path. inline_routed_leaf cert root p fn path ==>
    inline_namespace_leaf_at cert p (inline_path_rename path) fn
Proof
  ho_match_mp_tac inline_routed_leaf_ind >> rpt conj_tac >>
  rpt strip_tac >>
  gvs[inline_namespace_leaf_at_def, inline_path_rename_append,
      inline_path_rename_def, inline_choice_rename_def, o_DEF,
      inline_site_edit_valid_def] >>
  metis_tac[inline_namespace_node_at_rules]
QED

Theorem inline_annotated_origin_routed_leaf:
  !ctx n root cert. inline_annotated_origin ctx n root cert ==>
    !p (rho:string -> string) fn.
      inline_namespace_leaf_at cert p rho fn ==>
      ?path. inline_routed_leaf cert root p fn path /\
             inline_path_rename path = rho
Proof
  ho_match_mp_tac inline_annotated_origin_ind >> rpt conj_tac
  >- (simp[inline_namespace_leaf_at_def] >> rpt strip_tac >>
      qexists `[]` >> simp[inline_path_rename_def] >>
      metis_tac[inline_routed_leaf_rules])
  >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  drule inline_one_site_edit_exists >> strip_tac >>
  rpt gen_tac >>
  simp[inline_namespace_leaf_at_def, inline_namespace_node_edit] >>
  rpt strip_tac >> gvs[]
  >- (first_x_assum (drule o REWRITE_RULE [inline_namespace_leaf_at_def]) >>
      strip_tac >> qexists `path ++ [InlineKeep e]` >>
      conj_tac >- metis_tac[inline_routed_leaf_rules] >>
      simp[inline_path_rename_append, inline_path_rename_def,
           inline_choice_rename_def, o_DEF, FUN_EQ_THM]) >>
  first_x_assum (drule o REWRITE_RULE [inline_namespace_leaf_at_def]) >>
  strip_tac >> qexists `path ++ [InlineEnter e]` >>
  conj_tac >- metis_tac[inline_routed_leaf_rules] >>
  simp[inline_path_rename_append, inline_path_rename_def,
       inline_choice_rename_def, o_DEF]
QED

(* Consumers recover namespace and concrete edit validity without execution. *)
Theorem inline_routed_leaf_valid_choices:
  !cert root p fn path. inline_routed_leaf cert root p fn path ==>
    EVERY (\c. case c of InlineKeep e => inline_site_edit_valid e
                         | InlineEnter e => inline_site_edit_valid e) path
Proof
  ho_match_mp_tac inline_routed_leaf_ind >> rpt conj_tac >>
  simp[EVERY_APPEND]
QED

Theorem inline_routed_leaf_provenance:
  inline_routed_leaf cert root p fn path ==>
  inline_namespace_leaf_at cert p (inline_path_rename path) fn /\
  EVERY (\c. case c of InlineKeep e => inline_site_edit_valid e
                       | InlineEnter e => inline_site_edit_valid e) path
Proof
  metis_tac[inline_routed_leaf_namespace, inline_routed_leaf_valid_choices]
QED
