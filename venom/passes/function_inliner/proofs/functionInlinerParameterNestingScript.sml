(* Concrete root and selected-push route probes.  Syntactic layout paths are
   deliberately separate from the routes used for owner storage. *)
Theory functionInlinerParameterNesting
Ancestors
  functionInlinerParameterAncestors functionInlinerPairedSelection
  functionInlinerSelectedParameterDescriptors functionInlinerOccurrences
  functionInlinerRoutedProvenance functionInlinerOperationalCuts
  functionInlinerActivation functionInlinerEnvelopes functionInlinerTokenLineage list combin

Theorem inline_parameter_nesting_root:
  inline_annotated_origin C n root cert /\
  a.ia_function = inline_entry_function cert /\
  a.ia_entry.vs_labels = FEMPTY ==>
  ?path snap frame.
    inline_routed_leaf cert root (inline_entry_address cert) a.ia_function path /\
    EVERY (\c. ?e. c = InlineKeep e) path /\
    inline_path_rename path = I /\
    inline_owner_storage cert
      [(inline_entry_address cert,a,inline_route_identity a.ia_id,snap)] frame /\
    snap.ils_state = a.ia_entry /\ frame.ipf_state = a.ia_entry
Proof
  strip_tac >> drule inline_annotated_entry_route >> strip_tac >>
  `inline_namespace_leaf_at cert (inline_entry_address cert) I a.ia_function` by
    metis_tac[inline_entry_leaf] >>
  drule_all inline_owner_storage_root >> strip_tac >>
  metis_tac[]
QED

Theorem inline_selected_entry_route_pair:
  !cert root p fn l j orig outcome.
    inline_call_incidence cert root p fn l j orig outcome ==>
    !C n u q e zipper.
      inline_annotated_origin C n root cert /\
      outcome = InlineSelected u q e zipper ==>
      ?child path prefix.
        inline_namespace_leaf_at cert q
          (inline_path_rename (prefix ++ [InlineEnter e] ++ zipper)) child /\
        inline_routed_leaf cert root q child
          (prefix ++ [InlineEnter e] ++ zipper) /\
        EVERY (\c. ?d. c = InlineKeep d) prefix /\
        inline_routed_leaf cert root p fn (path ++ [InlineKeep e] ++ zipper)
Proof
  ho_match_mp_tac inline_call_incidence_strongind >> rpt conj_tac >> simp[] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  drule inline_annotated_origin_edit_elim >> simp[] >> strip_tac
  >- (drule inline_annotated_entry_route >> strip_tac >>
      drule inline_call_incidence_residual_routing >> simp[] >> strip_tac >>
      qexistsl_tac [`inline_entry_function b`, `path'`, `path`] >>
      `inline_routed_leaf
        (InlineNamespaceEdit e.ise_state e.ise_caller e.ise_callee cert b)
        e.ise_final (T::inline_entry_address b) (inline_entry_function b)
        (path ++ [InlineEnter e])` by
        metis_tac[inline_routed_leaf_rules] >>
      metis_tac[inline_routed_leaf_namespace, inline_routed_leaf_rules])
  >> first_x_assum drule >> strip_tac >>
  qexistsl_tac [`child`, `path`, `prefix`] >>
  pure_rewrite_tac[APPEND_ASSOC] >>
  rpt conj_tac >>
  metis_tac[inline_routed_leaf_rules, inline_routed_leaf_namespace]
QED

(* A produced push has paired syntactic routes and an actual suspended caller.
   No equality with the storage route's ir_path is needed or claimed. *)
Theorem inline_parameter_nesting_push:
  inline_annotated_origin C n root cert /\
  inline_owner_storage cert ((p,pa,proute,psnap)::rest) frame /\
  inline_original_child C fuel pa.ia_id occurrence call psnap.ils_state r child cr /\
  inline_call_incidence cert root p pa.ia_function l j call
    (InlineSelected u q e zipper) /\
  inline_namespace_leaf_at cert q route.ir_rename child.ia_function ==>
  ?prefix path csnap edge.
    inline_routed_leaf cert root q child.ia_function
      (prefix ++ [InlineEnter e] ++ zipper) /\
    EVERY (\c. ?d. c = InlineKeep d) prefix /\
    inline_routed_leaf cert root p pa.ia_function
      (path ++ [InlineKeep e] ++ zipper) /\
    inline_owner_storage cert
      ((q,child,route,csnap)::(p,pa,proute,psnap)::rest) frame /\
    child.ia_parent = SOME edge /\ edge.ipe_parent = pa.ia_id /\
    edge.ipe_call = call /\ edge.ipe_saved = psnap.ils_state /\
    edge.ipe_child = child.ia_entry /\
    inline_tracked_snapshot pa.ia_function pa proute psnap frame
Proof
  strip_tac >>
  drule inline_selected_entry_route_pair >>
  disch_then (qspecl_then [`C`, `n`, `u`, `q`, `e`, `zipper`] mp_tac) >>
  simp[] >> strip_tac >>
  `child' = child.ia_function` by
    (fs[inline_namespace_leaf_at_def] >>
     qpat_x_assum `inline_namespace_node_at cert q route.ir_rename _`
       (mp_tac o MATCH_MP inline_namespace_node_same_address) >>
     disch_then (qspecl_then
       [`inline_path_rename (prefix ++ [InlineEnter e] ++ zipper)`,
        `InlineNamespaceLeaf child'`] mp_tac) >> simp[]) >>
  drule_all inline_selected_child_stored_parent >> strip_tac >>
  metis_tac[]
QED

(* The newly introduced Enter is supported by the actual saved caller, even
   when the incoming token counter h differs from its original slot. *)
Theorem inline_parameter_nesting_push_enter:
  inline_annotated_origin C n root cert /\
  inline_owner_storage cert ((p,pa,proute,psnap)::rest) frame /\
  inline_original_child C fuel pa.ia_id occurrence call psnap.ils_state r child cr /\
  inline_call_incidence cert root p pa.ia_function l j call
    (InlineSelected u q e zipper) /\
  inline_namespace_leaf_at cert q route.ir_rename child.ia_function /\
  inline_token_consumes e incoming next ==>
  ?csnap edge bb cb h.
    inline_owner_storage cert
      ((q,child,route,csnap)::(p,pa,proute,psnap)::rest) frame /\
    MEM (p,pa,proute,psnap)
      ((q,child,route,csnap)::(p,pa,proute,psnap)::rest) /\
    child.ia_parent = SOME edge /\ edge.ipe_parent = pa.ia_id /\
    edge.ipe_call = call /\ edge.ipe_saved = psnap.ils_state /\
    edge.ipe_child = child.ia_entry /\
    inline_tracked_snapshot pa.ia_function pa proute psnap frame /\
    lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
    lookup_block incoming.ic_block e.ise_callee.fn_blocks = SOME cb /\
    h = SND (inline_cell_prefix e bb cb incoming.ic_index) /\
    h < LENGTH (rotate_invoke_ops
      (EL e.ise_index bb.bb_instructions).inst_operands) /\
    next.ic_fields =
      (ASSIGN, [EL h (rotate_invoke_ops
        (EL e.ise_index bb.bb_instructions).inst_operands)],
       MAP (STRCAT e.ise_prefix) (SND (SND incoming.ic_fields)))
Proof
  strip_tac >>
  drule_all inline_selected_child_stored_parent >> strip_tac >>
  gvs[inline_token_consumes_def] >> metis_tac[]
QED
