(* Immutable call ancestry: saved call witnesses are archived by PUSH, while
   the index deliberately omits live snapshots and storage-route choices. *)
Theory functionInlinerParameterAncestry
Ancestors
  functionInlinerParameterNesting list

Definition inline_parameter_owners_def:
  inline_parameter_owners entries =
    MAP (\(p,a,route,snap). (p,a)) entries
End

Theorem inline_parameter_owners_nil[simp]:
  inline_parameter_owners [] = []
Proof
  simp[inline_parameter_owners_def]
QED

Theorem inline_parameter_owners_cons[simp]:
  inline_parameter_owners ((p,a,route,snap)::rest) =
    (p,a)::inline_parameter_owners rest
Proof
  simp[inline_parameter_owners_def]
QED

Inductive inline_parameter_ancestry:
  (!C cert root n a.
    inline_annotated_origin C n root cert /\
    a.ia_function = inline_entry_function cert /\
    a.ia_entry.vs_labels = FEMPTY ==>
    inline_parameter_ancestry C cert root [(inline_entry_address cert,a)]) /\
  (!C cert root p pa rest fuel occurrence call saved r child cr
      l j u q e zipper rho.
    inline_parameter_ancestry C cert root ((p,pa)::rest) /\
    inline_original_child C fuel pa.ia_id occurrence call saved r child cr /\
    inline_call_incidence cert root p pa.ia_function l j call
      (InlineSelected u q e zipper) /\
    inline_namespace_leaf_at cert q rho child.ia_function ==>
    inline_parameter_ancestry C cert root ((q,child)::(p,pa)::rest))
End

Theorem inline_parameter_ancestry_push_elim:
  inline_parameter_ancestry C cert root ((q,child)::(p,pa)::rest) ==>
  inline_parameter_ancestry C cert root ((p,pa)::rest) /\
  ?fuel occurrence call saved r cr l j u e zipper rho.
    inline_original_child C fuel pa.ia_id occurrence call saved r child cr /\
    inline_call_incidence cert root p pa.ia_function l j call
      (InlineSelected u q e zipper) /\
    inline_namespace_leaf_at cert q rho child.ia_function
Proof
  simp[Once inline_parameter_ancestry_cases] >> metis_tac[]
QED

Theorem inline_parameter_ancestry_snapshot_independent:
  inline_parameter_ancestry C cert root
    (inline_parameter_owners ((p,a,route,snap)::rest)) <=>
  inline_parameter_ancestry C cert root
    (inline_parameter_owners ((p,a,route',snap')::rest))
Proof
  simp[]
QED

Theorem inline_parameter_ancestry_root:
  inline_annotated_origin C n root cert /\
  a.ia_function = inline_entry_function cert /\
  a.ia_entry.vs_labels = FEMPTY ==>
  ?path snap frame.
    inline_parameter_ancestry C cert root
      (inline_parameter_owners
        [(inline_entry_address cert,a,inline_route_identity a.ia_id,snap)]) /\
    inline_routed_leaf cert root (inline_entry_address cert) a.ia_function path /\
    EVERY (\c. ?e. c = InlineKeep e) path /\
    inline_path_rename path = I /\
    inline_owner_storage cert
      [(inline_entry_address cert,a,inline_route_identity a.ia_id,snap)] frame /\
    snap.ils_state = a.ia_entry /\ frame.ipf_state = a.ia_entry
Proof
  strip_tac >> drule_all inline_parameter_nesting_root >> strip_tac >>
  simp[] >> metis_tac[inline_parameter_ancestry_rules]
QED

Theorem inline_parameter_ancestry_push:
  inline_annotated_origin C n root cert /\
  inline_parameter_ancestry C cert root
    (inline_parameter_owners ((p,pa,proute,psnap)::rest)) /\
  inline_owner_storage cert ((p,pa,proute,psnap)::rest) frame /\
  inline_original_child C fuel pa.ia_id occurrence call psnap.ils_state r child cr /\
  inline_call_incidence cert root p pa.ia_function l j call
    (InlineSelected u q e zipper) /\
  inline_namespace_leaf_at cert q route.ir_rename child.ia_function ==>
  ?prefix path csnap edge.
    inline_parameter_ancestry C cert root
      (inline_parameter_owners
        ((q,child,route,csnap)::(p,pa,proute,psnap)::rest)) /\
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
  strip_tac >> drule_all inline_parameter_nesting_push >> strip_tac >>
  gvs[] >> metis_tac[inline_parameter_ancestry_rules]
QED

(* The first consuming Enter keeps precisely the same archived call witness. *)
Theorem inline_parameter_ancestry_push_enter:
  inline_annotated_origin C n root cert /\
  inline_parameter_ancestry C cert root
    (inline_parameter_owners ((p,pa,proute,psnap)::rest)) /\
  inline_owner_storage cert ((p,pa,proute,psnap)::rest) frame /\
  inline_original_child C fuel pa.ia_id occurrence call psnap.ils_state r child cr /\
  inline_call_incidence cert root p pa.ia_function l j call
    (InlineSelected u q e zipper) /\
  inline_namespace_leaf_at cert q route.ir_rename child.ia_function /\
  inline_token_consumes e incoming next ==>
  ?csnap edge bb cb h.
    inline_parameter_ancestry C cert root
      (inline_parameter_owners
        ((q,child,route,csnap)::(p,pa,proute,psnap)::rest)) /\
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
  strip_tac >> drule_all inline_parameter_nesting_push_enter >> strip_tac >>
  gvs[] >> metis_tac[inline_parameter_ancestry_rules]
QED
