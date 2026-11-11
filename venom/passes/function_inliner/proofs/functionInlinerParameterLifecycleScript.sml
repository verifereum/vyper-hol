(* Producer boundary for the storage, saved-read and immutable ancestry
   invariants.  Syntactic paths remain separate from physical storage routes. *)
Theory functionInlinerParameterLifecycle
Ancestors
  functionInlinerParameterCorrespondence functionInlinerParameterSavedReads
  functionInlinerParameterAncestry functionInlinerParameterNesting
  functionInlinerOperationalCuts list

Theorem inline_parameter_lifecycle_root:
  inline_annotated_origin C n root cert /\
  a.ia_function = inline_entry_function cert /\
  a.ia_entry.vs_labels = FEMPTY ==>
  ?path snap frame.
    inline_owner_storage cert
      [(inline_entry_address cert,a,inline_route_identity a.ia_id,snap)] frame /\
    inline_parameter_saved_reads
      [(inline_entry_address cert,a,inline_route_identity a.ia_id,snap)] /\
    inline_parameter_ancestry C cert root
      (inline_parameter_owners
        [(inline_entry_address cert,a,inline_route_identity a.ia_id,snap)]) /\
    inline_routed_leaf cert root (inline_entry_address cert) a.ia_function path /\
    EVERY (\c. ?e. c = InlineKeep e) path /\
    inline_path_rename path = I /\
    snap.ils_state = a.ia_entry /\ frame.ipf_state = a.ia_entry
Proof
  strip_tac >> drule_all inline_parameter_ancestry_root >> strip_tac >>
  qexistsl_tac [`path`, `snap`, `frame`] >>
  simp[inline_parameter_saved_reads_root]
QED

Theorem inline_parameter_lifecycle_selected_push:
  inline_owner_storage cert ((p,pa,proute,psnap)::rest) frame /\
  inline_original_child C fuel pa.ia_id occurrence call psnap.ils_state r child cr /\
  inline_call_incidence cert root p pa.ia_function l j call
    (InlineSelected u q e zipper) /\
  inline_namespace_leaf_at cert q route.ir_rename child.ia_function /\
  inline_annotated_origin C n root cert /\
  inline_parameter_saved_reads ((p,pa,proute,psnap)::rest) /\
  inline_parameter_ancestry C cert root
    (inline_parameter_owners ((p,pa,proute,psnap)::rest)) ==>
  ?prefix path csnap edge.
    csnap.ils_state = child.ia_entry /\ csnap.ils_defined = {} /\
    csnap.ils_saved = psnap.ils_state /\
    csnap.ils_protected = (psnap.ils_defined DIFF psnap.ils_opaque) DIFF set call.inst_outputs /\
    csnap.ils_parent_rename = proute.ir_rename /\
    inline_owner_storage cert
      ((q,child,route,csnap)::(p,pa,proute,psnap)::rest) frame /\
    inline_parameter_saved_reads
      ((q,child,route,csnap)::(p,pa,proute,psnap)::rest) /\
    inline_parameter_ancestry C cert root
      (inline_parameter_owners
        ((q,child,route,csnap)::(p,pa,proute,psnap)::rest)) /\
    inline_routed_leaf cert root q child.ia_function
      (prefix ++ [InlineEnter e] ++ zipper) /\
    EVERY (\c. ?d. c = InlineKeep d) prefix /\
    inline_routed_leaf cert root p pa.ia_function
      (path ++ [InlineKeep e] ++ zipper) /\
    child.ia_parent = SOME edge /\ edge.ipe_parent = pa.ia_id /\
    edge.ipe_call = call /\ edge.ipe_saved = psnap.ils_state /\
    edge.ipe_child = child.ia_entry /\
    inline_tracked_snapshot pa.ia_function pa proute psnap frame
Proof
  strip_tac >> drule_all inline_parameter_nesting_push >> strip_tac >>
  drule_all inline_owner_storage_selected_child >> strip_tac >>
  rename1 `csnap'.ils_defined = {}` >>
  qexistsl_tac [`prefix`, `path`, `csnap'`, `edge`] >>
  simp[] >> conj_tac
  >- metis_tac[inline_parameter_saved_reads_push] >>
  gvs[] >> metis_tac[inline_parameter_ancestry_rules]
QED

(* Replacing a live head does not change the archived call edges or owners. *)
Theorem inline_parameter_lifecycle_head_replace:
  inline_parameter_saved_reads ((p,a,route,snap)::rest) /\
  inline_parameter_ancestry C cert root
    (inline_parameter_owners ((p,a,route,snap)::rest)) ==>
  inline_parameter_saved_reads ((p,a,route',snap')::rest) /\
  inline_parameter_ancestry C cert root
    (inline_parameter_owners ((p,a,route',snap')::rest))
Proof
  simp[] >> metis_tac[inline_parameter_saved_reads_head_replace]
QED

(* Pop preserves auxiliary invariants only: resumed storage needs return writes. *)
Theorem inline_parameter_lifecycle_pop:
  inline_parameter_saved_reads
    ((q,child,croute,csnap)::(p,pa,proute,psnap)::rest) /\
  inline_parameter_ancestry C cert root
    (inline_parameter_owners
      ((q,child,croute,csnap)::(p,pa,proute,psnap)::rest)) ==>
  inline_parameter_saved_reads ((p,pa,proute,psnap)::rest) /\
  inline_parameter_ancestry C cert root
    (inline_parameter_owners ((p,pa,proute,psnap)::rest))
Proof
  metis_tac[inline_parameter_saved_reads_pop, inline_parameter_ancestry_pop]
QED
