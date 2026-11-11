(* Dynamic-owner audit boundaries.  Static token lineage alone does not
   certify that the selecting caller is on the dynamic owner stack. *)
Theory functionInlinerParameterAncestors
Ancestors
  functionInlinerOperationalCuts functionInlinerSelectedParameterDescriptors
  functionInlinerPairedSelection functionInlinerTokenLineage
  functionInlinerCuts functionInlinerStackSupports list

Theorem inline_owner_storage_member:
  inline_owner_storage cert entries frame /\ MEM (p,a,route,snap) entries ==>
  inline_tracked_snapshot a.ia_function a route snap frame
Proof
  simp[inline_owner_storage_def, inline_suspended_observations_def,
       inline_erase_addresses_def, EVERY_MAP, EVERY_MEM,
       pairTheory.FORALL_PROD] >> rpt strip_tac >>
  first_x_assum irule >> simp[MEM_MAP] >>
  qexists `(p,a,route,snap)` >> simp[]
QED

(* The actual child push supplies the immediate dynamic caller.  It does not
   identify callers of other Enter edits later in a token's static zipper. *)
Theorem inline_selected_child_stored_parent:
  inline_owner_storage cert ((p,pa,proute,psnap)::rest) frame /\
  inline_original_child C fuel pa.ia_id occurrence call psnap.ils_state r child cr /\
  inline_call_incidence cert root p pa.ia_function l j call
    (InlineSelected uaddr q e zipper) /\
  inline_namespace_leaf_at cert q route.ir_rename child.ia_function ==>
  ?csnap edge.
    inline_owner_storage cert
      ((q,child,route,csnap)::(p,pa,proute,psnap)::rest) frame /\
    child.ia_parent = SOME edge /\ edge.ipe_parent = pa.ia_id /\
    edge.ipe_call = call /\ edge.ipe_saved = psnap.ils_state /\
    edge.ipe_child = child.ia_entry /\
    MEM (p,pa,proute,psnap)
      ((q,child,route,csnap)::(p,pa,proute,psnap)::rest) /\
    inline_tracked_snapshot pa.ia_function pa proute psnap frame
Proof
  strip_tac >>
  drule_all inline_owner_storage_selected_child >> strip_tac >>
  `inline_tracked_snapshot pa.ia_function pa proute psnap frame` by
    metis_tac[inline_owner_storage_head] >>
  gvs[functionInlinerActivationTheory.inline_original_child_def] >>
  qexists `csnap` >> simp[]
QED
