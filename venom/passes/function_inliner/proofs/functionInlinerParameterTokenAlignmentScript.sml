(* Consuming token frames are matched by semantic route keys, not by the
   irrelevant before/after fields of a site-edit representative. *)
Theory functionInlinerParameterTokenAlignment
Ancestors functionInlinerParameterCorrespondence
  functionInlinerSelectedParameterDescriptors functionInlinerRouteKeys
  functionInlinerParameterAncestry functionInlinerReachableCuts
  functionInlinerTokenLineage list

Theorem inline_edit_key_equal_projections:
  inline_edit_key d = inline_edit_key e ==>
  d.ise_caller = e.ise_caller /\ d.ise_callee = e.ise_callee /\
  d.ise_block = e.ise_block /\ d.ise_index = e.ise_index /\
  d.ise_prefix = e.ise_prefix
Proof
  strip_tac >>
  metis_tac[inline_edit_key_fields]
QED

Theorem inline_path_keys_equal_rename:
  MAP inline_choice_key path = MAP inline_choice_key path' ==>
  inline_path_rename path = inline_path_rename path'
Proof
  metis_tac[inline_path_key_rename]
QED

Theorem inline_token_consumption_stored_alignment:
  inline_annotated_origin C n root cert /\
  inline_parameter_ancestry C cert root
    (inline_parameter_owners ((p,a,route,snap)::entries)) /\
  inline_owner_storage cert ((p,a,route,snap)::entries) frame /\
  inline_routed_leaf cert root p a.ia_function path /\
  MAP inline_choice_key path =
    MAP inline_choice_key (MAP (\(tag,next). inline_cell_choice tag) frames) /\
  inline_cell_zipper c frames out /\
  frames = before ++ [(EnterCell consuming 0,next)] ++ after /\
  inline_token_consumes consuming incoming next ==>
  ?younger q child pp pa older fuel occurrence call saved r cr l j u e zipper parentpath
    proute psnap croute csnap.
    (p,a)::inline_parameter_owners entries =
      younger ++ [(q,child);(pp,pa)] ++ older /\
    inline_original_child C fuel pa.ia_id occurrence call saved r child cr /\
    inline_call_incidence cert root pp pa.ia_function l j call
      (InlineSelected u q e zipper) /\
    inline_edit_key consuming = inline_edit_key e /\
    MAP inline_choice_key (MAP (\(tag,next). inline_cell_choice tag) after) =
      MAP inline_choice_key zipper /\
    inline_routed_leaf cert root pp pa.ia_function
      (parentpath ++ [InlineKeep e] ++ zipper) /\
    MEM (pp,pa,proute,psnap) ((p,a,route,snap)::entries) /\
    MEM (q,child,croute,csnap) ((p,a,route,snap)::entries) /\
    inline_tracked_snapshot pa.ia_function pa proute psnap frame
Proof
  strip_tac >>
  `?pre tail. path = pre ++ tail /\
     MAP inline_choice_key tail =
       InlineEnter (inline_edit_key consuming) ::
       MAP inline_choice_key (MAP (\(tag,next). inline_cell_choice tag) after)` by
    (gvs[MAP_EQ_APPEND, inline_cell_choice_def, inline_choice_key_def] >>
     qexistsl_tac [`l10'`, `x0::l20`] >> simp[]) >>
  Cases_on `tail` >> gvs[] >> Cases_on `h` >>
  gvs[inline_choice_key_def, inline_cell_choice_def] >>
  mp_tac (Q.INST [`before` |-> `pre`, `d` |-> `i`, `after` |-> `t`]
    inline_parameter_ancestry_enter_stored) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[]
QED
