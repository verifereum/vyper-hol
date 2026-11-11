Theory functionInlinerParameterCorrespondence
Ancestors functionInlinerParameterAncestry functionInlinerRouteKeys
  functionInlinerParameterNesting functionInlinerRoutedProvenance
  functionInlinerActivation functionInlinerPairedSelection functionInlinerOccurrences list

Theorem inline_route_enter_transfer[local]:
  !before path d after.
    MAP inline_choice_key path =
      MAP inline_choice_key (before ++ [InlineEnter d] ++ after) ==>
    ?pre e post. path = pre ++ [InlineEnter e] ++ post /\
      inline_edit_key d = inline_edit_key e /\
      MAP inline_choice_key after = MAP inline_choice_key post
Proof
  Induct >> Cases_on `path` >> simp[] >> rpt gen_tac >> strip_tac
  >- (Cases_on `h` >> gvs[inline_choice_key_def] >>
      qexistsl_tac [`[]`, `i`, `t`] >> simp[]) >>
  first_x_assum (qspecl_then [`t`, `d`, `after`] mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`h::pre`, `e`, `post`] >> simp[]
QED

Theorem inline_route_enter_split[local]:
  !prefix before d after e zipper.
    EVERY (\c. ?k. c = InlineKeep k) prefix /\
    MAP inline_choice_key (prefix ++ [InlineEnter e] ++ zipper) =
      MAP inline_choice_key (before ++ [InlineEnter d] ++ after) ==>
    (inline_edit_key d = inline_edit_key e /\
     MAP inline_choice_key after = MAP inline_choice_key zipper) \/
    ?pre z post. zipper = pre ++ [InlineEnter z] ++ post /\
      inline_edit_key d = inline_edit_key z /\
      MAP inline_choice_key after = MAP inline_choice_key post
Proof
  Induct >> Cases_on `before` >> simp[] >> rpt gen_tac >> strip_tac
  >- gvs[inline_choice_key_def]
  >- (irule inline_route_enter_transfer >> simp[] >> metis_tac[])
  >- gvs[inline_choice_key_def] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem inline_parameter_ancestry_enter_aux[local]:
  !C cert root owners. inline_parameter_ancestry C cert root owners ==>
  !n p a rest before d after.
    inline_annotated_origin C n root cert /\ owners = (p,a)::rest /\
    inline_routed_leaf cert root p a.ia_function
      (before ++ [InlineEnter d] ++ after) ==>
    ?younger q child pp pa older fuel occurrence call saved r cr l j u e zipper parentpath.
      (p,a)::rest = younger ++ [(q,child);(pp,pa)] ++ older /\
      inline_original_child C fuel pa.ia_id occurrence call saved r child cr /\
      inline_call_incidence cert root pp pa.ia_function l j call
        (InlineSelected u q e zipper) /\
      inline_edit_key d = inline_edit_key e /\
      MAP inline_choice_key after = MAP inline_choice_key zipper /\
      inline_routed_leaf cert root pp pa.ia_function
        (parentpath ++ [InlineKeep e] ++ zipper)
Proof
  ho_match_mp_tac inline_parameter_ancestry_ind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
      drule inline_annotated_entry_route >> strip_tac >>
      `MAP inline_choice_key path =
       MAP inline_choice_key (before ++ [InlineEnter d] ++ after)` by
        metis_tac[inline_routed_leaf_key_unique] >>
      `EVERY (\c. ?e. c = InlineKeep e) (MAP inline_choice_key path)` by
        (gvs[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
         res_tac >> gvs[inline_choice_key_def]) >>
      gvs[EVERY_APPEND, inline_choice_key_def]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  drule inline_selected_entry_route_pair >>
  disch_then (qspecl_then [`C`, `n`, `u`, `p'`, `e`, `zipper`] mp_tac) >>
  simp[] >> strip_tac >>
  `MAP inline_choice_key (prefix ++ [InlineEnter e] ++ zipper) =
   MAP inline_choice_key (before ++ [InlineEnter d] ++ after)` by
    metis_tac[inline_routed_leaf_key_unique] >>
  drule_all inline_route_enter_split >> strip_tac
  >- (qexistsl_tac [`[]`, `p'`, `a`, `p`, `pa`, `rest`] >>
      simp[] >> metis_tac[]) >>
  `inline_routed_leaf cert root p pa.ia_function
    ((path ++ [InlineKeep e] ++ pre) ++ [InlineEnter z] ++ post)` by
    gvs[APPEND_ASSOC] >>
  first_x_assum drule >> strip_tac >>
  first_x_assum (qspecl_then [`path ++ [InlineKeep e] ++ pre`, `z`, `post`] mp_tac) >>
  simp[APPEND_ASSOC] >> strip_tac >>
  qexists_tac `((p',a)::younger)` >> simp[] >> metis_tac[]
QED

Theorem inline_parameter_ancestry_enter:
  inline_annotated_origin C n root cert /\
  inline_parameter_ancestry C cert root ((p,a)::rest) /\
  inline_routed_leaf cert root p a.ia_function
    (before ++ [InlineEnter d] ++ after) ==>
  ?younger q child pp pa older fuel occurrence call saved r cr l j u e zipper parentpath.
    (p,a)::rest = younger ++ [(q,child);(pp,pa)] ++ older /\
    inline_original_child C fuel pa.ia_id occurrence call saved r child cr /\
    inline_call_incidence cert root pp pa.ia_function l j call
      (InlineSelected u q e zipper) /\
    inline_edit_key d = inline_edit_key e /\
    MAP inline_choice_key after = MAP inline_choice_key zipper /\
    inline_routed_leaf cert root pp pa.ia_function
      (parentpath ++ [InlineKeep e] ++ zipper)
Proof
  metis_tac[inline_parameter_ancestry_enter_aux]
QED

Theorem inline_parameter_ancestry_owners_cong:
  inline_parameter_owners entries = inline_parameter_owners entries' ==>
  (inline_parameter_ancestry C cert root (inline_parameter_owners entries) <=>
   inline_parameter_ancestry C cert root (inline_parameter_owners entries'))
Proof simp[]
QED

Theorem inline_parameter_ancestry_pop:
  inline_parameter_ancestry C cert root
    (inline_parameter_owners ((q,child,croute,csnap)::(p,pa,proute,psnap)::rest)) ==>
  inline_parameter_ancestry C cert root
    (inline_parameter_owners ((p,pa,proute,psnap)::rest))
Proof simp[] >> metis_tac[inline_parameter_ancestry_push_elim]
QED

Theorem inline_parameter_owners_member:
  MEM (p,a) (inline_parameter_owners entries) <=>
  ?route snap. MEM (p,a,route,snap) entries
Proof
  simp[inline_parameter_owners_def, MEM_MAP, pairTheory.EXISTS_PROD] >>
  metis_tac[]
QED

Theorem inline_parameter_ancestry_enter_stored:
  inline_annotated_origin C n root cert /\
  inline_parameter_ancestry C cert root
    (inline_parameter_owners ((p,a,route,snap)::entries)) /\
  inline_owner_storage cert ((p,a,route,snap)::entries) frame /\
  inline_routed_leaf cert root p a.ia_function
    (before ++ [InlineEnter d] ++ after) ==>
  ?younger q child pp pa older fuel occurrence call saved r cr l j u e zipper parentpath
    proute psnap croute csnap.
    (p,a)::inline_parameter_owners entries =
      younger ++ [(q,child);(pp,pa)] ++ older /\
    inline_original_child C fuel pa.ia_id occurrence call saved r child cr /\
    inline_call_incidence cert root pp pa.ia_function l j call
      (InlineSelected u q e zipper) /\
    inline_edit_key d = inline_edit_key e /\
    MAP inline_choice_key after = MAP inline_choice_key zipper /\
    inline_routed_leaf cert root pp pa.ia_function
      (parentpath ++ [InlineKeep e] ++ zipper) /\
    MEM (pp,pa,proute,psnap) ((p,a,route,snap)::entries) /\
    MEM (q,child,croute,csnap) ((p,a,route,snap)::entries) /\
    inline_tracked_snapshot pa.ia_function pa proute psnap frame
Proof
  simp[] >> strip_tac >> drule_all inline_parameter_ancestry_enter >> strip_tac >>
  `MEM (pp,pa) (inline_parameter_owners ((p,a,route,snap)::entries)) /\
   MEM (q,child) (inline_parameter_owners ((p,a,route,snap)::entries))` by
    (simp[] >> metis_tac[MEM_APPEND, MEM]) >>
  `?proute psnap. MEM (pp,pa,proute,psnap) ((p,a,route,snap)::entries)` by
    metis_tac[inline_parameter_owners_member] >>
  `?croute csnap. MEM (q,child,croute,csnap) ((p,a,route,snap)::entries)` by
    metis_tac[inline_parameter_owners_member] >>
  `inline_tracked_snapshot pa.ia_function pa proute psnap frame` by
    metis_tac[functionInlinerParameterAncestorsTheory.inline_owner_storage_member] >>
  qexists_tac `younger` >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  gvs[] >> metis_tac[]
QED
