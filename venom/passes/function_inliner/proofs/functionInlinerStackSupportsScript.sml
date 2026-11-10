(* Static owner-local supports. No execution or write-avoidance premise. *)
Theory functionInlinerStackSupports
Ancestors
  functionInlinerEnvelopes functionInlinerCuts list pred_set

Definition inline_address_entry_def:
  inline_address_entry cert (p,a,route,snap) <=>
    inline_namespace_leaf_at cert p route.ir_rename a.ia_function /\
    snap.ils_defined SUBSET set (cfgTransform$fn_all_vars a.ia_function)
End

Definition inline_address_links_def:
  (inline_address_links [] = T) /\
  (inline_address_links [(p,a,route,snap)] = (snap.ils_protected = {})) /\
  (inline_address_links ((p,a,route,snap)::(q,b,outer,saved)::rest) <=>
    snap.ils_protected SUBSET set (cfgTransform$fn_all_vars b.ia_function) /\
    snap.ils_parent_rename = outer.ir_rename /\
    inline_address_links ((q,b,outer,saved)::rest))
End

Definition inline_address_stack_def:
  inline_address_stack cert entries <=>
    ALL_DISTINCT (MAP FST entries) /\
    EVERY (inline_address_entry cert) entries /\
    inline_address_links entries
End

Definition inline_erase_addresses_def:
  inline_erase_addresses entries = MAP SND entries
End

Theorem inline_address_stack_empty[simp]:
  inline_address_stack cert []
Proof
  simp[inline_address_stack_def, inline_address_links_def]
QED

Theorem inline_address_stack_pop:
  inline_address_stack cert (entry::rest) ==>
  inline_address_stack cert rest
Proof
  PairCases_on `entry` >>
  Cases_on `rest` >> simp[inline_address_stack_def, inline_address_links_def] >>
  PairCases_on `h` >> simp[inline_address_stack_def, inline_address_links_def]
QED

Theorem inline_address_stack_root:
  inline_namespace_leaf_at cert p route.ir_rename a.ia_function ==>
  snap.ils_defined SUBSET set (cfgTransform$fn_all_vars a.ia_function) ==>
  snap.ils_protected = {} ==>
  inline_address_stack cert [(p,a,route,snap)]
Proof
  simp[inline_address_stack_def, inline_address_entry_def, inline_address_links_def]
QED

Theorem inline_address_stack_push:
  inline_address_stack cert ((q,b,outer,saved)::rest) ==>
  ~MEM p (MAP FST ((q,b,outer,saved)::rest)) ==>
  inline_namespace_leaf_at cert p route.ir_rename a.ia_function ==>
  snap.ils_defined SUBSET set (cfgTransform$fn_all_vars a.ia_function) ==>
  snap.ils_protected SUBSET set (cfgTransform$fn_all_vars b.ia_function) ==>
  snap.ils_parent_rename = outer.ir_rename ==>
  inline_address_stack cert ((p,a,route,snap)::(q,b,outer,saved)::rest)
Proof
  simp[inline_address_stack_def, inline_address_entry_def, inline_address_links_def]
QED

Theorem inline_address_stack_avoids_from_locals:
  !entries. inline_address_stack cert entries ==>
    !d. (!p a route snap x. MEM (p,a,route,snap) entries ==>
      MEM x (cfgTransform$fn_all_vars a.ia_function) ==> d <> route.ir_rename x) ==>
    inline_suspended_avoids (inline_erase_addresses entries) d
Proof
  ho_match_mp_tac inline_address_links_ind >> rpt conj_tac
  >- simp[inline_erase_addresses_def]
  >- (simp[inline_address_stack_def, inline_address_entry_def,
        inline_address_links_def, inline_erase_addresses_def,
        inline_suspended_avoids_def] >>
      metis_tac[pred_setTheory.SUBSET_DEF]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  drule inline_address_stack_pop >> strip_tac >>
  `inline_suspended_avoids
    (inline_erase_addresses ((q,b,outer,saved)::rest)) d` by
    (first_x_assum irule >> gvs[] >> metis_tac[]) >>
  gvs[inline_address_stack_def, inline_address_entry_def,
    inline_address_links_def] >>
  asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss)
    [inline_erase_addresses_def, listTheory.MAP,
     inline_suspended_avoids_def, listTheory.EVERY_DEF] >>
  conj_tac
  >- (gvs[pred_setTheory.SUBSET_DEF] >> metis_tac[listTheory.MEM]) >>
  qpat_x_assum `inline_suspended_avoids _ _` mp_tac >>
  simp[inline_suspended_avoids_def, inline_erase_addresses_def]
QED

Theorem inline_address_stack_external_avoids:
  !entries. inline_address_stack cert entries ==>
    !p (rho:string -> string) fn x.
    inline_annotated_origin ctx n root cert ==>
    inline_namespace_leaf_at cert p rho fn ==>
    ~MEM p (MAP FST entries) ==>
    MEM x (cfgTransform$fn_all_vars fn) ==>
    inline_suspended_avoids (inline_erase_addresses entries) (rho x)
Proof
  rpt strip_tac >> irule inline_address_stack_avoids_from_locals >>
  reverse conj_tac >- metis_tac[] >> rpt strip_tac >>
  `inline_address_entry cert (p',a,route,snap)` by
    (gvs[inline_address_stack_def, EVERY_MEM] >> metis_tac[]) >>
  `p <> p'` by (gvs[MEM_MAP] >> metis_tac[pairTheory.FST]) >>
  gvs[inline_address_entry_def] >>
  drule_all inline_namespace_leaves_separate >>
  simp[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION,
    pred_setTheory.IN_IMAGE] >> metis_tac[]
QED

Theorem inline_address_stack_body_avoids:
  inline_address_stack cert ((p,a,route,snap)::rest) ==>
  inline_annotated_origin ctx n root cert ==>
  MEM x (cfgTransform$fn_all_vars a.ia_function) ==>
  inline_suspended_avoids (inline_erase_addresses rest) (route.ir_rename x)
Proof
  rpt strip_tac >> drule inline_address_stack_pop >> strip_tac >>
  irule inline_address_stack_external_avoids >>
  gvs[inline_address_stack_def, inline_address_entry_def] >> metis_tac[]
QED

Theorem inline_address_stack_body_protected:
  inline_address_stack cert ((p,a,route,snap)::rest) ==>
  inline_annotated_origin ctx n root cert ==>
  MEM x (cfgTransform$fn_all_vars a.ia_function) ==>
  !y. y IN snap.ils_protected ==> route.ir_rename x <> snap.ils_parent_rename y
Proof
  Cases_on `rest`
  >- simp[inline_address_stack_def, inline_address_links_def] >>
  PairCases_on `h` >>
  simp[inline_address_stack_def, inline_address_entry_def,
    inline_address_links_def] >> rpt strip_tac >>
  drule_all inline_namespace_leaves_separate >>
  simp[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION,
    pred_setTheory.IN_IMAGE] >> metis_tac[pred_setTheory.SUBSET_DEF]
QED

(* At return, apply body_avoids to the parent::older tail after popping the
   child. The parent is intentionally absent from the protected observations. *)
Theorem inline_address_stack_return_avoids:
  inline_address_stack cert (child::(p,a,route,snap)::older) ==>
  inline_annotated_origin ctx n root cert ==>
  MEM x (cfgTransform$fn_all_vars a.ia_function) ==>
  inline_suspended_avoids (inline_erase_addresses older) (route.ir_rename x)
Proof
  metis_tac[inline_address_stack_pop, inline_address_stack_body_avoids]
QED

Theorem inline_address_stack_body_writes_avoid:
  inline_address_stack cert ((p,a,route,snap)::rest) ==>
  inline_annotated_origin ctx n root cert ==>
  EVERY (\(d,w). d IN IMAGE route.ir_rename
    (set (cfgTransform$fn_all_vars a.ia_function))) writes ==>
  EVERY (\(d,w). inline_suspended_avoids (inline_erase_addresses rest) d) writes
Proof
  simp[EVERY_MEM, pairTheory.FORALL_PROD, pred_setTheory.IN_IMAGE] >>
  metis_tac[inline_address_stack_body_avoids]
QED

Theorem inline_address_stack_subtree_avoids:
  !cert entries ctx n root p (rho:string -> string) sub d.
  inline_address_stack cert entries ==>
  inline_annotated_origin ctx n root cert ==>
  inline_namespace_node_at cert p rho sub ==>
  EVERY (\entry. inline_namespace_incomparable p (FST entry)) entries ==>
  d IN IMAGE rho (inline_namespace_envelope sub) ==>
  inline_suspended_avoids (inline_erase_addresses entries) d
Proof
  rpt strip_tac >> irule inline_address_stack_avoids_from_locals >>
  reverse conj_tac >- metis_tac[] >> rpt strip_tac >>
  `inline_address_entry cert (p',a,route,snap)` by
    (gvs[inline_address_stack_def, EVERY_MEM] >> metis_tac[]) >>
  `inline_namespace_incomparable p p'` by
    (gvs[EVERY_MEM] >> metis_tac[pairTheory.FST]) >>
  gvs[inline_address_entry_def, inline_namespace_leaf_at_def] >>
  drule_all inline_namespace_nodes_separate >>
  simp[inline_namespace_envelope_def, pred_setTheory.DISJOINT_DEF,
    pred_setTheory.EXTENSION, pred_setTheory.IN_IMAGE] >>
  gvs[pred_setTheory.IN_IMAGE] >> metis_tac[]
QED

Theorem inline_address_stack_subtree_writes_avoid:
  !cert entries ctx n root p (rho:string -> string) sub writes.
  inline_address_stack cert entries ==>
  inline_annotated_origin ctx n root cert ==>
  inline_namespace_node_at cert p rho sub ==>
  EVERY (\entry. inline_namespace_incomparable p (FST entry)) entries ==>
  EVERY (\(d,w). d IN IMAGE rho (inline_namespace_envelope sub)) writes ==>
  EVERY (\(d,w). inline_suspended_avoids (inline_erase_addresses entries) d) writes
Proof
  rpt strip_tac >> drule inline_address_stack_subtree_avoids >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  gvs[EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]
QED
