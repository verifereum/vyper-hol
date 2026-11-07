Theory concretizeLayoutCanonicalBase
Ancestors concretizeLayoutCanonicalDriver concretizeLayoutCanonicalIndex frameResolvedCoherent
  concretizeLayoutPhaseSuccess list

Theorem layout_annotation_update_ordinary_unique:
  ev = SOME (OriginOrdinary fuel post) /\
  resolved_annotation_update q ev ids anns left /\
  resolved_annotation_update q ev ids anns right ==>
  left = right
Proof
  Cases_on `q` >> simp[Once resolved_annotation_update_cases] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `resolved_annotation_update _ _ _ _ _` mp_tac >>
  simp[Once resolved_annotation_update_cases] >> rpt strip_tac >> gvs[]
QED

Theorem layout_driver_indexed_ordinary:
  layout_driver_indexed es ass g /\ g.lop_cursor < LENGTH es /\
  EL g.lop_cursor es = SOME (OriginOrdinary fuel post) /\
  k.lop_cursor = SUC g.lop_cursor /\ k.lop_ids = g.lop_ids /\
  resolved_annotation_update g.lop_config (EL g.lop_cursor es)
    g.lop_ids g.lop_anns k.lop_anns /\
  resolved_annotation_edge C g.lop_cursor g.lop_config (EL g.lop_cursor es) q'
    g.lop_ids (EL g.lop_cursor ass) ids' (EL (SUC g.lop_cursor) ass) ==>
  layout_driver_indexed es ass k
Proof
  simp[layout_driver_indexed_def, resolved_annotation_edge_def] >> strip_tac >>
  conj_tac
  >- (irule layout_phase_canonical_ordinary >> goal_assum (drule_at Any) >> simp[]) >>
  irule layout_annotation_update_ordinary_unique >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

val _ = export_theory();
