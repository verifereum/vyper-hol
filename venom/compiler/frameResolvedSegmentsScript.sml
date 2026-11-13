Theory frameResolvedSegments
Ancestors frameResolvedCoherent frameFiniteJointDecoration frameDecoratedEndpoints
  frameJointTransition frameActivationLifetime frameSelectedDecoration list arithmetic

(* A restriction of one chosen coherent annotation sequence. *)
Definition resolved_annotation_segment_def:
  (resolved_annotation_segment C n q [] qe ids anns idse annse <=>
    qe = q /\ idse = ids /\ annse = anns) /\
  (resolved_annotation_segment C n q ((ev,q1)::w) qe ids anns idse annse <=>
    ?ids1 anns1.
      resolved_annotation_edge C n q ev q1 ids anns ids1 anns1 /\
      resolved_annotation_segment C (SUC n) q1 w qe ids1 anns1 idse annse)
End

Theorem resolved_annotation_segment_append:
  !w n q v qe ids anns idse annse.
  resolved_annotation_segment C n q (w ++ v) qe ids anns idse annse <=>
  ?mid idsm annsm.
    resolved_annotation_segment C n q w mid ids anns idsm annsm /\
    resolved_annotation_segment C (n + LENGTH w) mid v qe idsm annsm idse annse
Proof
  Induct >> simp[resolved_annotation_segment_def] >>
  Cases_on `h` >> simp[resolved_annotation_segment_def, ADD_CLAUSES] >>
  metis_tac[]
QED

Theorem resolved_annotation_segment_projects:
  !w n q qe ids anns idse annse.
  resolved_annotation_segment C n q w qe ids anns idse annse ==>
  joint_segment C q w qe
Proof
  Induct >> simp[resolved_annotation_segment_def, joint_segment_def] >>
  Cases_on `h` >> simp[resolved_annotation_segment_def, joint_segment_def] >>
  metis_tac[resolved_annotation_edge_def]
QED

Theorem resolved_annotation_segment_append_at:
  joint_segment C q w mid ==>
  (resolved_annotation_segment C n q (w ++ v) qe ids anns idse annse <=>
   ?idsm annsm.
    resolved_annotation_segment C n q w mid ids anns idsm annsm /\
    resolved_annotation_segment C (n + LENGTH w) mid v qe idsm annsm idse annse)
Proof
  strip_tac >> rewrite_tac[resolved_annotation_segment_append] >>
  eq_tac >> rpt strip_tac
  >- (`joint_segment C q w mid'` by
        metis_tac[resolved_annotation_segment_projects] >>
      `mid' = mid` by
        metis_tac[joint_segment_endpoint_index] >> gvs[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem resolved_annotation_call_suffix:
  resolved_annotation_edge C n q NONE q' ids (ann::saved) ids' anns' ==>
  ?callee. anns' = callee::ann::saved
Proof
  simp[resolved_annotation_edge_def, Once resolved_annotation_update_cases] >>
  metis_tac[]
QED

Theorem resolved_annotation_ordinary_suffix:
  resolved_annotation_edge C n q (SOME (OriginOrdinary fuel post)) q'
    ids (ann::saved) ids' anns' ==> ?ann'. anns' = ann'::saved
Proof
  simp[resolved_annotation_edge_def, Once resolved_annotation_update_cases] >>
  metis_tac[]
QED

Theorem resolved_annotation_block_suffix:
  resolved_annotation_edge C n q (SOME (OriginBlock fuel post)) q'
    ids (ann::saved) ids' anns' ==> ?ann'. anns' = ann'::saved
Proof
  simp[resolved_annotation_edge_def, Once resolved_annotation_update_cases] >>
  metis_tac[]
QED

Theorem resolved_annotation_resume_suffix:
  resolved_annotation_edge C n q
    (SOME (OriginResume fuel fn inst s ret send post)) q'
    ids (callee::ann::saved) ids' anns' ==> ?ann'. anns' = ann'::saved
Proof
  simp[resolved_annotation_edge_def, Once resolved_annotation_update_cases] >>
  metis_tac[]
QED

Theorem resolved_annotation_segment_indexed:
  !w n q I A.
  (!k. k < LENGTH w ==>
    resolved_annotation_edge C (n+k) (EL k (q::MAP SND w)) (FST (EL k w))
      (SND (EL k w)) (I k) (A k) (I (SUC k)) (A (SUC k))) ==>
  resolved_annotation_segment C n q w (EL (LENGTH w) (q::MAP SND w))
    (I 0) (A 0) (I (LENGTH w)) (A (LENGTH w))
Proof
  Induct >> simp[resolved_annotation_segment_def] >>
  Cases_on `h` >> rpt gen_tac >> strip_tac >>
  rename1 `resolved_annotation_segment C n src ((ev,dest)::w) _ (I0 0) (A0 0) _ _` >>
  simp[resolved_annotation_segment_def] >>
  qexistsl_tac [`I0 1`, `A0 1`] >> conj_tac
  >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  qpat_x_assum `!n q I A. _` (qspecl_then [`SUC n`, `dest`, `\k. I0 (SUC k)`,
    `\k. A0 (SUC k)`] mp_tac) >>
  simp[] >> disch_then irule >> gen_tac >> strip_tac >>
  first_x_assum (qspec_then `SUC k` mp_tac) >> simp[ADD_CLAUSES]
QED

Theorem selected_resolved_annotation_segment:
  selected_segment C q0 path n q w qe /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path)) (EL k iss) (EL k ass)
      (EL (SUC k) iss) (EL (SUC k) ass)) ==>
  resolved_annotation_segment C n q w qe
    (EL n iss) (EL n ass) (EL (n+LENGTH w) iss) (EL (n+LENGTH w) ass)
Proof
  simp[selected_segment_def] >> rpt strip_tac >> gvs[] >>
  qspec_then `w` (qspecl_then [`LENGTH pre`, `q`,
    `\k. EL (LENGTH pre+k) iss`, `\k. EL (LENGTH pre+k) ass`] mp_tac)
    resolved_annotation_segment_indexed >>
  (impl_tac
   >- (gen_tac >> strip_tac >>
       first_x_assum (qspec_then `LENGTH pre+k` mp_tac) >>
       simp[MAP_APPEND, EL_APPEND_EQN, ADD_CLAUSES, EL_MAP] >>
       Cases_on `k`
       >- (rev_drule joint_segment_endpoint_index >>
           disch_then (qspec_then `w ++ suffix` mp_tac) >> simp[MAP_APPEND]) >>
       simp[ADD_CLAUSES, EL_APPEND_EQN])) >>
  drule joint_segment_endpoint_index >>
  disch_then (qspec_then `[]` mp_tac) >> simp[]
QED
