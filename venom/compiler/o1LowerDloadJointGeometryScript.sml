(* Exact extension interface; no dynamic frontier assumptions. *)
Theory o1LowerDloadJointGeometry
Ancestors o1LowerDloadJointRelation finite_map list pred_set words

Theorem ld_joint_geometry_extend_iff:
  ld_joint_geometry sites X lo owners /\ id NOTIN FDOM sites ==>
  (ld_joint_geometry (sites |+ (id,(b,c,z))) X lo owners <=>
   MEM (FST id) owners /\
   lo <= b /\ lo <= c /\ b+z < dimword (:256) /\ c+z < dimword (:256) /\
   (!jd d e w. FLOOKUP sites jd = SOME (d,e,w) /\ 0 < z /\ 0 < w ==>
      (b+z <= d \/ d+w <= b) /\ (c+z <= e \/ e+w <= c)) /\
   (!jd aid e. FLOOKUP X jd = SOME (aid,e) /\ 0 < z ==>
      c+z <= e \/ e+32 <= c))
Proof
  strip_tac >> eq_tac
  >- (simp[ld_joint_geometry_def, FLOOKUP_UPDATE] >> strip_tac >>
      `MEM (FST id) owners` by metis_tac[] >>
      `lo <= b /\ lo <= c /\ b+z < dimword (:256) /\ c+z < dimword (:256)` by
        (qpat_x_assum `!id' b' c' z'. (if _ then _ else _) = SOME (b',c',z') ==> _` (qspec_then `id` mp_tac) >> simp[]) >>
      simp[] >> conj_tac
      >- (rpt strip_tac >>
          `id <> jd` by (gvs[FLOOKUP_DEF] >> metis_tac[]) >>
          qpat_x_assum `!id' jd b' c' z' d e w. _`
            (qspec_then `id` mp_tac) >> simp[] >>
          disch_then (qspec_then `jd` mp_tac) >> simp[] >>
          metis_tac[]) >>
      rpt strip_tac >>
      qpat_x_assum `!id' jd b' c' z' aid e. _`
        (qspec_then `id` mp_tac) >> simp[] >> metis_tac[]) >>
  strip_tac >>
  simp[ld_joint_geometry_def, FLOOKUP_UPDATE] >>
  rpt conj_tac >> rpt gen_tac >>
  rpt (IF_CASES_TAC >> gvs[]) >> rpt strip_tac >>
  fs[ld_joint_geometry_def] >> metis_tac[]
QED

Theorem ld_joint_geometry_extend_frontiers:
  ld_joint_geometry sites X lo owners /\ id NOTIN FDOM sites /\
  MEM (FST id) owners /\ lo <= b /\ lo <= c /\
  b+z < dimword (:256) /\ c+z < dimword (:256) /\
  (!jd d e w. FLOOKUP sites jd = SOME (d,e,w) /\ 0 < w ==>
     d+w <= b /\ e+w <= c) /\
  (!jd aid e. FLOOKUP X jd = SOME (aid,e) ==> e+32 <= c) ==>
  ld_joint_geometry (sites |+ (id,(b,c,z))) X lo owners
Proof
  strip_tac >> drule_all ld_joint_geometry_extend_iff >>
  disch_then (irule o iffRL) >> simp[] >> metis_tac[]
QED
