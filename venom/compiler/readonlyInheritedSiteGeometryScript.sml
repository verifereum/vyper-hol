(* Separation of inherited positive-size sites from local allocations.
   Occurrence owners, not instruction ids, distinguish recursive frames. *)
Theory readonlyInheritedSiteGeometry
Ancestors
  occurrenceGeometry o1LowerDloadOccurrence ptrDiscipline venomExecSemantics
  finite_map list pred_set arithmetic

Theorem inherited_site_current_alloca_exclusion:
  occurrence_natural_geometry lo a U B stk s /\
  occurrence_annotation_ok n a U B HP H stk PG G s /\
  MEM owner (MAP (\u. u.of_owner) U) /\
  FLOOKUP B (owner,aid) = SOME (b,z) /\ 0 < z ==>
  !local_id. FLOOKUP s.vs_allocas local_id <> SOME (b,z)
Proof
  rpt strip_tac >>
  `owner <> a` by metis_tac[occurrence_annotation_ok_def,
    listTheory.ALL_DISTINCT, listTheory.MEM] >>
  `FLOOKUP B (a,local_id) = SOME (b,z)` by
    gvs[occurrence_annotation_ok_def, occurrence_allocas_ok_def] >>
  metis_tac[occurrence_geometry_positive_site_unique, pairTheory.PAIR_EQ]
QED

(* The successful-step boundary does not require a following active instruction. *)
Theorem inherited_site_alloca_step_exclusion:
  occurrence_natural_geometry lo a U B stk s /\
  occurrence_annotation_ok n a U B HP H stk PG G s /\
  MEM owner (MAP (\u. u.of_owner) U) /\
  FLOOKUP B (owner,aid) = SOME (b,z) /\ 0 < z /\
  lo <= s.vs_alloca_next /\ inst.inst_opcode = ALLOCA /\
  step_inst fuel C inst s = OK s' ==>
  !local_id. FLOOKUP s'.vs_allocas local_id <> SOME (b,z)
Proof
  rpt strip_tac >>
  `owner <> a` by metis_tac[occurrence_annotation_ok_def,
    listTheory.ALL_DISTINCT, listTheory.MEM] >>
  `occurrence_allocas_ok B a s` by fs[occurrence_annotation_ok_def] >>
  `occurrence_natural_geometry lo a U (occurrence_sites_step a B inst s') stk
     (s' with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule occurrence_geometry_next >> simp[] >> metis_tac[]) >>
  `FLOOKUP (occurrence_sites_step a B inst s') (owner,aid) = SOME (b,z)` by
    simp[occurrence_sites_step_other_owner] >>
  `occurrence_allocas_ok (occurrence_sites_step a B inst s') a s'` by
    metis_tac[occurrence_sites_step_allocas] >>
  `FLOOKUP (occurrence_sites_step a B inst s') (a,local_id) = SOME (b,z)` by
    fs[occurrence_allocas_ok_def] >>
  metis_tac[occurrence_geometry_positive_site_unique, pairTheory.PAIR_EQ]
QED

(* Direct interface for provenance support at an ALLOCA step. *)
Theorem inherited_site_out_prov_exclusion:
  occurrence_natural_geometry lo a U B stk s /\
  occurrence_annotation_ok n a U B HP H stk PG G s /\
  MEM owner (MAP (\u. u.of_owner) U) /\
  FLOOKUP B (owner,aid) = SOME (b,z) /\ 0 < z /\
  lo <= s.vs_alloca_next /\ inst.inst_opcode = ALLOCA /\
  step_inst fuel C inst s = OK s' ==>
  out_prov PG G inst s' <> SOME (b,z)
Proof
  strip_tac >> simp[out_prov_def] >>
  metis_tac[inherited_site_alloca_step_exclusion]
QED

(* Recover the annotated interface from ordinary reachable frames.  The
   bound lo=0 is enough here: no pointer-discipline premise is necessary.
   Ownership transport uses occurrence_annotation_call/block/return;
   occurrence_sites_step_other_owner preserves each inherited lookup. *)
Theorem frame_reachable_inherited_site_exclusion:
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  frame_reachable vs C stk PG G tn fn active s ==>
  ?n a U B HP H.
    occ_frame_reachable vs C stk PG G tn fn active s n a U B HP H /\
    occurrence_annotation_ok n a U B HP H stk PG G s /\
    occurrence_natural_geometry 0 a U B stk s /\
    !owner aid b z.
      MEM owner (MAP (\u. u.of_owner) U) /\
      FLOOKUP B (owner,aid) = SOME (b,z) /\ 0 < z ==>
      (!local_id. FLOOKUP s.vs_allocas local_id <> SOME (b,z)) /\
      (!inst fuel s'. inst.inst_opcode = ALLOCA /\
          step_inst fuel C inst s = OK s' ==>
          out_prov PG G inst s' <> SOME (b,z))
Proof
  strip_tac >>
  `?n a U B HP H.
    occ_frame_reachable vs C stk PG G tn fn active s n a U B HP H /\
    occurrence_annotation_ok n a U B HP H stk PG G s /\
    occurrence_natural_geometry 0 a U B stk s` by
    (irule frame_reachable_occurrence_geometry >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`n`, `a`, `U`, `B`, `HP`, `H`] >> simp[] >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- metis_tac[inherited_site_current_alloca_exclusion] >>
  rpt gen_tac >> strip_tac >>
  irule (Q.INST [`lo` |-> `0`] inherited_site_out_prov_exclusion) >>
  simp[] >> metis_tac[]
QED
