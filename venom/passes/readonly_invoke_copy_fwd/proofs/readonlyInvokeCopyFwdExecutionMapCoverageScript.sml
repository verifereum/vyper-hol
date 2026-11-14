(* Numeric coverage follows the original source provenance through PHIs and
   ordinary instructions, independently of the target opcode proof. *)
Theory readonlyInvokeCopyFwdExecutionMapCoverage
Ancestors
  readonlyInvokeCopyFwdMapCoverage occurrenceOrigin
  occurrenceGeometry o1LowerDloadOccurrence
  ptrDiscipline o1LowerDloadGhost o1FrameLockstep finite_map list pred_set
  venomExecSemantics venomState venomInst arithmetic

Theorem ricf_execution_mapped_support_entry:
  ricf_mapped_support a B E PG G sites ==>
  ricf_mapped_support a B E PG (entry_prov fn s G) sites
Proof
  strip_tac >>
  irule (INST_TYPE [alpha |-> ``:string``] ricf_mapped_support_provenance_origin) >>
  qexistsl_tac [`G`,`PG`] >>
  simp[] >> metis_tac[entry_prov_identity_absent]
QED

Theorem ricf_execution_mapped_support_alloca:
  ricf_mapped_support a B E PG G sites /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  active_inst fn inst s /\ inst.inst_opcode = ALLOCA /\
  step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ricf_mapped_support a (occurrence_sites_step a B inst u) E PG
    (step_prov PG G inst u) sites
Proof
  strip_tac >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    simp[is_terminator_def] >>
  `occ_frame_reachable vs C stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn next (u with vs_inst_idx := SUC s.vs_inst_idx)
    n a U (occurrence_sites_step a B inst u) HP (occurrence_step a HP H inst u)` by
    (irule occ_frame_reachable_next >> metis_tac[]) >>
  `occurrence_natural_geometry 0 a U (occurrence_sites_step a B inst u) stk
    (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    metis_tac[occ_frame_reachable_geometry, arithmeticTheory.ZERO_LESS_EQ] >>
  `!id. FST id <> a ==>
    FLOOKUP (occurrence_sites_step a B inst u) id = FLOOKUP B id` by
    (Cases >> simp[occurrence_sites_step_other_owner]) >>
  `!id b z. FST id <> a /\
    FLOOKUP (occurrence_sites_step a B inst u) id = SOME (b,z) /\ 0 < z ==>
    FLOOKUP u.vs_allocas inst.inst_id <> SOME (b,z)` by
    (rpt strip_tac >>
     `id <> (a,inst.inst_id)` by metis_tac[pairTheory.FST] >>
     `FLOOKUP (occurrence_sites_step a B inst u) (a,inst.inst_id) = SOME (b,z)` by
       simp[occurrence_sites_step_def, FLOOKUP_UPDATE] >>
     `b + z <= b` by
       (fs[occurrence_natural_geometry_def] >>
        qpat_x_assum `!id jd b z c w. _`
          (qspecl_then [`id`,`(a,inst.inst_id)`,`b`,`z`,`b`,`z`] mp_tac) >>
        simp[] >> decide_tac) >> decide_tac) >>
  rw[ricf_mapped_support_def] >>
  gvs[step_prov_def, FLOOKUP_set_prov, out_prov_def, AllCaseEqs()] >>
  fs[ricf_mapped_support_def] >> metis_tac[]
QED

Theorem ricf_execution_mapped_support_ordinary:
  ricf_mapped_support a B E PG G sites /\
  inst.inst_opcode <> ALLOCA /\ inst.inst_opcode <> DALLOCA ==>
  ricf_mapped_support a B E PG (step_prov PG G inst s) sites
Proof
  strip_tac >>
  irule (INST_TYPE [alpha |-> ``:string``] ricf_mapped_support_provenance_origin) >>
  qexistsl_tac [`G`,`PG`] >> simp[] >>
  rpt strip_tac >>
  gvs[step_prov_def, FLOOKUP_set_prov, out_prov_def, AllCaseEqs()] >>
  metis_tac[first_prov_origin, MEM_EL]
QED
