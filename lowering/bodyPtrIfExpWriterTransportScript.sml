Theory bodyPtrIfExpWriterTransport
Ancestors bodyPtrIfExpReturnBounds decoderGhostFramePtr ptrSafeRun
          ptrDiscipline finite_map list

Theorem ifexp_ghost_nonwriter:
  !fuel ctx PG G tn inst s p.
    ~MEM p inst.inst_outputs ==>
    FLOOKUP (FST (ghost_step fuel ctx PG G tn inst s)) p = FLOOKUP G p
Proof
  rpt strip_tac >> Cases_on `inst.inst_opcode = INVOKE`
  >- metis_tac[ifexp_invoke_caller_prov] >>
  simp[Once ghost_step_def] >>
  Cases_on `step_inst fuel ctx inst s` >>
  simp[step_prov_other_output]
QED

Theorem ifexp_phis_nonwriter:
  !is prev G p.
    (!i. MEM i is /\ i.inst_opcode = PHI ==> ~MEM p i.inst_outputs) ==>
    FLOOKUP (phis_prov prev G is) p = FLOOKUP G p
Proof
  Induct >> simp[phis_prov_def] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[phis_prov_def] >>
  `~MEM p h.inst_outputs` by metis_tac[] >>
  `FLOOKUP (phis_prov prev G is) p = FLOOKUP G p` by
    (first_x_assum irule >> metis_tac[]) >>
  Cases_on `h.inst_outputs` >> simp[set_prov_def, FLOOKUP_DRESTRICT] >>
  Cases_on `t` >> simp[set_prov_def, FLOOKUP_DRESTRICT] >>
  Cases_on `phi_prov prev G h` >>
  gvs[set_prov_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED

Theorem ifexp_entry_nonwriter:
  !fn s G p.
    (!bb i. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      MEM i bb.bb_instructions /\ i.inst_opcode = PHI ==>
      ~MEM p i.inst_outputs) ==>
    FLOOKUP (entry_prov fn s G) p = FLOOKUP G p
Proof
  rpt strip_tac >> simp[entry_prov_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  irule ifexp_phis_nonwriter >> metis_tac[]
QED
