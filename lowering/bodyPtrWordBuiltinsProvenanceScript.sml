(* Load-like instructions overwrite stale output provenance, independently
   of the old ghost map. No new semantic definitions are needed. *)
Theory bodyPtrWordBuiltinsProvenance
Ancestors
  ptrDiscipline finite_map

Theorem step_prov_clear_output:
  !PG G inst s' x.
    MEM x inst.inst_outputs /\
    inst.inst_opcode <> ALLOCA /\ inst.inst_opcode <> DALLOCA /\
    inst.inst_opcode <> PARAM /\ inst.inst_opcode <> ADD /\
    inst.inst_opcode <> SUB /\ inst.inst_opcode <> ASSIGN ==>
    FLOOKUP (step_prov PG G inst s') x = NONE
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_outputs` >>
  gvs[step_prov_def, out_prov_def, set_prov_def, FLOOKUP_DRESTRICT]
QED
