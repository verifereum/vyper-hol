(* Immediate runtime provenance sources, independent of any compiler pass. *)
Theory runtimeProvenanceSources
Ancestors ptrDiscipline finite_map

Theorem set_prov_source:
  FLOOKUP (set_prov G outs p) v = SOME site ==>
  FLOOKUP G v = SOME site \/ (outs = [v] /\ p = SOME site)
Proof
  Cases_on `outs` >> Cases_on `p` >> simp[set_prov_def, FLOOKUP_DRESTRICT] >>
  Cases_on `t` >> simp[set_prov_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  Cases_on `h = v` >> simp[]
QED

Theorem set_prov_non_output:
  ~MEM v outs ==> FLOOKUP (set_prov G outs p) v = FLOOKUP G v
Proof
  Cases_on `outs` >> Cases_on `p` >> simp[set_prov_def, FLOOKUP_DRESTRICT] >>
  Cases_on `t` >> simp[set_prov_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED

Theorem first_prov_source:
  !ops. first_prov G ops = SOME site ==>
  ?v. MEM (Var v) ops /\ FLOOKUP G v = SOME site
Proof
  Induct >> simp[first_prov_def] >>
  Cases_on `h` >> simp[op_prov_def] >>
  rename1 `FLOOKUP G name` >>
  Cases_on `FLOOKUP G name` >> simp[] >> metis_tac[]
QED

Theorem step_prov_source:
  inst.inst_opcode <> DALLOCA /\
  FLOOKUP (step_prov PG G inst s') v = SOME site ==>
  FLOOKUP G v = SOME site \/
  (inst.inst_outputs = [v] /\
    ((inst.inst_opcode = ALLOCA /\
      FLOOKUP s'.vs_allocas inst.inst_id = SOME site) \/
     (inst.inst_opcode = PARAM /\ ?idx.
       inst.inst_operands = [Lit idx] /\ w2n idx < LENGTH PG /\
       EL (w2n idx) PG = SOME site) \/
     ((inst.inst_opcode = ADD \/ inst.inst_opcode = SUB \/
       inst.inst_opcode = ASSIGN) /\ ?u.
       MEM (Var u) inst.inst_operands /\ FLOOKUP G u = SOME site)))
Proof
  simp[step_prov_def] >> strip_tac >> drule set_prov_source >>
  strip_tac >- simp[] >> simp[] >>
  qpat_x_assum `out_prov _ _ _ _ = _` mp_tac >>
  simp[out_prov_def] >>
  Cases_on `inst.inst_opcode = ALLOCA` >> simp[] >>
  Cases_on `inst.inst_opcode = PARAM` >> simp[]
  >- (Cases_on `inst.inst_operands` >> simp[] >>
      Cases_on `t` >> simp[] >> Cases_on `h` >> simp[] >>
      IF_CASES_TAC >> simp[]) >>
  Cases_on `inst.inst_opcode = ADD \/ inst.inst_opcode = SUB \/
            inst.inst_opcode = ASSIGN` >> simp[] >>
  metis_tac[first_prov_source]
QED

Theorem phis_prov_source:
  !insts. FLOOKUP (phis_prov prev G0 insts) v = SOME site ==>
  FLOOKUP G0 v = SOME site \/ ?inst lbl op.
    MEM inst insts /\ inst.inst_opcode = PHI /\ inst.inst_outputs = [v] /\
    prev = SOME lbl /\ resolve_phi lbl inst.inst_operands = SOME op /\
    op_prov G0 op = SOME site
Proof
  Induct >> simp[phis_prov_def] >> gen_tac >>
  rename1 `inst.inst_opcode <> PHI` >>
  Cases_on `inst.inst_opcode = PHI` >> simp[]
  >- (strip_tac >> drule set_prov_source >> strip_tac
      >- metis_tac[] >>
      disj2_tac >> qexists_tac `inst` >> simp[] >>
      qpat_x_assum `phi_prov _ _ _ = _` mp_tac >>
      Cases_on `prev` >> simp[phi_prov_def] >>
      Cases_on `resolve_phi x inst.inst_operands` >> simp[]) >>
  metis_tac[]
QED
