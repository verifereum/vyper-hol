(* Local provenance boundaries; not a reachable-frame coherence theorem. *)
Theory o1LowerDloadGhost
Ancestors
  ptrDiscipline finite_map pointerConfinedDefs venomInst

Theorem first_prov_origin:
  !ops G site. first_prov G ops = SOME site ==>
    ?v. MEM (Var v) ops /\ FLOOKUP G v = SOME site
Proof
  Induct >> simp[first_prov_def] >> rpt gen_tac >>
  Cases_on `op_prov G h` >> simp[]
  >- metis_tac[] >>
  Cases_on `h` >> gvs[op_prov_def] >> metis_tac[]
QED

Theorem step_prov_origin:
  MEM inst (fn_insts fn) /\
  (!k site. k < LENGTH PG /\ EL k PG = SOME site ==> k IN P fn.fn_name) /\
  FLOOKUP (step_prov PG G inst s') v = SOME site ==>
  (FLOOKUP G v = SOME site /\ ~MEM v inst.inst_outputs) \/
  v IN ptr_roots P fn \/
  (MEM v inst.inst_outputs /\
   (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB \/ inst.inst_opcode = ASSIGN) /\
   ?u. MEM (Var u) inst.inst_operands /\ FLOOKUP G u = SOME site)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_outputs` >>
  gvs[step_prov_def, set_prov_def, FLOOKUP_DRESTRICT] >>
  Cases_on `t` >>
  gvs[step_prov_def, set_prov_def, FLOOKUP_DRESTRICT] >>
  Cases_on `out_prov PG G inst s'` >>
  gvs[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, AllCaseEqs()] >>
  `inst_output inst = SOME h` by simp[inst_output_def] >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (disj1_tac >> simp[ptr_roots_def, alloca_roots_def] >>
      metis_tac[inst_output_def]) >>
  Cases_on `inst.inst_opcode = DALLOCA`
  >- (disj1_tac >> simp[ptr_roots_def] >>
      metis_tac[inst_output_def]) >>
  Cases_on `inst.inst_opcode = PARAM`
  >- (gvs[out_prov_def, AllCaseEqs()] >>
      simp[ptr_roots_def] >>
      metis_tac[inst_output_def]) >>
  gvs[out_prov_def, AllCaseEqs()] >>
  metis_tac[first_prov_origin]
QED
