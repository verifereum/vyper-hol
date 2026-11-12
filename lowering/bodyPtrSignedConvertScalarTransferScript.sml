Theory bodyPtrSignedConvertScalarTransfer
Ancestors bodyPtrBopScalarStep
  ptrDiscipline decoderGhostFramePtr finite_map list

Theorem step_prov_output_none:
  out_prov PG G inst t = NONE /\ MEM x inst.inst_outputs ==>
  FLOOKUP (step_prov PG G inst t) x = NONE
Proof
  Cases_on `inst.inst_outputs` >>
  simp[step_prov_def, set_prov_def, FLOOKUP_DRESTRICT]
QED

Theorem out_prov_forward_none:
  MEM inst.inst_opcode [ADD; SUB; ASSIGN] /\
  EVERY (\op. op_prov G op = NONE) inst.inst_operands ==>
  out_prov PG G inst t = NONE
Proof
  strip_tac >> drule bodyPtrBopScalarStepTheory.first_prov_none >>
  gvs[out_prov_def]
QED

Theorem phi_prov_selected_none:
  resolve_phi lbl inst.inst_operands = SOME op /\
  op_prov G op = NONE ==>
  phi_prov (SOME lbl) G inst = NONE
Proof
  simp[phi_prov_def]
QED

Theorem out_prov_clearing_none:
  ~MEM inst.inst_opcode [ALLOCA; DALLOCA; PARAM; ADD; SUB; ASSIGN] ==>
  out_prov PG G inst t = NONE
Proof
  simp[out_prov_def]
QED
