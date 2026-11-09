(* Provenance computations for subscript address arithmetic. *)
Theory bodyPtrSubscriptAddress
Ancestors
  ptrDiscipline finite_map

Theorem first_prov_base_op:
  op_prov G base_op = SOME site ==>
  first_prov G (base_op :: ops) = SOME site
Proof
  simp[first_prov_def]
QED

Theorem first_prov_pair_none:
  op_prov G base_op = NONE /\ op_prov G offset = NONE ==>
  first_prov G [base_op; offset] = NONE
Proof
  simp[first_prov_def]
QED

Theorem out_prov_mul:
  inst.inst_opcode = MUL ==> out_prov PG G inst s = NONE
Proof
  simp[out_prov_def]
QED

Theorem step_prov_add_base_op:
  inst.inst_opcode = ADD /\ inst.inst_operands = base_op :: ops /\
  inst.inst_outputs = [dst] /\ op_prov G base_op = SOME site ==>
  FLOOKUP (step_prov PG G inst s) dst = SOME site
Proof
  strip_tac >>
  simp[step_prov_def, out_prov_def, first_prov_def, set_prov_def, FLOOKUP_UPDATE]
QED

Theorem step_prov_add_none:
  inst.inst_opcode = ADD /\ inst.inst_operands = [base_op; offset] /\
  inst.inst_outputs = [dst] /\ op_prov G base_op = NONE /\
  op_prov G offset = NONE ==>
  FLOOKUP (step_prov PG G inst s) dst = NONE
Proof
  strip_tac >>
  simp[step_prov_def, out_prov_def, first_prov_def, set_prov_def,
       FLOOKUP_DRESTRICT]
QED
