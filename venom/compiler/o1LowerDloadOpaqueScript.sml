(* Opaque return-PC boundaries for LowerDload relocation.
   These are syntactic exclusions, not a frame simulation. *)
Theory o1LowerDloadOpaque
Ancestors
  unitShapeDefs venomExecSemantics list rich_list

Theorem non_retpc_assign_input:
  MEM i (fn_insts fn) /\ i.inst_opcode = ASSIGN /\
  i.inst_operands = [Var y] /\ MEM x i.inst_outputs /\
  ~retpc_var fn x ==> ~retpc_var fn y
Proof
  rw[retpc_var_def] >>
  metis_tac[copy_phi_var_assign]
QED

Theorem non_retpc_phi_input:
  MEM i (fn_insts fn) /\ i.inst_opcode = PHI /\
  MEM (Var y) i.inst_operands /\ MEM x i.inst_outputs /\
  ~retpc_var fn x ==> ~retpc_var fn y
Proof
  rw[retpc_var_def] >>
  metis_tac[copy_phi_var_phi]
QED

Theorem ret_front_non_retpc:
  opaque_use_ok fn /\ MEM i (fn_insts fn) /\
  i.inst_opcode = RET /\ i.inst_operands <> [] /\
  MEM (Var v) (FRONT i.inst_operands) ==> ~retpc_var fn v
Proof
  rpt strip_tac >>
  `MEM (Var v) i.inst_operands` by metis_tac[MEM_FRONT_NOT_NIL] >>
  drule_all opaque_use_ok_retpc_use >>
  simp[retpc_use_ok_def] >> rpt strip_tac >>
  gvs[FRONT_APPEND_NOT_NIL]
QED
