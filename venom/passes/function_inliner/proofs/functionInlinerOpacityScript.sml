(* Static token ancestry survives replacement of RETPC_PARAM by ASSIGN 0.
   This interface intentionally does not rediscover seeds in transformed code. *)
Theory functionInlinerOpacity
Ancestors
  functionInlinerOrigin unitShapeDefs pred_set list rich_list

Definition inline_opacity_ok_def:
  inline_opacity_ok fn opaque <=>
    (!i x. MEM i (fn_insts fn) /\ i.inst_opcode = RETPC_PARAM /\
      MEM x i.inst_outputs ==> x IN opaque) /\
    (!i x y. MEM i (fn_insts fn) /\ i.inst_opcode = ASSIGN /\
      i.inst_operands = [Var y] /\ MEM x i.inst_outputs /\ y IN opaque ==>
      x IN opaque) /\
    (!i x y. MEM i (fn_insts fn) /\ i.inst_opcode = PHI /\
      MEM (Var y) i.inst_operands /\ MEM x i.inst_outputs /\ y IN opaque ==>
      x IN opaque) /\
    (!i x. MEM i (fn_insts fn) /\ MEM (Var x) i.inst_operands /\
      x IN opaque ==> retpc_use_ok i x) /\
    (!i x. MEM i (fn_insts fn) /\ MEM x i.inst_outputs /\ x IN opaque ==>
      MEM i.inst_opcode [RETPC_PARAM; ASSIGN; PHI])
End

Theorem inline_opacity_root:
  opaque_use_ok fn /\ retpc_shape_ok fn ==>
  inline_opacity_ok fn {x | retpc_var fn x}
Proof
  simp[inline_opacity_ok_def, opaque_use_ok_def, retpc_shape_ok_def,
    retpc_var_def] >> rpt strip_tac >>
  metis_tac[copy_phi_var_rules]
QED

Theorem inliner_input_opacity:
  inliner_input_ok ctx /\ MEM fn ctx.ctx_functions ==>
  inline_opacity_ok fn {x | retpc_var fn x}
Proof
  rpt strip_tac >> irule inline_opacity_root >>
  gvs[functionInlinerContractTheory.inliner_input_ok_def, EVERY_MEM] >> metis_tac[]
QED

Theorem inline_opacity_use:
  inline_opacity_ok fn opaque /\ MEM i (fn_insts fn) /\
  MEM (Var x) i.inst_operands /\ x IN opaque ==> retpc_use_ok i x
Proof
  simp[inline_opacity_ok_def] >> metis_tac[]
QED

Theorem inline_opacity_writer:
  inline_opacity_ok fn opaque /\ MEM i (fn_insts fn) /\
  MEM x i.inst_outputs /\ x IN opaque ==>
  MEM i.inst_opcode [RETPC_PARAM; ASSIGN; PHI]
Proof
  simp[inline_opacity_ok_def] >> metis_tac[]
QED

Theorem inline_opacity_invoke_operand:
  inline_opacity_ok fn opaque /\ MEM i (fn_insts fn) /\
  i.inst_opcode = INVOKE /\ MEM (Var x) i.inst_operands ==> x NOTIN opaque
Proof
  rpt strip_tac >> drule_all inline_opacity_use >>
  simp[retpc_use_ok_def]
QED

Theorem inline_opacity_invoke_output:
  inline_opacity_ok fn opaque /\ MEM i (fn_insts fn) /\
  i.inst_opcode = INVOKE /\ MEM x i.inst_outputs ==> x NOTIN opaque
Proof
  rpt strip_tac >> drule_all inline_opacity_writer >> simp[]
QED

Theorem inline_opacity_copy:
  inline_opacity_ok fn opaque /\ MEM i (fn_insts fn) /\
  i.inst_opcode = ASSIGN /\ i.inst_operands = [Var y] /\
  MEM x i.inst_outputs /\ y IN opaque ==> x IN opaque
Proof
  simp[inline_opacity_ok_def] >> metis_tac[]
QED

Theorem inline_opacity_phi:
  inline_opacity_ok fn opaque /\ MEM i (fn_insts fn) /\
  i.inst_opcode = PHI /\ MEM (Var y) i.inst_operands /\
  MEM x i.inst_outputs /\ y IN opaque ==> x IN opaque
Proof
  simp[inline_opacity_ok_def] >> metis_tac[]
QED

Theorem inline_opacity_ordinary_operand:
  inline_opacity_ok fn opaque /\ MEM i (fn_insts fn) /\
  ~MEM i.inst_opcode [ASSIGN; PHI; RET; RETFMP; DRET] /\
  MEM (Var x) i.inst_operands ==> x NOTIN opaque
Proof
  rpt strip_tac >> drule_all inline_opacity_use >>
  gvs[retpc_use_ok_def]
QED

Theorem inline_opacity_return_front:
  inline_opacity_ok fn opaque /\ MEM i (fn_insts fn) /\
  MEM i.inst_opcode [RET; RETFMP] /\
  MEM (Var x) (TAKE (LENGTH i.inst_operands - 1) i.inst_operands) ==>
  x NOTIN opaque
Proof
  rpt strip_tac >>
  `MEM (Var x) i.inst_operands` by metis_tac[MEM_TAKE] >>
  drule_all inline_opacity_use >>
  simp[retpc_use_ok_def] >> rpt strip_tac >> gvs[TAKE_APPEND] >>
  rpt strip_tac >> gvs[TAKE_APPEND]
QED

Theorem inline_opacity_seed:
  inline_opacity_ok fn opaque /\ MEM i (fn_insts fn) /\
  i.inst_opcode = RETPC_PARAM /\ MEM x i.inst_outputs ==> x IN opaque
Proof
  simp[inline_opacity_ok_def] >> metis_tac[]
QED
