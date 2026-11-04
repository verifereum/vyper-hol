Theory lowerDloadOpaqueExecution
Ancestors
  unitShapeDefs execEquivParamBase venomExecSemantics venomInst
  contextCodegenRel list

(* Opaque return-PC values cannot be observed by ordinary instructions. *)
Theorem ld_retpc_observable_operand:
  opaque_use_ok fn /\ MEM i (fn_insts fn) /\
  i.inst_opcode <> ASSIGN /\ i.inst_opcode <> PHI /\
  ~MEM i.inst_opcode [RET; RETFMP; DRET] /\
  MEM (Var x) i.inst_operands ==> ~retpc_var fn x
Proof
  strip_tac >> strip_tac >>
  drule_all opaque_use_ok_retpc_use >> simp[retpc_use_ok_def]
QED

(* Only the final operand is permitted to carry an opaque return token. *)
Theorem ld_retpc_return_front:
  opaque_use_ok fn /\ MEM i (fn_insts fn) /\
  MEM i.inst_opcode [RET; RETFMP; DRET] /\
  MEM (Var x) (FRONT i.inst_operands) ==> ~retpc_var fn x
Proof
  strip_tac >> strip_tac >>
  `i.inst_operands <> []` by (strip_tac >> gvs[]) >>
  `MEM (Var x) i.inst_operands` by
    metis_tac[APPEND_FRONT_LAST, MEM_APPEND] >>
  drule_all opaque_use_ok_retpc_use >>
  simp[retpc_use_ok_def] >> rpt strip_tac >>
  gvs[GSYM SNOC_APPEND, FRONT_SNOC]
QED

(* Contraposition of the seeded closure: a nonopaque output of a copy
   cannot have obtained its value from an opaque input.  The seed is
   arbitrary, so the same interface also covers opaque gas variables. *)
Theorem ld_copy_nonopaque_input:
  MEM i (fn_insts fn) /\ i.inst_opcode = ASSIGN /\
  i.inst_operands = [Var y] /\ MEM x i.inst_outputs /\
  ~copy_phi_var origin fn x ==> ~copy_phi_var origin fn y
Proof
  metis_tac[copy_phi_var_assign]
QED

Theorem ld_phi_nonopaque_selected_input:
  MEM i (fn_insts fn) /\ i.inst_opcode = PHI /\
  resolve_phi prev i.inst_operands = SOME (Var y) /\
  MEM x i.inst_outputs /\ ~copy_phi_var origin fn x ==>
  ~copy_phi_var origin fn y
Proof
  strip_tac >> strip_tac >>
  `MEM (Var y) i.inst_operands` by metis_tac[resolve_phi_MEM] >>
  metis_tac[copy_phi_var_phi]
QED
