Theory frameViewFacts
Ancestors
  frameRel unitShapeDefs stackPlanGen allocaRemapSSA venomInst list

Theorem retpc_var_output_cases:
  ssa_form fn /\ MEM inst (fn_insts fn) /\
  MEM x inst.inst_outputs /\ retpc_var fn x ==>
  inst.inst_opcode = RETPC_PARAM \/
  (?y. inst.inst_opcode = ASSIGN /\ inst.inst_operands = [Var y] /\
       retpc_var fn y) \/
  (?y. inst.inst_opcode = PHI /\ MEM (Var y) inst.inst_operands /\
       retpc_var fn y)
Proof
  strip_tac >>
  qpat_x_assum `retpc_var fn x` mp_tac >>
  simp[retpc_var_def, Once copy_phi_var_cases] >>
  strip_tac >> rename1 `MEM producer (fn_insts fn)` >>
  `inst = producer` by metis_tac[ssa_unique_output] >> gvs[] >>
  metis_tac[]
QED

Theorem noncopy_output_not_retpc:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs /\
  inst.inst_opcode <> RETPC_PARAM /\ inst.inst_opcode <> ASSIGN /\
  inst.inst_opcode <> PHI ==> ~retpc_var fn x
Proof
  metis_tac[retpc_var_output_cases]
QED

Theorem assign_output_retpc:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [Var y] ==>
  (retpc_var fn x <=> retpc_var fn y)
Proof
  strip_tac >> eq_tac
  >- (strip_tac >> drule_all retpc_var_output_cases >> simp[])
  >> simp[retpc_var_def] >> strip_tac >>
  irule copy_phi_var_assign >> metis_tac[]
QED

Theorem assign_nonvar_output_not_retpc:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [op] /\
  (!y. op <> Var y) ==> ~retpc_var fn x
Proof
  strip_tac >> strip_tac >> drule_all retpc_var_output_cases >>
  simp[] >> metis_tac[]
QED

Theorem ordinary_operand_not_retpc:
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  MEM (Var x) inst.inst_operands /\ inst.inst_opcode <> ASSIGN /\
  inst.inst_opcode <> PHI /\ inst.inst_opcode <> RET ==>
  ~retpc_var fn x
Proof
  metis_tac[opaque_use_ok_retpc_use, retpc_use_ok_def]
QED

Theorem codegen_ready_inst_not_pre:
  codegen_ready_fn fn /\ MEM inst (fn_insts fn) ==>
  ~is_pre_codegen_opcode inst.inst_opcode
Proof
  `!bbs. fn_insts_blocks bbs = FLAT (MAP (\bb. bb.bb_instructions) bbs)`
    by (Induct >> simp[fn_insts_blocks_def]) >>
  simp[codegen_ready_fn_def, fn_insts_def, MEM_FLAT, MEM_MAP,
       EVERY_MEM, codegen_ready_inst_def] >> metis_tac[]
QED
