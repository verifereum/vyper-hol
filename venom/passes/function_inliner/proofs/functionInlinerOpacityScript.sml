(* Static token ancestry survives replacement of RETPC_PARAM by ASSIGN 0.
   This interface intentionally does not rediscover seeds in transformed code. *)
Theory functionInlinerOpacity
Ancestors
  functionInlinerOrigin functionInlinerDefs unitShapeDefs pred_set list rich_list string

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

(* Instruction-local form for structural transport, equivalent to the public
   function interface above. *)
Definition inline_inst_opacity_ok_def:
  inline_inst_opacity_ok opaque i <=>
    (!x. i.inst_opcode = RETPC_PARAM /\ MEM x i.inst_outputs ==> x IN opaque) /\
    (!x y. i.inst_opcode = ASSIGN /\ i.inst_operands = [Var y] /\
      MEM x i.inst_outputs /\ y IN opaque ==> x IN opaque) /\
    (!x y. i.inst_opcode = PHI /\ MEM (Var y) i.inst_operands /\
      MEM x i.inst_outputs /\ y IN opaque ==> x IN opaque) /\
    (!x. MEM (Var x) i.inst_operands /\ x IN opaque ==> retpc_use_ok i x) /\
    (!x. MEM x i.inst_outputs /\ x IN opaque ==>
      MEM i.inst_opcode [RETPC_PARAM; ASSIGN; PHI])
End

Theorem inline_opacity_every:
  inline_opacity_ok fn opaque <=>
  EVERY (inline_inst_opacity_ok opaque) (fn_insts fn)
Proof
  simp[inline_opacity_ok_def, inline_inst_opacity_ok_def, EVERY_MEM] >>
  metis_tac[]
QED

Theorem inline_inst_opacity_id:
  inline_inst_opacity_ok opaque (i with inst_id := n) <=>
  inline_inst_opacity_ok opaque i
Proof
  simp[inline_inst_opacity_ok_def, retpc_use_ok_def]
QED

Theorem inline_inst_opacity_phi_labels:
  i.inst_opcode = PHI /\ inline_inst_opacity_ok opaque i ==>
  inline_inst_opacity_ok opaque (subst_label_inst old new i)
Proof
  simp[inline_inst_opacity_ok_def, cfgTransformTheory.subst_label_inst_def,
    retpc_use_ok_def, MEM_MAP] >> rpt strip_tac >>
  rename1 `Var v = subst_label_op old new op` >>
  Cases_on `op` >> gvs[cfgTransformTheory.subst_label_op_def,
    SF boolSimps.COND_elim_ss] >> metis_tac[]
QED

Theorem inline_opacity_renumber:
  inline_opacity_ok (renumber_fn_inst_ids fn) opaque <=> inline_opacity_ok fn opaque
Proof
  simp[inline_opacity_every, EVERY_MAP] >>
  `MAP (inline_inst_opacity_ok opaque) (fn_insts (renumber_fn_inst_ids fn)) =
    MAP (inline_inst_opacity_ok opaque) (fn_insts fn)` by
    (irule renumber_fn_projection >> simp[inline_inst_opacity_id]) >>
  pop_assum (mp_tac o AP_TERM ``EVERY I``) >> simp[EVERY_MAP, SF ETA_ss]
QED

Theorem inline_opacity_fix_phis:
  inline_opacity_ok fn opaque ==>
  inline_opacity_ok (fix_inline_phis old new bb fn) opaque
Proof
  simp[inline_opacity_every, functionInlinerDefsTheory.fix_inline_phis_def,
    venomInstTheory.fn_insts_def, MEM_fn_insts_blocks_iff, EVERY_MEM, MEM_MAP] >>
  rpt strip_tac >> gvs[SF boolSimps.COND_elim_ss] >>
  gvs[MEM_MAP, SF boolSimps.COND_elim_ss] >>
  metis_tac[inline_inst_opacity_phi_labels]
QED

Theorem clone_operand_var_iff:
  clone_operand p labels op = Var x <=>
  ?v. op = Var v /\ x = STRCAT p v
Proof
  Cases_on `op` >> simp[clone_operand_def, SF boolSimps.COND_elim_ss] >>
  metis_tac[]
QED

Theorem clone_retpc_use_ok:
  retpc_use_ok i x ==> retpc_use_ok (clone_instruction p labels i) (STRCAT p x)
Proof
  simp[retpc_use_ok_def, clone_instruction_def] >> rpt strip_tac >>
  simp[clone_operand_def, MEM_MAP] >> rpt strip_tac >>
  gvs[clone_operand_var_iff]
QED

Theorem clone_inst_opacity:
  inline_inst_opacity_ok opaque i ==>
  inline_inst_opacity_ok (IMAGE (STRCAT p) opaque) (clone_instruction p labels i)
Proof
  simp[inline_inst_opacity_ok_def, clone_instruction_def,
    MEM_MAP, IN_IMAGE] >> rpt strip_tac >> gvs[]
  >- (qpat_x_assum `Var _ = clone_operand _ _ _` (mp_tac o SYM) >>
      simp[clone_operand_var_iff] >> strip_tac >> gvs[] >> metis_tac[])
  >- (qpat_x_assum `Var _ = clone_operand _ _ _` (mp_tac o SYM) >>
      simp[clone_operand_var_iff] >> strip_tac >> gvs[] >> metis_tac[])
  >- (qpat_x_assum `Var _ = clone_operand _ _ _` (mp_tac o SYM) >>
      simp[clone_operand_var_iff] >> strip_tac >> gvs[] >>
      metis_tac[clone_retpc_use_ok, clone_instruction_def])
  >> metis_tac[]
QED
