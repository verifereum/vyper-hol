(* Opaque variable provenance and positional use legality. *)
Theory simplifyCfgOpaque
Ancestors
  simplifyCfgShape simplifyCfgInvariant simplifyCfgDefs cfgTransform
  unitShapeDefs venomInst venomWf list

Theorem subst_label_inst_copy_source:
  MEM v (subst_label_inst a b i).inst_outputs /\
  (((subst_label_inst a b i).inst_opcode = ASSIGN /\
    (subst_label_inst a b i).inst_operands = [Var w]) \/
   ((subst_label_inst a b i).inst_opcode = PHI /\
    MEM (Var w) (subst_label_inst a b i).inst_operands)) ==>
  MEM v i.inst_outputs /\
  ((i.inst_opcode = ASSIGN /\ i.inst_operands = [Var w]) \/
   (i.inst_opcode = PHI /\ MEM (Var w) i.inst_operands))
Proof
  simp[subst_label_inst_def, MEM_MAP, subst_label_op_var] >>
  strip_tac >> simp[] >>
  Cases_on `i.inst_opcode = ASSIGN` >> gvs[] >>
  Cases_on `i.inst_operands` >> gvs[] >>
  metis_tac[subst_label_op_var]
QED

Theorem subst_label_map_op_var_iff:
  subst_label_map_op lm op = Var w <=> op = Var w
Proof
  Cases_on `op` >> simp[subst_label_map_op_def] >>
  Cases_on `ALOOKUP lm s` >> simp[]
QED

Theorem subst_block_labels_inst_copy_source:
  MEM v (subst_block_labels_inst lm i).inst_outputs /\
  (((subst_block_labels_inst lm i).inst_opcode = ASSIGN /\
    (subst_block_labels_inst lm i).inst_operands = [Var w]) \/
   ((subst_block_labels_inst lm i).inst_opcode = PHI /\
    MEM (Var w) (subst_block_labels_inst lm i).inst_operands)) ==>
  MEM v i.inst_outputs /\
  ((i.inst_opcode = ASSIGN /\ i.inst_operands = [Var w]) \/
   (i.inst_opcode = PHI /\ MEM (Var w) i.inst_operands))
Proof
  Cases_on `is_block_label_opcode i.inst_opcode` >>
  simp[subst_block_labels_inst_def, subst_label_map_inst_def,
       MEM_MAP, subst_label_map_op_var_iff] >>
  strip_tac >> simp[] >>
  Cases_on `i.inst_opcode = ASSIGN` >> gvs[] >>
  Cases_on `i.inst_operands` >> gvs[] >>
  metis_tac[subst_label_map_op_var_iff]
QED
