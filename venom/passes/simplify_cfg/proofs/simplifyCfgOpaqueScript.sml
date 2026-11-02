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

Theorem map_var_head_unique:
  (!op. h op = Var x <=> op = Var x) ==>
  !ops. (?rest. MAP h ops = Var x :: rest /\ ~MEM (Var x) rest) <=>
        (?rest. ops = Var x :: rest /\ ~MEM (Var x) rest)
Proof
  strip_tac >> Cases >> simp[MEM_MAP] >> metis_tac[]
QED

Theorem map_var_last_unique:
  (!op. h op = Var x <=> op = Var x) ==>
  !ops. (?front. MAP h ops = front ++ [Var x] /\ ~MEM (Var x) front) <=>
        (?front. ops = front ++ [Var x] /\ ~MEM (Var x) front)
Proof
  strip_tac >> ho_match_mp_tac SNOC_INDUCT >>
  simp[SNOC_APPEND, MAP_APPEND, APPEND_11, MEM_MAP] >> metis_tac[]
QED

Theorem opaque_use_map_operands:
  (!op. h op = Var x <=> op = Var x) ==>
  (gas_use_ok (i with inst_operands := MAP h i.inst_operands) x <=>
   gas_use_ok i x) /\
  (retpc_use_ok (i with inst_operands := MAP h i.inst_operands) x <=>
   retpc_use_ok i x)
Proof
  strip_tac >>
  simp[gas_use_ok_def, retpc_use_ok_def, map_var_head_unique,
       map_var_last_unique]
QED

val opaque_legal = ``\A B i.
  (!x. A x /\ MEM (Var x) i.inst_operands ==> gas_use_ok i x) /\
  (!x. B x /\ MEM (Var x) i.inst_operands ==> retpc_use_ok i x)``;

Theorem fix_phi_inst_opaque_legal:
  ^opaque_legal A B i ==> ^opaque_legal A B (fix_phi_inst ps i)
Proof
  Cases_on `i.inst_opcode = PHI`
  >- (simp[fix_phi_inst_def] >>
      Cases_on `filter_phi_ops ps i.inst_operands` >>
      simp[gas_use_ok_def, retpc_use_ok_def] >>
      rename1 `h::t` >> Cases_on `t` >>
      simp[gas_use_ok_def, retpc_use_ok_def] >>
      rename1 `filter_phi_ops ps i.inst_operands = h::k::rest` >>
      Cases_on `rest` >>
      simp[gas_use_ok_def, retpc_use_ok_def]) >>
  simp[fix_phi_inst_def]
QED

Theorem update_phi_bypass_opaque_legal:
  ^opaque_legal A B i ==> ^opaque_legal A B (update_phi_bypass a b i)
Proof
  Cases_on `i.inst_opcode = PHI`
  >- simp[gas_use_ok_def, retpc_use_ok_def, update_phi_bypass_opcode] >>
  simp[update_phi_bypass_def]
QED

Theorem subst_label_inst_opaque_legal:
  ^opaque_legal A B i ==> ^opaque_legal A B (subst_label_inst a b i)
Proof
  simp[subst_label_inst_def, opaque_use_map_operands, subst_label_op_var,
       MEM_MAP] >> metis_tac[subst_label_op_var]
QED

Theorem subst_block_labels_inst_opaque_legal:
  ^opaque_legal A B i ==> ^opaque_legal A B (subst_block_labels_inst lm i)
Proof
  Cases_on `is_block_label_opcode i.inst_opcode` >>
  simp[subst_block_labels_inst_def, subst_label_map_inst_def,
       opaque_use_map_operands, subst_label_map_op_var_iff, MEM_MAP] >>
  metis_tac[subst_label_map_op_var_iff]
QED

Theorem canon_jnz_inst_opaque_legal:
  ^opaque_legal A B i ==> ^opaque_legal A B (canon_jnz_inst i)
Proof
  Cases_on `canon_jnz_inst i = i` >- simp[] >>
  drule canon_jnz_inst_changed >> strip_tac >>
  simp[gas_use_ok_def, retpc_use_ok_def] >>
  metis_tac[canon_jnz_inst_var_subset]
QED
