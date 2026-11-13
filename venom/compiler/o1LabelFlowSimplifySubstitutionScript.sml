Theory o1LabelFlowSimplifySubstitution
Ancestors
  codegenSymRel cfgTransform unitShapeDefs venomInst list

Theorem simplify_subst_inst_fields:
  (subst_block_labels_inst lm i).inst_opcode = i.inst_opcode /\
  (subst_block_labels_inst lm i).inst_outputs = i.inst_outputs
Proof
  simp[subst_block_labels_inst_def, subst_label_map_inst_def] >>
  IF_CASES_TAC >> simp[]
QED

Theorem simplify_subst_data_inst:
  i.inst_opcode = ADD \/ i.inst_opcode = ASSIGN \/
  i.inst_opcode = CODECOPY ==>
  subst_block_labels_inst lm i = i
Proof
  strip_tac >> simp[subst_block_labels_inst_def, is_block_label_opcode_def,
      is_terminator_def]
QED

Theorem simplify_subst_var_operand:
  MEM (Var x) (subst_block_labels_inst lm i).inst_operands <=>
  MEM (Var x) i.inst_operands
Proof
  simp[subst_block_labels_inst_def, subst_label_map_inst_def] >>
  IF_CASES_TAC >> simp[MEM_MAP] >> eq_tac >> rpt strip_tac
  >- (Cases_on `y` >> gvs[subst_label_map_op_def, AllCaseEqs()]) >>
  qexists_tac `Var x` >> simp[subst_label_map_op_def]
QED

Theorem simplify_subst_insts:
  MEM j (fn_insts (subst_block_labels_fn lm f)) <=>
  ?i. MEM i (fn_insts f) /\ j = subst_block_labels_inst lm i
Proof
  simp[fn_insts_def, MEM_fn_insts_blocks_iff, subst_block_labels_fn_def,
       subst_block_labels_block_def, MEM_FLAT, MEM_MAP] >>
  eq_tac >> rpt strip_tac >> gvs[MEM_MAP]
  >- (qexists_tac `y'` >> simp[] >> metis_tac[]) >>
  qexists_tac `subst_block_labels_block lm bb` >>
  simp[subst_block_labels_block_def, MEM_MAP] >> metis_tac[]
QED

Theorem simplify_subst_code_end_forward:
  !f x. code_end_var f x ==>
    !lm. code_end_var (subst_block_labels_fn lm f) x
Proof
  Induct_on `code_end_var` >> rpt strip_tac >>
  `subst_block_labels_inst lm inst = inst` by
    metis_tac[simplify_subst_data_inst] >>
  `MEM inst (fn_insts (subst_block_labels_fn lm f))` by
    (simp[simplify_subst_insts] >> metis_tac[]) >>
  metis_tac[code_end_var_rules]
QED

Theorem simplify_subst_code_end_backward:
  !g x. code_end_var g x ==>
    !lm f. g = subst_block_labels_fn lm f ==> code_end_var f x
Proof
  Induct_on `code_end_var` >> rpt strip_tac >>
  gvs[simplify_subst_insts, simplify_subst_inst_fields] >>
  `subst_block_labels_inst lm i = i` by
    metis_tac[simplify_subst_data_inst] >>
  gvs[] >> metis_tac[code_end_var_rules]
QED

Theorem simplify_subst_code_end_iff:
  code_end_var (subst_block_labels_fn lm f) x <=> code_end_var f x
Proof
  metis_tac[simplify_subst_code_end_forward, simplify_subst_code_end_backward]
QED

(* Even a map mentioning code_end cannot change data instructions.  In
   fact the structural premise is unnecessary for this restricted map. *)
Theorem simplify_subst_block_labels_label_flow:
  label_flow_ok (ctx with ctx_functions := [f]) ==>
  label_flow_ok (ctx with ctx_functions := [subst_block_labels_fn lm f])
Proof
  simp[label_flow_ok_def, simplify_subst_insts] >>
  strip_tac >> gen_tac >> strip_tac >> gvs[] >>
  first_x_assum (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
  simp[simplify_subst_inst_fields] >> conj_tac
  >- (rpt strip_tac >>
      `MEM (Var x) i.inst_operands /\ code_end_var f x` by
        metis_tac[simplify_subst_var_operand, simplify_subst_code_end_iff] >>
      `i.inst_opcode = ASSIGN \/ i.inst_opcode = CODECOPY` by metis_tac[] >>
      `subst_block_labels_inst lm i = i` by
        metis_tac[simplify_subst_data_inst] >>
      metis_tac[]) >>
  strip_tac >>
  `subst_block_labels_inst lm i = i` by
    metis_tac[simplify_subst_data_inst] >>
  gvs[simplify_subst_code_end_iff]
QED
