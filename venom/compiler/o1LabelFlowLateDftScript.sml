Theory o1LabelFlowLateDft
Ancestors
  o1DftStep o1LabelFlowRetention dftShape dftStructural dftDefs
  unitShapeDefs codegenSymRel passSharedDefs venomEffects list

Theorem flip_operands_label_seed:
  label_positions_ok j /\ is_flippable j.inst_opcode /\
  (flip_operands j).inst_opcode = ADD /\
  (flip_operands j).inst_operands = [op; Label "code_end"] ==> F
Proof
  Cases_on `j.inst_operands` >> simp[flip_operands_def] >>
  Cases_on `t` >> simp[flip_operands_def] >>
  Cases_on `t'` >> simp[flip_operands_def] >>
  Cases_on `j.inst_opcode` >>
  gvs[is_comparator_def, flip_comparison_opcode_def,
      label_positions_ok_def, stackPlanTypesTheory.is_label_operand_def] >>
  Cases_on `op` >> simp[]
QED

Theorem dft_code_end_var_reflect:
  !g x. code_end_var g x ==> !ctx f.
    g = dft_fn f /\ o1_fn_shape ctx f /\
    EVERY label_positions_ok (fn_insts f) ==> code_end_var f x
Proof
  Induct_on `code_end_var` >> rpt strip_tac >> gvs[]
  >- (drule_all dft_shape_instruction_source >> strip_tac >> gvs[]
      >- metis_tac[code_end_var_rules] >>
      gvs[EVERY_MEM] >> metis_tac[flip_operands_label_seed]) >>
  `MEM inst (fn_insts f)` by
    (irule dft_shape_special_source >> simp[] >> metis_tac[]) >>
  metis_tac[code_end_var_rules]
QED

Theorem flip_operands_flow_opcodes:
  is_flippable j.inst_opcode ==>
  ~MEM j.inst_opcode [ASSIGN; CODECOPY; CODESIZE] /\
  ~MEM (flip_operands j).inst_opcode [ASSIGN; CODECOPY; CODESIZE]
Proof
  Cases_on `j.inst_opcode` >>
  simp[is_flippable_def, is_commutative_def, is_comparator_def] >>
  Cases_on `j.inst_operands` >> simp[flip_operands_def] >>
  Cases_on `t` >> simp[flip_operands_def] >>
  Cases_on `t'` >> simp[flip_operands_def, is_comparator_def,
                       flip_comparison_opcode_def]
QED

Theorem dft_label_flow_ok_closed_retention:
  o1_fn_shape ctx f /\ EVERY label_positions_ok (fn_insts f) /\
  (!i d x. MEM i (fn_insts (dft_fn f)) /\
           MEM (Var x) i.inst_operands /\ MEM d (fn_insts f) /\
           MEM x d.inst_outputs ==> MEM d (fn_insts (dft_fn f))) /\
  label_flow_ok (ctx with ctx_functions := [f]) ==>
  label_flow_ok (ctx with ctx_functions := [dft_fn f])
Proof
  strip_tac >> simp[label_flow_ok_def] >> gen_tac >> strip_tac >>
  `?j. MEM j (fn_insts f) /\
       (inst = j \/ (inst = flip_operands j /\ is_flippable j.inst_opcode))` by
    metis_tac[dft_shape_instruction_source] >>
  pop_assum strip_assume_tac >>
  `j.inst_opcode <> CODESIZE /\
   (!x. MEM (Var x) j.inst_operands /\ code_end_var f x ==>
     (j.inst_opcode = ASSIGN /\ j.inst_operands = [Var x]) \/
     (j.inst_opcode = CODECOPY /\ ?dst sz.
       j.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)) /\
   (j.inst_opcode = CODECOPY ==> ?dst src sz.
     j.inst_operands = [dst; src; sz] /\
     (src = Label "runtime_begin" \/ ?x. src = Var x /\ code_end_var f x))` by
    (gvs[label_flow_ok_def] >> metis_tac[]) >>
  gvs[]
  >- (conj_tac
      >- (rpt strip_tac >>
          `code_end_var f x` by metis_tac[dft_code_end_var_reflect] >>
          metis_tac[]) >>
      strip_tac >> gvs[] >>
      irule code_end_var_closed_retention >> metis_tac[MEM]) >>
  drule flip_operands_flow_opcodes >> simp[] >> strip_tac >>
  simp[] >> gen_tac >> spose_not_then strip_assume_tac >>
  `code_end_var f x` by metis_tac[dft_code_end_var_reflect] >>
  `MEM (Var x) j.inst_operands` by metis_tac[flip_operands_operand_mem] >>
  metis_tac[]
QED
