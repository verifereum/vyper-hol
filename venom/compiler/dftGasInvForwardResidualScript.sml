Theory dftGasInvForwardResidual
Ancestors
  dftGasInvForwardEffects dftGasInvInitializedTerminals dftGasInvAliasPaths
  dftGasInvStackLineage dftDefs dftRunRel dftCorrectness dftIdempotent
  passSharedDefs venomWf venomInst relation list rich_list contextCodegenRel
  dftGasInvRevertChildOrder dftGasInvForwardConeProbe

Theorem inv_path_terminal_producer:
  RTC (inv_assign_edge bi) a b /\ operand_producer bi b = SOME prod /\
  prod.inst_opcode <> ASSIGN ==>
  inv_terminal_producer bi a prod
Proof
  strip_tac >> simp[inv_terminal_producer_def] >> qexists `b` >>
  simp[inv_alias_terminal_def] >>
  Cases_on `b` >> gvs[operand_producer_def, inv_assign_edge_def]
QED

Theorem inv_forward_initialized_residual:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  revert_forward_pair bb i j /\
  get_instruction bb i = SOME copy /\ copy.inst_operands = [p;src;n] /\
  get_instruction bb j = SOME rev /\ rev.inst_operands = [q;m] /\
  st = inv_line_state bb.bb_instructions [] (dft_eda bb.bb_instructions)
    (build_offspring_map bb.bb_instructions []) T
    (entry_instructions bb.bb_instructions [] (dft_eda bb.bb_instructions)) ticks /\
  MEM copy st.ds_output /\
  (RTC (inv_assign_edge bb.bb_instructions) q b \/
   RTC (inv_assign_edge bb.bb_instructions) m b) /\
  operand_producer bb.bb_instructions b = SOME prod ==>
  prod.inst_opcode = ASSIGN \/ is_pseudo prod.inst_opcode \/
  (MEM prod.inst_id (MAP (\z. z.inst_id) st.ds_output) /\
   MEM prod.inst_id st.ds_visited /\
   ~MEM prod.inst_id (stack_emit_ids st.ds_stack))
Proof
  strip_tac >> Cases_on `prod.inst_opcode = ASSIGN` >> simp[] >>
  Cases_on `is_pseudo prod.inst_opcode` >> simp[] >>
  `inv_terminal_producer bb.bb_instructions q prod \/
   inv_terminal_producer bb.bb_instructions m prod` by
    metis_tac[inv_path_terminal_producer] >>
  metis_tac[inv_forward_initialized_terminals]
QED

Theorem inv_assign_path_children:
  ALL_DISTINCT (MAP (\z. z.inst_id) bi) /\ EVERY inst_wf bi /\
  RTC (inv_assign_edge bi) a b /\ operand_producer bi b = SOME prod /\
  prod.inst_opcode = ASSIGN /\
  MEM dep (inst_all_deps bi [] (dft_eda bi) prod) ==>
  ?c. RTC (inv_assign_edge bi) a c /\ operand_producer bi c = SOME dep
Proof
  strip_tac >>
  Cases_on `b` >> gvs[operand_producer_def] >> rename1 `producing_inst bi v = SOME prod` >>
  `MEM prod bi /\ MEM v prod.inst_outputs` by metis_tac[producing_inst_unique] >>
  `inst_wf prod` by metis_tac[EVERY_MEM] >>
  `LENGTH prod.inst_outputs = 1 /\ LENGTH prod.inst_operands = 1` by
    gvs[inst_wf_def] >>
  `prod.inst_outputs = [v]` by
    (Cases_on `prod.inst_outputs` >> gvs[] >> Cases_on `t` >> gvs[]) >>
  `?c. prod.inst_operands = [c]` by
    (Cases_on `prod.inst_operands` >> gvs[] >> Cases_on `t` >> gvs[]) >>
  `inv_assign_edge bi (Var v) c` by
    (simp[inv_assign_edge_def] >> metis_tac[]) >>
  `RTC (inv_assign_edge bi) a c` by metis_tac[RTC_TRANS, RTC_SINGLE] >>
  `MEM dep (inst_data_deps bi [] prod)` by metis_tac[inv_assign_all_deps] >>
  qexists `c` >> simp[] >>
  gvs[inst_data_deps_def, python_stack_operands_def, ir_specific_operand_order_def,
      is_terminator_def, nub_first_def, nub_def, AllCaseEqs()] >>
  Cases_on `operand_producer bi c` >> gvs[]
QED

Theorem inv_forward_residual_children:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  (RTC (inv_assign_edge bb.bb_instructions) q b \/
   RTC (inv_assign_edge bb.bb_instructions) m b) /\
  operand_producer bb.bb_instructions b = SOME prod /\
  prod.inst_opcode = ASSIGN /\
  MEM dep (inst_all_deps bb.bb_instructions [] (dft_eda bb.bb_instructions) prod) ==>
  ?c. (RTC (inv_assign_edge bb.bb_instructions) q c \/
       RTC (inv_assign_edge bb.bb_instructions) m c) /\
      operand_producer bb.bb_instructions c = SOME dep
Proof
  strip_tac >>
  `EVERY inst_wf bb.bb_instructions` by
    (gvs[dft_fn_rel_def, fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP (\z. z.inst_id) bb.bb_instructions)` by
    (irule bb_inst_ids_distinct >> gvs[dft_fn_rel_def] >> metis_tac[]) >>
  metis_tac[inv_assign_path_children]
QED

(* Literal origins end the path without producing a work item, including
   the literal COPY/data-child tie example. *)
Theorem inv_residual_literal_check:
  inv_assign_edge inv_child_tie_bi (Var "p") (Lit 32w) /\
  operand_producer inv_child_tie_bi (Lit 32w) = NONE /\
  inst_all_deps inv_child_tie_bi [] (dft_eda inv_child_tie_bi)
    (EL 1 inv_child_tie_bi) = []
Proof
  EVAL_TAC >> simp[]
QED

(* PARAM processing marks it visited but skips emission. *)
Theorem inv_residual_pseudo_check:
  inv_assign_edge inv_pseudo_terminal_block (Var "alias") (Var "external") /\
  inst_all_deps inv_pseudo_terminal_block [] (dft_eda inv_pseudo_terminal_block)
    (EL 1 inv_pseudo_terminal_block) = [EL 0 inv_pseudo_terminal_block] /\
  MEM 2 (inv_terminal_check_state inv_pseudo_terminal_block).ds_visited /\
  ~MEM 2 (MAP (\z. z.inst_id)
    (inv_terminal_check_state inv_pseudo_terminal_block).ds_output) /\
  is_pseudo (EL 0 inv_pseudo_terminal_block).inst_opcode
Proof
  EVAL_TAC >> simp[]
QED

(* Distinct operand paths, reusing the earlier forwarding block. *)
Theorem inv_residual_distinct_paths_check:
  inv_assign_edge (EL 1 inv_cone_blocks).bb_instructions (Var "p3") (Var "p2") /\
  inv_assign_edge (EL 1 inv_cone_blocks).bb_instructions (Var "p2") (Var "p") /\
  inv_assign_edge (EL 1 inv_cone_blocks).bb_instructions (Var "s2") (Var "sz") /\
  inst_all_deps (EL 1 inv_cone_blocks).bb_instructions []
    (dft_eda (EL 1 inv_cone_blocks).bb_instructions)
    (EL 6 (EL 1 inv_cone_blocks).bb_instructions) =
      [EL 5 (EL 1 inv_cone_blocks).bb_instructions]
Proof
  EVAL_TAC >> simp[]
QED
