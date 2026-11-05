Theory bodyPtrTypeBuiltinsControlProbe
Ancestors
  exprLowering vyperCompiler compileEnv emitHelper ptrSafeRun
  bodyPtrTypeBuiltinsScalarTransfer fragGasPathPtr venomInst ptrDiscipline
  gasCount venomExecSemantics venomState

(* A literal conditional exercises the actual compiler's branching layout;
   the environment is deliberately unrestricted. *)
Theorem compile_literal_conditional_probe:
  compile_expr ce (BaseT (UintT 256))
    (IfExp (BaseT (UintT 256)) (Literal (BaseT BoolT) (BoolL b))
      (Literal (BaseT (UintT 256)) (IntL 7))
      (Literal (BaseT (UintT 256)) (IntL 9)))
    (initial_compile_state "entry") = (vv, st) ==>
  vv = StackValue (BaseT (UintT 256)) (Var "%0") /\
  st = <| cs_next_var := 1; cs_next_label := 3; cs_next_id := 5;
    cs_current_bb := "@exit_2"; cs_current_insts := [];
    cs_data_sections := [];
    cs_blocks :=
    [<|bb_label := "@else_1"; bb_instructions :=
      [<|inst_id := 3; inst_opcode := ASSIGN; inst_operands := [Lit 9w];
         inst_outputs := ["%0"]|>;
       <|inst_id := 4; inst_opcode := JMP; inst_operands := [Label "@exit_2"];
         inst_outputs := []|>]|>;
     <|bb_label := "@then_0"; bb_instructions :=
      [<|inst_id := 1; inst_opcode := ASSIGN; inst_operands := [Lit 7w];
         inst_outputs := ["%0"]|>;
       <|inst_id := 2; inst_opcode := JMP; inst_operands := [Label "@exit_2"];
         inst_outputs := []|>]|>;
     <|bb_label := "entry"; bb_instructions :=
      [<|inst_id := 0; inst_opcode := JNZ;
         inst_operands := [Lit (if b then 1w else 0w);
                           Label "@then_0"; Label "@else_1"];
         inst_outputs := []|>]|>] |>
Proof
  Cases_on `b` >> EVAL_TAC >> strip_tac >> gvs[] >>
  CONV_TAC (DEPTH_CONV wordsLib.WORD_EVAL_CONV) >> simp[]
QED

Theorem literal_conditional_arm_producer:
  compile_expr ce (BaseT (UintT 256))
    (IfExp (BaseT (UintT 256)) (Literal (BaseT BoolT) (BoolL b))
      (Literal (BaseT (UintT 256)) (IntL 7))
      (Literal (BaseT (UintT 256)) (IntL 9)))
    (initial_compile_state "entry") = (vv, st) /\
  fn.fn_blocks = REVERSE st.cs_blocks ++
    [<|bb_label := st.cs_current_bb; bb_instructions := st.cs_current_insts|>] /\
  s.vs_current_bb = (if b then "@then_0" else "@else_1") /\
  s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i ==>
  i.inst_opcode = ASSIGN /\ i.inst_outputs = ["%0"] /\
  i.inst_operands = [Lit (if b then 7w else 9w)]
Proof
  strip_tac >> drule compile_literal_conditional_probe >> strip_tac >>
  Cases_on `b` >> gvs[lookup_block_def, get_instruction_def, listTheory.FIND_thm]
QED

Theorem literal_conditional_entry_prov:
  compile_expr ce (BaseT (UintT 256))
    (IfExp (BaseT (UintT 256)) (Literal (BaseT BoolT) (BoolL b))
      (Literal (BaseT (UintT 256)) (IntL 7))
      (Literal (BaseT (UintT 256)) (IntL 9)))
    (initial_compile_state "entry") = (vv, st) /\
  fn.fn_blocks = REVERSE st.cs_blocks ++
    [<|bb_label := st.cs_current_bb; bb_instructions := st.cs_current_insts|>] ==>
  entry_prov fn s G = G
Proof
  strip_tac >> drule compile_literal_conditional_probe >> strip_tac >>
  gvs[entry_prov_def, lookup_block_def, phis_prov_def, listTheory.FIND_thm] >>
  rpt IF_CASES_TAC >> simp[phis_prov_def]
QED

Theorem literal_assign_edge_none:
  gas_path_ptr_edge D lo ctx fn PG G tn s n H ts (OK t) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode = ASSIGN /\ i.inst_outputs = [x] /\
  i.inst_operands = [Lit w] ==>
  FLOOKUP H x = NONE
Proof
  strip_tac >>
  gvs[gas_path_ptr_edge_def, is_terminator_def, fragExecTheory.exit_result_def]
  >- (gvs[Once ghost_step_def] >> irule step_prov_output_none >>
      simp[out_prov_def, first_prov_def, op_prov_def]) >>
  qpat_x_assum `OK t = _` (assume_tac o SYM) >>
  gvs[fragExecTheory.exit_result_def]
QED

(* Raw partial-jump interface: unlike the emit-based statement helpers,
   this uses fetched instructions and makes the pointer check explicit. *)
Theorem checked_partial_jump_path:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  MEM i.inst_opcode [JNZ; JMP] /\
  step_inst 0 ctx i s = OK (jump_to lbl s) /\
  ptr_safe_step D lo 0 ctx fn PG G tn i s ==>
  gas_path_ptr D lo ctx fn PG G tn s 0 G tn (OK (jump_to lbl s))
Proof
  strip_tac >>
  `gas_path_ptr_edge D lo ctx fn PG G tn s 0 G tn
    (OK (jump_to lbl s))` by
    (rewrite_tac[gas_path_ptr_edge_def] >> simp[] >>
     qexists_tac `0` >> simp[gas_count_step_def] >>
     gvs[] >> simp[is_terminator_def] >> metis_tac[]) >>
  `~(jump_to lbl s).vs_halted` by simp[jump_to_def] >>
  metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]
QED
