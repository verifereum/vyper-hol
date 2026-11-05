Theory bodyPtrTypeBuiltinsControlProbe
Ancestors
  exprLowering vyperCompiler compileEnv emitHelper ptrSafeRun
  bodyPtrTypeBuiltinsScalarTransfer fragGasPathPtr venomInst ptrDiscipline
  gasCount venomExecSemantics venomState fragGasSeqPtr

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

(* All three instruction checks are explicit; G is arbitrary, including
   an initial binding for %0.  The selected ASSIGN overwrites that binding. *)
Theorem literal_conditional_bounded_path:
  compile_expr ce (BaseT (UintT 256))
    (IfExp (BaseT (UintT 256)) (Literal (BaseT BoolT) (BoolL b))
      (Literal (BaseT (UintT 256)) (IntL 7))
      (Literal (BaseT (UintT 256)) (IntL 9)))
    (initial_compile_state "entry") = (vv, st) /\
  fn.fn_blocks = REVERSE st.cs_blocks ++
    [<|bb_label := st.cs_current_bb; bb_instructions := st.cs_current_insts|>] /\
  ~s.vs_halted /\ s.vs_current_bb = "entry" /\ s.vs_inst_idx = 0 /\
  i = <|inst_id := 0; inst_opcode := JNZ;
    inst_operands := [Lit (if b then 1w else 0w);
                     Label "@then_0"; Label "@else_1"]; inst_outputs := []|> /\
  j = <|inst_id := (if b then 1 else 3); inst_opcode := ASSIGN;
    inst_operands := [Lit (if b then 7w else 9w)]; inst_outputs := ["%0"]|> /\
  k = <|inst_id := (if b then 2 else 4); inst_opcode := JMP;
    inst_operands := [Label "@exit_2"]; inst_outputs := []|> /\
  s1 = jump_to (if b then "@then_0" else "@else_1") s /\
  u = update_var "%0" (if b then 7w else 9w) s1 /\
  s2 = (u with vs_inst_idx := 1) /\
  H = step_prov PG G j u /\ ts = step_taint j s1 u tn /\
  ptr_safe_step D lo 0 ctx fn PG G tn i s /\
  ptr_inst_ok D lo 0 ctx fn G tn j s1 /\
  ptr_safe_step D lo 0 ctx fn PG H ts k s2 ==>
  gas_path_ptr D lo ctx fn PG G tn s 0 H ts
    (OK (jump_to "@exit_2" s2)) /\ FLOOKUP H "%0" = NONE
Proof
  strip_tac >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME i` by
    (drule compile_literal_conditional_probe >> strip_tac >>
     gvs[lookup_block_def, get_instruction_def, listTheory.FIND_thm]) >>
  `?bb. lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
        get_instruction bb s1.vs_inst_idx = SOME j` by
    (drule compile_literal_conditional_probe >> strip_tac >>
     Cases_on `b` >>
     gvs[jump_to_def, lookup_block_def, get_instruction_def, listTheory.FIND_thm]) >>
  `?bb. lookup_block s2.vs_current_bb fn.fn_blocks = SOME bb /\
        get_instruction bb s2.vs_inst_idx = SOME k` by
    (drule compile_literal_conditional_probe >> strip_tac >>
     Cases_on `b` >> gvs[jump_to_def, update_var_def,
       lookup_block_def, get_instruction_def, listTheory.FIND_thm]) >>
  `step_inst 0 ctx i s = OK s1` by
    (simp[step_inst_non_invoke] >> Cases_on `b` >>
     gvs[step_inst_base_def, eval_operand_def]) >>
  `step_inst_base j s1 = OK u` by
    simp[step_inst_base_def, eval_operand_def] >>
  `step_inst 0 ctx k s2 = OK (jump_to "@exit_2" s2)` by
    simp[step_inst_non_invoke, step_inst_base_def] >>
  `~s1.vs_halted /\ ~s2.vs_halted /\ s1.vs_inst_idx = 0` by
    gvs[jump_to_def, update_var_def] >>
  `gas_path_ptr D lo ctx fn PG G tn s 0 G tn (OK s1)` by
    (qpat_x_assum `s1 = _` SUBST_ALL_TAC >>
     irule checked_partial_jump_path >> simp[] >>
     qexists_tac `i` >> gvs[]) >>
  `gas_path_ptr D lo ctx fn PG H ts s2 0 H ts
     (OK (jump_to "@exit_2" s2))` by
    (irule checked_partial_jump_path >> simp[] >>
     qexists_tac `k` >> gvs[]) >>
  `gas_path_ptr D lo ctx fn PG G tn s1 0 H ts
     (OK (jump_to "@exit_2" s2))` by
    (drule_at (Pat `step_inst_base _ _ = _`) gas_path_ptr_step >>
     simp[is_terminator_def] >> disch_then irule >> gvs[]) >>
  conj_tac
  >- metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES] >>
  gvs[] >> irule step_prov_output_none >>
  simp[out_prov_def, first_prov_def, op_prov_def]
QED

(* The normal simulation continuation is exit_2:0, not an arbitrary path
   prefix.  In particular the reflexive entry path and the partial JNZ
   edge cannot alone satisfy that continuation.  Partial JMP to exit is
   sufficient here because the exit's PHI prefix is empty. *)
Theorem literal_conditional_continuation_probe:
  compile_expr ce (BaseT (UintT 256))
    (IfExp (BaseT (UintT 256)) (Literal (BaseT BoolT) (BoolL b))
      (Literal (BaseT (UintT 256)) (IntL 7))
      (Literal (BaseT (UintT 256)) (IntL 9)))
    (initial_compile_state "entry") = (vv, st) /\
  s.vs_current_bb = "entry" ==>
  (jump_to "@exit_2" t).vs_current_bb = st.cs_current_bb /\
  (jump_to "@exit_2" t).vs_inst_idx = LENGTH st.cs_current_insts /\
  s.vs_current_bb <> st.cs_current_bb /\
  (jump_to (if b then "@then_0" else "@else_1") s).vs_current_bb <>
    st.cs_current_bb
Proof
  strip_tac >> drule compile_literal_conditional_probe >> strip_tac >>
  Cases_on `b` >> gvs[jump_to_def]
QED
