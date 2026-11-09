(* Counterexample to unrestricted endpoint preservation, NOT to the frozen
   existential expression/statement simulation.  No source post is claimed. *)
Theory augAssignPtrEndpointReentry
Ancestors
  augAssignPtrScalarJoin fragGasPathPtr fragExec compileEnv venomInst venomWf
  venomState venomExecSemantics ptrDiscipline finite_map list pred_set

Theorem tagged_suffix_layout:
  fn = mk_raw_function "loop_fn"
    [<|bb_label := "loop"; bb_instructions :=
       [mk_inst 0 ASSIGN [Var "p"] ["r"];
        mk_inst 1 JMP [Label "loop"] []]|>] /\
  st.cs_blocks = [] /\ st.cs_current_bb = "loop" /\
  st.cs_current_insts = [] ==>
  fn_inst_ids_distinct fn /\ fn_has_code st st fn
Proof
  strip_tac >>
  simp[fn_inst_ids_distinct_def, fn_has_code_def, emitted_blocks_def,
       mk_raw_function_def, mk_inst_def, lookup_block_def, FIND_thm]
QED

Theorem tagged_suffix_path:
  fn = mk_raw_function "loop_fn"
    [<|bb_label := "loop"; bb_instructions :=
       [mk_inst 0 ASSIGN [Var "p"] ["r"];
        mk_inst 1 JMP [Label "loop"] []]|>] /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = "loop" /\ s.vs_inst_idx = 0 /\
  lookup_var "p" s = SOME w /\
  G = FEMPTY |+ ("p",(0,32)) ==>
  ?H tm u.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK u) /\
    op_prov G (Var "r") = NONE /\ op_prov H (Var "r") <> NONE /\
    u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = 0
Proof
  strip_tac >>
  qmatch_asmsub_abbrev_tac `fn = mk_raw_function nm [bb]` >>
  qabbrev_tac `i = mk_inst 0 ASSIGN [Var "p"] ["r"]` >>
  qabbrev_tac `v = update_var "r" w s` >>
  qabbrev_tac `s1 = v with vs_inst_idx := 1` >>
  qabbrev_tac `H = step_prov PG G i v` >>
  qabbrev_tac `tm = step_taint i s v tn` >>
  `step_inst_base i s = OK v` by
    simp[Abbr `i`, Abbr `v`, step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def] >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0 H tm (OK s1)` by
    (unabbrev_all_tac >>
     `1 = SUC s.vs_inst_idx` by simp[] >> pop_assum SUBST1_TAC >>
     irule assign_ptr_edge >>
     simp[mk_raw_function_def, lookup_block_def, FIND_thm, get_instruction_def] >>
     metis_tac[]) >>
  `~s1.vs_halted` by simp[Abbr `s1`, Abbr `v`, update_var_def] >>
  `gas_path_ptr_edge D 0 ctx fn PG H tm s1 0 H tm
     (OK (jump_to "loop" s1))` by
    (irule jump_ptr_edge >>
     simp[Abbr `s1`, Abbr `v`, update_var_def, mk_raw_function_def,
          Abbr `bb`, Abbr `nm`, lookup_block_def, FIND_thm, get_instruction_def] >>
     metis_tac[]) >>
  qexistsl_tac [`H`, `tm`, `jump_to "loop" s1`] >> conj_tac
  >- (`gas_path_ptr D 0 ctx fn PG H tm (jump_to "loop" s1) 0 H tm
        (OK (jump_to "loop" s1))` by
        (irule (cj 1 gas_path_ptr_rules) >> simp[jump_to_def]) >>
      metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]) >>
  simp[Abbr `H`, Abbr `i`, Abbr `s1`, Abbr `v`, update_var_def,
       jump_to_def, step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       op_prov_def, mk_inst_def, FLOOKUP_UPDATE]
QED

Theorem endpoint_reentry_counterexample:
  ?ctx fn G H tm s u st.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK u) /\
    op_prov G (Var "r") = NONE /\ op_prov H (Var "r") <> NONE /\
    s.vs_current_bb = u.vs_current_bb /\
    s.vs_inst_idx = 0 /\ u.vs_inst_idx = 0 /\
    fn_inst_ids_distinct fn /\ fn_has_code st st fn /\
    st.cs_current_bb = s.vs_current_bb /\ st.cs_current_insts = []
Proof
  qabbrev_tac `ctx = ctx0 with ctx_functions := []` >>
  qabbrev_tac `fn = mk_raw_function "loop_fn"
    [<|bb_label := "loop"; bb_instructions :=
       [mk_inst 0 ASSIGN [Var "p"] ["r"];
        mk_inst 1 JMP [Label "loop"] []]|>]` >>
  qabbrev_tac `s = s0 with <|vs_current_bb := "loop"; vs_inst_idx := 0;
    vs_halted := F; vs_vars := FEMPTY |+ ("p",0w)|>` >>
  qabbrev_tac `st = st0 with <|cs_current_bb := "loop"; cs_current_insts := [];
    cs_blocks := []|>` >>
  `?H tm u.
    gas_path_ptr D 0 ctx fn PG (FEMPTY |+ ("p",(0,32))) tn s 0 H tm (OK u) /\
    op_prov (FEMPTY |+ ("p",(0,32))) (Var "r") = NONE /\
    op_prov H (Var "r") <> NONE /\
    u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = 0` by
    (irule tagged_suffix_path >>
     simp[Abbr `ctx`, Abbr `fn`, Abbr `s`, ctx_has_dalloca_def,
          lookup_var_def, FLOOKUP_UPDATE]) >>
  pop_assum strip_assume_tac >>
  qexistsl_tac [`ctx`, `fn`, `FEMPTY |+ ("p",(0,32))`, `H`, `tm`, `s`, `u`, `st`] >>
  simp[Abbr `s`, Abbr `st`] >>
  irule tagged_suffix_layout >> simp[Abbr `fn`]
QED
