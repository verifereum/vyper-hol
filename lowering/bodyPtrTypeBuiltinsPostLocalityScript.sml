Theory bodyPtrTypeBuiltinsPostLocality
Ancestors
  bodyPtrTypeBuiltinsSuffixProbe bodyPtrTypeBuiltinsControlProbe loweringPosts valueEncoding vyperValue
  fragGasSeqPtr fragGasPathPtr ptrSafeRun ptrDiscipline venomExecSemantics
  venomState venomInst finite_map compileEnv integer words

Libs intLib wordsLib

(* A machine-path diagnostic only: no compilation or source frame is asserted. *)
Theorem scalar_copy_return_path:
  ~s.vs_halted /\ s.vs_current_bb = lbl /\ s.vs_inst_idx = 0 /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  bb.bb_instructions = [i; j] /\
  i.inst_opcode = ASSIGN /\ i.inst_operands = [Var p] /\
  i.inst_outputs = [x] /\
  j.inst_opcode = JMP /\ j.inst_operands = [Label lbl] /\
  lookup_var p s = SOME w /\
  u = update_var x w s /\ t = (u with vs_inst_idx := 1) /\
  H = step_prov PG G i u /\ ts = step_taint i s u tn /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  gas_path_ptr D lo ctx fn PG G tn s 0 H ts (OK (jump_to lbl t))
Proof
  strip_tac >>
  `step_inst_base i s = OK u` by
    gvs[step_inst_base_def, eval_operand_def] >>
  `step_inst 0 ctx j t = OK (jump_to lbl t)` by
    simp[step_inst_non_invoke, step_inst_base_def] >>
  `ptr_inst_ok D lo 0 ctx fn G tn i s` by
    (irule suffix_copy_check >> metis_tac[]) >>
  `ptr_safe_step D lo 0 ctx fn PG H ts j t` by
    (irule suffix_jump_check >>
     gvs[allocas_from_def, allocas_below_fmp_def, update_var_def] >>
     metis_tac[]) >>
  `gas_path_ptr D lo ctx fn PG H ts t 0 H ts
    (OK (jump_to lbl t))` by
    (irule checked_partial_jump_path >>
     conj_tac >- gvs[update_var_def] >>
     qexistsl_tac [`bb`, `j`] >>
     gvs[get_instruction_def, update_var_def, jump_to_def]) >>
  drule_at (Pat `step_inst_base _ _ = _`) gas_path_ptr_step >>
  simp[is_terminator_def] >> disch_then irule >>
  gvs[get_instruction_def]
QED

Theorem scalar_value_zero_count_counterexample:
  !cx. ?ctx fn PG G tn s H ts t.
    gas_path_ptr (ARB:dead) 0 ctx fn PG G tn s 0 H ts (OK t) /\
    s.vs_current_bb = t.vs_current_bb /\
    s.vs_inst_idx = 0 /\ t.vs_inst_idx = 0 /\
    expr_val_rel cx (BaseT (UintT 256)) (IntV 7) (Var "%probe_result") t /\
    ~expr_val_rel cx (BaseT (UintT 256)) (IntV 7) (Var "%probe_result") s
Proof
  gen_tac >>
  qabbrev_tac `i = <|inst_id := 0; inst_opcode := ASSIGN;
    inst_operands := [Var "%probe_source"]; inst_outputs := ["%probe_result"]|>` >>
  qabbrev_tac `j = <|inst_id := 1; inst_opcode := JMP;
    inst_operands := [Label "loop"]; inst_outputs := []|>` >>
  qabbrev_tac `bb = <|bb_label := "loop"; bb_instructions := [i;j]|>` >>
  qabbrev_tac `fn = ARB with fn_blocks := [bb]` >>
  qabbrev_tac `ctx = ARB with ctx_functions := []` >>
  qabbrev_tac `s = ARB with <|vs_halted := F; vs_current_bb := "loop";
    vs_inst_idx := 0; vs_allocas := FEMPTY;
    vs_vars := FEMPTY |+ ("%probe_source",7w) |+ ("%probe_result",9w)|>` >>
  qabbrev_tac `u = update_var "%probe_result" 7w s` >>
  qabbrev_tac `a = u with vs_inst_idx := 1` >>
  qabbrev_tac `H = step_prov (ARB) FEMPTY i u` >>
  qabbrev_tac `ts = step_taint i s u (ARB)` >>
  `gas_path_ptr (ARB:dead) 0 ctx fn ARB FEMPTY ARB s 0 H ts
    (OK (jump_to "loop" a))` by
    (irule scalar_copy_return_path >>
     simp[Abbr `fn`, Abbr `bb`, Abbr `i`, Abbr `j`, Abbr `ctx`,
          Abbr `s`, Abbr `u`, Abbr `a`, Abbr `H`, Abbr `ts`,
          lookup_block_def, listTheory.FIND_thm, lookup_var_def,
          allocas_from_def, ctx_has_dalloca_def, FLOOKUP_UPDATE]) >>
  qexistsl_tac [`ctx`, `fn`, `ARB`, `FEMPTY`, `ARB`, `s`, `H`, `ts`,
                 `jump_to "loop" a`] >>
  simp[Abbr `s`, Abbr `a`, Abbr `u`, jump_to_def, update_var_def,
       expr_val_rel_def, eval_operand_def, lookup_var_def,
       vyperValueTheory.evaluate_type_def, is_word_type_def,
       typed_val_to_w256_def, val_to_w256_def, FLOOKUP_UPDATE] >> EVAL_TAC
QED

(* Same PC and zero counted gas alone do not transport semantic posts.
   This omits compilation from sa, expr_body_pre, stmt_state_rel,
   ghost_inv, and body_inv for the actual context. It is not a
   counterexample to type_builtin_expr_ptr_ok. *)
Theorem scalar_value_backward_locality_false:
  !cx. ~(!ctx fn PG G tn s H ts t.
    gas_path_ptr (ARB:dead) 0 ctx fn PG G tn s 0 H ts (OK t) /\
    s.vs_current_bb = t.vs_current_bb /\
    s.vs_inst_idx = 0 /\ t.vs_inst_idx = 0 /\
    expr_val_rel cx (BaseT (UintT 256)) (IntV 7) (Var "%probe_result") t ==>
    expr_val_rel cx (BaseT (UintT 256)) (IntV 7) (Var "%probe_result") s)
Proof
  gen_tac >>
  qspec_then `cx` strip_assume_tac scalar_value_zero_count_counterexample >>
  metis_tac[]
QED
