Theory bodyPtrTypeBuiltinsSuffixProbe
Ancestors
  bodyPtrTypeBuiltinsControlProbe bodyPtrTypeBuiltinsEmbeddingProbe
  fragGasSeqPtr fragGasPathPtr ptrSafeRun ptrDiscipline venomExecSemantics
  venomState venomInst venomWf fragExec emitHelper compileEnv vyperCompiler
  contextCodegenRel codegenRel

(* A non-PHI at the front of a Name block prevents a jump from skipping
   the MLOAD. This is deliberately not an all-path dominance theorem. *)
Theorem name_jump_cannot_skip_load:
  i.inst_opcode = MLOAD ==>
  phi_prefix_length (i::rest) = 0 /\
  (jump_to lbl s).vs_inst_idx = 0
Proof
  simp[phi_prefix_length_def, jump_to_def]
QED

(* A continuation at index zero, in contrast, admits this suffix loop.
   Pointer checks remain explicit: no body simulation premise is claimed. *)
Theorem assign_suffix_return_path:
  ~s.vs_halted /\ s.vs_current_bb = lbl /\ s.vs_inst_idx = 0 /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  bb.bb_instructions = [i; j] /\
  i.inst_opcode = ASSIGN /\ i.inst_operands = [Var p] /\
  i.inst_outputs = [x] /\
  j.inst_opcode = JMP /\ j.inst_operands = [Label lbl] /\
  lookup_var p s = SOME w /\ FLOOKUP G p = SOME site /\
  u = update_var x w s /\ t = (u with vs_inst_idx := 1) /\
  H = step_prov PG G i u /\ ts = step_taint i s u tn /\
  ptr_inst_ok D lo 0 ctx fn G tn i s /\
  ptr_safe_step D lo 0 ctx fn PG H ts j t ==>
  gas_path_ptr D lo ctx fn PG G tn s 0 H ts
    (OK (jump_to lbl t)) /\ FLOOKUP H x = SOME site /\
  (jump_to lbl t).vs_inst_idx = 0 /\
  (jump_to lbl t).vs_current_bb = lbl
Proof
  strip_tac >>
  `step_inst_base i s = OK u` by
    gvs[step_inst_base_def, eval_operand_def] >>
  `step_inst 0 ctx j t = OK (jump_to lbl t)` by
    simp[step_inst_non_invoke, step_inst_base_def] >>
  `gas_path_ptr D lo ctx fn PG H ts t 0 H ts
    (OK (jump_to lbl t))` by
    (irule checked_partial_jump_path >>
     conj_tac >- gvs[update_var_def] >>
     qexistsl_tac [`bb`, `j`] >>
     gvs[get_instruction_def, update_var_def, jump_to_def]) >>
  `gas_path_ptr D lo ctx fn PG G tn s 0 H ts
    (OK (jump_to lbl t))` by
    (drule_at (Pat `step_inst_base _ _ = _`) gas_path_ptr_step >>
     simp[is_terminator_def] >> disch_then irule >>
     gvs[get_instruction_def]) >>
  gvs[jump_to_def, step_prov_def, set_prov_def, out_prov_def,
      first_prov_def, op_prov_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem literal_conditional_suffix_embedding:
  compile_expr ce (BaseT (UintT 256))
    (IfExp (BaseT (UintT 256)) (Literal (BaseT BoolT) (BoolL b))
      (Literal (BaseT (UintT 256)) (IntL 7))
      (Literal (BaseT (UintT 256)) (IntL 9)))
    (initial_compile_state "entry") = (vv, st) /\
  i = <|inst_id := 5; inst_opcode := ASSIGN;
        inst_operands := [Var p]; inst_outputs := ["%0"]|> /\
  j = <|inst_id := 6; inst_opcode := JMP;
        inst_operands := [Label "@exit_2"]; inst_outputs := []|> /\
  fn.fn_blocks = REVERSE st.cs_blocks ++
    [<|bb_label := st.cs_current_bb; bb_instructions := [i; j]|>] ==>
  fn_has_code (initial_compile_state "entry") st fn /\
  fn_inst_ids_distinct fn /\
  st.cs_current_bb = "@exit_2" /\ LENGTH st.cs_current_insts = 0
Proof
  strip_tac >> drule compile_literal_conditional_probe >> strip_tac >>
  gvs[fn_has_code_def, emitted_blocks_def, initial_compile_state_def,
      lookup_block_def, listTheory.FIND_thm, fn_inst_ids_distinct_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem suffix_copy_check:
  i.inst_opcode = ASSIGN /\ i.inst_operands = [Var p] /\
  i.inst_outputs = [x] /\ lookup_var p s = SOME w /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ptr_inst_ok D lo fuel ctx fn G tn i s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       step_inst_non_invoke, step_inst_base_def, eval_operand_def,
       update_var_def]
QED

Theorem suffix_jump_check:
  i.inst_opcode = JMP /\ i.inst_operands = [Label lbl] /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ptr_safe_step D lo fuel ctx fn PG G tn i s
Proof
  strip_tac >>
  simp[Once ptr_safe_defs] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, op_taint_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       step_inst_non_invoke, step_inst_base_def, jump_to_def]
QED

(* No ghost-absence premise on the copied pointer is hidden in these
   checks. The only resource side condition is the usual allocation frame. *)
Theorem suffix_can_reintroduce_provenance:
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = [i; j] /\
  i.inst_opcode = ASSIGN /\ i.inst_operands = [Var p] /\
  i.inst_outputs = [x] /\
  j.inst_opcode = JMP /\ j.inst_operands = [Label s.vs_current_bb] /\
  lookup_var p s = SOME w /\ FLOOKUP G p = SOME site /\
  FLOOKUP G x = NONE /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?H ts t.
    gas_path_ptr D lo ctx fn PG G tn s 0 H ts (OK t) /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = 0 /\
    FLOOKUP H x = SOME site
Proof
  strip_tac >>
  `ptr_inst_ok D lo 0 ctx fn G tn i s` by
    (irule suffix_copy_check >> simp[] >> metis_tac[]) >>
  qabbrev_tac `u = update_var x w s` >>
  qabbrev_tac `v = u with vs_inst_idx := 1` >>
  qabbrev_tac `H = step_prov PG G i u` >>
  qabbrev_tac `ts = step_taint i s u tn` >>
  `ptr_safe_step D lo 0 ctx fn PG H ts j v` by
    (irule suffix_jump_check >>
     gvs[Abbr `v`, Abbr `u`, allocas_from_def, allocas_below_fmp_def,
         update_var_def] >> metis_tac[]) >>
  `u = update_var x w s /\ v = (u with vs_inst_idx := 1) /\
   H = step_prov PG G i u /\ ts = step_taint i s u tn` by
    simp[Abbr `u`, Abbr `v`, Abbr `H`, Abbr `ts`] >>
  `s.vs_current_bb = s.vs_current_bb` by simp[] >>
  drule_all assign_suffix_return_path >> metis_tac[]
QED
