(* Concrete continuation-only diagnostic. These definitions name the small
   looping machine so the checked witness is readable; they are not a new
   simulation interface. No claim about a compiled expression's full post. *)
Theory assignBasePtrStoppingProbe
Ancestors bodyPtrDefs fragGasPathPtr venomExecSemantics ptrSafeRun
  ptrDiscipline gasCount fragExec venomInst venomState list finite_map words

Definition stopping_probe_fn_def:
  stopping_probe_fn = (ARB:ir_function) with fn_blocks :=
    [<|bb_label := "loop"; bb_instructions :=
       [mk_inst 0 ASSIGN [Lit 32w] ["p"];
        mk_inst 1 JMP [Label "loop"] []]|>]
End

Definition stopping_probe_cs_def:
  stopping_probe_cs = (ARB:compile_state) with
    <|cs_current_bb := "loop"; cs_current_insts := []; cs_blocks := []|>
End

Definition stopping_probe_state_def:
  stopping_probe_state = (ARB:venom_state) with
    <|vs_current_bb := "loop"; vs_inst_idx := 0; vs_halted := F;
      vs_vars := FEMPTY |+ ("p",0w); vs_allocas := FEMPTY|>
End

Theorem assign_base_ptr_stopping_layout:
  fn_has_code stopping_probe_cs stopping_probe_cs stopping_probe_fn /\
  fn_inst_ids_distinct stopping_probe_fn
Proof
  simp[fn_has_code_def, emitted_blocks_def, stopping_probe_cs_def,
       stopping_probe_fn_def, lookup_block_def, FIND_thm] >>
  EVAL_TAC >> metis_tac[]
QED

Theorem assign_base_ptr_stopping_steps:
  !ctx.
    step_inst 0 ctx (mk_inst 0 ASSIGN [Lit 32w] ["p"])
      stopping_probe_state =
      OK (update_var "p" 32w stopping_probe_state) /\
    step_inst 0 ctx (mk_inst 1 JMP [Label "loop"] [])
      ((update_var "p" 32w stopping_probe_state) with vs_inst_idx := 1) =
      OK (jump_to "loop" ((update_var "p" 32w stopping_probe_state)
        with vs_inst_idx := 1))
Proof
  EVAL_TAC >> simp[]
QED

Theorem assign_base_ptr_stopping_safe:
  !D ctx PG.
    ~ctx_has_dalloca ctx ==>
    ptr_safe_step D 0 0 ctx stopping_probe_fn PG FEMPTY entry_taint
      (mk_inst 0 ASSIGN [Lit 32w] ["p"]) stopping_probe_state /\
    ptr_safe_step D 0 0 ctx stopping_probe_fn PG FEMPTY entry_taint
      (mk_inst 1 JMP [Label "loop"] [])
      ((update_var "p" 32w stopping_probe_state) with vs_inst_idx := 1)
Proof
  rpt strip_tac >>
  simp[ptr_safe_step_def, ptr_inst_ok_def] >> EVAL_TAC >> simp[]
QED

Theorem assign_base_ptr_stopping_assign_edge:
  !D ctx PG.
    ~ctx_has_dalloca ctx ==>
    ?G tn. gas_path_ptr_edge D 0 ctx stopping_probe_fn PG
      FEMPTY entry_taint stopping_probe_state 0 G tn
      (OK ((update_var "p" 32w stopping_probe_state) with vs_inst_idx := 1))
Proof
  rpt strip_tac >>
  Cases_on `ghost_step 0 ctx PG FEMPTY entry_taint
    (mk_inst 0 ASSIGN [Lit 32w] ["p"]) stopping_probe_state` >>
  qexistsl_tac [`q`, `r`] >>
  simp[gas_path_ptr_edge_def] >>
  conj_tac >- EVAL_TAC >>
  qexists_tac `0` >>
  simp[stopping_probe_state_def, stopping_probe_fn_def,
       lookup_block_def, FIND_thm, get_instruction_def] >>
  simp[ptr_safe_step_def, ptr_inst_ok_def] >> EVAL_TAC >>
  qpat_x_assum `ghost_step _ _ _ _ _ _ _ = _` mp_tac >>
  EVAL_TAC >> simp[]
QED

Theorem assign_base_ptr_stopping_jump_edge:
  !D ctx PG G tn.
    ~ctx_has_dalloca ctx ==>
    gas_path_ptr_edge D 0 ctx stopping_probe_fn PG G tn
      ((update_var "p" 32w stopping_probe_state) with vs_inst_idx := 1)
      0 G tn
      (OK (jump_to "loop" ((update_var "p" 32w stopping_probe_state)
        with vs_inst_idx := 1)))
Proof
  rpt strip_tac >> simp[gas_path_ptr_edge_def] >>
  conj_tac >- EVAL_TAC >>
  qexists_tac `0` >>
  simp[stopping_probe_state_def, stopping_probe_fn_def,
       lookup_block_def, FIND_thm, get_instruction_def] >>
  simp[ptr_safe_step_def, ptr_inst_ok_def] >> EVAL_TAC >> simp[] >>
  disj2_tac >> qexists_tac `"loop"` >> simp[]
QED

Theorem assign_base_ptr_stopping_revisit:
  !D ctx PG.
    ~ctx_has_dalloca ctx ==>
    ?G tn t.
      gas_path_ptr D 0 ctx stopping_probe_fn PG FEMPTY entry_taint
        stopping_probe_state 0 G tn (OK t) /\
      t.vs_current_bb = stopping_probe_cs.cs_current_bb /\
      t.vs_inst_idx = LENGTH stopping_probe_cs.cs_current_insts /\
      eval_operand (Var "p") stopping_probe_state = SOME 0w /\
      eval_operand (Var "p") t = SOME 32w
Proof
  rpt strip_tac >>
  drule assign_base_ptr_stopping_assign_edge >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  drule assign_base_ptr_stopping_jump_edge >>
  disch_then (qspecl_then [`D`, `PG`, `G`, `tn`] assume_tac) >>
  qexistsl_tac [`G`, `tn`,
    `jump_to "loop" ((update_var "p" 32w stopping_probe_state)
      with vs_inst_idx := 1)`] >>
  conj_tac
  >- (`gas_path_ptr D 0 ctx stopping_probe_fn PG G tn
        (jump_to "loop" ((update_var "p" 32w stopping_probe_state)
          with vs_inst_idx := 1)) 0 G tn
        (OK (jump_to "loop" ((update_var "p" 32w stopping_probe_state)
          with vs_inst_idx := 1)))` by
          (irule (cj 1 gas_path_ptr_rules) >> EVAL_TAC) >>
      drule_all (cj 2 gas_path_ptr_rules) >> simp[] >> strip_tac >>
      qpat_x_assum `gas_path_ptr_edge _ _ _ _ _ _ _
        (_ with vs_inst_idx := 1) _ _ _ _` kall_tac >>
      drule_all (cj 2 gas_path_ptr_rules) >> simp[]) >>
  EVAL_TAC
QED

(* This falsifies endpoint-operand uniqueness for the actual path and layout
   primitives. It deliberately does not assert compile_expr or expr_post. *)
Theorem assign_base_ptr_stopping_layout_not_unique:
  !D ctx PG.
    ~ctx_has_dalloca ctx ==>
    ?G tn t.
      fn_has_code stopping_probe_cs stopping_probe_cs stopping_probe_fn /\
      fn_inst_ids_distinct stopping_probe_fn /\
      gas_path_ptr D 0 ctx stopping_probe_fn PG FEMPTY entry_taint
        stopping_probe_state 0 FEMPTY entry_taint (OK stopping_probe_state) /\
      gas_path_ptr D 0 ctx stopping_probe_fn PG FEMPTY entry_taint
        stopping_probe_state 0 G tn (OK t) /\
      stopping_probe_state.vs_current_bb = stopping_probe_cs.cs_current_bb /\
      stopping_probe_state.vs_inst_idx = LENGTH stopping_probe_cs.cs_current_insts /\
      t.vs_current_bb = stopping_probe_cs.cs_current_bb /\
      t.vs_inst_idx = LENGTH stopping_probe_cs.cs_current_insts /\
      eval_operand (Var "p") stopping_probe_state <>
        eval_operand (Var "p") t
Proof
  rpt strip_tac >> drule assign_base_ptr_stopping_revisit >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`G`, `tn`, `t`] >> simp[assign_base_ptr_stopping_layout] >>
  conj_tac >- (irule (cj 1 gas_path_ptr_rules) >> EVAL_TAC) >>
  EVAL_TAC >> simp[dimword_def]
QED
