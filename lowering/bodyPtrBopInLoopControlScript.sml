Theory bodyPtrBopInLoopControl
Ancestors bodyPtrBopInLoopExit bodyPtrBopInLoopFrame fragGasSeqPtr fragGasPathPtr
  emitHelper ptrSafeRun ptrDiscipline venomInstProofs venomInst
  codegenRel contextCodegenRel venomExecSemantics venomState
  instIdxIndep finite_map pred_set gasCount emitHelperProps compileEnv

(* One scalar literal write.  The destination need not have been clean:
   ASSIGN overwrites both its value and its ghost binding. *)
Theorem membership_assign_literal_check:
  ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id ASSIGN [Lit w] [dst]) s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
       allocas_from_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, mk_inst_def, op_taint_def] >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, eval_operand_def,
       update_var_def]
QED

Theorem membership_assign_literal_path:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id ASSIGN [Lit w] [dst]) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {dst}))
    (tn with t_var := set_var_taint tn.t_var [dst] {})
    (OK ((update_var dst w s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id ASSIGN [Lit w] [dst]) s` by
    simp[membership_assign_literal_check] >>
  `step_inst_base (mk_inst id ASSIGN [Lit w] [dst]) s =
     OK (update_var dst w s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def] >>
  `(mk_inst id ASSIGN [Lit w] [dst]).inst_opcode <> INVOKE /\
    ~is_terminator (mk_inst id ASSIGN [Lit w] [dst]).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all straight_line_ptr_edge >>
  disch_then (qspec_then `PG` mp_tac) >>
  simp[mk_inst_def, step_prov_def, set_prov_def, out_prov_def,
       first_prov_def, op_prov_def, step_taint_def,
       mem_taint_def, out_taint_def, store_taint_def, adopt_reset_def,
       imm_taint_def, op_taint_def, taint_component_equality,
       new_site_bytes_def, step_writes_def, written_taint_def,
       eval_operand_def, update_var_def, range_bytes_def,
       source_memory_write_ranges_def, FLOOKUP_DEF, SF CONJ_ss] >>
  strip_tac >>
  `~(update_var dst w s with vs_inst_idx := SUC s.vs_inst_idx).vs_halted` by
    simp[update_var_def] >>
  qpat_x_assum `gas_path_ptr_edge _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  `(<|t_mem := tn.t_mem; t_var := set_var_taint tn.t_var [dst] {};
      t_stor := tn.t_stor; t_trans := tn.t_trans; t_imm := tn.t_imm|>) =
    (tn with t_var := set_var_taint tn.t_var [dst] {})` by
    simp[taint_component_equality] >>
  simp[] >> strip_tac >>
  drule (cj 2 gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >>
  simp[gas_path_ptr_rules, update_var_def]
QED

Theorem membership_jump_path:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id JMP [Label lbl] []) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G tn (OK (jump_to lbl s))
Proof
  strip_tac >>
  `step_inst 0 ctx (mk_inst id JMP [Label lbl] []) s = OK (jump_to lbl s)` by
    simp[step_inst_non_invoke, step_inst_base_opcode_eqs, mk_inst_def] >>
  `ptr_safe_step D 0 0 ctx fn PG G tn (mk_inst id JMP [Label lbl] []) s` by
    (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          allocas_from_def, source_memory_write_ranges_def,
          source_memory_read_ranges_def, mk_inst_def, op_taint_def]) >>
  `is_terminator (mk_inst id JMP [Label lbl] []).inst_opcode /\
   (mk_inst id JMP [Label lbl] []).inst_opcode <> INVOKE` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all raw_jump_path_ptr >>
  simp[mk_inst_def, gas_count_step_def]
QED

(* The concrete entry spine is independent of allocation/name freshness. *)
Theorem membership_entry_path:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions =
    [mk_inst id ASSIGN [Lit 0w] [idx];
     mk_inst (id+1) ASSIGN [Lit 0w] [result];
     mk_inst (id+2) JMP [Label cond] []] /\ s.vs_inst_idx = 0 ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT (DRESTRICT G (COMPL {idx})) (COMPL {result}))
    (tn with t_var := set_var_taint (set_var_taint tn.t_var [idx] {}) [result] {})
    (OK (jump_to cond (update_var result 0w (update_var idx 0w s))))
Proof
  strip_tac >>
  `get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id ASSIGN [Lit 0w] [idx])` by simp[get_instruction_def] >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 (DRESTRICT G (COMPL {idx}))
    (tn with t_var := set_var_taint tn.t_var [idx] {})
    (OK (update_var idx 0w s with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule membership_assign_literal_path >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `OK s1` >>
  `~s1.vs_halted /\ s1.vs_current_bb = s.vs_current_bb /\ s1.vs_inst_idx = 1` by
    simp[Abbr `s1`, update_var_def] >>
  `get_instruction bb s1.vs_inst_idx =
    SOME (mk_inst (id+1) ASSIGN [Lit 0w] [result])` by simp[get_instruction_def] >>
  `lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 _` >>
  `gas_path_ptr D 0 ctx fn PG G1 tn1 s1 0 (DRESTRICT G1 (COMPL {result}))
    (tn1 with t_var := set_var_taint tn1.t_var [result] {})
    (OK (update_var result 0w s1 with vs_inst_idx := SUC s1.vs_inst_idx))` by
    (irule membership_assign_literal_path >> simp[] >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `OK s2` >>
  `~s2.vs_halted /\ s2.vs_current_bb = s.vs_current_bb /\ s2.vs_inst_idx = 2` by
    simp[Abbr `s2`, update_var_def] >>
  `get_instruction bb s2.vs_inst_idx =
    SOME (mk_inst (id+2) JMP [Label cond] [])` by simp[get_instruction_def] >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG G1 tn1 s1 0 G2 tn2 _` >>
  `gas_path_ptr D 0 ctx fn PG G2 tn2 s2 0 G2 tn2 (OK (jump_to cond s2))` by
    (irule membership_jump_path >> simp[] >> metis_tac[]) >>
  dxrule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  dxrule_all gas_path_ptr_then >> simp[] >>
  simp[Abbr `s1`, Abbr `s2`, Abbr `G1`, Abbr `G2`, Abbr `tn1`, Abbr `tn2`,
       jump_to_def, update_var_def]
QED

Theorem membership_init_spine:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME old_bb /\
  get_instruction old_bb s.vs_inst_idx = SOME (mk_inst id JMP [Label entry] []) /\
  lookup_block entry fn.fn_blocks = SOME entry_bb /\
  entry_bb.bb_instructions =
    [mk_inst (id+1) ASSIGN [Lit 0w] [idx];
     mk_inst (id+2) ASSIGN [Lit 0w] [result];
     mk_inst (id+3) JMP [Label cond] []] ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT (DRESTRICT G (COMPL {idx})) (COMPL {result}))
    (tn with t_var := set_var_taint (set_var_taint tn.t_var [idx] {}) [result] {})
    (OK (jump_to cond (update_var result 0w (update_var idx 0w (jump_to entry s)))))
Proof
  strip_tac >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G tn (OK (jump_to entry s))` by
    (irule membership_jump_path >> metis_tac[]) >>
  `gas_path_ptr D 0 ctx fn PG G tn (jump_to entry s) 0
    (DRESTRICT (DRESTRICT G (COMPL {idx})) (COMPL {result}))
    (tn with t_var := set_var_taint (set_var_taint tn.t_var [idx] {}) [result] {})
    (OK (jump_to cond (update_var result 0w (update_var idx 0w (jump_to entry s)))))` by
    (irule membership_entry_path >> simp[jump_to_def] >>
     qexists_tac `id+1` >> simp[arithmeticTheory.ADD_ASSOC]) >>
  drule_all gas_path_ptr_then >> simp[]
QED

Theorem membership_init_path_ptr:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  idx = "%" ++ toString (sa.cs_next_var+1) /\
  result = "%" ++ toString sa.cs_next_var /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME old_bb /\
  get_instruction old_bb s.vs_inst_idx =
    SOME (mk_inst sa.cs_next_id JMP [Label entry] []) /\
  lookup_block entry fn.fn_blocks = SOME entry_bb /\
  entry_bb.bb_instructions =
    [mk_inst (sa.cs_next_id+1) ASSIGN [Lit 0w] [idx];
     mk_inst (sa.cs_next_id+2) ASSIGN [Lit 0w] [result];
     mk_inst (sa.cs_next_id+3) JMP [Label cond] []] ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = cond /\ t.vs_inst_idx = 0 /\
    lookup_var idx t = SOME 0w /\ lookup_var result t = SOME 0w /\
    FLOOKUP G' idx = NONE /\ FLOOKUP G' result = NONE /\
    op_taint tn' (Var idx) = {} /\ op_taint tn' (Var result) = {} /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    t = s with <|vs_vars := t.vs_vars; vs_current_bb := t.vs_current_bb;
      vs_prev_bb := t.vs_prev_bb; vs_inst_idx := t.vs_inst_idx|>
Proof
  strip_tac >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT (DRESTRICT G (COMPL {idx})) (COMPL {result}))
    (tn with t_var := set_var_taint (set_var_taint tn.t_var [idx] {}) [result] {})
    (OK (jump_to cond (update_var result 0w (update_var idx 0w (jump_to entry s)))))` by
    (irule membership_init_spine >> metis_tac[]) >>
  goal_assum (drule_at Any) >>
  simp[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_DRESTRICT,
       op_taint_def, set_var_taint_def] >>
  simp[FLOOKUP_UPDATE] >> rpt strip_tac >>
  `x <> STRING #"%" (toString (sa.cs_next_var+1)) /\
   x <> STRING #"%" (toString sa.cs_next_var)` by
    (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.ADD_0]) >>
  simp[]
QED

Theorem membership_eq_check:
  ~ctx_has_dalloca ctx /\
  eval_operand a s = SOME aw /\ eval_operand b s = SOME bw /\
  op_taint tn a = {} /\ op_taint tn b = {} /\
  op_prov G a = NONE /\ op_prov G b = NONE ==>
  ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id EQ [a;b] [dst]) s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       mk_inst_def] >>
  conj_tac >-
    (rpt strip_tac >> gvs[op_prov_def, FLOOKUP_DEF]) >>
  conj_tac >- metis_tac[] >>
  `step_inst 0 ctx (mk_inst id EQ [a;b] [dst]) s =
    OK (update_var dst (bool_to_word (aw = bw)) s)` by
    simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_pure2_def,
         eval_operands_def] >>
  fs[mk_inst_def, update_var_def]
QED
