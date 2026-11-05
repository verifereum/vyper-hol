(* Memory boundary for the range loop's variable store. *)
Theory stmtForRangeMemoryParts
Ancestors
  instMemFrontier bodyMemoryDefs stmtSimForRounds exprLoweringProps
  venomMemDefs venomExecSemantics stmtSimProps fragGasPathMem fragGasMode
  fragGasSeqMem gasCount memSafeRun fragExecMem venomInstProofs emitHelperProps venomInst venomState words venomExecProofs finite_map list rich_list

Theorem for_range_allocated_store_below:
  !s aid b sz dst v iid outs.
    alloca_inv s /\ FLOOKUP s.vs_allocas aid = SOME (b, sz) /\
    32 <= sz /\ eval_operand dst s = SOME (n2w b) /\
    b < dimword (:256) ==>
    inst_mem_below_frontier (mk_inst iid MSTORE [dst; v] outs) s
Proof
  rpt strip_tac >> simp[below_frontier_MSTORE] >>
  rpt strip_tac >> gvs[] >>
  irule alloca_region_below_frontier >>
  conj_tac >- fs[alloca_inv_def] >>
  qexistsl_tac [`aid`, `b`, `sz`] >> simp[]
QED

Theorem for_range_store_zero_path_mem:
  !ctx func s bb iid dst v w value aid sz.
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst iid MSTORE [dst; v] []) /\
    ~s.vs_halted /\ eval_operand dst s = SOME w /\
    eval_operand v s = SOME value /\ alloca_inv s /\
    FLOOKUP s.vs_allocas aid = SOME (w2n w, sz) /\ 32 <= sz ==>
    gas_path_mem ctx func s 0
      (OK (mstore (w2n w) value s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt strip_tac >>
  `inst_mem_below_frontier (mk_inst iid MSTORE [dst; v] []) s` by
    (irule for_range_allocated_store_below >> conj_tac >- simp[] >>
     qexistsl_tac [`aid`, `w2n w`, `sz`] >> simp[w2n_lt]) >>
  `step_inst_base (mk_inst iid MSTORE [dst; v] []) s =
     OK (mstore (w2n w) value s)` by
    (irule step_MSTORE >> simp[]) >>
  `gas_path_mem_edge ctx func s 0
     (OK (mstore (w2n w) value s with vs_inst_idx := SUC s.vs_inst_idx))` by
    (rewrite_tac[gas_path_mem_edge_def] >> simp[] >>
     qexists_tac `0:num` >>
     simp[step_inst_non_invoke, mk_inst_def, gas_count_step_def,
          mem_safe_step_non_invoke, is_terminator_def, mstore_def] >>
     metis_tac[]) >>
  `~(mstore (w2n w) value s with
       vs_inst_idx := SUC s.vs_inst_idx).vs_halted` by simp[mstore_def] >>
  metis_tac[gas_path_mem_rules, arithmeticTheory.ADD_CLAUSES]
QED

(* Concrete instruction interface for both JMP and JNZ boundaries. *)
Theorem for_range_jump_at_zero_path_mem:
  !ctx func s bb inst lbl.
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\ ~s.vs_halted /\
    is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> GAS /\ inst_mem_below_frontier inst s /\
    inst_dload_in_section inst s /\
    step_inst_base inst s = OK (jump_to lbl s) ==>
    gas_path_mem ctx func s 0 (OK (jump_to lbl s))
Proof
  rpt strip_tac >>
  `gas_path_mem_edge ctx func s 0 (OK (jump_to lbl s))` by
    (rewrite_tac[gas_path_mem_edge_def] >> simp[] >>
     qexists_tac `0:num` >>
     simp[step_inst_non_invoke, gas_count_step_def, mem_safe_step_non_invoke] >>
     metis_tac[]) >>
  `~(jump_to lbl s).vs_halted` by simp[jump_to_def] >>
  metis_tac[gas_path_mem_rules, arithmeticTheory.ADD_CLAUSES]
QED


Theorem for_range_straight_line_mem_edge:
  !ctx func s bb i u k t.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME i /\
    i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    inst_mem_below_frontier i s /\ inst_dload_in_section i s /\
    step_inst_base i s = OK u /\
    k = (if i.inst_opcode = GAS then 1 else 0) /\
    t = (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
    gas_path_mem_edge ctx func s k (OK t)
Proof
  rpt strip_tac >> gvs[] >> irule straight_line_mem_edge >> metis_tac[]
QED

Theorem for_range_jnz_zero_path_mem:
  !ctx func s bb iid op yes no cond.
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst iid JNZ [op; Label yes; Label no] []) /\
    ~s.vs_halted /\ eval_operand op s = SOME cond ==>
    gas_path_mem ctx func s 0
      (OK (jump_to (if cond <> 0w then yes else no) s))
Proof
  rpt strip_tac >>
  drule venomExecProofsTheory.step_jnz_behavior >>
  disch_then (qspecl_then [`yes`, `no`, `iid`] assume_tac) >>
  irule for_range_jump_at_zero_path_mem >>
  conj_tac >- simp[] >>
  qexistsl_tac [`bb`, `mk_inst iid JNZ [op; Label yes; Label no] []`] >>
  simp[mk_inst_def, is_terminator_def, inst_dload_in_section_def] >>
  conj_tac >- (Cases_on `cond = 0w` >> gvs[]) >>
  irule below_frontier_no_ranges >> simp[]
QED

Theorem for_cond_zero_path_mem:
  !ctx func cc cv ev dv a b lbl exit_lbl body_lbl j1 j2.
    lookup_block lbl func.fn_blocks =
      SOME <| bb_label := lbl;
              bb_instructions :=
                [mk_inst j1 EQ [Var cv; Var ev] [dv];
                 mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] []] |> /\
    cc.vs_current_bb = lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
    lookup_var cv cc = SOME a /\ lookup_var ev cc = SOME b ==>
    gas_path_mem ctx func cc 0
      (OK (jump_to (if a = b then exit_lbl else body_lbl)
        (update_var dv (bool_to_word (a = b)) cc)))
Proof
  rpt strip_tac >>
  qmatch_asmsub_abbrev_tac `lookup_block lbl func.fn_blocks = SOME bb` >>
  qabbrev_tac `u = update_var dv (bool_to_word (a = b)) cc with vs_inst_idx := 1` >>
  `gas_path_mem_edge ctx func cc 0 (OK u)` by
    (irule for_range_straight_line_mem_edge >> simp[] >>
     qexistsl_tac [`mk_inst j1 EQ [Var cv; Var ev] [dv]`,
       `update_var dv (bool_to_word (a = b)) cc`] >>
     simp[Abbr `bb`, Abbr `u`, get_instruction_def, mk_inst_def,
          is_terminator_def, inst_dload_in_section_def] >>
     conj_tac
     >- (pure_rewrite_tac[GSYM mk_inst_def] >> irule step_EQ >>
         simp[eval_operand_def]) >>
     irule below_frontier_no_ranges >> simp[]) >>
  `gas_path_mem ctx func u 0
     (OK (jump_to (if bool_to_word (a = b) <> 0w then exit_lbl else body_lbl) u))` by
    (irule for_range_jnz_zero_path_mem >>
     simp[Abbr `u`, update_var_def] >>
     qexistsl_tac [`j2`, `Var dv`] >>
     simp[Abbr `bb`, get_instruction_def, eval_operand_def,
          lookup_var_def, FLOOKUP_UPDATE]) >>
  `gas_path_mem ctx func u 0
     (OK (jump_to (if a = b then exit_lbl else body_lbl) u))` by
    (Cases_on `a = b` >> fs[bool_to_word_def]) >>
  drule (cj 2 gas_path_mem_rules) >> disch_then drule >>
  simp[Abbr `u`, jump_to_def, update_var_def]
QED

Theorem for_entry_zero_path_mem:
  !ctx func ee cv ev a b lbl cond_lbl i1 i2 i3.
    lookup_block lbl func.fn_blocks =
      SOME <|bb_label := lbl;
        bb_instructions := [mk_inst i1 ASSIGN [Lit a] [cv];
                            mk_inst i2 ADD [Lit a; Lit b] [ev];
                            mk_inst i3 JMP [Label cond_lbl] []]|> /\
    ee.vs_current_bb = lbl /\ ee.vs_inst_idx = 0 /\ ~ee.vs_halted ==>
    gas_path_mem ctx func ee 0
      (OK (jump_to cond_lbl (update_var ev (a + b) (update_var cv a ee))))
Proof
  rpt strip_tac >>
  qmatch_asmsub_abbrev_tac `lookup_block lbl func.fn_blocks = SOME bb` >>
  qabbrev_tac `code = [mk_inst i1 ASSIGN [Lit a] [cv];
                       mk_inst i2 ADD [Lit a; Lit b] [ev]]` >>
  `!s. step_inst_base (mk_inst i1 ASSIGN [Lit a] [cv]) s =
       OK (update_var cv a s)` by
    simp[step_inst_base_def, mk_inst_def, eval_operand_def] >>
  `!s. step_inst_base (mk_inst i2 ADD [Lit a; Lit b] [ev]) s =
       OK (update_var ev (a + b) s)` by
    (gen_tac >> irule step_ADD >> simp[eval_operand_def]) >>
  qabbrev_tac `u = update_var ev (a + b) (update_var cv a ee)` >>
  `gas_path_mem ctx func ee 0 (OK (u with vs_inst_idx := 2))` by
    (qspecl_then [`code`, `ee`, `u`, `ctx`, `func`, `bb`]
       mp_tac run_inst_seq_gas_path_mem >>
     simp[Abbr `code`] >> disch_then irule >>
     simp[Abbr `bb`, is_terminator_def, run_inst_seq_mem_ok_def,
          inst_dload_in_section_def, run_inst_seq_def, mk_inst_def,
          Abbr `u`] >>
     conj_tac >- (irule below_frontier_no_ranges >> simp[]) >>
     irule below_frontier_no_ranges >> simp[]) >>
  `gas_path_mem ctx func (u with vs_inst_idx := 2) 0
     (OK (jump_to cond_lbl (u with vs_inst_idx := 2)))` by
    (irule for_range_jump_at_zero_path_mem >>
     simp[Abbr `u`, update_var_def] >>
     qexists_tac `mk_inst i3 JMP [Label cond_lbl] []` >>
     simp[Abbr `bb`, get_instruction_def, mk_inst_def,
          is_terminator_def, inst_dload_in_section_def,
          step_jmp_behavior] >>
     irule below_frontier_no_ranges >> simp[]) >>
  qpat_assum `gas_path_mem _ _ ee _ _`
    (mp_then Any mp_tac gas_path_mem_then) >> disch_then drule >>
  simp[jump_to_def, Abbr `u`]
QED

Theorem for_incr_zero_path_mem:
  !ctx func dd cv nv c lbl cond_lbl i1 i2 i3.
    lookup_block lbl func.fn_blocks =
      SOME <|bb_label := lbl;
        bb_instructions := [mk_inst i1 ADD [Var cv; Lit 1w] [nv];
                            mk_inst i2 ASSIGN [Var nv] [cv];
                            mk_inst i3 JMP [Label cond_lbl] []]|> /\
    dd.vs_current_bb = lbl /\ dd.vs_inst_idx = 0 /\ ~dd.vs_halted /\
    lookup_var cv dd = SOME c ==>
    gas_path_mem ctx func dd 0
      (OK (jump_to cond_lbl
        (update_var cv (c + 1w) (update_var nv (c + 1w) dd))))
Proof
  rpt strip_tac >>
  qmatch_asmsub_abbrev_tac `lookup_block lbl func.fn_blocks = SOME bb` >>
  qabbrev_tac `code = [mk_inst i1 ADD [Var cv; Lit 1w] [nv];
                       mk_inst i2 ASSIGN [Var nv] [cv]]` >>
  `step_inst_base (mk_inst i1 ADD [Var cv; Lit 1w] [nv]) dd =
       OK (update_var nv (c + 1w) dd)` by
    (irule step_ADD >> simp[eval_operand_def]) >>
  `step_inst_base (mk_inst i2 ASSIGN [Var nv] [cv])
       (update_var nv (c + 1w) dd) =
       OK (update_var cv (c + 1w) (update_var nv (c + 1w) dd))` by
    simp[step_inst_base_def, mk_inst_def, eval_operand_def,
         lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  fs[mk_inst_def] >>
  qabbrev_tac `u = update_var cv (c + 1w) (update_var nv (c + 1w) dd)` >>
  `gas_path_mem ctx func dd 0 (OK (u with vs_inst_idx := 2))` by
    (qspecl_then [`code`, `dd`, `u`, `ctx`, `func`, `bb`]
       mp_tac run_inst_seq_gas_path_mem >>
     simp[Abbr `code`] >> disch_then irule >>
     simp[Abbr `bb`, is_terminator_def, run_inst_seq_mem_ok_def,
          inst_dload_in_section_def, run_inst_seq_def, mk_inst_def,
          Abbr `u`] >>
     conj_tac >- (irule below_frontier_no_ranges >> simp[]) >>
     irule below_frontier_no_ranges >> simp[]) >>
  `gas_path_mem ctx func (u with vs_inst_idx := 2) 0
     (OK (jump_to cond_lbl (u with vs_inst_idx := 2)))` by
    (irule for_range_jump_at_zero_path_mem >>
     simp[Abbr `u`, update_var_def] >>
     qexists_tac `mk_inst i3 JMP [Label cond_lbl] []` >>
     simp[Abbr `bb`, get_instruction_def, mk_inst_def,
          is_terminator_def, inst_dload_in_section_def, step_jmp_behavior] >>
     irule below_frontier_no_ranges >> simp[]) >>
  qpat_assum `gas_path_mem _ _ dd _ _`
    (mp_then Any mp_tac gas_path_mem_then) >> disch_then drule >>
  simp[jump_to_def, Abbr `u`]
QED

Theorem for_start_zero_path_mem:
  !ctx func s0 s1 aa pre lbl entry_lbl i.
    lookup_block s0.vs_current_bb func.fn_blocks =
      SOME <|bb_label := lbl;
        bb_instructions := pre ++ [aa; mk_inst i JMP [Label entry_lbl] []]|> /\
    s0.vs_inst_idx = LENGTH pre /\ ~s0.vs_halted /\
    aa.inst_opcode = ALLOCA /\ step_inst_base aa s0 = OK s1 /\
    s1.vs_current_bb = s0.vs_current_bb /\ ~s1.vs_halted ==>
    gas_path_mem ctx func s0 0 (OK (jump_to entry_lbl s1))
Proof
  rpt strip_tac >>
  qmatch_asmsub_abbrev_tac `lookup_block _ func.fn_blocks = SOME bb` >>
  qabbrev_tac `u = s1 with vs_inst_idx := SUC (LENGTH pre)` >>
  `gas_path_mem_edge ctx func s0 0 (OK u)` by
    (irule for_range_straight_line_mem_edge >> simp[] >>
     qexistsl_tac [`aa`, `s1`] >>
     simp[Abbr `bb`, Abbr `u`, get_instruction_def, EL_APPEND,
          is_terminator_def, inst_dload_in_section_def] >>
     irule below_frontier_no_ranges >> simp[]) >>
  `gas_path_mem ctx func u 0 (OK (jump_to entry_lbl u))` by
    (irule for_range_jump_at_zero_path_mem >> simp[Abbr `u`] >>
     qexists_tac `mk_inst i JMP [Label entry_lbl] []` >>
     simp[Abbr `bb`, get_instruction_def, EL_APPEND, mk_inst_def,
          is_terminator_def, inst_dload_in_section_def, step_jmp_behavior] >>
     irule below_frontier_no_ranges >> simp[]) >>
  drule (cj 2 gas_path_mem_rules) >> disch_then drule >>
  simp[Abbr `u`, jump_to_def]
QED
