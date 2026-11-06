Theory bodyPtrBytestringBuiltinsUintBlocks
Ancestors
  bodyPtrBytestringBuiltinsUintGhost bodyPtrBytestringBuiltinsBounds
  fragGasSeqPtr fragGasPathPtr gasCount ptrSafeRun ptrDiscipline codegenRel contextCodegenRel
  venomExecProofs
  venomExecSemantics venomInst venomState finite_map exprSimUint2Str fragExec exprLoweringProps words

Theorem uint_scalar_inst_check:
  MEM opc [Mod; Div; EQ; ADD] /\
  (!op. MEM op ops ==> op_taint tn op = {} /\ op_prov G op = NONE) /\
  ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst id opc ops outs) s = OK t /\
  t.vs_requests = s.vs_requests ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id opc ops outs) s
Proof
  rpt strip_tac >>
  `!v. MEM (Var v) ops ==> FLOOKUP G v = NONE` by
    (rpt strip_tac >> first_x_assum drule >> simp[op_prov_def]) >>
  gvs[] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke] >>
  gvs[FLOOKUP_DEF] >> metis_tac[]
QED

Theorem uint_scalar_counted_edge:
  MEM opc [Mod; Div; EQ; ADD] /\
  (!op. MEM op ops ==> op_taint tn op = {} /\ op_prov G op = NONE) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc ops outs) /\
  step_inst_base (mk_inst id opc ops outs) s = OK t /\
  t.vs_requests = s.vs_requests ==>
  gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id opc ops outs) t)
    (step_taint (mk_inst id opc ops outs) s t tn)
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id opc ops outs) s` by
    (irule uint_scalar_inst_check >> metis_tac[]) >>
  `opc <> INVOKE /\ ~is_terminator opc /\ opc <> GAS` by
    gvs[is_terminator_def] >>
  mp_tac (Q.INST [`i` |-> `mk_inst id opc ops outs`, `lo` |-> `0`,
    `u` |-> `t`] straight_line_ptr_edge) >>
  simp[mk_inst_def]
QED

Theorem uint_eq_counted_edge:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (u2s_inst a id EQ [Var (u2s_var a 0); Lit 0w] [u2s_var a k]) /\
  lookup_var (u2s_var a 0) s = SOME (n2w x) /\ x < dimword(:256) /\
  op_taint tn (Var (u2s_var a 0)) = {} /\
  FLOOKUP G (u2s_var a 0) = NONE ==>
  gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {u2s_var a k}))
    (tn with t_var := tn.t_var |+ (u2s_var a k,{}))
    (OK ((update_var (u2s_var a k) (bool_to_word (x = 0)) s) with
      vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst_base
     (u2s_inst a id EQ [Var (u2s_var a 0); Lit 0w] [u2s_var a k]) s =
     OK (update_var (u2s_var a k) (bool_to_word (x = 0)) s)` by
    (drule_all u2s_eq_run >> simp[run_inst_seq_def, AllCaseEqs()]) >>
  gvs[u2s_inst_def] >>
  qmatch_asmsub_abbrev_tac `step_inst_base inst s = OK t` >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0
     (step_prov PG G inst t) (step_taint inst s t tn)
     (OK (t with vs_inst_idx := SUC s.vs_inst_idx))` by
    (simp[Abbr `inst`] >> irule uint_scalar_counted_edge >>
     simp[Abbr `t`, update_var_def] >>
     rpt strip_tac >> gvs[op_taint_def, op_prov_def]) >>
  `step_prov PG G inst t = DRESTRICT G (COMPL {u2s_var a k}) /\
   step_taint inst s t tn = (tn with t_var := tn.t_var |+ (u2s_var a k,{}))` by
    (simp[Abbr `inst`] >> irule uint_scalar_ghost >>
     simp[Abbr `t`, update_var_def] >> rpt strip_tac >> gvs[op_prov_def]) >>
  gvs[Abbr `t`]
QED

Theorem uint_jnz_counted_edge:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id JNZ [op; Label yes; Label no] []) /\
  eval_operand op s = SOME (if b then 1w else 0w) /\
  op_taint tn op = {} ==>
  gas_path_ptr_edge D 0 ctx fn PG G tn s 0 G tn
    (OK (jump_to (if b then yes else no) s))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id JNZ [op; Label yes; Label no] []) s =
    OK (jump_to (if b then yes else no) s)` by
    (Cases_on `b` >> simp[mk_inst_def, step_inst_base_def]) >>
  `ptr_safe_step D 0 0 ctx fn PG G tn
     (mk_inst id JNZ [op; Label yes; Label no] []) s` by
    (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          allocas_from_def, mk_inst_def, source_memory_write_ranges_def,
          source_memory_read_ranges_def, op_taint_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     simp[mk_inst_def, step_inst_base_def, step_jnz_behavior, jump_to_def] >>
     Cases_on `b` >> gvs[op_taint_def] >>
     gen_tac >> Cases_on `op' = op` >> gvs[] >>
     Cases_on `op' = Label yes` >> gvs[] >>
     Cases_on `op' = Label no` >> gvs[]) >>
  rewrite_tac[gas_path_ptr_edge_def] >> simp[] >>
  qexists_tac `0:num` >>
  simp[step_inst_non_invoke, gas_count_step_def, is_terminator_def] >>
  simp[mk_inst_def] >> metis_tac[]
QED

(* One test boundary covers both check (k=3) and condition (k=4). *)
Theorem uint_test_counted_path:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (u2s_inst a id EQ [Var (u2s_var a 0); Lit 0w] [u2s_var a k]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst jid JNZ [Var (u2s_var a k); Label yes; Label no] []) /\
  lookup_var (u2s_var a 0) s = SOME (n2w x) /\ x < dimword(:256) /\
  op_taint tn (Var (u2s_var a 0)) = {} /\
  FLOOKUP G (u2s_var a 0) = NONE ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {u2s_var a k}))
    (tn with t_var := tn.t_var |+ (u2s_var a k,{}))
    (OK (jump_to (if x = 0 then yes else no)
      ((update_var (u2s_var a k) (bool_to_word (x = 0)) s) with
        vs_inst_idx := SUC s.vs_inst_idx)))
Proof
  strip_tac >> drule_all uint_eq_counted_edge >>
  disch_then (qspecl_then [`PG`, `D`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr_edge _ _ _ _ _ _ _ _ _ g t (OK mid)` >>
  `gas_path_ptr_edge D 0 ctx fn PG g t mid 0 g t
     (OK (jump_to (if x = 0 then yes else no) mid))` by
    (irule uint_jnz_counted_edge >>
     simp[Abbr `mid`, Abbr `t`, update_var_def, lookup_var_def,
          eval_operand_def, op_taint_def, FLOOKUP_UPDATE, bool_to_word_def] >>
     qexistsl_tac [`jid`, `Var (u2s_var a k)`] >>
     simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
          bool_to_word_def] >> Cases_on `x = 0` >> simp[bool_to_word_def]) >>
  `~(jump_to (if x = 0 then yes else no) mid).vs_halted` by
    simp[jump_to_def, Abbr `mid`, update_var_def] >>
  `gas_path_ptr D 0 ctx fn PG g t mid 0 g t
     (OK (jump_to (if x = 0 then yes else no) mid))` by
    metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES] >>
  gvs[] >> metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]
QED

Theorem u2s_check_counted_ptr:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block (u2s_label a 0) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 0; bb_instructions := u2s_check a|> /\
  s.vs_current_bb = u2s_label a 0 /\ s.vs_inst_idx = 0 /\
  lookup_var (u2s_var a 0) s = SOME (n2w x) /\ x < dimword(:256) /\
  op_taint tn (Var (u2s_var a 0)) = {} /\ FLOOKUP G (u2s_var a 0) = NONE ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {u2s_var a 3}))
    (tn with t_var := tn.t_var |+ (u2s_var a 3,{}))
    (OK (jump_to (u2s_label a (if x = 0 then 3 else 1))
      (update_var (u2s_var a 3) (bool_to_word (x = 0)) s)))
Proof
  strip_tac >>
  `jump_to (u2s_label a (if x = 0 then 3 else 1))
     (update_var (u2s_var a 3) (bool_to_word (x = 0)) s) =
   jump_to (if x = 0 then u2s_label a 3 else u2s_label a 1)
     ((update_var (u2s_var a 3) (bool_to_word (x = 0)) s) with
       vs_inst_idx := SUC s.vs_inst_idx)` by
    (Cases_on `x = 0` >> simp[jump_to_def]) >>
  pop_assum SUBST1_TAC >> irule uint_test_counted_path >> simp[] >>
  qexistsl_tac
    [`4`, `a.cs_next_id+5`] >>
  simp[get_instruction_def, u2s_check_def, u2s_inst_def]
QED

Theorem u2s_cond_counted_ptr:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block (u2s_label a 1) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 1; bb_instructions := u2s_cond a|> /\
  s.vs_current_bb = u2s_label a 1 /\ s.vs_inst_idx = 0 /\
  lookup_var (u2s_var a 0) s = SOME (n2w x) /\ x < dimword(:256) /\
  op_taint tn (Var (u2s_var a 0)) = {} /\ FLOOKUP G (u2s_var a 0) = NONE ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {u2s_var a 4}))
    (tn with t_var := tn.t_var |+ (u2s_var a 4,{}))
    (OK (jump_to (u2s_label a (if x = 0 then 4 else 2))
      (update_var (u2s_var a 4) (bool_to_word (x = 0)) s)))
Proof
  strip_tac >>
  `jump_to (u2s_label a (if x = 0 then 4 else 2))
     (update_var (u2s_var a 4) (bool_to_word (x = 0)) s) =
   jump_to (if x = 0 then u2s_label a 4 else u2s_label a 2)
     ((update_var (u2s_var a 4) (bool_to_word (x = 0)) s) with
       vs_inst_idx := SUC s.vs_inst_idx)` by
    (Cases_on `x = 0` >> simp[jump_to_def]) >>
  pop_assum SUBST1_TAC >> irule uint_test_counted_path >> simp[] >>
  qexistsl_tac
    [`6`, `a.cs_next_id+7`] >>
  simp[get_instruction_def, u2s_cond_def, u2s_inst_def]
QED
