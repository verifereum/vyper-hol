Theory bodyPtrBytestringBuiltinsUintBlocks
Ancestors
  bodyPtrBytestringBuiltinsUintGhost bodyPtrBytestringBuiltinsBounds
  fragGasSeqPtr fragGasPathPtr gasCount ptrSafeRun ptrDiscipline codegenRel contextCodegenRel
  venomExecProofs exprSimPtrProps bodyPtrDefs wordArgsPtr compileEnv
  venomExecSemantics venomInst venomState finite_map exprSimUint2Str fragExec exprLoweringProps words list rich_list

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

Theorem uint_clean_scalar_counted_edge:
  MEM opc [Mod; Div; EQ; ADD] /\
  (!op. MEM op ops ==> op_taint tn op = {} /\ op_prov G op = NONE) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc ops [out]) /\
  step_inst_base (mk_inst id opc ops [out]) s = OK (update_var out w s) ==>
  gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {out})) (tn with t_var := tn.t_var |+ (out,{}))
    (OK (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0
     (step_prov PG G (mk_inst id opc ops [out]) (update_var out w s))
     (step_taint (mk_inst id opc ops [out]) s (update_var out w s) tn)
     (OK (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule uint_scalar_counted_edge >> simp[update_var_def]) >>
  `step_prov PG G (mk_inst id opc ops [out]) (update_var out w s) =
     DRESTRICT G (COMPL {out}) /\
   step_taint (mk_inst id opc ops [out]) s (update_var out w s) tn =
     (tn with t_var := tn.t_var |+ (out,{}))` by
    (irule uint_scalar_ghost >> simp[update_var_def] >> metis_tac[]) >>
  gvs[]
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
  gvs[u2s_inst_def] >> irule uint_clean_scalar_counted_edge >> simp[] >>
  qexistsl_tac [`id + a.cs_next_id`, `EQ`, `[Var (u2s_var a 0); Lit 0w]`] >>
  simp[] >> rpt strip_tac >> gvs[op_taint_def, op_prov_def]
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

Theorem u2s_scalar_ghost_inv:
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv a /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) ==>
  ghost_inv d cenv cx es (DRESTRICT G (COMPL {u2s_var a k}))
    (tn with t_var := tn.t_var |+ (u2s_var a k,{}))
    (update_var (u2s_var a k) w s with vs_inst_idx := idx)
Proof
  strip_tac >> irule ghost_inv_fresh_frame >>
  goal_assum (drule_at Any) >> simp[update_var_def] >>
  qexistsl_tac [`G`, `es`, `s`, `tn`] >> simp[] >> rpt strip_tac >>
  `x <> u2s_var a k` by metis_tac[u2s_var_fresh] >>
  simp[lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def]
QED

Theorem u2s_scalar_ghost_kept:
  ghost_kept cenv es a G0 tn0 s0 G tn ==>
  ghost_kept cenv es a G0 tn0 s0 (DRESTRICT G (COMPL {u2s_var a k}))
    (tn with t_var := tn.t_var |+ (u2s_var a k,{}))
Proof
  simp[ghost_kept_def] >> strip_tac >> conj_tac
  >- (rpt strip_tac >>
      `x <> u2s_var a k` by metis_tac[u2s_var_fresh] >>
      simp[FLOOKUP_DRESTRICT, op_taint_def, FLOOKUP_UPDATE] >>
      qpat_x_assum `!x. not_fresh_at a x ==> _` drule >>
      simp[op_taint_def]) >>
  metis_tac[]
QED

Theorem uint_assign_counted_edge:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ASSIGN [op] [out]) /\
  eval_operand op s = SOME w ==>
  gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id ASSIGN [op] [out]) (update_var out w s))
    (step_taint (mk_inst id ASSIGN [op] [out]) s (update_var out w s) tn)
    (OK (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ASSIGN [op] [out]) s = OK (update_var out w s)` by
    simp[mk_inst_def, step_inst_base_def] >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id ASSIGN [op] [out]) s` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
          mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke, update_var_def]) >>
  mp_tac (Q.INST [`i` |-> `mk_inst id ASSIGN [op] [out]`, `lo` |-> `0`,
    `u` |-> `update_var out w s`] straight_line_ptr_edge) >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem uint_jump_counted_edge:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id JMP [Label lbl] []) ==>
  gas_path_ptr_edge D 0 ctx fn PG G tn s 0 G tn (OK (jump_to lbl s))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id JMP [Label lbl] []) s = OK (jump_to lbl s)` by
    simp[mk_inst_def, step_inst_base_def] >>
  `ptr_safe_step D 0 0 ctx fn PG G tn (mk_inst id JMP [Label lbl] []) s` by
    simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
         allocas_from_def, mk_inst_def, source_memory_write_ranges_def,
         source_memory_read_ranges_def, step_inst_non_invoke,
         step_inst_base_def, jump_to_def, op_taint_def] >>
  rewrite_tac[gas_path_ptr_edge_def] >> simp[] >> qexists_tac `0:num` >>
  simp[step_inst_non_invoke, gas_count_step_def, is_terminator_def, mk_inst_def] >>
  metis_tac[]
QED

Theorem uint_assign_counted_prefix:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ASSIGN [op] [out]) /\
  eval_operand op s = SOME w /\
  gas_path_ptr D 0 ctx fn PG
    (step_prov PG G (mk_inst id ASSIGN [op] [out]) (update_var out w s))
    (step_taint (mk_inst id ASSIGN [op] [out]) s (update_var out w s) tn)
    (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx) n G' tn' r ==>
  gas_path_ptr D 0 ctx fn PG G tn s n G' tn' r
Proof
  strip_tac >> drule_all uint_assign_counted_edge >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] assume_tac) >>
  metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]
QED

Theorem uint_jump_counted_path:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id JMP [Label lbl] []) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G tn (OK (jump_to lbl s))
Proof
  strip_tac >> drule_all uint_jump_counted_edge >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] assume_tac) >>
  `~(jump_to lbl s).vs_halted` by simp[jump_to_def] >>
  metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]
QED

Theorem u2s_setup_counted_ptr:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = pre ++ u2s_setup a op buf /\
  s.vs_inst_idx = LENGTH pre /\
  eval_operand op s = SOME (n2w x) /\ eval_operand buf s = SOME (n2w b) /\
  (!k. op <> Var (u2s_var a k) /\ buf <> Var (u2s_var a k)) ==>
  ?G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
    (OK (jump_to (u2s_label a 0)
      (update_var (u2s_var a 2) (n2w b)
        (update_var (u2s_var a 1) 0w (update_var (u2s_var a 0) (n2w x) s)))))
Proof
  strip_tac >>
  irule_at Any uint_assign_counted_prefix >>
  simp[u2s_setup_def, get_instruction_def, EL_APPEND_EQN, u2s_inst_def] >>
  simp[mk_inst_def] >>
  irule_at Any uint_assign_counted_prefix >>
  simp[update_var_def, get_instruction_def, EL_APPEND_EQN, u2s_setup_def,
       u2s_inst_def, mk_inst_def, eval_operand_def] >>
  irule_at Any uint_assign_counted_prefix >>
  simp[update_var_def, get_instruction_def, EL_APPEND_EQN, u2s_setup_def,
       u2s_inst_def, mk_inst_def] >>
  simp[arithmeticTheory.ADD1] >>
  `eval_operand buf (s with
      <|vs_vars := s.vs_vars |+ (u2s_var a 0,n2w x) |+ (u2s_var a 1,0w);
        vs_inst_idx := LENGTH pre + 2|>) = SOME (n2w b)` by
    (Cases_on `buf` >> gvs[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  simp[] >>
  qmatch_goalsub_abbrev_tac `gas_path_ptr _ _ _ _ _ gg tt mid` >>
  qmatch_goalsub_abbrev_tac `OK dest` >>
  `dest = jump_to (u2s_label a 0) mid` by
    simp[Abbr `dest`, Abbr `mid`, jump_to_def] >>
  pop_assum SUBST1_TAC >> irule_at Any uint_jump_counted_path >>
  simp[Abbr `mid`, get_instruction_def, EL_APPEND_EQN, u2s_setup_def,
       u2s_inst_def, mk_inst_def, arithmeticTheory.ADD1]
QED

Theorem uint_clean_scalar_counted_prefix:
  MEM opc [Mod; Div; EQ; ADD] /\
  (!op. MEM op ops ==> op_taint tn op = {} /\ op_prov G op = NONE) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc ops [out]) /\
  step_inst_base (mk_inst id opc ops [out]) s = OK (update_var out w s) /\
  gas_path_ptr D 0 ctx fn PG (DRESTRICT G (COMPL {out}))
    (tn with t_var := tn.t_var |+ (out,{}))
    (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx) n G' tn' r ==>
  gas_path_ptr D 0 ctx fn PG G tn s n G' tn' r
Proof
  strip_tac >> drule_all uint_clean_scalar_counted_edge >>
  disch_then (qspecl_then [`PG`, `D`] assume_tac) >>
  metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]
QED

Theorem u2s_digit_prepare_counted_ptr:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block (u2s_label a 2) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 2; bb_instructions := u2s_body a buf n|> /\
  s.vs_current_bb = u2s_label a 2 /\ s.vs_inst_idx = 0 /\
  lookup_var (u2s_var a 0) s = SOME xw /\
  op_taint tn (Var (u2s_var a 0)) = {} /\ FLOOKUP G (u2s_var a 0) = NONE ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT (DRESTRICT G (COMPL {u2s_var a 5})) (COMPL {u2s_var a 6}))
    (tn with t_var := tn.t_var |+ (u2s_var a 5,{}) |+ (u2s_var a 6,{}))
    (OK (update_var (u2s_var a 6) (48w + safe_mod xw 10w)
      (update_var (u2s_var a 5) (safe_mod xw 10w) s) with vs_inst_idx := 2))
Proof
  strip_tac >> irule uint_clean_scalar_counted_prefix >>
  simp[get_instruction_def, u2s_body_def, u2s_inst_def, mk_inst_def] >>
  qexists_tac `safe_mod xw 10w` >>
  conj_tac >- (rpt strip_tac >> gvs[op_taint_def, op_prov_def]) >>
  conj_tac >- simp[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  irule uint_clean_scalar_counted_prefix >>
  simp[update_var_def, get_instruction_def, u2s_body_def, u2s_inst_def, mk_inst_def] >>
  qexists_tac `48w + safe_mod xw 10w` >>
  conj_tac >- (rpt strip_tac >> gvs[op_taint_def, op_prov_def,
                                  FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]) >>
  conj_tac >- simp[step_inst_base_def, exec_pure2_def, eval_operand_def,
                   lookup_var_def, FLOOKUP_UPDATE, update_var_def] >>
  irule (cj 1 gas_path_ptr_rules) >> simp[]
QED
