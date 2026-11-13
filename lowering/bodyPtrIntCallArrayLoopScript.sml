(* Pointer control for the non-fast typed-array copy loop.  These facts
   concern its concrete compiler header, not execution of a child copy. *)
Theory bodyPtrIntCallArrayLoop
Ancestors
  typedArrayLoopCode typedArrayLoopHeader typedArrayLoopAddress typedArrayLoopCounter
  bodyPtrBopScalarSeq bodyPtrBopInLoopSegments bodyPtrBopInLoopControl fragGasSeqPtr
  ptrDiscipline fragExec ssaOperandFrame exprLoweringProps
  bodyPtrBytestringBuiltinsUintBody fragGasSeqAbort
  venomInst venomState venomExecSemantics fragGasPathPtr compileEnv finite_map pred_set list rich_list

Theorem intcall_typed_array_header_scalar[local]:
  compiler_var_name vb 1 NOTIN R /\ compiler_var_name vb 2 NOTIN R ==>
  bop_scalar_seq R {Var (compiler_var_name vb 0); len}
    (TAKE 2 (typed_array_loop_header id vb bl el len))
    {Var (compiler_var_name vb 2); Var (compiler_var_name vb 1);
     Var (compiler_var_name vb 0); len}
Proof
  strip_tac >> simp[typed_array_loop_header_def] >>
  pure_once_rewrite_tac[bop_scalar_seq_def] >> disj1_tac >>
  qexistsl_tac [`id + 2`, `LT`, `[Var (compiler_var_name vb 0); len]`,
    `compiler_var_name vb 1`] >> simp[] >>
  pure_once_rewrite_tac[bop_scalar_seq_def] >> disj1_tac >>
  qexistsl_tac [`id + 3`, `ISZERO`, `[Var (compiler_var_name vb 1)]`,
    `compiler_var_name vb 2`] >> simp[bop_scalar_seq_def]
QED

Theorem intcall_typed_array_header_prefix_counted:
  !D ctx fn PG G tn s id vb bl el len cw lw bb R.
  compiler_var_name vb 1 NOTIN R /\ compiler_var_name vb 2 NOTIN R /\
  op_prov G (Var (compiler_var_name vb 0)) = NONE /\
  op_taint tn (Var (compiler_var_name vb 0)) = {} /\
  op_prov G len = NONE /\ op_taint tn len = {} /\
  eval_operand (Var (compiler_var_name vb 0)) s = SOME cw /\
  eval_operand len s = SOME lw /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = typed_array_loop_header id vb bl el len ==>
  ?H tf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tf
      (OK ((typed_array_loop_header_state vb cw lw s) with vs_inst_idx := 2)) /\
    op_prov H (Var (compiler_var_name vb 2)) = NONE /\
    op_taint tf (Var (compiler_var_name vb 2)) = {} /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. x IN R ==> FLOOKUP H x = FLOOKUP G x /\
      FLOOKUP tf.t_var x = FLOOKUP tn.t_var x)
Proof
  rpt gen_tac >> strip_tac >>
  `run_inst_seq (TAKE 2 (typed_array_loop_header id vb bl el len)) s =
    OK (typed_array_loop_header_state vb cw lw s)` by
    (irule typed_array_loop_header_execution >> simp[]) >>
  `bop_scalar_seq R {Var (compiler_var_name vb 0); len}
    (TAKE 2 (typed_array_loop_header id vb bl el len))
    {Var (compiler_var_name vb 2); Var (compiler_var_name vb 1);
     Var (compiler_var_name vb 0); len}` by
    (irule intcall_typed_array_header_scalar >> simp[]) >>
  `!op. op IN {Var (compiler_var_name vb 0); len} ==>
    op_prov G op = NONE /\ op_taint tn op = {}` by
    (simp[] >> rpt strip_tac >> gvs[]) >>
  `isPREFIX (TAKE 2 (typed_array_loop_header id vb bl el len))
    (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[typed_array_loop_header_def] >>
  drule_all bop_scalar_seq_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`] >> gvs[typed_array_loop_header_def]
QED

Theorem intcall_typed_array_header_counted:
  !D ctx fn PG G tn s id vb bl el len cw lw bb R.
  compiler_var_name vb 1 NOTIN R /\ compiler_var_name vb 2 NOTIN R /\
  op_prov G (Var (compiler_var_name vb 0)) = NONE /\
  op_taint tn (Var (compiler_var_name vb 0)) = {} /\
  op_prov G len = NONE /\ op_taint tn len = {} /\
  eval_operand (Var (compiler_var_name vb 0)) s = SOME cw /\
  eval_operand len s = SOME lw /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = typed_array_loop_header id vb bl el len ==>
  ?H tf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tf
      (OK (jump_to (if w2n cw < w2n lw then bl else el)
        (typed_array_loop_header_state vb cw lw s))) /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. x IN R ==> FLOOKUP H x = FLOOKUP G x /\
      FLOOKUP tf.t_var x = FLOOKUP tn.t_var x)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all intcall_typed_array_header_prefix_counted >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `OK u` >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = 2` by
    simp[Abbr `u`] >>
  `get_instruction bb u.vs_inst_idx =
    SOME (mk_inst (id+4) JNZ [Var (compiler_var_name vb 2); Label el; Label bl] [])` by
    simp[get_instruction_def, typed_array_loop_header_def] >>
  `eval_operand (Var (compiler_var_name vb 2)) u =
    SOME (bool_to_word (~(w2n cw < w2n lw)))` by
    simp[Abbr `u`, typed_array_loop_header_state_def,
      eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `gas_path_ptr D 0 ctx fn PG H tf u 0 H tf
    (OK (jump_to (if w2n cw < w2n lw then bl else el) u))` by
    (`lookup_block u.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
     drule_all membership_jnz_path >>
     disch_then (qspecl_then [`PG`, `H`, `D`] mp_tac) >>
     Cases_on `w2n cw < w2n lw` >> simp[]) >>
  drule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  qexistsl_tac [`H`, `tf`] >> simp[] >>
  gvs[Abbr `u`, jump_to_def]
QED

(* The offset multiplications are scalar even when the two base operands
   carry allocation provenance.  Keep those base operands in the frame. *)
Theorem intcall_typed_array_offsets_scalar[local]:
  compiler_var_name vb 3 NOTIN R /\ compiler_var_name vb 4 NOTIN R ==>
  bop_scalar_seq R {Var (compiler_var_name vb 0); Lit (n2w ss); Lit (n2w ds)}
    (TAKE 2 (typed_array_loop_addresses id vb dst src ds ss))
    {Var (compiler_var_name vb 4); Var (compiler_var_name vb 3);
     Var (compiler_var_name vb 0); Lit (n2w ss); Lit (n2w ds)}
Proof
  strip_tac >> simp[typed_array_loop_addresses_def] >>
  pure_once_rewrite_tac[bop_scalar_seq_def] >> disj1_tac >>
  qexistsl_tac [`id + 5`, `MUL`,
    `[Var (compiler_var_name vb 0); Lit (n2w ss)]`, `compiler_var_name vb 3`] >>
  simp[] >> pure_once_rewrite_tac[bop_scalar_seq_def] >> disj1_tac >>
  qexistsl_tac [`id + 6`, `MUL`,
    `[Var (compiler_var_name vb 0); Lit (n2w ds)]`, `compiler_var_name vb 4`] >>
  simp[bop_scalar_seq_def]
QED

Theorem intcall_typed_array_offsets_counted:
  !D ctx fn PG G tn s id vb dst src ds ss cw bb R.
  compiler_var_name vb 3 NOTIN R /\ compiler_var_name vb 4 NOTIN R /\
  op_prov G (Var (compiler_var_name vb 0)) = NONE /\
  op_taint tn (Var (compiler_var_name vb 0)) = {} /\
  eval_operand (Var (compiler_var_name vb 0)) s = SOME cw /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (typed_array_loop_addresses id vb dst src ds ss) bb.bb_instructions ==>
  ?H tf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tf
      (OK (update_var (compiler_var_name vb 4) (cw * n2w ds)
        (update_var (compiler_var_name vb 3) (cw * n2w ss) s)
        with vs_inst_idx := 2)) /\
    op_prov H (Var (compiler_var_name vb 3)) = NONE /\
    op_prov H (Var (compiler_var_name vb 4)) = NONE /\
    op_taint tf (Var (compiler_var_name vb 3)) = {} /\
    op_taint tf (Var (compiler_var_name vb 4)) = {} /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. x IN R ==> FLOOKUP H x = FLOOKUP G x /\
      FLOOKUP tf.t_var x = FLOOKUP tn.t_var x)
Proof
  rpt gen_tac >> strip_tac >>
  `bop_scalar_seq R {Var (compiler_var_name vb 0); Lit (n2w ss); Lit (n2w ds)}
    (TAKE 2 (typed_array_loop_addresses id vb dst src ds ss))
    {Var (compiler_var_name vb 4); Var (compiler_var_name vb 3);
     Var (compiler_var_name vb 0); Lit (n2w ss); Lit (n2w ds)}` by
    (irule intcall_typed_array_offsets_scalar >> simp[]) >>
  `!op. op IN {Var (compiler_var_name vb 0); Lit (n2w ss); Lit (n2w ds)} ==>
    op_prov G op = NONE /\ op_taint tn op = {}` by
    (simp[op_prov_def, op_taint_def] >> rpt strip_tac >> gvs[op_prov_def, op_taint_def]) >>
  `run_inst_seq (TAKE 2 (typed_array_loop_addresses id vb dst src ds ss)) s =
    OK (update_var (compiler_var_name vb 4) (cw * n2w ds)
      (update_var (compiler_var_name vb 3) (cw * n2w ss) s))` by
    (simp[typed_array_loop_addresses_def, run_inst_seq_def,
      step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
      eval_operand_update_var_avoids] >>
     gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `isPREFIX (TAKE 2 (typed_array_loop_addresses id vb dst src ds ss))
    (DROP s.vs_inst_idx bb.bb_instructions)` by
    (irule isPREFIX_TRANS >>
     qexists_tac `typed_array_loop_addresses id vb dst src ds ss` >>
     conj_tac >- simp[typed_array_loop_addresses_def] >> simp[]) >>
  drule_all bop_scalar_seq_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`] >> gvs[typed_array_loop_addresses_def]
QED

(* The last two address instructions retain the independent allocation
   sites of source and destination; no scalar provenance premise is made
   about either base pointer. *)
Theorem intcall_typed_array_address_suffix_counted:
  !D ctx fn PG G tn s id vb dst src ds ss so doff da sa dp sp bb.
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ s.vs_inst_idx = 2 /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (typed_array_loop_addresses id vb dst src ds ss) bb.bb_instructions /\
  eval_operand src s = SOME sa /\ eval_operand dst s = SOME da /\
  eval_operand (Var (compiler_var_name vb 3)) s = SOME so /\
  eval_operand (Var (compiler_var_name vb 4)) s = SOME doff /\
  op_prov G src = SOME sp /\ op_prov G dst = SOME dp /\
  op_taint tn src = {} /\ op_taint tn dst = {} /\
  op_taint tn (Var (compiler_var_name vb 3)) = {} /\
  op_taint tn (Var (compiler_var_name vb 4)) = {} /\
  dst <> Var (compiler_var_name vb 5) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (G |+ (compiler_var_name vb 5,sp) |+ (compiler_var_name vb 6,dp))
    (tn with t_var := tn.t_var |+ (compiler_var_name vb 5,{})
                               |+ (compiler_var_name vb 6,{}))
    (OK (update_var (compiler_var_name vb 6) (da+doff)
      (update_var (compiler_var_name vb 5) (sa+so) s) with vs_inst_idx := 4))
Proof
  rpt gen_tac >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME
    (mk_inst (id+7) ADD [src; Var (compiler_var_name vb 3)]
      [compiler_var_name vb 5]) /\
   get_instruction bb 3 = SOME
    (mk_inst (id+8) ADD [dst; Var (compiler_var_name vb 4)]
      [compiler_var_name vb 6])` by
    (gvs[IS_PREFIX_APPEND] >>
     simp[typed_array_loop_addresses_def, get_instruction_def]) >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (G |+ (compiler_var_name vb 5,sp))
    (tn with t_var := tn.t_var |+ (compiler_var_name vb 5,{}))
    (OK (update_var (compiler_var_name vb 5) (sa+so) s
      with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule uint_pointer_add_site_edge >> simp[] >>
     qexistsl_tac [`id+7`, `src`, `Var (compiler_var_name vb 3)`] >> gvs[]) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr_edge _ _ _ _ _ _ _ _ _ g t (OK mid)` >>
  `eval_operand dst mid = SOME da /\
   eval_operand (Var (compiler_var_name vb 4)) mid = SOME doff /\
   op_prov g dst = SOME dp /\ op_taint t dst = {} /\
   op_taint t (Var (compiler_var_name vb 4)) = {}` by
    (simp[Abbr `mid`, Abbr `g`, Abbr `t`, eval_operand_update_var_avoids] >>
     Cases_on `dst` >> gvs[op_prov_def, op_taint_def, FLOOKUP_UPDATE]) >>
  `gas_path_ptr_edge D 0 ctx fn PG g t mid 0
    (g |+ (compiler_var_name vb 6,dp))
    (t with t_var := t.t_var |+ (compiler_var_name vb 6,{}))
    (OK (update_var (compiler_var_name vb 6) (da+doff) mid
      with vs_inst_idx := SUC mid.vs_inst_idx))` by
    (irule uint_pointer_add_site_edge >>
     simp[Abbr `mid`, update_var_def] >>
     qexistsl_tac [`id+8`, `dst`, `Var (compiler_var_name vb 4)`] >>
     gvs[update_var_def]) >>
  `gas_path_ptr D 0 ctx fn PG g t mid 0
    (g |+ (compiler_var_name vb 6,dp))
    (t with t_var := t.t_var |+ (compiler_var_name vb 6,{}))
    (OK (update_var (compiler_var_name vb 6) (da+doff) mid
      with vs_inst_idx := SUC mid.vs_inst_idx))` by
    (`~(update_var (compiler_var_name vb 6) (da+doff) mid
         with vs_inst_idx := SUC mid.vs_inst_idx).vs_halted` by
        simp[Abbr `mid`, update_var_def] >>
     metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0
    (g |+ (compiler_var_name vb 6,dp))
    (t with t_var := t.t_var |+ (compiler_var_name vb 6,{}))
    (OK (update_var (compiler_var_name vb 6) (da+doff) mid
      with vs_inst_idx := SUC mid.vs_inst_idx))` by
    metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES] >>
  gvs[Abbr `mid`, Abbr `g`, Abbr `t`, update_var_def]
QED

Theorem intcall_typed_array_counter_scalar[local]:
  compiler_var_name vb 0 NOTIN R /\ counter NOTIN R ==>
  bop_scalar_seq R {Var counter; Lit 1w}
    (TAKE 2 (typed_array_loop_counter id vb counter cl))
    {Var counter; Var (compiler_var_name vb 0); Lit 1w}
Proof
  strip_tac >> simp[typed_array_loop_counter_def] >>
  pure_once_rewrite_tac[bop_scalar_seq_def] >> disj1_tac >>
  qexistsl_tac [`id`, `ADD`, `[Var counter; Lit 1w]`, `compiler_var_name vb 0`] >>
  simp[] >> pure_once_rewrite_tac[bop_scalar_seq_def] >> disj1_tac >>
  qexistsl_tac [`id+1`, `ASSIGN`, `[Var (compiler_var_name vb 0)]`, `counter`] >>
  simp[bop_scalar_seq_def, EXTENSION] >> metis_tac[]
QED

Theorem intcall_typed_array_counter_counted:
  !D ctx fn PG G tn s id vb counter cl cw bb R.
  compiler_var_name vb 0 NOTIN R /\ counter NOTIN R /\
  op_prov G (Var counter) = NONE /\ op_taint tn (Var counter) = {} /\
  eval_operand (Var counter) s = SOME cw /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (typed_array_loop_counter id vb counter cl)
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?H tf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tf
      (OK (jump_to cl (typed_array_loop_counter_state vb counter cw s))) /\
    op_prov H (Var counter) = NONE /\ op_taint tf (Var counter) = {} /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. x IN R ==> FLOOKUP H x = FLOOKUP G x /\
      FLOOKUP tf.t_var x = FLOOKUP tn.t_var x)
Proof
  rpt gen_tac >> strip_tac >>
  `bop_scalar_seq R {Var counter; Lit 1w}
    (TAKE 2 (typed_array_loop_counter id vb counter cl))
    {Var counter; Var (compiler_var_name vb 0); Lit 1w}` by
    (irule intcall_typed_array_counter_scalar >> simp[]) >>
  `!op. op IN {Var counter; Lit 1w} ==>
    op_prov G op = NONE /\ op_taint tn op = {}` by
    (simp[] >> rpt strip_tac >> gvs[op_prov_def, op_taint_def]) >>
  `run_inst_seq (TAKE 2 (typed_array_loop_counter id vb counter cl)) s =
    OK (typed_array_loop_counter_state vb counter cw s)` by
    (irule typed_array_loop_counter_execution >> simp[]) >>
  `isPREFIX (TAKE 2 (typed_array_loop_counter id vb counter cl))
    (DROP s.vs_inst_idx bb.bb_instructions)` by
    (irule isPREFIX_TRANS >> qexists_tac `typed_array_loop_counter id vb counter cl` >>
     conj_tac >- simp[typed_array_loop_counter_def] >> simp[]) >>
  drule_all bop_scalar_seq_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `OK u` >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb /\
    u.vs_inst_idx = s.vs_inst_idx + 2` by
    simp[Abbr `u`, typed_array_loop_counter_def] >>
  `get_instruction bb u.vs_inst_idx = SOME (mk_inst (id+2) JMP [Label cl] [])` by
    (qpat_x_assum `isPREFIX (typed_array_loop_counter _ _ _ _) _` mp_tac >>
     pure_rewrite_tac[typed_array_loop_counter_def] >> strip_tac >>
     dxrule instruction_prefix_cursor >> strip_tac >>
     dxrule instruction_prefix_cursor >> strip_tac >>
     drule instruction_prefix_cursor >> simp[arithmeticTheory.ADD_CLAUSES] >>
     `s.vs_inst_idx + 2 = SUC (SUC s.vs_inst_idx)` by decide_tac >> simp[]) >>
  `gas_path_ptr D 0 ctx fn PG G' tn' u 0 G' tn' (OK (jump_to cl u))` by
    (irule membership_jump_path >> simp[] >> metis_tac[]) >>
  drule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  qexistsl_tac [`G'`, `tn'`] >>
  gvs[Abbr `u`, typed_array_loop_counter_def, jump_to_def]
QED

Theorem intcall_typed_array_entry_scalar[local]:
  compiler_var_name vb 0 NOTIN R ==>
  bop_scalar_seq R {Lit 0w}
    (TAKE 1 (typed_array_loop_entry id vb cl))
    {Var (compiler_var_name vb 0); Lit 0w}
Proof
  strip_tac >> simp[typed_array_loop_entry_def] >>
  pure_once_rewrite_tac[bop_scalar_seq_def] >> disj1_tac >>
  qexistsl_tac [`id`, `ASSIGN`, `[Lit 0w]`, `compiler_var_name vb 0`] >>
  simp[bop_scalar_seq_def]
QED

Theorem intcall_typed_array_entry_counted:
  !D ctx fn PG G tn s id vb cl bb R.
  compiler_var_name vb 0 NOTIN R /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (typed_array_loop_entry id vb cl)
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?H tf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tf
      (OK (jump_to cl (update_var (compiler_var_name vb 0) 0w s))) /\
    op_prov H (Var (compiler_var_name vb 0)) = NONE /\
    op_taint tf (Var (compiler_var_name vb 0)) = {} /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. x IN R ==> FLOOKUP H x = FLOOKUP G x /\
      FLOOKUP tf.t_var x = FLOOKUP tn.t_var x)
Proof
  rpt gen_tac >> strip_tac >>
  `bop_scalar_seq R {Lit 0w}
    (TAKE 1 (typed_array_loop_entry id vb cl))
    {Var (compiler_var_name vb 0); Lit 0w}` by
    (irule intcall_typed_array_entry_scalar >> simp[]) >>
  `!op. op IN {Lit 0w} ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    simp[op_prov_def, op_taint_def] >>
  `run_inst_seq (TAKE 1 (typed_array_loop_entry id vb cl)) s =
    OK (update_var (compiler_var_name vb 0) 0w s)` by
    simp[typed_array_loop_entry_def, run_inst_seq_def,
      step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def] >>
  `isPREFIX (TAKE 1 (typed_array_loop_entry id vb cl))
    (DROP s.vs_inst_idx bb.bb_instructions)` by
    (irule isPREFIX_TRANS >> qexists_tac `typed_array_loop_entry id vb cl` >>
     conj_tac >- simp[typed_array_loop_entry_def] >> simp[]) >>
  drule_all bop_scalar_seq_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `OK u` >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb /\
    u.vs_inst_idx = s.vs_inst_idx + 1` by
    simp[Abbr `u`, typed_array_loop_entry_def, update_var_def] >>
  `get_instruction bb u.vs_inst_idx = SOME (mk_inst (id+1) JMP [Label cl] [])` by
    (qpat_x_assum `isPREFIX (typed_array_loop_entry _ _ _) _` mp_tac >>
     pure_rewrite_tac[typed_array_loop_entry_def] >> strip_tac >>
     dxrule instruction_prefix_cursor >> strip_tac >>
     drule instruction_prefix_cursor >> simp[arithmeticTheory.ADD1]) >>
  `gas_path_ptr D 0 ctx fn PG G' tn' u 0 G' tn' (OK (jump_to cl u))` by
    (irule membership_jump_path >> simp[] >> metis_tac[]) >>
  drule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  qexistsl_tac [`G'`, `tn'`] >>
  gvs[Abbr `u`, typed_array_loop_entry_def, jump_to_def]
QED

Theorem intcall_typed_array_addresses_counted:
  !D ctx fn PG G tn s id vb dst src ds ss cw da sa dp sp bb R.
  compiler_var_name vb 3 NOTIN R /\ compiler_var_name vb 4 NOTIN R /\
  compiler_var_name vb 5 NOTIN R /\ compiler_var_name vb 6 NOTIN R /\
  src <> Var (compiler_var_name vb 3) /\ src <> Var (compiler_var_name vb 4) /\
  dst <> Var (compiler_var_name vb 3) /\ dst <> Var (compiler_var_name vb 4) /\
  dst <> Var (compiler_var_name vb 5) /\
  op_prov G (Var (compiler_var_name vb 0)) = NONE /\
  op_taint tn (Var (compiler_var_name vb 0)) = {} /\
  eval_operand (Var (compiler_var_name vb 0)) s = SOME cw /\
  eval_operand src s = SOME sa /\ eval_operand dst s = SOME da /\
  op_prov G src = SOME sp /\ op_prov G dst = SOME dp /\
  op_taint tn src = {} /\ op_taint tn dst = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (typed_array_loop_addresses id vb dst src ds ss) bb.bb_instructions ==>
  ?H tf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tf
      (OK (update_var (compiler_var_name vb 6) (da + cw * n2w ds)
        (update_var (compiler_var_name vb 5) (sa + cw * n2w ss)
          (update_var (compiler_var_name vb 4) (cw * n2w ds)
            (update_var (compiler_var_name vb 3) (cw * n2w ss) s)))
        with vs_inst_idx := 4)) /\
    op_prov H (Var (compiler_var_name vb 5)) = SOME sp /\
    op_prov H (Var (compiler_var_name vb 6)) = SOME dp /\
    op_taint tf (Var (compiler_var_name vb 5)) = {} /\
    op_taint tf (Var (compiler_var_name vb 6)) = {} /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. x IN R ==> FLOOKUP H x = FLOOKUP G x /\
      FLOOKUP tf.t_var x = FLOOKUP tn.t_var x)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `protected = R UNION {x | src = Var x \/ dst = Var x}` >>
  `compiler_var_name vb 3 NOTIN protected /\ compiler_var_name vb 4 NOTIN protected` by
    simp[Abbr `protected`] >>
  drule_all intcall_typed_array_offsets_counted >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr _ _ _ _ _ _ _ _ _ H tf (OK u)` >>
  `eval_operand src u = SOME sa /\ eval_operand dst u = SOME da /\
   eval_operand (Var (compiler_var_name vb 3)) u = SOME (cw * n2w ss) /\
   eval_operand (Var (compiler_var_name vb 4)) u = SOME (cw * n2w ds)` by
    (simp[Abbr `u`, eval_operand_update_var_avoids] >>
     gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `op_prov H src = SOME sp /\ op_prov H dst = SOME dp /\
   op_taint tf src = {} /\ op_taint tf dst = {}` by
    (Cases_on `src` >> Cases_on `dst` >>
     gvs[op_prov_def, op_taint_def, Abbr `protected`]) >>
  `~u.vs_halted /\ u.vs_inst_idx = 2 /\
    lookup_block u.vs_current_bb fn.fn_blocks = SOME bb` by
    simp[Abbr `u`, update_var_def] >>
  drule_all intcall_typed_array_address_suffix_counted >>
  disch_then (qspecl_then [`D`, `PG`] assume_tac) >>
  drule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  qexistsl_tac [`H |+ (compiler_var_name vb 5, sp) |+ (compiler_var_name vb 6, dp)`,
    `tf with t_var := tf.t_var |+ (compiler_var_name vb 5, {}) |+
      (compiler_var_name vb 6, {})`] >>
  gvs[op_prov_def, op_taint_def, FLOOKUP_UPDATE, Abbr `u`, update_var_def,
      Abbr `protected`] >>
  rpt strip_tac >> simp[] >> metis_tac[]
QED
