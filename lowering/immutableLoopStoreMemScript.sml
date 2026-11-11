(* Memory checks for runtime constructor immutable writes. *)
Theory immutableLoopStoreMem
Ancestors
  immutableAssignStoreMem immutableCopyExecution immutableWordExecution fragGasSeqMem
  placeCopyControlPath stmtForRangeMemoryParts fragGasPathMem
  instMemFrontier memSafeRun fragExecMem
  context compileEnv emitHelper emitHelperProps loweringStateRelDefs
  exprLoweringProps venomExecSemantics venomState venomInst
  words arithmetic list rich_list finite_map

Theorem immutable_loop_body_mem_ok:
  eval_operand src q = SOME a /\ eval_operand dst q = SOME b /\
  eval_operand region q = SOME 0w /\
  eval_operand (Var cv) q = SOME (n2w i) /\
  ALL_DISTINCT [cv;mv;sv;vv;dm;dv;av;nv] /\
  (!x. MEM x [cv;mv;sv;vv;dm;dv;av;nv] ==>
       src <> Var x /\ dst <> Var x /\ region <> Var x) /\
  w2n (a+n2w (32*i)) + 32 <= q.vs_alloca_next /\
  w2n (b+n2w (32*i)) + 32 <= q.vs_alloca_next ==>
  run_inst_seq_mem_ok
    [mk_inst id MUL [Var cv; Lit 32w] [mv];
     mk_inst (id+1) ADD [src; Var mv] [sv];
     mk_inst (id+2) MLOAD [Var sv] [vv];
     mk_inst (id+3) MUL [Var cv; Lit 32w] [dm];
     mk_inst (id+4) ADD [dst; Var dm] [dv];
     mk_inst (id+5) ADD [region; Var dv] [av];
     mk_inst (id+6) ISTORE [Var av; Var vv] [];
     mk_inst (id+7) ADD [Var cv; Lit 1w] [nv];
     mk_inst (id+8) ASSIGN [Var nv] [cv]] q
Proof
  strip_tac >>
  `n2w i * 32w = (n2w (32*i):bytes32)` by
    simp[GSYM word_mul_n2w, WORD_MULT_COMM] >>
  fs[ALL_DISTINCT, MEM, DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[run_inst_seq_mem_ok_def, step_inst_base_opcode_eqs,
       exec_pure2_def, exec_read1_def,
       below_frontier_MLOAD, below_frontier_ISTORE,
       below_frontier_no_ranges, inst_dload_in_section_def,
       mk_inst_def, eval_operand_lit, slot_copy_operand_update,
       immutable_word_istore_operand_frame, WORD_ADD_0]
QED

Theorem immutable_loop_body_mem_path:
  ~q.vs_halted /\
  lookup_block q.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX
    [mk_inst id MUL [Var cv; Lit 32w] [mv];
     mk_inst (id+1) ADD [src; Var mv] [sv];
     mk_inst (id+2) MLOAD [Var sv] [vv];
     mk_inst (id+3) MUL [Var cv; Lit 32w] [dm];
     mk_inst (id+4) ADD [dst; Var dm] [dv];
     mk_inst (id+5) ADD [region; Var dv] [av];
     mk_inst (id+6) ISTORE [Var av; Var vv] [];
     mk_inst (id+7) ADD [Var cv; Lit 1w] [nv];
     mk_inst (id+8) ASSIGN [Var nv] [cv]]
    (DROP q.vs_inst_idx bb.bb_instructions) /\
  immutable_loop_frame sa sb s a b i q /\
  eval_operand src q = SOME a /\ eval_operand dst q = SOME b /\
  eval_operand region q = SOME 0w /\
  eval_operand (Var cv) q = SOME (n2w i) /\
  ALL_DISTINCT [cv;mv;sv;vv;dm;dv;av;nv] /\
  (!x. MEM x [cv;mv;sv;vv;dm;dv;av;nv] ==>
       src <> Var x /\ dst <> Var x /\ region <> Var x /\ not_fresh_at sb x) /\
  (!x. not_fresh_at sa x ==> ~MEM x [cv;mv;sv;vv;dm;dv;av;nv]) /\
  w2n (a+n2w (32*i)) + 32 <= q.vs_alloca_next /\
  w2n (b+n2w (32*i)) + 32 <= q.vs_alloca_next ==>
  ?t. gas_path_mem ctx func q 0 (OK t) /\
      immutable_loop_frame sa sb s a b (SUC i) t /\
      eval_operand (Var cv) t = SOME (n2w (SUC i)) /\
      ~t.vs_halted /\ t.vs_current_bb = q.vs_current_bb /\
      t.vs_inst_idx = q.vs_inst_idx + 9
Proof
  strip_tac >>
  `!x. MEM x [cv;mv;sv;vv;dm;dv;av;nv] ==>
       src <> Var x /\ dst <> Var x /\ region <> Var x` by metis_tac[] >>
  drule_all immutable_loop_body_run >>
  disch_then (qspec_then `id` mp_tac) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_inst_seq code q = OK result` >>
  `immutable_loop_frame sa sb s a b (SUC i) result` by
    (simp_tac bool_ss [Abbr `result`] >>
     irule immutable_loop_body_frame >> metis_tac[]) >>
  `run_inst_seq_mem_ok code q` by
    (simp_tac bool_ss [Abbr `code`] >>
     irule immutable_loop_body_mem_ok >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code` by
    simp[Abbr `code`, mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_mem >>
  disch_then (qspec_then `ctx` mp_tac) >>
  simp[Abbr `code`, mk_inst_def, is_terminator_def] >> strip_tac >>
  qexists_tac `result with vs_inst_idx := q.vs_inst_idx + 9` >>
  simp[immutable_loop_frame_control] >>
  simp[Abbr `result`, eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE, istore_def, mstore_def]
QED

Theorem immutable_loop_test_mem_path:
  ~q.vs_halted /\
  lookup_block q.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id EQ [Var cv; cnt] [tv]]
    (DROP q.vs_inst_idx bb.bb_instructions) /\
  immutable_loop_frame sa sb s a b i q /\
  eval_operand (Var cv) q = SOME (n2w i) /\
  eval_operand cnt q = SOME (n2w n) /\
  cv <> tv /\ (!x. not_fresh_at sa x ==> x <> tv) /\
  not_fresh_at sb tv /\ i <= n /\ n < dimword (:256) ==>
  ?t. gas_path_mem ctx func q 0 (OK t) /\
      immutable_loop_frame sa sb s a b i t /\
      eval_operand (Var cv) t = SOME (n2w i) /\
      eval_operand (Var tv) t = SOME (if i = n then 1w else 0w) /\
      ~t.vs_halted /\ t.vs_current_bb = q.vs_current_bb /\
      t.vs_inst_idx = q.vs_inst_idx + 1
Proof
  strip_tac >>
  `i < dimword (:256)` by decide_tac >>
  `bool_to_word (n2w i = n2w n : bytes32) =
   (if i = n then 1w else 0w)` by
    (Cases_on `i = n` >> simp[n2w_11, LESS_MOD, bool_to_word_def]) >>
  qmatch_asmsub_abbrev_tac `isPREFIX code _` >>
  `run_inst_seq code q =
   OK (update_var tv (if i = n then 1w else 0w) q)` by
    simp[Abbr `code`, run_inst_seq_def, mk_inst_def,
         step_inst_base_opcode_eqs, exec_pure2_def] >>
  `run_inst_seq_mem_ok code q` by
    simp[Abbr `code`, run_inst_seq_mem_ok_def, mk_inst_def,
         step_inst_base_opcode_eqs, exec_pure2_def,
         below_frontier_no_ranges, inst_dload_in_section_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code` by
    simp[Abbr `code`, mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_mem >>
  disch_then (qspec_then `ctx` mp_tac) >>
  simp[Abbr `code`, mk_inst_def] >> strip_tac >>
  qexists_tac `update_var tv (if i = n then 1w else 0w) q
                 with vs_inst_idx := q.vs_inst_idx + 1` >>
  conj_tac >- simp[] >>
  conj_tac >- (simp[immutable_loop_frame_control] >>
               irule immutable_loop_frame_write >> metis_tac[]) >>
  gvs[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem immutable_loop_header_mem_path:
  ~q.vs_halted /\ q.vs_inst_idx = 0 /\
  lookup_block q.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id EQ [Var cv; cnt] [tv];
    mk_inst (id+1) JNZ [Var tv; Label exit; Label body_lbl] []]
    bb.bb_instructions /\
  immutable_loop_frame sa sb s a b i q /\
  eval_operand (Var cv) q = SOME (n2w i) /\
  eval_operand cnt q = SOME (n2w n) /\
  cv <> tv /\ (!x. not_fresh_at sa x ==> x <> tv) /\
  not_fresh_at sb tv /\ i <= n /\ n < dimword (:256) ==>
  ?r. gas_path_mem ctx func q 0 (OK r) /\
      immutable_loop_frame sa sb s a b i r /\
      eval_operand (Var cv) r = SOME (n2w i) /\
      ~r.vs_halted /\ r.vs_inst_idx = 0 /\
      r.vs_current_bb = (if i = n then exit else body_lbl)
Proof
  strip_tac >>
  qpat_assum `isPREFIX _ _`
    (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
  `isPREFIX [mk_inst id EQ [Var cv; cnt] [tv]]
    (DROP q.vs_inst_idx bb.bb_instructions)` by simp[] >>
  drule_all immutable_loop_test_mem_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `get_instruction bb t.vs_inst_idx =
   SOME (mk_inst (id+1) JNZ [Var tv; Label exit; Label body_lbl] [])` by
    simp[get_instruction_def, EL_APPEND_EQN] >>
  `lookup_block t.vs_current_bb func.fn_blocks = SOME bb` by metis_tac[] >>
  drule_all for_range_jnz_zero_path_mem >>
  disch_then (qspec_then `ctx` assume_tac) >>
  `gas_path_mem ctx func t 0
    (OK (jump_to (if i = n then exit else body_lbl) t))` by
    (Cases_on `i = n` >> fs[]) >>
  qexists_tac `jump_to (if i = n then exit else body_lbl) t` >>
  conj_tac >- (drule_all gas_path_mem_then >> simp[]) >>
  conj_tac >- simp[immutable_loop_frame_control] >>
  qpat_x_assum `eval_operand (Var cv) t = _`
    (assume_tac o REWRITE_RULE [eval_operand_def, lookup_var_def]) >>
  simp[jump_to_def, eval_operand_def, lookup_var_def]
QED
