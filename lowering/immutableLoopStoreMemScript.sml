(* Memory checks for runtime constructor immutable writes. *)
Theory immutableLoopStoreMem
Ancestors
  immutableAssignStoreMem immutableCopyExecution immutableWordExecution fragGasSeqMem
  placeCopyControlPath stmtForRangeMemoryParts fragGasPathMem
  bytestringCopyExecution fragExec memContinuation
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

Theorem immutable_transfers_allocation_frame[local]:
  !n off s. (immutable_transfers T T a b n off s).vs_allocas = s.vs_allocas /\
    (immutable_transfers T T a b n off s).vs_alloca_next = s.vs_alloca_next
Proof
  Induct >> simp[immutable_transfers_def, immutable_word_transfer_def,
                istore_def, mstore_def]
QED

Theorem immutable_loop_allocation_frame:
  immutable_loop_frame sa sb s a b i q ==>
  q.vs_allocas = s.vs_allocas /\ q.vs_alloca_next = s.vs_alloca_next
Proof
  simp[immutable_loop_frame_def] >> strip_tac >>
  qpat_x_assum `store_copy_normalize _ _ = _`
    (mp_tac o Q.AP_TERM `\t. (t.vs_allocas,t.vs_alloca_next)`) >>
  simp[stmtSimStoreCopyTheory.store_copy_normalize_def,
       immutable_transfers_allocation_frame]
QED

Theorem immutable_loop_jump_mem_path:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id JMP [Label target] []) ==>
  gas_path_mem ctx func s 0 (OK (jump_to target s))
Proof
  strip_tac >> irule for_range_jump_at_zero_path_mem >>
  conj_tac >- simp[] >>
  qexistsl_tac [`bb`, `mk_inst id JMP [Label target] []`] >>
  simp[mk_inst_def, is_terminator_def, below_frontier_no_ranges,
       inst_dload_in_section_def, step_inst_base_opcode_eqs]
QED

Theorem immutable_loop_iterate_mem:
  lookup_block hdr func.fn_blocks = SOME bbh /\
  isPREFIX [mk_inst idh EQ [Var cv; cnt] [tv];
    mk_inst (idh+1) JNZ [Var tv; Label exit; Label body_lbl] []]
    bbh.bb_instructions /\
  lookup_block body_lbl func.fn_blocks = SOME bbb /\
  isPREFIX
    [mk_inst idb MUL [Var cv; Lit 32w] [mv];
     mk_inst (idb+1) ADD [src; Var mv] [sv];
     mk_inst (idb+2) MLOAD [Var sv] [vv];
     mk_inst (idb+3) MUL [Var cv; Lit 32w] [dm];
     mk_inst (idb+4) ADD [dst; Var dm] [dv];
     mk_inst (idb+5) ADD [region; Var dv] [av];
     mk_inst (idb+6) ISTORE [Var av; Var vv] [];
     mk_inst (idb+7) ADD [Var cv; Lit 1w] [nv];
     mk_inst (idb+8) ASSIGN [Var nv] [cv];
     mk_inst (idb+9) JMP [Label hdr] []] bbb.bb_instructions /\
  ALL_DISTINCT [cv;tv;mv;sv;vv;dm;dv;av;nv] /\
  (!x. MEM x [cv;tv;mv;sv;vv;dm;dv;av;nv] ==> not_fresh_at sb x) /\
  (!x. not_fresh_at sa x ==> ~MEM x [cv;tv;mv;sv;vv;dm;dv;av;nv]) /\
  (!x. src = Var x \/ dst = Var x \/ cnt = Var x \/ region = Var x ==>
       not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  eval_operand cnt s = SOME (n2w n) /\ eval_operand region s = SOME 0w /\
  (!j. j < n ==> w2n (a+n2w (32*j)) + 32 <= s.vs_alloca_next /\
                  w2n (b+n2w (32*j)) + 32 <= s.vs_alloca_next) /\
  n < dimword (:256) /\ k <= n /\
  immutable_loop_frame sa sb s a b k r /\
  eval_operand (Var cv) r = SOME (n2w k) /\
  ~r.vs_halted /\ r.vs_current_bb = hdr /\ r.vs_inst_idx = 0 ==>
  ?t. gas_path_mem ctx func r 0 (OK t) /\
      immutable_loop_frame sa sb s a b n t /\
      eval_operand (Var cv) t = SOME (n2w n) /\
      ~t.vs_halted /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0
Proof
  strip_tac >>
  qabbrev_tac `Inv = \j q. immutable_loop_frame sa sb s a b j q /\
    eval_operand (Var cv) q = SOME (n2w j)` >>
  `?t. gas_marked_path T ctx func r 0 (OK t) /\ Inv n t /\
       ~t.vs_halted /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0`
    suffices_by (simp[fragGasModeTheory.gas_marked_path_def, Abbr `Inv`] >> metis_tac[]) >>
  irule place_copy_iterate_path >> simp[] >>
  reverse conj_tac
  >- (qexistsl_tac [`k`, `n-k`] >> simp[Abbr `Inv`]) >>
  qexists_tac `body_lbl` >> simp[] >>
  conj_tac >- suspend "body" >> suspend "header"
QED

Resume immutable_loop_iterate_mem[body]:
  qunabbrev_tac `Inv` >> BETA_TAC >> rpt gen_tac >> strip_tac >>
  `eval_operand src q = SOME a /\ eval_operand dst q = SOME b /\
   eval_operand region q = SOME 0w` by
    (conj_tac >- (drule_at (Pat `immutable_loop_frame _ _ _ _ _ j q`)
        immutable_loop_frame_operand >>
       disch_then (qspec_then `src` mp_tac) >> simp[] >> metis_tac[]) >>
     conj_tac >- (drule_at (Pat `immutable_loop_frame _ _ _ _ _ j q`)
        immutable_loop_frame_operand >>
       disch_then (qspec_then `dst` mp_tac) >> simp[] >> metis_tac[]) >>
     drule_at (Pat `immutable_loop_frame _ _ _ _ _ j q`)
        immutable_loop_frame_operand >>
     disch_then (qspec_then `region` mp_tac) >> simp[] >> metis_tac[]) >>
  qpat_assum `isPREFIX (_::_::_::_::_::_::_::_::_::_::[]) _`
    (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
  qmatch_asmsub_abbrev_tac `isPREFIX code bbb.bb_instructions` >>
  `isPREFIX (TAKE 9 code) (DROP q.vs_inst_idx bbb.bb_instructions)` by
    simp[Abbr `code`] >>
  `ALL_DISTINCT [cv;mv;sv;vv;dm;dv;av;nv] /\
   (!x. MEM x [cv;mv;sv;vv;dm;dv;av;nv] ==>
     src <> Var x /\ dst <> Var x /\ region <> Var x /\ not_fresh_at sb x) /\
   (!x. not_fresh_at sa x ==> ~MEM x [cv;mv;sv;vv;dm;dv;av;nv])` by
    (fs[ALL_DISTINCT, MEM] >> metis_tac[]) >>
  `lookup_block q.vs_current_bb func.fn_blocks = SOME bbb` by simp[] >>
  `w2n (a+n2w (32*j)) + 32 <= q.vs_alloca_next /\
   w2n (b+n2w (32*j)) + 32 <= q.vs_alloca_next` by
    (drule immutable_loop_allocation_frame >> metis_tac[]) >>
  qunabbrev_tac `code` >>
  qpat_x_assum `isPREFIX (TAKE 9 _) _`
    (assume_tac o SIMP_RULE (srw_ss()) [TAKE_def, Excl "isPREFIX"]) >>
  drule_all immutable_loop_body_mem_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `gas_path_mem ctx func t 0 (OK (jump_to hdr t))` by
    (irule immutable_loop_jump_mem_path >> simp[] >>
     qexists_tac `idb+9` >> simp[get_instruction_def, EL_APPEND_EQN]) >>
  qexists_tac `jump_to hdr t` >>
  conj_tac >- (simp[fragGasModeTheory.gas_marked_path_def] >>
               drule_all gas_path_mem_then >> simp[]) >>
  qpat_x_assum `eval_operand (Var cv) t = _`
    (assume_tac o REWRITE_RULE [eval_operand_def, lookup_var_def]) >>
  simp[immutable_loop_frame_control, jump_to_def, eval_operand_def,
       lookup_var_def, GSYM ADD1]
QED

Resume immutable_loop_iterate_mem[header]:
  qunabbrev_tac `Inv` >> BETA_TAC >> rpt gen_tac >> strip_tac >>
  `eval_operand cnt q = SOME (n2w n)` by
    (drule immutable_loop_frame_operand >>
     disch_then (qspec_then `cnt` mp_tac) >> simp[] >> metis_tac[]) >>
  `cv <> tv /\ (!x. not_fresh_at sa x ==> x <> tv) /\
   not_fresh_at sb tv` by
    (fs[ALL_DISTINCT] >> metis_tac[MEM]) >>
  `lookup_block q.vs_current_bb func.fn_blocks = SOME bbh` by simp[] >>
  drule_all immutable_loop_header_mem_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `r'` >> simp[fragGasModeTheory.gas_marked_path_def]
QED

Finalise immutable_loop_iterate_mem

Theorem immutable_loop_path_mem_cont:
  gas_path_mem ctx func s n (OK t) ==> mem_cont_sim ctx func s t
Proof
  strip_tac >> drule gas_path_mem_exec >>
  simp[mem_cont_sim_def, fragExecTheory.exit_result_def]
QED

Theorem compile_imm_store_loop_mem_path:
  compile_word_copy_loop_base src dst cnt LocMemory LocCode T
    (SOME region) sa = (u,sb) /\
  fn_has_code sa sb func /\ n < dimword (:256) /\
  (!x. src = Var x \/ dst = Var x \/ cnt = Var x \/ region = Var x ==>
       not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  eval_operand cnt s = SOME (n2w n) /\ eval_operand region s = SOME 0w /\
  (!j. j < n ==> w2n (a+n2w (32*j)) + 32 <= s.vs_alloca_next /\
                  w2n (b+n2w (32*j)) + 32 <= s.vs_alloca_next) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      mem_cont_sim ctx func s t /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (t with <|vs_vars := s.vs_vars;
                vs_current_bb := s.vs_current_bb;
                vs_prev_bb := s.vs_prev_bb;
                vs_inst_idx := s.vs_inst_idx|>) =
        immutable_transfers T T a b n 0 s /\
      (fresh_vars_wrt sa s ==> immutable_operand_frame sa s sb t) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all immutable_loop_code >> strip_tac >>
  `?r. gas_path_mem ctx func s 0 (OK r) /\
       immutable_loop_frame sa sb s a b 0 r /\
       eval_operand (Var cv) r = SOME 0w /\ ~r.vs_halted /\
       r.vs_current_bb = hdr /\ r.vs_inst_idx = 0` by suspend "init" >>
  `?t. gas_path_mem ctx func r 0 (OK t) /\
       immutable_loop_frame sa sb s a b n t /\
       eval_operand (Var cv) t = SOME (n2w n) /\
       ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = 0` by
    (`eval_operand (Var cv) r = SOME (n2w 0) /\ 0 <= n` by simp[] >>
     drule_all immutable_loop_iterate_mem >>
     disch_then (qspec_then `ctx` mp_tac) >> simp[]) >>
  `gas_path_mem ctx func s 0 (OK t)` by
    (drule_all gas_path_mem_then >> simp[]) >>
  `mem_cont_sim ctx func s t` by metis_tac[immutable_loop_path_mem_cont] >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    metis_tac[immutable_loop_allocation_frame] >>
  qexists_tac `t` >> simp[] >>
  `t.vs_labels = s.vs_labels` by metis_tac[immutable_loop_frame_shared] >>
  fs[immutable_loop_frame_def, stmtSimStoreCopyTheory.store_copy_normalize_def] >>
  metis_tac[immutable_loop_operand_frame]
QED

Resume compile_imm_store_loop_mem_path[init]:
  `immutable_loop_frame sa sb s a b 0 s` by
    (simp[immutable_loop_frame_def, immutable_transfers_def, fresh_vars_wrt_def,
          stmtSimStoreCopyTheory.store_copy_normalize_def,
          venom_state_component_equality]) >>
  `!x. not_fresh_at sa x ==> x <> cv` by metis_tac[MEM] >>
  `not_fresh_at sb cv` by metis_tac[MEM] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb0` by simp[] >>
  `isPREFIX [mk_inst id0 ASSIGN [Lit 0w] [cv]]
    (DROP s.vs_inst_idx bb0.bb_instructions)` by
    (qpat_assum `isPREFIX [mk_inst _ ASSIGN _ _; _] _`
       (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >> simp[]) >>
  `run_inst_seq [mk_inst id0 ASSIGN [Lit 0w] [cv]] s =
    OK (update_var cv 0w s)` by
    simp[run_inst_seq_def, mk_inst_def,
         step_inst_base_opcode_eqs, eval_operand_lit] >>
  `run_inst_seq_mem_ok [mk_inst id0 ASSIGN [Lit 0w] [cv]] s` by
    simp[run_inst_seq_mem_ok_def, mk_inst_def, step_inst_base_opcode_eqs,
         eval_operand_lit, below_frontier_no_ranges, inst_dload_in_section_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    [mk_inst id0 ASSIGN [Lit 0w] [cv]]` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_mem >>
  disch_then (qspec_then `ctx` mp_tac) >> simp[mk_inst_def] >> strip_tac >>
  qabbrev_tac `t = update_var cv 0w s with
    vs_inst_idx := LENGTH sa.cs_current_insts + 1` >>
  `gas_path_mem ctx func s 0 (OK t)` by simp[Abbr `t`] >>
  `~t.vs_halted /\ t.vs_current_bb = sa.cs_current_bb /\
   t.vs_inst_idx = LENGTH sa.cs_current_insts + 1` by
    simp[Abbr `t`, update_var_def] >>
  `get_instruction bb0 t.vs_inst_idx =
    SOME (mk_inst (id0+1) JMP [Label hdr] [])` by
    (qpat_assum `isPREFIX [mk_inst _ ASSIGN _ _; _] _`
       (mp_then Any strip_assume_tac fragGasSeqAbortTheory.instruction_prefix_cursor) >>
     drule fragGasSeqAbortTheory.instruction_prefix_cursor >> simp[ADD1]) >>
  `gas_path_mem ctx func t 0 (OK (jump_to hdr t))` by
    (irule immutable_loop_jump_mem_path >> simp[] >> metis_tac[]) >>
  qexists_tac `jump_to hdr t` >>
  conj_tac >- (drule_all gas_path_mem_then >> simp[]) >>
  conj_tac >- (simp[immutable_loop_frame_control, Abbr `t`] >>
               irule immutable_loop_frame_write >> simp[] >> metis_tac[]) >>
  simp[Abbr `t`, jump_to_def, eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE]
QED

Finalise compile_imm_store_loop_mem_path

Theorem bytestring_word_count_mem_ok[local]:
  compile_bytestring_word_count src sa = (out,sb) /\
  eval_operand src s = SOME a /\ w2n a + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >>
  gvs[compile_bytestring_word_count_def, emit_op_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def] >>
  simp[emitted_insts_def, DROP_APPEND, SUB_PLUS, run_inst_seq_mem_ok_def,
       mk_inst_def, step_inst_base_opcode_eqs, exec_pure2_def, exec_read1_def,
       SRULE [mk_inst_def] below_frontier_MLOAD,
       below_frontier_no_ranges, inst_dload_in_section_def,
       eval_operand_lit, slot_copy_operand_update]
QED

Theorem bytestring_word_count_mem_path:
  compile_bytestring_word_count src sa = (out,sb) /\
  fn_has_code sa sb func /\
  eval_operand src s = SOME w /\ mload (w2n w) s = n2w len /\
  len + 63 < dimword (:256) /\ w2n w + 32 <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      eval_operand out t = SOME (n2w (1 + word_size len)) /\
      (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all bytestring_word_count_run >> strip_tac >>
  drule bytestring_word_count_shape >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sa sb)
          (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >>
     qexists_tac `l` >> simp[DROP_APPEND, SUB_PLUS]) >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule bytestring_word_count_mem_ok >> metis_tac[]) >>
  drule_all run_inst_seq_gas_path_mem >> strip_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  fs[same_blocks_def, eval_operand_def, lookup_var_def] >>
  fs[venom_state_component_equality] >>
  qpat_x_assum `!ctx. gas_path_mem _ _ _ _ _` (qspec_then `ctx` mp_tac) >>
  simp[ADD_COMM]
QED

Theorem compile_store_immutable_bytestring_mem_path:
  compile_store_immutable_bytestring (SOME region) src dst sa = ((),sb) /\
  fn_has_code sa sb func /\ len + 63 < dimword (:256) /\
  (!x. src = Var x \/ dst = Var x \/ region = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  eval_operand region s = SOME 0w /\ mload (w2n a) s = n2w len /\
  (!j. j < 1 + word_size len ==>
       w2n (a+n2w (32*j)) + 32 <= s.vs_alloca_next /\
       w2n (b+n2w (32*j)) + 32 <= s.vs_alloca_next) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      mem_cont_sim ctx func s t /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (t with <|vs_vars := s.vs_vars;
                vs_current_bb := s.vs_current_bb;
                vs_prev_bb := s.vs_prev_bb;
                vs_inst_idx := s.vs_inst_idx|>) =
        immutable_transfers T T a b (1 + word_size len) 0 s /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  Cases_on `compile_bytestring_word_count src sa` >>
  rename1 `compile_bytestring_word_count src sa = (wc,sm)` >>
  Cases_on `compile_word_copy_loop_base src dst wc LocMemory LocCode T
    (SOME region) sm` >>
  rename1 `compile_word_copy_loop_base src dst wc LocMemory LocCode T
    (SOME region) sm = (u,sn)` >>
  `sn = sb` by
    fs[compile_store_immutable_bytestring_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, pairTheory.UNCURRY] >> gvs[] >>
  drule bytestring_word_count_shape >> strip_tac >>
  `cs_extends sa sm` by
    (irule cs_extends_same_block >> fs[same_blocks_def] >> simp[]) >>
  `ci_mono sm sb` by
    (mp_tac (Q.SPECL [`src`, `dst`, `wc`, `LocMemory`, `LocCode`, `T`,
                      `SOME region`, `sm`] ci_mono_word_copy) >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> fs[ci_mono_def]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> decide_tac) >>
  `!x. wc = Var x ==> not_fresh_at sm x` by
    (qpat_x_assum `compile_bytestring_word_count _ _ = _` mp_tac >>
     simp[compile_bytestring_word_count_def, emit_op_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_id_def, fresh_var_def, emit_def] >>
     strip_tac >> gvs[not_fresh_at_def]) >>
  `1 + word_size len < dimword (:256)` by
    (`(len + 31) DIV 32 <= len + 31` by simp[DIV_LESS_EQ] >>
     fs[vfmConstantsTheory.word_size_def] >> decide_tac) >>
  suspend "execute"
QED

Resume compile_store_immutable_bytestring_mem_path[execute]:
  `w2n a + 32 <= s.vs_alloca_next` by
    (qpat_assum `!j. j < _ ==> w2n _ + 32 <= _ /\ _`
       (qspec_then `0` mp_tac) >>
     simp_tac (srw_ss()) [MULT_0, word_0_n2w, WORD_ADD_0, GSYM ADD1] >>
     metis_tac[]) >>
  drule_all bytestring_word_count_mem_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_path_mem ctx func s 0 (OK r)` >>
  `r.vs_labels = s.vs_labels /\ stmtSimStoreCopy$store_copy_normalize s r = s /\
   r.vs_alloca_next = s.vs_alloca_next /\ r.vs_allocas = s.vs_allocas` by
    (fs[venom_state_component_equality,
        stmtSimStoreCopyTheory.store_copy_normalize_def]) >>
  `!p. (!x. p = Var x ==> not_fresh_at sa x) ==>
       eval_operand p r = eval_operand p s` by
    (Cases >> simp[eval_operand_def]) >>
  `eval_operand src r = SOME a /\ eval_operand dst r = SOME b /\
   eval_operand region r = SOME 0w` by metis_tac[] >>
  `!x. src = Var x \/ dst = Var x \/ wc = Var x \/ region = Var x ==>
       not_fresh_at sm x` by metis_tac[] >>
  `!j. j < 1 + word_size len ==>
       w2n (a+n2w (32*j)) + 32 <= r.vs_alloca_next /\
       w2n (b+n2w (32*j)) + 32 <= r.vs_alloca_next` by simp[] >>
  drule_all compile_imm_store_loop_mem_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `gas_path_mem ctx func s 0 (OK t)` by
    (drule_all gas_path_mem_then >> simp[]) >>
  `mem_cont_sim ctx func s t` by metis_tac[immutable_loop_path_mem_cont] >>
  qexists_tac `t` >> simp[] >>
  qpat_x_assum `(t with <|vs_vars := r.vs_vars; vs_current_bb := r.vs_current_bb;
      vs_prev_bb := r.vs_prev_bb; vs_inst_idx := r.vs_inst_idx|>) = _`
    (mp_tac o AP_TERM ``stmtSimStoreCopy$store_copy_normalize s``) >>
  simp[immutable_transfers_normalize, stmtSimStoreCopyTheory.store_copy_normalize_def]
QED

Finalise compile_store_immutable_bytestring_mem_path
