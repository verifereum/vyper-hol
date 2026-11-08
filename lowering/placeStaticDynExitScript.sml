Theory placeStaticDynExit
Ancestors
  placeStaticStoreExit placeStaticCopyExit placeDynStoragePath placeDynExecutionLayout
  placeDynCompile placeCopyControlPath placeStoreCopyPath stmtSimStoreCopy
  fragExec fragGasSeq fragGasSeqAbort fragGasMode slotCopyExecution emitHelperProps
  exprLoweringProps exprLowering context compileEnv venomInst venomState
  venomExecSemantics list rich_list words arithmetic
Libs
  stepInstBaseLib

Theorem place_zero_word_copy_path:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_word_copy_loop src dst 0 LocMemory loc F sa = (u,sb) /\
  fn_has_code sa sb func /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s0 = SOME b /\ eval_operand dst s0 = SOME k /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s0 0 (OK t) /\
      store_copy_frame sa loc b k s0 0 t /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule_all place_store_copy_code >> strip_tac >>
  `?r. gas_marked_path F ctx func s0 0 (OK r) /\
       store_copy_frame sa loc b k s0 0 r /\
       eval_operand (Var cv) r = SOME 0w /\ ~r.vs_halted /\
       r.vs_current_bb = hdr /\ r.vs_inst_idx = 0` by suspend "init" >>
  `?t. gas_marked_path F ctx func r 0 (OK t) /\
       store_copy_frame sa loc b k s0 0 t /\ ~t.vs_halted /\
       t.vs_current_bb = exit /\ t.vs_inst_idx = 0` by suspend "header" >>
  qexists_tac `t` >> simp[] >>
  metis_tac[gas_marked_path_then, ADD_CLAUSES]
QED

Resume place_zero_word_copy_path[init]:
  qpat_assum `isPREFIX [mk_inst _ ASSIGN _ _; _] _`
    (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
  `isPREFIX [mk_inst id0 ASSIGN [Lit 0w] [cv]]
    (DROP s0.vs_inst_idx bb0.bb_instructions)` by simp[] >>
  `!x. not_fresh_at sa x ==> x <> cv` by (fs[] >> metis_tac[]) >>
  `lookup_block s0.vs_current_bb func.fn_blocks = SOME bb0` by simp[] >>
  drule_all place_store_copy_init_path >>
  disch_then (qspecl_then [`loc`, `k`, `ctx`, `b`] strip_assume_tac) >>
  `get_instruction bb0 t.vs_inst_idx =
   SOME (mk_inst (id0+1) JMP [Label hdr] [])` by
    (qpat_assum `isPREFIX [mk_inst _ ASSIGN _ _; _] _`
       (mp_then Any strip_assume_tac instruction_prefix_cursor) >>
     drule instruction_prefix_cursor >> simp[ADD1]) >>
  `gas_marked_path F ctx func t 0 (OK (jump_to hdr t))` by
    (irule place_copy_jump_path >> simp[] >> metis_tac[]) >>
  qexists_tac `jump_to hdr t` >>
  conj_tac >- metis_tac[gas_marked_path_then, ADD_CLAUSES] >>
  fs[place_store_frame_control, jump_to_def, eval_operand_def, lookup_var_def]
QED

Resume place_zero_word_copy_path[header]:
  qpat_assum `isPREFIX [mk_inst _ EQ _ _; _] _`
    (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
  `isPREFIX [mk_inst idh EQ [Var cv; Lit (n2w 0)] [tv]]
    (DROP r.vs_inst_idx bbh.bb_instructions)` by simp[] >>
  `cv <> tv /\ (!x. not_fresh_at sa x ==> x <> tv)` by
    (fs[ALL_DISTINCT] >> metis_tac[]) >>
  `lookup_block r.vs_current_bb func.fn_blocks = SOME bbh` by simp[] >>
  `eval_operand (Var cv) r = SOME (n2w 0)` by simp[] >>
  `0 <= (0:num) /\ 0 < dimword (:256)` by simp[] >>
  drule_all place_store_copy_test_path >>
  disch_then (qspec_then `ctx` mp_tac) >> simp[] >> strip_tac >>
  `get_instruction bbh t.vs_inst_idx =
   SOME (mk_inst (idh+1) JNZ [Var tv; Label exit; Label body_lbl] [])` by
    simp[get_instruction_def, EL_APPEND_EQN] >>
  `lookup_block t.vs_current_bb func.fn_blocks = SOME bbh` by metis_tac[] >>
  drule_all place_copy_branch_path >>
  disch_then (qspec_then `ctx` mp_tac) >> simp[] >> strip_tac >>
  qexists_tac `jump_to exit t` >>
  conj_tac >- metis_tac[gas_marked_path_then, ADD_CLAUSES] >>
  fs[place_store_frame_control, jump_to_def, eval_operand_def, lookup_var_def]
QED

Finalise place_zero_word_copy_path

Theorem place_static_dyn_single_exit[local]:
  s.vs_call_ctx.cc_static /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX
    [mk_inst id MUL [Var ctr; Lit 32w] [mv];
     mk_inst (id+1) ADD [Lit 32w;Var mv] [ov];
     mk_inst (id+2) ADD [src;Var ov] [sv];
     mk_inst (id+3) MLOAD [Var sv] [vv];
     mk_inst (id+4) ADD [Var ctr;Lit 1w] [kv];
     mk_inst (id+5) ADD [dst;Var kv] [dv];
     mk_inst (id+6) (if transient then TSTORE else SSTORE) [Var dv;Var vv] []]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  eval_operand src s = SOME b /\ eval_operand dst s = SOME k /\
  eval_operand (Var ctr) s = SOME (n2w j) /\ not_fresh_at sa ctr /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  ALL_DISTINCT [mv;ov;sv;vv;kv;dv] /\
  (!x. not_fresh_at sa x ==> ~MEM x [mv;ov;sv;vv;kv;dv]) ==>
  ?r. gas_marked_path F ctx func s 0 r /\ exit_result r /\
      stmt_exit RetQ ee (INR (Error (RuntimeError "write in static context"))) r
Proof
  strip_tac >>
  qabbrev_tac `a = n2w j * 32w : bytes32` >>
  qabbrev_tac `val = mload (w2n (b+32w+a)) s` >>
  qabbrev_tac `q = update_var dv (k+1w+n2w j)
    (update_var kv (n2w j+1w) (update_var vv val
      (update_var sv (b+32w+a) (update_var ov (32w+a) (update_var mv a s)))))` >>
  qabbrev_tac `code =
    [mk_inst id MUL [Var ctr; Lit 32w] [mv];
     mk_inst (id+1) ADD [Lit 32w;Var mv] [ov];
     mk_inst (id+2) ADD [src;Var ov] [sv];
     mk_inst (id+3) MLOAD [Var sv] [vv];
     mk_inst (id+4) ADD [Var ctr;Lit 1w] [kv];
     mk_inst (id+5) ADD [dst;Var kv] [dv]]` >>
  `run_inst_seq code s = OK q` by suspend "run" >>
  `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `isPREFIX (_::_::_::_::_::_::_::[]) _`
       (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
     simp[Abbr `code`]) >>
  drule tuple_run_inst_seq_gas_path >> disch_then drule >> disch_then drule >>
  simp[Abbr `code`, mk_inst_def, is_terminator_def] >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qabbrev_tac `endpoint = q with vs_inst_idx := s.vs_inst_idx+6` >>
  `gas_marked_path F ctx func s 0 (OK endpoint)` by
    simp[Abbr `endpoint`, gas_marked_path_def] >>
  `?r. gas_marked_path F ctx func endpoint 0 r /\ exit_result r /\
      stmt_exit RetQ ee (INR (Error (RuntimeError "write in static context"))) r`
    by suspend "fault" >>
  qexists_tac `r` >> simp[] >>
  metis_tac[gas_marked_path_then, ADD_CLAUSES]
QED

Resume place_static_dyn_single_exit[run]:
  fs[ALL_DISTINCT] >>
  `!x. MEM x [mv;ov;sv;vv;kv;dv] ==>
    src <> Var x /\ dst <> Var x /\ ctr <> x` by
    (simp[] >> rpt strip_tac >> metis_tac[]) >>
  simp[Abbr `code`, Abbr `q`, Abbr `a`, Abbr `val`,
    run_inst_seq_def, mk_inst_def,
    stepInstBaseLib.simp_opcode_clause ``MUL``,
    stepInstBaseLib.simp_opcode_clause ``ADD``,
    stepInstBaseLib.simp_opcode_clause ``MLOAD``,
    exec_pure2_def, exec_read1_def,
    slot_copy_operand_update, eval_operand_lit, eval_operand_update_var_local,
    WORD_ADD_ASSOC] >>
  fs[update_var_def, mload_def, eval_operand_def, lookup_var_def,
     finite_mapTheory.FLOOKUP_UPDATE, Excl "isPREFIX"] >>
  simp[AC WORD_ADD_ASSOC WORD_ADD_COMM]
QED

Resume place_static_dyn_single_exit[fault]:
  `endpoint.vs_call_ctx.cc_static /\ ~endpoint.vs_halted /\
   lookup_block endpoint.vs_current_bb func.fn_blocks = SOME bb /\
   endpoint.vs_inst_idx = s.vs_inst_idx+6` by
    simp[Abbr `endpoint`, Abbr `q`, update_var_def] >>
  `eval_operand (Var dv) endpoint = SOME (k+1w+n2w j) /\
   eval_operand (Var vv) endpoint = SOME val` by
    (fs[ALL_DISTINCT] >>
     simp[Abbr `endpoint`, Abbr `q`, update_var_def, eval_operand_def,
          lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  `isPREFIX [mk_inst (id+6) (if transient then TSTORE else SSTORE)
       [Var dv;Var vv] []]
     (DROP endpoint.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `isPREFIX (_::_::_::_::_::_::_::[]) _`
       (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
     `DROP (s.vs_inst_idx+6) bb.bb_instructions =
      DROP 6 (DROP s.vs_inst_idx bb.bb_instructions)` by
       simp[DROP_DROP_T, ADD_COMM] >>
     asm_rewrite_tac[] >> simp[]) >>
  irule place_static_store_prefix_exit >> metis_tac[]
QED

Finalise place_static_dyn_single_exit
