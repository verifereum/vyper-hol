Theory placeStaticCopyExit
Ancestors
  placeStaticStoreExit placeStoreCopyPath placeCopyControlPath fragGasSeqAbort
  stmtSimStoreCopy stmtSimDefs exprSimDefs fragExec fragGasMode
  slotCopyExecution fragGasSeq fragGasSeqMem emitHelperProps
  exprLoweringProps exprLowering context compileEnv venomInst venomState
  venomExecSemantics list rich_list words arithmetic
Libs
  stepInstBaseLib

Theorem place_static_copy_op_exit:

  (loc = LocStorage \/ loc = LocTransient) /\
  compile_word_copy_loop_op src dst cnt LocMemory loc F sa = (u,sb) /\
  fn_has_code sa sb func /\ 0 < n /\ n < dimword (:256) /\
  (!x. src = Var x \/ dst = Var x \/ cnt = Var x ==> not_fresh_at sa x) /\
  eval_operand src s0 = SOME b /\ eval_operand dst s0 = SOME k /\
  eval_operand cnt s0 = SOME (n2w n) /\
  s0.vs_call_ctx.cc_static /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r. gas_marked_path F ctx func s0 0 r /\ exit_result r /\
      stmt_exit RetQ ee (INR (Error (RuntimeError "write in static context"))) r
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule_all place_store_runtime_copy_code >> strip_tac >>
  `?r. gas_marked_path F ctx func s0 0 (OK r) /\
       store_copy_frame sa loc b k s0 0 r /\
       eval_operand (Var cv) r = SOME 0w /\ ~r.vs_halted /\
       r.vs_current_bb = hdr /\ r.vs_inst_idx = 0` by suspend "init" >>
  `?q. gas_marked_path F ctx func r 0 (OK q) /\
       store_copy_frame sa loc b k s0 0 q /\
       eval_operand (Var cv) q = SOME 0w /\ ~q.vs_halted /\
       q.vs_current_bb = body_lbl /\ q.vs_inst_idx = 0` by suspend "header" >>
  `?z. gas_marked_path F ctx func q 0 z /\ exit_result z /\
       stmt_exit RetQ ee (INR (Error (RuntimeError "write in static context"))) z`
    by suspend "body" >>
  qexists_tac `z` >> simp[] >>
  metis_tac[gas_marked_path_then, ADD_CLAUSES]
QED

Resume place_static_copy_op_exit[init]:
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
  conj_tac >- (drule_all gas_marked_path_then >> simp[]) >>
  fs[place_store_frame_control, jump_to_def, eval_operand_def, lookup_var_def]
QED

Resume place_static_copy_op_exit[header]:
  qpat_assum `isPREFIX [mk_inst _ EQ _ _; _] _`
    (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
  `isPREFIX [mk_inst idh EQ [Var cv;cnt] [tv]]
    (DROP r.vs_inst_idx bbh.bb_instructions)` by simp[] >>
  `cv <> tv /\ (!x. not_fresh_at sa x ==> x <> tv)` by
    (fs[ALL_DISTINCT] >> metis_tac[]) >>
  `lookup_block r.vs_current_bb func.fn_blocks = SOME bbh` by simp[] >>
  `eval_operand (Var cv) r = SOME (n2w 0)` by simp[] >>
  `r.vs_labels = s0.vs_labels` by metis_tac[place_store_frame_fields] >>
  `eval_operand cnt r = SOME (n2w n)` by
    (Cases_on `cnt` >> fs[store_copy_frame_def, eval_operand_def] >> metis_tac[]) >>
  `0 <= n` by simp[] >>
  drule_all place_store_runtime_copy_test_path >>
  disch_then (qspec_then `ctx` mp_tac) >> simp[] >> strip_tac >>
  `get_instruction bbh t.vs_inst_idx =
   SOME (mk_inst (idh+1) JNZ [Var tv;Label exit;Label body_lbl] [])` by
    simp[get_instruction_def, EL_APPEND_EQN] >>
  `lookup_block t.vs_current_bb func.fn_blocks = SOME bbh` by metis_tac[] >>
  drule_all place_copy_branch_path >>
  disch_then (qspec_then `ctx` mp_tac) >> simp[] >> strip_tac >>
  qexists_tac `jump_to body_lbl t` >>
  conj_tac >- metis_tac[gas_marked_path_then, ADD_CLAUSES] >>
  fs[place_store_frame_control, jump_to_def, eval_operand_def, lookup_var_def]
QED

Resume place_static_copy_op_exit[body]:
  drule_at (Pat `store_copy_frame _ _ _ _ _ _ q`) place_store_frame_fields >>
  strip_tac >>
  `eval_operand src q = SOME b /\ eval_operand dst q = SOME k` by
    (Cases_on `src` >> Cases_on `dst` >> fs[eval_operand_def] >>
     qpat_x_assum `store_copy_frame _ _ _ _ _ _ q`
       (strip_assume_tac o REWRITE_RULE [store_copy_frame_def]) >> metis_tac[]) >>
  `!x. MEM x [cv;mv;sv;vv;dv;nv] ==> src <> Var x /\ dst <> Var x` by
    (fs[ALL_DISTINCT] >> rpt strip_tac >> metis_tac[]) >>
  qabbrev_tac `code =
    [mk_inst idb MUL [Var cv;Lit 32w] [mv];
     mk_inst (idb+1) ADD [src;Var mv] [sv];
     mk_inst (idb+2) MLOAD [Var sv] [vv];
     mk_inst (idb+3) ADD [dst;Var cv] [dv]]` >>
  qabbrev_tac `t = update_var dv k (update_var vv (mload (w2n b) q)
    (update_var sv b (update_var mv 0w q)))` >>
  `run_inst_seq code q = OK t` by
    (fs[ALL_DISTINCT] >>
     simp[Abbr `code`, Abbr `t`, run_inst_seq_def, mk_inst_def,
       stepInstBaseLib.simp_opcode_clause ``MUL``,
       stepInstBaseLib.simp_opcode_clause ``ADD``,
       stepInstBaseLib.simp_opcode_clause ``MLOAD``,
       exec_pure2_def, exec_read1_def, slot_copy_operand_update,
       eval_operand_lit, eval_operand_update_var_local] >>
     simp[mload_def, update_var_def, WORD_MULT_CLAUSES, WORD_ADD_0]) >>
  `isPREFIX code (DROP q.vs_inst_idx bbb.bb_instructions)` by
    (qpat_assum `isPREFIX (_::_::_::_::_::_::_::_::[]) _`
       (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >> simp[Abbr `code`]) >>
  `lookup_block q.vs_current_bb func.fn_blocks = SOME bbb` by simp[] >>
  drule tuple_run_inst_seq_gas_path >> disch_then drule >> disch_then drule >>
  simp[Abbr `code`, mk_inst_def, is_terminator_def] >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path ctx func q 0 (OK endpoint)` >>
  `gas_marked_path F ctx func q 0 (OK endpoint)` by simp[gas_marked_path_def] >>
  `?z. gas_marked_path F ctx func endpoint 0 z /\ exit_result z /\
       stmt_exit RetQ ee (INR (Error (RuntimeError "write in static context"))) z`
    by suspend "fault" >>
  qexists_tac `z` >> simp[] >> metis_tac[gas_marked_path_then, ADD_CLAUSES]
QED

Resume place_static_copy_op_exit[fault]:
  `endpoint.vs_call_ctx.cc_static /\ ~endpoint.vs_halted /\
   lookup_block endpoint.vs_current_bb func.fn_blocks = SOME bbb /\
   endpoint.vs_inst_idx = 4` by simp[Abbr `endpoint`, Abbr `t`, update_var_def] >>
  `eval_operand (Var dv) endpoint = SOME k /\
   eval_operand (Var vv) endpoint = SOME (mload (w2n b) q)` by
    (fs[ALL_DISTINCT] >>
     simp[Abbr `endpoint`, Abbr `t`, update_var_def, eval_operand_def,
          lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  `isPREFIX [mk_inst (idb+4)
      (if loc = LocStorage then SSTORE else TSTORE) [Var dv;Var vv] []]
      (DROP endpoint.vs_inst_idx bbb.bb_instructions)` by
    (qpat_assum `isPREFIX (_::_::_::_::_::_::_::_::[]) _`
       (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >> simp[]) >>
  irule place_static_store_prefix_exit >> metis_tac[]
QED

Finalise place_static_copy_op_exit


Theorem place_static_copy_op_exit_mem:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_word_copy_loop_op src dst cnt LocMemory loc F sa = (u,sb) /\
  fn_has_code sa sb func /\ 0 < n /\ n < dimword (:256) /\
  (!x. src = Var x \/ dst = Var x \/ cnt = Var x ==> not_fresh_at sa x) /\
  eval_operand src s0 = SOME b /\ eval_operand dst s0 = SOME k /\
  eval_operand cnt s0 = SOME (n2w n) /\
  w2n b + 32 < dimword (:256) /\ w2n b + 32 <= s0.vs_alloca_next /\
  s0.vs_call_ctx.cc_static /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?z. gas_marked_path T ctx func s0 0 z /\ exit_result z /\
      stmt_exit RetQ ee (INR (Error (RuntimeError "write in static context"))) z
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule_all place_store_runtime_copy_code >> strip_tac >>
  `!x. MEM x [cv;tv;mv;sv;vv;dv;nv] ==>
       src <> Var x /\ dst <> Var x /\ cnt <> Var x` by
    (rpt strip_tac >> metis_tac[]) >>
  qabbrev_tac `a = update_var cv 0w s0 with vs_inst_idx := s0.vs_inst_idx + 1` >>
  qabbrev_tac `r = jump_to hdr a` >>
  qabbrev_tac `t = update_var tv 0w r with vs_inst_idx := 1` >>
  qabbrev_tac `q = jump_to body_lbl t` >>
  `gas_marked_path T ctx func s0 0 (OK a)` by suspend "init" >>
  `gas_marked_path T ctx func a 0 (OK r)` by suspend "jump" >>
  `gas_marked_path T ctx func r 0 (OK t)` by suspend "test" >>
  `gas_marked_path T ctx func t 0 (OK q)` by suspend "branch" >>
  `?z. gas_marked_path T ctx func q 0 z /\ exit_result z /\
       stmt_exit RetQ ee (INR (Error (RuntimeError "write in static context"))) z`
    by suspend "body" >>
  qexists_tac `z` >> simp[] >>
  metis_tac[gas_marked_path_then, ADD_CLAUSES]
QED

Resume place_static_copy_op_exit_mem[init]:
  `isPREFIX [mk_inst id0 ASSIGN [Lit 0w] [cv]]
      (DROP s0.vs_inst_idx bb0.bb_instructions)` by
    (qpat_assum `isPREFIX [mk_inst _ ASSIGN _ _; _] _`
       (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >> simp[]) >>
  `run_inst_seq [mk_inst id0 ASSIGN [Lit 0w] [cv]] s0 =
      OK (update_var cv 0w s0)` by
    simp[run_inst_seq_def, stepInstBaseLib.simp_opcode_clause ``ASSIGN``,
         mk_inst_def, eval_operand_lit] >>
  `run_inst_seq_mem_ok [mk_inst id0 ASSIGN [Lit 0w] [cv]] s0` by
    simp[fragExecMemTheory.run_inst_seq_mem_ok_def,
         stepInstBaseLib.simp_opcode_clause ``ASSIGN``,
         stepInstBaseLib.simp_opcode_clause ``EQ``, exec_pure2_def,
         eval_operand_lit, mk_inst_def,
         unitTransformDefsTheory.inst_mem_below_frontier_def,
         contextCodegenRelTheory.source_memory_read_ranges_def,
         codegenRelTheory.source_memory_write_ranges_def,
         memSafeRunTheory.inst_dload_in_section_def] >>
  `lookup_block s0.vs_current_bb func.fn_blocks = SOME bb0` by simp[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      [mk_inst id0 ASSIGN [Lit 0w] [cv]]` by simp[mk_inst_def, is_terminator_def] >>
  simp[gas_marked_path_def, Abbr `a`] >>
  drule_all run_inst_seq_gas_path_mem >>
  disch_then (qspec_then `ctx` mp_tac) >>
  simp[mk_inst_def, is_terminator_def]
QED

Resume place_static_copy_op_exit_mem[jump]:
  `get_instruction bb0 a.vs_inst_idx =
      SOME (mk_inst (id0+1) JMP [Label hdr] [])` by
    (qpat_assum `isPREFIX [mk_inst _ ASSIGN _ _; _] _`
       (mp_then Any strip_assume_tac fragGasSeqAbortTheory.instruction_prefix_cursor) >>
     drule fragGasSeqAbortTheory.instruction_prefix_cursor >>
     simp[Abbr `a`, ADD1]) >>
  `~a.vs_halted /\ lookup_block a.vs_current_bb func.fn_blocks = SOME bb0` by
    simp[Abbr `a`, update_var_def] >>
  `gas_path_mem_edge ctx func a 0 (OK r)` by
    (simp[fragGasPathMemTheory.gas_path_mem_edge_def] >>
     qexists_tac `0` >>
     simp[Abbr `r`, step_inst_non_invoke, mk_inst_def,
          stepInstBaseLib.simp_opcode_clause ``JMP``, gasCountTheory.gas_count_step_def,
          memSafeRunTheory.mem_safe_step_non_invoke, is_terminator_def,
          unitTransformDefsTheory.inst_mem_below_frontier_def,
          contextCodegenRelTheory.source_memory_read_ranges_def,
          codegenRelTheory.source_memory_write_ranges_def,
          memSafeRunTheory.inst_dload_in_section_def, update_var_def] >>
     metis_tac[]) >>
  `~r.vs_halted` by simp[Abbr `r`, Abbr `a`, jump_to_def, update_var_def] >>
  simp[gas_marked_path_def] >>
  metis_tac[fragGasPathMemTheory.gas_path_mem_rules, ADD_CLAUSES]
QED

Resume place_static_copy_op_exit_mem[test]:
  `eval_operand cnt r = SOME (n2w n) /\ eval_operand (Var cv) r = SOME 0w` by
    (simp[Abbr `r`, Abbr `a`, jump_to_def, slot_copy_operand_update,
          eval_operand_def, lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
     Cases_on `cnt` >> gvs[eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
                           Excl "isPREFIX"] >> metis_tac[]) >>
  `n2w n <> (0w:bytes32)` by simp[wordsTheory.n2w_11, LESS_MOD] >>
  `isPREFIX [mk_inst idh EQ [Var cv;cnt] [tv]]
      (DROP r.vs_inst_idx bbh.bb_instructions)` by
    (qpat_assum `isPREFIX [mk_inst _ EQ _ _; _] _`
       (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
     simp[Abbr `r`, jump_to_def]) >>
  `run_inst_seq [mk_inst idh EQ [Var cv;cnt] [tv]] r =
      OK (update_var tv 0w r)` by
    simp[run_inst_seq_def, stepInstBaseLib.simp_opcode_clause ``EQ``,
         mk_inst_def, exec_pure2_def, bool_to_word_def] >>
  `run_inst_seq_mem_ok [mk_inst idh EQ [Var cv;cnt] [tv]] r` by
    simp[fragExecMemTheory.run_inst_seq_mem_ok_def,
         stepInstBaseLib.simp_opcode_clause ``ASSIGN``,
         stepInstBaseLib.simp_opcode_clause ``EQ``, exec_pure2_def,
         eval_operand_lit, mk_inst_def,
         unitTransformDefsTheory.inst_mem_below_frontier_def,
         contextCodegenRelTheory.source_memory_read_ranges_def,
         codegenRelTheory.source_memory_write_ranges_def,
         memSafeRunTheory.inst_dload_in_section_def] >>
  `~r.vs_halted /\ lookup_block r.vs_current_bb func.fn_blocks = SOME bbh /\
   r.vs_inst_idx = 0` by
    simp[Abbr `r`, Abbr `a`, jump_to_def, update_var_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      [mk_inst idh EQ [Var cv;cnt] [tv]]` by simp[mk_inst_def, is_terminator_def] >>
  simp[gas_marked_path_def, Abbr `t`] >>
  drule_all run_inst_seq_gas_path_mem >>
  disch_then (qspec_then `ctx` mp_tac) >>
  simp[mk_inst_def, is_terminator_def]
QED

Resume place_static_copy_op_exit_mem[branch]:
  `get_instruction bbh t.vs_inst_idx =
      SOME (mk_inst (idh+1) JNZ [Var tv;Label exit;Label body_lbl] [])` by
    (qpat_assum `isPREFIX [mk_inst _ EQ _ _; _] _`
       (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
     simp[Abbr `t`, get_instruction_def, EL_APPEND_EQN]) >>
  `eval_operand (Var tv) t = SOME 0w` by
    simp[Abbr `t`, eval_operand_def, lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  `~t.vs_halted /\ lookup_block t.vs_current_bb func.fn_blocks = SOME bbh` by
    simp[Abbr `t`, Abbr `r`, Abbr `a`, jump_to_def, update_var_def] >>
  `step_inst 0 ctx (mk_inst (idh+1) JNZ [Var tv;Label exit;Label body_lbl] []) t =
     OK q` by
    simp[step_inst_non_invoke, mk_inst_def,
         stepInstBaseLib.simp_opcode_clause ``JNZ``, Abbr `q`] >>
  `gas_path_mem_edge ctx func t 0 (OK q)` by
    (simp[fragGasPathMemTheory.gas_path_mem_edge_def] >>
     qexists_tac `0` >>
     simp[mk_inst_def, gasCountTheory.gas_count_step_def,
          memSafeRunTheory.mem_safe_step_non_invoke, is_terminator_def,
          unitTransformDefsTheory.inst_mem_below_frontier_def,
          contextCodegenRelTheory.source_memory_read_ranges_def,
          codegenRelTheory.source_memory_write_ranges_def,
          memSafeRunTheory.inst_dload_in_section_def] >>
     simp[Abbr `q`] >>
     metis_tac[]) >>
  `~q.vs_halted` by
    simp[Abbr `q`, Abbr `t`, Abbr `r`, Abbr `a`, jump_to_def, update_var_def] >>
  simp[gas_marked_path_def] >>
  metis_tac[fragGasPathMemTheory.gas_path_mem_rules, ADD_CLAUSES]
QED

Resume place_static_copy_op_exit_mem[body]:
  `!x. MEM x [cv;tv;mv;sv;vv;dv;nv] ==> src <> Var x /\ dst <> Var x` by
    metis_tac[] >>
  `eval_operand src q = SOME b /\ eval_operand dst q = SOME k /\
   eval_operand (Var cv) q = SOME 0w` by
    (fs[ALL_DISTINCT] >>
     simp[Abbr `q`, Abbr `t`, Abbr `r`, Abbr `a`, jump_to_def,
          slot_copy_operand_update, eval_operand_update_var_local,
          eval_operand_def, lookup_var_def, update_var_def,
          finite_mapTheory.FLOOKUP_UPDATE] >>
     Cases_on `src` >> Cases_on `dst` >>
     gvs[eval_operand_def, lookup_var_def, Excl "isPREFIX"] >> metis_tac[]) >>
  qabbrev_tac `code =
    [mk_inst idb MUL [Var cv;Lit 32w] [mv];
     mk_inst (idb+1) ADD [src;Var mv] [sv];
     mk_inst (idb+2) MLOAD [Var sv] [vv];
     mk_inst (idb+3) ADD [dst;Var cv] [dv]]` >>
  qabbrev_tac `u1 = update_var dv k (update_var vv (mload (w2n b) q)
    (update_var sv b (update_var mv 0w q)))` >>
  `run_inst_seq code q = OK u1` by
    (fs[ALL_DISTINCT] >>
     simp[Abbr `code`, Abbr `u1`, run_inst_seq_def, mk_inst_def,
       stepInstBaseLib.simp_opcode_clause ``MUL``,
       stepInstBaseLib.simp_opcode_clause ``ADD``,
       stepInstBaseLib.simp_opcode_clause ``MLOAD``,
       exec_pure2_def, exec_read1_def, slot_copy_operand_update,
       eval_operand_lit, eval_operand_update_var_local] >>
     simp[mload_def, update_var_def, wordsTheory.WORD_MULT_CLAUSES,
          wordsTheory.WORD_ADD_0]) >>
  `run_inst_seq_mem_ok code q` by suspend "checks" >>
  `isPREFIX code (DROP q.vs_inst_idx bbb.bb_instructions)` by
    (qpat_assum `isPREFIX (_::_::_::_::_::_::_::_::[]) _`
       (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
     simp[Abbr `code`, Abbr `q`, jump_to_def]) >>
  `~q.vs_halted /\ lookup_block q.vs_current_bb func.fn_blocks = SOME bbb /\
   q.vs_inst_idx = 0` by
    simp[Abbr `q`, Abbr `t`, Abbr `r`, Abbr `a`, jump_to_def, update_var_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code` by
    simp[Abbr `code`, mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_mem >>
  disch_then (qspec_then `ctx` mp_tac) >>
  simp[Abbr `code`, mk_inst_def] >> strip_tac >>
  qabbrev_tac `endpoint = u1 with vs_inst_idx := 4` >>
  `?z. gas_marked_path T ctx func endpoint 0 z /\ exit_result z /\
       stmt_exit RetQ ee (INR (Error (RuntimeError "write in static context"))) z`
    by suspend "fault" >>
  qexists_tac `z` >> simp[] >>
  fs[gas_marked_path_def] >>
  drule_all fragGasPathMemTheory.gas_path_mem_then >> simp[]
QED

Resume place_static_copy_op_exit_mem[checks]:
  fs[ALL_DISTINCT] >>
  simp[Abbr `code`, fragExecMemTheory.run_inst_seq_mem_ok_def, mk_inst_def,
       stepInstBaseLib.simp_opcode_clause ``MUL``,
       stepInstBaseLib.simp_opcode_clause ``ADD``,
       stepInstBaseLib.simp_opcode_clause ``MLOAD``,
       exec_pure2_def, exec_read1_def, slot_copy_operand_update,
       eval_operand_lit, eval_operand_update_var_local,
       wordsTheory.WORD_MULT_CLAUSES, wordsTheory.WORD_ADD_0,
       unitTransformDefsTheory.inst_mem_below_frontier_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def,
       memSafeRunTheory.inst_dload_in_section_def] >>
  simp[update_var_def, Abbr `q`, Abbr `t`, Abbr `r`, Abbr `a`, jump_to_def]
QED

Resume place_static_copy_op_exit_mem[fault]:
  `endpoint.vs_call_ctx.cc_static /\ ~endpoint.vs_halted /\
   lookup_block endpoint.vs_current_bb func.fn_blocks = SOME bbb /\
   endpoint.vs_inst_idx = 4` by
    simp[Abbr `endpoint`, Abbr `u1`, Abbr `q`, Abbr `t`, Abbr `r`, Abbr `a`,
         update_var_def, jump_to_def] >>
  `eval_operand (Var dv) endpoint = SOME k /\
   eval_operand (Var vv) endpoint = SOME (mload (w2n b) q)` by
    (fs[ALL_DISTINCT] >>
     simp[Abbr `endpoint`, Abbr `u1`, update_var_def, eval_operand_def,
          lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  `isPREFIX [mk_inst (idb+4)
      (if loc = LocStorage then SSTORE else TSTORE) [Var dv;Var vv] []]
      (DROP endpoint.vs_inst_idx bbb.bb_instructions)` by
    (qpat_assum `isPREFIX (_::_::_::_::_::_::_::_::[]) _`
       (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >> simp[]) >>
  irule place_static_store_prefix_exit_marked >> metis_tac[]
QED

Finalise place_static_copy_op_exit_mem

Theorem place_empty_copy_op_path:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_word_copy_loop_op src dst cnt LocMemory loc F sa = (u,sb) /\
  fn_has_code sa sb func /\
  (!x. cnt = Var x ==> not_fresh_at sa x) /\
  eval_operand cnt s0 = SOME 0w /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s0 0 (OK t) /\
      store_copy_frame sa loc b k s0 0 t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule_all place_store_runtime_copy_code >> strip_tac >>
  `?r. gas_marked_path F ctx func s0 0 (OK r) /\
       store_copy_frame sa loc b k s0 0 r /\
       eval_operand (Var cv) r = SOME 0w /\ ~r.vs_halted /\
       r.vs_current_bb = hdr /\ r.vs_inst_idx = 0` by suspend "init" >>
  `r.vs_labels = s0.vs_labels` by metis_tac[place_store_frame_fields] >>
  `eval_operand cnt r = SOME 0w` by
    (Cases_on `cnt` >> fs[store_copy_frame_def, eval_operand_def] >> metis_tac[]) >>
  qpat_assum `isPREFIX [mk_inst _ EQ _ _; _] _`
    (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
  `isPREFIX [mk_inst idh EQ [Var cv;cnt] [tv]]
    (DROP r.vs_inst_idx bbh.bb_instructions)` by simp[] >>
  `cv <> tv /\ (!x. not_fresh_at sa x ==> x <> tv)` by
    (fs[ALL_DISTINCT] >> metis_tac[]) >>
  `lookup_block r.vs_current_bb func.fn_blocks = SOME bbh` by simp[] >>
  `0 <= (0:num) /\ (0:num) < dimword (:256)` by simp[] >>
  `eval_operand cnt r = SOME (n2w 0) /\
   eval_operand (Var cv) r = SOME (n2w 0)` by simp[] >>
  drule_all place_store_runtime_copy_test_path >>
  disch_then (qspec_then `ctx` mp_tac) >> simp[] >> strip_tac >>
  `get_instruction bbh t.vs_inst_idx =
   SOME (mk_inst (idh+1) JNZ [Var tv;Label exit;Label body_lbl] [])` by
    simp[get_instruction_def, EL_APPEND_EQN] >>
  `lookup_block t.vs_current_bb func.fn_blocks = SOME bbh` by metis_tac[] >>
  drule_all place_copy_branch_path >>
  disch_then (qspec_then `ctx` mp_tac) >> simp[] >> strip_tac >>
  qexists_tac `jump_to exit t` >>
  conj_tac >- metis_tac[gas_marked_path_then, ADD_CLAUSES] >>
  fs[place_store_frame_control, jump_to_def]
QED

Resume place_empty_copy_op_path[init]:
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
  conj_tac >- (drule_all gas_marked_path_then >> simp[]) >>
  fs[place_store_frame_control, jump_to_def, eval_operand_def, lookup_var_def]
QED

Finalise place_empty_copy_op_path

Theorem place_static_copy_exit:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_word_copy_loop src dst n LocMemory loc F sa = (u,sb) /\
  fn_has_code sa sb func /\ 0 < n /\ n < dimword (:256) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s0 = SOME b /\ eval_operand dst s0 = SOME k /\
  s0.vs_call_ctx.cc_static /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r. gas_marked_path F ctx func s0 0 r /\ exit_result r /\
      stmt_exit RetQ ee (INR (Error (RuntimeError "write in static context"))) r
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  qpat_x_assum `compile_word_copy_loop _ _ _ _ _ _ _ = _`
    (assume_tac o REWRITE_RULE [compile_word_copy_loop_def]) >>
  `eval_operand (Lit (n2w n)) s0 = SOME (n2w n)` by simp[eval_operand_def] >>
  `!x. src = Var x \/ dst = Var x \/ Lit (n2w n) = Var x ==>
       not_fresh_at sa x` by (simp[] >> metis_tac[]) >>
  drule_all place_static_copy_op_exit >>
  disch_then (ACCEPT_TAC o SPEC_ALL)
QED
