Theory placeStaticCopyExit
Ancestors
  placeStaticStoreExit placeStoreCopyPath placeCopyControlPath fragGasSeqAbort
  stmtSimStoreCopy stmtSimDefs exprSimDefs fragExec fragGasMode
  slotCopyExecution fragGasSeq emitHelperProps
  exprLoweringProps exprLowering context compileEnv venomInst venomState
  venomExecSemantics list rich_list words arithmetic
Libs
  stepInstBaseLib

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
  drule_all place_store_copy_code >> strip_tac >>
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

Resume place_static_copy_exit[init]:
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

Resume place_static_copy_exit[header]:
  qpat_assum `isPREFIX [mk_inst _ EQ _ _; _] _`
    (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
  `isPREFIX [mk_inst idh EQ [Var cv; Lit (n2w n)] [tv]]
    (DROP r.vs_inst_idx bbh.bb_instructions)` by simp[] >>
  `cv <> tv /\ (!x. not_fresh_at sa x ==> x <> tv)` by
    (fs[ALL_DISTINCT] >> metis_tac[]) >>
  `lookup_block r.vs_current_bb func.fn_blocks = SOME bbh` by simp[] >>
  `eval_operand (Var cv) r = SOME (n2w 0)` by simp[] >>
  `0 <= n` by simp[] >>
  drule_all place_store_copy_test_path >>
  disch_then (qspec_then `ctx` mp_tac) >> simp[] >> strip_tac >>
  `get_instruction bbh t.vs_inst_idx =
   SOME (mk_inst (idh+1) JNZ [Var tv; Label exit; Label body_lbl] [])` by
    simp[get_instruction_def, EL_APPEND_EQN] >>
  `lookup_block t.vs_current_bb func.fn_blocks = SOME bbh` by metis_tac[] >>
  drule_all place_copy_branch_path >>
  disch_then (qspec_then `ctx` mp_tac) >> simp[] >> strip_tac >>
  qexists_tac `jump_to body_lbl t` >>
  conj_tac >- metis_tac[gas_marked_path_then, ADD_CLAUSES] >>
  fs[place_store_frame_control, jump_to_def, eval_operand_def, lookup_var_def]
QED

Resume place_static_copy_exit[body]:
  drule_at (Pat `store_copy_frame _ _ _ _ _ _ q`) place_store_frame_fields >>
  strip_tac >>
  `eval_operand src q = SOME b /\ eval_operand dst q = SOME k` by
    (Cases_on `src` >> Cases_on `dst` >>
     gvs[eval_operand_def, store_copy_frame_def] >> metis_tac[]) >>
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
       (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
     simp[Abbr `code`]) >>
  `lookup_block q.vs_current_bb func.fn_blocks = SOME bbb` by simp[] >>
  drule tuple_run_inst_seq_gas_path >> disch_then drule >> disch_then drule >>
  simp[Abbr `code`, mk_inst_def, is_terminator_def] >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path ctx func q 0 (OK endpoint)` >>
  `gas_marked_path F ctx func q 0 (OK endpoint)` by
    simp[gas_marked_path_def] >>
  `?z. gas_marked_path F ctx func endpoint 0 z /\ exit_result z /\
       stmt_exit RetQ ee (INR (Error (RuntimeError "write in static context"))) z`
    by suspend "fault" >>
  qexists_tac `z` >> simp[] >>
  metis_tac[gas_marked_path_then, ADD_CLAUSES]
QED

Resume place_static_copy_exit[fault]:
  `endpoint.vs_call_ctx.cc_static /\ ~endpoint.vs_halted /\
   lookup_block endpoint.vs_current_bb func.fn_blocks = SOME bbb /\
   endpoint.vs_inst_idx = 4` by
    simp[Abbr `endpoint`, Abbr `t`, update_var_def] >>
  `eval_operand (Var dv) endpoint = SOME k /\
   eval_operand (Var vv) endpoint = SOME (mload (w2n b) q)` by
    (fs[ALL_DISTINCT] >>
     simp[Abbr `endpoint`, Abbr `t`, update_var_def, eval_operand_def,
          lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  `isPREFIX [mk_inst (idb+4)
      (if loc = LocStorage then SSTORE else TSTORE) [Var dv;Var vv] []]
      (DROP endpoint.vs_inst_idx bbb.bb_instructions)` by
    (qpat_assum `isPREFIX (_::_::_::_::_::_::_::_::[]) _`
       (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
     simp[]) >>
  irule place_static_store_prefix_exit >>
  metis_tac[]
QED

Finalise place_static_copy_exit
