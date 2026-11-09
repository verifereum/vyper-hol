Theory placeStoreCopyPath
Ancestors
  placeDynCompile stmtSimStoreCopy placeCopyControlPath placeTypedCopyPath
  fragExec loweringSlice emitHelper emitHelperProps exprLoweringProps
  context compileEnv loweringStateRelDefs venomInst venomState venomExecSemantics words
  fragGasSeq fragGasMode list rich_list arithmetic finite_map slotCopyExecution fragGasSeqAbort
Libs
  stepInstBaseLib

Theorem place_store_copy_code:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_word_copy_loop src dst n LocMemory loc F sa = (u,sb) /\
  fn_has_code sa sb func ==>
  ?hdr body_lbl exit cv tv mv sv vv dv nv id0 idh idb bb0 bbh bbb.
    lookup_block sa.cs_current_bb func.fn_blocks = SOME bb0 /\
    isPREFIX
      [mk_inst id0 ASSIGN [Lit 0w] [cv];
       mk_inst (id0+1) JMP [Label hdr] []]
      (DROP (LENGTH sa.cs_current_insts) bb0.bb_instructions) /\
    lookup_block hdr func.fn_blocks = SOME bbh /\
    isPREFIX
      [mk_inst idh EQ [Var cv; Lit (n2w n)] [tv];
       mk_inst (idh+1) JNZ [Var tv; Label exit; Label body_lbl] []]
      bbh.bb_instructions /\
    lookup_block body_lbl func.fn_blocks = SOME bbb /\
    isPREFIX
      [mk_inst idb MUL [Var cv; Lit 32w] [mv];
       mk_inst (idb+1) ADD [src; Var mv] [sv];
       mk_inst (idb+2) MLOAD [Var sv] [vv];
       mk_inst (idb+3) ADD [dst; Var cv] [dv];
       mk_inst (idb+4) (if loc = LocStorage then SSTORE else TSTORE)
         [Var dv; Var vv] [];
       mk_inst (idb+5) ADD [Var cv; Lit 1w] [nv];
       mk_inst (idb+6) ASSIGN [Var nv] [cv];
       mk_inst (idb+7) JMP [Label hdr] []]
      bbb.bb_instructions /\
    sb.cs_current_bb = exit /\ LENGTH sb.cs_current_insts = 0 /\
    ALL_DISTINCT [cv;tv;mv;sv;vv;dv;nv] /\
    (!x. not_fresh_at sa x ==> ~MEM x [cv;tv;mv;sv;vv;dv;nv])
Proof
  strip_tac >> Cases_on `loc = LocStorage` >>
  gvs[compile_word_copy_loop_def, word_scale_def,
      compile_ptr_load_def, compile_ptr_store_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_label_def, fresh_var_def, emit_inst_def, emit_op_def,
      emit_void_def, fresh_id_def, emit_def, new_block_def,
      not_fresh_at_def, fn_has_code_def, emitted_blocks_def,
      Excl "isPREFIX"] >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM, ADD1, Excl "isPREFIX"] >>
  qmatch_asmsub_abbrev_tac `mk_inst _ MUL [Var cv; Lit 32w] [mv]` >>
  qmatch_asmsub_abbrev_tac `mk_inst _ EQ _ [tv]` >>
  qmatch_asmsub_abbrev_tac `mk_inst _ ADD [src; Var mv] [sv]` >>
  qmatch_asmsub_abbrev_tac `mk_inst _ MLOAD _ [vv]` >>
  qmatch_asmsub_abbrev_tac `mk_inst _ ADD [dst; Var cv] [dv]` >>
  qmatch_asmsub_abbrev_tac `mk_inst _ ADD [Var cv; Lit 1w] [nv]` >>
  qexistsl_tac [`fresh_label_output "wcopy_cond" sa.cs_next_label`,
    `fresh_label_output "wcopy_body" (sa.cs_next_label + 1)`,
    `cv`, `tv`, `mv`, `sv`, `vv`, `dv`, `nv`,
    `sa.cs_next_id`, `sa.cs_next_id + 2`, `sa.cs_next_id + 4`] >>
  rpt (goal_assum (drule_at Any)) >>
  once_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, Excl "isPREFIX"] >>
  simp[Abbr `cv`, Abbr `tv`, Abbr `mv`, Abbr `sv`, Abbr `vv`,
       Abbr `dv`, Abbr `nv`, fresh_var_distinct] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem place_store_prefix_eqs:
  store_copy_prefix loc b k s0 0 = s0 /\
  (!i. store_copy_prefix loc b k s0 (SUC i) =
    (if loc = LocStorage then sstore else tstore)
      (k + n2w i) (mload (w2n (b + n2w i * 32w)) s0)
      (store_copy_prefix loc b k s0 i))
Proof
  conj_tac >- simp[store_copy_prefix_def, COUNT_LIST_def] >>
  simp[store_copy_prefix_def, COUNT_LIST_SNOC, FOLDL_SNOC]
QED

Theorem place_store_frame_control:
  (store_copy_frame sa loc b k s0 i (jump_to lbl s) <=>
   store_copy_frame sa loc b k s0 i s) /\
  (store_copy_frame sa loc b k s0 i (s with vs_inst_idx := idx) <=>
   store_copy_frame sa loc b k s0 i s)
Proof
  simp[store_copy_frame_def, store_copy_normalize_def, jump_to_def, lookup_var_def]
QED

Theorem place_store_prefix_fields:
  (store_copy_prefix loc b k s0 i).vs_memory = s0.vs_memory /\
  (store_copy_prefix loc b k s0 i).vs_labels = s0.vs_labels /\
  (store_copy_prefix loc b k s0 i).vs_call_ctx = s0.vs_call_ctx /\
  (store_copy_prefix loc b k s0 i).vs_allocas = s0.vs_allocas /\
  (store_copy_prefix loc b k s0 i).vs_alloca_next = s0.vs_alloca_next /\
  (store_copy_prefix loc b k s0 i).vs_halted = s0.vs_halted
Proof
  Induct_on `i` >> simp[place_store_prefix_eqs] >>
  Cases_on `loc = LocStorage` >> gvs[sstore_def, tstore_def]
QED

Theorem place_store_frame_fields:
  store_copy_frame sa loc b k s0 i s ==>
  s.vs_memory = s0.vs_memory /\ s.vs_labels = s0.vs_labels /\
  s.vs_call_ctx = s0.vs_call_ctx /\ s.vs_allocas = s0.vs_allocas /\
  s.vs_alloca_next = s0.vs_alloca_next /\ s.vs_halted = s0.vs_halted
Proof
  simp[store_copy_frame_def] >> strip_tac >>
  qpat_x_assum `store_copy_normalize _ _ = _`
    (mp_tac o Q.AP_TERM `\s. (s.vs_memory, s.vs_labels, s.vs_call_ctx,
      s.vs_allocas, s.vs_alloca_next, s.vs_halted)`) >>
  simp[store_copy_normalize_def, place_store_prefix_fields]
QED

Theorem place_store_copy_init_path:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id ASSIGN [Lit 0w] [cv]]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  (!x. not_fresh_at sa x ==> x <> cv) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      store_copy_frame sa loc b k s 0 t /\
      eval_operand (Var cv) t = SOME 0w /\
      ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx + 1
Proof
  strip_tac >>
  `run_inst_seq [mk_inst id ASSIGN [Lit 0w] [cv]] s =
   OK (update_var cv 0w s)` by
    simp[run_inst_seq_def, stepInstBaseLib.simp_opcode_clause ``ASSIGN``,
         mk_inst_def, eval_operand_lit] >>
  drule tuple_run_inst_seq_gas_path >>
  disch_then drule >> disch_then drule >>
  simp[mk_inst_def, is_terminator_def] >>
  disch_then (qspec_then `ctx` mp_tac) >>
  strip_tac >>
  qexists_tac `(update_var cv 0w s) with vs_inst_idx := s.vs_inst_idx + 1` >>
  conj_tac >- simp[gas_marked_path_def] >>
  simp[store_copy_frame_def, store_copy_normalize_def, place_store_prefix_eqs,
       update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem place_store_copy_test_path:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id EQ [Var cv; Lit (n2w n)] [tv]]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  store_copy_frame sa loc b k s0 i s /\
  eval_operand (Var cv) s = SOME (n2w i) /\
  cv <> tv /\ (!x. not_fresh_at sa x ==> x <> tv) /\
  i <= n /\ n < dimword (:256) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      store_copy_frame sa loc b k s0 i t /\
      eval_operand (Var cv) t = SOME (n2w i) /\
      eval_operand (Var tv) t = SOME (if i = n then 1w else 0w) /\
      ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx + 1
Proof
  strip_tac >>
  `i < dimword (:256)` by decide_tac >>
  `bool_to_word (n2w i = n2w n : bytes32) =
   (if i = n then 1w else 0w)` by
    (Cases_on `i = n` >> simp[n2w_11, LESS_MOD, bool_to_word_def]) >>
  `run_inst_seq [mk_inst id EQ [Var cv; Lit (n2w n)] [tv]] s =
   OK (update_var tv (if i = n then 1w else 0w) s)` by
    simp[run_inst_seq_def, stepInstBaseLib.simp_opcode_clause ``EQ``,
         mk_inst_def, exec_pure2_def, eval_operand_lit] >>
  drule tuple_run_inst_seq_gas_path >>
  disch_then drule >> disch_then drule >>
  simp[mk_inst_def, is_terminator_def] >>
  disch_then (qspec_then `ctx` mp_tac) >> strip_tac >>
  qexists_tac `(update_var tv (if i = n then 1w else 0w) s)
    with vs_inst_idx := s.vs_inst_idx + 1` >>
  conj_tac >- simp[gas_marked_path_def] >>
  gvs[store_copy_frame_def, store_copy_normalize_def,
      update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem place_store_copy_body_path:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX
    [mk_inst id MUL [Var cv; Lit 32w] [mv];
     mk_inst (id+1) ADD [src; Var mv] [sv];
     mk_inst (id+2) MLOAD [Var sv] [vv];
     mk_inst (id+3) ADD [dst; Var cv] [dv];
     mk_inst (id+4) (if loc = LocStorage then SSTORE else TSTORE)
       [Var dv; Var vv] [];
     mk_inst (id+5) ADD [Var cv; Lit 1w] [nv];
     mk_inst (id+6) ASSIGN [Var nv] [cv]]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  store_copy_frame sa loc b k s0 i s /\
  eval_operand src s0 = SOME b /\ eval_operand dst s0 = SOME k /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand (Var cv) s = SOME (n2w i) /\
  ALL_DISTINCT [cv;mv;sv;vv;dv;nv] /\
  (!x. not_fresh_at sa x ==> ~MEM x [cv;mv;sv;vv;dv;nv]) /\
  ~s0.vs_call_ctx.cc_static ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      store_copy_frame sa loc b k s0 (SUC i) t /\
      eval_operand (Var cv) t = SOME (n2w (SUC i)) /\
      ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx + 7
Proof
  strip_tac >>
  drule place_store_frame_fields >> strip_tac >>
  `eval_operand src s = SOME b /\ eval_operand dst s = SOME k` by
    (Cases_on `src` >> Cases_on `dst` >>
     gvs[eval_operand_def, store_copy_frame_def] >> metis_tac[]) >>
  qabbrev_tac `a = n2w i * 32w : bytes32` >>
  qabbrev_tac `val = mload (w2n (b + a)) s0` >>
  qabbrev_tac `q = update_var dv (k + n2w i)
    (update_var vv val (update_var sv (b+a) (update_var mv a s)))` >>
  qabbrev_tac `r = update_var cv (n2w i + 1w)
    (update_var nv (n2w i + 1w)
      ((if loc = LocStorage then sstore else tstore) (k+n2w i) val q))` >>
  qmatch_asmsub_abbrev_tac `isPREFIX code _` >>
  `mload (w2n (b+a)) (update_var sv (b+a) (update_var mv a s)) = val` by
    simp[Abbr `val`, mload_def, update_var_def] >>
  `run_inst_seq code s = OK r` by
    (fs[ALL_DISTINCT] >>
     `!x. MEM x [cv;mv;sv;vv;dv;nv] ==> src <> Var x /\ dst <> Var x` by
       (simp[] >> rpt strip_tac >> metis_tac[]) >>
     Cases_on `loc = LocStorage` >>
     simp[Abbr `code`, Abbr `r`, Abbr `q`, Abbr `a`,
         run_inst_seq_def, mk_inst_def,
         stepInstBaseLib.simp_opcode_clause ``MUL``,
         stepInstBaseLib.simp_opcode_clause ``ADD``,
         stepInstBaseLib.simp_opcode_clause ``MLOAD``,
         stepInstBaseLib.simp_opcode_clause ``SSTORE``,
         stepInstBaseLib.simp_opcode_clause ``TSTORE``,
         stepInstBaseLib.simp_opcode_clause ``ASSIGN``,
         exec_pure2_def, exec_read1_def, slot_copy_operand_update, eval_operand_lit,
         eval_operand_update_var_local] >>
     simp[exec_write2_def, update_var_def, eval_operand_def, lookup_var_def,
          FLOOKUP_UPDATE, sstore_def, tstore_def] >>
     fs[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, Excl "isPREFIX"]) >>
  drule tuple_run_inst_seq_gas_path >>
  disch_then drule >> disch_then drule >>
  simp[Abbr `code`, mk_inst_def, is_terminator_def] >>
  disch_then (qspec_then `ctx` mp_tac) >> strip_tac >>
  qexists_tac `r with vs_inst_idx := s.vs_inst_idx + 7` >>
  conj_tac >- (Cases_on `loc = LocStorage` >>
    gvs[gas_marked_path_def, is_terminator_def, Excl "isPREFIX"]) >>
  Cases_on `loc = LocStorage` >>
  gvs[Abbr `r`, Abbr `q`, Abbr `val`, Abbr `a`,
      store_copy_frame_def, store_copy_normalize_def, place_store_prefix_eqs,
      update_var_def, lookup_var_def, eval_operand_def, FLOOKUP_UPDATE,
      sstore_def, tstore_def, ADD1, n2w_SUC, Excl "isPREFIX"] >>
  qpat_x_assum `_ = store_copy_prefix _ _ _ _ _` (SUBST1_TAC o SYM) >> simp[]
QED

Theorem place_store_copy_path:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_word_copy_loop src dst n LocMemory loc F sa = (u,sb) /\
  fn_has_code sa sb func /\ n < dimword (:256) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s0 = SOME b /\ eval_operand dst s0 = SOME k /\
  ~s0.vs_call_ctx.cc_static /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s0 0 (OK t) /\
      store_copy_frame sa loc b k s0 n t /\ ~t.vs_halted /\
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
       store_copy_frame sa loc b k s0 n t /\ ~t.vs_halted /\
       t.vs_current_bb = exit /\ t.vs_inst_idx = 0` by suspend "loop" >>
  qexists_tac `t` >> simp[] >>
  drule_all gas_marked_path_then >> simp[]
QED

Resume place_store_copy_path[init]:
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

Resume place_store_copy_path[loop]:
  qabbrev_tac `Inv = \j q. store_copy_frame sa loc b k s0 j q /\
    eval_operand (Var cv) q = SOME (n2w j)` >>
  `?t. gas_marked_path F ctx func r 0 (OK t) /\ Inv n t /\
       ~t.vs_halted /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0`
    suffices_by (simp[Abbr `Inv`] >> metis_tac[]) >>
  irule place_copy_iterate_path >> simp[] >>
  reverse conj_tac
  >- (qexistsl_tac [`0`, `n`] >> simp[Abbr `Inv`]) >>
  qexists_tac `body_lbl` >> simp[] >>
  conj_tac >- suspend "body" >> suspend "header"
QED

Resume place_store_copy_path[body]:
  qunabbrev_tac `Inv` >> BETA_TAC >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `isPREFIX (_::_::_::_::_::_::_::_::[]) _`
    (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
  qmatch_asmsub_abbrev_tac `isPREFIX code bbb.bb_instructions` >>
  `isPREFIX (TAKE 7 code) (DROP q.vs_inst_idx bbb.bb_instructions)` by
    simp[Abbr `code`] >>
  `ALL_DISTINCT [cv;mv;sv;vv;dv;nv] /\
   (!x. not_fresh_at sa x ==> ~MEM x [cv;mv;sv;vv;dv;nv])` by
    (fs[ALL_DISTINCT] >> metis_tac[]) >>
  `lookup_block q.vs_current_bb func.fn_blocks = SOME bbb` by simp[] >>
  qunabbrev_tac `code` >>
  qpat_x_assum `isPREFIX (TAKE 7 _) _`
    (assume_tac o SIMP_RULE (srw_ss()) [TAKE_def, Excl "isPREFIX"]) >>
  drule_all place_store_copy_body_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `get_instruction bbb t.vs_inst_idx =
   SOME (mk_inst (idb+7) JMP [Label hdr] [])` by
    simp[get_instruction_def, EL_APPEND_EQN] >>
  `gas_marked_path F ctx func t 0 (OK (jump_to hdr t))` by
    (irule place_copy_jump_path >> simp[] >>
     qexists_tac `idb+7` >> simp[get_instruction_def, EL_APPEND_EQN]) >>
  qexists_tac `jump_to hdr t` >>
  conj_tac >- (drule_all gas_marked_path_then >> simp[]) >>
  qpat_x_assum `eval_operand (Var cv) t = _`
    (assume_tac o REWRITE_RULE [eval_operand_def, lookup_var_def]) >>
  simp[place_store_frame_control, jump_to_def, eval_operand_def,
       lookup_var_def, GSYM ADD1]
QED

Resume place_store_copy_path[header]:
  qunabbrev_tac `Inv` >> BETA_TAC >> rpt gen_tac >> strip_tac >>
  qpat_assum `isPREFIX [mk_inst _ EQ _ _; _] _`
    (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
  `isPREFIX [mk_inst idh EQ [Var cv; Lit (n2w n)] [tv]]
    (DROP q.vs_inst_idx bbh.bb_instructions)` by simp[] >>
  `cv <> tv /\ (!x. not_fresh_at sa x ==> x <> tv)` by
    (fs[ALL_DISTINCT] >> metis_tac[]) >>
  `lookup_block q.vs_current_bb func.fn_blocks = SOME bbh` by simp[] >>
  drule_all place_store_copy_test_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `get_instruction bbh t.vs_inst_idx =
   SOME (mk_inst (idh+1) JNZ [Var tv; Label exit; Label body_lbl] [])` by
    simp[get_instruction_def, EL_APPEND_EQN] >>
  `lookup_block t.vs_current_bb func.fn_blocks = SOME bbh` by metis_tac[] >>
  drule_all place_copy_branch_path >>
  disch_then (qspec_then `ctx` assume_tac) >>
  `gas_marked_path F ctx func t 0
    (OK (jump_to (if j = n then exit else body_lbl) t))` by
    (Cases_on `j = n` >> fs[]) >>
  qexists_tac `jump_to (if j = n then exit else body_lbl) t` >>
  conj_tac >- (drule_all gas_marked_path_then >> simp[]) >>
  qpat_x_assum `eval_operand (Var cv) t = _`
    (assume_tac o REWRITE_RULE [eval_operand_def, lookup_var_def]) >>
  qpat_x_assum `store_copy_frame sa loc b k s0 j t` mp_tac >>
  simp[place_store_frame_control, jump_to_def, eval_operand_def, lookup_var_def]
QED

Finalise place_store_copy_path
