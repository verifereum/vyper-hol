Theory immutableBytestringRuntime
Ancestors
  immutableCopyExecution bytestringCopyExecution fragExec stmtSimStoreCopy
  fragGasPath fragGasMode fragGasSeq placeCopyControlPath immutableWordExecution
  immutableMemoryFrame emitHelperProps context compileEnv loweringStateRelDefs
  emitHelper exprLoweringProps venomState venomExecSemantics venomInst
Libs
  stepInstBaseLib

val _ = Parse.hide "count";

Theorem compile_imm_store_loop_none_path:
  compile_word_copy_loop_base src dst count LocMemory LocCode T NONE sa = (u,sb) /\
  fn_has_code sa sb func /\ n < dimword (:256) /\
  (!x. src = Var x \/ dst = Var x \/ count = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  eval_operand count s = SOME (n2w n) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
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
  strip_tac >>
  `?hdr body_lbl cv tv mv sv vv dm dv nv id0 idh idb bb0 bbh bbb.
    lookup_block sa.cs_current_bb func.fn_blocks = SOME bb0 /\
    isPREFIX
      [mk_inst id0 ASSIGN [Lit 0w] [cv];
       mk_inst (id0+1) JMP [Label hdr] []]
      (DROP (LENGTH sa.cs_current_insts) bb0.bb_instructions) /\
    lookup_block hdr func.fn_blocks = SOME bbh /\
    isPREFIX
      [mk_inst idh EQ [Var cv; count] [tv];
       mk_inst (idh+1) JNZ [Var tv; Label sb.cs_current_bb; Label body_lbl] []]
      bbh.bb_instructions /\
    lookup_block body_lbl func.fn_blocks = SOME bbb /\
    isPREFIX
      [mk_inst idb MUL [Var cv; Lit 32w] [mv];
       mk_inst (idb+1) ADD [src; Var mv] [sv];
       mk_inst (idb+2) MLOAD [Var sv] [vv];
       mk_inst (idb+3) MUL [Var cv; Lit 32w] [dm];
       mk_inst (idb+4) ADD [dst; Var dm] [dv];
       mk_inst (idb+5) ISTORE [Var dv; Var vv] [];
       mk_inst (idb+6) ADD [Var cv; Lit 1w] [nv];
       mk_inst (idb+7) ASSIGN [Var nv] [cv];
       mk_inst (idb+8) JMP [Label hdr] []]
      bbb.bb_instructions /\
    LENGTH sb.cs_current_insts = 0 /\
    sb.cs_next_var = sa.cs_next_var + 8 /\
    ALL_DISTINCT [cv;tv;mv;sv;vv;dm;dv;nv] /\
    (!x. MEM x [cv;tv;mv;sv;vv;dm;dv;nv] ==> not_fresh_at sb x) /\
    (!x. not_fresh_at sa x ==> ~MEM x [cv;tv;mv;sv;vv;dm;dv;nv])`
    by suspend "shape" >>
  suspend "execute"
QED

Resume compile_imm_store_loop_none_path[shape]:
  gvs[compile_word_copy_loop_base_def, word_scale_def,
      compile_ptr_load_def, compile_ptr_store_def, compile_imm_store_word_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_label_def, fresh_var_def, emit_inst_def, emit_op_def,
      emit_void_def, fresh_id_def, emit_def, new_block_def,
      not_fresh_at_def, fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def,
      Excl "isPREFIX"] >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM, arithmeticTheory.ADD1, Excl "isPREFIX"] >>
  qmatch_asmsub_abbrev_tac `mk_inst _ MUL [Var cv; Lit 32w] [mv]` >>
  qmatch_asmsub_abbrev_tac `mk_inst _ EQ _ [tv]` >>
  qmatch_asmsub_abbrev_tac `mk_inst _ ADD [src; Var mv] [sv]` >>
  qmatch_asmsub_abbrev_tac `mk_inst _ MLOAD _ [vv]` >>
  qmatch_asmsub_abbrev_tac `mk_inst _ ADD [dst; Var dm] [dv]` >>
  qmatch_asmsub_abbrev_tac `mk_inst _ ADD [Var cv; Lit 1w] [nv]` >>
  qexistsl_tac [`fresh_label_output "wcopy_cond" sa.cs_next_label`,
    `fresh_label_output "wcopy_body" (sa.cs_next_label + 1)`,
    `cv`, `tv`, `mv`, `sv`, `vv`, `dm`, `dv`, `nv`,
    `sa.cs_next_id`, `sa.cs_next_id + 2`, `sa.cs_next_id + 4`] >>
  rpt (goal_assum (drule_at Any)) >>
  once_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  simp[rich_listTheory.DROP_LENGTH_APPEND, Excl "isPREFIX"] >>
  simp[Abbr `cv`, Abbr `tv`, Abbr `mv`, Abbr `sv`, Abbr `vv`,
       Abbr `dm`, Abbr `dv`, Abbr `nv`, fresh_var_distinct] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Resume compile_imm_store_loop_none_path[execute]:
  `?r. gas_marked_path F ctx func s 0 (OK r) /\
       immutable_loop_frame sa sb s a b 0 r /\
       eval_operand (Var cv) r = SOME 0w /\ ~r.vs_halted /\
       r.vs_current_bb = hdr /\ r.vs_inst_idx = 0` by suspend "entry" >>
  qabbrev_tac `Inv = \j q. immutable_loop_frame sa sb s a b j q /\
    eval_operand (Var cv) q = SOME (n2w j)` >>
  `?t. gas_marked_path F ctx func r 0 (OK t) /\ Inv n t /\
       ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = 0` by
    (irule place_copy_iterate_path >> simp[] >>
     reverse conj_tac
     >- (qexistsl_tac [`0`, `n`] >> simp[Abbr `Inv`]) >>
     qexists_tac `body_lbl` >> simp[] >>
     conj_tac >- suspend "body" >> suspend "header") >>
  qexists_tac `t` >>
  conj_tac >- (drule_all gas_marked_path_then >> simp[]) >>
  suspend "exit"
QED

Resume compile_imm_store_loop_none_path[entry]:
  `!x. not_fresh_at sa x ==> x <> cv` by metis_tac[listTheory.MEM] >>
  `not_fresh_at sb cv` by metis_tac[listTheory.MEM] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb0` by simp[] >>
  `isPREFIX [mk_inst id0 ASSIGN [Lit 0w] [cv]]
    (DROP s.vs_inst_idx bb0.bb_instructions)` by
    (qpat_assum `isPREFIX [mk_inst _ ASSIGN _ _; _] _`
       (strip_assume_tac o REWRITE_RULE [rich_listTheory.IS_PREFIX_APPEND]) >> simp[]) >>
  `run_inst_seq [mk_inst id0 ASSIGN [Lit 0w] [cv]] s =
    OK (update_var cv 0w s)` by
    simp[run_inst_seq_def, mk_inst_def,
         stepInstBaseLib.simp_opcode_clause ``ASSIGN``, eval_operand_lit] >>
  drule tuple_run_inst_seq_gas_path >>
  disch_then drule >> disch_then drule >>
  simp[mk_inst_def, is_terminator_def] >>
  disch_then (qspec_then `ctx` mp_tac) >> strip_tac >>
  qabbrev_tac `t = update_var cv 0w s with
    vs_inst_idx := LENGTH sa.cs_current_insts + 1` >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    simp[gas_marked_path_def, Abbr `t`] >>
  `~t.vs_halted /\ t.vs_current_bb = sa.cs_current_bb /\
   t.vs_inst_idx = LENGTH sa.cs_current_insts + 1` by
    simp[Abbr `t`, update_var_def] >>
  `get_instruction bb0 t.vs_inst_idx =
    SOME (mk_inst (id0+1) JMP [Label hdr] [])` by
    (qpat_assum `isPREFIX [mk_inst _ ASSIGN _ _; _] _`
       (mp_then Any strip_assume_tac fragGasSeqAbortTheory.instruction_prefix_cursor) >>
     drule fragGasSeqAbortTheory.instruction_prefix_cursor >> simp[arithmeticTheory.ADD1]) >>
  `gas_marked_path F ctx func t 0 (OK (jump_to hdr t))` by
    (irule place_copy_jump_path >> simp[] >> metis_tac[]) >>
  qexists_tac `jump_to hdr t` >>
  conj_tac >- (drule_all gas_marked_path_then >> simp[]) >>
  reverse conj_tac
  >- simp[Abbr `t`, jump_to_def, eval_operand_def, lookup_var_def,
           update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[immutable_loop_frame_def, Abbr `t`, store_copy_normalize_def,
       immutable_transfers_def, jump_to_def, update_var_def, lookup_var_def,
       fresh_vars_wrt_def, finite_mapTheory.FLOOKUP_UPDATE,
       venom_state_component_equality] >>
  rpt strip_tac >> gvs[not_fresh_at_def]
QED

Resume compile_imm_store_loop_none_path[body]:
  qunabbrev_tac `Inv` >> BETA_TAC >> rpt gen_tac >> strip_tac >>
  `eval_operand src q = SOME a /\ eval_operand dst q = SOME b` by
    (fs[immutable_loop_frame_def] >>
     `q.vs_labels = s.vs_labels` by
       (qpat_x_assum `store_copy_normalize _ _ = _` mp_tac >>
        simp[store_copy_normalize_def, venom_state_component_equality] >>
        suspend "labels") >>
     Cases_on `src` >> Cases_on `dst` >> gvs[eval_operand_def] >> metis_tac[]) >>
  qpat_assum `isPREFIX (_::_::_::_::_::_::_::_::_::[]) _`
    (strip_assume_tac o REWRITE_RULE [rich_listTheory.IS_PREFIX_APPEND]) >>
  qmatch_asmsub_abbrev_tac `isPREFIX code bbb.bb_instructions` >>
  qabbrev_tac `value = mload (w2n (a+n2w (32*j))) q` >>
  qabbrev_tac `result = update_var cv (n2w (j+1))
    (update_var nv (n2w (j+1))
      (istore (w2n (b+n2w (32*j))) value
        (update_var dv (b+n2w (32*j)) (update_var dm (n2w (32*j))
          (update_var vv value (update_var sv (a+n2w (32*j))
            (update_var mv (n2w (32*j)) q)))))))` >>
  `run_inst_seq (TAKE 8 code) q = OK result` by suspend "body_run" >>
  `isPREFIX (TAKE 8 code) (DROP q.vs_inst_idx bbb.bb_instructions)` by
    simp[Abbr `code`] >>
  `lookup_block q.vs_current_bb func.fn_blocks = SOME bbb` by simp[] >>
  drule tuple_run_inst_seq_gas_path >>
  disch_then drule >> disch_then drule >>
  simp[Abbr `code`, mk_inst_def, is_terminator_def] >>
  disch_then (qspec_then `ctx` mp_tac) >> strip_tac >>
  qabbrev_tac `t = result with vs_inst_idx := 8` >>
  `gas_marked_path F ctx func q 0 (OK t)` by simp[gas_marked_path_def, Abbr `t`] >>
  `~t.vs_halted /\ t.vs_current_bb = body_lbl /\ t.vs_inst_idx = 8` by
    simp[Abbr `t`, Abbr `result`, update_var_def, istore_def, mstore_def] >>
  `gas_marked_path F ctx func t 0 (OK (jump_to hdr t))` by
    (irule place_copy_jump_path >> simp[] >> qexists_tac `idb+8` >>
     simp[get_instruction_def, listTheory.EL_APPEND_EQN]) >>
  qexists_tac `jump_to hdr t` >>
  conj_tac >- (drule_all gas_marked_path_then >> simp[]) >>
  reverse conj_tac >- simp[jump_to_def] >>
  reverse conj_tac
  >- (fs[listTheory.ALL_DISTINCT] >>
      simp[Abbr `t`, Abbr `result`, eval_operand_def, lookup_var_def,
           jump_to_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  suspend "body_frame"
QED

Resume compile_imm_store_loop_none_path[header]:
  qunabbrev_tac `Inv` >> BETA_TAC >> rpt gen_tac >> strip_tac >>
  `eval_operand count q = SOME (n2w n)` by
    (fs[immutable_loop_frame_def] >>
     Cases_on `count` >> gvs[eval_operand_def] >>
     suspend "count_operand") >>
  `j < dimword (:256)` by decide_tac >>
  `bool_to_word (n2w j = n2w n : bytes32) =
   (if j = n then 1w else 0w)` by
    (Cases_on `j = n` >> simp[wordsTheory.n2w_11, arithmeticTheory.LESS_MOD,
                              bool_to_word_def]) >>
  qpat_assum `isPREFIX [mk_inst _ EQ _ _; _] _`
    (strip_assume_tac o REWRITE_RULE [rich_listTheory.IS_PREFIX_APPEND]) >>
  `isPREFIX [mk_inst idh EQ [Var cv; count] [tv]]
    (DROP q.vs_inst_idx bbh.bb_instructions)` by simp[] >>
  `lookup_block q.vs_current_bb func.fn_blocks = SOME bbh` by simp[] >>
  `run_inst_seq [mk_inst idh EQ [Var cv; count] [tv]] q =
   OK (update_var tv (if j = n then 1w else 0w) q)` by
    simp[run_inst_seq_def, mk_inst_def,
         stepInstBaseLib.simp_opcode_clause ``EQ``, exec_pure2_def] >>
  drule tuple_run_inst_seq_gas_path >>
  disch_then drule >> disch_then drule >>
  simp[mk_inst_def, is_terminator_def] >>
  disch_then (qspec_then `ctx` mp_tac) >> strip_tac >>
  qabbrev_tac `t = update_var tv (if j = n then 1w else 0w) q
    with vs_inst_idx := 1` >>
  `gas_marked_path F ctx func q 0 (OK t)` by simp[gas_marked_path_def, Abbr `t`] >>
  `get_instruction bbh t.vs_inst_idx =
   SOME (mk_inst (idh+1) JNZ [Var tv; Label sb.cs_current_bb; Label body_lbl] [])` by
    simp[Abbr `t`, get_instruction_def, listTheory.EL_APPEND_EQN] >>
  `~t.vs_halted /\ lookup_block t.vs_current_bb func.fn_blocks = SOME bbh /\
   eval_operand (Var tv) t = SOME (if j = n then 1w else 0w)` by
    simp[Abbr `t`, update_var_def, eval_operand_def, lookup_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  drule_all place_copy_branch_path >>
  disch_then (qspec_then `ctx` assume_tac) >>
  `gas_marked_path F ctx func t 0
    (OK (jump_to (if j = n then sb.cs_current_bb else body_lbl) t))` by
    (Cases_on `j = n` >> fs[]) >>
  qexists_tac `jump_to (if j = n then sb.cs_current_bb else body_lbl) t` >>
  conj_tac >- (drule_all gas_marked_path_then >> simp[]) >>
  reverse conj_tac >- simp[jump_to_def] >>
  reverse conj_tac
  >- gvs[listTheory.ALL_DISTINCT, Abbr `t`, eval_operand_def,
       lookup_var_def, jump_to_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  fs[immutable_loop_frame_def] >>
  simp[store_copy_normalize_def, Abbr `t`, jump_to_def, update_var_def,
       lookup_var_def, fresh_vars_wrt_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  suspend "header_frame"
QED

Resume compile_imm_store_loop_none_path[exit]:
  fs[Abbr `Inv`, immutable_loop_frame_def] >>
  `!i. (immutable_transfers T T a b i 0 s).vs_labels = s.vs_labels` by
    (Induct >> simp[immutable_transfers_snoc, immutable_transfers_def,
      immutable_word_transfer_def, istore_def, mstore_def]) >>
  `t.vs_labels = s.vs_labels` by
    (qpat_x_assum `store_copy_normalize s t = _` mp_tac >>
     simp[store_copy_normalize_def, venom_state_component_equality]) >>
  conj_tac >- gvs[store_copy_normalize_def] >>
  rpt strip_tac >> simp[immutable_operand_frame_def] >>
  rpt strip_tac >> Cases_on `p` >> gvs[eval_operand_def] >>
  suspend "exit_operand"
QED

Resume compile_imm_store_loop_none_path[labels]:
  `!i. (immutable_transfers T T a b i 0 s).vs_labels = s.vs_labels` by
    (Induct >> simp[immutable_transfers_snoc, immutable_transfers_def,
      immutable_word_transfer_def, istore_def, mstore_def]) >>
  simp[]
QED

Resume compile_imm_store_loop_none_path[body_run]:
  `!x. MEM x [cv;tv;mv;sv;vv;dm;dv;nv] ==> src <> Var x /\ dst <> Var x` by
    metis_tac[] >>
  fs[listTheory.ALL_DISTINCT, listTheory.MEM, DISJ_IMP_THM, FORALL_AND_THM] >>
  `n2w j * 32w = (n2w (32*j):bytes32)` by
    simp[GSYM wordsTheory.word_mul_n2w, wordsTheory.WORD_MULT_COMM] >>
  simp[Abbr `code`, Abbr `result`, Abbr `value`, run_inst_seq_def, mk_inst_def,
    stepInstBaseLib.simp_opcode_clause ``MUL``,
    stepInstBaseLib.simp_opcode_clause ``ADD``,
    stepInstBaseLib.simp_opcode_clause ``MLOAD``,
    stepInstBaseLib.simp_opcode_clause ``ISTORE``,
    stepInstBaseLib.simp_opcode_clause ``ASSIGN``,
    exec_pure2_def, exec_read1_def, eval_operand_lit, slot_copy_operand_update,
    immutable_word_istore_operand_frame,
    wordsTheory.n2w_SUC, GSYM arithmeticTheory.ADD1] >>
  simp[mload_def, update_var_def]
QED

Resume compile_imm_store_loop_none_path[body_frame]:
  fs[immutable_loop_frame_def] >>
  conj_tac
  >- (simp[Abbr `t`, Abbr `result`, store_copy_normalize_update,
           store_copy_normalize_jump, store_copy_normalize_idx] >>
      `j+1 = SUC j` by decide_tac >> pop_assum SUBST1_TAC >>
      simp[immutable_transfers_snoc, immutable_word_transfer_def,
           immutable_copy_read_def] >>
      qpat_x_assum `store_copy_normalize s q = _` (SUBST1_TAC o SYM) >>
      simp[Abbr `value`, store_copy_normalize_def, update_var_def,
           mload_def, istore_def, mstore_def]) >>
  simp[Abbr `t`, Abbr `result`, jump_to_def, update_var_def,
       lookup_var_def, fresh_vars_wrt_def, istore_def, mstore_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  suspend "body_vars"
QED

Resume compile_imm_store_loop_none_path[count_operand]:
  `!i. (immutable_transfers T T a b i 0 s).vs_labels = s.vs_labels` by
    (Induct >> simp[immutable_transfers_snoc, immutable_transfers_def,
      immutable_word_transfer_def, istore_def, mstore_def]) >>
  `q.vs_labels = s.vs_labels` by
    (qpat_x_assum `store_copy_normalize s q = _` mp_tac >>
     simp[store_copy_normalize_def, venom_state_component_equality]) >> simp[]
QED

Resume compile_imm_store_loop_none_path[header_frame]:
  `not_fresh_at sb tv` by metis_tac[] >>
  qpat_x_assum `!x. not_fresh_at sa x ==> lookup_var x q = _` mp_tac >>
  qpat_x_assum `fresh_vars_wrt sa s ==> fresh_vars_wrt sb q` mp_tac >>
  qpat_x_assum `sb.cs_next_var = _` mp_tac >>
  qpat_x_assum `not_fresh_at sb tv` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[lookup_var_def, fresh_vars_wrt_def, not_fresh_at_def] >>
  metis_tac[]
QED

Resume compile_imm_store_loop_none_path[exit_operand]:
  `not_fresh_at sa s'` by
    (qpat_x_assum `fresh_vars_wrt sa s` mp_tac >>
     qpat_x_assum `lookup_var s' s = SOME w` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[fresh_vars_wrt_def, not_fresh_at_def, lookup_var_def,
          finite_mapTheory.FLOOKUP_DEF, arithmeticTheory.GREATER_EQ] >> metis_tac[]) >>
  metis_tac[]
QED

Resume compile_imm_store_loop_none_path[body_vars]:
  qpat_x_assum `!x. not_fresh_at sa x ==> lookup_var x q = _` mp_tac >>
  qpat_x_assum `fresh_vars_wrt sa s ==> fresh_vars_wrt sb q` mp_tac >>
  qpat_x_assum `sb.cs_next_var = _` mp_tac >>
  qpat_x_assum `!x. x = cv \/ _ ==> not_fresh_at sb x` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[lookup_var_def, fresh_vars_wrt_def, not_fresh_at_def] >>
  metis_tac[]
QED

Finalise compile_imm_store_loop_none_path

Theorem compile_store_immutable_bytestring_optional_path:
  compile_store_immutable_bytestring imm src dst sa = ((),sb) /\
  fn_has_code sa sb func /\ len + 63 < dimword (:256) /\
  (!x. src = Var x \/ dst = Var x \/
       (?region. imm = SOME region /\ region = Var x) ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w) /\
  mload (w2n a) s = n2w len /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (t with <|vs_vars := s.vs_vars;
                vs_current_bb := s.vs_current_bb;
                vs_prev_bb := s.vs_prev_bb;
                vs_inst_idx := s.vs_inst_idx|>) =
        immutable_transfers T T a b (1 + word_size len) 0 s /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  Cases_on `imm`
  >- suspend "none"
  >> strip_tac >> irule compile_store_immutable_bytestring_path >>
  metis_tac[]
QED

Resume compile_store_immutable_bytestring_optional_path[none]:
  strip_tac >>
  Cases_on `compile_bytestring_word_count src sa` >>
  rename1 `compile_bytestring_word_count src sa = (wc,sm)` >>
  Cases_on `compile_word_copy_loop_base src dst wc LocMemory LocCode T NONE sm` >>
  rename1 `compile_word_copy_loop_base src dst wc LocMemory LocCode T NONE sm = (u,sn)` >>
  `sn = sb` by
    fs[compile_store_immutable_bytestring_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, pairTheory.UNCURRY] >> gvs[] >>
  drule bytestring_word_count_shape >> strip_tac >>
  `cs_extends sa sm` by
    (irule cs_extends_same_block >> fs[same_blocks_def] >> simp[]) >>
  `ci_mono sm sb` by
    (mp_tac (Q.SPECL [`src`, `dst`, `wc`, `LocMemory`, `LocCode`, `T`,
                      `NONE`, `sm`] ci_mono_word_copy) >> simp[]) >>
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
    (`(len + 31) DIV 32 <= len + 31` by simp[arithmeticTheory.DIV_LESS_EQ] >>
     fs[vfmConstantsTheory.word_size_def] >> decide_tac) >>
  drule_all bytestring_word_count_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_marked_path F ctx func s 0 (OK r)` >>
  `r.vs_labels = s.vs_labels /\ store_copy_normalize s r = s` by
    (fs[venom_state_component_equality, store_copy_normalize_def]) >>
  `!p. (!x. p = Var x ==> not_fresh_at sa x) ==>
       eval_operand p r = eval_operand p s` by
    (Cases >> simp[eval_operand_def]) >>
  `eval_operand src r = SOME a /\ eval_operand dst r = SOME b` by metis_tac[] >>
  `!x. src = Var x \/ dst = Var x \/ wc = Var x ==>
       not_fresh_at sm x` by metis_tac[] >>
  drule_all compile_imm_store_loop_none_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >>
  conj_tac >- (drule_all gas_marked_path_then >> simp[]) >>
  conj_tac >- metis_tac[] >>
  simp[] >>
  suspend "normalize"
QED

Resume compile_store_immutable_bytestring_optional_path[normalize]:
  `!n off q. store_copy_normalize s (immutable_transfers T T a b n off q) =
      immutable_transfers T T a b n off (store_copy_normalize s q)` by
    (Induct >> simp[immutable_transfers_def] >>
     simp[immutable_word_transfer_def, immutable_copy_read_def,
          store_copy_normalize_def, mload_def, istore_def, mstore_def]) >>
  qpat_x_assum `(t with <|vs_vars := r.vs_vars; vs_current_bb := r.vs_current_bb;
      vs_prev_bb := r.vs_prev_bb; vs_inst_idx := r.vs_inst_idx|>) = _`
    (mp_tac o AP_TERM ``store_copy_normalize s``) >>
  simp[store_copy_normalize_def]
QED

Finalise compile_store_immutable_bytestring_optional_path
