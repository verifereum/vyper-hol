(* Compose fixed-run blocks before a single counted-path lift. *)
Theory bodyPtrSignedConvertUnsignedCompose
Ancestors
  bodyPtrSignedConvertSourceFixed bodyPtrSignedConvertUnsignedFixed
  bodyPtrSignedConvertUnsignedLoad bodyPtrSignedConvertSourceFrame
  instSeqComposePtr fragGasSeqPtr exprLoweringProps fragExec ghostPcTransportPtr
  emitHelperProps venomState venomInst venomExecSemantics ptrDiscipline
  bodyPtrDefs finite_map words arithmetic list compileEnv loweringStateRelDefs

Theorem bytestring_source_run:
  src <> len /\ lookup_var src s = SOME a ==>
  run_inst_seq [mk_inst i MLOAD [Var src] [len];
                mk_inst j ADD [Var src;Lit 32w] [dp]] s =
    OK (update_var dp (a+32w) (update_var len (mload (w2n a) s) s))
Proof
  strip_tac >>
  `step_inst_base (mk_inst i MLOAD [Var src] [len]) s =
     OK (update_var len (mload (w2n a) s) s)` by
    (irule step_MLOAD >> simp[eval_operand_def]) >>
  `step_inst_base (mk_inst j ADD [Var src;Lit 32w] [dp])
     (update_var len (mload (w2n a) s) s) =
     OK (update_var dp (a+32w) (update_var len (mload (w2n a) s) s))` by
    (irule step_ADD >> fs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  simp[run_inst_seq_def]
QED

Theorem unsigned_loader_fixed_frame_raw:
  ALL_DISTINCT [src;len;dp;data;sub;bits;dst] /\ ~ctx_has_dalloca ctx /\
  lookup_var src s = SOME a /\ ptr_covers G tn src s capacity /\ 64 <= capacity /\
  w2n a+32 < dimword(:256) /\ mload (w2n a) s = n2w n /\ n <= 32 /\
  (!x. w2n a <= x /\ x < w2n a+32+n ==> x NOTIN tn.t_mem) /\
  run_inst_seq [mk_inst i MLOAD [Var src] [len];
    mk_inst j ADD [Var src;Lit 32w] [dp];
    mk_inst k MLOAD [Var dp] [data];
    mk_inst l SUB [Lit 32w;Var len] [sub];
    mk_inst m MUL [Var sub;Lit 8w] [bits];
    mk_inst r SHR [Var bits;Var data] [dst]] s = OK t ==>
  ?H th.
    (!q. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst i MLOAD [Var src] [len];
       mk_inst j ADD [Var src;Lit 32w] [dp];
       mk_inst k MLOAD [Var dp] [data];
       mk_inst l SUB [Lit 32w;Var len] [sub];
       mk_inst m MUL [Var sub;Lit 8w] [bits];
       mk_inst r SHR [Var bits;Var data] [dst]] (s with vs_inst_idx := q) H th) /\
    op_prov H (Var dst) = NONE /\ op_taint th (Var dst) = {} /\
    op_prov H (Var bits) = NONE /\ op_taint th (Var bits) = {} /\
    eval_operand (Var bits) t = SOME (n2w (8*(32-n))) /\
    t.vs_memory = s.vs_memory /\ th.t_mem = tn.t_mem /\
    th.t_stor = tn.t_stor /\ th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_current_bb = s.vs_current_bb /\
    t = s with vs_vars := t.vs_vars /\
    (!p. ~MEM p [len;dp;data;sub;bits;dst] ==> lookup_var p t = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint th (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `src <> len` by fs[] >> drule_all bytestring_source_run >>
  disch_then (qspecl_then [`j`,`i`,`dp`] assume_tac) >>
  qabbrev_tac `u = update_var dp (a+32w) (update_var len (mload (w2n a) s) s)` >>
  `32 <= capacity /\
   (!x. w2n a <= x /\ x < w2n a+32 ==> x NOTIN tn.t_mem)` by
    (conj_tac >- decide_tac >> gen_tac >> disch_then strip_assume_tac >> qpat_x_assum `!x. _ ==> x NOTIN tn.t_mem` irule >> decide_tac) >>
  `ALL_DISTINCT [src;len;dp]` by fs[] >>
  drule_all bytestring_source_fixed_frame >>
  disch_then (qspecl_then [`D`,`fn`,`PG`]
    (qx_choose_then `G1` (qx_choose_then `tn1` strip_assume_tac))) >>
  `ptr_covers G1 tn1 dp u 32 /\ ALL_DISTINCT [len;dp;data;sub;bits;dst] /\
   lookup_var len u = SOME (n2w n)` by
    (rpt conj_tac >- (first_x_assum irule >> decide_tac) >> fs[]) >>
  `w2n (a+32w) = w2n a+32` by
    (simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  `!x. w2n (a+32w) <= x /\ x < w2n (a+32w)+n ==> x NOTIN tn1.t_mem` by
    (simp[wordsTheory.w2n_add, wordsTheory.w2n_n2w,
          arithmeticTheory.LESS_MOD] >>
     gen_tac >> disch_then strip_assume_tac >>
     qpat_x_assum `!x. _ /\ x < w2n a+32+n ==> _` irule >> decide_tac) >>
  `run_inst_seq [mk_inst k MLOAD [Var dp] [data];
    mk_inst l SUB [Lit 32w;Var len] [sub];
    mk_inst m MUL [Var sub;Lit 8w] [bits];
    mk_inst r SHR [Var bits;Var data] [dst]] u = OK t` by
    (drule run_inst_seq_append >>
     disch_then (qspec_then `[mk_inst k MLOAD [Var dp] [data];
       mk_inst l SUB [Lit 32w;Var len] [sub];
       mk_inst m MUL [Var sub;Lit 8w] [bits];
       mk_inst r SHR [Var bits;Var data] [dst]]` mp_tac) >> simp[]) >>
  drule_all unsigned_suffix_fixed_frame >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `H` (qx_choose_then `th` strip_assume_tac))) >>
  qexistsl_tac [`H`,`th`] >> conj_tac
  >- (irule (SRULE [APPEND] (Q.INST [`xs` |->
        `[mk_inst i MLOAD [Var src] [len]; mk_inst j ADD [Var src;Lit 32w] [dp]]`]
        inst_seq_ptr_uniform_append)) >>
      simp[is_terminator_def] >> qexistsl_tac [`G1`,`tn1`] >> simp[]) >>
  simp[] >>
  qpat_x_assum `t = u with vs_vars := _` (fn eq => once_rewrite_tac[eq]) >>
  qpat_x_assum `u = s with vs_vars := _` (fn eq => once_rewrite_tac[eq]) >> simp[]
QED

Theorem unsigned_loader_fixed_frame:
  load_bytestring_as_word (Var src) SHR sa = ((out,bits),sb) /\
  not_fresh_at sa src /\ ~ctx_has_dalloca ctx /\
  lookup_var src s = SOME a /\ ptr_covers G tn src s capacity /\ 64 <= capacity /\
  w2n a+32 < dimword(:256) /\ mload (w2n a) s = n2w n /\ n <= 32 /\
  (!x. w2n a <= x /\ x < w2n a+32+n ==> x NOTIN tn.t_mem) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H th.
    (!q. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := q) H th) /\
    op_prov H out = NONE /\ op_taint th out = {} /\
    op_prov H bits = NONE /\ op_taint th bits = {} /\
    eval_operand bits t = SOME (n2w (8*(32-n))) /\
    t.vs_memory = s.vs_memory /\ th.t_mem = tn.t_mem /\
    th.t_stor = tn.t_stor /\ th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_current_bb = s.vs_current_bb /\
    t = s with vs_vars := t.vs_vars /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint th (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all unsigned_loader_shape_fresh >> strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >> simp[] >> strip_tac >>
  drule_all unsigned_loader_fixed_frame_raw >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `H` (qx_choose_then `th` strip_assume_tac))) >>
  qexistsl_tac [`H`,`th`] >> simp[] >> metis_tac[]
QED

Theorem unsigned_loader_counted_frame:
  load_bytestring_as_word (Var src) SHR sa = ((out,bits),sb) /\
  not_fresh_at sa src /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  lookup_var src s = SOME a /\ ptr_covers G tn src s capacity /\ 64 <= capacity /\
  w2n a+32 < dimword(:256) /\ mload (w2n a) s = n2w n /\ n <= 32 /\
  (!x. w2n a <= x /\ x < w2n a+32+n ==> x NOTIN tn.t_mem) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H th.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th
      (OK (t with vs_inst_idx := s.vs_inst_idx+6)) /\
    op_prov H out = NONE /\ op_taint th out = {} /\
    op_prov H bits = NONE /\ op_taint th bits = {} /\
    eval_operand bits t = SOME (n2w (8*(32-n))) /\
    t.vs_memory = s.vs_memory /\ th.t_mem = tn.t_mem /\
    th.t_stor = tn.t_stor /\ th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_current_bb = s.vs_current_bb /\
    t = s with vs_vars := t.vs_vars /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint th (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all unsigned_loader_fixed_frame >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `H` (qx_choose_then `th` strip_assume_tac))) >>
  drule_all unsigned_loader_shape_fresh >> strip_tac >>
  `inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th` by
    (first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)` by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >> strip_tac >>
  qexistsl_tac [`H`,`th`] >> simp[] >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[mk_inst_def, arithmeticTheory.ADD_COMM]
QED

Theorem unsigned_loader_counted_ghost_frame:
  load_bytestring_as_word (Var src) SHR sa = ((out,bits),sb) /\
  not_fresh_at sa src /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  lookup_var src s = SOME a /\ ptr_covers G tn src s capacity /\ 64 <= capacity /\
  w2n a+32 < dimword(:256) /\ mload (w2n a) s = n2w n /\ n <= 32 /\
  (!x. w2n a <= x /\ x < w2n a+32+n ==> x NOTIN tn.t_mem) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es0 s0a G0 tn0 s0 G tn /\
  s0a.cs_next_var <= sa.cs_next_var /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) ==>
  ?H th.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th
      (OK (t with vs_inst_idx := s.vs_inst_idx+6)) /\
    op_prov H out = NONE /\ op_taint th out = {} /\
    op_prov H bits = NONE /\ op_taint th bits = {} /\
    eval_operand bits t = SOME (n2w (8*(32-n))) /\
    ghost_inv d cenv cx es H th (t with vs_inst_idx := s.vs_inst_idx+6) /\
    ghost_kept cenv es0 s0a G0 tn0 s0 H th /\
    (t with vs_inst_idx := s.vs_inst_idx+6) =
      s with <|vs_vars := t.vs_vars; vs_inst_idx := s.vs_inst_idx+6|> /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint th (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all unsigned_loader_counted_frame >>
  disch_then (qspecl_then [`PG`,`D`]
    (qx_choose_then `H` (qx_choose_then `th` strip_assume_tac))) >>
  `ghost_inv d cenv cx es H th (t with vs_inst_idx := s.vs_inst_idx+6)` by
    (irule ghost_inv_readonly_frame >>
     qexistsl_tac [`G`,`not_fresh_at sa`,`s`,`tn`] >>
     simp[lookup_var_def] >> metis_tac[lookup_var_def]) >>
  `ghost_kept cenv es0 s0a G0 tn0 s0 H th` by
    (irule ghost_kept_readonly_frame >>
     qexistsl_tac [`G`,`not_fresh_at sa`,`tn`] >> simp[] >>
     fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  qexistsl_tac [`H`,`th`] >> simp[] >>
  qpat_x_assum `t = s with vs_vars := _` (fn eq => once_rewrite_tac[eq]) >> simp[]
QED
