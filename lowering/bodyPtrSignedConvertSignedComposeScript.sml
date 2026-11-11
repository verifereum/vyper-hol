(* Compose the header, selector, and arithmetic normalization boundaries. *)
Theory bodyPtrSignedConvertSignedCompose
Ancestors bodyPtrBopHashSuffix
  bodyPtrSignedConvertSignedLoad bodyPtrSignedConvertSignedFixed bodyPtrSignedConvertUnsignedCompose
  bodyPtrSignedConvertSourceFixed instSeqComposePtr fragGasSeqPtr
  exprLoweringProps fragExec ghostPcTransportPtr bodyPtrSignedConvertSourceFrame
  emitHelperProps venomState venomInst
  venomExecSemantics ptrDiscipline bodyPtrDefs finite_map words arithmetic
  list rich_list compileEnv loweringStateRelDefs pred_set exprLowering bodyPtrSignedConvertClamp
  exprSimConvertFromBytes exprSimHyps exprSimHypsDefs loweringPosts
  memoryLocalRhsProps vyperAST bodyPtrSignedConvertConvertEntry
  bodyPtrSignedConvertUnsignedValue exprSimHash exprSimHashBoundary valueEncoding
  bodyPtrSignedConvertUintContinue gasSummaryComposePtr gasOutcome
  fragGasPathPtr fragGasMode stmtAppendStoragePathPtr bodyPtrHashBuiltinsShaAlloc
  exprSimExtract32Post varsExt appendStorageStageTransportPtr

Theorem signed_payload_padding[local]:
  (!x. a <= x /\ x < a+n ==> x NOTIN M) ==>
  !i. i IN mem_word_taint M a ==> n <= i /\ i < 32
Proof
  simp[mem_word_taint_def] >> rpt strip_tac >>
  spose_not_then strip_assume_tac >>
  `a <= a+i /\ a+i < a+n` by decide_tac >> metis_tac[]
QED

Theorem signed_loader_fixed_frame_raw:
  ALL_DISTINCT [src;len;dp;data;empty;nonempty;selected;sub;bits;dst] /\
  ~ctx_has_dalloca ctx /\
  lookup_var src s = SOME a /\ ptr_covers G tn src s capacity /\ 64 <= capacity /\
  w2n a+32 < dimword(:256) /\ mload (w2n a) s = n2w n /\ n <= 32 /\
  (!x. w2n a <= x /\ x < w2n a+32+n ==> x NOTIN tn.t_mem) /\
  run_inst_seq [mk_inst i MLOAD [Var src] [len];
    mk_inst j ADD [Var src;Lit 32w] [dp];
    mk_inst k MLOAD [Var dp] [data];
    mk_inst l ISZERO [Var len] [empty];
    mk_inst m ISZERO [Var empty] [nonempty];
    mk_inst r MUL [Var data;Var nonempty] [selected];
    mk_inst u SUB [Lit 32w;Var len] [sub];
    mk_inst v MUL [Var sub;Lit 8w] [bits];
    mk_inst w SAR [Var bits;Var selected] [dst]] s = OK t ==>
  ?H th.
    (!q. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst i MLOAD [Var src] [len];
       mk_inst j ADD [Var src;Lit 32w] [dp];
       mk_inst k MLOAD [Var dp] [data];
       mk_inst l ISZERO [Var len] [empty];
       mk_inst m ISZERO [Var empty] [nonempty];
       mk_inst r MUL [Var data;Var nonempty] [selected];
       mk_inst u SUB [Lit 32w;Var len] [sub];
       mk_inst v MUL [Var sub;Lit 8w] [bits];
       mk_inst w SAR [Var bits;Var selected] [dst]] (s with vs_inst_idx := q) H th) /\
    op_prov H (Var dst) = NONE /\ op_taint th (Var dst) = {} /\
    op_prov H (Var bits) = NONE /\ op_taint th (Var bits) = {} /\
    eval_operand (Var bits) t = SOME (n2w (8*(32-n))) /\
    t.vs_memory = s.vs_memory /\ th.t_mem = tn.t_mem /\
    th.t_stor = tn.t_stor /\ th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_current_bb = s.vs_current_bb /\
    t = s with vs_vars := t.vs_vars /\
    (!p. ~MEM p [len;dp;data;empty;nonempty;selected;sub;bits;dst] ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  drule (SRULE [APPEND] (Q.INST [`is1` |->
    `[mk_inst i MLOAD [Var src] [len]; mk_inst j ADD [Var src;Lit 32w] [dp]]`,
    `is2` |-> `[mk_inst k MLOAD [Var dp] [data];
      mk_inst l ISZERO [Var len] [empty]; mk_inst m ISZERO [Var empty] [nonempty];
      mk_inst r MUL [Var data;Var nonempty] [selected];
      mk_inst u SUB [Lit 32w;Var len] [sub]; mk_inst v MUL [Var sub;Lit 8w] [bits];
      mk_inst w SAR [Var bits;Var selected] [dst]]`] (iffLR bodyPtrBopHashSuffixTheory.bop_run_inst_seq_append_ok))) >>
  disch_then (qx_choose_then `s1` strip_assume_tac) >>
  drule (SRULE [APPEND] (Q.INST [`is1` |->
    `[mk_inst k MLOAD [Var dp] [data];
      mk_inst l ISZERO [Var len] [empty]; mk_inst m ISZERO [Var empty] [nonempty];
      mk_inst r MUL [Var data;Var nonempty] [selected]]`,
    `is2` |-> `[mk_inst u SUB [Lit 32w;Var len] [sub];
      mk_inst v MUL [Var sub;Lit 8w] [bits];
      mk_inst w SAR [Var bits;Var selected] [dst]]`] (iffLR bodyPtrBopHashSuffixTheory.bop_run_inst_seq_append_ok))) >>
  disch_then (qx_choose_then `s2` strip_assume_tac) >>
  `32 <= capacity /\ ALL_DISTINCT [src;len;dp] /\
   (!x. w2n a <= x /\ x < w2n a+32 ==> x NOTIN tn.t_mem)` by
    (fs[] >> rpt strip_tac >>
     qpat_x_assum `!x. _ ==> x NOTIN tn.t_mem` irule >> decide_tac) >>
  drule_all bytestring_source_fixed_frame >>
  disch_then (qspecl_then [`D`,`fn`,`PG`]
    (qx_choose_then `G1` (qx_choose_then `tn1` strip_assume_tac))) >>
  `ptr_covers G1 tn1 dp s1 32 /\
   ALL_DISTINCT [len;dp;data;empty;nonempty;selected] /\
   lookup_var len s1 = SOME (n2w n)` by
    (rpt conj_tac >- (first_x_assum irule >> decide_tac) >> fs[]) >>
  drule_all signed_select_fixed_frame >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `G2` (qx_choose_then `tn2` strip_assume_tac))) >>
  `w2n (a+32w) = w2n a+32` by
    (simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  `!x. w2n (a+32w) <= x /\ x < w2n (a+32w)+n ==> x NOTIN tn1.t_mem` by
    (simp[] >> rpt strip_tac >>
     qpat_x_assum `!x. _ /\ x < w2n a+32+n ==> _` irule >> decide_tac) >>
  `!z. z IN mem_word_taint tn1.t_mem (w2n (a+32w)) ==> n <= z /\ z < 32` by
    (match_mp_tac signed_payload_padding >> simp[]) >>
  `ALL_DISTINCT [len;selected;sub;bits;dst] /\
   lookup_var len s2 = SOME (n2w n) /\ op_prov G2 (Var len) = NONE /\
   op_taint tn2 (Var len) = {} /\
   (n = 0 ==> op_taint tn2 (Var selected) = {}) /\
   (!z. z IN op_taint tn2 (Var selected) ==> n <= z /\ z < 32)` by
    (fs[op_prov_def] >> Cases_on `n = 0` >> gvs[]) >>
  drule_all signed_normalize_fixed_frame >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `H` (qx_choose_then `th` strip_assume_tac))) >>
  `!q. inst_seq_ptr D 0 ctx fn PG G1 tn1
    [mk_inst k MLOAD [Var dp] [data];
     mk_inst l ISZERO [Var len] [empty]; mk_inst m ISZERO [Var empty] [nonempty];
     mk_inst r MUL [Var data;Var nonempty] [selected];
     mk_inst u SUB [Lit 32w;Var len] [sub]; mk_inst v MUL [Var sub;Lit 8w] [bits];
     mk_inst w SAR [Var bits;Var selected] [dst]] (s1 with vs_inst_idx := q) H th` by
    (irule (SRULE [APPEND] (Q.INST [`xs` |->
      `[mk_inst k MLOAD [Var dp] [data];
        mk_inst l ISZERO [Var len] [empty]; mk_inst m ISZERO [Var empty] [nonempty];
        mk_inst r MUL [Var data;Var nonempty] [selected]]`] inst_seq_ptr_uniform_append)) >>
     simp[is_terminator_def] >> qexistsl_tac [`G2`,`tn2`] >> simp[]) >>
  qexistsl_tac [`H`,`th`] >> conj_tac
  >- (irule (SRULE [APPEND] (Q.INST [`xs` |->
        `[mk_inst i MLOAD [Var src] [len]; mk_inst j ADD [Var src;Lit 32w] [dp]]`]
        inst_seq_ptr_uniform_append)) >>
      simp[is_terminator_def] >> qexistsl_tac [`G1`,`tn1`] >> simp[]) >>
  simp[] >>
  qpat_x_assum `t = s2 with vs_vars := _` (fn eq => once_rewrite_tac[eq]) >>
  qpat_x_assum `s2 = s1 with vs_vars := _` (fn eq => once_rewrite_tac[eq]) >>
  qpat_x_assum `s1 = s with vs_vars := _` (fn eq => once_rewrite_tac[eq]) >> simp[]
QED

Theorem signed_loader_fixed_frame:
  load_bytestring_as_word (Var src) SAR sa = ((out,bits),sb) /\
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
  strip_tac >> drule_all signed_loader_shape_fresh >> strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >> simp[] >> strip_tac >>
  drule_all signed_loader_fixed_frame_raw >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `H` (qx_choose_then `th` strip_assume_tac))) >>
  qexistsl_tac [`H`,`th`] >> simp[] >> metis_tac[]
QED

Theorem signed_loader_counted_frame:
  load_bytestring_as_word (Var src) SAR sa = ((out,bits),sb) /\
  not_fresh_at sa src /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  lookup_var src s = SOME a /\ ptr_covers G tn src s capacity /\ 64 <= capacity /\
  w2n a+32 < dimword(:256) /\ mload (w2n a) s = n2w n /\ n <= 32 /\
  (!x. w2n a <= x /\ x < w2n a+32+n ==> x NOTIN tn.t_mem) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H th.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th
      (OK (t with vs_inst_idx := s.vs_inst_idx+9)) /\
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
  strip_tac >> drule_all signed_loader_fixed_frame >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `H` (qx_choose_then `th` strip_assume_tac))) >>
  drule_all signed_loader_shape_fresh >> strip_tac >>
  `inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th` by
    (first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)` by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >> strip_tac >>
  qexistsl_tac [`H`,`th`] >> simp[] >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[mk_inst_def, arithmeticTheory.ADD_COMM]
QED

Theorem signed_loader_counted_ghost_frame:
  load_bytestring_as_word (Var src) SAR sa = ((out,bits),sb) /\
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
      (OK (t with vs_inst_idx := s.vs_inst_idx+9)) /\
    op_prov H out = NONE /\ op_taint th out = {} /\
    op_prov H bits = NONE /\ op_taint th bits = {} /\
    eval_operand bits t = SOME (n2w (8*(32-n))) /\
    ghost_inv d cenv cx es H th (t with vs_inst_idx := s.vs_inst_idx+9) /\
    ghost_kept cenv es0 s0a G0 tn0 s0 H th /\
    (t with vs_inst_idx := s.vs_inst_idx+9) =
      s with <|vs_vars := t.vs_vars; vs_inst_idx := s.vs_inst_idx+9|> /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint th (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all signed_loader_counted_frame >>
  disch_then (qspecl_then [`PG`,`D`]
    (qx_choose_then `H` (qx_choose_then `th` strip_assume_tac))) >>
  `ghost_inv d cenv cx es H th (t with vs_inst_idx := s.vs_inst_idx+9)` by
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

(* The signed integer continuation has one loader followed by an optional clamp. *)
Theorem signed_convert_loader_suffix:
  compile_type_convert x (ConvBytestringToInt T b n) sa = (out,sb) ==>
  ?word bits sm.
    load_bytestring_as_word x SAR sa = ((word,bits),sm) /\
    (if b < n*8 then compile_int_clamp T b word sm = (out,sb)
     else out = word /\ sb = sm)
Proof
  simp[compile_type_convert_def, LET_THM, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> Cases_on `a` >> simp[comp_return_def] >>
  Cases_on `b < 8*n` >> simp[comp_return_def]
QED

Theorem decimal_convert_loader_suffix:
  compile_type_convert x (ConvBytestringToDecimal divisor lo hi n) sa = (out,sb) ==>
  ?word bits sm.
    load_bytestring_as_word x SAR sa = ((word,bits),sm) /\ out = word /\
    (if n*8 <= 168 then sb = sm else
     ?a b c d e.
       emitted_insts sm sb =
        [mk_inst sm.cs_next_id SLT [word; Lit (i2w lo)] [a];
         mk_inst (sm.cs_next_id+1) ISZERO [Var a] [b];
         mk_inst (sm.cs_next_id+2) SGT [word; Lit (i2w hi)] [c];
         mk_inst (sm.cs_next_id+3) ISZERO [Var c] [d];
         mk_inst (sm.cs_next_id+4) AND [Var b; Var d] [e];
         mk_inst (sm.cs_next_id+5) ASSERT [Var e] []] /\
       ALL_DISTINCT [a;b;c;d;e] /\
       (!p. not_fresh_at sm p ==> ~MEM p [a;b;c;d;e]) /\
       sb.cs_next_var = sm.cs_next_var+5 /\
       sb.cs_current_bb = sm.cs_current_bb /\
       LENGTH sb.cs_current_insts = LENGTH sm.cs_current_insts+6)
Proof
  simp[compile_type_convert_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> Cases_on `a` >> simp[] >>
  Cases_on `n*8 <= 168`
  >- simp[comp_return_def] >>
  simp[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[comp_ignore_bind_def, comp_bind_def, comp_return_def]) >>
  strip_tac >> gvs[] >>
  imp_res_tac emitted_insts_emit_op >>
  imp_res_tac emitted_insts_emit_void >> gvs[] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  gvs[same_blocks_def, not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  qexistsl_tac [`STRING #"%" (toString cs'.cs_next_var)`,
    `STRING #"%" (toString (cs'.cs_next_var+1))`,
    `STRING #"%" (toString (cs'.cs_next_var+2))`,
    `STRING #"%" (toString (cs'.cs_next_var+3))`,
    `STRING #"%" (toString (cs'.cs_next_var+4))`] >>
  simp[ASCIInumbersTheory.toString_inj]
QED

Theorem signed_loader_exec_counted_ghost_frame:
  load_bytestring_as_word (Var src) SAR sa = ((out,bits),sb) /\
  fresh_vars_wrt sa s /\
  not_fresh_at sa src /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  lookup_var src s = SOME a /\ ptr_covers G tn src s capacity /\ 64 <= capacity /\
  w2n a+32 < dimword(:256) /\ mload (w2n a) s = n2w n /\ n <= 32 /\
  (!x. w2n a <= x /\ x < w2n a+32+n ==> x NOTIN tn.t_mem) /\
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es0 s0a G0 tn0 s0 G tn /\
  s0a.cs_next_var <= sa.cs_next_var /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) ==>
  ?t H th.
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand out t = SOME
      (word_asr (if (n2w n : 256 word) = 0w then 0w else mload (w2n (a+32w)) s)
         (w2n (((32w - n2w n) * 8w) : 256 word))) /\
    fresh_vars_wrt sb t /\ t.vs_memory = s.vs_memory /\
    t.vs_allocas = s.vs_allocas /\
    (!p w. eval_operand p s = SOME w ==> eval_operand p t = SOME w) /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th
      (OK (t with vs_inst_idx := s.vs_inst_idx+9)) /\
    op_prov H out = NONE /\ op_taint th out = {} /\
    op_prov H bits = NONE /\ op_taint th bits = {} /\
    eval_operand bits t = SOME (n2w (8*(32-n))) /\
    ghost_inv d cenv cx es H th (t with vs_inst_idx := s.vs_inst_idx+9) /\
    ghost_kept cenv es0 s0a G0 tn0 s0 H th /\
    (t with vs_inst_idx := s.vs_inst_idx+9) =
      s with <|vs_vars := t.vs_vars; vs_inst_idx := s.vs_inst_idx+9|> /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint th (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `eval_operand (Var src) s = SOME a` by simp[eval_operand_def] >>
  drule dynamic_load_word_raw_exact >>
  disch_then (qspecl_then [`s`,`n2w n`,`mload (w2n (a+32w)) s`,`a`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule_all signed_loader_counted_ghost_frame >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`sf`,`H`,`th`] >> simp[]
QED

(* The semantic continuation uses the annotated type, not the allocation type. *)
Theorem signed_convert_child_memory:
  expr_body_pre cenv cx env e es /\ is_bytestring_type (expr_type e) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  expr_post ctx fn cenv cx e es s0a sa s0 ee v op s ==>
  ?tv a. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    value_has_type tv v /\ eval_operand op s = SOME a /\
    val_in_memory tv v (w2n a) s.vs_memory
Proof
  strip_tac >> drule_all memory_rhs_read_annotation_typed >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule_all memory_rhs_runtime_layout >> strip_tac >>
  `~is_word_type (expr_type e)` by
    (Cases_on `expr_type e` >> gvs[is_bytestring_type_def] >>
     rename1 `is_bytestring_type (BaseT bt)` >> Cases_on `bt` >>
     gvs[is_bytestring_type_def, is_word_type_def] >>
     rename1 `is_bytestring_type (BaseT (BytesT bd))` >> Cases_on `bd` >>
     gvs[is_bytestring_type_def, is_word_type_def]) >>
  gvs[expr_post_def, expr_val_rel_def] >> metis_tac[]
QED

Theorem signed_convert_run_from_child:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert typ [e]) es /\
  body_expr_ptr_ok cx e /\ is_bytestring_type (expr_type e) /\
  ((?b. typ = BaseT (IntT b)) \/ typ = BaseT DecimalT) /\
  (do z <- eval_expr cx e; read_result cx z od) es = (INL v,ee) /\
  expr_post ctx fn cenv cx e es s0a sa s0 ee v op s /\
  compile_type_convert op (mk_convert_op (expr_type e) typ) sa = (out,sb) /\
  fresh_vars_wrt sa s /\ eval_operand op s = SOME a /\
  w2n a+32 < dimword(:256) ==>
  case convert_result cx (expr_type e) typ v of
  | INL vout => ?dtv t. evaluate_type (get_tenv cx) typ = SOME dtv /\
      run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand out t = SOME (typed_val_to_w256 dtv vout) /\
      fresh_vars_wrt sb t /\ t.vs_memory = s.vs_memory /\
      t.vs_allocas = s.vs_allocas /\
      (!p w. eval_operand p s = SOME w ==> eval_operand p t = SOME w)
  | INR ex => (?m. ex = Error (RuntimeError m)) /\
      ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
Proof
  strip_tac >> (
  `expr_body_pre cenv cx env e es /\
   valid_conversion (expr_type e) typ /\ well_formed_type env.type_defs typ` by
    metis_tac[signed_convert_body_entry] >>
  drule_all signed_convert_child_memory >> strip_tac >>
  `~is_bytestring_type typ` by gvs[is_bytestring_type_def] >>
  `val_in_memory tv v (w2n a) s.vs_memory` by gvs[] >>
  drule_at (Pat `compile_type_convert _ _ _ = _`) dynamic_scalar_run_exact >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  disch_then (drule_at (Pat `well_formed_type _ _`)) >>
  disch_then (qspecl_then [`convert_result cx (expr_type e) typ v`,`cx`] mp_tac) >>
  simp[] >> gvs[])
QED

(* Child postconditions supply the actual address, not just a buffer size. *)
Theorem signed_convert_bytes_loader_inputs:
  expr_post ctx fn cenv cx e es s0a sa s0 ee (BytesV bs) op s /\
  expr_type e = BaseT (BytesT (Dynamic cap)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic cap))) /\
  ptr_val_ok cx (expr_type e) (BytesV bs) op G tn s /\
  ptr_buf_ok cenv e op G s /\
  64 <= type_memory_bytes cenv (lowered_value_type cenv e) ==>
  ?src a.
    op = Var src /\ lookup_var src s = SOME a /\
    ptr_covers G tn src s (type_memory_bytes cenv (lowered_value_type cenv e)) /\
    w2n a+32 < dimword(:256) /\
    mload (w2n a) s = n2w (LENGTH bs) /\
    (!x. w2n a <= x /\ x < w2n a+32+LENGTH bs ==> x NOTIN tn.t_mem)
Proof
  strip_tac >>
  `evaluate_type (get_tenv cx) (expr_type e) =
     SOME (BaseTV (BytesT (Dynamic cap))) /\ ~is_word_type (expr_type e)` by
    simp[vyperValueTheory.evaluate_type_def, is_word_type_def] >>
  `?a. eval_operand op s = SOME a` by
    gvs[expr_post_def, expr_val_rel_def] >>
  `?src. op = Var src` by
    (gvs[ptr_buf_ok_def] >> first_x_assum drule >> simp[] >> metis_tac[]) >>
  gvs[] >>
  `lookup_var src s = SOME a` by fs[eval_operand_def] >>
  `ptr_mem_ok cx (expr_type e) (BytesV bs) (Var src) G tn s /\
   op_taint tn (Var src) = {}` by fs[ptr_val_ok_def] >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic cap))) /\
   ~is_word_type (expr_type e)` by simp[] >>
  `post_value_type cenv e = expr_type e` by
    simp[post_value_type_bytestring, is_bytestring_type_def] >>
  drule_all hash_post_footprint_bound >>
  simp[val_footprint_def] >> strip_tac >>
  drule_at (Pat `ptr_mem_ok _ _ _ _ _ _ _`) unsigned_bytes_value_source_facts >>
  disch_then (qspecl_then [`BaseTV (BytesT (Dynamic cap))`,`cenv`,`a`] mp_tac) >>
  simp[] >> strip_tac >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED


Theorem signed_clamp_counted_ghost_frame:
  compile_int_clamp T bits x sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es0 s0a G0 tn0 s0 G tn /\
  s0a.cs_next_var <= sa.cs_next_var /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) ==>
  ?H th.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
    out = x /\ op_prov H out = NONE /\ op_taint th out = {} /\
    ghost_inv d cenv cx es H th
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)) /\
    ghost_kept cenv es0 s0a G0 tn0 s0 H th /\
    (t with vs_vars := s.vs_vars) = s /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint th (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all int_clamp_counted_certificate >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  drule_all int_clamp_runtime_frame >> strip_tac >>
  `t = s with vs_vars := t.vs_vars` by
    (qpat_x_assum `(t with vs_vars := _) = s` (fn eq => once_rewrite_tac[GSYM eq]) >> simp[]) >>
  `t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient /\ t.vs_memory = s.vs_memory` by
    (qpat_x_assum `t = s with vs_vars := _` (fn eq => once_rewrite_tac[eq]) >> simp[]) >>
  `ghost_inv d cenv cx es H th
    (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))` by
    (irule ghost_inv_readonly_frame >>
     qexistsl_tac [`G`,`not_fresh_at sa`,`s`,`tn`] >>
     simp[lookup_var_def] >> metis_tac[lookup_var_def]) >>
  `ghost_kept cenv es0 s0a G0 tn0 s0 H th` by
    (irule ghost_kept_readonly_frame >>
     qexistsl_tac [`G`,`not_fresh_at sa`,`tn`] >> simp[] >>
     fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  qexistsl_tac [`H`,`th`] >> simp[]
QED

Theorem decimal_convert_suffix_fixed_certificate:
  compile_type_convert x (ConvBytestringToDecimal divisor lo hi n) sa = (out,sb) /\
  load_bytestring_as_word x SAR sa = ((word,bits),sm) /\ 168 < n*8 /\
  op_prov G word = NONE /\ op_taint tn word = {} /\ ~ctx_has_dalloca ctx /\
  (run_inst_seq (emitted_insts sm sb) s = OK t \/
   run_inst_seq (emitted_insts sm sb) s = Abort err t) ==>
  ?H th.
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sm sb) s H th /\
    out = word /\ op_prov H out = NONE /\ op_taint th out = {} /\
    (!p. not_fresh_at sm p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule decimal_convert_loader_suffix >> strip_tac >> gnvs[] >>
  qpat_x_assum `?a b c d e. _` strip_assume_tac >> gnvs[] >>
  drule_all (SIMP_RULE (srw_ss()) [] (Q.INST
    [`opc1` |-> `SLT`, `opc2` |-> `SGT`] (SPEC_ALL scalar_double_check_certificate))) >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`H`,`th`] >> simp[] >> metis_tac[]
QED

Theorem signed_convert_child_loader_inputs:
  expr_body_pre cenv cx env e es /\ is_bytestring_type (expr_type e) /\
  valid_conversion (expr_type e) typ /\
  ((?b. typ = BaseT (IntT b)) \/ typ = BaseT DecimalT) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  expr_post ctx fn cenv cx e es s0a sa s0 ee v op s /\
  ptr_val_ok cx (expr_type e) v op G tn s /\ ptr_buf_ok cenv e op G s /\
  64 <= type_memory_bytes cenv (lowered_value_type cenv e) ==>
  ?src a n.
    op = Var src /\ lookup_var src s = SOME a /\ n <= 32 /\
    ptr_covers G tn src s (type_memory_bytes cenv (lowered_value_type cenv e)) /\
    w2n a+32 < dimword(:256) /\ mload (w2n a) s = n2w n /\
    (!x. w2n a <= x /\ x < w2n a+32+n ==> x NOTIN tn.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?cap bs. expr_type e = BaseT (BytesT (Dynamic cap)) /\
    v = BytesV bs /\ LENGTH bs <= 32` by
    (drule_all bodyPtrSignedConvertSourceTypingTheory.source_read_bytestring_view >> strip_tac >>
     qpat_x_assum `(?b. typ = _) \/ _` strip_assume_tac >>
     gvs[vyperTypeSystemTheory.valid_conversion_def] >> decide_tac) >>
  gvs[] >>
  `is_bytestring_type (expr_type e)` by simp[is_bytestring_type_def] >>
  drule_all signed_convert_child_memory >> strip_tac >>
  `evaluate_type (get_tenv cx) (expr_type e) =
    SOME (BaseTV (BytesT (Dynamic cap)))` by
    (gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()]) >>
  `ptr_val_ok cx (expr_type e) (BytesV bs) op G tn s` by simp[] >>
  drule_all signed_convert_bytes_loader_inputs >> strip_tac >>
  gvs[eval_operand_def] >> qexists_tac `LENGTH bs` >>
  simp[dimword_def] >> decide_tac
QED

(* The signed loader consumes exactly the normal child interface. *)
Theorem signed_convert_child_loader_frame:
  expr_body_pre cenv cx env e es /\ is_bytestring_type (expr_type e) /\
  valid_conversion (expr_type e) typ /\
  ((?b. typ = BaseT (IntT b)) \/ typ = BaseT DecimalT) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  expr_post ctx fn cenv cx e es s0a sa s0 ee v op s /\
  ptr_val_ok cx (expr_type e) v op G tn s /\ ptr_buf_ok cenv e op G s /\
  64 <= type_memory_bytes cenv (lowered_value_type cenv e) /\
  load_bytestring_as_word op SAR sa = ((word,bits),sm) /\
  fresh_vars_wrt sa s /\ (!p. op = Var p ==> not_fresh_at sa p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ghost_inv d cenv cx ee G tn s /\ ghost_kept cenv es s0a G0 tn0 s0 G tn /\
  s0a.cs_next_var <= sa.cs_next_var /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) ==>
  ?t H th.
    run_inst_seq (emitted_insts sa sm) s = OK t /\ fresh_vars_wrt sm t /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th
      (OK (t with vs_inst_idx := s.vs_inst_idx+9)) /\
    op_prov H word = NONE /\ op_taint th word = {} /\
    op_prov H bits = NONE /\ op_taint th bits = {} /\
    ghost_inv d cenv cx ee H th (t with vs_inst_idx := s.vs_inst_idx+9) /\
    ghost_kept cenv es s0a G0 tn0 s0 H th /\
    (t with vs_inst_idx := s.vs_inst_idx+9) =
      s with <|vs_vars := t.vs_vars; vs_inst_idx := s.vs_inst_idx+9|> /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    (!p w. eval_operand p s = SOME w ==> eval_operand p t = SOME w) /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint th (Var p) = op_taint tn (Var p))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all signed_convert_child_loader_inputs >> strip_tac >>
  `not_fresh_at sa src` by metis_tac[] >>
  qpat_x_assum `op = Var src` SUBST_ALL_TAC >>
  drule_all signed_loader_exec_counted_ghost_frame >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`t`,`H`,`th`] >> simp[]
QED

(* Reconstruct the parent post once, after a clean readonly scalar path. *)
Theorem signed_scalar_path_summary:
  expr_post ctx fn cenv cx e es s0a sa s0 (ee with gas_obs := []) v op s /\
  convert_result cx (expr_type e) typ v = INL result /\
  is_word_type typ /\ evaluate_type (get_tenv cx) typ = SOME tv /\
  eval_operand out t = SOME (typed_val_to_w256 tv result) /\
  gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 H th (OK t) /\
  op_prov H out = NONE /\ op_taint th out = {} /\
  ghost_inv d cenv cx (ee with gas_obs := []) H th t /\
  ghost_kept cenv es s0a G0 tn0 s0 H th /\
  local_ptrs_reserved cenv sa /\ s0a.cs_next_var <= sa.cs_next_var /\
  t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
  (!p w. not_fresh_at sa p /\ lookup_var p s = SOME w ==> lookup_var p t = SOME w) /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  gas_summary_ptr_at (cx_dead cx) (ctx,fn) PG []
    (\vs. (convert_result cx (expr_type e) typ v,vs))
    (ee with gas_obs := [],s,G,tn)
    (\res fin K tk ss. ?vout. res = INL vout /\
      expr_post ctx fn cenv cx (TypeBuiltin typ Convert typ [e])
        es s0a sb s0 fin vout out ss /\
      ss.vs_current_bb = sb.cs_current_bb /\
      ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin K tk ss /\
      ptr_val_ok cx typ vout out K tk ss /\
      ghost_kept cenv es s0a G0 tn0 s0 K tk)
    (\res fin gt r. expr_exit res r)
Proof
  strip_tac >>
  `stmt_state_rel ctx fn cenv cx (ee with gas_obs := []) s` by
    fs[expr_post_def] >>
  `stmt_state_rel ctx fn cenv cx (ee with gas_obs := []) t` by
    (irule stmt_state_rel_readonly_vars_pc >> qexistsl_tac [`s`,`sa`] >> simp[]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory` by
    (qpat_x_assum `t = s with <|vs_vars := _; vs_inst_idx := _|>`
      (fn eq => once_rewrite_tac[eq]) >> simp[]) >>
  `expr_post ctx fn cenv cx (TypeBuiltin typ Convert typ [e])
     es s0a sb s0 (ee with gas_obs := []) result out t` by
    (irule scalar_suffix_expr_post >> simp[expr_type_def] >> metis_tac[]) >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL result`,`ee with gas_obs := []`,`H`,`th`,`OK t`] >>
  simp[ptr_val_ok_def]
QED

(* The no-check nonzero branch: semantic and pointer executions are the same loader. *)
Theorem signed_loader_only_continuation:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TypeBuiltin typ Convert typ [e]) es /\
  body_expr_ptr_ok cx e /\ is_bytestring_type (expr_type e) /\
  ((?b. typ = BaseT (IntT b)) \/ typ = BaseT DecimalT) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  expr_post ctx fn cenv cx e es s0a sa s0 ee v op s /\
  ptr_val_ok cx (expr_type e) v op G tn s /\ ptr_buf_ok cenv e op G s /\
  64 <= type_memory_bytes cenv (lowered_value_type cenv e) /\
  compile_type_convert op (mk_convert_op (expr_type e) typ) sa = (out,sb) /\
  load_bytestring_as_word op SAR sa = ((out,bits),sb) /\
  fresh_vars_wrt sa s /\ (!p. op = Var p ==> not_fresh_at sa p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ghost_inv d cenv cx ee G tn s /\ ghost_kept cenv es s0a G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sa /\ s0a.cs_next_var <= sa.cs_next_var /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx+9 = LENGTH sb.cs_current_insts ==>
  gas_summary_ptr_at (cx_dead cx) (ctx,fn) PG []
    (\vs. (convert_result cx (expr_type e) typ v,vs))
    (ee with gas_obs := [],s,G,tn)
    (\res fin K tk ss. ?vout. res = INL vout /\
      expr_post ctx fn cenv cx (TypeBuiltin typ Convert typ [e])
        es s0a sb s0 fin vout out ss /\
      ss.vs_current_bb = sb.cs_current_bb /\
      ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin K tk ss /\
      ptr_val_ok cx typ vout out K tk ss /\
      ghost_kept cenv es s0a G0 tn0 s0 K tk)
    (\res fin gt r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre cenv cx env e es /\ valid_conversion (expr_type e) typ` by
    metis_tac[signed_convert_body_entry] >>
  drule_all signed_convert_child_loader_inputs >> strip_tac >>
  `eval_operand op s = SOME a` by gvs[eval_operand_def] >>
  drule_all signed_convert_run_from_child >>
  disch_tac >>
  drule_all signed_convert_child_loader_frame >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`] strip_assume_tac) >>
  `?tv result. convert_result cx (expr_type e) typ v = INL result /\
     evaluate_type (get_tenv cx) typ = SOME tv /\
     eval_operand out t = SOME (typed_val_to_w256 tv result)` by
    (Cases_on `convert_result cx (expr_type e) typ v` >> gvs[]) >>
  irule signed_scalar_path_summary >>
  conj_tac >- gvs[is_word_type_def] >>
  goal_assum (drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  qexistsl_tac [`op`,`result`,`sa`,`tv`] >>
  simp[] >>
  conj_tac
  >- (rpt strip_tac >> simp[lookup_var_def] >>
      first_x_assum drule >> simp[lookup_var_def]) >>
  conj_tac
  >- (qpat_x_assum `t with vs_inst_idx := _ = _` mp_tac >>
      simp[venom_state_component_equality]) >>
  conj_tac
  >- (gvs[stmtFragPtrTheory.ghost_inv_gas_obs]) >>
  gvs[expr_post_def, expr_val_at_def, stmt_state_rel_def,
      state_rel_gas_obs,
      loweringPostsTheory.locals_kept_def, loweringPostsTheory.popped_kept_def] >>
    metis_tac[]
QED

Theorem signed_zero_capacity_continuation:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TypeBuiltin typ Convert typ [e]) es /\
  body_expr_ptr_ok cx e /\ is_bytestring_type (expr_type e) /\
  ((?b. typ = BaseT (IntT b)) \/ typ = BaseT DecimalT) /\
  (lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
   lowered_value_type cenv e = BaseT (StringT 0)) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  expr_post ctx fn cenv cx e es s0a sa s0 (ee with gas_obs := []) v op s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ghost_inv d cenv cx (ee with gas_obs := []) G tn s /\
  ghost_kept cenv es s0a G0 tn0 s0 G tn ==>
  gas_summary_ptr_at (cx_dead cx) (ctx,fn) PG []
    (\vs. (convert_result cx (expr_type e) typ v,vs))
    (ee with gas_obs := [],s,G,tn)
    (\res fin K tk ss. ?vout. res = INL vout /\
      expr_post ctx fn cenv cx (TypeBuiltin typ Convert typ [e])
        es s0a sa s0 fin vout (Lit 0w) ss /\
      ss.vs_current_bb = sa.cs_current_bb /\
      ss.vs_inst_idx = LENGTH sa.cs_current_insts /\
      ghost_inv d cenv cx fin K tk ss /\
      ptr_val_ok cx typ vout (Lit 0w) K tk ss /\
      ghost_kept cenv es s0a G0 tn0 s0 K tk)
    (\res fin gt r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre cenv cx env e es /\ valid_conversion (expr_type e) typ /\
   well_formed_type env.type_defs typ` by metis_tac[signed_convert_body_entry] >>
  `v = BytesV [] \/ v = StringV []` by
    metis_tac[bodyPtrSignedConvertSourceTypingTheory.body_source_lowered_zero_empty] >>
  `?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v` by
    (drule_all memory_rhs_read_annotation_typed >> strip_tac >>
     `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
     drule_all memory_rhs_runtime_layout >> metis_tac[]) >>
  `is_word_type typ` by gvs[is_word_type_def] >>
  gvs[] >> irule zero_scalar_continuation >> simp[] >> metis_tac[]
QED

(* Failed scalar checks execute no GAS; retain the exact zero count. *)
Theorem signed_clamp_abort_zero_path:
  compile_int_clamp T bits x sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = Abort err t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?H th j. gas_path_ptr D 0 ctx fn PG G tn s 0 H th
    (Abort err (t with vs_inst_idx := j))
Proof
  strip_tac >>
  drule_all (cj 2 (PURE_REWRITE_RULE
    [RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, DISJ_IMP_THM] int_clamp_fixed_certificate)) >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (drule int_clamp_signed_code >> strip_tac >>
     simp[mk_inst_def, is_terminator_def]) >>
  drule_all run_inst_seq_abort_zero_path_ptr >> strip_tac >>
  qexistsl_tac [`H`,`th`,`j`] >> simp[]
QED

Theorem decimal_convert_suffix_runtime_frame:
  compile_type_convert x (ConvBytestringToDecimal divisor lo hi n) sa = (out,sb) /\
  load_bytestring_as_word x SAR sa = ((word,bits),sm) /\ 168 < n*8 /\
  run_inst_seq (emitted_insts sm sb) s = OK t ==>
  (t with vs_vars := s.vs_vars) = s /\
  (!p. not_fresh_at sm p ==> lookup_var p t = lookup_var p s)
Proof
  strip_tac >> drule decimal_convert_loader_suffix >> strip_tac >> gnvs[] >>
  qpat_x_assum `?a b c d e. _` strip_assume_tac >> gnvs[] >>
  drule (SIMP_RULE (srw_ss()) [] (Q.INST
    [`opc1` |-> `SLT`, `opc2` |-> `SGT`] (SPEC_ALL scalar_double_check_runtime_frame))) >>
  strip_tac >> simp[] >> metis_tac[]
QED

Theorem decimal_suffix_counted_ghost_frame:
  compile_type_convert x (ConvBytestringToDecimal divisor lo hi n) sa = (out,sb) /\
  load_bytestring_as_word x SAR sa = ((word,bits),sm) /\ 168 < n*8 /\
  op_prov G word = NONE /\ op_taint tn word = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sm sb) s = OK t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es0 s0a G0 tn0 s0 G tn /\
  s0a.cs_next_var <= sm.cs_next_var /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) ==>
  ?H th.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb))) /\
    out = word /\ op_prov H out = NONE /\ op_taint th out = {} /\
    ghost_inv d cenv cx es H th
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb)) /\
    ghost_kept cenv es0 s0a G0 tn0 s0 H th /\
    (t with vs_vars := s.vs_vars) = s /\
    (!p. not_fresh_at sm p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint th (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  drule_all (cj 1 (PURE_REWRITE_RULE
    [RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, DISJ_IMP_THM] decimal_convert_suffix_fixed_certificate)) >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  drule_all decimal_convert_suffix_runtime_frame >> strip_tac >>
  `t = s with vs_vars := t.vs_vars` by
    (qpat_x_assum `(t with vs_vars := _) = s` (fn eq => once_rewrite_tac[GSYM eq]) >> simp[]) >>
  `t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient /\ t.vs_memory = s.vs_memory` by
    (qpat_x_assum `t = s with vs_vars := _` (fn eq => once_rewrite_tac[eq]) >> simp[]) >>
  `ghost_inv d cenv cx es H th
    (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb))` by
    (irule ghost_inv_readonly_frame >>
     qexistsl_tac [`G`,`not_fresh_at sm`,`s`,`tn`] >>
     simp[lookup_var_def] >> metis_tac[lookup_var_def]) >>
  `ghost_kept cenv es0 s0a G0 tn0 s0 H th` by
    (irule ghost_kept_readonly_frame >>
     qexistsl_tac [`G`,`not_fresh_at sm`,`tn`] >> simp[] >>
     fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  qexistsl_tac [`H`,`th`] >> simp[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sm sb) /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm sb) = []` by
    (drule decimal_convert_loader_suffix >> strip_tac >> gvs[] >>
     simp[mk_inst_def, is_terminator_def]) >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED

Theorem decimal_suffix_abort_zero_path:
  compile_type_convert x (ConvBytestringToDecimal divisor lo hi n) sa = (out,sb) /\
  load_bytestring_as_word x SAR sa = ((word,bits),sm) /\ 168 < n*8 /\
  op_prov G word = NONE /\ op_taint tn word = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sm sb) s = Abort err t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?H th j. gas_path_ptr D 0 ctx fn PG G tn s 0 H th
    (Abort err (t with vs_inst_idx := j))
Proof
  strip_tac >>
  drule_all (cj 2 (PURE_REWRITE_RULE
    [RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, DISJ_IMP_THM] decimal_convert_suffix_fixed_certificate)) >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
    (drule decimal_convert_loader_suffix >> strip_tac >> gvs[] >>
     simp[mk_inst_def, is_terminator_def]) >>
  drule_all run_inst_seq_abort_zero_path_ptr >> strip_tac >>
  qexistsl_tac [`H`,`th`,`j`] >> simp[]
QED

(* Layout facts needed to split the actual compiler fragment at the loader. *)
Theorem signed_loader_layout:
  load_bytestring_as_word x SAR sa = ((word,bits),sm) ==>
  sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
  sm.cs_current_bb = sa.cs_current_bb /\
  LENGTH sm.cs_current_insts = LENGTH sa.cs_current_insts+9 /\
  sa.cs_next_var <= sm.cs_next_var
Proof
  strip_tac >> drule signed_loader_decompose >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> gvs[] >>
  imp_res_tac emit_op_extends >>
  fs[same_blocks_def] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND]
QED

Theorem signed_clamp_block_layout[local]:
  compile_int_clamp T n word sm = (out,sb) ==>
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
  sb.cs_current_bb = sm.cs_current_bb
Proof
  simp[compile_int_clamp_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[comp_ignore_bind_def, comp_bind_def, comp_return_def]) >>
  strip_tac >> gvs[] >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >> gvs[] >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  fs[same_blocks_def] >> simp[emitted_insts_def, DROP_LENGTH_APPEND]
QED

Theorem signed_clamp_layout:
  compile_int_clamp T n word sm = (out,sb) ==>
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb
Proof
  metis_tac[signed_clamp_block_layout]
QED

Theorem decimal_checked_suffix_layout[local]:
  compile_type_convert op (ConvBytestringToDecimal divisor lo hi k) sa = (out,sb) /\
  load_bytestring_as_word op SAR sa = ((word,bits),sm) /\ 168 < k*8 ==>
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
  sb.cs_current_bb = sm.cs_current_bb
Proof
  simp[compile_type_convert_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[comp_ignore_bind_def, comp_bind_def, comp_return_def]) >>
  strip_tac >> gvs[] >>
  qpat_x_assum `do _ od _ = _` mp_tac >>
  simp[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[comp_ignore_bind_def, comp_bind_def, comp_return_def]) >>
  strip_tac >> gvs[] >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >> gvs[] >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  fs[same_blocks_def] >> simp[emitted_insts_def, DROP_LENGTH_APPEND]
QED

Theorem signed_checked_suffix_layout[local]:
  load_bytestring_as_word op SAR sa = ((word,bits),sm) /\
  ((?n. compile_int_clamp T n word sm = (out,sb)) \/
   (?divisor lo hi k. compile_type_convert op (ConvBytestringToDecimal divisor lo hi k) sa = (out,sb) /\ 168 < k*8)) ==>
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb
Proof
  strip_tac >- metis_tac[signed_clamp_layout] >>
  metis_tac[decimal_checked_suffix_layout]
QED

Theorem signed_checked_suffix_filter[local]:
  load_bytestring_as_word op SAR sa = ((word,bits),sm) /\
  ((?n. compile_int_clamp T n word sm = (out,sb)) \/
   (?divisor lo hi k. compile_type_convert op (ConvBytestringToDecimal divisor lo hi k) sa = (out,sb) /\ 168 < k*8)) ==>
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)
Proof
  strip_tac
  >- (drule int_clamp_instruction_filter >> simp[EVERY_MEM] >> metis_tac[]) >>
  drule decimal_convert_loader_suffix >> strip_tac >> gvs[] >>
  simp[mk_inst_def, is_terminator_def]
QED

(* The compiler/run cut is independent of conversion values and ghosts. *)
Theorem signed_suffix_entry:
  isPREFIX (pre ++ post) (DROP s.vs_inst_idx bb.bb_instructions) /\
  middle = u with vs_inst_idx := s.vs_inst_idx + LENGTH pre /\
  (u with vs_vars := s.vs_vars) = s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
  lookup_block middle.vs_current_bb fn.fn_blocks = SOME bb /\
  middle.vs_inst_idx = s.vs_inst_idx + LENGTH pre /\
  isPREFIX post (DROP middle.vs_inst_idx bb.bb_instructions)
Proof
  strip_tac >>
  `u.vs_current_bb = s.vs_current_bb` by
    (qpat_assum `(u with vs_vars := _) = s`
      (mp_tac o Q.AP_TERM `\vs. vs.vs_current_bb`) >> simp[]) >>
  drule hash_code_prefix_split >> strip_tac >> fs[ADD_COMM]
QED

Theorem signed_suffix_run_ok:
  EVERY (\i. ~is_terminator i.inst_opcode) post /\
  run_inst_seq pre s = OK u /\ run_inst_seq (pre ++ post) s = OK t /\
  middle = u with vs_inst_idx := j ==>
  run_inst_seq post middle = OK (t with vs_inst_idx := j)
Proof
  strip_tac >>
  qpat_assum `run_inst_seq pre s = OK u` (mp_tac o MATCH_MP run_inst_seq_append) >>
  disch_then (qspec_then `post` assume_tac) >>
  fs[run_inst_seq_inst_idx, instIdxIndepTheory.exec_result_map_def]
QED

Theorem signed_suffix_run_abort:
  EVERY (\i. ~is_terminator i.inst_opcode) post /\
  run_inst_seq pre s = OK u /\ run_inst_seq (pre ++ post) s = Abort err t /\
  middle = u with vs_inst_idx := j ==>
  run_inst_seq post middle = Abort err (t with vs_inst_idx := j)
Proof
  strip_tac >>
  qpat_assum `run_inst_seq pre s = OK u` (mp_tac o MATCH_MP run_inst_seq_append) >>
  disch_then (qspec_then `post` assume_tac) >>
  fs[run_inst_seq_inst_idx, instIdxIndepTheory.exec_result_map_def]
QED

Theorem signed_checked_suffix_runtime_frame[local]:
  load_bytestring_as_word op SAR sa = ((word,bits),sm) /\
  ((?n. compile_int_clamp T n word sm = (out,sb)) \/
   (?divisor lo hi k. compile_type_convert op (ConvBytestringToDecimal divisor lo hi k) sa = (out,sb) /\ 168 < k*8)) /\
  run_inst_seq (emitted_insts sm sb) s = OK t ==>
  (t with vs_vars := s.vs_vars) = s /\
  (!p. not_fresh_at sm p ==> lookup_var p t = lookup_var p s)
Proof
  strip_tac >- metis_tac[int_clamp_runtime_frame] >>
  metis_tac[decimal_convert_suffix_runtime_frame]
QED

(* Both checked suffixes expose the same pointer and readonly boundary. *)
Theorem signed_checked_suffix_frame[local]:
  load_bytestring_as_word op SAR sa = ((word,bits),sm) /\
  ((?n. compile_int_clamp T n word sm = (out,sb)) \/
   (?divisor lo hi k. compile_type_convert op (ConvBytestringToDecimal divisor lo hi k) sa = (out,sb) /\ 168 < k*8)) /\
  op_prov G word = NONE /\ op_taint tn word = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sm sb) s = OK t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es0 s0a G0 tn0 s0 G tn /\
  s0a.cs_next_var <= sm.cs_next_var /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) ==>
  ?H th.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb))) /\
    out = word /\ op_prov H out = NONE /\ op_taint th out = {} /\
    ghost_inv d cenv cx es H th
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb)) /\
    ghost_kept cenv es0 s0a G0 tn0 s0 H th /\
    (t with vs_vars := s.vs_vars) = s /\
    (!p. not_fresh_at sm p ==> lookup_var p t = lookup_var p s)
Proof
  strip_tac
  >- (drule_all signed_clamp_counted_ghost_frame >>
      disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
      qexistsl_tac [`H`,`th`] >> simp[] >> metis_tac[]) >>
  drule_all decimal_suffix_counted_ghost_frame >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`H`,`th`] >> simp[] >> metis_tac[]
QED

(* Compose a successful checked suffix with the very loader path used by the run. *)
Theorem signed_checked_suffix_path[local]:
  load_bytestring_as_word op SAR sa = ((word,bits),sm) /\
  ((?n. compile_int_clamp T n word sm = (out,sb)) \/
   (?divisor lo hi k. compile_type_convert op (ConvBytestringToDecimal divisor lo hi k) sa = (out,sb) /\ 168 < k*8)) /\
  run_inst_seq (emitted_insts sa sm) s = OK u /\
  run_inst_seq (emitted_insts sa sm ++ emitted_insts sm sb) s = OK t /\
  gas_path_ptr D 0 ctx fn PG G tn s 0 H th
    (OK (u with vs_inst_idx := s.vs_inst_idx+9)) /\
  (u with vs_inst_idx := s.vs_inst_idx+9) =
    s with <|vs_vars := u.vs_vars; vs_inst_idx := s.vs_inst_idx+9|> /\
  op_prov H word = NONE /\ op_taint th word = {} /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sm ++ emitted_insts sm sb)
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  ghost_inv d cenv cx ee H th (u with vs_inst_idx := s.vs_inst_idx+9) /\
  ghost_kept cenv es s0a G0 tn0 s0 H th /\
  s0a.cs_next_var <= sa.cs_next_var /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) ==>
  ?K tk.
    gas_path_ptr D 0 ctx fn PG G tn s 0 K tk
      (OK (t with vs_inst_idx := s.vs_inst_idx+9+LENGTH (emitted_insts sm sb))) /\
    out = word /\ op_prov K out = NONE /\ op_taint tk out = {} /\
    ghost_inv d cenv cx ee K tk
      (t with vs_inst_idx := s.vs_inst_idx+9+LENGTH (emitted_insts sm sb)) /\
    ghost_kept cenv es s0a G0 tn0 s0 K tk
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule signed_loader_layout >> strip_tac >>
  `LENGTH (emitted_insts sa sm) = 9` by
    (qpat_x_assum `LENGTH sm.cs_current_insts = _` mp_tac >> simp[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
    (drule_all signed_checked_suffix_filter >> simp[]) >>
  qabbrev_tac `mid = u with vs_inst_idx := s.vs_inst_idx+9` >>
  `lookup_block mid.vs_current_bb fn.fn_blocks = SOME bb /\
   mid.vs_inst_idx = s.vs_inst_idx+9 /\
   isPREFIX (emitted_insts sm sb) (DROP mid.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `LENGTH (emitted_insts sa sm) = 9`
       (fn thm => once_rewrite_tac[GSYM thm]) >>
     irule signed_suffix_entry >>
     goal_assum (drule_at (Pat `isPREFIX _ _`)) >>
     conj_tac >- simp[] >>
     qexists_tac `s with vs_vars := u.vs_vars` >> simp[]) >>
  `~mid.vs_halted` by metis_tac[gas_path_ptr_ok_not_halted] >>
  `run_inst_seq (emitted_insts sm sb) mid =
    OK (t with vs_inst_idx := s.vs_inst_idx+9)` by
    (irule signed_suffix_run_ok >> simp[Abbr `mid`] >> metis_tac[]) >>
  `s0a.cs_next_var <= sm.cs_next_var /\
   (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
   (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
   (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p)` by
    (fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  drule_all signed_checked_suffix_frame >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  gs[] >>
  qexistsl_tac [`H'`,`th'`] >> simp[] >>
  irule (SIMP_RULE (srw_ss()) [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)) >>
  goal_assum (drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ (OK mid)`)) >>
  simp[]
QED

Theorem signed_checked_path:
  load_bytestring_as_word op SAR sa = ((word,bits),sm) /\
  compile_int_clamp T n word sm = (out,sb) /\
  run_inst_seq (emitted_insts sa sm) s = OK u /\
  run_inst_seq (emitted_insts sa sm ++ emitted_insts sm sb) s = OK t /\
  gas_path_ptr D 0 ctx fn PG G tn s 0 H th
    (OK (u with vs_inst_idx := s.vs_inst_idx+9)) /\
  (u with vs_inst_idx := s.vs_inst_idx+9) =
    s with <|vs_vars := u.vs_vars; vs_inst_idx := s.vs_inst_idx+9|> /\
  op_prov H word = NONE /\ op_taint th word = {} /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sm ++ emitted_insts sm sb)
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  ghost_inv d cenv cx ee H th (u with vs_inst_idx := s.vs_inst_idx+9) /\
  ghost_kept cenv es s0a G0 tn0 s0 H th /\
  s0a.cs_next_var <= sa.cs_next_var /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) ==>
  ?K tk.
    gas_path_ptr D 0 ctx fn PG G tn s 0 K tk
      (OK (t with vs_inst_idx := s.vs_inst_idx+9+LENGTH (emitted_insts sm sb))) /\
    out = word /\ op_prov K out = NONE /\ op_taint tk out = {} /\
    ghost_inv d cenv cx ee K tk
      (t with vs_inst_idx := s.vs_inst_idx+9+LENGTH (emitted_insts sm sb)) /\
    ghost_kept cenv es s0a G0 tn0 s0 K tk
Proof
  strip_tac >> irule signed_checked_suffix_path >> simp[] >>
  goal_assum (drule_at (Pat `load_bytestring_as_word _ _ _ = _`)) >>
  simp[] >> metis_tac[]
QED

(* Readonly algebra: record expansion stays at this boundary. *)
Theorem signed_readonly_inverse:
  (t with <|vs_vars := s.vs_vars; vs_inst_idx := i|>) = s ==>
  !j. (t with vs_inst_idx := j) =
    s with <|vs_vars := t.vs_vars; vs_inst_idx := j|>
Proof
  simp[venom_state_component_equality] >> metis_tac[]
QED

Theorem signed_readonly_trans:
  m = s with <|vs_vars := m.vs_vars; vs_inst_idx := i|> /\
  t = m with <|vs_vars := t.vs_vars; vs_inst_idx := j|> ==>
  t = s with <|vs_vars := t.vs_vars; vs_inst_idx := j|>
Proof
  strip_tac >>
  qpat_x_assum `t = _` (fn eq => once_rewrite_tac[eq]) >>
  qpat_x_assum `m = _` (fn eq => once_rewrite_tac[eq]) >> simp[]
QED

Theorem signed_old_vars_trans:
  sa.cs_next_var <= sm.cs_next_var /\
  (!p. not_fresh_at sa p ==> lookup_var p u = lookup_var p s) /\
  (!p. not_fresh_at sm p ==> lookup_var p t = lookup_var p u) ==>
  !p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s
Proof
  simp[not_fresh_at_def] >> rpt strip_tac >>
  `p < sm.cs_next_var` by decide_tac >> metis_tac[]
QED

(* One child entry supplies both the semantic case and the pointer loader cut. *)
Theorem signed_scalar_compile_cases[local]:
  is_bytestring_type src /\
  ((?b. typ = BaseT (IntT b)) \/ typ = BaseT DecimalT) /\
  compile_type_convert op (mk_convert_op src typ) sa = (out,sb) ==>
  (?bits. load_bytestring_as_word op SAR sa = ((out,bits),sb)) \/
  (?word bits sm.
    load_bytestring_as_word op SAR sa = ((word,bits),sm) /\
    ((?n. compile_int_clamp T n word sm = (out,sb)) \/
     (?divisor lo hi k. compile_type_convert op (ConvBytestringToDecimal divisor lo hi k) sa = (out,sb) /\ 168 < k*8)))
Proof
  strip_tac
  >- (gvs[mk_convert_op_def] >>
      drule signed_convert_loader_suffix >> strip_tac >>
      gvs[AllCaseEqs()] >> metis_tac[]) >>
  gvs[mk_convert_op_def] >> pairarg_tac >> gvs[] >>
  drule decimal_convert_loader_suffix >> strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[NOT_LESS_EQUAL]
QED

(* Runtime temporaries need not be absent: exact semantics is first applied
   to the restricted map, then only execution and values are extended. *)
Theorem signed_loader_run_actual:
  load_bytestring_as_word (Var src) SAR sa = ((out,bits),sb) /\
  not_fresh_at sa src /\ lookup_var src s = SOME a /\
  mload (w2n a) s = n ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand bits t = SOME ((32w - n) * 8w) /\
    eval_operand out t = SOME
      (word_asr (if n = 0w then 0w else mload (w2n (a+32w)) s)
        (w2n ((32w - n) * 8w)))
Proof
  strip_tac >>
  `eval_operand (Var src) (drop_fresh sa s) = SOME a` by
    simp[eval_operand_def, lookup_var_drop_fresh] >>
  drule dynamic_load_word_raw_exact >>
  disch_then (qspec_then `drop_fresh sa s` mp_tac) >>
  simp[fresh_vars_wrt_drop_fresh, drop_fresh_def, mload_def] >>
  strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
      ~is_ext_call_op i.inst_opcode) (emitted_insts sa sb)` by
    (drule_all signed_loader_shape_fresh >> strip_tac >>
     simp[mk_inst_def, is_terminator_def, is_ext_call_op_def]) >>
  `vars_ext_result (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s))
     (run_inst_seq (emitted_insts sa sb) s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh]) >>
  gvs[vars_ext_result_def, drop_fresh_def, mload_def] >>
  metis_tac[vars_ext_eval_operand]
QED

Theorem signed_loader_run_filter[local]:
  load_bytestring_as_word op SAR sa = ((out,bits),sb) ==>
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
    ~is_ext_call_op i.inst_opcode) (emitted_insts sa sb)
Proof
  strip_tac >> drule signed_loader_decompose >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> gvs[] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND,
       mk_inst_def, is_terminator_def, is_ext_call_op_def]
QED

Theorem signed_convert_run_filter[local]:
  is_bytestring_type src /\
  ((?b. typ = BaseT (IntT b)) \/ typ = BaseT DecimalT) /\
  compile_type_convert op (mk_convert_op src typ) sa = (out,sb) ==>
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
    ~is_ext_call_op i.inst_opcode) (emitted_insts sa sb)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all signed_scalar_compile_cases >>
  disch_then (DISJ_CASES_THEN2 strip_assume_tac
    (qx_choose_then `word` (qx_choose_then `bits` (qx_choose_then `sm`
      (map_every assume_tac o CONJUNCTS)))))
  >- (drule signed_loader_run_filter >> simp[]) >>
  drule signed_loader_layout >> strip_tac >>
  drule_all signed_checked_suffix_layout >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> metis_tac[]) >>
  asm_rewrite_tac[EVERY_APPEND] >> conj_tac
  >- (drule signed_loader_run_filter >> simp[]) >>
  qpat_x_assum `(?n. compile_int_clamp _ _ _ _ = _) \/ _` mp_tac >>
  strip_tac
  >- (drule int_clamp_signed_code >> strip_tac >>
      simp[mk_inst_def, is_terminator_def, is_ext_call_op_def]) >>
  drule decimal_convert_loader_suffix >> strip_tac >>
  gvs[] >> simp[mk_inst_def, is_terminator_def, is_ext_call_op_def]
QED

Theorem signed_convert_run_from_child_actual:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert typ [e]) es /\
  body_expr_ptr_ok cx e /\ is_bytestring_type (expr_type e) /\
  ((?b. typ = BaseT (IntT b)) \/ typ = BaseT DecimalT) /\
  (do z <- eval_expr cx e; read_result cx z od) es = (INL v,ee) /\
  expr_post ctx fn cenv cx e es s0a sa s0 ee v op s /\
  compile_type_convert op (mk_convert_op (expr_type e) typ) sa = (out,sb) /\
  (!p. op = Var p ==> not_fresh_at sa p) /\ eval_operand op s = SOME a /\
  w2n a+32 < dimword(:256) ==>
  case convert_result cx (expr_type e) typ v of
  | INL vout => ?dtv t. evaluate_type (get_tenv cx) typ = SOME dtv /\
      run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand out t = SOME (typed_val_to_w256 dtv vout)
  | INR ex => (?m. ex = Error (RuntimeError m)) /\
      ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre cenv cx env e es /\
   valid_conversion (expr_type e) typ /\ well_formed_type env.type_defs typ` by
    metis_tac[signed_convert_body_entry] >>
  drule_all signed_convert_child_memory >> strip_tac >>
  `~is_bytestring_type typ` by gvs[is_bytestring_type_def] >>
  `val_in_memory tv v (w2n a) s.vs_memory` by gvs[] >>
  `eval_operand op (drop_fresh sa s) = SOME a` by
    (Cases_on `op` >> gvs[eval_operand_def, lookup_var_drop_fresh, drop_fresh_def]) >>
  `val_in_memory tv v (w2n a) (drop_fresh sa s).vs_memory` by
    simp[drop_fresh_def] >>
  `fresh_vars_wrt sa (drop_fresh sa s)` by simp[fresh_vars_wrt_drop_fresh] >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
    ~is_ext_call_op i.inst_opcode) (emitted_insts sa sb)` by
    (irule signed_convert_run_filter >> metis_tac[]) >>
  `vars_ext_result (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s))
     (run_inst_seq (emitted_insts sa sb) s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh]) >>
  drule_at (Pat `compile_type_convert _ _ _ = _`) dynamic_scalar_run_exact >>
  disch_then (drule_at (Pat `fresh_vars_wrt _ _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  disch_then (drule_at (Pat `well_formed_type _ _`)) >>
  disch_then (qspecl_then [`convert_result cx (expr_type e) typ v`,`cx`] mp_tac) >>
  simp[] >> Cases_on `convert_result cx (expr_type e) typ v` >>
  simp[] >> strip_tac >> gvs[vars_ext_result_def] >>
  metis_tac[vars_ext_eval_operand]
QED

Theorem signed_child_entry_packet[local]:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TypeBuiltin typ Convert typ [e]) es /\
  body_expr_ptr_ok cx e /\ is_bytestring_type (expr_type e) /\
  ((?b. typ = BaseT (IntT b)) \/ typ = BaseT DecimalT) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  expr_post ctx fn cenv cx e es s0a sa s0 ee v op s /\
  ptr_val_ok cx (expr_type e) v op G tn s /\ ptr_buf_ok cenv e op G s /\
  64 <= type_memory_bytes cenv (lowered_value_type cenv e) /\
  compile_type_convert op (mk_convert_op (expr_type e) typ) sa = (out,sb) /\
  load_bytestring_as_word op SAR sa = ((word,bits),sm) /\
  (!p. op = Var p ==> not_fresh_at sa p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ghost_inv d cenv cx ee G tn s /\ ghost_kept cenv es s0a G0 tn0 s0 G tn /\
  s0a.cs_next_var <= sa.cs_next_var /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) ==>
  (case convert_result cx (expr_type e) typ v of
   | INL vout => ?dtv t. evaluate_type (get_tenv cx) typ = SOME dtv /\
       run_inst_seq (emitted_insts sa sb) s = OK t /\
       eval_operand out t = SOME (typed_val_to_w256 dtv vout)
   | INR ex => (?m. ex = Error (RuntimeError m)) /\
       ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t) /\
  ?u H th.
    run_inst_seq (emitted_insts sa sm) s = OK u /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th
      (OK (u with vs_inst_idx := s.vs_inst_idx+9)) /\
    op_prov H word = NONE /\ op_taint th word = {} /\
    ghost_inv d cenv cx ee H th (u with vs_inst_idx := s.vs_inst_idx+9) /\
    ghost_kept cenv es s0a G0 tn0 s0 H th /\
    (u with vs_inst_idx := s.vs_inst_idx+9) =
      s with <|vs_vars := u.vs_vars; vs_inst_idx := s.vs_inst_idx+9|> /\
    (!p. not_fresh_at sa p ==> lookup_var p u = lookup_var p s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre cenv cx env e es /\ valid_conversion (expr_type e) typ` by
    metis_tac[signed_convert_body_entry] >>
  drule_all signed_convert_child_loader_inputs >> strip_tac >>
  `eval_operand op s = SOME a` by gvs[eval_operand_def] >>
  conj_tac >- (drule_all signed_convert_run_from_child_actual >> simp[]) >>
  `not_fresh_at sa src` by metis_tac[] >>
  qpat_x_assum `op = Var src` SUBST_ALL_TAC >>
  drule_all signed_loader_run_actual >> strip_tac >>
  drule_all signed_loader_counted_ghost_frame >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`t`,`H`,`th`] >> simp[] >> metis_tac[]
QED

Theorem signed_checked_success_continuation[local]:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TypeBuiltin typ Convert typ [e]) es /\
  body_expr_ptr_ok cx e /\ is_bytestring_type (expr_type e) /\
  ((?b. typ = BaseT (IntT b)) \/ typ = BaseT DecimalT) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  expr_post ctx fn cenv cx e es s0a sa s0 ee v op s /\
  ptr_val_ok cx (expr_type e) v op G tn s /\ ptr_buf_ok cenv e op G s /\
  64 <= type_memory_bytes cenv (lowered_value_type cenv e) /\
  compile_type_convert op (mk_convert_op (expr_type e) typ) sa = (out,sb) /\
  load_bytestring_as_word op SAR sa = ((word,bits),sm) /\
  ((?n. compile_int_clamp T n word sm = (out,sb)) \/
   (?divisor lo hi k. compile_type_convert op (ConvBytestringToDecimal divisor lo hi k) sa = (out,sb) /\ 168 < k*8)) /\
  convert_result cx (expr_type e) typ v = INL result /\
  (!p. op = Var p ==> not_fresh_at sa p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ghost_inv d cenv cx ee G tn s /\ ghost_kept cenv es s0a G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sa /\ s0a.cs_next_var <= sa.cs_next_var /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx+9+LENGTH (emitted_insts sm sb) = LENGTH sb.cs_current_insts ==>
  gas_summary_ptr_at (cx_dead cx) (ctx,fn) PG []
    (\vs. (convert_result cx (expr_type e) typ v,vs))
    (ee with gas_obs := [],s,G,tn)
    (\res fin K tk ss. ?vout. res = INL vout /\
      expr_post ctx fn cenv cx (TypeBuiltin typ Convert typ [e])
        es s0a sb s0 fin vout out ss /\
      ss.vs_current_bb = sb.cs_current_bb /\
      ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin K tk ss /\
      ptr_val_ok cx typ vout out K tk ss /\
      ghost_kept cenv es s0a G0 tn0 s0 K tk)
    (\res fin gt r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule signed_loader_layout >> strip_tac >>
  drule_all signed_checked_suffix_layout >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> metis_tac[]) >>
  `isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions)` by
    metis_tac[hash_code_prefix_split] >>
  drule_all signed_child_entry_packet >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`] assume_tac) >>
  qpat_assum `convert_result cx (expr_type e) typ v = INL result`
    (fn eq => first_x_assum (strip_assume_tac o SIMP_RULE (srw_ss()) [eq])) >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK t'` >>
  rename1 `run_inst_seq (emitted_insts sa sb) s = OK t` >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
    (drule_all signed_checked_suffix_filter >> simp[]) >>
  `run_inst_seq (emitted_insts sm sb) t' = OK t` by
    (qpat_assum `run_inst_seq (emitted_insts sa sm) s = OK t'`
       (mp_tac o MATCH_MP run_inst_seq_append) >>
     disch_then (qspec_then `emitted_insts sm sb` assume_tac) >> metis_tac[]) >>
  drule_all signed_checked_suffix_runtime_frame >> strip_tac >>
  `run_inst_seq (emitted_insts sa sm ++ emitted_insts sm sb) s = OK t /\
   isPREFIX (emitted_insts sa sm ++ emitted_insts sm sb)
     (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
  drule_all signed_checked_suffix_path >> strip_tac >>
  qabbrev_tac `j = s.vs_inst_idx+9+LENGTH (emitted_insts sm sb)` >>
  `t with <|vs_vars := t'.vs_vars; vs_inst_idx := t'.vs_inst_idx|> = t'` by
    (qpat_assum `t with vs_vars := t'.vs_vars = t'`
       (mp_tac o Q.AP_TERM `\st. st with vs_inst_idx := t'.vs_inst_idx`) >>
     simp[]) >>
  drule signed_readonly_inverse >> disch_then (qspec_then `j` assume_tac) >>
  `t with vs_inst_idx := j =
     s with <|vs_vars := t.vs_vars; vs_inst_idx := j|>` by
    (qpat_assum `t' with vs_inst_idx := _ = s with <|vs_vars := _; vs_inst_idx := _|>`
       (mp_tac o Q.AP_TERM `\st. st with <|vs_vars := t.vs_vars; vs_inst_idx := j|>`) >>
     simp[] >> metis_tac[]) >>
  `!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s` by
    (match_mp_tac (Q.INST [`u` |-> `t'`] (SPEC_ALL signed_old_vars_trans)) >> simp[]) >>
  qpat_assum `convert_result cx (expr_type e) typ v = INL result`
    (fn eq => once_rewrite_tac[GSYM eq]) >>
  irule signed_scalar_path_summary >>
  conj_tac >- gvs[is_word_type_def] >>
  goal_assum (drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  qexistsl_tac [`op`,`result`,`sa`,`dtv`] >>
  simp[Abbr `j`] >>
  conj_tac >- (rpt strip_tac >> simp[lookup_var_def] >> metis_tac[lookup_var_def]) >>
  conj_tac
  >- (qpat_assum `t with vs_inst_idx := _ = s with <|vs_vars := _; vs_inst_idx := _|>`
        (mp_tac o Q.AP_TERM `\st. st.vs_current_bb`) >> simp[]) >>
  conj_tac >- gvs[stmtFragPtrTheory.ghost_inv_gas_obs] >>
  gvs[expr_post_def, expr_val_at_def, stmt_state_rel_def, state_rel_gas_obs,
      loweringPostsTheory.locals_kept_def, loweringPostsTheory.popped_kept_def] >>
    metis_tac[]
QED

Theorem signed_clamped_success_continuation:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TypeBuiltin typ Convert typ [e]) es /\
  body_expr_ptr_ok cx e /\ is_bytestring_type (expr_type e) /\
  ((?b. typ = BaseT (IntT b)) \/ typ = BaseT DecimalT) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  expr_post ctx fn cenv cx e es s0a sa s0 ee v op s /\
  ptr_val_ok cx (expr_type e) v op G tn s /\ ptr_buf_ok cenv e op G s /\
  64 <= type_memory_bytes cenv (lowered_value_type cenv e) /\
  compile_type_convert op (mk_convert_op (expr_type e) typ) sa = (out,sb) /\
  load_bytestring_as_word op SAR sa = ((word,bits),sm) /\
  compile_int_clamp T n word sm = (out,sb) /\
  convert_result cx (expr_type e) typ v = INL result /\
  fresh_vars_wrt sa s /\ (!p. op = Var p ==> not_fresh_at sa p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ghost_inv d cenv cx ee G tn s /\ ghost_kept cenv es s0a G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sa /\ s0a.cs_next_var <= sa.cs_next_var /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx+9+LENGTH (emitted_insts sm sb) = LENGTH sb.cs_current_insts ==>
  gas_summary_ptr_at (cx_dead cx) (ctx,fn) PG []
    (\vs. (convert_result cx (expr_type e) typ v,vs))
    (ee with gas_obs := [],s,G,tn)
    (\res fin K tk ss. ?vout. res = INL vout /\
      expr_post ctx fn cenv cx (TypeBuiltin typ Convert typ [e])
        es s0a sb s0 fin vout out ss /\
      ss.vs_current_bb = sb.cs_current_bb /\
      ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin K tk ss /\
      ptr_val_ok cx typ vout out K tk ss /\
      ghost_kept cenv es s0a G0 tn0 s0 K tk)
    (\res fin gt r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule signed_checked_success_continuation >> simp[] >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  goal_assum (drule_at (Pat `load_bytestring_as_word _ _ _ = _`)) >>
  simp[] >> metis_tac[]
QED

Theorem signed_checked_suffix_abort[local]:
  load_bytestring_as_word op SAR sa = ((word,bits),sm) /\
  ((?n. compile_int_clamp T n word sm = (out,sb)) \/
   (?divisor lo hi k. compile_type_convert op (ConvBytestringToDecimal divisor lo hi k) sa = (out,sb) /\ 168 < k*8)) /\
  op_prov G word = NONE /\ op_taint tn word = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sm sb) s = Abort err t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?H th j. gas_path_ptr D 0 ctx fn PG G tn s 0 H th
    (Abort err (t with vs_inst_idx := j))
Proof
  strip_tac
  >- (drule_all signed_clamp_abort_zero_path >> simp[]) >>
  drule_all decimal_suffix_abort_zero_path >> simp[]
QED

Theorem signed_checked_abort_summary[local]:
  load_bytestring_as_word op SAR sa = ((word,bits),sm) /\
  ((?n. compile_int_clamp T n word sm = (out,sb)) \/
   (?divisor lo hi k. compile_type_convert op (ConvBytestringToDecimal divisor lo hi k) sa = (out,sb) /\ 168 < k*8)) /\
  run_inst_seq (emitted_insts sa sm) s = OK u /\
  run_inst_seq (emitted_insts sa sm ++ emitted_insts sm sb) s = Abort Revert_abort t /\
  gas_path_ptr D 0 ctx fn PG G tn s 0 H th
    (OK (u with vs_inst_idx := s.vs_inst_idx+9)) /\
  (u with vs_inst_idx := s.vs_inst_idx+9) =
    s with <|vs_vars := u.vs_vars; vs_inst_idx := s.vs_inst_idx+9|> /\
  op_prov H word = NONE /\ op_taint th word = {} /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sm ++ emitted_insts sm sb)
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  (?m. ex = Error (RuntimeError m)) ==>
  gas_summary_ptr_at D (ctx,fn) PG [] (\vs. (INR ex,vs))
    (ee with gas_obs := [],s,G,tn) Q (\res fin gt r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule signed_loader_layout >> strip_tac >>
  `LENGTH (emitted_insts sa sm) = 9` by
    (qpat_x_assum `LENGTH sm.cs_current_insts = _` mp_tac >> simp[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
    (drule_all signed_checked_suffix_filter >> simp[]) >>
  qabbrev_tac `mid = u with vs_inst_idx := s.vs_inst_idx+9` >>
  `lookup_block mid.vs_current_bb fn.fn_blocks = SOME bb /\
   mid.vs_inst_idx = s.vs_inst_idx+9 /\
   isPREFIX (emitted_insts sm sb) (DROP mid.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `LENGTH (emitted_insts sa sm) = 9`
       (fn thm => once_rewrite_tac[GSYM thm]) >>
     irule signed_suffix_entry >>
     goal_assum (drule_at (Pat `isPREFIX _ _`)) >>
     conj_tac >- simp[] >>
     qexists_tac `s with vs_vars := u.vs_vars` >> simp[]) >>
  `~mid.vs_halted` by metis_tac[gas_path_ptr_ok_not_halted] >>
  `run_inst_seq (emitted_insts sm sb) mid =
    Abort Revert_abort (t with vs_inst_idx := s.vs_inst_idx+9)` by
    (irule signed_suffix_run_abort >> simp[Abbr `mid`] >> metis_tac[]) >>
  drule_all signed_checked_suffix_abort >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 H' th'
    (Abort Revert_abort (t with vs_inst_idx := j))` by
    (irule (SIMP_RULE (srw_ss()) [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)) >>
     goal_assum (drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ (OK mid)`)) >>
     gvs[]) >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INR ex`,`ee with gas_obs := []`,`H'`,`th'`,
    `Abort Revert_abort (t with vs_inst_idx := j)`] >>
  gvs[exprSimDefsTheory.expr_exit_def, exit_result_def]
QED

Theorem signed_checked_abort_continuation[local]:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TypeBuiltin typ Convert typ [e]) es /\
  body_expr_ptr_ok cx e /\ is_bytestring_type (expr_type e) /\
  ((?b. typ = BaseT (IntT b)) \/ typ = BaseT DecimalT) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  expr_post ctx fn cenv cx e es s0a sa s0 ee v op s /\
  ptr_val_ok cx (expr_type e) v op G tn s /\ ptr_buf_ok cenv e op G s /\
  64 <= type_memory_bytes cenv (lowered_value_type cenv e) /\
  compile_type_convert op (mk_convert_op (expr_type e) typ) sa = (out,sb) /\
  load_bytestring_as_word op SAR sa = ((word,bits),sm) /\
  ((?n. compile_int_clamp T n word sm = (out,sb)) \/
   (?divisor lo hi k. compile_type_convert op (ConvBytestringToDecimal divisor lo hi k) sa = (out,sb) /\ 168 < k*8)) /\
  convert_result cx (expr_type e) typ v = INR ex /\
  (!p. op = Var p ==> not_fresh_at sa p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ghost_inv d cenv cx ee G tn s /\ ghost_kept cenv es s0a G0 tn0 s0 G tn /\
  s0a.cs_next_var <= sa.cs_next_var /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) ==>
  gas_summary_ptr_at (cx_dead cx) (ctx,fn) PG []
    (\vs. (convert_result cx (expr_type e) typ v,vs))
    (ee with gas_obs := [],s,G,tn) Q (\res fin gt r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule signed_loader_layout >> strip_tac >>
  drule_all signed_checked_suffix_layout >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> metis_tac[]) >>
  `isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions)` by
    metis_tac[hash_code_prefix_split] >>
  drule_all signed_child_entry_packet >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`] assume_tac) >>
  qpat_assum `convert_result cx (expr_type e) typ v = INR ex`
    (fn eq => first_x_assum (strip_assume_tac o SIMP_RULE (srw_ss()) [eq])) >>
  qpat_assum `convert_result cx (expr_type e) typ v = INR ex`
    (fn eq => once_rewrite_tac[eq]) >>
  irule signed_checked_abort_summary >> simp[] >>
  goal_assum (drule_at (Pat `load_bytestring_as_word _ _ _ = _`)) >>
  simp[] >> qexistsl_tac [`H`,`out`,`sb`,`t`,`th`] >> gvs[] >> metis_tac[]
QED


Theorem signed_nonzero_continuation:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TypeBuiltin typ Convert typ [e]) es /\
  body_expr_ptr_ok cx e /\ is_bytestring_type (expr_type e) /\
  ((?b. typ = BaseT (IntT b)) \/ typ = BaseT DecimalT) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  expr_post ctx fn cenv cx e es s0a sa s0 ee v op s /\
  ptr_val_ok cx (expr_type e) v op G tn s /\ ptr_buf_ok cenv e op G s /\
  64 <= type_memory_bytes cenv (lowered_value_type cenv e) /\
  compile_type_convert op (mk_convert_op (expr_type e) typ) sa = (out,sb) /\
  fresh_vars_wrt sa s /\ (!p. op = Var p ==> not_fresh_at sa p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ghost_inv d cenv cx ee G tn s /\ ghost_kept cenv es s0a G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sa /\ s0a.cs_next_var <= sa.cs_next_var /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_summary_ptr_at (cx_dead cx) (ctx,fn) PG []
    (\vs. (convert_result cx (expr_type e) typ v,vs))
    (ee with gas_obs := [],s,G,tn)
    (\res fin K tk ss. ?vout. res = INL vout /\
      expr_post ctx fn cenv cx (TypeBuiltin typ Convert typ [e])
        es s0a sb s0 fin vout out ss /\
      ss.vs_current_bb = sb.cs_current_bb /\
      ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin K tk ss /\
      ptr_val_ok cx typ vout out K tk ss /\
      ghost_kept cenv es s0a G0 tn0 s0 K tk)
    (\res fin gt r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all signed_scalar_compile_cases >>
  disch_then (DISJ_CASES_THEN2 strip_assume_tac
    (qx_choose_then `word` (qx_choose_then `bits` (qx_choose_then `sm`
      (map_every assume_tac o CONJUNCTS)))))
  >- (drule signed_loader_layout >> strip_tac >>
      `s.vs_inst_idx+9 = LENGTH sb.cs_current_insts` by metis_tac[] >>
      drule_all signed_loader_only_continuation >> simp[]) >>
  drule signed_loader_layout >> strip_tac >>
  drule_all signed_checked_suffix_layout >> strip_tac >>
  `s.vs_inst_idx+9+LENGTH (emitted_insts sm sb) = LENGTH sb.cs_current_insts` by
    (qpat_assum `sb.cs_current_insts = _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  Cases_on `convert_result cx (expr_type e) typ v`
  >- (drule_all signed_checked_success_continuation >> simp[]) >>
  drule_all signed_checked_abort_continuation >> simp[]
QED

(* The child endpoint chooses zero-capacity dispatch before any payload load. *)
Theorem signed_convert_continuation:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TypeBuiltin typ Convert typ [e]) es /\
  body_expr_ptr_ok cx e /\ is_bytestring_type (expr_type e) /\
  ((?b. typ = BaseT (IntT b)) \/ typ = BaseT DecimalT) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  expr_post ctx fn cenv cx e es s0a sa s0 ee v op s /\
  ptr_val_ok cx (expr_type e) v op G tn s /\ ptr_buf_ok cenv e op G s /\
  (if lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
      lowered_value_type cenv e = BaseT (StringT 0)
   then out = Lit 0w /\ sb = sa
   else 64 <= type_memory_bytes cenv (lowered_value_type cenv e) /\
        compile_type_convert op (mk_convert_op (expr_type e) typ) sa = (out,sb)) /\
  fresh_vars_wrt sa s /\ (!p. op = Var p ==> not_fresh_at sa p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ghost_inv d cenv cx ee G tn s /\ ghost_kept cenv es s0a G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sa /\ s0a.cs_next_var <= sa.cs_next_var /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_summary_ptr_at (cx_dead cx) (ctx,fn) PG []
    (\vs. (convert_result cx (expr_type e) typ v,vs))
    (ee with gas_obs := [],s,G,tn)
    (\res fin K tk ss. ?vout. res = INL vout /\
      expr_post ctx fn cenv cx (TypeBuiltin typ Convert typ [e])
        es s0a sb s0 fin vout out ss /\
      ss.vs_current_bb = sb.cs_current_bb /\
      ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin K tk ss /\
      ptr_val_ok cx typ vout out K tk ss /\
      ghost_kept cenv es s0a G0 tn0 s0 K tk)
    (\res fin gt r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
            lowered_value_type cenv e = BaseT (StringT 0)`
  >- (qpat_x_assum `if _ then _ else _` mp_tac >> asm_rewrite_tac[] >> strip_tac >>
      gnvs[] >> irule signed_zero_capacity_continuation >> simp[] >>
      conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
      conj_tac >- gvs[stmtFragPtrTheory.ghost_inv_gas_obs] >>
      qexists_tac `op` >>
      gvs[expr_post_def, expr_val_at_def, stmt_state_rel_def, state_rel_gas_obs,
      loweringPostsTheory.locals_kept_def, loweringPostsTheory.popped_kept_def] >>
    metis_tac[]) >>
  qpat_x_assum `if _ then _ else _` mp_tac >> simp[] >> strip_tac >>
  drule_all signed_nonzero_continuation >> simp[]
QED

(* The child runs with the observations selected by its marked execution.
   Only structural framing is transported back to the original source state. *)
Theorem signed_convert_continuation_gas:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TypeBuiltin typ Convert typ [e]) es /\
  body_expr_ptr_ok cx e /\ is_bytestring_type (expr_type e) /\
  ((?b. typ = BaseT (IntT b)) \/ typ = BaseT DecimalT) /\
  (do r <- eval_expr cx e; read_result cx r od) (es with gas_obs := gs) = (INL v,ee) /\
  expr_post ctx fn cenv cx e es s0a sa s0 ee v op s /\
  ptr_val_ok cx (expr_type e) v op G tn s /\ ptr_buf_ok cenv e op G s /\
  (if lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
      lowered_value_type cenv e = BaseT (StringT 0)
   then out = Lit 0w /\ sb = sa
   else 64 <= type_memory_bytes cenv (lowered_value_type cenv e) /\
        compile_type_convert op (mk_convert_op (expr_type e) typ) sa = (out,sb)) /\
  fresh_vars_wrt sa s /\ (!p. op = Var p ==> not_fresh_at sa p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ghost_inv d cenv cx ee G tn s /\ ghost_kept cenv es s0a G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sa /\ s0a.cs_next_var <= sa.cs_next_var /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_summary_ptr_at (cx_dead cx) (ctx,fn) PG []
    (\vs. (convert_result cx (expr_type e) typ v,vs))
    (ee with gas_obs := [],s,G,tn)
    (\res fin K tk ss. ?vout. res = INL vout /\
      expr_post ctx fn cenv cx (TypeBuiltin typ Convert typ [e])
        es s0a sb s0 fin vout out ss /\
      ss.vs_current_bb = sb.cs_current_bb /\
      ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin K tk ss /\
      ptr_val_ok cx typ vout out K tk ss /\
      ghost_kept cenv es s0a G0 tn0 s0 K tk)
    (\res fin gt r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!K tk. ghost_kept cenv (es with gas_obs := gs) s0a G0 tn0 s0 K tk =
          ghost_kept cenv es s0a G0 tn0 s0 K tk` by simp[ghost_kept_def] >>
  mp_tac (Q.INST [`es` |-> `es with gas_obs := gs`] signed_convert_continuation) >>
  simp[extract32_expr_post_start_gas_obs] >>
  disch_then irule >> first_assum ACCEPT_TAC
QED


(* Freshness-free orchestration: all pointer checks run on the child state. *)
Theorem signed_loader_only_continuation_actual[local]:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TypeBuiltin typ Convert typ [e]) es /\
  body_expr_ptr_ok cx e /\ is_bytestring_type (expr_type e) /\
  ((?b. typ = BaseT (IntT b)) \/ typ = BaseT DecimalT) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  expr_post ctx fn cenv cx e es s0a sa s0 ee v op s /\
  ptr_val_ok cx (expr_type e) v op G tn s /\ ptr_buf_ok cenv e op G s /\
  64 <= type_memory_bytes cenv (lowered_value_type cenv e) /\
  compile_type_convert op (mk_convert_op (expr_type e) typ) sa = (out,sb) /\
  load_bytestring_as_word op SAR sa = ((out,bits),sb) /\
  (!p. op = Var p ==> not_fresh_at sa p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ghost_inv d cenv cx ee G tn s /\ ghost_kept cenv es s0a G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sa /\ s0a.cs_next_var <= sa.cs_next_var /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx+9 = LENGTH sb.cs_current_insts ==>
  gas_summary_ptr_at (cx_dead cx) (ctx,fn) PG []
    (\vs. (convert_result cx (expr_type e) typ v,vs))
    (ee with gas_obs := [],s,G,tn)
    (\res fin K tk ss. ?vout. res = INL vout /\
      expr_post ctx fn cenv cx (TypeBuiltin typ Convert typ [e])
        es s0a sb s0 fin vout out ss /\
      ss.vs_current_bb = sb.cs_current_bb /\
      ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin K tk ss /\
      ptr_val_ok cx typ vout out K tk ss /\
      ghost_kept cenv es s0a G0 tn0 s0 K tk)
    (\res fin gt r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all signed_child_entry_packet >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`] strip_assume_tac) >>
  `?tv result. convert_result cx (expr_type e) typ v = INL result /\
     evaluate_type (get_tenv cx) typ = SOME tv /\
     eval_operand out u = SOME (typed_val_to_w256 tv result)` by
    (Cases_on `convert_result cx (expr_type e) typ v` >> gvs[]) >>
  irule signed_scalar_path_summary >>
  conj_tac >- gvs[is_word_type_def] >>
  goal_assum (drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  qexistsl_tac [`op`,`result`,`sa`,`tv`] >>
  simp[] >>
  conj_tac >- (rpt strip_tac >> simp[lookup_var_def] >> metis_tac[lookup_var_def]) >>
  conj_tac
  >- (qpat_x_assum `u with vs_inst_idx := _ = _` mp_tac >>
      simp[venom_state_component_equality]) >>
  conj_tac >- gvs[stmtFragPtrTheory.ghost_inv_gas_obs] >>
  gvs[expr_post_def, expr_val_at_def, stmt_state_rel_def, state_rel_gas_obs,
      loweringPostsTheory.locals_kept_def, loweringPostsTheory.popped_kept_def] >>
    metis_tac[]
QED

Theorem signed_nonzero_continuation_actual[local]:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TypeBuiltin typ Convert typ [e]) es /\
  body_expr_ptr_ok cx e /\ is_bytestring_type (expr_type e) /\
  ((?b. typ = BaseT (IntT b)) \/ typ = BaseT DecimalT) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  expr_post ctx fn cenv cx e es s0a sa s0 ee v op s /\
  ptr_val_ok cx (expr_type e) v op G tn s /\ ptr_buf_ok cenv e op G s /\
  64 <= type_memory_bytes cenv (lowered_value_type cenv e) /\
  compile_type_convert op (mk_convert_op (expr_type e) typ) sa = (out,sb) /\
  (!p. op = Var p ==> not_fresh_at sa p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ghost_inv d cenv cx ee G tn s /\ ghost_kept cenv es s0a G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sa /\ s0a.cs_next_var <= sa.cs_next_var /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_summary_ptr_at (cx_dead cx) (ctx,fn) PG []
    (\vs. (convert_result cx (expr_type e) typ v,vs))
    (ee with gas_obs := [],s,G,tn)
    (\res fin K tk ss. ?vout. res = INL vout /\
      expr_post ctx fn cenv cx (TypeBuiltin typ Convert typ [e])
        es s0a sb s0 fin vout out ss /\
      ss.vs_current_bb = sb.cs_current_bb /\
      ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin K tk ss /\
      ptr_val_ok cx typ vout out K tk ss /\
      ghost_kept cenv es s0a G0 tn0 s0 K tk)
    (\res fin gt r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all signed_scalar_compile_cases >>
  disch_then (DISJ_CASES_THEN2 strip_assume_tac
    (qx_choose_then `word` (qx_choose_then `bits` (qx_choose_then `sm`
      (map_every assume_tac o CONJUNCTS)))))
  >- (drule signed_loader_layout >> strip_tac >>
      `s.vs_inst_idx+9 = LENGTH sb.cs_current_insts` by metis_tac[] >>
      drule_all signed_loader_only_continuation_actual >> simp[]) >>
  drule signed_loader_layout >> strip_tac >>
  drule_all signed_checked_suffix_layout >> strip_tac >>
  `s.vs_inst_idx+9+LENGTH (emitted_insts sm sb) = LENGTH sb.cs_current_insts` by
    (qpat_assum `sb.cs_current_insts = _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  Cases_on `convert_result cx (expr_type e) typ v`
  >- (drule_all signed_checked_success_continuation >> simp[]) >>
  drule_all signed_checked_abort_continuation >> simp[]
QED

Theorem signed_convert_continuation_actual:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TypeBuiltin typ Convert typ [e]) es /\
  body_expr_ptr_ok cx e /\ is_bytestring_type (expr_type e) /\
  ((?b. typ = BaseT (IntT b)) \/ typ = BaseT DecimalT) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  expr_post ctx fn cenv cx e es s0a sa s0 ee v op s /\
  ptr_val_ok cx (expr_type e) v op G tn s /\ ptr_buf_ok cenv e op G s /\
  (if lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
      lowered_value_type cenv e = BaseT (StringT 0)
   then out = Lit 0w /\ sb = sa
   else 64 <= type_memory_bytes cenv (lowered_value_type cenv e) /\
        compile_type_convert op (mk_convert_op (expr_type e) typ) sa = (out,sb)) /\
  (!p. op = Var p ==> not_fresh_at sa p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ghost_inv d cenv cx ee G tn s /\ ghost_kept cenv es s0a G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sa /\ s0a.cs_next_var <= sa.cs_next_var /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_summary_ptr_at (cx_dead cx) (ctx,fn) PG []
    (\vs. (convert_result cx (expr_type e) typ v,vs))
    (ee with gas_obs := [],s,G,tn)
    (\res fin K tk ss. ?vout. res = INL vout /\
      expr_post ctx fn cenv cx (TypeBuiltin typ Convert typ [e])
        es s0a sb s0 fin vout out ss /\
      ss.vs_current_bb = sb.cs_current_bb /\
      ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin K tk ss /\
      ptr_val_ok cx typ vout out K tk ss /\
      ghost_kept cenv es s0a G0 tn0 s0 K tk)
    (\res fin gt r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
            lowered_value_type cenv e = BaseT (StringT 0)`
  >- (qpat_x_assum `if _ then _ else _` mp_tac >> asm_rewrite_tac[] >> strip_tac >>
      gnvs[] >> irule signed_zero_capacity_continuation >> simp[] >>
      conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
      conj_tac >- gvs[stmtFragPtrTheory.ghost_inv_gas_obs] >>
      qexists_tac `op` >>
      gvs[expr_post_def, expr_val_at_def, stmt_state_rel_def, state_rel_gas_obs,
      loweringPostsTheory.locals_kept_def, loweringPostsTheory.popped_kept_def] >>
    metis_tac[]) >>
  qpat_x_assum `if _ then _ else _` mp_tac >> simp[] >> strip_tac >>
  drule_all signed_nonzero_continuation_actual >> simp[]
QED

Theorem signed_convert_continuation_gas_actual:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TypeBuiltin typ Convert typ [e]) es /\
  body_expr_ptr_ok cx e /\ is_bytestring_type (expr_type e) /\
  ((?b. typ = BaseT (IntT b)) \/ typ = BaseT DecimalT) /\
  (do r <- eval_expr cx e; read_result cx r od) (es with gas_obs := gs) = (INL v,ee) /\
  expr_post ctx fn cenv cx e es s0a sa s0 ee v op s /\
  ptr_val_ok cx (expr_type e) v op G tn s /\ ptr_buf_ok cenv e op G s /\
  (if lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
      lowered_value_type cenv e = BaseT (StringT 0)
   then out = Lit 0w /\ sb = sa
   else 64 <= type_memory_bytes cenv (lowered_value_type cenv e) /\
        compile_type_convert op (mk_convert_op (expr_type e) typ) sa = (out,sb)) /\
  (!p. op = Var p ==> not_fresh_at sa p) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ghost_inv d cenv cx ee G tn s /\ ghost_kept cenv es s0a G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sa /\ s0a.cs_next_var <= sa.cs_next_var /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_summary_ptr_at (cx_dead cx) (ctx,fn) PG []
    (\vs. (convert_result cx (expr_type e) typ v,vs))
    (ee with gas_obs := [],s,G,tn)
    (\res fin K tk ss. ?vout. res = INL vout /\
      expr_post ctx fn cenv cx (TypeBuiltin typ Convert typ [e])
        es s0a sb s0 fin vout out ss /\
      ss.vs_current_bb = sb.cs_current_bb /\
      ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin K tk ss /\
      ptr_val_ok cx typ vout out K tk ss /\
      ghost_kept cenv es s0a G0 tn0 s0 K tk)
    (\res fin gt r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!K tk. ghost_kept cenv (es with gas_obs := gs) s0a G0 tn0 s0 K tk =
          ghost_kept cenv es s0a G0 tn0 s0 K tk` by simp[ghost_kept_def] >>
  mp_tac (Q.INST [`es` |-> `es with gas_obs := gs`] signed_convert_continuation_actual) >>
  simp[extract32_expr_post_start_gas_obs] >>
  disch_then irule >> first_assum ACCEPT_TAC
QED

Theorem signed_convert_code_entry:
  is_bytestring_type src /\
  ((?b. typ = BaseT (IntT b)) \/ typ = BaseT DecimalT) /\
  (if zero_cap then out = Lit 0w /\ sb = sa
   else compile_type_convert op (mk_convert_op src typ) sa = (out,sb)) /\
  fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  s.vs_current_bb = sb.cs_current_bb /\
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (Cases_on `zero_cap` >- gvs[] >>
     gnvs[] >> drule_all signed_scalar_compile_cases >> strip_tac
     >- metis_tac[signed_loader_layout] >>
     metis_tac[signed_loader_layout, signed_clamp_block_layout,
       decimal_checked_suffix_layout]) >>
  gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
  simp[emitted_insts_def, listTheory.DROP_APPEND]
QED
