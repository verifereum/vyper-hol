(* Fixed physical signed-loader endpoint and mask-uniform ghost witnesses. *)
Theory bodyFullConvertSignedLoader
Ancestors
  bodyPtrSignedConvertSignedFixed bodyPtrSignedConvertSourceFixed bodyPtrSignedConvertSourceFrame
  exprSimConvertFromBytes instSeqComposePtr fragGasSeqPtr fragGasPathPtr
  fragExec emitHelperProps exprLoweringProps venomState venomInst
  venomExecSemantics ptrDiscipline finite_map words arithmetic list pred_set varsExt

Theorem inst_seq_ptr_uniformize[local]:
  (!D. ?H th.
    (!q. inst_seq_ptr D 0 ctx fn PG G tn code
      (s with vs_inst_idx := q) H th) /\ P H th) ==>
  ?H th.
    (!D q. inst_seq_ptr D 0 ctx fn PG G tn code
      (s with vs_inst_idx := q) H th) /\ P H th
Proof
  strip_tac >>
  first_assum (qspec_then `ARB` (qx_choose_then `H` (qx_choose_then `th` strip_assume_tac))) >>
  qexistsl_tac [`H`,`th`] >> simp[] >> rpt gen_tac >>
  first_x_assum (qspec_then `D` (qx_choose_then `H1` (qx_choose_then `th1` strip_assume_tac))) >>
  `H1 = H /\ th1 = th` by
    (irule inst_seq_ptr_ghost_unique >> metis_tac[]) >>
  gvs[]
QED

Theorem signed_loader_uniform_frame_raw:
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
  ?HG th.
    (!D q. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst i MLOAD [Var src] [len];
       mk_inst j ADD [Var src;Lit 32w] [dp];
       mk_inst k MLOAD [Var dp] [data];
       mk_inst l ISZERO [Var len] [empty];
       mk_inst m ISZERO [Var empty] [nonempty];
       mk_inst r MUL [Var data;Var nonempty] [selected];
       mk_inst u SUB [Lit 32w;Var len] [sub];
       mk_inst v MUL [Var sub;Lit 8w] [bits];
       mk_inst w SAR [Var bits;Var selected] [dst]] (s with vs_inst_idx := q) HG th) /\
    op_prov HG (Var dst) = NONE /\ op_taint th (Var dst) = {} /\
    op_prov HG (Var bits) = NONE /\ op_taint th (Var bits) = {} /\
    eval_operand (Var bits) t = SOME (n2w (8*(32-n))) /\
    t.vs_memory = s.vs_memory /\ th.t_mem = tn.t_mem /\
    th.t_stor = tn.t_stor /\ th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_current_bb = s.vs_current_bb /\
    t = s with vs_vars := t.vs_vars /\
    (!p. ~MEM p [len;dp;data;empty;nonempty;selected;sub;bits;dst] ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP HG p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  drule (SRULE [APPEND] (Q.INST [`xs` |->
    `[mk_inst i MLOAD [Var src] [len]; mk_inst j ADD [Var src;Lit 32w] [dp]]`,
    `ys` |-> `[mk_inst k MLOAD [Var dp] [data];
      mk_inst l ISZERO [Var len] [empty]; mk_inst m ISZERO [Var empty] [nonempty];
      mk_inst r MUL [Var data;Var nonempty] [selected];
      mk_inst u SUB [Lit 32w;Var len] [sub]; mk_inst v MUL [Var sub;Lit 8w] [bits];
      mk_inst w SAR [Var bits;Var selected] [dst]]`] run_inst_seq_append_ok_split)) >>
  disch_then (qx_choose_then `s1` strip_assume_tac) >>
  drule (SRULE [APPEND] (Q.INST [`xs` |->
    `[mk_inst k MLOAD [Var dp] [data];
      mk_inst l ISZERO [Var len] [empty]; mk_inst m ISZERO [Var empty] [nonempty];
      mk_inst r MUL [Var data;Var nonempty] [selected]]`,
    `ys` |-> `[mk_inst u SUB [Lit 32w;Var len] [sub];
      mk_inst v MUL [Var sub;Lit 8w] [bits];
      mk_inst w SAR [Var bits;Var selected] [dst]]`] run_inst_seq_append_ok_split)) >>
  disch_then (qx_choose_then `s2` strip_assume_tac) >>
  `32 <= capacity /\ ALL_DISTINCT [src;len;dp] /\
   (!x. w2n a <= x /\ x < w2n a+32 ==> x NOTIN tn.t_mem)` by
    (fs[] >> rpt strip_tac >>
     qpat_x_assum `!x. _ ==> x NOTIN tn.t_mem` irule >> decide_tac) >>
  `?G1 tn1.
     (!D q. inst_seq_ptr D 0 ctx fn PG G tn
       [mk_inst i MLOAD [Var src] [len]; mk_inst j ADD [Var src;Lit 32w] [dp]]
       (s with vs_inst_idx := q) G1 tn1) /\
     lookup_var len s1 = SOME (mload (w2n a) s) /\
     op_taint tn1 (Var len) = {} /\ op_prov G1 (Var len) = NONE /\
     lookup_var dp s1 = SOME (a+32w) /\
     s1.vs_memory = s.vs_memory /\ tn1.t_mem = tn.t_mem /\
     tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
     s1.vs_call_ctx = s.vs_call_ctx /\ s1.vs_accounts = s.vs_accounts /\
     s1.vs_transient = s.vs_transient /\ s1.vs_current_bb = s.vs_current_bb /\
     s1 = s with vs_vars := s1.vs_vars /\
     (!p. p <> len /\ p <> dp ==> lookup_var p s1 = lookup_var p s /\
       FLOOKUP G1 p = FLOOKUP G p /\ op_taint tn1 (Var p) = op_taint tn (Var p)) /\
     (!z. 32 < capacity /\ 32+z <= capacity /\ w2n a+32 < dimword(:256) ==>
       ptr_covers G1 tn1 dp s1 z)` by
    (ho_match_mp_tac inst_seq_ptr_uniformize >> gen_tac >>
     irule bytestring_source_fixed_frame >> simp[] >> metis_tac[]) >>
  `ptr_covers G1 tn1 dp s1 32 /\
   ALL_DISTINCT [len;dp;data;empty;nonempty;selected] /\
   lookup_var len s1 = SOME (n2w n)` by
    (rpt conj_tac >- (first_x_assum irule >> decide_tac) >> fs[]) >>
  `?G2 tn2.
    (!D q. inst_seq_ptr D 0 ctx fn PG G1 tn1
      [mk_inst k MLOAD [Var dp] [data];
       mk_inst l ISZERO [Var len] [empty]; mk_inst m ISZERO [Var empty] [nonempty];
       mk_inst r MUL [Var data;Var nonempty] [selected]] (s1 with vs_inst_idx := q) G2 tn2) /\
    op_prov G2 (Var selected) = NONE /\
    op_taint tn2 (Var selected) = (if n = 0 then {} else mem_word_taint tn1.t_mem (w2n (a+32w))) /\
    s2.vs_memory = s1.vs_memory /\ tn2.t_mem = tn1.t_mem /\
    tn2.t_stor = tn1.t_stor /\ tn2.t_trans = tn1.t_trans /\ tn2.t_imm = tn1.t_imm /\
    s2.vs_call_ctx = s1.vs_call_ctx /\ s2.vs_accounts = s1.vs_accounts /\
    s2.vs_transient = s1.vs_transient /\ s2.vs_current_bb = s1.vs_current_bb /\
    s2 = s1 with vs_vars := s2.vs_vars /\
    (!p. ~MEM p [data;empty;nonempty;selected] ==>
      lookup_var p s2 = lookup_var p s1 /\ FLOOKUP G2 p = FLOOKUP G1 p /\
      op_taint tn2 (Var p) = op_taint tn1 (Var p))` by
    (ho_match_mp_tac inst_seq_ptr_uniformize >> gen_tac >>
     irule signed_select_fixed_frame >> simp[] >> metis_tac[]) >>
  `w2n (a+32w) = w2n a+32` by
    simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  `!z. z IN mem_word_taint tn1.t_mem (w2n (a+32w)) ==> n <= z /\ z < 32` by
    (simp[mem_word_taint_def] >> rpt strip_tac >>
     spose_not_then strip_assume_tac >>
     `w2n a <= w2n a+32+z /\ w2n a+32+z < w2n a+32+n` by decide_tac >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  `ALL_DISTINCT [len;selected;sub;bits;dst] /\
   lookup_var len s2 = SOME (n2w n) /\ op_prov G2 (Var len) = NONE /\
   op_taint tn2 (Var len) = {} /\
   (n = 0 ==> op_taint tn2 (Var selected) = {}) /\
   (!z. z IN op_taint tn2 (Var selected) ==> n <= z /\ z < 32)` by
    (fs[op_prov_def] >> Cases_on `n = 0` >> gvs[]) >>
  `?HG th.
    (!D q. inst_seq_ptr D 0 ctx fn PG G2 tn2
      [mk_inst u SUB [Lit 32w;Var len] [sub];
       mk_inst v MUL [Var sub;Lit 8w] [bits];
       mk_inst w SAR [Var bits;Var selected] [dst]] (s2 with vs_inst_idx := q) HG th) /\
    op_prov HG (Var dst) = NONE /\ op_taint th (Var dst) = {} /\
    op_prov HG (Var bits) = NONE /\ op_taint th (Var bits) = {} /\
    eval_operand (Var bits) t = SOME (n2w (8*(32-n))) /\
    t.vs_memory = s2.vs_memory /\ th.t_mem = tn2.t_mem /\
    th.t_stor = tn2.t_stor /\ th.t_trans = tn2.t_trans /\ th.t_imm = tn2.t_imm /\
    t.vs_call_ctx = s2.vs_call_ctx /\ t.vs_accounts = s2.vs_accounts /\
    t.vs_transient = s2.vs_transient /\ t.vs_current_bb = s2.vs_current_bb /\
    t = s2 with vs_vars := t.vs_vars /\
    (!p. ~MEM p [sub;bits;dst] ==> lookup_var p t = lookup_var p s2 /\
      FLOOKUP HG p = FLOOKUP G2 p /\ op_taint th (Var p) = op_taint tn2 (Var p))` by
    (ho_match_mp_tac inst_seq_ptr_uniformize >> gen_tac >>
     irule signed_normalize_fixed_frame >> simp[] >> metis_tac[]) >>
  `!D q. inst_seq_ptr D 0 ctx fn PG G1 tn1
    [mk_inst k MLOAD [Var dp] [data];
     mk_inst l ISZERO [Var len] [empty]; mk_inst m ISZERO [Var empty] [nonempty];
     mk_inst r MUL [Var data;Var nonempty] [selected];
     mk_inst u SUB [Lit 32w;Var len] [sub]; mk_inst v MUL [Var sub;Lit 8w] [bits];
     mk_inst w SAR [Var bits;Var selected] [dst]] (s1 with vs_inst_idx := q) HG th` by
    (gen_tac >> irule (SRULE [APPEND] (Q.INST [`xs` |->
      `[mk_inst k MLOAD [Var dp] [data];
        mk_inst l ISZERO [Var len] [empty]; mk_inst m ISZERO [Var empty] [nonempty];
        mk_inst r MUL [Var data;Var nonempty] [selected]]`] inst_seq_ptr_uniform_append)) >>
     simp[is_terminator_def] >> qexistsl_tac [`G2`,`tn2`] >> simp[]) >>
  qexistsl_tac [`HG`,`th`] >> conj_tac
  >- (gen_tac >> irule (SRULE [APPEND] (Q.INST [`xs` |->
        `[mk_inst i MLOAD [Var src] [len]; mk_inst j ADD [Var src;Lit 32w] [dp]]`]
        inst_seq_ptr_uniform_append)) >>
      simp[is_terminator_def] >> qexistsl_tac [`G1`,`tn1`] >> simp[]) >>
  simp[] >>
  qpat_x_assum `t = s2 with vs_vars := _` (fn eq => once_rewrite_tac[eq]) >>
  qpat_x_assum `s2 = s1 with vs_vars := _` (fn eq => once_rewrite_tac[eq]) >>
  qpat_x_assum `s1 = s with vs_vars := _` (fn eq => once_rewrite_tac[eq]) >> simp[]
QED

Theorem convert_signed_loader_uniform:
  load_bytestring_as_word (Var src) SAR sa = ((out,bits),sb) /\
  not_fresh_at sa src /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  lookup_var src s = SOME a /\ ptr_covers G tn src s capacity /\ 64 <= capacity /\
  w2n a+32 < dimword(:256) /\ mload (w2n a) s = n2w n /\ n <= 32 /\
  (!x. w2n a <= x /\ x < w2n a+32+n ==> x NOTIN tn.t_mem) ==>
  ?t HG th.
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand out t = SOME
      (word_asr (if (n2w n:256 word) = 0w then 0w else mload (w2n (a+32w)) s)
        (w2n (((32w-n2w n)*8w):256 word))) /\
    eval_operand bits t = SOME (n2w (8*(32-n))) /\
    t.vs_allocas = s.vs_allocas /\
    t = s with vs_vars := t.vs_vars /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
    op_prov HG out = NONE /\ op_taint th out = {} /\
    op_prov HG bits = NONE /\ op_taint th bits = {} /\
    (!p w. (!z. p = Var z ==> not_fresh_at sa z) /\ eval_operand p s = SOME w ==>
      eval_operand p t = SOME w) /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP HG p = FLOOKUP G p /\ op_taint th (Var p) = op_taint tn (Var p)) /\
    (!D. gas_path_ptr D 0 ctx fn PG G tn s 0 HG th
      (OK (t with vs_inst_idx := s.vs_inst_idx+9)))
Proof
  strip_tac >>
  `eval_operand (Var src) (drop_fresh sa s) = SOME a` by
    simp[eval_operand_def, lookup_var_drop_fresh] >>
  drule dynamic_load_word_raw_exact >>
  disch_then (qspecl_then [`drop_fresh sa s`,`n2w n`,`mload (w2n (a+32w)) s`,`a`] mp_tac) >>
  `mload (w2n a) (drop_fresh sa s) = n2w n /\
   mload (w2n (a+32w)) (drop_fresh sa s) = mload (w2n (a+32w)) s` by
    (simp[drop_fresh_def, mload_def] >> fs[mload_def]) >>
  simp[fresh_vars_wrt_drop_fresh] >> strip_tac >>
  drule_all bodyPtrSignedConvertSignedLoadTheory.signed_loader_shape_fresh >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
    ~is_ext_call_op i.inst_opcode) (emitted_insts sa sb)` by
    simp[mk_inst_def, is_terminator_def, is_ext_call_op_def] >>
  `vars_ext_result (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s))
    (run_inst_seq (emitted_insts sa sb) s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh]) >>
  `?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand out t = SOME
      (word_asr (if (n2w n:256 word) = 0w then 0w else mload (w2n (a+32w)) s)
        (w2n (((32w-n2w n)*8w):256 word))) /\
    eval_operand bits t = SOME (n2w (8*(32-n)))` by
    (gvs[vars_ext_result_def, vars_ext_def] >>
     conj_tac >- metis_tac[eval_operand_vars_ext, optionTheory.NOT_NONE_SOME] >>
     `((32w - n2w n) * 8w :256 word) = n2w (8*(32-n))` by
       (simp[GSYM wordsTheory.n2w_sub, wordsTheory.word_mul_n2w,
          arithmeticTheory.MULT_COMM]) >>
     metis_tac[eval_operand_vars_ext, optionTheory.NOT_NONE_SOME]) >>
  qpat_x_assum `run_inst_seq _ (drop_fresh sa s) = _` kall_tac >>
  `run_inst_seq [mk_inst i MLOAD [Var src] [len];
    mk_inst j ADD [Var src;Lit 32w] [dp];
    mk_inst k MLOAD [Var dp] [data];
    mk_inst l ISZERO [Var len] [empty];
    mk_inst m ISZERO [Var empty] [nonempty];
    mk_inst r MUL [Var data;Var nonempty] [selected];
    mk_inst u SUB [Lit 32w;Var len] [sub];
    mk_inst v MUL [Var sub;Lit 8w] [b];
    mk_inst w SAR [Var b;Var selected] [dst]] s = OK t` by
    (qpat_x_assum `run_inst_seq (emitted_insts sa sb) s = OK t` mp_tac >>
     asm_rewrite_tac[]) >>
  drule_all signed_loader_uniform_frame_raw >>
  disch_then (qspecl_then [`fn`,`PG`]
    (qx_choose_then `HG` (qx_choose_then `th` strip_assume_tac))) >>
  qexistsl_tac [`t`,`HG`,`th`] >> simp[] >>
  conj_tac
  >- (qpat_x_assum `t = s with vs_vars := _` (fn eq => once_rewrite_tac[eq]) >> simp[]) >>
  conj_tac
  >- (`t.vs_labels = s.vs_labels` by
        (qpat_x_assum `t = s with vs_vars := _` (fn eq => once_rewrite_tac[eq]) >> simp[]) >>
      rpt gen_tac >> strip_tac >> Cases_on `p` >>
      gvs[eval_operand_def] >> metis_tac[]) >>
  gen_tac >>
  mp_tac (Q.SPECL [`emitted_insts sa sb`,`s`,`t`,`G`,`tn`,`HG`,`th`,`ctx`,`fn`,`bb`]
    (Q.INST [`lo` |-> `0`] run_inst_seq_gas_path_ptr)) >>
  simp[is_terminator_def] >>
  disch_then irule >>
  qpat_x_assum `!D q. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
    (qspecl_then [`D`,`s.vs_inst_idx`] mp_tac) >> simp[]
QED

(* Readonly consequences for the very same endpoint, at any horizon/cursor. *)
Theorem convert_signed_loader_endpoint_posts:
  t = s with vs_vars := t.vs_vars /\
  th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
  th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
  (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
    FLOOKUP HG p = FLOOKUP G p /\ op_taint th (Var p) = op_taint tn (Var p)) ==>
  (!H d cenv cx es idx.
    ghost_inv H d cenv cx es G tn s /\
    (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
      not_fresh_at sa p) /\
    (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
    (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) ==>
    ghost_inv H d cenv cx es HG th (t with vs_inst_idx := idx)) /\
  (!cenv es0 s0a G0 tn0 s0.
    ghost_kept cenv es0 s0a G0 tn0 s0 G tn /\
    s0a.cs_next_var <= sa.cs_next_var ==>
    ghost_kept cenv es0 s0a G0 tn0 s0 HG th)
Proof
  strip_tac >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      irule (Q.SPEC `not_fresh_at sa` ghost_inv_readonly_frame) >>
      simp[] >>
      qpat_x_assum `t = s with vs_vars := _` (fn eq => once_rewrite_tac[eq]) >>
      simp[] >> qexistsl_tac [`G`,`s`,`sa`,`tn`] >>
      fs[lookup_var_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  irule (Q.SPEC `not_fresh_at sa` ghost_kept_readonly_frame) >>
  qexistsl_tac [`G`,`sa`,`tn`] >>
  simp[] >> metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]
QED
