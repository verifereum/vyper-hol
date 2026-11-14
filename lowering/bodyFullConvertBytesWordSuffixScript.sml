(* Uniform composition of the header and normalized payload certificates. *)
Theory bodyFullConvertBytesWordSuffix
Ancestors
  bodyFullConvertBytesWordPrefix bodyFullConvertBytesWordNormalize
  bodyPtrTypeBuiltinsBytesWordParts
  bodyPtrSignedConvertUnsignedCompose reasonCopySourcePtr instSeqComposePtr
  bodyPtrSignedConvertUnsignedLoad bodyPtrDefs fragExec venomState
  venomInst venomExecSemantics finite_map words arithmetic exprLoweringProps list

Theorem bytes_word_loader_fixed_frame:
  load_bytestring_as_word (Var src) SHR sa = ((out,bits),sb) /\
  not_fresh_at sa src /\ ~ctx_has_dalloca ctx /\
  lookup_var src s = SOME a /\ ptr_covers G tn src s capacity /\
  64 <= capacity /\ FLOOKUP G src = SOME (b,sz) /\ b+sz <= dimword(:256) /\
  mload (w2n a) s = n2w n /\ n <= 32 /\
  (!x. w2n a <= x /\ x < w2n a+32+n ==> x NOTIN tn.t_mem) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?HG th.
    (!D q. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := q) HG th) /\
    op_prov HG out = NONE /\ op_taint th out = {} /\
    op_prov HG bits = NONE /\ op_taint th bits = {} /\
    eval_operand bits t = SOME (n2w (8*(32-n))) /\
    t = s with vs_vars := t.vs_vars /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP HG p = FLOOKUP G p /\ op_taint th (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all unsigned_loader_shape_fresh >> strip_tac >>
  `ptr_covers G tn src s 64` by (irule ptr_covers_mono >> metis_tac[]) >>
  `w2n a+64 <= dimword(:256)` by (gvs[ptr_covers_def] >> decide_tac) >>
  `src <> len` by fs[] >>
  drule_all bytestring_source_run >>
  disch_then (qspecl_then [`sa.cs_next_id+1`,`sa.cs_next_id`,`dp`] assume_tac) >>
  qabbrev_tac `u = update_var dp (a+32w) (update_var len (mload (w2n a) s) s)` >>
  `ALL_DISTINCT [src;len;dp] /\
   (!x. w2n a <= x /\ x < w2n a+32 ==> x NOTIN tn.t_mem)` by
    (conj_tac >- fs[] >> gen_tac >> disch_then strip_assume_tac >>
     qpat_x_assum `!x. _ ==> x NOTIN tn.t_mem` irule >> decide_tac) >>
  drule_all bytes_word_prefix_fixed_frame >>
  disch_then (qspecl_then [`fn`,`PG`]
    (qx_choose_then `G1` (qx_choose_then `tn1` strip_assume_tac))) >>
  `ALL_DISTINCT [len;dp;data;sub;shift;dst]` by fs[] >>
  `w2n (a+32w) = w2n a+32` by
    (simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  `!x. w2n (a+32w) <= x /\ x < w2n (a+32w)+n ==> x NOTIN tn1.t_mem` by
    (simp[] >> gen_tac >> disch_then strip_assume_tac >>
     qpat_x_assum `!x. _ /\ x < w2n a+32+n ==> _` irule >> decide_tac) >>
  `run_inst_seq [mk_inst (sa.cs_next_id+2) MLOAD [Var dp] [data];
    mk_inst (sa.cs_next_id+3) SUB [Lit 32w;Var len] [sub];
    mk_inst (sa.cs_next_id+4) MUL [Var sub;Lit 8w] [shift];
    mk_inst (sa.cs_next_id+5) SHR [Var shift;Var data] [dst]] u = OK t` by
    (drule run_inst_seq_append >>
     disch_then (qspec_then `[mk_inst (sa.cs_next_id+2) MLOAD [Var dp] [data];
       mk_inst (sa.cs_next_id+3) SUB [Lit 32w;Var len] [sub];
       mk_inst (sa.cs_next_id+4) MUL [Var sub;Lit 8w] [shift];
       mk_inst (sa.cs_next_id+5) SHR [Var shift;Var data] [dst]]` mp_tac) >> fs[]) >>
  drule_all bytes_word_normalize_fixed_frame >>
  disch_then (qspecl_then [`fn`,`PG`]
    (qx_choose_then `HG` (qx_choose_then `th` strip_assume_tac))) >>
  qexistsl_tac [`HG`,`th`] >>
  conj_tac
  >- (gen_tac >> simp[] >>
      irule (SRULE [APPEND] (Q.INST [`xs` |->
        `[mk_inst sa.cs_next_id MLOAD [Var src] [len];
          mk_inst (sa.cs_next_id+1) ADD [Var src;Lit 32w] [dp]]`]
        inst_seq_ptr_uniform_append)) >>
      simp[is_terminator_def] >> qexistsl_tac [`G1`,`tn1`] >> simp[]) >>
  `t = s with vs_vars := t.vs_vars` by
    (qpat_x_assum `t = u with vs_vars := _` (fn eq => once_rewrite_tac[eq]) >>
     qpat_x_assum `u = s with vs_vars := _` (fn eq => once_rewrite_tac[eq]) >> simp[]) >>
  simp[] >> rpt strip_tac >>
  `~MEM p [len;dp] /\ ~MEM p [data;sub;shift;dst]` by
    (fs[] >> metis_tac[]) >> metis_tac[]
QED
