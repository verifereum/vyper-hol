(* Fixed physical header/address endpoint, with dead-mask-uniform ghosts. *)
Theory bodyFullConvertBytesWordPrefix
Ancestors
  bodyPtrSignedConvertSourceFixed
  wordLoadStorePtr bodyPtrSignedConvertLoad typedCopyPtr typedCopyLoopHeaderPtr
  fragGasSeqPtr ghostPcTransportPtr instIdxIndep fragExec exprLoweringProps
  venomInstProofs venomState venomExecSemantics venomInst finite_map
  ptrDiscipline emitHelperProps bodyPtrDefs

Theorem prefix_uniform_checks[local]:
  ALL_DISTINCT [src;len;dp] /\ lookup_var src s = SOME a /\
  ptr_covers G tn src s 64 /\ ~ctx_has_dalloca ctx /\
  run_inst_seq [mk_inst i MLOAD [Var src] [len];
                mk_inst j ADD [Var src;Lit 32w] [dp]] s = OK t ==>
  ?H th.
    (!D k. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst i MLOAD [Var src] [len];
       mk_inst j ADD [Var src;Lit 32w] [dp]]
      (s with vs_inst_idx := k) H th) /\
    H = step_prov PG
      (step_prov PG G (mk_inst i MLOAD [Var src] [len])
        (update_var len (mload (w2n a) s) s))
      (mk_inst j ADD [Var src;Lit 32w] [dp]) t /\
    th = step_taint (mk_inst j ADD [Var src;Lit 32w] [dp])
      (update_var len (mload (w2n a) s) s) t
      (step_taint (mk_inst i MLOAD [Var src] [len]) s
        (update_var len (mload (w2n a) s) s) tn)
Proof
  strip_tac >>
  `src <> len` by fs[] >>
  drule_all bodyPtrSignedConvertSourceFixedTheory.bytestring_source_run_endpoint >> strip_tac >>
  qmatch_goalsub_abbrev_tac `step_prov PG G _ u` >>
  qabbrev_tac `G1 = step_prov PG G (mk_inst i MLOAD [Var src] [len]) u` >>
  qabbrev_tac `tn1 = step_taint (mk_inst i MLOAD [Var src] [len]) s u tn` >>
  `op_taint tn1 (Var src) = {}` by
    (simp[Abbr `tn1`, Abbr `u`, mload_ambient_frame] >> fs[ptr_covers_def]) >>
  qexistsl_tac [`step_prov PG G1 (mk_inst j ADD [Var src;Lit 32w] [dp]) t`,
    `step_taint (mk_inst j ADD [Var src;Lit 32w] [dp]) u t tn1`] >>
  reverse conj_tac >- simp[Abbr `G1`, Abbr `tn1`] >>
  rpt gen_tac >>
  `step_inst_base (mk_inst i MLOAD [Var src] [len]) (s with vs_inst_idx := k) =
     OK (u with vs_inst_idx := k)` by
    (`step_inst_base (mk_inst i MLOAD [Var src] [len]) (s with vs_inst_idx := k) =
       OK (update_var len (mload (w2n a) (s with vs_inst_idx := k))
         (s with vs_inst_idx := k))` by
       (irule step_MLOAD >> fs[eval_operand_def, lookup_var_def]) >>
     gvs[Abbr `u`, update_var_def, mload_def]) >>
  `step_inst_base (mk_inst j ADD [Var src;Lit 32w] [dp])
     (u with vs_inst_idx := SUC k) = OK (t with vs_inst_idx := SUC k)` by
    (`step_inst_base (mk_inst j ADD [Var src;Lit 32w] [dp])
        (u with vs_inst_idx := SUC k) =
       OK (update_var dp (a+32w) (u with vs_inst_idx := SUC k))` by
       (irule step_ADD >>
        fs[Abbr `u`, eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
     simp[update_var_def]) >>
  simp[inst_seq_ptr_def, Abbr `G1`, Abbr `tn1`] >>
  conj_tac
  >- (irule ptr_inst_ok_mload >> simp[eval_operand_def] >>
      fs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  irule ptr_inst_ok_copy_len_binop >> simp[op_taint_def]
QED

Theorem bytes_word_prefix_fixed_frame:
  ALL_DISTINCT [src;len;dp] /\ ~ctx_has_dalloca ctx /\
  lookup_var src s = SOME a /\ ptr_covers G tn src s 64 /\
  w2n a + 64 <= dimword (:256) /\ mload (w2n a) s = n2w n /\ n <= 32 /\
  (!x. w2n a <= x /\ x < w2n a+32 ==> x NOTIN tn.t_mem) /\
  run_inst_seq [mk_inst i MLOAD [Var src] [len];
    mk_inst j ADD [Var src;Lit 32w] [dp]] s = OK t ==>
  ?H th.
    (!D q. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst i MLOAD [Var src] [len];
       mk_inst j ADD [Var src;Lit 32w] [dp]] (s with vs_inst_idx := q) H th) /\
    lookup_var len t = SOME (n2w n) /\
    lookup_var dp t = SOME (a+32w) /\ ptr_covers H th dp t 32 /\
    op_prov H (Var len) = NONE /\ op_taint th (Var len) = {} /\
    t = s with vs_vars := t.vs_vars /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
    (!p. ~MEM p [len;dp] ==> lookup_var p t = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint th (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all prefix_uniform_checks >>
  disch_then (qspecl_then [`fn`,`PG`] strip_assume_tac) >>
  `src <> len` by fs[] >>
  drule_all bodyPtrSignedConvertSourceFixedTheory.bytestring_source_run_endpoint >> strip_tac >>
  `ptr_covers H th dp t 32` by
    (qpat_x_assum `H = _` (fn eq => rewrite_tac[eq]) >>
     qpat_x_assum `th = _` (fn eq => rewrite_tac[eq]) >>
     qpat_x_assum `t = update_var _ _ _` (fn eq => rewrite_tac[eq]) >>
     irule typed_copy_loop_dynamic_offset_covers >>
     simp[eval_operand_def] >> conj_tac >- fs[] >>
     conj_tac >- fs[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     qexists_tac `64` >> simp[] >>
     qpat_x_assum `mload (w2n a) s = n2w n` (fn eq => rewrite_tac[GSYM eq]) >>
     irule mload_preserves_ptr_covers >> simp[]) >>
  qexistsl_tac [`H`,`th`] >> conj_tac >- simp[] >>
  `eval_operand (Var src) s = SOME a` by simp[eval_operand_def] >>
  drule_all mload_ghost_clean >> strip_tac >> gvs[] >>
  simp[copy_len_binop_ghost_frame, mload_ambient_frame,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  simp[op_prov_def, step_prov_def, out_prov_def, set_prov_def,
       mk_inst_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
       step_taint_def, set_var_taint_def, imm_taint_def] >>
  CASE_TAC >> simp[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def]
QED
