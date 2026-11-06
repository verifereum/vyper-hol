(* Fixed-run source prefix: the endpoint is supplied, never existential. *)
Theory bodyPtrTypeBuiltinsSourceFixed
Ancestors
  bodyPtrTypeBuiltinsSourceCompile bodyPtrTypeBuiltinsSourcePrefix
  typedCopyPtr typedCopyLoopHeaderPtr fragGasSeqPtr ghostPcTransportPtr
  instIdxIndep fragExec exprLoweringProps venomInstProofs venomState
  venomExecSemantics venomInst finite_map ptrDiscipline emitHelperProps bodyPtrDefs

Theorem bytestring_source_run_endpoint:
  src <> len /\ lookup_var src s = SOME a /\
  run_inst_seq [mk_inst i MLOAD [Var src] [len];
                mk_inst j ADD [Var src;Lit 32w] [dp]] s = OK t ==>
  t = update_var dp (a+32w) (update_var len (mload (w2n a) s) s)
Proof
  strip_tac >>
  `eval_operand (Var src) s = SOME a` by simp[eval_operand_def] >>
  `step_inst_base (mk_inst i MLOAD [Var src] [len]) s =
     OK (update_var len (mload (w2n a) s) s)` by simp[step_MLOAD] >>
  `eval_operand (Var src) (update_var len (mload (w2n a) s) s) = SOME a` by
    fs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `eval_operand (Lit 32w) (update_var len (mload (w2n a) s) s) = SOME 32w` by
    simp[eval_operand_def] >>
  `step_inst_base (mk_inst j ADD [Var src;Lit 32w] [dp])
      (update_var len (mload (w2n a) s) s) =
    OK (update_var dp (a+32w) (update_var len (mload (w2n a) s) s))` by
    (irule step_ADD >> simp[]) >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >> simp[run_inst_seq_def]
QED

Theorem bytestring_source_uniform_checks:
  !D ctx fn PG G tn s src len dp i j a capacity t.
    ALL_DISTINCT [src;len;dp] /\ lookup_var src s = SOME a /\
    ptr_covers G tn src s capacity /\ 32 <= capacity /\
    ~ctx_has_dalloca ctx /\
    run_inst_seq [mk_inst i MLOAD [Var src] [len];
                  mk_inst j ADD [Var src;Lit 32w] [dp]] s = OK t ==>
    ?H th.
      (!k. inst_seq_ptr D 0 ctx fn PG G tn
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
  rpt gen_tac >> strip_tac >>
  `src <> len` by fs[] >>
  drule_all bytestring_source_run_endpoint >> strip_tac >>
  qmatch_goalsub_abbrev_tac `step_prov PG G _ u` >>
  qabbrev_tac `G1 = step_prov PG G (mk_inst i MLOAD [Var src] [len]) u` >>
  qabbrev_tac `tn1 = step_taint (mk_inst i MLOAD [Var src] [len]) s u tn` >>
  `op_taint tn1 (Var src) = {}` by
    (simp[Abbr `tn1`, Abbr `u`, bodyPtrTypeBuiltinsLoadTheory.mload_ambient_frame] >>
     fs[ptr_covers_def]) >>
  qexistsl_tac [`step_prov PG G1 (mk_inst j ADD [Var src;Lit 32w] [dp]) t`,
    `step_taint (mk_inst j ADD [Var src;Lit 32w] [dp]) u t tn1`] >>
  reverse conj_tac >- simp[Abbr `G1`, Abbr `tn1`] >>
  gen_tac >>
  `step_inst_base (mk_inst i MLOAD [Var src] [len]) (s with vs_inst_idx := k) =
     OK (u with vs_inst_idx := k)` by
    (`step_inst_base (mk_inst i MLOAD [Var src] [len]) (s with vs_inst_idx := k) =
       OK (update_var len (mload (w2n a) (s with vs_inst_idx := k))
         (s with vs_inst_idx := k))` by
       (irule step_MLOAD >> fs[eval_operand_def, lookup_var_def]) >>
     gvs[Abbr `u`, update_var_def, mload_def]) >>
  `step_inst_base (mk_inst j ADD [Var src;Lit 32w] [dp])
     (u with vs_inst_idx := SUC k) =
     OK (t with vs_inst_idx := SUC k)` by
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
  irule ptr_inst_ok_copy_len_binop >>
  simp[op_taint_def]
QED

Theorem bytestring_source_fixed_frame:
  !D ctx fn PG G tn s src len dp i j a capacity t.
    ALL_DISTINCT [src;len;dp] /\ lookup_var src s = SOME a /\
    ptr_covers G tn src s capacity /\ 32 <= capacity /\
    ~ctx_has_dalloca ctx /\
    (!x. w2n a <= x /\ x < w2n a + 32 ==> x NOTIN tn.t_mem) /\
    run_inst_seq [mk_inst i MLOAD [Var src] [len];
                  mk_inst j ADD [Var src;Lit 32w] [dp]] s = OK t ==>
    ?H th.
      (!k. inst_seq_ptr D 0 ctx fn PG G tn
        [mk_inst i MLOAD [Var src] [len];
         mk_inst j ADD [Var src;Lit 32w] [dp]]
        (s with vs_inst_idx := k) H th) /\
      lookup_var len t = SOME (mload (w2n a) s) /\
      op_taint th (Var len) = {} /\ op_prov H (Var len) = NONE /\
      lookup_var dp t = SOME (a+32w) /\
      t.vs_memory = s.vs_memory /\ th.t_mem = tn.t_mem /\
      th.t_stor = tn.t_stor /\ th.t_trans = tn.t_trans /\
      th.t_imm = tn.t_imm /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
      t.vs_current_bb = s.vs_current_bb /\
      t = s with vs_vars := t.vs_vars /\
      (!p. p <> len /\ p <> dp ==> lookup_var p t = lookup_var p s /\
        FLOOKUP H p = FLOOKUP G p /\ op_taint th (Var p) = op_taint tn (Var p)) /\
      (!n. 32 < capacity /\ 32+n <= capacity /\ w2n a+32 < dimword(:256) ==>
        ptr_covers H th dp t n)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all bytestring_source_uniform_checks >>
  disch_then (qspecl_then [`D`,`fn`,`PG`]
    (qx_choose_then `H` (qx_choose_then `th` strip_assume_tac))) >>
  `src <> len` by fs[] >>
  drule_all bytestring_source_run_endpoint >> strip_tac >>
  `!n. 32 < capacity /\ 32+n <= capacity /\ w2n a+32 < dimword(:256) ==>
     ptr_covers H th dp t n` by
     (rpt strip_tac >>
      qpat_x_assum `H = _` (fn eq => rewrite_tac[eq]) >>
      qpat_x_assum `th = _` (fn eq => rewrite_tac[eq]) >>
      qpat_x_assum `t = update_var _ _ _` (fn eq => rewrite_tac[eq]) >>
      irule typed_copy_loop_dynamic_offset_covers >>
      simp[eval_operand_def] >> conj_tac >- fs[] >>
      conj_tac >- fs[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      qexists_tac `capacity` >>
      simp[arithmeticTheory.ADD_COMM, mload_preserves_ptr_covers]) >>
  qexistsl_tac [`H`,`th`] >> conj_tac >- simp[] >>
  `eval_operand (Var src) s = SOME a` by simp[eval_operand_def] >>
  drule_all mload_ghost_clean >> strip_tac >>
  gvs[] >>
  simp[copy_len_binop_ghost_frame, bodyPtrTypeBuiltinsLoadTheory.mload_ambient_frame,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  simp[op_prov_def, step_prov_def, out_prov_def, set_prov_def,
       mk_inst_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
       step_taint_def, set_var_taint_def, imm_taint_def] >>
  CASE_TAC >> simp[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED

Theorem compile_bytestring_src_fixed_frame:
  !D ctx fn PG G tn s src a capacity sa sm len_op dp_op t.
    compile_bytestring_src (Var src) sa = ((len_op,dp_op),sm) /\
    not_fresh_at sa src /\ lookup_var src s = SOME a /\
    ptr_covers G tn src s capacity /\ 32 <= capacity /\
    ~ctx_has_dalloca ctx /\
    (!x. w2n a <= x /\ x < w2n a + 32 ==> x NOTIN tn.t_mem) /\
    run_inst_seq (emitted_insts sa sm) s = OK t ==>
    ?len dp H th.
      len_op = Var len /\ dp_op = Var dp /\ ALL_DISTINCT [src;len;dp] /\
      ~not_fresh_at sa len /\ ~not_fresh_at sa dp /\
      not_fresh_at sm src /\ not_fresh_at sm len /\ not_fresh_at sm dp /\
      (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sm)
        (s with vs_inst_idx := k) H th) /\
      eval_operand len_op t = SOME (mload (w2n a) s) /\
      op_taint th len_op = {} /\ op_prov H len_op = NONE /\
      eval_operand dp_op t = SOME (a+32w) /\
      t.vs_memory = s.vs_memory /\ th.t_mem = tn.t_mem /\
      th.t_stor = tn.t_stor /\ th.t_trans = tn.t_trans /\
      th.t_imm = tn.t_imm /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
      t.vs_current_bb = s.vs_current_bb /\
      t = s with vs_vars := t.vs_vars /\
      (!p. p <> len /\ p <> dp ==> lookup_var p t = lookup_var p s /\
        FLOOKUP H p = FLOOKUP G p /\ op_taint th (Var p) = op_taint tn (Var p)) /\
      (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
        FLOOKUP H p = FLOOKUP G p /\ op_taint th (Var p) = op_taint tn (Var p)) /\
      (!n. 32 < capacity /\ 32+n <= capacity /\ w2n a+32 < dimword(:256) ==>
        ptr_covers H th dp t n)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_bytestring_src_shape_fresh >>
  disch_then (qx_choose_then `len` (qx_choose_then `dp` strip_assume_tac)) >>
  `run_inst_seq [mk_inst sa.cs_next_id MLOAD [Var src] [len];
     mk_inst (sa.cs_next_id+1) ADD [Var src; Lit 32w] [dp]] s = OK t` by fs[] >>
  drule_all bytestring_source_fixed_frame >>
  disch_then (qspecl_then [`D`,`fn`,`PG`]
    (qx_choose_then `H` (qx_choose_then `th` strip_assume_tac))) >>
  qexistsl_tac [`len`,`dp`,`H`,`th`] >> simp[eval_operand_def] >>
  metis_tac[]
QED
