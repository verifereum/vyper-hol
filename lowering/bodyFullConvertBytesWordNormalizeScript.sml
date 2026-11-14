(* Occupied bytes only: padding taint is removed by the right shift. *)
Theory bodyFullConvertBytesWordNormalize
Ancestors
  wordLoadStorePtr bodyPtrSignedConvertScalarOps fragGasSeqPtr
  venomState venomInst venomInstProofs venomExecSemantics finite_map words
  arithmetic pred_set fragExec ptrSafeRun ptrDiscipline instIdxIndep
  emitHelperProps exprLoweringProps contextCodegenRel

Theorem shift_count_word[local]:
  n <= 32 ==>
  ((32w - n2w n) * 8w : 256 word) = n2w (8*(32-n)) /\
  w2n ((32w - n2w n) * 8w : 256 word) = 8*(32-n)
Proof
  strip_tac >>
  `n < dimword(:256) /\ 8*(32-n) < dimword(:256)` by
    (simp[dimword_def] >> decide_tac) >>
  `32w - n2w n = (n2w (32-n) : 256 word)` by
    simp[GSYM wordsTheory.n2w_sub] >>
  simp[wordsTheory.word_mul_n2w, wordsTheory.w2n_n2w,
       arithmeticTheory.MULT_COMM, arithmeticTheory.LESS_MOD]
QED

Theorem normalize_run_endpoint[local]:
  ALL_DISTINCT [len;dp;data;sub;bits;dst] /\
  lookup_var len s = SOME nv /\ lookup_var dp s = SOME a /\
  run_inst_seq [mk_inst i MLOAD [Var dp] [data];
    mk_inst j SUB [Lit 32w;Var len] [sub];
    mk_inst k MUL [Var sub;Lit 8w] [bits];
    mk_inst l SHR [Var bits;Var data] [dst]] s = OK t ==>
  ?u v w.
    u = update_var data (mload (w2n a) s) s /\
    v = update_var sub (32w-nv) u /\
    w = update_var bits ((32w-nv)*8w) v /\
    t = update_var dst (word_lsr (mload (w2n a) s) (w2n ((32w-nv)*8w))) w /\
    step_inst_base (mk_inst i MLOAD [Var dp] [data]) s = OK u /\
    step_inst_base (mk_inst j SUB [Lit 32w;Var len] [sub]) u = OK v /\
    step_inst_base (mk_inst k MUL [Var sub;Lit 8w] [bits]) v = OK w /\
    step_inst_base (mk_inst l SHR [Var bits;Var data] [dst]) w = OK t
Proof
  strip_tac >>
  qabbrev_tac `u = update_var data (mload (w2n a) s) s` >>
  qabbrev_tac `v = update_var sub (32w-nv) u` >>
  qabbrev_tac `w = update_var bits ((32w-nv)*8w) v` >>
  `step_inst_base (mk_inst i MLOAD [Var dp] [data]) s = OK u` by
    (simp[Abbr `u`] >> irule step_MLOAD >> simp[eval_operand_def]) >>
  `step_inst_base (mk_inst j SUB [Lit 32w;Var len] [sub]) u = OK v` by
    (simp[Abbr `v`] >> irule step_SUB >>
     fs[Abbr `u`, eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `step_inst_base (mk_inst k MUL [Var sub;Lit 8w] [bits]) v = OK w` by
    (simp[Abbr `w`] >> irule step_MUL >>
     simp[Abbr `v`, eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `step_inst_base (mk_inst l SHR [Var bits;Var data] [dst]) w =
    OK (update_var dst (word_lsr (mload (w2n a) s) (w2n ((32w-nv)*8w))) w)` by
    (irule step_SHR >>
     fs[Abbr `w`, Abbr `v`, Abbr `u`, eval_operand_def,
        lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `t = update_var dst (word_lsr (mload (w2n a) s) (w2n ((32w-nv)*8w))) w` by
    (qpat_x_assum `run_inst_seq _ _ = _` mp_tac >> simp[run_inst_seq_def]) >>
  qexistsl_tac [`u`,`v`,`w`] >> simp[Abbr `u`, Abbr `v`, Abbr `w`]
QED

Theorem sub_ptr_inst_ok[local]:
  op_prov G x = NONE /\ op_prov G y = NONE /\
  op_taint tn x = {} /\ op_taint tn y = {} /\ ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst id SUB [x;y] [z]) s = OK (update_var z w s) ==>
  ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id SUB [x;y] [z]) s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       allocas_from_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke, update_var_def] >>
  rpt strip_tac >> gvs[op_prov_def, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem payload_ghost_update[local]:
  eval_operand (Var dp) s = SOME a ==>
  step_prov PG G (mk_inst id MLOAD [Var dp] [data])
    (update_var data (mload (w2n a) s) s) = DRESTRICT G (COMPL {data}) /\
  step_taint (mk_inst id MLOAD [Var dp] [data]) s
    (update_var data (mload (w2n a) s) s) tn =
    (tn with t_var := tn.t_var |+ (data,mem_word_taint tn.t_mem (w2n a)))
Proof
  strip_tac >>
  `new_site_bytes s (update_var data (mload (w2n a) s) s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss] >>
  simp[step_prov_def, set_prov_def, out_prov_def, mk_inst_def,
       step_taint_def, set_var_taint_def, out_taint_def,
       mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       written_taint_def, store_taint_def, adopt_reset_def,
       imm_taint_def, range_bytes_def, taint_component_equality]
QED

Theorem normalize_ghost_chain[local]:
  ALL_DISTINCT [len;data;sub;bits;dst] /\
  lookup_var len s = SOME nv /\ lookup_var data s = SOME dw /\
  op_prov G (Var len) = NONE /\ op_prov G (Var data) = NONE /\
  op_taint tn (Var len) = {} /\
  u = update_var sub (32w-nv) s /\
  v = update_var bits ((32w-nv)*8w) u /\
  t = update_var dst (word_lsr dw (w2n ((32w-nv)*8w))) v ==>
  step_prov PG G (mk_inst j SUB [Lit 32w;Var len] [sub]) u =
    DRESTRICT G (COMPL {sub}) /\
  step_taint (mk_inst j SUB [Lit 32w;Var len] [sub]) s u tn =
    (tn with t_var := tn.t_var |+ (sub,{})) /\
  step_prov PG (DRESTRICT G (COMPL {sub}))
    (mk_inst k MUL [Var sub;Lit 8w] [bits]) v =
    DRESTRICT G (COMPL {sub} INTER COMPL {bits}) /\
  step_taint (mk_inst k MUL [Var sub;Lit 8w] [bits]) u v
    (tn with t_var := tn.t_var |+ (sub,{})) =
    (tn with t_var := tn.t_var |+ (sub,{}) |+ (bits,{})) /\
  step_prov PG (DRESTRICT G (COMPL {sub} INTER COMPL {bits}))
    (mk_inst l SHR [Var bits;Var data] [dst]) t =
    DRESTRICT G (COMPL {sub} INTER COMPL {bits} INTER COMPL {dst}) /\
  step_taint (mk_inst l SHR [Var bits;Var data] [dst]) v t
    (tn with t_var := tn.t_var |+ (sub,{}) |+ (bits,{})) =
    (tn with t_var := tn.t_var |+ (sub,{}) |+ (bits,{}) |+
       (dst,shift_taint SHR (w2n ((32w-nv)*8w)) (op_taint tn (Var data))))
Proof
  strip_tac >>
  `op_prov G (Lit 32w) = NONE /\ op_taint tn (Lit 32w) = {}` by
    simp[op_prov_def, op_taint_def] >>
  gvs[] >> fs[op_prov_def, op_taint_def, lookup_var_def] >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       step_taint_def, set_var_taint_def, out_taint_def, mk_inst_def,
       mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       written_taint_def, store_taint_def, adopt_reset_def,
       imm_taint_def, range_bytes_def, taint_component_equality,
       new_site_bytes_def, update_var_def, FLOOKUP_DEF, EXTENSION,
       op_taint_def, FLOOKUP_UPDATE, eval_operand_def, lookup_var_def,
       SF CONJ_ss] >>
  simp[op_prov_def, FAPPLY_FUPDATE_THM]
QED

Theorem shift_ptr_inst_ok[local]:
  op_prov G bits = NONE /\ op_prov G data = NONE /\
  op_taint tn bits = {} /\ ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst id SHR [bits;data] [out]) s = OK u ==>
  ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id SHR [bits;data] [out]) s
Proof
  strip_tac >>
  `MEM SHR [GT;SLT;SGT;AND;EQ;SIGNEXTEND;SAR;SHR;SHL;MUL;SDIV]` by simp[] >>
  drule_all convert_scalar_run_shape >> strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       allocas_from_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke, update_var_def] >>
  rpt strip_tac >> gvs[op_prov_def, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem step_cursor[local]:
  ~is_terminator opc ==>
  step_inst_base (mk_inst id opc ops outs) (s with vs_inst_idx := q) =
    exec_result_map (\v. v with vs_inst_idx := q)
      (step_inst_base (mk_inst id opc ops outs) s)
Proof
  strip_tac >> irule step_inst_inst_idx_indep >> simp[mk_inst_def]
QED

Theorem normalize_uniform_checks[local]:
  ALL_DISTINCT [len;data;sub;bits;dst] /\ ~ctx_has_dalloca ctx /\
  lookup_var len s = SOME nv /\ lookup_var data s = SOME dw /\
  op_prov G (Var len) = NONE /\ op_prov G (Var data) = NONE /\
  op_taint tn (Var len) = {} /\
  u = update_var sub (32w-nv) s /\
  v = update_var bits ((32w-nv)*8w) u /\
  t = update_var dst (word_lsr dw (w2n ((32w-nv)*8w))) v /\
  step_inst_base (mk_inst j SUB [Lit 32w;Var len] [sub]) s = OK u /\
  step_inst_base (mk_inst k MUL [Var sub;Lit 8w] [bits]) u = OK v /\
  step_inst_base (mk_inst l SHR [Var bits;Var data] [dst]) v = OK t ==>
  !q. inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst j SUB [Lit 32w;Var len] [sub];
     mk_inst k MUL [Var sub;Lit 8w] [bits];
     mk_inst l SHR [Var bits;Var data] [dst]] (s with vs_inst_idx := q)
    (DRESTRICT G (COMPL {sub} INTER COMPL {bits} INTER COMPL {dst}))
    (tn with t_var := tn.t_var |+ (sub,{}) |+ (bits,{}) |+
      (dst,shift_taint SHR (w2n ((32w-nv)*8w)) (op_taint tn (Var data))))
Proof
  strip_tac >>
  drule_all normalize_ghost_chain >> disch_then (qspec_then `PG` strip_assume_tac) >>
  gvs[] >> gen_tac >>
  simp[inst_seq_ptr_def, step_cursor, is_terminator_def, exec_result_map_def] >>
  conj_tac
  >- (irule sub_ptr_inst_ok >> simp[op_prov_def, op_taint_def] >>
      qexists_tac `32w-nv` >>
      simp[step_cursor, is_terminator_def, exec_result_map_def] >> simp[update_var_def]) >>
  conj_tac
  >- (irule convert_scalar_ptr_inst_ok >>
      simp[op_prov_def, FLOOKUP_DRESTRICT, op_taint_def, FLOOKUP_UPDATE] >>
      qexists_tac `(update_var bits ((32w-nv)*8w) (update_var sub (32w-nv) s))
        with vs_inst_idx := SUC q` >>
      simp[step_cursor, is_terminator_def, exec_result_map_def]) >>
  irule shift_ptr_inst_ok >>
  simp[op_prov_def, FLOOKUP_DRESTRICT, op_taint_def, FLOOKUP_UPDATE] >>
  reverse conj_tac >- fs[op_prov_def] >>
  qexists_tac `(update_var dst (word_lsr dw (w2n ((32w-nv)*8w)))
    (update_var bits ((32w-nv)*8w) (update_var sub (32w-nv) s)))
    with vs_inst_idx := SUC (SUC q)` >>
  simp[step_cursor, is_terminator_def, exec_result_map_def]
QED

Theorem payload_uniform_checks[local]:
  ALL_DISTINCT [len;dp;data;sub;bits;dst] /\ ~ctx_has_dalloca ctx /\
  lookup_var len s = SOME nv /\ lookup_var dp s = SOME a /\
  ptr_covers G tn dp s 32 /\ op_prov G (Var len) = NONE /\
  op_taint tn (Var len) = {} /\
  run_inst_seq [mk_inst i MLOAD [Var dp] [data];
    mk_inst j SUB [Lit 32w;Var len] [sub];
    mk_inst k MUL [Var sub;Lit 8w] [bits];
    mk_inst l SHR [Var bits;Var data] [dst]] s = OK t ==>
  !q. inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst i MLOAD [Var dp] [data];
     mk_inst j SUB [Lit 32w;Var len] [sub];
     mk_inst k MUL [Var sub;Lit 8w] [bits];
     mk_inst l SHR [Var bits;Var data] [dst]] (s with vs_inst_idx := q)
    (DRESTRICT G (COMPL {data} INTER COMPL {sub} INTER COMPL {bits} INTER COMPL {dst}))
    (tn with t_var := tn.t_var |+ (data,mem_word_taint tn.t_mem (w2n a)) |+
      (sub,{}) |+ (bits,{}) |+
      (dst,shift_taint SHR (w2n ((32w-nv)*8w)) (mem_word_taint tn.t_mem (w2n a))))
Proof
  strip_tac >> drule_all normalize_run_endpoint >>
  disch_then (qx_choose_then `u` (qx_choose_then `v` (qx_choose_then `w` strip_assume_tac))) >>
  `eval_operand (Var dp) s = SOME a` by simp[eval_operand_def] >>
  drule_all payload_ghost_update >> strip_tac >>
  gen_tac >> simp[Once inst_seq_ptr_def, step_cursor, is_terminator_def, exec_result_map_def] >>
  conj_tac >- (irule ptr_inst_ok_mload >> simp[eval_operand_def]) >>
  simp[AC INTER_ASSOC INTER_COMM] >>
  irule (SRULE [DRESTRICT_DRESTRICT, op_taint_def, FLOOKUP_UPDATE,
    AC INTER_ASSOC INTER_COMM]
    (Q.INST [`G` |-> `DRESTRICT G (COMPL {data})`,
      `tn` |-> `tn with t_var := tn.t_var |+ (data,mem_word_taint tn.t_mem (w2n a))`]
      normalize_uniform_checks)) >>
  gvs[] >> fs[op_prov_def, op_taint_def, FLOOKUP_DRESTRICT,
    lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  qexists_tac `mload (w2n a) s` >> simp[] >> metis_tac[]
QED

Theorem bytes_word_normalize_fixed_frame:
  ALL_DISTINCT [len;dp;data;sub;bits;dst] /\ ~ctx_has_dalloca ctx /\
  lookup_var len s = SOME (n2w n) /\ n <= 32 /\ lookup_var dp s = SOME a /\
  ptr_covers G tn dp s 32 /\ op_prov G (Var len) = NONE /\
  op_taint tn (Var len) = {} /\
  (!x. w2n a <= x /\ x < w2n a+n ==> x NOTIN tn.t_mem) /\
  run_inst_seq [mk_inst i MLOAD [Var dp] [data];
    mk_inst j SUB [Lit 32w;Var len] [sub];
    mk_inst k MUL [Var sub;Lit 8w] [bits];
    mk_inst l SHR [Var bits;Var data] [dst]] s = OK t ==>
  ?H th.
    (!D q. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst i MLOAD [Var dp] [data];
       mk_inst j SUB [Lit 32w;Var len] [sub];
       mk_inst k MUL [Var sub;Lit 8w] [bits];
       mk_inst l SHR [Var bits;Var data] [dst]] (s with vs_inst_idx := q) H th) /\
    op_prov H (Var dst) = NONE /\ op_taint th (Var dst) = {} /\
    op_prov H (Var bits) = NONE /\ op_taint th (Var bits) = {} /\
    eval_operand (Var bits) t = SOME (n2w (8*(32-n))) /\
    t.vs_memory = s.vs_memory /\ th.t_mem = tn.t_mem /\
    th.t_stor = tn.t_stor /\ th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_current_bb = s.vs_current_bb /\
    t = s with vs_vars := t.vs_vars /\
    (!p. ~MEM p [data;sub;bits;dst] ==> lookup_var p t = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint th (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  drule_all normalize_run_endpoint >>
  disch_then (qx_choose_then `u` (qx_choose_then `v` (qx_choose_then `w` strip_assume_tac))) >>
  `shift_taint SHR (w2n ((32w-n2w n)*8w:256 word))
      (mem_word_taint tn.t_mem (w2n a)) = {}` by
    (simp[shift_count_word] >> irule unsigned_data_window_shift_clean >> simp[]) >>
  qexistsl_tac [`DRESTRICT G (COMPL {data} INTER COMPL {sub} INTER COMPL {bits} INTER COMPL {dst})`,
    `tn with t_var := tn.t_var |+ (data,mem_word_taint tn.t_mem (w2n a)) |+
      (sub,{}) |+ (bits,{}) |+ (dst,{})`] >>
  conj_tac >- (rpt gen_tac >> drule_all payload_uniform_checks >> simp[]) >>
  gvs[] >> simp[op_prov_def, FLOOKUP_DRESTRICT, op_taint_def,
    FLOOKUP_UPDATE, update_var_def, lookup_var_def, eval_operand_def, shift_count_word] >>
  rpt strip_tac >> simp[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED
