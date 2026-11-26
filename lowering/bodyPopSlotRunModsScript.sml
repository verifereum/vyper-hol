(* Compose the five counted cuts of a successful storage/transient Pop. *)
Theory bodyPopSlotRunMods
Ancestors
  bodyPopHeaderSlotMods bodyPopLengthTestMods bodyPopLiveCheckMods
  bodyPopHeaderWriteSlotMods bodyPopAddressSlotMods
  fragGasOriginPtrLoop fragGasSeqAbort fragExec instIdxIndep
  exprSimPopNestedBase exprLoweringProps allocaHistory bodyBinopFragMemory
  venomState venomInst venomExecSemantics ptrDiscipline arithmetic rich_list

Theorem slot_pop_join_path[local]:
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
          (OK t,G1,tn1)) /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G1,tn1) [] out) ==>
  !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] out
Proof
  strip_tac >> gen_tac >> irule gas_origin_ptr_path_trans >>
  qexistsl_tac [`G1`,`t`,`tn1`] >> simp[]
QED

Theorem slot_pop_cut_history[local]:
  alloca_history func s /\ t.vs_allocas = s.vs_allocas /\
  t.vs_current_bb = s.vs_current_bb /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  t.vs_inst_idx = s.vs_inst_idx + LENGTH code /\
  EVERY (\i. i.inst_opcode <> ALLOCA) code ==> alloca_history func t
Proof
  strip_tac >>
  `t with vs_inst_idx := s.vs_inst_idx + LENGTH code = t` by
    simp[venom_state_component_equality] >>
  pop_assum (SUBST1_TAC o SYM) >> irule alloca_history_no_alloca_slice >>
  fs[IS_PREFIX_APPEND]
QED

Theorem slot_pop_prefix_cut[local]:
  isPREFIX (front ++ rest) (DROP k code) ==>
  isPREFIX front (DROP k code) /\
  isPREFIX rest (DROP (k + LENGTH front) code)
Proof
  simp_tac bool_ss [IS_PREFIX_APPEND] >>
  disch_then (qx_choose_then `tail` assume_tac) >> conj_tac
  >- (qexists `rest ++ tail` >> fs[APPEND_ASSOC]) >>
  qexists `tail` >>
  once_rewrite_tac[ADD_COMM] >> rewrite_tac[GSYM DROP_DROP_T] >>
  asm_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND]
QED

(* Run each counted slice at the original cursor before composing the raw run. *)
Theorem slot_pop_run_at[local]:
  run_inst_seq code s = OK q /\
  t = (q with vs_inst_idx := j) /\
  EVERY (\i. ~is_terminator i.inst_opcode) code ==>
  !k. run_inst_seq code (s with vs_inst_idx := k) = OK (t with vs_inst_idx := k)
Proof
  strip_tac >> simp[run_inst_seq_inst_idx,exec_result_map_def]
QED

Theorem slot_pop_run_cons[local]:
  run_inst_seq front s = OK t /\ run_inst_seq rest t = OK u ==>
  run_inst_seq (front ++ rest) s = OK u
Proof
  strip_tac >>
  `run_inst_seq (front ++ rest) s = run_inst_seq rest t` by
    (irule run_inst_seq_append >> first_assum ACCEPT_TAC) >> simp[]
QED

Theorem pop_slot_positive_run_mods:
  eval_operand hdr s = SOME slot /\ op_prov G hdr = NONE /\ op_taint tn hdr = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  (if tr then tload slot s else sload slot s) = n /\ n <> 0w /\
  ALL_DISTINCT [x0;x1;x2;x3;x4;x5;x6] /\
  (!x. hdr = Var x ==> ~MEM x [x0;x1;x2;x3;x4;x5;x6]) /\
  ~s.vs_call_ctx.cc_static /\ alloca_history func s /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (nested_pop_suffix hdr tr id esz x0 x1 x2 x3 x4 x5 x6)
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?u Gf tf.
    run_inst_seq (nested_pop_suffix hdr tr id esz x0 x1 x2 x3 x4 x5 x6) s = OK u /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
       (OK (u with vs_inst_idx := s.vs_inst_idx+9),Gf,tf)) /\
    u = (if tr then tstore slot (n-1w) s else sstore slot (n-1w) s)
          with vs_vars := u.vs_vars /\
    lookup_var x6 u = SOME (slot + 1w + (n-1w) * n2w esz) /\
    op_prov Gf (Var x6) = NONE /\ op_taint tf (Var x6) = {} /\
    (!x. ~MEM x [x0;x1;x2;x3;x4;x5;x6] ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x)) /\
    tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
    (if tr then tf.t_trans = key_update tn.t_trans slot {} /\ tf.t_stor = tn.t_stor
     else tf.t_stor = key_update tn.t_stor slot {} /\ tf.t_trans = tn.t_trans) /\
    alloca_history func (u with vs_inst_idx := s.vs_inst_idx+9) /\
    allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u)
Proof
  strip_tac >>
  qabbrev_tac `k = s.vs_inst_idx` >>
  qabbrev_tac `il = mk_inst id (if tr then TLOAD else SLOAD) [hdr] [x0]` >>
  qabbrev_tac `test = [mk_inst (id+1) ISZERO [Var x0] [x1];
                       mk_inst (id+2) ISZERO [Var x1] [x2]]` >>
  qabbrev_tac `popcheck = [mk_inst (id+3) ASSERT [Var x2] [];
                        mk_inst (id+4) SUB [Var x0; Lit 1w] [x3]]` >>
  qabbrev_tac `iw = mk_inst (id+5) (if tr then TSTORE else SSTORE) [hdr;Var x3] []` >>
  qmatch_asmsub_abbrev_tac `isPREFIX code _` >>
  qabbrev_tac `slotpop_suffix = DROP 6 code` >>
  `code = [il] ++ test ++ popcheck ++ [iw] ++ slotpop_suffix` by
    (unabbrev_all_tac >> simp[nested_pop_suffix_def]) >>
  `LENGTH test = 2 /\ LENGTH popcheck = 2` by
    (unabbrev_all_tac >> simp[]) >>
  `isPREFIX [il] (DROP k bb.bb_instructions) /\
   isPREFIX test (DROP (k+1) bb.bb_instructions) /\
   isPREFIX popcheck (DROP (k+3) bb.bb_instructions) /\
   get_instruction bb (k+5) = SOME iw /\
   isPREFIX slotpop_suffix (DROP (k+6) bb.bb_instructions)` by
    (qpat_assum `isPREFIX code _` mp_tac >>
     qpat_assum `code = _` (fn th => PURE_REWRITE_TAC [th,GSYM APPEND_ASSOC]) >>
     disch_then (mp_tac o MATCH_MP slot_pop_prefix_cut) >> simp_tac bool_ss [LENGTH] >>
     strip_tac >>
     qpat_assum `isPREFIX (test ++ _) _` (mp_tac o MATCH_MP slot_pop_prefix_cut) >>
     asm_simp_tac bool_ss [ADD_ASSOC] >> strip_tac >>
     qpat_assum `isPREFIX (popcheck ++ _) _` (mp_tac o MATCH_MP slot_pop_prefix_cut) >>
     asm_simp_tac bool_ss [ADD_ASSOC] >> strip_tac >>
     qpat_assum `isPREFIX ([iw] ++ slotpop_suffix) _`
       (mp_tac o MATCH_MP instruction_prefix_cursor o REWRITE_RULE [APPEND]) >>
     fs[ADD1,GSYM ADD_ASSOC]) >>
  `s.vs_inst_idx = k` by simp[Abbr `k`] >>
  `isPREFIX [mk_inst id (if tr then TLOAD else SLOAD) [hdr] [x0]]
     (DROP s.vs_inst_idx bb.bb_instructions)` by fs[Abbr `il`] >>
  drule_all pop_header_slot_load_mods >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`]
    (qx_choosel_then [`q1`,`s1`,`G1`,`tn1`] strip_assume_tac)) >>
  `s1.vs_inst_idx = k+1 /\ lookup_block s1.vs_current_bb func.fn_blocks = SOME bb` by simp[ADD1] >>
  mp_tac (Q.INST [`id` |-> `id+1`, `G` |-> `G1`, `tn` |-> `tn1`,
    `code` |-> `test`] pop_length_test_mods) >>
  impl_tac >- fs[Abbr `test`, Abbr `k`, GSYM ADD_ASSOC] >>
  disch_then (qx_choosel_then [`q3`,`s3`,`G3`,`tn3`] strip_assume_tac) >>
  qpat_assum `s1 with <|vs_vars := _; vs_inst_idx := _|> = s`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [] o Q.AP_TERM `\z. (z.vs_allocas,z.vs_call_ctx)`) >>
  qpat_assum `s3 with <|vs_vars := _; vs_inst_idx := _|> = s1`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [] o Q.AP_TERM `\z. (z.vs_allocas,z.vs_call_ctx)`) >>
  `alloca_history func s1` by
    (irule slot_pop_cut_history >> qexistsl_tac [`bb`,`[il]`,`s`] >> simp[ADD1] >>
     Cases_on `tr` >> fs[Abbr `il`,mk_inst_def]) >>
  `alloca_history func s3` by
    (irule slot_pop_cut_history >> qexistsl_tac [`bb`,`test`,`s1`] >>
     simp[GSYM ADD_ASSOC] >> simp[Abbr `test`, mk_inst_def]) >>
  `s3.vs_inst_idx = k+3 /\ lookup_block s3.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  mp_tac (Q.INST [`s` |-> `s3`, `G` |-> `G3`, `tn` |-> `tn3`]
    (SIMP_RULE bool_ss [LET_THM] pop_live_check_mods)) >>
  impl_tac >- fs[Abbr `popcheck`] >>
  disch_then (qx_choosel_then [`q5`,`G5`,`tn5`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `lookup_var x3 s5 = SOME (n-1w)` >>
  suspend "store"
QED

Resume pop_slot_positive_run_mods[store]:
  `s5.vs_inst_idx = k+5 /\ lookup_block s5.vs_current_bb func.fn_blocks = SOME bb` by
    (reverse conj_tac >- simp[] >> simp[Abbr `s5`]) >>
  `s5.vs_call_ctx = s3.vs_call_ctx` by
    (qpat_assum `s5 with <|vs_vars := _; vs_inst_idx := _|> = s3`
       (mp_tac o Q.AP_TERM `\z. z.vs_call_ctx`) >> simp[]) >>
  `~s5.vs_call_ctx.cc_static` by simp[] >>
  `EVERY (\x. hdr <> Var x) [x0;x1;x2;x3;x4;x5;x6]` by
    (qpat_assum `!x. hdr = Var x ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp_tac bool_ss [listTheory.EVERY_MEM] >> metis_tac[]) >>
  `s3.vs_labels = s.vs_labels` by
    (qpat_assum `s1 with <|vs_vars := _; vs_inst_idx := _|> = s`
       (assume_tac o SIMP_RULE (srw_ss()) [] o Q.AP_TERM `\z. z.vs_labels`) >>
     qpat_assum `s3 with <|vs_vars := _; vs_inst_idx := _|> = s1`
       (assume_tac o SIMP_RULE (srw_ss()) [] o Q.AP_TERM `\z. z.vs_labels`) >> simp[]) >>
  `eval_operand hdr s3 = SOME slot /\ op_taint tn3 hdr = {} /\ op_prov G3 hdr = NONE` by
    (Cases_on `hdr` >> fs[eval_operand_def,op_taint_def,op_prov_def]) >>
  `eval_operand hdr s5 = SOME slot /\ op_taint tn5 hdr = {} /\ op_prov G5 hdr = NONE` by
    (conj_tac >- fs[] >> Cases_on `hdr` >> fs[op_taint_def,op_prov_def]) >>
  `get_instruction bb s5.vs_inst_idx =
     SOME (mk_inst (id+5) (if tr then TSTORE else SSTORE) [hdr;Var x3] [])` by
    simp[Abbr `iw`] >>
  drule_all pop_header_slot_store_mods >>
  disch_then (qspecl_then [`explicit`,`PG`,`G5`]
    (qx_choosel_then [`q6`,`s6`,`tn6`] strip_assume_tac)) >>
  `s6.vs_inst_idx = k+6 /\ lookup_block s6.vs_current_bb func.fn_blocks = SOME bb` by
    simp[GSYM ADD_ASSOC] >>
  `op_prov G5 (Var x3) = NONE /\ op_taint tn6 (Var x3) = {} /\
   lookup_var x3 s6 = SOME (n-1w) /\ eval_operand hdr s6 = SOME slot /\ op_taint tn6 hdr = {}` by
    fs[GSYM eval_operand_def] >>
  mp_tac (Q.INST [`s` |-> `s6`, `G` |-> `G5`, `tn` |-> `tn6`, `m` |-> `n-1w`]
    (SIMP_RULE bool_ss [LET_THM] pop_address_slot_mods)) >>
  impl_tac >- fs[Abbr `slotpop_suffix`,Abbr `code`] >>
  disch_then (qx_choosel_then [`q9`,`G9`,`tn9`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `lookup_var x6 s9 = SOME (slot + 1w + (n-1w) * n2w esz)` >>
  suspend "join"
QED

Resume pop_slot_positive_run_mods[join]:
  `EVERY (\i. ~is_terminator i.inst_opcode) code` by
    (simp_tac (srw_ss()) [Abbr `code`,nested_pop_suffix_def,mk_inst_def] >>
     Cases_on `tr` >> simp[is_terminator_def]) >>
  qpat_x_assum `EVERY _ code` mp_tac >>
  qpat_assum `code = _` (fn th =>
    disch_then (strip_assume_tac o REWRITE_RULE [th,listTheory.EVERY_APPEND])) >>
  `run_inst_seq [il] s = OK q1` by fs[Abbr `il`] >>
  `run_inst_seq popcheck s3 = OK q5` by fs[Abbr `popcheck`] >>
  `run_inst_seq [iw] s5 = OK q6` by fs[Abbr `iw`] >>
  `run_inst_seq slotpop_suffix s6 = OK q9` by fs[Abbr `slotpop_suffix`,Abbr `code`] >>
  `run_inst_seq [il] (s with vs_inst_idx := k) = OK (s1 with vs_inst_idx := k)` by
    (irule slot_pop_run_at >> (reverse conj_tac >- first_assum ACCEPT_TAC) >> qexistsl_tac [`SUC s.vs_inst_idx`,`q1`] >> simp[]) >>
  `run_inst_seq test (s1 with vs_inst_idx := k) = OK (s3 with vs_inst_idx := k)` by
    (irule slot_pop_run_at >> (reverse conj_tac >- first_assum ACCEPT_TAC) >> qexistsl_tac [`k+3`,`q3`] >> simp[]) >>
  `run_inst_seq popcheck (s3 with vs_inst_idx := k) = OK (s5 with vs_inst_idx := k)` by
    (irule slot_pop_run_at >> (reverse conj_tac >- first_assum ACCEPT_TAC) >> qexistsl_tac [`k+5`,`q5`] >> simp[Abbr `s5`]) >>
  `run_inst_seq [iw] (s5 with vs_inst_idx := k) = OK (s6 with vs_inst_idx := k)` by
    (irule slot_pop_run_at >> (reverse conj_tac >- first_assum ACCEPT_TAC) >> qexistsl_tac [`s5.vs_inst_idx+1`,`q6`] >> simp[]) >>
  `run_inst_seq slotpop_suffix (s6 with vs_inst_idx := k) = OK (s9 with vs_inst_idx := k)` by
    (irule slot_pop_run_at >> (reverse conj_tac >- first_assum ACCEPT_TAC) >> qexistsl_tac [`k+9`,`q9`] >> simp[Abbr `s9`]) >>
  `run_inst_seq code s = OK (s9 with vs_inst_idx := k)` by
    (qpat_assum `code = _` (fn th => PURE_REWRITE_TAC [th,GSYM APPEND_ASSOC]) >>
     `s with vs_inst_idx := k = s` by simp[Abbr `k`] >>
     pop_assum (SUBST1_TAC o SYM) >>
     irule slot_pop_run_cons >> qexists `s1 with vs_inst_idx := k` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule slot_pop_run_cons >> qexists `s3 with vs_inst_idx := k` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule slot_pop_run_cons >> qexists `s5 with vs_inst_idx := k` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule slot_pop_run_cons >> qexists `s6 with vs_inst_idx := k` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "endpoint"
QED

Resume pop_slot_positive_run_mods[endpoint]:
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK s9,G9,tn9)` by
    (irule slot_pop_join_path >> qexistsl_tac [`G1`,`s1`,`tn1`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule slot_pop_join_path >> qexistsl_tac [`G3`,`s3`,`tn3`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule slot_pop_join_path >> qexistsl_tac [`G5`,`s5`,`tn5`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule slot_pop_join_path >> qexistsl_tac [`G5`,`s6`,`tn6`] >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  mp_tac nested_pop_suffix_run >>
  impl_tac >-
    (conj_tac >-
       (qpat_assum `ALL_DISTINCT _` mp_tac >> simp_tac (srw_ss()) [EQ_SYM_EQ]) >>
     simp[]) >>
  disch_then (qx_choose_then `raw` strip_assume_tac) >>
  `raw with vs_inst_idx := k + 9 = s9` by
    (`raw = (s9 with vs_inst_idx := k)` by
       (qpat_assum `run_inst_seq code s = _` mp_tac >>
        qpat_assum `run_inst_seq (nested_pop_suffix _ _ _ _ _ _ _ _ _ _ _) s = OK raw`
          (fn th => simp_tac (srw_ss()) [Abbr `code`,th]) >> simp[EQ_SYM_EQ]) >>
     pop_assum SUBST1_TAC >> simp[Abbr `s9`]) >>
  qexistsl_tac [`raw`,`G9`,`tn9`] >>
  conj_tac >- (simp_tac (srw_ss()) [Abbr `code`] >> first_assum ACCEPT_TAC) >>
  conj_tac >- simp[] >>
  conj_tac >-
    (qpat_assum `raw = (_ with vs_vars := _)` mp_tac >>
     qpat_assum `(if tr then _ else _) = n` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `tr` >> simp[] >> metis_tac[]) >>
  conj_tac >- (qpat_assum `lookup_var x6 raw = _` mp_tac >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qx_gen_tac `x` >> strip_tac >>
      qpat_assum `!q. ~MEM q [x4;x5;x6] ==> _` (qspec_then `x` mp_tac) >>
      qpat_assum `!q. q <> x3 ==> _` (qspec_then `x` mp_tac) >>
      qpat_assum `!q. q <> x1 /\ q <> x2 ==> _` (qspec_then `x` mp_tac) >>
      qpat_assum `!q. q <> x0 ==> _` (qspec_then `x` mp_tac) >>
      qpat_assum `!op. eval_operand op s6 = _ /\ _` (qspec_then `Var x` mp_tac) >>
      fs[]) >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- (Cases_on `tr` >> fs[]) >>
  conj_tac >- simp[] >>
  qpat_assum `raw with vs_inst_idx := k + 9 = s9` (fn th =>
    qpat_assum `allocas_from lo s9` (mp_tac o REWRITE_RULE [GSYM th]) >>
    qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s9`
      (mp_tac o REWRITE_RULE [GSYM th])) >>
  simp[exprPtrUnwrapFramesTheory.copy_allocas_inst_idx]
QED

Finalise pop_slot_positive_run_mods
