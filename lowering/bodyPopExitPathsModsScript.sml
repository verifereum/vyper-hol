(* Count the terminal Pop paths at the actual header cursor. *)
Theory bodyPopExitPathsMods
Ancestors
  bodyPopHeaderMemoryMods bodyPopHeaderSlotMods bodyPopLengthTestMods
  bodyPopLiveCheckMods bodyPopZeroAssertMods bodyPopStaticStoreMods
  fragGasOriginPtrLoop fragGasSeqAbort bodyBinopFragMemory
  venomState venomInst venomExecSemantics ptrDiscipline arithmetic rich_list

Theorem pop_path_join[local]:
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
        (OK t,G1,tn1)) /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G1,tn1) [] out) ==>
  !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] out
Proof
  strip_tac >> gen_tac >>
  irule gas_origin_ptr_path_trans >> qexistsl_tac [`G1`,`t`,`tn1`] >> simp[]
QED

Theorem pop_header_test_cuts[local]:
  isPREFIX (load::a::b::rest) (DROP k code) ==>
  isPREFIX [load] (DROP k code) /\ isPREFIX [a;b] (DROP (k+1) code) /\
  isPREFIX rest (DROP (k+3) code)
Proof
  rewrite_tac[IS_PREFIX_APPEND] >> strip_tac >>
  `DROP k code = [load] ++ [a;b] ++ rest ++ l` by simp[] >>
  `DROP (k+1) code = [a;b] ++ rest ++ l` by
    (once_rewrite_tac[arithmeticTheory.ADD_COMM] >> rewrite_tac[GSYM DROP_DROP_T] >> simp[]) >>
  `DROP (k+3) code = rest ++ l` by
    (once_rewrite_tac[arithmeticTheory.ADD_COMM] >> rewrite_tac[GSYM DROP_DROP_T] >> simp[]) >>
  conj_tac >- (qexists `[a;b] ++ rest ++ l` >> simp[]) >>
  conj_tac >- (qexists `rest ++ l` >> simp[]) >> metis_tac[]
QED

Theorem pop_test_then_zero_exit[local]:
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK s1,G1,tn1)) /\
  s1.vs_inst_idx = k+1 /\ ~s1.vs_halted /\
  lookup_block s1.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst (id+1) ISZERO [Var x0] [x1];
            mk_inst (id+2) ISZERO [Var x1] [x2]] (DROP (k+1) bb.bb_instructions) /\
  get_instruction bb (k+3) = SOME (mk_inst (id+3) ASSERT [Var x2] []) /\
  ALL_DISTINCT [x0;x1;x2] /\ lookup_var x0 s1 = SOME 0w /\
  op_prov G1 (Var x0) = NONE /\ op_taint tn1 (Var x0) = {} /\
  allocas_from lo s1 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s1) ==>
  ?v G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (Abort Revert_abort v,G',tn')) /\
    v.vs_halted /\ v.vs_returndata = [] /\ v.vs_inst_idx = k+3 /\
    allocas_from lo v /\ (ctx_has_dalloca ctx ==> allocas_below_fmp v)
Proof
  strip_tac >>
  qmatch_asmsub_abbrev_tac `isPREFIX code _` >>
  `?q s3 G3 tn3. s3 = q with vs_inst_idx := k+3 /\
     (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s1,G1,tn1) []
       (OK s3,G3,tn3)) /\
     ~s3.vs_halted /\ s3.vs_current_bb = s1.vs_current_bb /\
     allocas_from lo s3 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s3) /\
     lookup_var x2 s3 = SOME 0w /\ op_taint tn3 (Var x2) = {}` by
    (mp_tac (Q.INST [`id` |-> `id+1`, `n` |-> `0w`, `G` |-> `G1`,
       `tn` |-> `tn1`, `explicit` |-> `explicit`, `PG` |-> `PG`] pop_length_test_mods) >>
     impl_tac >- fs[Abbr `code`, ADD_ASSOC] >>
     simp[bool_to_word_def] >> metis_tac[]) >>
  `s3.vs_inst_idx = k+3` by simp[] >>
  `lookup_block s3.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `get_instruction bb s3.vs_inst_idx = SOME (mk_inst (id+3) ASSERT [Var x2] [])` by simp[] >>
  drule_all pop_zero_assert_exit_mods >>
  disch_then (qspecl_then [`explicit`,`PG`,`G3`] mp_tac) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qexistsl_tac [`revert_state (set_returndata [] s3)`,`G3`,`tn3`] >>
  reverse conj_tac >- simp[] >>
  irule pop_path_join >> qexistsl_tac [`G1`,`s1`,`tn1`] >>
  simp[] >>
  irule pop_path_join >> qexistsl_tac [`G3`,`s3`,`tn3`] >> gvs[]
QED

Theorem pop_memory_empty_exit_mods:
  ptr_covers G tn p s 32 /\ lookup_var p s = SOME w /\
  mem_word_taint tn.t_mem (w2n w) = {} /\
  w2n w + 32 <= s.vs_alloca_next /\ mload (w2n w) s = 0w /\
  ALL_DISTINCT [x0;x1;x2] /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id MLOAD [Var p] [x0];
    mk_inst (id+1) ISZERO [Var x0] [x1];
    mk_inst (id+2) ISZERO [Var x1] [x2]] (DROP s.vs_inst_idx bb.bb_instructions) /\
  get_instruction bb (s.vs_inst_idx+3) = SOME (mk_inst (id+3) ASSERT [Var x2] []) ==>
  ?v G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (Abort Revert_abort v,G',tn')) /\
    v.vs_halted /\ v.vs_returndata = [] /\ v.vs_inst_idx = s.vs_inst_idx+3 /\
    allocas_from lo v /\ (ctx_has_dalloca ctx ==> allocas_below_fmp v)
Proof
  strip_tac >> drule pop_header_test_cuts >> strip_tac >>
  `s.vs_inst_idx = s.vs_inst_idx` by simp[] >>
  drule_all pop_header_memory_load_mods >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `~u.vs_halted /\ u.vs_inst_idx = s.vs_inst_idx+1 /\
   lookup_block u.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  irule pop_test_then_zero_exit >>
  rename1 `op_prov G1 (Var x0) = NONE` >>
  rename1 `op_taint tn1 (Var x0) = {}` >>
  qexistsl_tac [`G1`,`bb`,`id`,`u`,`tn1`,`x0`,`x1`,`x2`] >> fs[]
QED

Theorem pop_slot_empty_exit_mods:
  eval_operand hdr s = SOME slot /\ op_taint tn hdr = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  (if tr then tload slot s else sload slot s) = 0w /\
  ALL_DISTINCT [x0;x1;x2] /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id (if tr then TLOAD else SLOAD) [hdr] [x0];
    mk_inst (id+1) ISZERO [Var x0] [x1];
    mk_inst (id+2) ISZERO [Var x1] [x2]] (DROP s.vs_inst_idx bb.bb_instructions) /\
  get_instruction bb (s.vs_inst_idx+3) = SOME (mk_inst (id+3) ASSERT [Var x2] []) ==>
  ?v G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (Abort Revert_abort v,G',tn')) /\
    v.vs_halted /\ v.vs_returndata = [] /\ v.vs_inst_idx = s.vs_inst_idx+3 /\
    allocas_from lo v /\ (ctx_has_dalloca ctx ==> allocas_below_fmp v)
Proof
  strip_tac >> drule pop_header_test_cuts >> strip_tac >>
  drule_all pop_header_slot_load_mods >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`] strip_assume_tac) >>
  rename1 `op_prov G1 (Var x0) = NONE` >>
  rename1 `op_taint tn1 (Var x0) = {}` >>
  rename1 `lookup_var x0 s1 = SOME _` >>
  `lookup_block s1.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  irule pop_test_then_zero_exit >>
  qexistsl_tac [`G1`,`bb`,`id`,`s1`,`tn1`,`x0`,`x1`,`x2`] >> fs[ADD1]
QED

Theorem pop_slice_history[local]:
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

Theorem pop_slot_static_exit_cc_static_mods:
  eval_operand hdr s = SOME slot /\ op_taint tn hdr = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  (if tr then tload slot s else sload slot s) = n /\ n <> 0w /\
  ALL_DISTINCT [x0;x1;x2;x3] /\
  EVERY (\x. hdr <> Var x) [x0;x1;x2;x3] /\
  s.vs_call_ctx.cc_static /\ alloca_history func s /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id (if tr then TLOAD else SLOAD) [hdr] [x0];
    mk_inst (id+1) ISZERO [Var x0] [x1];
    mk_inst (id+2) ISZERO [Var x1] [x2];
    mk_inst (id+3) ASSERT [Var x2] [];
    mk_inst (id+4) SUB [Var x0;Lit 1w] [x3];
    mk_inst (id+5) (if tr then TSTORE else SSTORE) [hdr;Var x3] []]
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?v G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (Abort ExHalt_abort v,G',tn')) /\
    v.vs_halted /\ v.vs_returndata = [] /\ v.vs_inst_idx = s.vs_inst_idx+5 /\
    allocas_from lo v /\ (ctx_has_dalloca ctx ==> allocas_below_fmp v) /\
    v.vs_call_ctx.cc_static
Proof
  strip_tac >> drule pop_header_test_cuts >> strip_tac >>
  drule_all pop_header_slot_load_mods >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`] strip_assume_tac) >>
  rename1 `u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|> = s` >>
  rename1 `op_prov G1 (Var x0) = NONE` >> rename1 `op_taint tn1 (Var x0) = {}` >>
  `lookup_block u.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  qabbrev_tac `code = [mk_inst (id+1) ISZERO [Var x0] [x1];
                       mk_inst (id+2) ISZERO [Var x1] [x2]]` >>
  mp_tac (Q.INST [`id` |-> `id+1`, `G` |-> `G1`, `tn` |-> `tn1`,
    `k` |-> `s.vs_inst_idx`, `s1` |-> `u`] pop_length_test_mods) >>
  impl_tac >- fs[Abbr `code`, ADD_ASSOC, ADD1] >>
  disch_then strip_assume_tac >>
  rename1 `lookup_var x2 s3 = SOME _` >>
  rename1 `op_prov G3 (Var x0) = NONE` >> rename1 `op_taint tn3 (Var x2) = {}` >>
  qpat_assum `u with <|vs_vars := _; vs_inst_idx := _|> = s`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [] o Q.AP_TERM `\z. (z.vs_allocas,z.vs_labels,z.vs_call_ctx)`) >>
  qpat_assum `s3 with <|vs_vars := _; vs_inst_idx := _|> = u`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [] o Q.AP_TERM `\z. (z.vs_allocas,z.vs_labels,z.vs_call_ctx)`) >>
  `alloca_history func u` by
    (irule pop_slice_history >>
     qexistsl_tac [`bb`,`[mk_inst id (if tr then TLOAD else SLOAD) [hdr] [x0]]`,`s`] >>
     simp[ADD1] >> Cases_on `tr` >> fs[mk_inst_def]) >>
  `LENGTH code = 2 /\ EVERY (\i. i.inst_opcode <> ALLOCA) code` by
    simp[Abbr `code`, mk_inst_def] >>
  `alloca_history func s3` by
    (irule pop_slice_history >> qexistsl_tac [`bb`,`code`,`u`] >>
     simp[ADD1, ADD_ASSOC]) >>
  `s3.vs_inst_idx = s.vs_inst_idx+3 /\
   lookup_block s3.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  qabbrev_tac `a = mk_inst (id+3) ASSERT [Var x2] []` >>
  qabbrev_tac `b = mk_inst (id+4) SUB [Var x0;Lit 1w] [x3]` >>
  qabbrev_tac `c = mk_inst (id+5) (if tr then TSTORE else SSTORE) [hdr;Var x3] []` >>
  `isPREFIX [a;b] (DROP s3.vs_inst_idx bb.bb_instructions)` by
    (irule IS_PREFIX_TRANS >> qexists `[a;b;c]` >> fs[]) >>
  `get_instruction bb (s.vs_inst_idx+5) = SOME c` by
    (qpat_assum `isPREFIX [a;b;c] _` (strip_assume_tac o REWRITE_RULE[IS_PREFIX_APPEND]) >>
     `DROP (s.vs_inst_idx+5) bb.bb_instructions = c::l` by
       (`s.vs_inst_idx+5 = 2 + (s.vs_inst_idx+3)` by decide_tac >>
        pop_assum SUBST1_TAC >> once_rewrite_tac[GSYM DROP_DROP_T] >> simp[]) >>
     `[c] ≼ DROP (s.vs_inst_idx+5) bb.bb_instructions` by simp[] >>
     pop_assum (mp_tac o MATCH_MP instruction_prefix_cursor) >> simp[]) >>
  mp_tac (Q.INST [`s` |-> `s3`, `G` |-> `G3`, `tn` |-> `tn3`,
    `k` |-> `s.vs_inst_idx`] (SIMP_RULE bool_ss [LET_THM] pop_live_check_mods)) >>
  impl_tac >-
    (qpat_assum `isPREFIX [a;b] _` mp_tac >> fs[Abbr `a`, Abbr `b`] >>
     conj_tac >> strip_tac >> gvs[]) >>
  disch_then strip_assume_tac >>
  qmatch_asmsub_abbrev_tac `lookup_var x3 s5 = SOME (n-1w)` >>
  suspend "store"
QED

Resume pop_slot_static_exit_cc_static_mods[store]:
  `s5.vs_inst_idx = s.vs_inst_idx+5 /\
   lookup_block s5.vs_current_bb func.fn_blocks = SOME bb` by
    (reverse conj_tac >- simp[] >> simp[Abbr `s5`]) >>
  `s5.vs_call_ctx = s3.vs_call_ctx` by
    (qpat_assum `s5 with <|vs_vars := _; vs_inst_idx := _|> = s3`
      (mp_tac o Q.AP_TERM `\z. z.vs_call_ctx`) >> simp[]) >>
  `s5.vs_call_ctx.cc_static` by simp[] >>
  `eval_operand hdr s3 = SOME slot /\ op_taint tn3 hdr = {}` by
    (Cases_on `hdr` >> fs[eval_operand_def, listTheory.EVERY_DEF, op_taint_def]) >>
  `eval_operand hdr s5 = SOME slot /\ op_taint tn5 hdr = {}` by
    (conj_tac >- fs[] >> Cases_on `hdr` >> fs[listTheory.EVERY_DEF, op_taint_def]) >>
  `eval_operand (Var x3) s5 = SOME (n-1w)` by simp[eval_operand_def] >>
  `get_instruction bb s5.vs_inst_idx =
    SOME (mk_inst (id+5) (if tr then TSTORE else SSTORE) [hdr;Var x3] [])` by simp[Abbr `c`] >>
  drule_all pop_static_store_exit_mods >>
  disch_then (qspecl_then [`explicit`,`PG`,`G5`] mp_tac) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qexistsl_tac [`halt_state (set_returndata [] s5)`,`G5`,`tn5`] >>
  reverse conj_tac >- simp[halt_state_def,set_returndata_def] >>
  irule pop_path_join >> qexistsl_tac [`G1`,`u`,`tn1`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule pop_path_join >> qexistsl_tac [`G3`,`s3`,`tn3`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule pop_path_join >> qexistsl_tac [`G5`,`s5`,`tn5`] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Finalise pop_slot_static_exit_cc_static_mods

Theorem pop_slot_static_exit_mods:
  eval_operand hdr s = SOME slot /\ op_taint tn hdr = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  (if tr then tload slot s else sload slot s) = n /\ n <> 0w /\
  ALL_DISTINCT [x0;x1;x2;x3] /\
  EVERY (\x. hdr <> Var x) [x0;x1;x2;x3] /\
  s.vs_call_ctx.cc_static /\ alloca_history func s /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id (if tr then TLOAD else SLOAD) [hdr] [x0];
    mk_inst (id+1) ISZERO [Var x0] [x1];
    mk_inst (id+2) ISZERO [Var x1] [x2];
    mk_inst (id+3) ASSERT [Var x2] [];
    mk_inst (id+4) SUB [Var x0;Lit 1w] [x3];
    mk_inst (id+5) (if tr then TSTORE else SSTORE) [hdr;Var x3] []]
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?v G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (Abort ExHalt_abort v,G',tn')) /\
    v.vs_halted /\ v.vs_returndata = [] /\ v.vs_inst_idx = s.vs_inst_idx+5 /\
    allocas_from lo v /\ (ctx_has_dalloca ctx ==> allocas_below_fmp v)
Proof
  disch_then (mp_tac o MATCH_MP pop_slot_static_exit_cc_static_mods) >>
  strip_tac >> qexistsl_tac [`v`,`G'`,`tn'`] >> simp[]
QED
