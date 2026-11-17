Theory bodyFullRawCallBytes
Ancestors
  exprSimRawCall fragGasSeqPtr wordLoadStorePtr bodyFullGhostFrame
  rawCallBufferPtr representationCleanPtr builtinSimple emitHelper compileEnv
  venomState venomInst fragExec exprLoweringProps list ptrDisciplineEmptyTaint
  augAssignPtrScalarRun augAssignPtrScalarCertificate instSeqComposePtr
  bodyFullRawCallCallFrame instIdxIndep ghostPcTransportPtr
  allocaHistoryFragment
Libs
  monadsyntax

Theorem raw_call_bytes_success_full_path:
  (do len <- emit_op RETURNDATASIZE [];
      cmp <- emit_op LT [len;Lit (n2w n)];
      capped <- compile_select cmp len (Lit (n2w n));
      emit_void MSTORE [Var p;capped]; return (Var p) od) sa = (result,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  0 < n /\ n < dimword (:256) /\
  LENGTH s.vs_returndata < dimword (:256) /\
  n <= rounded /\ ((n+31) DIV 32)*32 <= rounded /\
  lookup_var p s = SOME (n2w b) /\ not_fresh_at sa p /\
  ptr_covers G tn p s (32+rounded) /\
  lo <= b /\ b+32+rounded < dimword (:256) /\
  b+32+rounded <= s.vs_alloca_next /\
  mem_bytes_at (b+32) (LENGTH (TAKE n s.vs_returndata)) s.vs_memory =
    TAKE n s.vs_returndata /\
  (!i. b+32 <= i /\ i < b+32+LENGTH (TAKE n s.vs_returndata) ==>
       i NOTIN tn.t_mem) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ allocas_from lo s /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?Gf tf.
    result = Var p /\
    (!D explicit.
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
        (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tf)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    lookup_var p t = SOME (n2w b) /\
    ptr_covers Gf tf p t (32+rounded) /\
    raw_call_finish_view t = raw_call_finish_view
      (mstore b (n2w (MIN (LENGTH s.vs_returndata) n)) s) /\
    tf.t_mem = tn.t_mem DIFF {i | b <= i /\ i < b+32} /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x)) /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
      val_in_memory (BaseTV (BytesT (Dynamic n)))
        (BytesV (TAKE n s.vs_returndata)) b mem) /\
    (!D d cenv cx es.
      ghost_inv_at D lo d cenv cx es G tn s /\
      local_ptrs_rel func cenv es.scopes s /\ local_ptrs_reserved cenv sa /\
      (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
      (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
      (!name lb k. local_region cenv es.scopes s name lb k ==>
        lb+k <= b \/ b+32 <= lb) ==>
      ghost_inv_at D lo d cenv cx es Gf tf
        (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
      ghost_kept_at lo cenv es sa G tn s Gf tf)
Proof
  strip_tac >>
  `eval_operand (Var p) s = SOME (n2w b)` by simp[eval_operand_def] >>
  drule raw_call_success_run_aged >> simp[] >>
  disch_then (qspecl_then [`s`, `n2w b`] mp_tac) >> simp[] >> strip_tac >>
  gvs[] >>
  qpat_x_assum `comp_bind _ _ _ = _` mp_tac >>
  simp[compile_select_def, comp_bind_def, emit_op_def, fresh_var_def,
       fresh_id_def, comp_ignore_bind_def, comp_return_def, emit_def,
       emit_void_def] >> strip_tac >> gvs[] >>
  qabbrev_tac `a0 = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `a1 = STRING #"%" (toString (sa.cs_next_var+1))` >>
  qabbrev_tac `a2 = STRING #"%" (toString (sa.cs_next_var+2))` >>
  qabbrev_tac `a3 = STRING #"%" (toString (sa.cs_next_var+3))` >>
  qabbrev_tac `a4 = STRING #"%" (toString (sa.cs_next_var+4))` >>
  qmatch_asmsub_abbrev_tac `fn_has_code sa sc func` >>
  qpat_x_assum `run_inst_seq _ _ = OK t` mp_tac >>
  simp[emitted_insts_def, Abbr `sc`] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  strip_tac >>
  `ALL_DISTINCT [a0;a1;a2;a3;a4]` by
    simp[Abbr `a0`, Abbr `a1`, Abbr `a2`, Abbr `a3`, Abbr `a4`,
         builtinIntClampTheory.fresh_var_name_eq] >>
  `!x. not_fresh_at sa x ==> ~MEM x [a0;a1;a2;a3;a4]` by
    (simp[loweringStateRelDefsTheory.not_fresh_at_def,
          Abbr `a0`, Abbr `a1`, Abbr `a2`, Abbr `a3`, Abbr `a4`] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL, arithmeticTheory.LESS_EQ_ADD]) >>
  `p <> a0 /\ p <> a1 /\ p <> a2 /\ p <> a3 /\ p <> a4` by metis_tac[MEM] >>
  fs[ALL_DISTINCT, lookup_var_def] >>
  qpat_x_assum `run_inst_seq _ _ = OK t` mp_tac >>
  simp[run_inst_seq_def, venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       mk_inst_def, venomExecSemanticsTheory.exec_read0_def,
       venomExecSemanticsTheory.exec_pure2_def,
       venomExecSemanticsTheory.exec_write2_def, eval_operand_def,
       lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `mstore b capword u = t` >>
  `capword = n2w (MIN (LENGTH s.vs_returndata) n)` by
    (simp[Abbr `capword`] >> Cases_on `LENGTH s.vs_returndata < n` >>
     simp[venomExecSemanticsTheory.bool_to_word_def, arithmeticTheory.MIN_DEF] >>
     wordsLib.WORD_DECIDE_TAC) >>
  qabbrev_tac `Gf = DRESTRICT G (COMPL {a0;a1;a2;a3;a4})` >>
  qabbrev_tac `tp = tn with t_var :=
    tn.t_var |+ (a0,{}) |+ (a1,{}) |+ (a2,{}) |+ (a3,{}) |+ (a4,{})` >>
  qabbrev_tac `tf = tp with t_mem := tn.t_mem DIFF {i | b <= i /\ i < b+32}` >>
  `!x. not_fresh_at sa x ==>
     lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
     op_taint tp (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> first_x_assum drule >>
     simp[Abbr `u`, Abbr `Gf`, Abbr `tp`, lookup_var_def,
       ptrDisciplineTheory.op_taint_def, finite_mapTheory.FLOOKUP_UPDATE,
       finite_mapTheory.FLOOKUP_DRESTRICT]) >>
  qmatch_asmsub_abbrev_tac `fn_has_code sa sc func` >>
  `!D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sc) s Gf tf` by
    suspend "checks" >>
  qabbrev_tac `code = emitted_insts sa sc` >>
  `code =
    [mk_inst sa.cs_next_id RETURNDATASIZE [] [a0];
     mk_inst (sa.cs_next_id+1) LT [Var a0;Lit (n2w n)] [a1];
     mk_inst (sa.cs_next_id+2) XOR [Var a0;Lit (n2w n)] [a2];
     mk_inst (sa.cs_next_id+3) MUL [Var a1;Var a2] [a3];
     mk_inst (sa.cs_next_id+4) XOR [Lit (n2w n);Var a3] [a4];
     mk_inst (sa.cs_next_id+5) MSTORE [Var p;Var a4] []]` by
    (simp[Abbr `code`, emitted_insts_def, Abbr `sc`] >>
     pure_rewrite_tac [GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
     simp[]) >>
  `run_inst_seq code s = OK t` by
    (qpat_x_assum `mstore _ _ _ = t` (SUBST1_TAC o SYM) >>
     simp[Abbr `u`, Abbr `capword`, run_inst_seq_def, venomExecSemanticsTheory.step_inst_base_opcode_eqs,
      mk_inst_def, venomExecSemanticsTheory.exec_read0_def,
      venomExecSemanticsTheory.exec_pure2_def,
      venomExecSemanticsTheory.exec_write2_def, eval_operand_def,
      lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  `?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    DROP s.vs_inst_idx bb.bb_instructions = code ++ rest` by
    (qpat_x_assum `fn_has_code sa sc func` mp_tac >>
     simp[fn_has_code_def, Abbr `sc`, rich_listTheory.IS_PREFIX_APPEND] >>
     strip_tac >> goal_assum (drule_at Any) >>
     qexists_tac `l` >>
     simp[] >>
     pure_rewrite_tac [GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
     simp[]) >>
  pop_assum strip_assume_tac >>
  `LENGTH sc.cs_current_insts = s.vs_inst_idx + LENGTH code` by
    simp[Abbr `code`, emitted_insts_def, Abbr `sc`] >>
  qexistsl_tac [`Gf`, `tf`] >>
  conj_tac >- suspend "path" >>
  conj_tac >- suspend "halted" >>
  conj_tac >- suspend "block" >>
  conj_tac >- suspend "history" >>
  conj_tac >- suspend "allocas" >>
  conj_tac >- suspend "next" >>
  conj_tac >- suspend "lookup" >>
  conj_tac >- suspend "covers" >>
  conj_tac >- suspend "memtaint" >>
  conj_tac >- suspend "stor" >>
  conj_tac >- suspend "trans" >>
  conj_tac >- suspend "imm" >>
  conj_tac >- suspend "old" >>
  conj_tac >- suspend "robust" >>
  suspend "frame"
QED

Resume raw_call_bytes_success_full_path[checks]:
  gen_tac >> simp[emitted_insts_def, Abbr `sc`] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[Once inst_seq_ptr_def, raw_call_returndatasize_step_base] >>
  conj_tac >- (
    simp[ptrSafeRunTheory.ptr_inst_ok_def, ptrDisciplineTheory.access_ok_def,
      ptrDisciplineTheory.taint_ok_def, mk_inst_def,
      codegenRelTheory.source_memory_write_ranges_def,
      contextCodegenRelTheory.source_memory_read_ranges_def,
      venomExecSemanticsTheory.step_inst_non_invoke,
      raw_call_returndatasize_step_base, update_var_def] >>
    rpt strip_tac >> gvs[]) >>
  simp[ptrDisciplineTheory.step_prov_def, ptrDisciplineTheory.set_prov_def,
    ptrDisciplineTheory.out_prov_def, ptrDisciplineTheory.step_taint_def,
    ptrDisciplineTheory.mem_taint_def, new_site_bytes_unchanged,
    ptrDisciplineTheory.step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
    ptrDisciplineTheory.range_bytes_def, ptrDisciplineTheory.written_taint_def,
    ptrDisciplineTheory.set_var_taint_def, ptrDisciplineTheory.out_taint_def,
    ptrDisciplineTheory.adopt_reset_def, ptrDisciplineTheory.store_taint_def,
    ptrDisciplineTheory.imm_taint_def, mk_inst_def, update_var_def] >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr D lo ctx func PG G0 tn0 _ s0 Gf tf` >>
  qabbrev_tac `C =
    [mk_inst (sa.cs_next_id+1) LT [Var a0;Lit (n2w n)] [a1];
     mk_inst (sa.cs_next_id+2) XOR [Var a0;Lit (n2w n)] [a2];
     mk_inst (sa.cs_next_id+3) MUL [Var a1;Var a2] [a3];
     mk_inst (sa.cs_next_id+4) XOR [Lit (n2w n);Var a3] [a4]]` >>
  `scalar_code {a0} C` by
    simp[Abbr `C`, scalar_code_def, scalar_shape_def,
         scalar_binary_def, scalar_available_def, mk_inst_def] >>
  `?H tm. inst_seq_ptr D lo ctx func PG G0 tn0 C s0 H tm` by
    (irule scalar_code_inst_seq_ptr_lo >>
     simp[Abbr `s0`, ptrDisciplineTheory.allocas_from_def] >>
     conj_tac >- (fs[ptrDisciplineTheory.allocas_from_def] >> metis_tac[]) >>
     qexists_tac `{a0}` >>
     simp[Abbr `G0`, Abbr `tn0`,
       ptrDisciplineTheory.op_prov_def, ptrDisciplineTheory.op_taint_def,
       finite_mapTheory.FLOOKUP_DRESTRICT, finite_mapTheory.FLOOKUP_UPDATE,
       ptrDisciplineTheory.allocas_from_def]) >>
  pop_assum strip_assume_tac >>
  `H = Gf /\ tm = tp` by (
    qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ C _ _ _` mp_tac >>
    simp[Abbr `C`, Abbr `s0`, inst_seq_ptr_def,
      venomExecSemanticsTheory.step_inst_base_opcode_eqs,
      mk_inst_def, venomExecSemanticsTheory.exec_pure2_def, eval_operand_def,
      lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE, update_var_def] >>
    disch_then (mp_tac o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) >>
    strip_tac >> conj_tac >- (
      qpat_x_assum `H = _` SUBST1_TAC >>
      simp[Abbr `G0`, Abbr `Gf`, ptrDisciplineTheory.step_prov_def,
        ptrDisciplineTheory.set_prov_def, ptrDisciplineTheory.out_prov_def,
        finite_mapTheory.DRESTRICT_DRESTRICT] >>
      AP_TERM_TAC >> simp[NoAsms, pred_setTheory.EXTENSION] >> metis_tac[]) >>
    qpat_x_assum `tm = _` SUBST1_TAC >>
    qmatch_goalsub_abbrev_tac `step_taint i1 s1 u1 tn0` >>
    `step_taint i1 s1 u1 tn0 = tn0 with t_var := tn0.t_var |+ (a1,{})` by (
      simp[Abbr `i1`, Abbr `s1`, Abbr `u1`, Abbr `tn0`,
        eval_operand_def, lookup_var_def,
        ptrDisciplineTheory.step_taint_def,
        ptrDisciplineTheory.mem_taint_def, new_site_bytes_unchanged,
        ptrDisciplineTheory.step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
        ptrDisciplineTheory.range_bytes_def, ptrDisciplineTheory.written_taint_def,
        ptrDisciplineTheory.set_var_taint_def, ptrDisciplineTheory.out_taint_def,
        ptrDisciplineTheory.adopt_reset_def, ptrDisciplineTheory.store_taint_def,
        ptrDisciplineTheory.imm_taint_def, ptrDisciplineTheory.op_taint_def,
        finite_mapTheory.FLOOKUP_UPDATE]) >>
    asm_rewrite_tac [] >>
    qmatch_goalsub_abbrev_tac `step_taint i2 u1 u2 tn1` >>
    `step_taint i2 u1 u2 tn1 = tn1 with t_var := tn1.t_var |+ (a2,{})` by (
      simp[Abbr `i2`, Abbr `u1`, Abbr `u2`, Abbr `tn1`, Abbr `tn0`,
        eval_operand_def, lookup_var_def,
        ptrDisciplineTheory.step_taint_def,
        ptrDisciplineTheory.mem_taint_def, new_site_bytes_unchanged,
        ptrDisciplineTheory.step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
        ptrDisciplineTheory.range_bytes_def, ptrDisciplineTheory.written_taint_def,
        ptrDisciplineTheory.set_var_taint_def, ptrDisciplineTheory.out_taint_def,
        ptrDisciplineTheory.adopt_reset_def, ptrDisciplineTheory.store_taint_def,
        ptrDisciplineTheory.imm_taint_def, ptrDisciplineTheory.op_taint_def,
        finite_mapTheory.FLOOKUP_UPDATE]) >>
    asm_rewrite_tac [] >>
    qmatch_goalsub_abbrev_tac `step_taint i3 u2 u3 tn2` >>
    `step_taint i3 u2 u3 tn2 = tn2 with t_var := tn2.t_var |+ (a3,{})` by (
      simp[Abbr `i3`, Abbr `u2`, Abbr `u3`, Abbr `tn2`, Abbr `tn1`, Abbr `tn0`,
        eval_operand_def, lookup_var_def,
        ptrDisciplineTheory.step_taint_def,
        ptrDisciplineTheory.mem_taint_def, new_site_bytes_unchanged,
        ptrDisciplineTheory.step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
        ptrDisciplineTheory.range_bytes_def, ptrDisciplineTheory.written_taint_def,
        ptrDisciplineTheory.set_var_taint_def, ptrDisciplineTheory.out_taint_def,
        ptrDisciplineTheory.adopt_reset_def, ptrDisciplineTheory.store_taint_def,
        ptrDisciplineTheory.imm_taint_def, ptrDisciplineTheory.op_taint_def,
        finite_mapTheory.FLOOKUP_UPDATE]) >>
    asm_rewrite_tac [] >>
    simp[Abbr `tp`, Abbr `tn2`, Abbr `tn1`, Abbr `tn0`, Abbr `u3`,
        eval_operand_def, lookup_var_def,
        ptrDisciplineTheory.step_taint_def,
        ptrDisciplineTheory.mem_taint_def, new_site_bytes_unchanged,
        ptrDisciplineTheory.step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
        ptrDisciplineTheory.range_bytes_def, ptrDisciplineTheory.written_taint_def,
        ptrDisciplineTheory.set_var_taint_def, ptrDisciplineTheory.out_taint_def,
        ptrDisciplineTheory.adopt_reset_def, ptrDisciplineTheory.store_taint_def,
        ptrDisciplineTheory.imm_taint_def, ptrDisciplineTheory.op_taint_def,
        finite_mapTheory.FLOOKUP_UPDATE] >>
      simp[DB.fetch "ptrDiscipline" "taint_component_equality",
        DB.fetch "ptrDiscipline" "taint_accfupds",
        DB.fetch "ptrDiscipline" "taint_accessors"]) >>
  gvs[] >> suspend "middlejoin"
QED

Resume raw_call_bytes_success_full_path[path]:
  rpt gen_tac >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn)
    (MAP (\i. (func.fn_name,i.inst_id) IN explicit)
      (FILTER (\i. i.inst_opcode = GAS) code))
    (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code),Gf,tf)`
    suffices_by simp[mk_inst_def] >>
  irule run_inst_seq_gas_origin_ptr_path >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[mk_inst_def, is_terminator_def] >>
  conj_tac >- (qexists_tac `bb` >>
    pure_asm_rewrite_tac [] >> simp[]) >>
  reverse conj_tac >- simp[] >>
  suspend "memsafe"
QED
Resume raw_call_bytes_success_full_path[halted]:
  qpat_x_assum `mstore _ _ _ = t` (SUBST1_TAC o SYM) >>
  simp[Abbr `u`, venomStateTheory.mstore_def]
QED
Resume raw_call_bytes_success_full_path[block]:
  qpat_x_assum `mstore _ _ _ = t` (SUBST1_TAC o SYM) >>
  simp[Abbr `u`, Abbr `sc`, venomStateTheory.mstore_def]
QED
Resume raw_call_bytes_success_full_path[history]:
  `alloca_history func (t with vs_inst_idx := s.vs_inst_idx + LENGTH code)`
    suffices_by simp[] >>
  irule alloca_history_run_inst_seq >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qexistsl_tac [`bb`, `rest`] >> simp[]) >>
  simp[mk_inst_def, is_terminator_def]
QED
Resume raw_call_bytes_success_full_path[allocas]:
  qpat_x_assum `mstore _ _ _ = t` (SUBST1_TAC o SYM) >>
  simp[Abbr `u`, venomStateTheory.mstore_def]
QED
Resume raw_call_bytes_success_full_path[next]:
  qpat_x_assum `mstore _ _ _ = t` (SUBST1_TAC o SYM) >>
  simp[Abbr `u`, venomStateTheory.mstore_def]
QED
Resume raw_call_bytes_success_full_path[lookup]:
  qpat_x_assum `mstore _ _ _ = t` (SUBST1_TAC o SYM) >>
  simp[Abbr `u`, venomStateTheory.mstore_def, lookup_var_def,
    finite_mapTheory.FLOOKUP_UPDATE]
QED
Resume raw_call_bytes_success_full_path[covers]:
  qpat_x_assum `mstore _ _ _ = t` (SUBST1_TAC o SYM) >>
  fs[bodyPtrDefsTheory.ptr_covers_def] >>
  simp[Abbr `tf`, Abbr `tp`, Abbr `Gf`, Abbr `u`,
    venomStateTheory.mstore_def, lookup_var_def,
    ptrDisciplineTheory.op_taint_def, finite_mapTheory.FLOOKUP_DRESTRICT,
    finite_mapTheory.FLOOKUP_UPDATE] >>
  fs[ptrDisciplineTheory.op_taint_def]
QED
Resume raw_call_bytes_success_full_path[memtaint]:
  simp[Abbr `tf`, Abbr `tp`]
QED
Resume raw_call_bytes_success_full_path[stor]:
  simp[Abbr `tf`, Abbr `tp`]
QED
Resume raw_call_bytes_success_full_path[trans]:
  simp[Abbr `tf`, Abbr `tp`]
QED
Resume raw_call_bytes_success_full_path[imm]:
  simp[Abbr `tf`, Abbr `tp`]
QED
Resume raw_call_bytes_success_full_path[old]:
  qpat_x_assum `mstore _ _ _ = t` (SUBST1_TAC o SYM) >>
  simp[Abbr `tf`, venomStateTheory.mstore_def, lookup_var_def,
    ptrDisciplineTheory.op_taint_def] >>
  rpt strip_tac >>
  qpat_x_assum `!x. not_fresh_at sa x ==> _ /\ _ /\ _` drule >>
  simp[lookup_var_def, ptrDisciplineTheory.op_taint_def]
QED
Resume raw_call_bytes_success_full_path[robust]:
  qpat_x_assum `mstore _ _ _ = t` (SUBST1_TAC o SYM) >>
  simp[Abbr `tf`, Abbr `tp`] >>
  mp_tac (bytes_length_store_robust |> Q.INST
    [`bs` |-> `TAKE n s.vs_returndata`, `s` |-> `u`,
     `dirty` |-> `tn.t_mem`, `cap` |-> `n`, `b` |-> `b`]) >>
  simp[Abbr `u`, LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF] >>
  Cases_on `n <= LENGTH s.vs_returndata` >>
  gvs[LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF]
QED
Resume raw_call_bytes_success_full_path[frame]:
  rpt gen_tac >> strip_tac >>
  conj_tac >- suspend "invframe" >>
  simp[bodyPtrDefsTheory.ghost_kept_at_def, Abbr `tf`, Abbr `tp`,
    ptrDisciplineTheory.op_taint_def] >>
  rpt strip_tac >>
  qpat_x_assum `!x. not_fresh_at sa x ==> _ /\ _ /\ _` drule >>
  simp[ptrDisciplineTheory.op_taint_def]
QED

Resume raw_call_bytes_success_full_path[middlejoin]:
  `run_inst_seq C s0 = OK (u with vs_inst_idx := s0.vs_inst_idx)` by (
    simp[Abbr `C`, Abbr `s0`, Abbr `u`, run_inst_seq_def,
      venomExecSemanticsTheory.step_inst_base_opcode_eqs,
      mk_inst_def, venomExecSemanticsTheory.exec_pure2_def, eval_operand_def,
      lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE, update_var_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) C` by
    simp[Abbr `C`, mk_inst_def, is_terminator_def] >>
  `inst_seq_ptr D lo ctx func PG G0 tn0
    (C ++ [mk_inst (sa.cs_next_id+5) MSTORE [Var p;Var a4] []]) s0 Gf tf`
    suffices_by simp[Abbr `C`, mk_inst_def] >>
  irule instSeqComposePtrTheory.inst_seq_ptr_append >>
  simp[] >>
  qexistsl_tac [`Gf`, `tm`] >>
  simp[] >> gen_tac >> suspend "store"
QED

Resume raw_call_bytes_success_full_path[store]:
  `p <> a0 /\ p <> a1 /\ p <> a2 /\ p <> a3 /\ p <> a4` by metis_tac[] >>
  simp[inst_seq_ptr_def, venomExecSemanticsTheory.step_inst_base_opcode_eqs,
    mk_inst_def, venomExecSemanticsTheory.exec_write2_def,
    eval_operand_def, lookup_var_def, Abbr `u`,
    finite_mapTheory.FLOOKUP_UPDATE] >>
  conj_tac >- suspend "storecheck" >>
  suspend "storeghost"
QED

Resume raw_call_bytes_success_full_path[storecheck]:
  qmatch_goalsub_abbrev_tac `ptr_inst_ok D lo fuel ctx func Gf tm inst v` >>
  `lookup_var p v = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
    op_taint tm (Var p) = op_taint tn (Var p)` by
    simp[Abbr `v`, Abbr `Gf`, Abbr `tm`, lookup_var_def,
      ptrDisciplineTheory.op_taint_def,
      finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FLOOKUP_DRESTRICT] >>
  `ptr_covers Gf tm p v 32` by (
    fs[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_ADD,
      arithmeticTheory.LESS_EQ_TRANS]) >>
  qpat_x_assum `ptr_covers Gf tm p v 32` mp_tac >>
  simp[bodyPtrDefsTheory.ptr_covers_def] >> strip_tac >>
  simp[ptrSafeRunTheory.ptr_inst_ok_def, ptrDisciplineTheory.access_ok_def,
    ptrDisciplineTheory.taint_ok_def,
    codegenRelTheory.source_memory_write_ranges_def,
    contextCodegenRelTheory.source_memory_read_ranges_def,
    codegenRelTheory.fixed_source_write_range_def,
    eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
    ptrDisciplineTheory.allocas_from_def] >>
  suspend "storecheckrest"
QED
Resume raw_call_bytes_success_full_path[storeghost]:
  simp[ptrDisciplineTheory.step_prov_def, ptrDisciplineTheory.set_prov_def,
    finite_mapTheory.DRESTRICT_UNIV] >>
  qmatch_goalsub_abbrev_tac `step_taint inst v (mstore b w vk) tm` >>
  `vk = v with vs_inst_idx := k` by simp[Abbr `vk`, Abbr `v`] >>
  pure_asm_rewrite_tac [] >>
  pure_rewrite_tac [instIdxIndepTheory.mstore_idx,
    ghostPcTransportPtrTheory.step_taint_inst_idx_right] >>
  simp[Abbr `tf`, Abbr `tm`, Abbr `inst`, Abbr `v`, Abbr `w`,
    DB.fetch "ptrDiscipline" "taint_component_equality",
    ifexp_materialize_mstore_ghost, GSYM mk_inst_def,
    ifexp_materialize_mstore_taint, eval_operand_def, lookup_var_def,
    finite_mapTheory.FLOOKUP_UPDATE, ptrDisciplineTheory.op_taint_def] >>
  qmatch_goalsub_abbrev_tac `step_taint inst v (mstore b w v) tm` >>
  `eval_operand (Var p) v = SOME (n2w b)` by
    simp[Abbr `v`, eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  `eval_operand (Var a4) v = SOME w` by
    simp[Abbr `v`, Abbr `w`, eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  `b < dimword (:256)` by (simp[] >> decide_tac) >>
  qpat_assum `eval_operand (Var p) v = _`
    (mp_then Any mp_tac ifexp_materialize_mstore_taint) >>
  disch_then drule >>
  simp[Abbr `inst`, Abbr `tm`, Abbr `w`, wordsTheory.w2n_n2w,
    ptrDisciplineTheory.op_taint_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Resume raw_call_bytes_success_full_path[storecheckrest]:
  simp[Abbr `inst`, Abbr `v`, Abbr `tm`, Abbr `fuel`,
    eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
    ptrDisciplineTheory.op_taint_def,
    venomExecSemanticsTheory.step_inst_non_invoke,
    venomExecSemanticsTheory.step_inst_base_opcode_eqs,
    venomExecSemanticsTheory.exec_write2_def] >>
  rpt strip_tac >> gvs[] >>
  gvs[memLocDefsTheory.mem_write_ops_def, Abbr `Gf`,
    ptrDisciplineTheory.op_taint_def, finite_mapTheory.FLOOKUP_DRESTRICT] >>
  fs[ptrDisciplineTheory.allocas_from_def] >> metis_tac[]
QED

Resume raw_call_bytes_success_full_path[memsafe]:
  simp[fragExecMemTheory.run_inst_seq_mem_ok_def,
    venomExecSemanticsTheory.step_inst_base_opcode_eqs,
    mk_inst_def, venomExecSemanticsTheory.exec_read0_def,
    venomExecSemanticsTheory.exec_pure2_def,
    venomExecSemanticsTheory.exec_write2_def, eval_operand_def,
    lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
    contextCodegenRelTheory.source_memory_read_ranges_def,
    codegenRelTheory.source_memory_write_ranges_def,
    codegenRelTheory.fixed_source_write_range_def, eval_operand_def,
    lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE, wordsTheory.w2n_n2w] >>
  `b < dimword (:256)` by (simp[] >> decide_tac) >>
  simp[wordsTheory.w2n_n2w] >> decide_tac
QED

Resume raw_call_bytes_success_full_path[invframe]:
  irule raw_call_clean_write_ghost_at >>
  conj_tac >- (
    qpat_x_assum `mstore _ _ _ = t` (SUBST1_TAC o SYM) >>
    fs[bodyPtrDefsTheory.ghost_inv_at_def,
       bodyPtrDefsTheory.stor_taint_ok_at_def, Abbr `tf`, Abbr `tp`, Abbr `u`,
       venomStateTheory.mstore_def]) >>
  qexistsl_tac [`G`, `word_to_bytes capword T`, `b`, `es`, `func`, `s`, `sa`, `tn`] >>
  simp[Abbr `tf`, Abbr `tp`] >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    qpat_x_assum `!name lb k. local_region _ _ _ _ _ _ ==> _` drule >>
    simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  conj_tac >- (
    qpat_x_assum `mstore _ _ _ = t` (SUBST1_TAC o SYM) >>
    simp[venomStateTheory.mstore_def, lookup_var_def,
      ptrDisciplineTheory.op_taint_def] >>
    rpt strip_tac >>
    qpat_x_assum `!x. not_fresh_at sa x ==> _ /\ _ /\ _` drule >>
    simp[lookup_var_def, ptrDisciplineTheory.op_taint_def]) >>
  qpat_x_assum `mstore _ _ _ = t` (SUBST1_TAC o SYM) >>
  simp[Abbr `u`, venomStateTheory.mstore_def,
    venomStateTheory.write_memory_with_expansion_def]
QED

Finalise raw_call_bytes_success_full_path
