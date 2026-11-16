Theory bodyFullRawCallBytes
Ancestors
  exprSimRawCall fragGasSeqPtr wordLoadStorePtr bodyFullGhostFrame
  rawCallBufferPtr representationCleanPtr builtinSimple emitHelper compileEnv
  venomState venomInst fragExec exprLoweringProps list ptrDisciplineEmptyTaint
  augAssignPtrScalarRun augAssignPtrScalarCertificate instSeqComposePtr
  bodyFullRawCallCallFrame
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
        finite_mapTheory.DRESTRICT_DRESTRICT, pred_setTheory.EXTENSION] >>
      metis_tac[]) >>
    qpat_x_assum `tm = _` SUBST1_TAC >>
    simp[Abbr `tn0`, Abbr `tp`,
      ptrDisciplineTheory.step_taint_def,
      ptrDisciplineTheory.mem_taint_def, new_site_bytes_unchanged,
      ptrDisciplineTheory.step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
      ptrDisciplineTheory.range_bytes_def, ptrDisciplineTheory.written_taint_def,
      ptrDisciplineTheory.set_var_taint_def, ptrDisciplineTheory.out_taint_def,
      ptrDisciplineTheory.adopt_reset_def, ptrDisciplineTheory.store_taint_def,
      ptrDisciplineTheory.imm_taint_def, ptrDisciplineTheory.op_taint_def,
      ptrDisciplineTheory.op_prov_def, ptrDisciplineTheory.first_prov_def,
      finite_mapTheory.FLOOKUP_DRESTRICT, finite_mapTheory.FLOOKUP_UPDATE] >>
    suspend "metadata") >>
  gvs[] >> suspend "middlejoin"
QED

Resume raw_call_bytes_success_full_path[path]:
  cheat
QED
Resume raw_call_bytes_success_full_path[halted]:
  cheat
QED
Resume raw_call_bytes_success_full_path[block]:
  cheat
QED
Resume raw_call_bytes_success_full_path[history]:
  cheat
QED
Resume raw_call_bytes_success_full_path[allocas]:
  cheat
QED
Resume raw_call_bytes_success_full_path[next]:
  cheat
QED
Resume raw_call_bytes_success_full_path[lookup]:
  cheat
QED
Resume raw_call_bytes_success_full_path[covers]:
  cheat
QED
Resume raw_call_bytes_success_full_path[memtaint]:
  cheat
QED
Resume raw_call_bytes_success_full_path[stor]:
  cheat
QED
Resume raw_call_bytes_success_full_path[trans]:
  cheat
QED
Resume raw_call_bytes_success_full_path[imm]:
  cheat
QED
Resume raw_call_bytes_success_full_path[old]:
  cheat
QED
Resume raw_call_bytes_success_full_path[robust]:
  cheat
QED
Resume raw_call_bytes_success_full_path[frame]:
  cheat
QED

Resume raw_call_bytes_success_full_path[middlejoin]:
  FAIL_TAC "middlejoin"
QED

Finalise raw_call_bytes_success_full_path

