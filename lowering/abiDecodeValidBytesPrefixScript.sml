(* Certificate cuts for the bounded MLOAD bytes decoder. *)
Theory abiDecodeValidBytesPrefix
Ancestors abiBuiltinDecodeSetup[qualified,ignore_grammar] loweringHalt[qualified,ignore_grammar] abiEncoderArrayRound[qualified,ignore_grammar] abiBuiltinEncodeContext[qualified,ignore_grammar] ASCIInumbers[qualified,ignore_grammar] bool[qualified,ignore_grammar] arithmetic[qualified,ignore_grammar]
  abiDecoderBytesPrefix abiDecodePtrMemberFrame bodyPtrBopScalarCompile
  loweringShapeRules abiDecoderBytesBound abiDecoderGuards abiEncoder
  compileEnv emitHelperProps exprLoweringProps bodyPtrBopScalarSeq
  loweringStateRelDefs emitHelper freshWrites venomInst pred_set rich_list list
  bodyPtrDefs logAbiPrefixPtr reasonCopySourcePtr
  logInstSeqPtr bodyPtrIfExpBytesCounted bodyPtrIfExpBytesFrame
  ghostPcTransportPtr allocaFootprint bodyFieldMemoryProps fragExecMem
  fragExec venomExecSemantics venomState words

Theorem abi_decode_bytes_mload_prefix_cuts[local]:
  abi_decode_bytes_position_prefix pos MLOAD (Var src) hi n sa = ((addr,cnt),cm) ==>
  ?head sh ar sp sl bad sg good sz sc.
    abi_decode_bytes_head pos hi sa = (head,sh) /\
    emit_op ADD [Var src;pos] sh = (Var ar,sp) /\ addr = Var ar /\
    emit_op MLOAD [Var ar] sp = (cnt,sl) /\
    emit_op GT [cnt;Lit (n2w n)] sl = (bad,sg) /\
    emit_op ISZERO [bad] sg = (good,sz) /\
    emit_void ASSERT [good] sz = ((),sc) /\
    abi_decode_bytes_payload_guard head cnt hi sc = ((),cm) /\
    emitted_insts sa cm = emitted_insts sa sh ++
      (emitted_insts sh sp ++ emitted_insts sp sl) ++ emitted_insts sl cm /\
    sl.cs_next_var = sh.cs_next_var + 2
Proof
  simp[abi_decode_bytes_position_prefix_trace, compile_abi_dec_addr_def] >>
  strip_tac >>
  qpat_x_assum `abi_decode_count_guard _ _ _ _ = _` mp_tac >>
  simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule_then assume_tac abi_decode_bytes_head_shape >>
  drule_then assume_tac abi_decode_bytes_payload_guard_shape >>
  imp_res_tac emit_op_facts >> gvs[] >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  rename1 `emit_op ADD _ sh = (Var ar,sp)` >>
  rename1 `emit_op MLOAD _ sp = (Var cntv,sl)` >>
  rename1 `emit_op GT _ sl = (Var bad,sg)` >>
  rename1 `emit_op ISZERO _ sg = (Var good,sz)` >>
  rename1 `emit_void ASSERT _ sz = ((),sc)` >>
  `inst_extends sh sl /\ inst_extends sl sz` by metis_tac[inst_extends_trans] >>
  `inst_extends sa sl /\ inst_extends sl sc` by metis_tac[inst_extends_trans] >>
  `inst_extends sl cm` by metis_tac[inst_extends_trans] >>
  `emitted_insts sa cm = emitted_insts sa sl ++ emitted_insts sl cm /\
   emitted_insts sa sl = emitted_insts sa sh ++ emitted_insts sh sl /\
   emitted_insts sh sl = emitted_insts sh sp ++ emitted_insts sp sl` by
    (rpt conj_tac >> irule emitted_insts_append >> fs[inst_extends_def]) >>
  simp[APPEND_ASSOC]
QED

(* Both bounded bytes guards first compute an end, then compare the interval. *)
Theorem abi_decode_bytes_scalar_add_range[local]:
  emit_op ADD [start;len] sa = (last,sm) /\
  compile_abi_decode_range_check start last hi sm = ((),sb) /\
  start IN A /\ len IN A /\ hi IN A /\
  (!x. x IN R ==> not_fresh_at sa x) ==>
  ?C. bop_scalar_seq R A (emitted_insts sa sb) C /\
      last IN C /\ A SUBSET C /\
      sa.cs_next_var <= sb.cs_next_var /\
      ?v. last = Var v /\ not_fresh_at sb v
Proof
  strip_tac >>
  `!k. sa.cs_next_var <= k ==> STRING #"%" (toString k) NOTIN R` by
    (rpt strip_tac >>
     qpat_assum `!x. x IN R ==> not_fresh_at sa x`
       (drule_then (qspec_then `k` mp_tac o REWRITE_RULE[not_fresh_at_def])) >>
     simp[]) >>
  gvs[compile_abi_decode_range_check_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
      emit_def, emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, bop_scalar_seq_def, mk_inst_def, SUBSET_INSERT_RIGHT,
       not_fresh_at_def, ASCIInumbersTheory.toString_11] >>
  simp[SUBSET_DEF]
QED

Theorem abi_decode_bytes_scalar_head[local]:
  abi_decode_bytes_head pos hi sa = (head,sh) /\ hi <> Lit 0w /\
  pos IN A /\ Lit 32w IN A /\ hi IN A /\
  (!x. x IN R ==> not_fresh_at sa x) ==>
  ?C. bop_scalar_seq R A (emitted_insts sa sh) C /\
      head IN C /\ A SUBSET C /\ sa.cs_next_var <= sh.cs_next_var /\
      ?v. head = Var v /\ not_fresh_at sh v
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_bytes_head _ _ _ = _` mp_tac >>
  simp[abi_decode_bytes_head_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  irule abi_decode_bytes_scalar_add_range >> metis_tac[]
QED

Theorem abi_decode_bytes_scalar_count_payload[local]:
  emit_op GT [cnt;Lit (n2w n)] sl = (bad,sg) /\
  emit_op ISZERO [bad] sg = (good,sz) /\
  emit_void ASSERT [good] sz = ((),sc) /\
  abi_decode_bytes_payload_guard head cnt hi sc = ((),cm) /\ hi <> Lit 0w /\
  cnt IN A /\ head IN A /\ hi IN A /\ Lit (n2w n) IN A /\
  (!x. x IN R ==> not_fresh_at sl x) ==>
  ?C. bop_scalar_seq R A (emitted_insts sl cm) C /\
      A SUBSET C /\ sl.cs_next_var <= cm.cs_next_var
Proof
  strip_tac >>
  `bop_scalar_seq R A (emitted_insts sl sz) (good INSERT bad INSERT A)` by
    (irule bop_scalar_seq_emit_iszero >> simp[] >>
     qexistsl_tac [`sg`, `GT`, `[cnt; Lit (n2w n)]`] >> simp[]) >>
  `bop_scalar_seq R (good INSERT bad INSERT A) (emitted_insts sz sc)
     (good INSERT bad INSERT A)` by
    (irule bop_scalar_seq_emit_assert >> qexistsl_tac [`good`, `ASSERT`] >> simp[]) >>
  `inst_extends sl sg /\ inst_extends sg sz /\ inst_extends sz sc /\
   inst_extends sc cm` by
    metis_tac[inst_extends_emit_op, inst_extends_emit_void,
              abi_decode_bytes_payload_guard_shape] >>
  `inst_extends sl sz /\ inst_extends sl sc` by metis_tac[inst_extends_trans] >>
  `sc.cs_next_var = sz.cs_next_var /\ sz.cs_next_var = sg.cs_next_var+1 /\
   sg.cs_next_var = sl.cs_next_var+1` by
    metis_tac[emit_op_facts, emitted_insts_emit_void] >>
  `!x. x IN R ==> not_fresh_at sc x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sl` >> simp[]) >>
  qpat_x_assum `abi_decode_bytes_payload_guard _ _ _ _ = _` mp_tac >>
  simp[abi_decode_bytes_payload_guard_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  `?C. bop_scalar_seq R (good INSERT bad INSERT A) (emitted_insts sc cm) C /\
       (good INSERT bad INSERT A) SUBSET C /\ sc.cs_next_var <= cm.cs_next_var` by
    (drule abi_decode_bytes_scalar_add_range >>
     disch_then (qspecl_then [`cm`, `hi`, `R`, `good INSERT bad INSERT A`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  `emitted_insts sl sc = emitted_insts sl sz ++ emitted_insts sz sc /\
   emitted_insts sl cm = emitted_insts sl sc ++ emitted_insts sc cm` by
    (rpt conj_tac >> irule emitted_insts_append >> fs[inst_extends_def]) >>
  qexists `C` >> conj_tac
  >- (simp[] >> irule bop_scalar_seq_append >>
      qexists `good INSERT bad INSERT A` >> simp[] >>
      irule bop_scalar_seq_append >> qexists `good INSERT bad INSERT A` >> simp[]) >>
  conj_tac >- (irule SUBSET_TRANS >> qexists `good INSERT bad INSERT A` >>
               simp[SUBSET_DEF]) >>
  decide_tac
QED

(* The ADD retains the entire payload window; the MLOAD uses only its head. *)
Theorem abi_decode_bytes_addr_load[local]:
  emit_op ADD [Var src;pos] sh = (Var ar,sp) /\
  emit_op MLOAD [Var ar] sp = (Var cnt,sl) /\
  not_fresh_at sh src /\ ~ctx_has_dalloca ctx /\
  abi_decode_ptr_window G tn s src (n2w B) L /\
  eval_operand pos s = SOME (n2w p) /\ op_taint tn pos = {} /\
  p + 32 + c <= L /\ B + L < dimword (:256) /\ B + L <= s.vs_alloca_next ==>
  ?u H tm.
    run_inst_seq (emitted_insts sh sp ++ emitted_insts sp sl) s = OK u /\
    run_inst_seq_mem_ok (emitted_insts sh sp ++ emitted_insts sp sl) s /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sh sp ++ emitted_insts sp sl) s H tm /\
    abi_decode_ptr_window H tm u ar (n2w (B+p)) (32+c) /\
    not_fresh_at sl ar /\ not_fresh_at sl cnt /\
    op_prov H (Var cnt) = NONE /\ op_taint tm (Var cnt) = {} /\
    (u with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sh x ==> lookup_var x u = lookup_var x s /\
       FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)) /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm
Proof
  strip_tac >>
  `ptr_covers G tn src s (p+(32+c)) /\ lookup_var src s = SOME (n2w B)` by
    (fs[abi_decode_ptr_window_def] >> irule ptr_covers_mono >> qexists `L` >> simp[]) >>
  `w2n (n2w B : bytes32) + p < dimword (:256)` by simp[w2n_n2w] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by simp[] >>
  drule_all emit_addr_add_seq_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts sh sp) s = OK v` >>
  qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emit_op_facts) >>
  qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any strip_assume_tac emit_op_facts) >>
  `v = update_var ar (n2w (B+p)) s` by
    (qpat_assum `emit_op ADD _ _ = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     qpat_x_assum `run_inst_seq (emitted_insts sh sp) s = OK v` mp_tac >>
     gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
         exec_pure2_def, eval_operand_def, word_add_n2w]) >>
  qabbrev_tac `vp = v with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sh sp)` >>
  `abi_decode_ptr_window Gf tnf vp ar (n2w (B+p)) (32+c)` by
    (`lookup_var ar v = SOME (n2w (B+p))` by metis_tac[word_add_n2w] >>
     simp[abi_decode_ptr_window_def, Abbr `vp`, lookup_var_def, update_var_def,
          finite_mapTheory.FLOOKUP_UPDATE] >>
     fs[abi_decode_ptr_window_def] >>
     `w2n (n2w B : bytes32) = B /\ w2n (n2w (B+p) : bytes32) = B+p` by
       simp[w2n_n2w] >>
     rpt strip_tac >> qpat_x_assum `!i. _ ==> i NOTIN tn.t_mem` irule >>
     fs[] >> decide_tac) >>
  `ptr_covers Gf tnf ar vp 32 /\ lookup_var ar vp = SOME (n2w (B+p)) /\
   (!i. w2n (n2w (B+p):bytes32) <= i /\
        i < w2n (n2w (B+p):bytes32)+32 ==> i NOTIN tnf.t_mem)` by
    (conj_tac
     >- (irule ptr_covers_mono >> qexists `32+c` >>
         gvs[abi_decode_ptr_window_def]) >>
     gvs[abi_decode_ptr_window_def]) >>
  suspend "load"
QED

Resume abi_decode_bytes_addr_load[load]:
  `ctx_has_dalloca ctx ==> allocas_below_fmp vp` by simp[] >>
  drule_all emit_mload_clean_seq_ptr >>
  disch_then (qspecl_then [`D`, `fn`, `PG`] strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts sp sl) vp = OK w` >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> ISTORE)
     (emitted_insts sh sp ++ emitted_insts sp sl)` by
    (imp_res_tac emitted_insts_emit_op >> simp[mk_inst_def, is_terminator_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sh sp) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sp sl)` by
    fs[EVERY_CONJ] >>
  qabbrev_tac `u = w with vs_inst_idx := s.vs_inst_idx` >>
  `run_inst_seq (emitted_insts sh sp ++ emitted_insts sp sl) s = OK u /\
   inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sh sp ++ emitted_insts sp sl) s Gf' tnf'` by
    (simp[Abbr `u`] >> qunabbrev_tac `vp` >> conj_tac
     >- (drule_all run_inst_seq_append_advanced >> simp[update_var_def]) >>
     irule bop_inst_seq_ptr_append >> conj_tac >- simp[] >>
     qexistsl_tac [`Gf`, `v`, `tnf`] >>
     simp[arithmeticTheory.ADD_COMM]) >>
  `run_inst_seq_mem_ok (emitted_insts sp sl) vp` by
    (irule emit_mload_mem_ok >>
     qexistsl_tac [`n2w (B+p):bytes32`, `Var ar`, `Var cnt`] >>
     simp[eval_operand_def] >> simp[Abbr `vp`, update_var_def, w2n_n2w] >>
     decide_tac) >>
  `run_inst_seq_mem_ok (emitted_insts sp sl) v` by
    (fs[Abbr `vp`, EVERY_CONJ] >> metis_tac[run_inst_seq_mem_ok_inst_idx]) >>
  `run_inst_seq_mem_ok (emitted_insts sh sp ++ emitted_insts sp sl) s` by
    (irule run_inst_seq_mem_ok_append >> simp[] >> metis_tac[attr_add_prefix_mem_ok]) >>
  `tnf'.t_imm = tn.t_imm` by
    (`EVERY (\i. i.inst_opcode <> ISTORE) (emitted_insts sh sp ++ emitted_insts sp sl)` by
       fs[EVERY_CONJ] >>
     metis_tac[inst_seq_ptr_immutable_frame]) >>
  `ar = out /\ cnt = out'` by fs[] >>
  `!x. not_fresh_at sh x ==> not_fresh_at sp x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists `sh` >> simp[]) >>
  `not_fresh_at sl ar` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists `sp` >> simp[]) >>
  `(u with vs_vars := s.vs_vars) = s` by
    (qpat_assum `w with vs_vars := vp.vs_vars = vp` mp_tac >>
     simp[Abbr `u`, Abbr `vp`, update_var_def, venom_state_component_equality]) >>
  `!x. not_fresh_at sp x ==> lookup_var x u = lookup_var x vp` by
    (simp[Abbr `u`, lookup_var_def] >> metis_tac[lookup_var_def]) >>
  `abi_decode_ptr_window Gf' tnf' u ar (n2w (B+p)) (32+c)` by
    (irule abi_decode_ptr_window_frame >> qexistsl_tac [`Gf`, `vp`, `tnf`] >> simp[]) >>
  `!x. not_fresh_at sh x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP Gf' x = FLOOKUP G x /\ op_taint tnf' (Var x) = op_taint tn (Var x)` by
    (fs[lookup_var_def, Abbr `vp`] >> metis_tac[]) >>
  qexistsl_tac [`u`, `Gf'`, `tnf'`] >> simp[]
QED

Finalise abi_decode_bytes_addr_load


(* The two scalar guards need only the physical frame and the indexed ghosts. *)
Theorem abi_decode_bytes_scalar_cut[local]:
  bop_scalar_seq R A code C /\
  (!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  ~ctx_has_dalloca ctx /\ run_inst_seq code s = OK t ==>
  ?H u.
    EVERY (\i. ~is_terminator i.inst_opcode) code /\
    run_inst_seq_mem_ok code s /\
    inst_seq_ptr D 0 ctx fn PG G tn code (s with vs_inst_idx := pc) H u /\
    (!op. op IN C ==> op_prov H op = NONE /\ op_taint u op = {}) /\
    (t with vs_vars := s.vs_vars) = s /\
    (!x. x IN R ==> lookup_var x t = lookup_var x s /\
       FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm
Proof
  strip_tac >>
  drule bop_scalar_seq_opcodes >> simp[EVERY_CONJ] >> strip_tac >>
  `run_inst_seq_mem_ok code s` by
    (irule run_inst_seq_mem_ok_every >> simp[EVERY_MEM] >> rpt strip_tac >>
     drule_all bodyPtrBopScalarOutcomeTheory.bop_scalar_seq_outputs >>
     simp[] >> strip_tac >> gvs[unitTransformDefsTheory.inst_mem_below_frontier_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def, memSafeRunTheory.inst_dload_in_section_def]) >>
  drule_all bodyPtrBopScalarOutcomeTheory.bop_scalar_seq_runtime_frame >> strip_tac >>
  `run_inst_seq code (s with vs_inst_idx := pc) = OK (t with vs_inst_idx := pc)` by
    simp[run_inst_seq_inst_idx, instIdxIndepTheory.exec_result_map_def] >>
  qpat_x_assum `run_inst_seq _ s = OK t` kall_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp (s with vs_inst_idx := pc)` by simp[] >>
  drule_all bop_scalar_seq_run >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  rename1 `inst_seq_ptr _ _ _ _ _ _ _ _ _ H u` >>
  qexistsl_tac [`H`,`u`] >> simp[lookup_var_def, ptrDisciplineTheory.op_taint_def] >>
  fs[venom_state_component_equality]
QED

(* The bounded prefix certifies the same read-only run as its physical semantics. *)
Theorem abi_decode_valid_bytes_prefix_certificate:
  abi_decode_bytes_position_prefix pos MLOAD (Var src) hi n sa = ((addr,cnt),cm) /\
  hi <> Lit 0w /\ fresh_vars_wrt sa s /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  (!x. MEM (Var x) [pos;hi] ==> not_fresh_at sa x) /\
  abi_decode_ptr_window G tn s src (n2w B) L /\
  lookup_var dst s = SOME (n2w d) /\ ptr_covers G tn dst s cap /\
  eval_operand pos s = SOME (n2w p) /\ eval_operand hi s = SOME (n2w L) /\
  op_prov G pos = NONE /\ op_taint tn pos = {} /\
  op_prov G hi = NONE /\ op_taint tn hi = {} /\
  abi_decode_load MLOAD (n2w (B+p) : bytes32) s = n2w c /\
  c <= n /\ n < dimword (:256) /\ p + 32 + c <= L /\
  B + L < dimword (:256) /\ B + L <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx ==>
  ?ar cv m H u.
    addr = Var ar /\ cnt = Var cv /\ inst_extends sa cm /\
    m.vs_inst_idx = LENGTH cm.cs_current_insts /\
    run_inst_seq (emitted_insts sa cm) s = OK (m with vs_inst_idx := s.vs_inst_idx) /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa cm) /\
    run_inst_seq_mem_ok (emitted_insts sa cm) s /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa cm) s H u /\
    fresh_vars_wrt cm m /\ not_fresh_at cm ar /\ not_fresh_at cm cv /\
    not_fresh_at cm src /\ not_fresh_at cm dst /\
    eval_operand cnt m = SOME (n2w c) /\ op_prov H cnt = NONE /\ op_taint u cnt = {} /\
    abi_decode_ptr_window H u m ar (n2w (B+p)) (32+c) /\
    abi_decode_ptr_window H u m src (n2w B) L /\
    lookup_var dst m = SOME (n2w d) /\ ptr_covers H u dst m cap /\
    m.vs_memory = s.vs_memory /\ m.vs_allocas = s.vs_allocas /\
    m.vs_alloca_next = s.vs_alloca_next /\ m.vs_call_ctx = s.vs_call_ctx /\
    m.vs_data_section = s.vs_data_section /\
    (!x. not_fresh_at sa x ==> lookup_var x m = lookup_var x s /\
       FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm
Proof
  strip_tac >>
  `eval_operand (Var src) s = SOME (n2w B) /\ L < dimword (:256)` by
    fs[abi_decode_ptr_window_def, eval_operand_def] >>
  `abi_decode_source_opcode MLOAD` by simp[abiDecoderContractTheory.abi_decode_source_opcode_def] >>
  Q.SUBGOAL_THEN
    `hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
                       p + 32 + c <= h /\ h < dimword (:256)` assume_tac
  >- (disj2_tac >> qexists `L` >> simp[]) >>
  drule abi_decode_bytes_position_prefix_sequence >>
  disch_then (qspecl_then [`s`,`p`,`c`,`B`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  drule abi_decode_bytes_mload_prefix_cuts >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa cm) s = OK t` >>
  rename1 `emit_op MLOAD [Var ar] sp = (cnt,sl)` >>
  qabbrev_tac `hc = emitted_insts sa sh` >>
  qabbrev_tac `lc = emitted_insts sh sp ++ emitted_insts sp sl` >>
  qabbrev_tac `tc = emitted_insts sl cm` >>
  `run_inst_seq (hc ++ (lc ++ tc)) s = OK t` by fs[APPEND_ASSOC] >>
  drule instSeqComposePtrTheory.run_inst_seq_append_ok_split >> strip_tac >>
  rename1 `run_inst_seq hc s = OK h` >>
  qpat_assum `run_inst_seq (lc ++ tc) h = OK t`
    (mp_then Any strip_assume_tac instSeqComposePtrTheory.run_inst_seq_append_ok_split) >>
  rename1 `run_inst_seq lc h = OK l` >>
  `?C. bop_scalar_seq {x | not_fresh_at sa x} {pos;Lit 32w;hi} hc C /\
       head IN C /\ sa.cs_next_var <= sh.cs_next_var /\
       ?x. head = Var x /\ not_fresh_at sh x` by
    (drule (Q.INST [`A` |-> `{pos;Lit 32w;hi}`, `R` |-> `{x | not_fresh_at sa x}`]
       abi_decode_bytes_scalar_head) >> simp[Abbr `hc`] >>
     strip_tac >> qexists `C` >> simp[] >> metis_tac[]) >>
  `!op. op IN {pos;Lit 32w;hi} ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    (simp[] >> rpt strip_tac >> gvs[ptrDisciplineTheory.op_prov_def,
                                    ptrDisciplineTheory.op_taint_def]) >>
  `?Gh th.
      EVERY (\i. ~is_terminator i.inst_opcode) hc /\
      run_inst_seq_mem_ok hc s /\ inst_seq_ptr D 0 ctx fn PG G tn hc s Gh th /\
      op_prov Gh head = NONE /\ op_taint th head = {} /\
      (h with vs_vars := s.vs_vars) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x h = lookup_var x s /\
         FLOOKUP Gh x = FLOOKUP G x /\ op_taint th (Var x) = op_taint tn (Var x)) /\
      th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
      th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm` by
    (drule_all abi_decode_bytes_scalar_cut >>
     disch_then (qspecl_then [`s.vs_inst_idx`,`fn`,`PG`,`D`] strip_assume_tac) >>
     rename1 `inst_seq_ptr _ _ _ _ _ _ _ hc _ Gh th` >>
     qpat_assum `!op. op IN C ==> _` (drule_then strip_assume_tac) >>
     qexistsl_tac [`Gh`,`th`] >> gvs[]) >>
  qabbrev_tac `hi_state = h with vs_inst_idx := s.vs_inst_idx + LENGTH hc` >>
  `abi_decode_ptr_window Gh th hi_state src (n2w B) L` by
    (irule abi_decode_ptr_window_frame >> qexistsl_tac [`G`,`s`,`tn`] >>
     simp[Abbr `hi_state`, lookup_var_def] >> fs[lookup_var_def]) >>
  `h.vs_labels = s.vs_labels /\ h.vs_alloca_next = s.vs_alloca_next` by
    fs[venom_state_component_equality] >>
  `!op. (!v. Var v = op ==> not_fresh_at sa v) ==>
        eval_operand op hi_state = eval_operand op s /\
        op_prov Gh op = op_prov G op /\ op_taint th op = op_taint tn op` by
    (Cases >> simp[Abbr `hi_state`, eval_operand_def,
                   ptrDisciplineTheory.op_prov_def, ptrDisciplineTheory.op_taint_def] >>
     strip_tac >> qpat_assum `!v. not_fresh_at sa v ==> _`
       (drule_then strip_assume_tac) >>
     fs[lookup_var_def, ptrDisciplineTheory.op_taint_def]) >>
  `eval_operand pos hi_state = SOME (n2w p) /\ op_taint th pos = {} /\
   op_prov Gh hi = NONE /\ op_taint th hi = {}` by
    (qpat_assum `!op. _ ==> eval_operand op hi_state = _ /\ _`
       (fn thm => map_every (fn q => qspec_then q mp_tac thm) [`pos`,`hi`]) >>
     `!v. Var v = pos ==> not_fresh_at sa v` by fs[] >>
     `!v. Var v = hi ==> not_fresh_at sa v` by fs[] >>
     simp[] >> rpt strip_tac >> simp[]) >>
  `not_fresh_at sh src /\ B + L <= hi_state.vs_alloca_next` by
    (conj_tac >- (irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[]) >>
     simp[Abbr `hi_state`]) >>
  qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any strip_assume_tac emit_op_facts) >>
  rename1 `cnt = Var cv` >>
  qpat_x_assum `cnt = Var cv` SUBST_ALL_TAC >>
  `EVERY (\i. ~is_terminator i.inst_opcode) lc` by
    (qpat_assum `emit_op ADD _ _ = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     qpat_assum `emit_op MLOAD _ _ = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     simp[Abbr `lc`, mk_inst_def, is_terminator_def]) >>
  drule_all abi_decode_bytes_addr_load >>
  qpat_assum `Abbrev (lc = _)` (fn th => rewrite_tac[GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  rename1 `inst_seq_ptr _ _ _ _ _ _ _ lc _ Gl tl` >>
  rename1 `run_inst_seq lc hi_state = OK li` >>
  `li = l with vs_inst_idx := s.vs_inst_idx + LENGTH hc` by
    (qpat_x_assum `run_inst_seq lc hi_state = OK li` mp_tac >>
     simp[Abbr `hi_state`,run_inst_seq_inst_idx,instIdxIndepTheory.exec_result_map_def] >>
     disch_then (SUBST1_TAC o SYM) >> simp[]) >>
  `run_inst_seq_mem_ok lc h` by
    (fs[Abbr `hi_state`,run_inst_seq_mem_ok_inst_idx] >> (metis_tac[Abbr `hi_state`, run_inst_seq_mem_ok_inst_idx])) >>
  `run_inst_seq lc (h with vs_inst_idx := h.vs_inst_idx) =
   OK (l with vs_inst_idx := h.vs_inst_idx)` by
    simp[run_inst_seq_inst_idx,instIdxIndepTheory.exec_result_map_def] >>
  `l.vs_inst_idx = h.vs_inst_idx` by
    fs[venom_state_component_equality] >>
  `l with vs_vars := h.vs_vars = h` by
    gvs[Abbr `hi_state`,venom_state_component_equality] >>
  `!v. not_fresh_at sa v ==> not_fresh_at sh v` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `!v. not_fresh_at sh v ==> not_fresh_at sl v` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `sh` >> simp[]) >>
  `op_prov Gl head = NONE /\ op_taint tl head = {}` by
    (qpat_assum `!v. not_fresh_at sh v ==> _` (qspec_then `x` mp_tac) >>
     gvs[ptrDisciplineTheory.op_prov_def]) >>
  `op_prov Gl hi = NONE /\ op_taint tl hi = {}` by
    (Cases_on `hi` >> simp[ptrDisciplineTheory.op_prov_def,ptrDisciplineTheory.op_taint_def] >>
     rename1 `op_prov Gh (Var v) = NONE` >>
     `not_fresh_at sh v` by (first_assum irule >> fs[]) >>
     qpat_assum `!v. not_fresh_at sh v ==> lookup_var v li = _ /\ _`
       (qspec_then `v` strip_assume_tac) >>
     fs[ptrDisciplineTheory.op_prov_def,ptrDisciplineTheory.op_taint_def]) >>
  `?C. bop_scalar_seq {v | not_fresh_at sl v}
          {head;Var cv;hi;Lit (n2w n)} tc C /\
       {head;Var cv;hi;Lit (n2w n)} SUBSET C /\ sl.cs_next_var <= cm.cs_next_var` by
    (drule (Q.INST [`A` |-> `{head;Var cv;hi;Lit (n2w n)}`,
                   `R` |-> `{v | not_fresh_at sl v}`]
        abi_decode_bytes_scalar_count_payload) >> simp[Abbr `tc`] >> metis_tac[]) >>
  `!op. op IN {head;Var cv;hi;Lit (n2w n)} ==>
        op_prov Gl op = NONE /\ op_taint tl op = {}` by
    (simp[] >> rpt strip_tac >>
     gvs[ptrDisciplineTheory.op_prov_def, ptrDisciplineTheory.op_taint_def]) >>
  drule_all (Q.INST [`G` |-> `Gl`, `tn` |-> `tl`, `s` |-> `l`, `t` |-> `t`]
      abi_decode_bytes_scalar_cut) >>
  disch_then (qspecl_then [`s.vs_inst_idx + LENGTH (hc ++ lc)`,`fn`,`PG`,`D`] strip_assume_tac) >>
  suspend "join"
QED

Resume abi_decode_valid_bytes_prefix_certificate[join]:
  `run_inst_seq (hc ++ lc) s = OK l` by
    (qpat_assum `run_inst_seq hc s = OK h` (mp_then Any (fn th => simp[th]) run_inst_seq_append)) >>
  `run_inst_seq_mem_ok (hc ++ lc) s` by
    (irule run_inst_seq_mem_ok_append >> simp[]) >>
  `run_inst_seq_mem_ok ((hc ++ lc) ++ tc) s` by
    (irule run_inst_seq_mem_ok_append >> simp[]) >>
  `inst_seq_ptr D 0 ctx fn PG G tn (hc ++ lc) s Gl tl` by
    ((irule bop_inst_seq_ptr_append >> conj_tac >- simp[] >>
     qexistsl_tac [`Gh`,`h`,`th`] >> fs[Abbr `hi_state`] >> (metis_tac[Abbr `hi_state`, bop_inst_seq_ptr_append]))) >>
  `inst_seq_ptr D 0 ctx fn PG G tn ((hc ++ lc) ++ tc) s H u` by
    (irule bop_inst_seq_ptr_append >> conj_tac >- simp[] >>
     qexistsl_tac [`Gl`,`l`,`tl`] >> simp[]) >>
  `t.vs_inst_idx = s.vs_inst_idx` by fs[venom_state_component_equality] >>
  qabbrev_tac `m = t with vs_inst_idx := LENGTH cm.cs_current_insts` >>
  `!v. not_fresh_at sa v ==> lookup_var v m = lookup_var v s /\
        FLOOKUP H v = FLOOKUP G v /\ op_taint u (Var v) = op_taint tn (Var v)` by
    (rpt strip_tac >>
     `not_fresh_at sh v` by simp[] >> `not_fresh_at sl v` by simp[] >>
     qpat_assum `!x. x IN {v | not_fresh_at sl v} ==> _`
       (qspec_then `v` strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at sh x ==> lookup_var x li = _ /\ _`
       (qspec_then `v` strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x h = _ /\ _`
       (qspec_then `v` strip_assume_tac) >>
     fs[Abbr `m`, Abbr `hi_state`, lookup_var_def]) >>
  `not_fresh_at cm ar /\ not_fresh_at cm cv /\
   not_fresh_at cm src /\ not_fresh_at cm dst` by
    (rpt conj_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists `sl` >> simp[]) >>
  `u.t_mem = tl.t_mem /\ u.t_mem = tn.t_mem` by simp[] >>
  `abi_decode_ptr_window H u m ar (n2w (B+p)) (32+c)` by
    (qpat_assum `!x. x IN {v | not_fresh_at sl v} ==> _`
       (qspec_then `ar` (mp_tac o SRULE [])) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     `lookup_var ar m = lookup_var ar li` by fs[Abbr `m`, lookup_var_def] >>
     irule abi_decode_ptr_window_frame >> qexistsl_tac [`Gl`,`li`,`tl`] >> simp[]) >>
  `abi_decode_ptr_window H u m src (n2w B) L` by
    (irule abi_decode_ptr_window_frame >> qexistsl_tac [`G`,`s`,`tn`] >>
     qpat_assum `!v. not_fresh_at sa v ==> lookup_var v m = _ /\ _`
       (qspec_then `src` mp_tac) >> simp[]) >>
  `lookup_var dst m = SOME (n2w d) /\ ptr_covers H u dst m cap` by
    (qpat_assum `!v. not_fresh_at sa v ==> lookup_var v m = _ /\ _`
       (qspec_then `dst` mp_tac) >> (impl_tac >- simp[]) >>
     disch_then (fn th =>
       rewrite_tac[ptr_covers_def, th] >> simp[GSYM ptr_covers_def])) >>
  `op_prov H (Var cv) = NONE /\ op_taint u (Var cv) = {}` by
    (qpat_assum `!op. op IN C' ==> _` (qspec_then `Var cv` mp_tac) >>
     fs[SUBSET_DEF]) >>
  `m.vs_allocas = s.vs_allocas /\ m.vs_alloca_next = s.vs_alloca_next` by
    fs[Abbr `m`, venom_state_component_equality] >>
  qexistsl_tac [`ar`,`cv`,`m`,`H`,`u`] >>
  simp[APPEND_ASSOC, EVERY_APPEND] >>
  fs[Abbr `m`, venom_state_component_equality, fresh_vars_wrt_def]
QED

Finalise abi_decode_valid_bytes_prefix_certificate
