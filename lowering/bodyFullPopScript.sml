Theory bodyFullPop
Ancestors
  bodyFullTarget bodyFullTargetDefs bodyFullPreds bodySimFull bodyFullOfVV
  gasOutcomeFullCompose gasOutcomeFull gasShadowCompile gasShadowState gasShadow
  gasShadowCompileStmtHelpers
  exprSimPopNestedLocalSource exprSimPopNestedLocalHandoff exprSimPopNestedLocalRun
  popTargetPre exprSimHyps exprSimHypsDefs exprSimSource exprSimPopNestedBase
  exprLoweringProps loweringPosts exprLowering compileEnv stmtLoweringMono
  vyperTypeAssignContext exprSimUnwrap targetPtrFacts fragExec
  vyperInterpreter vyperState vyperAST targetSubscriptMemory bodyPtrBopInMemoryContents bodyPtrDefs
  ptrDiscipline venomExecSemantics venomState fragGasSeqPtr
  exprPtrCtorImmStore exprPtrCtorCodeLoad emitHelperProps venomInst decoderGhostFramePtr
  bodyPtrSignedConvertBool fragGasCopyLoop finite_map instSeqComposePtr exprSimPop words instIdxIndep
  fragGasCopySeqLiftProps
  fragExecMem instMemFrontier memSafeRun fragGasEmitCtrl fragGasOriginPtrLoop
  bodyPtrBopAssert gasEvents gasCount unitTransformDefs contextCodegenRel codegenRel ptrSafetyTransport
  stmtReasonLitFragMemory exprSimPopNestedLocalProps vyperLookup
  abiEncodeOwnership valueEncodingProps wordLoadStorePtr mstoreRestorePtr bodyPtrBopScalarStep
  typedCopyPtr bodyPtrAttributeAdd bodyPtrBopScalarSeq
  exprSimMemoryTransport exprSimPopNestedLocalMemory exprSimPopNestedLocalSuffix
  stmtPoppedKeys vyperEvalExprPreservesScopesDom
  bodyFullUnwrapRun bodyFullGhostFrame
  loweringStateRelDefs bodyFullMemoryFrames
  stmtAppendStorageRunPtr payloadLoadStorePtr appendStorageGhostPtr

val _ = Parse.hide "body";

Theorem pop_full_target_pre[local]:
  !cenv cx env ann bt es.
    expr_body_pre cenv cx env (Pop ann bt) es ==>
    target_pre cenv cx env bt es
Proof
  rpt strip_tac >> irule target_pre_of_pop >>
  reverse conj_tac >- (qexists `ann` >> simp[]) >>
  strip_tac >> gvs[targetPlaceSimTheory.immutable_root_def] >>
  drule pop_immutable_root_rejected >>
  disch_then drule >> simp[]
QED

Theorem pop_full_ghost_cursor_unique[local]:
  !code s t G tn H tm H' tm' k.
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
    run_inst_seq code s = OK t /\
    inst_seq_ptr D1 lo ctx fn PG G tn code s H tm /\
    inst_seq_ptr D2 lo ctx fn PG G tn code (s with vs_inst_idx := k) H' tm' ==>
    H' = H /\ tm' = tm
Proof
  Induct >> simp[run_inst_seq_def, inst_seq_ptr_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >>
  gvs[run_inst_seq_def, inst_seq_ptr_def,
    step_inst_inst_idx_indep, exec_result_map_def] >>
  first_x_assum irule >>
  qexistsl_tac [`step_prov PG G h v`, `SUC k`,
    `v with vs_inst_idx := SUC s.vs_inst_idx`,
    `t with vs_inst_idx := SUC s.vs_inst_idx`, `step_taint h s v tn`] >>
  fs[listTheory.EVERY_CONJ, run_inst_seq_inst_idx, exec_result_map_def]
QED

Theorem pop_full_memory_entry[local]:
  ghost_inv_at D lo d cenv cx es G tn s /\
  lookup_scopes id es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME b /\
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV (DynArrayV vs)) /\
  mem_path_offset entry.type path = SOME (k,ArrayTV et (Dynamic cap)) ==>
  ptr_covers G tn p s sz /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory entry.type entry.value (w2n b) mem) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory (ArrayTV et (Dynamic cap)) (ArrayV (DynArrayV vs))
       (w2n b + k) mem) /\
  mem_word_taint tn.t_mem (w2n b + k) = {}
Proof
  strip_tac >>
  `ptr_covers G tn p s sz /\
   (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory entry.type entry.value (w2n b) mem)` by
    (fs[ghost_inv_at_def] >>
     qpat_x_assum `!name entry p sz. _` drule_all >> simp[]) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory (ArrayTV et (Dynamic cap)) (ArrayV (DynArrayV vs))
       (w2n b + k) mem` by
    (rpt strip_tac >> irule targetSubscriptMemoryTheory.mem_path_offset_current_value >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  simp[] >> irule dynarray_memory_header_clean >>
  qexistsl_tac [`cap`, `s.vs_memory`, `et`, `vs`] >> gvs[]
QED

Theorem pop_full_header_coverage[local]:
  ptr_covers G tn p s sz /\ lookup_var p s = SOME b /\
  eval_operand hdr s = SOME a /\ w2n a = w2n b + k /\
  k + 32 <= sz /\ op_taint tn hdr = {} /\
  op_prov G hdr = FLOOKUP G p ==>
  ?q. hdr = Var q /\ ptr_covers G tn q s 32
Proof
  Cases_on `hdr` >>
  gvs[ptr_covers_def, op_prov_def, eval_operand_def] >>
  strip_tac >> gvs[] >>
  goal_assum (drule_at Any) >> decide_tac
QED

(* The loaded length and its ghosts are chosen before the dead-set horizon. *)
Theorem pop_full_memory_load[local]:
  ptr_covers G tn p s 32 /\ lookup_var p s = SOME w /\
  mem_word_taint tn.t_mem (w2n w) = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?u G' tn'.
    u = update_var out (mload (w2n w) s) s /\
    step_inst_base (mk_inst id MLOAD [Var p] [out]) s = OK u /\
    (!D. inst_seq_ptr D lo ctx fn PG G tn
      [mk_inst id MLOAD [Var p] [out]] s G' tn') /\
    op_taint tn' (Var out) = {} /\ op_prov G' (Var out) = NONE /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!q. q <> out ==> FLOOKUP G' q = FLOOKUP G q /\
      op_taint tn' (Var q) = op_taint tn (Var q))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id MLOAD [Var p] [out]) s =
    OK (update_var out (mload (w2n w) s) s)` by
    (irule step_MLOAD >> simp[eval_operand_def]) >>
  qexistsl_tac [`update_var out (mload (w2n w) s) s`,
    `step_prov PG G (mk_inst id MLOAD [Var p] [out])
       (update_var out (mload (w2n w) s) s)`,
    `step_taint (mk_inst id MLOAD [Var p] [out]) s
       (update_var out (mload (w2n w) s) s) tn`] >>
  `eval_operand (Var p) s = SOME w` by simp[eval_operand_def] >>
  simp[inst_seq_ptr_def, ptr_inst_ok_mload_lo, load_word_taint_frame] >>
  conj_tac >- (drule (GEN_ALL (SRULE []
    (Q.INST [`opc` |-> `MLOAD`] load_word_output_taint))) >> simp[]) >>
  conj_tac
  >- (irule step_prov_out_none >> simp[mk_inst_def] >>
      irule out_prov_other_none >> simp[mk_inst_def]) >>
  rpt strip_tac >>
  simp[step_prov_other_output, step_taint_other_output, mk_inst_def]
QED

Theorem pop_full_memory_load_uniform[local]:
  ptr_covers G tn p s 32 /\ lookup_var p s = SOME w /\
  mem_word_taint tn.t_mem (w2n w) = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  inst_seq_ptr D0 lo ctx fn PG G tn [mk_inst id MLOAD [Var p] [out]] s H tm ==>
  !D k. inst_seq_ptr D lo ctx fn PG G tn
    [mk_inst id MLOAD [Var p] [out]] (s with vs_inst_idx := k) H tm
Proof
  rpt strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp (s with vs_inst_idx := k)` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     simp[NoAsms, allocas_below_fmp_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`s` |-> `s with vs_inst_idx := k`] (SPEC_ALL pop_full_memory_load)) >>
  (impl_tac >- (gvs[lookup_var_def, allocas_from_def] >> metis_tac[])) >> strip_tac >>
  `step_inst_base (mk_inst id MLOAD [Var p] [out]) s =
    OK (update_var out (mload (w2n w) s) s)` by
    (irule step_MLOAD >> simp[eval_operand_def]) >>
  `run_inst_seq [mk_inst id MLOAD [Var p] [out]] s =
    OK (update_var out (mload (w2n w) s) s)` by simp[run_inst_seq_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    [mk_inst id MLOAD [Var p] [out]]` by simp[mk_inst_def, is_terminator_def] >>
  `G' = H /\ tn' = tm` by
    (metis_tac[pop_full_ghost_cursor_unique]) >>
  gvs[]
QED

Theorem pop_full_bool_pair[local]:
  op_taint tn x = {} /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  run_inst_seq [mk_inst id ISZERO [x] [a];
    mk_inst (id+1) ISZERO [Var a] [b]] s = OK t ==>
  ?G' tn'.
    (!D. inst_seq_ptr D lo ctx fn PG G tn
      [mk_inst id ISZERO [x] [a]; mk_inst (id+1) ISZERO [Var a] [b]] s G' tn') /\
    op_prov G' (Var b) = NONE /\ op_taint tn' (Var b) = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!q. q <> a /\ q <> b ==> FLOOKUP G' q = FLOOKUP G q /\
      op_taint tn' (Var q) = op_taint tn (Var q))
Proof
  strip_tac >>
  qexistsl_tac [`DRESTRICT (DRESTRICT G (COMPL {a})) (COMPL {b})`,
    `tn with t_var := tn.t_var |+ (a,{}) |+ (b,{})`] >>
  conj_tac
  >- (gen_tac >> irule inst_seq_ptr_lower_bound_transport >>
      simp[mk_inst_def] >> qexists_tac `0` >> simp[] >>
      drule_all iszero_pair_certificate >>
      disch_then (qspecl_then [`fn`, `PG`, `G`, `D`] strip_assume_tac) >> gvs[mk_inst_def]) >>
  simp[op_prov_def, op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  rpt strip_tac >> simp[]
QED

Theorem pop_full_memory_prefix_mem_ok[local]:
  eval_operand hdr s = SOME w /\ w2n w + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok
    [mk_inst id MLOAD [hdr] [x0];
     mk_inst (id+1) ISZERO [Var x0] [x1];
     mk_inst (id+2) ISZERO [Var x1] [x2]] s
Proof
  strip_tac >>
  `!t. run_inst_seq_mem_ok
     [mk_inst (id+1) ISZERO [Var x0] [x1];
      mk_inst (id+2) ISZERO [Var x1] [x2]] t` by
    (gen_tac >> irule run_inst_seq_mem_ok_every >>
     simp[mk_inst_def, inst_dload_in_section_def] >> rpt conj_tac >>
     irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  simp[run_inst_seq_mem_ok_def, below_frontier_MLOAD,
    inst_dload_in_section_def, mk_inst_def] >>
  Cases_on `step_inst_base (mk_inst id MLOAD [hdr] [x0]) s` >> gvs[mk_inst_def]
QED

Theorem pop_full_memory_prefix_run[local]:
  eval_operand hdr s = SOME w ==>
  ?t. run_inst_seq
    [mk_inst id MLOAD [hdr] [x0];
     mk_inst (id+1) ISZERO [Var x0] [x1];
     mk_inst (id+2) ISZERO [Var x1] [x2]] s = OK t /\
    lookup_var x2 t = SOME (bool_to_word (mload (w2n w) s <> 0w)) /\
    (t with vs_vars := s.vs_vars) = s /\
    (!q. q <> x0 /\ q <> x1 /\ q <> x2 ==> lookup_var q t = lookup_var q s)
Proof
  strip_tac >>
  `step_inst_base (mk_inst id MLOAD [hdr] [x0]) s =
    OK (update_var x0 (mload (w2n w) s) s)` by
    (irule step_MLOAD >> simp[]) >>
  simp[run_inst_seq_def, pop_step_ISZERO, lookup_var_def, update_var_def,
    FLOOKUP_UPDATE] >>
  Cases_on `mload (w2n w) s = 0w` >>
  simp[bool_to_word_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
    venom_state_component_equality] >> rpt strip_tac >> simp[]
QED

Theorem pop_full_memory_prefix[local]:
  ptr_covers G tn p s 32 /\ lookup_var p s = SOME w /\
  mem_word_taint tn.t_mem (w2n w) = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  run_inst_seq [mk_inst id MLOAD [Var p] [x0];
    mk_inst (id+1) ISZERO [Var x0] [x1];
    mk_inst (id+2) ISZERO [Var x1] [x2]] s = OK v ==>
  ?G' tn'.
    (!D. inst_seq_ptr D lo ctx fn PG G tn
      [mk_inst id MLOAD [Var p] [x0];
       mk_inst (id+1) ISZERO [Var x0] [x1];
       mk_inst (id+2) ISZERO [Var x1] [x2]] s G' tn') /\
    op_prov G' (Var x2) = NONE /\ op_taint tn' (Var x2) = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!q. q <> x0 /\ q <> x1 /\ q <> x2 ==>
      FLOOKUP G' q = FLOOKUP G q /\
      op_taint tn' (Var q) = op_taint tn (Var q))
Proof
  strip_tac >> drule_all pop_full_memory_load >>
  disch_then (qspecl_then [`x0`, `id`, `fn`, `PG`] strip_assume_tac) >>
  gvs[] >>
  `allocas_from lo (update_var x0 (mload (w2n w) s) s
    with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[allocas_from_def, update_var_def] >>
  `run_inst_seq [mk_inst (id+1) ISZERO [Var x0] [x1];
      mk_inst (id+2) ISZERO [Var x1] [x2]]
      (update_var x0 (mload (w2n w) s) s) = OK v` by
    (qpat_x_assum `run_inst_seq _ s = OK v` mp_tac >>
     simp[Once run_inst_seq_def]) >>
  `run_inst_seq [mk_inst (id+1) ISZERO [Var x0] [x1];
      mk_inst (id+2) ISZERO [Var x1] [x2]]
      (update_var x0 (mload (w2n w) s) s with vs_inst_idx := SUC s.vs_inst_idx) =
      OK (v with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[run_inst_seq_inst_idx, mk_inst_def, is_terminator_def, exec_result_map_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp (update_var x0 (mload (w2n w) s) s
    with vs_inst_idx := SUC s.vs_inst_idx)` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     simp[NoAsms, allocas_below_fmp_def, update_var_def] >> metis_tac[]) >>
  drule_all (GEN_ALL (SRULE [GSYM arithmeticTheory.ADD_ASSOC]
    (Q.INST [`id` |-> `id+1`] pop_full_bool_pair))) >>
  disch_then (qspecl_then [`fn`, `PG`, `G'`] strip_assume_tac) >>
  qexistsl_tac [`G''`, `tn''`] >>
  conj_tac
  >- (gen_tac >>
      ` [mk_inst id MLOAD [Var p] [x0];
         mk_inst (id+1) ISZERO [Var x0] [x1];
         mk_inst (id+2) ISZERO [Var x1] [x2]] =
        [mk_inst id MLOAD [Var p] [x0]] ++
        [mk_inst (id+1) ISZERO [Var x0] [x1];
         mk_inst (id+2) ISZERO [Var x1] [x2]]` by simp[] >>
      pop_assum SUBST1_TAC >> irule inst_seq_ptr_append_ok >>
      conj_tac >- simp[mk_inst_def, is_terminator_def] >>
      qexistsl_tac [`G'`, `update_var x0 (mload (w2n w) s) s`, `tn'`] >>
      gvs[run_inst_seq_def, arithmeticTheory.ADD1]) >>
  simp[] >> rpt strip_tac >> metis_tac[]
QED

Theorem pop_full_clean_word_diff[local]:
  mem_word_taint M off = {} ==>
  M DIFF {i | off <= i /\ i < off + 32} = M
Proof
  simp[mem_word_taint_def, pred_setTheory.EXTENSION] >>
  strip_tac >> gen_tac >>
  `off <= x /\ x < off + 32 ==> x NOTIN M` by
    (strip_tac >> first_x_assum (qspec_then `x - off` mp_tac) >> simp[]) >>
  metis_tac[]
QED

Theorem pop_full_scalar_step[local]:
  MEM opc [SUB; MUL] /\
  EVERY (\op. op_taint tn op = {} /\ op_prov G op = NONE) ops /\
  step_inst_base (mk_inst id opc ops [out]) s = OK u /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?G' tn'.
    (!D. inst_seq_ptr D lo ctx fn PG G tn [mk_inst id opc ops [out]] s G' tn') /\
    op_prov G' (Var out) = NONE /\ op_taint tn' (Var out) = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!q. q <> out ==> FLOOKUP G' q = FLOOKUP G q /\
      op_taint tn' (Var q) = op_taint tn (Var q))
Proof
  strip_tac >>
  `MEM opc [ADD; SUB; MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
    LT; GT; SLT; SGT; EQ; ISZERO; AND; OR; XOR; NOT;
    SHL; SHR; SAR; SIGNEXTEND; BYTE; ASSIGN]` by gvs[] >>
  drule_all bop_scalar_state_frame >> strip_tac >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp` by
    (qpat_x_assum `(u with vs_vars := _) = s` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  drule_all bop_scalar_ghost_frame >>
  disch_then (qspecl_then [`out`, `id`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`step_prov PG G (mk_inst id opc ops [out]) u`,
    `step_taint (mk_inst id opc ops [out]) s u tn`] >>
  conj_tac
  >- (gen_tac >> simp[inst_seq_ptr_def] >>
      irule ptr_inst_ok_lower_bound_transport >> simp[] >>
      qexists_tac `0` >> simp[] >>
      irule bop_scalar_ptr_inst_ok >> simp[] >> qexists_tac `u` >> gvs[]) >>
  simp[] >> rpt strip_tac >> gvs[op_taint_def]
QED

(* Uniqueness of operational ghosts removes the dead-mask witness dependency. *)
Theorem pop_full_scalar_sequence[local]:
  bop_scalar_seq R A code B /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> ALLOCA) code /\
  (!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ run_inst_seq code s = OK t ==>
  ?G' tn'.
    (!D. inst_seq_ptr D lo ctx fn PG G tn code s G' tn') /\
    (!op. op IN B ==> op_prov G' op = NONE /\ op_taint tn' op = {}) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x IN R ==> FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `!D. ?H tm. inst_seq_ptr D 0 ctx fn PG G tn code s H tm /\
    (!op. op IN B ==> op_prov H op = NONE /\ op_taint tm op = {}) /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. x IN R ==> FLOOKUP H x = FLOOKUP G x /\
      FLOOKUP tm.t_var x = FLOOKUP tn.t_var x)` by
    (gen_tac >> irule bop_scalar_seq_run >> goal_assum (drule_at Any) >>
     simp[] >> qexists_tac `A` >> simp[]) >>
  qpat_assum `!D. ?H tm. _` (qspec_then `ARB` strip_assume_tac) >>
  qexistsl_tac [`H`, `tm`] >> reverse conj_tac
  >- (simp[] >> rpt strip_tac >> simp[op_taint_def]) >>
  gen_tac >> first_x_assum (qspec_then `D` strip_assume_tac) >>
  `H' = H /\ tm' = tm` by (irule inst_seq_ptr_ghost_unique >> metis_tac[]) >>
  gvs[] >> irule inst_seq_ptr_lower_bound_transport >> simp[] >>
  qexists_tac `0` >> simp[]
QED

Theorem pop_full_memory_scalar_chunk[local]:
  ALL_DISTINCT [x0;x1;x2;x3] /\
  EVERY (\x. x <> p) [x1;x2;x3] /\
  lookup_var x0 s = SOME n /\ n <> 0w /\
  op_prov G (Var x0) = NONE /\ op_taint tn (Var x0) = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?u G' tn'.
    run_inst_seq [mk_inst id ISZERO [Var x0] [x1];
      mk_inst (id+1) ISZERO [Var x1] [x2];
      mk_inst (id+2) ASSERT [Var x2] [];
      mk_inst (id+3) SUB [Var x0; Lit 1w] [x3]] s = OK u /\
    (!D. inst_seq_ptr D lo ctx fn PG G tn
      [mk_inst id ISZERO [Var x0] [x1];
       mk_inst (id+1) ISZERO [Var x1] [x2];
       mk_inst (id+2) ASSERT [Var x2] [];
       mk_inst (id+3) SUB [Var x0; Lit 1w] [x3]] s G' tn') /\
    lookup_var x3 u = SOME (n - 1w) /\
    (u with vs_vars := s.vs_vars) = s /\
    (!q. q <> x1 /\ q <> x2 /\ q <> x3 ==> lookup_var q u = lookup_var q s) /\
    op_prov G' (Var x3) = NONE /\ op_taint tn' (Var x3) = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!q. q <> x1 /\ q <> x2 /\ q <> x3 ==>
      FLOOKUP G' q = FLOOKUP G q /\ op_taint tn' (Var q) = op_taint tn (Var q))
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `run_inst_seq code s` >>
  `?u. run_inst_seq code s = OK u /\
    lookup_var x3 u = SOME (n - 1w) /\
    (u with vs_vars := s.vs_vars) = s /\
    (!q. q <> x1 /\ q <> x2 /\ q <> x3 ==> lookup_var q u = lookup_var q s)` by
    (fs[lookup_var_def] >>
     simp[Abbr `code`, run_inst_seq_def, pop_step_ISZERO, pop_step_ASSERT,
       pop_step_SUB_lit, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       bool_to_word_def] >>
     simp[venom_state_component_equality] >> rpt strip_tac >> simp[]) >>
  `bop_scalar_seq {q | q <> x1 /\ q <> x2 /\ q <> x3}
    {Var x0; Lit 1w} code
    {Var x3; Var x2; Var x1; Var x0; Lit 1w}` by
    (simp[Abbr `code`, bop_scalar_seq_def, mk_inst_def] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> ALLOCA) code` by
    simp[Abbr `code`, mk_inst_def] >>
  `!op. op IN {Var x0; Lit 1w} ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    (rpt strip_tac >> gvs[] >> simp[op_prov_def, op_taint_def]) >>
  drule_all pop_full_scalar_sequence >>
  disch_then (qspecl_then [`fn`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`u`, `G'`, `tn'`] >> simp[] >> metis_tac[]
QED

Theorem pop_full_memory_scalar_chunk_uniform[local]:
  ALL_DISTINCT [x0;x1;x2;x3] /\
  EVERY (\x. x <> p) [x1;x2;x3] /\
  lookup_var x0 s = SOME n /\ n <> 0w /\
  op_prov G (Var x0) = NONE /\ op_taint tn (Var x0) = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  inst_seq_ptr D0 lo ctx fn PG G tn
    [mk_inst id ISZERO [Var x0] [x1];
     mk_inst (id+1) ISZERO [Var x1] [x2];
     mk_inst (id+2) ASSERT [Var x2] [];
     mk_inst (id+3) SUB [Var x0; Lit 1w] [x3]] s H tm ==>
  !D k. inst_seq_ptr D lo ctx fn PG G tn
    [mk_inst id ISZERO [Var x0] [x1];
     mk_inst (id+1) ISZERO [Var x1] [x2];
     mk_inst (id+2) ASSERT [Var x2] [];
     mk_inst (id+3) SUB [Var x0; Lit 1w] [x3]] (s with vs_inst_idx := k) H tm
Proof
  rpt strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp (s with vs_inst_idx := k)` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     simp[NoAsms, allocas_below_fmp_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`s` |-> `s with vs_inst_idx := k`]
    (SPEC_ALL pop_full_memory_scalar_chunk)) >>
  (impl_tac >- (gvs[lookup_var_def, allocas_from_def] >> metis_tac[])) >> strip_tac >>
  drule_all pop_full_memory_scalar_chunk >>
  disch_then (qspecl_then [`id`, `fn`, `PG`] strip_assume_tac) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    [mk_inst id ISZERO [Var x0] [x1];
     mk_inst (id+1) ISZERO [Var x1] [x2];
     mk_inst (id+2) ASSERT [Var x2] [];
     mk_inst (id+3) SUB [Var x0; Lit 1w] [x3]]` by simp[mk_inst_def, is_terminator_def] >>
  `G' = H /\ tn' = tm` by metis_tac[pop_full_ghost_cursor_unique] >>
  gvs[]
QED

Theorem pop_full_add_step[local]:
  op_taint tn left = {} /\ op_taint tn right = {} /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?u G' tn'.
    u = update_var out (a+b) s /\
    step_inst_base (mk_inst id ADD [left;right] [out]) s = OK u /\
    (!D. inst_seq_ptr D lo ctx fn PG G tn
      [mk_inst id ADD [left;right] [out]] s G' tn') /\
    op_prov G' (Var out) = first_prov G [left;right] /\
    op_taint tn' (Var out) = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!q. q <> out ==> FLOOKUP G' q = FLOOKUP G q /\
      op_taint tn' (Var q) = op_taint tn (Var q))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ADD [left;right] [out]) s =
    OK (update_var out (a+b) s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def] >>
  qexistsl_tac [`update_var out (a+b) s`,
    `step_prov PG G (mk_inst id ADD [left;right] [out]) (update_var out (a+b) s)`,
    `step_taint (mk_inst id ADD [left;right] [out]) s (update_var out (a+b) s) tn`] >>
  simp[] >> conj_tac
  >- (gen_tac >> simp[inst_seq_ptr_def] >>
      irule ptr_inst_ok_lower_bound_transport >> simp[] >>
      qexists_tac `0` >> simp[] >> irule ptr_inst_ok_copy_len_binop >> simp[]) >>
  `op_prov (step_prov PG G (mk_inst id ADD [left;right] [out])
     (update_var out (a+b) s)) (Var out) = first_prov G [left;right]` by
    (simp[op_prov_def, step_prov_def, set_prov_def, out_prov_def, mk_inst_def] >>
     Cases_on `first_prov G [left;right]` >>
     simp[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]) >>
  simp[copy_len_binop_ghost_frame] >>
  irule (cj 3 step_taint_nonmemory_frame) >> simp[mk_inst_def]
QED

Theorem pop_full_add_step_uniform[local]:
  op_taint tn left = {} /\ op_taint tn right = {} /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  inst_seq_ptr D0 lo ctx fn PG G tn [mk_inst id ADD [left;right] [out]] s H tm ==>
  !D k. inst_seq_ptr D lo ctx fn PG G tn
    [mk_inst id ADD [left;right] [out]] (s with vs_inst_idx := k) H tm
Proof
  rpt strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp (s with vs_inst_idx := k)` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     simp[NoAsms, allocas_below_fmp_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`s` |-> `s with vs_inst_idx := k`] (SPEC_ALL pop_full_add_step)) >>
  (impl_tac >- (gvs[eval_operand_def, lookup_var_def, allocas_from_def] >> metis_tac[])) >>
  strip_tac >>
  `step_inst_base (mk_inst id ADD [left;right] [out]) s =
    OK (update_var out (a+b) s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def] >>
  `run_inst_seq [mk_inst id ADD [left;right] [out]] s =
    OK (update_var out (a+b) s)` by simp[run_inst_seq_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    [mk_inst id ADD [left;right] [out]]` by simp[mk_inst_def, is_terminator_def] >>
  `G' = H /\ tn' = tm` by metis_tac[pop_full_ghost_cursor_unique] >> gvs[]
QED

Theorem pop_full_scalar_step_uniform[local]:
  MEM opc [SUB; MUL] /\
  EVERY (\op. op_taint tn op = {} /\ op_prov G op = NONE) ops /\
  step_inst_base (mk_inst id opc ops [out]) s = OK u /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  inst_seq_ptr D0 lo ctx fn PG G tn [mk_inst id opc ops [out]] s H tm ==>
  !D k. inst_seq_ptr D lo ctx fn PG G tn
    [mk_inst id opc ops [out]] (s with vs_inst_idx := k) H tm
Proof
  rpt strip_tac >>
  `step_inst_base (mk_inst id opc ops [out]) (s with vs_inst_idx := k) =
    OK (u with vs_inst_idx := k)` by
    (gvs[] >> simp[step_inst_inst_idx_indep, exec_result_map_def,
      mk_inst_def, is_terminator_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp (s with vs_inst_idx := k)` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     simp[NoAsms, allocas_below_fmp_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`s` |-> `s with vs_inst_idx := k`, `u` |-> `u with vs_inst_idx := k`]
    (SPEC_ALL pop_full_scalar_step)) >>
  (impl_tac >- (gvs[allocas_from_def] >> metis_tac[])) >> strip_tac >>
  `run_inst_seq [mk_inst id opc ops [out]] s = OK u` by
    (gvs[] >> simp[run_inst_seq_def, mk_inst_def, is_terminator_def]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    [mk_inst id opc ops [out]]` by gvs[mk_inst_def, is_terminator_def] >>
  `G' = H /\ tn' = tm` by metis_tac[pop_full_ghost_cursor_unique] >> gvs[]
QED

Theorem pop_full_memory_mem_ok[local]:
  ALL_DISTINCT [x0;x1;x2;x3;x4;x5;x6] /\
  EVERY (\x. x <> p) [x0;x1;x2;x3;x4;x5;x6] /\
  lookup_var p s = SOME w /\ w2n w + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (memory_pop_insts (Var p) id esz x0 x1 x2 x3 x4 x5 x6) s
Proof
  strip_tac >>
  `!t. run_inst_seq_mem_ok
    [mk_inst (id+6) ADD [Var p; Lit 32w] [x4];
     mk_inst (id+7) MUL [Var x3; Lit (n2w esz)] [x5];
     mk_inst (id+8) ADD [Var x4; Var x5] [x6]] t` by
    (gen_tac >> irule run_inst_seq_mem_ok_every >>
     simp[mk_inst_def, inst_dload_in_section_def] >> rpt conj_tac >>
     irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  `step_inst_base (mk_inst id MLOAD [Var p] [x0]) s =
    OK (update_var x0 (mload (w2n w) s) s)` by
    (irule step_MLOAD >> simp[eval_operand_def]) >>
  `!j opc args outs t. MEM opc [ISZERO; ASSERT; SUB] ==>
    inst_mem_below_frontier (mk_inst j opc args outs) t` by
    (rpt strip_tac >> irule below_frontier_no_ranges >>
     gvs[mk_inst_def]) >>
  fs[] >>
  simp[memory_pop_insts_def, run_inst_seq_mem_ok_def,
    below_frontier_MLOAD, below_frontier_MSTORE, inst_dload_in_section_def,
    pop_step_ISZERO, pop_step_ASSERT, pop_step_SUB_lit,
    eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
    bool_to_word_def] >>
  Cases_on `mload (w2n w) s = 0w` >>
  simp[pop_step_SUB_lit, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  Cases_on `step_inst_base (mk_inst (id+5) MSTORE [Var p; Var x3] [])
    (s with vs_vars := s.vs_vars |+ (x0,mload (w2n w) s) |+ (x1,0w) |+
      (x2,1w) |+ (x3,mload (w2n w) s - 1w))` >> gvs[lookup_var_def]
QED

Theorem pop_full_memory_store_ghost[local]:
  lookup_var p s = SOME a /\ eval_operand value s = SOME w /\
  op_taint tn value = {} /\ mem_word_taint tn.t_mem (w2n a) = {} ==>
  step_prov PG G (mk_inst id MSTORE [Var p; value] []) (mstore (w2n a) w s) = G /\
  step_taint (mk_inst id MSTORE [Var p; value] []) s (mstore (w2n a) w s) tn = tn
Proof
  strip_tac >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`, `G`, `id`] strip_assume_tac) >>
  simp[] >>
  `tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32} = tn.t_mem` by
    (irule pop_full_clean_word_diff >> simp[]) >>
  simp[taint_component_equality] >>
  simp[step_taint_def, mk_inst_def, imm_taint_def]
QED

Theorem pop_full_memory_store[local]:
  ptr_covers G tn p s 32 /\ lookup_var p s = SOME a /\
  eval_operand value s = SOME w /\ op_taint tn value = {} /\
  mem_word_taint tn.t_mem (w2n a) = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  step_inst_base (mk_inst id MSTORE [Var p; value] []) s =
    OK (mstore (w2n a) w s) /\
  (!D. inst_seq_ptr D lo ctx fn PG G tn
    [mk_inst id MSTORE [Var p; value] []] s G tn)
Proof
  strip_tac >>
  `step_inst_base (mk_inst id MSTORE [Var p; value] []) s =
    OK (mstore (w2n a) w s)` by
    (irule step_MSTORE >> simp[eval_operand_def]) >>
  drule_all pop_full_memory_store_ghost >>
  disch_then (qspecl_then [`id`, `PG`, `G`] strip_assume_tac) >>
  simp[inst_seq_ptr_def] >> gen_tac >>
  irule ptr_inst_ok_lower_bound_transport >> simp[] >>
  qexists_tac `0` >> simp[] >>
  irule fragExecPtrTheory.ptr_inst_ok_mstore >> simp[]
QED

Theorem pop_full_memory_store_uniform[local]:
  ptr_covers G tn p s 32 /\ lookup_var p s = SOME a /\
  eval_operand value s = SOME w /\ op_taint tn value = {} /\
  mem_word_taint tn.t_mem (w2n a) = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  !D k. inst_seq_ptr D lo ctx fn PG G tn
    [mk_inst id MSTORE [Var p; value] []] (s with vs_inst_idx := k) G tn
Proof
  rpt strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp (s with vs_inst_idx := k)` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     simp[NoAsms, allocas_below_fmp_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`s` |-> `s with vs_inst_idx := k`]
    (SPEC_ALL pop_full_memory_store)) >>
  (impl_tac >- (gvs[lookup_var_def, allocas_from_def, eval_operand_def] >> metis_tac[])) >>
  simp[]
QED

Theorem pop_full_memory_address_tail[local]:
  ALL_DISTINCT [p;x3;x4;x5;x6] /\
  lookup_var p s = SOME w /\ lookup_var x3 s = SOME n /\
  op_taint tn (Var p) = {} /\ op_taint tn (Var x3) = {} /\
  op_prov G (Var x3) = NONE /\ allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?u G' tn'.
    run_inst_seq [mk_inst j ADD [Var p;Lit 32w] [x4];
      mk_inst (j+1) MUL [Var x3;Lit (n2w esz)] [x5];
      mk_inst (j+2) ADD [Var x4;Var x5] [x6]] s = OK u /\
    (!D k. inst_seq_ptr D lo ctx fn PG G tn
      [mk_inst j ADD [Var p;Lit 32w] [x4];
       mk_inst (j+1) MUL [Var x3;Lit (n2w esz)] [x5];
       mk_inst (j+2) ADD [Var x4;Var x5] [x6]]
      (s with vs_inst_idx := k) G' tn') /\
    lookup_var x6 u = SOME ((w+32w)+n*n2w esz) /\
    (u with vs_vars := s.vs_vars) = s /\
    (!q. q <> x4 /\ q <> x5 /\ q <> x6 ==> lookup_var q u = lookup_var q s) /\
    op_prov G' (Var x6) = op_prov G (Var p) /\ op_taint tn' (Var x6) = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!q. q <> x4 /\ q <> x5 /\ q <> x6 ==>
      FLOOKUP G' q = FLOOKUP G q /\ op_taint tn' (Var q) = op_taint tn (Var q))
Proof
  strip_tac >>
  mp_tac (Q.INST [`left` |-> `Var p`, `right` |-> `Lit 32w`,
    `out` |-> `x4`, `id` |-> `j`, `a` |-> `w`, `b` |-> `32w`]
    (SPEC_ALL pop_full_add_step)) >>
  (impl_tac >- simp[eval_operand_def, op_taint_def]) >> strip_tac >>
  qpat_x_assum `u = _` SUBST_ALL_TAC >>
  qmatch_asmsub_abbrev_tac `step_inst_base _ s = OK s1` >>
  `allocas_from lo s1 /\ lookup_var x3 s1 = SOME n` by
    (gvs[Abbr `s1`, allocas_from_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     metis_tac[]) >>
  `step_inst_base (mk_inst (j+1) MUL [Var x3;Lit (n2w esz)] [x5]) s1 =
    OK (update_var x5 (n*n2w esz) s1)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, eval_operand_def] >>
  `EVERY (\op. op_taint tn' op = {} /\ op_prov G' op = NONE)
    [Var x3;Lit (n2w esz)]` by
    (gvs[op_prov_def, op_taint_def] >> metis_tac[]) >>
  `MEM MUL [SUB; MUL]` by simp[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s1` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     simp[NoAsms, allocas_below_fmp_def, Abbr `s1`, update_var_def] >> metis_tac[]) >>
  drule_all pop_full_scalar_step >>
  disch_then (qspecl_then [`fn`, `PG`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `step_inst_base _ s1 = OK s2` >>
  `allocas_from lo s2 /\ eval_operand (Var x4) s2 = SOME (w+32w) /\
    eval_operand (Var x5) s2 = SOME (n*n2w esz)` by
    (gvs[Abbr `s2`, Abbr `s1`, allocas_from_def, eval_operand_def,
      lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s2` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     simp[NoAsms, allocas_below_fmp_def, Abbr `s2`, Abbr `s1`, update_var_def] >> metis_tac[]) >>
  `op_taint tn'' (Var x4) = {}` by (fs[] >> metis_tac[]) >>
  mp_tac (Q.INST [`left` |-> `Var x4`, `right` |-> `Var x5`,
    `out` |-> `x6`, `id` |-> `j+2`, `a` |-> `w+32w`, `b` |-> `n*n2w esz`,
    `s` |-> `s2`, `G` |-> `G''`, `tn` |-> `tn''`] (SPEC_ALL pop_full_add_step)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `op_prov H (Var x6) = first_prov G'' [Var x4;Var x5]` >>
  rename1 `op_taint tm (Var x6) = {}` >>
  `!D k. inst_seq_ptr D lo ctx fn PG G tn
    [mk_inst j ADD [Var p;Lit 32w] [x4]] (s with vs_inst_idx := k) G' tn'` by
    (rpt gen_tac >> irule pop_full_add_step_uniform >>
     simp[eval_operand_def, op_taint_def]) >>
  `!D k. inst_seq_ptr D lo ctx fn PG G' tn'
    [mk_inst (j+1) MUL [Var x3;Lit (n2w esz)] [x5]]
    (s1 with vs_inst_idx := k) G'' tn''` by
    (metis_tac[pop_full_scalar_step_uniform]) >>
  `!D k. inst_seq_ptr D lo ctx fn PG G'' tn''
    [mk_inst (j+2) ADD [Var x4;Var x5] [x6]]
    (s2 with vs_inst_idx := k) H tm` by
    (metis_tac[pop_full_add_step_uniform]) >>
  qexistsl_tac [`u`, `H`, `tm`] >>
  conj_tac >- simp[run_inst_seq_def] >>
  conj_tac
  >- (gen_tac >>
      `[mk_inst j ADD [Var p;Lit 32w] [x4];
        mk_inst (j+1) MUL [Var x3;Lit (n2w esz)] [x5];
        mk_inst (j+2) ADD [Var x4;Var x5] [x6]] =
       [mk_inst j ADD [Var p;Lit 32w] [x4]] ++
       [mk_inst (j+1) MUL [Var x3;Lit (n2w esz)] [x5];
        mk_inst (j+2) ADD [Var x4;Var x5] [x6]]` by simp[] >>
      pop_assum SUBST1_TAC >> irule inst_seq_ptr_uniform_append >>
      reverse conj_tac >- simp[mk_inst_def, is_terminator_def] >>
      qexistsl_tac [`G'`, `s1`, `tn'`] >> simp[run_inst_seq_def] >>
      `[mk_inst (j+1) MUL [Var x3;Lit (n2w esz)] [x5];
        mk_inst (j+2) ADD [Var x4;Var x5] [x6]] =
       [mk_inst (j+1) MUL [Var x3;Lit (n2w esz)] [x5]] ++
       [mk_inst (j+2) ADD [Var x4;Var x5] [x6]]` by simp[] >>
      pop_assum SUBST1_TAC >> irule inst_seq_ptr_uniform_append >>
      reverse conj_tac >- simp[mk_inst_def, is_terminator_def] >>
      qexistsl_tac [`G''`, `s2`, `tn''`] >> simp[run_inst_seq_def]) >>
  `first_prov G [Var p;Lit 32w] = op_prov G (Var p)` by
    (simp[first_prov_def, op_prov_def] >> Cases_on `FLOOKUP G p` >> simp[]) >>
  `op_prov G'' (Var x4) = op_prov G (Var p)` by
    (fs[op_prov_def] >> metis_tac[]) >>
  simp[first_prov_def] >>
  Cases_on `op_prov G (Var p)` >>
  gvs[first_prov_def, Abbr `s1`, Abbr `s2`, update_var_def,
    lookup_var_def, FLOOKUP_UPDATE, venom_state_component_equality]
QED

Theorem pop_full_memory_checked_run[local]:
  ALL_DISTINCT [x0;x1;x2;x3;x4;x5;x6] /\
  EVERY (\x. x <> p) [x0;x1;x2;x3;x4;x5;x6] /\
  ptr_covers G tn p s 32 /\ lookup_var p s = SOME w /\
  mem_word_taint tn.t_mem (w2n w) = {} /\ mload (w2n w) s <> 0w /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?u G' tn'.
    run_inst_seq (memory_pop_insts (Var p) id esz x0 x1 x2 x3 x4 x5 x6) s = OK u /\
    (!D. inst_seq_ptr D lo ctx fn PG G tn
      (memory_pop_insts (Var p) id esz x0 x1 x2 x3 x4 x5 x6) s G' tn') /\
    op_prov G' (Var x6) = op_prov G (Var p) /\ op_taint tn' (Var x6) = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!q. ~MEM q [x0;x1;x2;x3;x4;x5;x6] ==>
      FLOOKUP G' q = FLOOKUP G q /\ op_taint tn' (Var q) = op_taint tn (Var q))
Proof
  strip_tac >>
  drule_all pop_full_memory_load >>
  disch_then (qspecl_then [`x0`, `id`, `fn`, `PG`] strip_assume_tac) >>
  gvs[] >>
  qmatch_asmsub_abbrev_tac `step_inst_base _ s = OK s1` >>
  `lookup_var x0 s1 = SOME (mload (w2n w) s) /\ allocas_from lo s1` by
    simp[Abbr `s1`, lookup_var_def, update_var_def, FLOOKUP_UPDATE, allocas_from_def] >>
  `ALL_DISTINCT [x0;x1;x2;x3] /\ EVERY (\x. x <> p) [x1;x2;x3]` by fs[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s1` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     simp[NoAsms, allocas_below_fmp_def, Abbr `s1`, update_var_def] >> metis_tac[]) >>
  drule_all pop_full_memory_scalar_chunk >>
  disch_then (qspecl_then [`id+1`, `fn`, `PG`] strip_assume_tac) >>
  `lookup_var p u = SOME w` by
    (simp[Abbr `s1`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     metis_tac[lookup_var_def]) >>
  `ptr_covers G'' tn'' p u 32` by
    (irule ptr_covers_frame >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (qpat_assum `(u with vs_vars := _) = s1` mp_tac >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s1` mp_tac >>
     simp[NoAsms, venom_state_component_equality, allocas_below_fmp_def] >>
     metis_tac[]) >>
  `allocas_from lo u` by
    (qpat_x_assum `(u with vs_vars := _) = s1` mp_tac >>
     simp[venom_state_component_equality] >> strip_tac >> fs[allocas_from_def] >>
     rpt strip_tac >> qpat_x_assum `!aid b sz. FLOOKUP s1.vs_allocas aid = _ ==> _` drule >> simp[]) >>
  `eval_operand (Var x3) u = SOME (mload (w2n w) s - 1w) /\
   mem_word_taint tn''.t_mem (w2n w) = {}` by
    simp[eval_operand_def] >>
  drule_all pop_full_memory_store >>
  disch_then (qspecl_then [`id+5`, `fn`, `PG`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `step_inst_base _ u = OK s2` >>
  `allocas_from lo s2 /\ eval_operand (Var p) s2 = SOME w /\
   eval_operand (Lit 32w) s2 = SOME 32w /\
   op_taint tn'' (Var p) = {} /\ op_taint tn'' (Lit 32w) = {}` by
    (simp[Abbr `s2`, allocas_from_def, mstore_def, write_memory_def,
      write_memory_with_expansion_def, eval_operand_def, lookup_var_def, op_taint_def] >>
     gvs[ptr_covers_def, lookup_var_def, op_taint_def, allocas_from_def] >> metis_tac[]) >>
  `ALL_DISTINCT [p;x3;x4;x5;x6] /\ lookup_var p s2 = SOME w /\
   lookup_var x3 s2 = SOME (mload (w2n w) s - 1w)` by
    (simp[Abbr `s2`, mstore_def, write_memory_def,
      write_memory_with_expansion_def, lookup_var_def] >> fs[lookup_var_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s2` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp u` mp_tac >>
     simp[NoAsms, Abbr `s2`, allocas_below_fmp_def, mstore_def, write_memory_def,
       write_memory_with_expansion_def] >> metis_tac[]) >>
  drule_all pop_full_memory_address_tail >>
  disch_then (qspecl_then [`id+6`, `fn`, `esz`, `PG`] strip_assume_tac) >>
  rename1 `op_prov H (Var x6) = op_prov G'' (Var p)` >>
  rename1 `op_taint tm (Var x6) = {}` >>
  `!D k. inst_seq_ptr D lo ctx fn PG G tn
    [mk_inst id MLOAD [Var p] [x0]] (s with vs_inst_idx := k) G' tn'` by
    metis_tac[pop_full_memory_load_uniform] >>
  `!D k. inst_seq_ptr D lo ctx fn PG G' tn'
    [mk_inst (id+1) ISZERO [Var x0] [x1];
     mk_inst (id+1+1) ISZERO [Var x1] [x2];
     mk_inst (id+1+2) ASSERT [Var x2] [];
     mk_inst (id+1+3) SUB [Var x0;Lit 1w] [x3]]
    (s1 with vs_inst_idx := k) G'' tn''` by
    metis_tac[pop_full_memory_scalar_chunk_uniform] >>
  `!D k. inst_seq_ptr D lo ctx fn PG G'' tn''
    [mk_inst (id+5) MSTORE [Var p;Var x3] []]
    (u with vs_inst_idx := k) G'' tn''` by
    metis_tac[pop_full_memory_store_uniform] >>
  qmatch_asmsub_abbrev_tac `run_inst_seq tail s2 = OK u'` >>
  qmatch_asmsub_abbrev_tac `run_inst_seq chunk s1 = OK u` >>
  qabbrev_tac `load = [mk_inst id MLOAD [Var p] [x0]]` >>
  qabbrev_tac `store = [mk_inst (id+5) MSTORE [Var p;Var x3] []]` >>
  `memory_pop_insts (Var p) id esz x0 x1 x2 x3 x4 x5 x6 =
    load ++ (chunk ++ (store ++ tail))` by
    simp[memory_pop_insts_def, Abbr `load`, Abbr `chunk`, Abbr `store`, Abbr `tail`] >>
  `run_inst_seq load s = OK s1 /\ run_inst_seq store u = OK s2` by
    simp[Abbr `load`, Abbr `store`, run_inst_seq_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) load /\
   EVERY (\i. ~is_terminator i.inst_opcode) chunk /\
   EVERY (\i. ~is_terminator i.inst_opcode) store` by
    simp[Abbr `load`, Abbr `chunk`, Abbr `store`, mk_inst_def, is_terminator_def] >>
  `!D k. inst_seq_ptr D lo ctx fn PG G'' tn'' (store ++ tail)
    (u with vs_inst_idx := k) H tm` by metis_tac[inst_seq_ptr_uniform_append] >>
  `!D k. inst_seq_ptr D lo ctx fn PG G' tn' (chunk ++ (store ++ tail))
    (s1 with vs_inst_idx := k) H tm` by metis_tac[inst_seq_ptr_uniform_append] >>
  `!D k. inst_seq_ptr D lo ctx fn PG G tn
    (load ++ (chunk ++ (store ++ tail))) (s with vs_inst_idx := k) H tm` by
    metis_tac[inst_seq_ptr_uniform_append] >>
  qexistsl_tac [`u'`, `H`, `tm`] >>
  conj_tac >- (qpat_assum `memory_pop_insts (Var p) id esz x0 x1 x2 x3 x4 x5 x6 = _`
      SUBST1_TAC >>
    qpat_assum `run_inst_seq load s = OK s1`
      (mp_then Any (qspec_then `chunk ++ (store ++ tail)` SUBST1_TAC)
        run_inst_seq_append) >>
    qpat_assum `run_inst_seq chunk s1 = OK u`
      (mp_then Any (qspec_then `store ++ tail` SUBST1_TAC) run_inst_seq_append) >>
    qpat_assum `run_inst_seq store u = OK s2`
      (mp_then Any (qspec_then `tail` SUBST1_TAC) run_inst_seq_append) >>
    first_assum ACCEPT_TAC) >>
  conj_tac >- (gen_tac >> first_x_assum (qspecl_then [`D`, `s.vs_inst_idx`] mp_tac) >> simp[]) >>
  fs[op_prov_def] >> metis_tac[]
QED

Theorem pop_memory_empty_selected:
  ptr_covers G tn p s 32 /\ lookup_var p s = SOME w /\
  mem_word_taint tn.t_mem (w2n w) = {} /\
  w2n w + 32 <= s.vs_alloca_next /\ mload (w2n w) s = 0w /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id MLOAD [Var p] [x0];
    mk_inst (id+1) ISZERO [Var x0] [x1];
    mk_inst (id+2) ISZERO [Var x1] [x2]]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  get_instruction bb (s.vs_inst_idx + 3) =
    SOME (mk_inst (id+3) ASSERT [Var x2] []) ==>
  ?t v G' tn'.
    run_inst_seq [mk_inst id MLOAD [Var p] [x0];
      mk_inst (id+1) ISZERO [Var x0] [x1];
      mk_inst (id+2) ISZERO [Var x1] [x2]] s = OK t /\
    let u = t with vs_inst_idx := s.vs_inst_idx + 3 in
      ~u.vs_halted /\
      lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb u.vs_inst_idx = SOME (mk_inst (id+3) ASSERT [Var x2] []) /\
      lookup_var x2 u = SOME 0w /\
      (!fuel. step_inst fuel ctx (mk_inst (id+3) ASSERT [Var x2] []) u =
        Abort Revert_abort v) /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
             (OK u,G',tn') /\
           gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (u,G',tn') []
             (Abort Revert_abort v,G',tn') /\
           gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
             (Abort Revert_abort v,G',tn'))
Proof
  strip_tac >>
  `eval_operand (Var p) s = SOME w` by simp[eval_operand_def] >>
  drule pop_full_memory_prefix_run >>
  disch_then (qspecl_then [`x2`, `x1`, `x0`, `id`] strip_assume_tac) >>
  drule_all pop_full_memory_prefix >>
  disch_then (qspecl_then [`fn`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`t`, `revert_state (set_returndata []
    (t with vs_inst_idx := s.vs_inst_idx + 3))`, `G'`, `tn'`] >>
  `~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\ allocas_from lo t` by
    (gvs[venom_state_component_equality, allocas_from_def] >> metis_tac[]) >>
  `lookup_var x2 (t with vs_inst_idx := s.vs_inst_idx + 3) = SOME 0w` by
    fs[lookup_var_def, bool_to_word_def] >>
  `step_inst_base (mk_inst (id+3) ASSERT [Var x2] [])
     (t with vs_inst_idx := s.vs_inst_idx + 3) =
    Abort Revert_abort (revert_state (set_returndata []
      (t with vs_inst_idx := s.vs_inst_idx + 3)))` by
    simp[pop_step_ASSERT] >>
  simp[LET_THM, step_inst_non_invoke, mk_inst_def] >>
  gen_tac >>
  conj_asm1_tac >-
    (`run_inst_seq_mem_ok [mk_inst id MLOAD [Var p] [x0];
       mk_inst (id+1) ISZERO [Var x0] [x1];
       mk_inst (id+2) ISZERO [Var x1] [x2]] s` by
       (irule pop_full_memory_prefix_mem_ok >> simp[]) >>
     `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
       [mk_inst id MLOAD [Var p] [x0];
        mk_inst (id+1) ISZERO [Var x0] [x1];
        mk_inst (id+2) ISZERO [Var x1] [x2]]` by
       simp[mk_inst_def, is_terminator_def] >>
     `(ctx_has_dalloca ctx ==> !pre i post u.
         [mk_inst id MLOAD [Var p] [x0];
          mk_inst (id+1) ISZERO [Var x0] [x1];
          mk_inst (id+2) ISZERO [Var x1] [x2]] = pre ++ i::post /\
         run_inst_seq pre s = OK u ==> dalloca_no_wrap i u)` by
       (rpt strip_tac >>
        qpat_x_assum `_ = _ ++ i::_` (mp_tac o Q.AP_TERM `MEM i`) >>
        simp[] >> disch_then (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) >>
        simp[dalloca_no_wrap_def,mk_inst_def]) >>
     qpat_assum `!D. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `D` assume_tac) >>
     drule_all run_inst_seq_gas_origin_ptr_path >>
     simp[mk_inst_def]) >>
  conj_asm1_tac >-
    (`ctx_has_dalloca ctx ==> allocas_below_fmp (t with vs_inst_idx := s.vs_inst_idx + 3)` by
       (qpat_assum `(t with vs_vars := _) = s` mp_tac >>
        qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
        simp[NoAsms, venom_state_component_equality, allocas_below_fmp_def] >>
        metis_tac[]) >>
     `ptr_inst_ok D lo 0 ctx fn G' tn' (mk_inst (id+3) ASSERT [Var x2] [])
        (t with vs_inst_idx := s.vs_inst_idx + 3)` by
       (irule ptr_inst_ok_lower_bound_transport >>
        conj_tac >- (fs[allocas_from_def] >> metis_tac[]) >> qexists_tac `0` >>
        simp[] >> irule bop_assert_ptr_inst_ok >> simp[]) >>
     irule exit_inst_origin_ptr >> simp[exit_result_def] >>
     simp[step_inst_non_invoke, pop_step_ASSERT, lookup_var_def,
       bool_to_word_def, gas_events_step_def, gas_count_step_def,
       mem_safe_step_non_invoke, dalloca_no_wrap_def, mk_inst_def,
       inst_mem_below_frontier_def, inst_dload_in_section_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
  metis_tac[gas_origin_ptr_path_trans]
QED

Theorem pop_full_memory_empty_path[local]:
  ptr_covers G tn p s 32 /\ lookup_var p s = SOME w /\
  mem_word_taint tn.t_mem (w2n w) = {} /\
  w2n w + 32 <= s.vs_alloca_next /\ mload (w2n w) s = 0w /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id MLOAD [Var p] [x0];
    mk_inst (id+1) ISZERO [Var x0] [x1];
    mk_inst (id+2) ISZERO [Var x1] [x2]]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  get_instruction bb (s.vs_inst_idx + 3) =
    SOME (mk_inst (id+3) ASSERT [Var x2] []) ==>
  ?v G' tn'. !D.
    gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (Abort Revert_abort v,G',tn')
Proof
  strip_tac >> drule_all pop_memory_empty_selected >> simp[] >> metis_tac[]
QED

Theorem pop_full_storage_load[local]:
  eval_operand hdr s = SOME slot /\ op_taint tn hdr = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?u G' tn'.
    u = update_var out (if tr then tload slot s else sload slot s) s /\
    step_inst_base (mk_inst id (if tr then TLOAD else SLOAD) [hdr] [out]) s = OK u /\
    (!D k. inst_seq_ptr D lo ctx fn PG G tn
      [mk_inst id (if tr then TLOAD else SLOAD) [hdr] [out]]
      (s with vs_inst_idx := k) G' tn') /\
    op_prov G' (Var out) = NONE /\ op_taint tn' (Var out) = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!q. q <> out ==> FLOOKUP G' q = FLOOKUP G q /\
      op_taint tn' (Var q) = op_taint tn (Var q))
Proof
  strip_tac >>
  qabbrev_tac `u = update_var out (if tr then tload slot s else sload slot s) s` >>
  qabbrev_tac `i = mk_inst id (if tr then TLOAD else SLOAD) [hdr] [out]` >>
  `i.inst_opcode <> INVOKE` by (Cases_on `tr` >> simp[Abbr `i`,mk_inst_def]) >>
  `~is_terminator i.inst_opcode` by
    (Cases_on `tr` >> simp[Abbr `i`,mk_inst_def,is_terminator_def]) >>
  `step_inst_base i s = OK u` by
    simp[Abbr `i`, Abbr `u`, nested_pop_step_load] >>
  `step_taint i s u tn = tn with t_var := tn.t_var |+ (out,{})` by
    (simp[Abbr `i`] >> irule scalar_storage_load_taint >>
     simp[Abbr `u`, update_var_def]) >>
  qexistsl_tac [`u`, `step_prov PG G i u`, `tn with t_var := tn.t_var |+ (out,{})`] >>
  simp[op_taint_def, FLOOKUP_UPDATE] >> conj_tac
  >- (rpt gen_tac >> simp[inst_seq_ptr_def, step_inst_inst_idx_indep,
        exec_result_map_def] >>
      irule ptr_inst_ok_lower_bound_transport >> simp[allocas_from_def] >>
      qexists_tac `0` >> simp[Abbr `i`] >>
      `ctx_has_dalloca ctx ==> allocas_below_fmp (s with vs_inst_idx := k)` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     simp[NoAsms, allocas_below_fmp_def] >> metis_tac[]) >>
      irule ptr_inst_ok_storage_load_payload >> simp[] >>
      qexists_tac `u with vs_inst_idx := k` >>
      Cases_on `tr` >>
      gvs[Abbr `u`, update_var_def,step_inst_inst_idx_indep,
        mk_inst_def,is_terminator_def,exec_result_map_def]) >>
  conj_tac
  >- (simp[Abbr `i`] >> irule payload_load_provenance >> Cases_on `tr` >> simp[]) >>
  rpt strip_tac >> simp[Abbr `i`, scalar_step_old_prov, op_taint_def, FLOOKUP_UPDATE]
QED

Theorem pop_full_storage_store[local]:
  eval_operand hdr s = SOME slot /\ lookup_var x s = SOME w /\
  op_taint tn hdr = {} /\ op_taint tn (Var x) = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_call_ctx.cc_static ==>
  !D k. inst_seq_ptr D lo ctx fn PG G tn
    [mk_inst id (if tr then TSTORE else SSTORE) [hdr;Var x] []]
    (s with vs_inst_idx := k) G
    (if tr then tn with t_trans := key_update tn.t_trans slot {}
     else tn with t_stor := key_update tn.t_stor slot {})
Proof
  strip_tac >>
  qabbrev_tac `u = if tr then tstore slot w s else sstore slot w s` >>
  qabbrev_tac `i = mk_inst id (if tr then TSTORE else SSTORE) [hdr;Var x] []` >>
  `i.inst_opcode <> INVOKE` by (Cases_on `tr` >> simp[Abbr `i`,mk_inst_def]) >>
  `~is_terminator i.inst_opcode` by
    (Cases_on `tr` >> simp[Abbr `i`,mk_inst_def,is_terminator_def]) >>
  `step_inst_base i s = OK u` by
    simp[Abbr `i`, Abbr `u`, nested_pop_step_store] >>
  `step_taint i s u tn =
    if tr then tn with t_trans := key_update tn.t_trans slot {}
    else tn with t_stor := key_update tn.t_stor slot {}` by
    (simp[Abbr `i`] >> irule scalar_storage_store_taint >>
     simp[eval_operand_def, Abbr `u`] >> Cases_on `tr` >> simp[sstore_def,tstore_def]) >>
  rpt gen_tac >> simp[inst_seq_ptr_def, step_inst_inst_idx_indep,
    exec_result_map_def, Abbr `i`, scalar_void_prov] >>
  irule ptr_inst_ok_lower_bound_transport >> simp[allocas_from_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp (s with vs_inst_idx := k)` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     simp[NoAsms, allocas_below_fmp_def] >> metis_tac[]) >>
  qexists_tac `0` >> simp[] >> irule append_scalar_inst_check >>
  Cases_on `tr` >> gvs[Abbr `u`, sstore_def, tstore_def,
    step_inst_inst_idx_indep,mk_inst_def,is_terminator_def,exec_result_map_def] >>
  metis_tac[]
QED

Theorem pop_full_storage_address_tail[local]:
  ALL_DISTINCT [x3;x4;x5;x6] /\
  (!q. hdr = Var q ==> ~MEM q [x4;x5;x6]) /\
  eval_operand hdr s = SOME slot /\ lookup_var x3 s = SOME len /\
  op_prov G hdr = NONE /\ op_taint tn hdr = {} /\
  op_prov G (Var x3) = NONE /\ op_taint tn (Var x3) = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?u G' tn'.
    run_inst_seq [mk_inst id ADD [hdr;Lit 1w] [x4];
      mk_inst (id+1) MUL [Var x3;Lit (n2w esz)] [x5];
      mk_inst (id+2) ADD [Var x4;Var x5] [x6]] s = OK u /\
    (!D k. inst_seq_ptr D lo ctx fn PG G tn
      [mk_inst id ADD [hdr;Lit 1w] [x4];
       mk_inst (id+1) MUL [Var x3;Lit (n2w esz)] [x5];
       mk_inst (id+2) ADD [Var x4;Var x5] [x6]]
      (s with vs_inst_idx := k) G' tn') /\
    op_prov G' (Var x6) = NONE /\ op_taint tn' (Var x6) = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!q. ~MEM q [x4;x5;x6] ==> FLOOKUP G' q = FLOOKUP G q /\
      op_taint tn' (Var q) = op_taint tn (Var q))
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `run_inst_seq code s` >>
  `?u. run_inst_seq code s = OK u` by
    (Cases_on `hdr` >>
     gvs[Abbr `code`, run_inst_seq_def, nested_pop_step_add,
       pop_step_MUL_lit, pop_step_ADD_var, eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE]) >>
  `bop_scalar_seq {q | ~MEM q [x4;x5;x6]}
    {hdr;Var x3;Lit 1w;Lit (n2w esz)} code
    {Var x6;Var x5;Var x4;hdr;Var x3;Lit 1w;Lit (n2w esz)}` by
    (simp[Abbr `code`, bop_scalar_seq_def, mk_inst_def] >> metis_tac[]) >>
  `!op. op IN {hdr;Var x3;Lit 1w;Lit (n2w esz)} ==>
     op_prov G op = NONE /\ op_taint tn op = {}` by
    (rpt strip_tac >> gvs[] >> simp[op_prov_def,op_taint_def]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> ALLOCA) code` by
    simp[Abbr `code`,mk_inst_def] >>
  drule_all pop_full_scalar_sequence >>
  disch_then (qspecl_then [`fn`,`PG`] strip_assume_tac) >>
  `!D k. inst_seq_ptr D lo ctx fn PG G tn code
      (s with vs_inst_idx := k) G' tn'` by
    (rpt gen_tac >>
     `run_inst_seq code (s with vs_inst_idx := k) =
       OK (u with vs_inst_idx := k)` by
       simp[Abbr `code`,run_inst_seq_inst_idx,exec_result_map_def,
         mk_inst_def,is_terminator_def] >>
     `allocas_from lo (s with vs_inst_idx := k)` by
       (fs[allocas_from_def] >> first_assum ACCEPT_TAC) >>
     `ctx_has_dalloca ctx ==> allocas_below_fmp (s with vs_inst_idx := k)` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     simp[NoAsms, allocas_below_fmp_def] >> metis_tac[]) >>
     mp_tac (Q.INST [`s` |-> `s with vs_inst_idx := k`,
       `t` |-> `u with vs_inst_idx := k`,
       `R` |-> `{q | ~MEM q [x4;x5;x6]}`,
       `A` |-> `{hdr;Var x3;Lit 1w;Lit (n2w esz)}`,
       `B` |-> `{Var x6;Var x5;Var x4;hdr;Var x3;Lit 1w;Lit (n2w esz)}`]
       (SPEC_ALL pop_full_scalar_sequence)) >>
     (impl_tac >- simp[]) >>
     strip_tac >>
     `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code` by
       simp[Abbr `code`,mk_inst_def,is_terminator_def] >>
     `G'' = G' /\ tn'' = tn'` by
       (metis_tac[pop_full_ghost_cursor_unique]) >>
     gvs[]) >>
  qexistsl_tac [`u`,`G'`,`tn'`] >> simp[] >> metis_tac[]
QED

Theorem pop_full_storage_checked_run[local]:
  ALL_DISTINCT [x0;x1;x2;x3;x4;x5;x6] /\
  (!q. hdr = Var q ==> ~MEM q [x0;x1;x2;x3;x4;x5;x6]) /\
  eval_operand hdr s = SOME slot /\ op_prov G hdr = NONE /\ op_taint tn hdr = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  (if tr then tload slot s else sload slot s) <> 0w /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_call_ctx.cc_static ==>
  ?u G' tn'.
    run_inst_seq (nested_pop_suffix hdr tr id esz x0 x1 x2 x3 x4 x5 x6) s = OK u /\
    (!D. inst_seq_ptr D lo ctx fn PG G tn
      (nested_pop_suffix hdr tr id esz x0 x1 x2 x3 x4 x5 x6) s G' tn') /\
    op_prov G' (Var x6) = NONE /\ op_taint tn' (Var x6) = {} /\
    tn'.t_mem = tn.t_mem /\
    tn'.t_stor = (if tr then tn.t_stor else key_update tn.t_stor slot {}) /\
    tn'.t_trans = (if tr then key_update tn.t_trans slot {} else tn.t_trans) /\
    tn'.t_imm = tn.t_imm /\
    (!q. ~MEM q [x0;x1;x2;x3;x4;x5;x6] ==>
      FLOOKUP G' q = FLOOKUP G q /\ op_taint tn' (Var q) = op_taint tn (Var q))
Proof
  strip_tac >>
  mp_tac (Q.INST [`out` |-> `x0`] (SPEC_ALL pop_full_storage_load)) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`s1`,`G1`,`tn1`] strip_assume_tac) >>
  qabbrev_tac `lenw = if tr then tload slot s else sload slot s` >>
  `lookup_var x0 s1 = SOME lenw /\ allocas_from lo s1` by
    (qpat_assum `s1 = update_var x0 _ s` (fn th => PURE_REWRITE_TAC [th]) >>
     simp[lookup_var_def,update_var_def,FLOOKUP_UPDATE,Abbr `lenw`,allocas_from_def] >>
     qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s1` by
    (qpat_assum `s1 = update_var x0 _ s` (fn th => PURE_REWRITE_TAC [th]) >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     simp[NoAsms, allocas_below_fmp_def, update_var_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`s` |-> `s1`,`G` |-> `G1`,`tn` |-> `tn1`,
    `n` |-> `lenw`,`id` |-> `id+1`,`p` |-> `x0`]
    (SPEC_ALL pop_full_memory_scalar_chunk)) >>
  (impl_tac >- (simp[Abbr `lenw`] >> fs[])) >>

  disch_then (qx_choosel_then [`s2`,`G2`,`tn2`] strip_assume_tac) >>
  `s2.vs_labels = s.vs_labels` by
    (qpat_assum `(s2 with vs_vars := _) = s1`
       (mp_tac o AP_TERM ``\z:venom_state. z.vs_labels``) >>
     qpat_assum `s1 = update_var x0 _ s` (fn th => PURE_REWRITE_TAC [th]) >>
     simp[update_var_def]) >>
  `eval_operand hdr s2 = SOME slot /\ op_prov G2 hdr = NONE /\
   op_taint tn2 hdr = {}` by
    (Cases_on `hdr` >>
     gvs[eval_operand_def,lookup_var_def,op_prov_def,op_taint_def,
       update_var_def,FLOOKUP_UPDATE] >> metis_tac[]) >>
  `allocas_from lo s2 /\ ~s2.vs_call_ctx.cc_static` by
    (qpat_assum `(s2 with vs_vars := _) = s1` mp_tac >>
     gvs[venom_state_component_equality,update_var_def,allocas_from_def] >>
     metis_tac[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s2` by
    (qpat_assum `(s2 with vs_vars := _) = s1` mp_tac >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s1` mp_tac >>
     simp[NoAsms, venom_state_component_equality, allocas_below_fmp_def] >>
     metis_tac[]) >>
  qabbrev_tac `s3 = if tr then tstore slot (lenw-1w) s2 else sstore slot (lenw-1w) s2` >>
  qabbrev_tac `tm = if tr then tn2 with t_trans := key_update tn2.t_trans slot {}
    else tn2 with t_stor := key_update tn2.t_stor slot {}` >>
  `step_inst_base (mk_inst (id+5) (if tr then TSTORE else SSTORE) [hdr;Var x3] [])
    s2 = OK s3` by simp[nested_pop_step_store,Abbr `s3`] >>
  `!D k. inst_seq_ptr D lo ctx fn PG G2 tn2
    [mk_inst (id+5) (if tr then TSTORE else SSTORE) [hdr;Var x3] []]
    (s2 with vs_inst_idx := k) G2 tm` by
    (qunabbrev_tac `tm` >> irule pop_full_storage_store >> simp[]) >>
  `eval_operand hdr s3 = SOME slot /\ lookup_var x3 s3 = SOME (lenw-1w) /\
   op_prov G2 hdr = NONE /\ op_taint tm hdr = {} /\
   op_prov G2 (Var x3) = NONE /\ op_taint tm (Var x3) = {} /\
   allocas_from lo s3` by
    (Cases_on `tr` >> Cases_on `hdr` >> gvs[Abbr `s3`,Abbr `tm`,sstore_def,tstore_def,
       eval_operand_def,lookup_var_def,op_taint_def,allocas_from_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s3` by
    (Cases_on `tr` >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s2` mp_tac >>
     simp[NoAsms, Abbr `s3`, allocas_below_fmp_def, sstore_def, tstore_def] >>
     metis_tac[]) >>
  mp_tac (Q.INST [`s` |-> `s3`,`G` |-> `G2`,`tn` |-> `tm`,
    `len` |-> `lenw-1w`,`id` |-> `id+6`]
    (SPEC_ALL pop_full_storage_address_tail)) >>
  (impl_tac >- (simp[] >> fs[] >> metis_tac[])) >>
  disch_then (qx_choosel_then [`u`,`G3`,`tn3`] strip_assume_tac) >>
  `!D k. inst_seq_ptr D lo ctx fn PG G1 tn1
    [mk_inst (id+1) ISZERO [Var x0] [x1];
     mk_inst (id+1+1) ISZERO [Var x1] [x2];
     mk_inst (id+1+2) ASSERT [Var x2] [];
     mk_inst (id+1+3) SUB [Var x0;Lit 1w] [x3]]
    (s1 with vs_inst_idx := k) G2 tn2` by
    (mp_tac (Q.INST [`p` |-> `x0`, `s` |-> `s1`, `G` |-> `G1`,
       `tn` |-> `tn1`, `id` |-> `id+1`, `H` |-> `G2`, `tm` |-> `tn2`,
       `n` |-> `lenw`, `D0` |-> `ARB`]
       (SPEC_ALL pop_full_memory_scalar_chunk_uniform)) >>
     impl_tac >- (fs[] >> metis_tac[]) >> simp[]) >>
  qabbrev_tac `load = [mk_inst id (if tr then TLOAD else SLOAD) [hdr] [x0]]` >>
  qmatch_asmsub_abbrev_tac `run_inst_seq chunk s1 = OK s2` >>
  qabbrev_tac `store = [mk_inst (id+5) (if tr then TSTORE else SSTORE) [hdr;Var x3] []]` >>
  qmatch_asmsub_abbrev_tac `run_inst_seq tail s3 = OK u` >>
  `run_inst_seq load s = OK s1 /\ run_inst_seq store s2 = OK s3` by
    simp[Abbr `load`,Abbr `store`,run_inst_seq_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) load /\
   EVERY (\i. ~is_terminator i.inst_opcode) chunk /\
   EVERY (\i. ~is_terminator i.inst_opcode) store` by
    (Cases_on `tr` >> simp[Abbr `load`,Abbr `chunk`,Abbr `store`,
      mk_inst_def,is_terminator_def]) >>
  `nested_pop_suffix hdr tr id esz x0 x1 x2 x3 x4 x5 x6 =
     load ++ (chunk ++ (store ++ tail))` by
    simp[nested_pop_suffix_def,Abbr `load`,Abbr `chunk`,Abbr `store`,Abbr `tail`,
      arithmeticTheory.ADD_ASSOC] >>
  `!D k. inst_seq_ptr D lo ctx fn PG G2 tn2 (store ++ tail)
     (s2 with vs_inst_idx := k) G3 tn3` by metis_tac[inst_seq_ptr_uniform_append] >>
  `!D k. inst_seq_ptr D lo ctx fn PG G1 tn1 (chunk ++ (store ++ tail))
     (s1 with vs_inst_idx := k) G3 tn3` by metis_tac[inst_seq_ptr_uniform_append] >>
  `!D k. inst_seq_ptr D lo ctx fn PG G tn (load ++ (chunk ++ (store ++ tail)))
     (s with vs_inst_idx := k) G3 tn3` by metis_tac[inst_seq_ptr_uniform_append] >>
  qexistsl_tac [`u`,`G3`,`tn3`] >>
  conj_tac >- metis_tac[run_inst_seq_append] >>
  conj_tac >- (gen_tac >>
    qpat_assum `nested_pop_suffix _ _ _ _ _ _ _ _ _ _ _ = _`
      (fn th => PURE_REWRITE_TAC [th]) >>
    `(s with vs_inst_idx := s.vs_inst_idx) = s` by
      simp[venom_state_component_equality] >>
    qpat_assum `(s with vs_inst_idx := s.vs_inst_idx) = s`
      (fn cursor_eq =>
        qpat_assum `!D k. inst_seq_ptr D lo ctx fn PG G tn
          (load ++ (chunk ++ (store ++ tail))) _ G3 tn3`
          (qspecl_then [`D`,`s.vs_inst_idx`]
            (ACCEPT_TAC o REWRITE_RULE [cursor_eq])))) >>
  Cases_on `tr` >> gvs[Abbr `tm`,op_taint_def] >> metis_tac[]
QED

Theorem pop_full_storage_empty_path[local]:
  eval_operand hdr s = SOME slot /\ op_taint tn hdr = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  (if tr then tload slot s else sload slot s) = 0w /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id (if tr then TLOAD else SLOAD) [hdr] [x0];
    mk_inst (id+1) ISZERO [Var x0] [x1];
    mk_inst (id+2) ISZERO [Var x1] [x2]]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  get_instruction bb (s.vs_inst_idx+3) =
    SOME (mk_inst (id+3) ASSERT [Var x2] []) ==>
  ?v G' tn'. !D.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (Abort Revert_abort v,G',tn')
Proof
  strip_tac >>
  mp_tac (Q.INST [`out` |-> `x0`, `fn` |-> `func`]
    (SPEC_ALL pop_full_storage_load)) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`u`,`G1`,`tn1`] strip_assume_tac) >>
  `u = update_var x0 0w s` by simp[] >>
  qabbrev_tac `v = update_var x2 0w (update_var x1 1w u)` >>
  `run_inst_seq [mk_inst (id+1) ISZERO [Var x0] [x1];
      mk_inst (id+2) ISZERO [Var x1] [x2]] u = OK v` by
    gvs[Abbr `v`,pop_step_ISZERO,run_inst_seq_def,lookup_var_def,
      update_var_def,FLOOKUP_UPDATE,bool_to_word_def] >>
  `run_inst_seq [mk_inst (id+1) ISZERO [Var x0] [x1];
      mk_inst (id+2) ISZERO [Var x1] [x2]]
     (u with vs_inst_idx := SUC s.vs_inst_idx) =
    OK (v with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[run_inst_seq_inst_idx,exec_result_map_def,mk_inst_def,is_terminator_def] >>
  `allocas_from lo (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (qpat_assum `u = update_var x0 0w s` (fn th => PURE_REWRITE_TAC [th]) >>
     simp[allocas_from_def,update_var_def] >>
     qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (qpat_assum `u = update_var x0 0w s` (fn th => PURE_REWRITE_TAC [th]) >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     simp[NoAsms, allocas_below_fmp_def, update_var_def] >> metis_tac[]) >>
  mp_tac (SRULE [GSYM arithmeticTheory.ADD_ASSOC]
    (Q.INST [`x` |-> `Var x0`, `a` |-> `x1`, `b` |-> `x2`,
    `id` |-> `id+1`, `s` |-> `u with vs_inst_idx := SUC s.vs_inst_idx`,
    `t` |-> `v with vs_inst_idx := SUC s.vs_inst_idx`,
    `tn` |-> `tn1`, `G` |-> `G1`, `fn` |-> `func`]
    (SPEC_ALL pop_full_bool_pair))) >>
  (impl_tac >- (asm_rewrite_tac[] >> simp[allocas_from_def,update_var_def] >>
    qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def]))) >>
  disch_then (qx_choosel_then [`G2`,`tn2`] strip_assume_tac) >>
  qabbrev_tac `prefix =
    [mk_inst id (if tr then TLOAD else SLOAD) [hdr] [x0];
     mk_inst (id+1) ISZERO [Var x0] [x1];
     mk_inst (id+2) ISZERO [Var x1] [x2]]` >>
  `run_inst_seq prefix s = OK v` by
    (simp[Abbr `prefix`,Once run_inst_seq_def] >>
     qpat_assum `u = update_var x0 0w s` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  `!D. inst_seq_ptr D lo ctx func PG G tn prefix s G2 tn2` by
    (gen_tac >>
     `prefix = [mk_inst id (if tr then TLOAD else SLOAD) [hdr] [x0]] ++
       [mk_inst (id+1) ISZERO [Var x0] [x1];
        mk_inst (id+2) ISZERO [Var x1] [x2]]` by simp[Abbr `prefix`] >>
     pop_assum SUBST1_TAC >> irule inst_seq_ptr_append_ok >>
     conj_tac >- (Cases_on `tr` >> simp[mk_inst_def,is_terminator_def]) >>
     qexistsl_tac [`G1`,`u`,`tn1`] >>
     simp[run_inst_seq_def] >>
     qpat_assum `u = update_var x0 0w s` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
     conj_tac
     >- (qpat_assum `!D k. inst_seq_ptr D lo ctx func PG G tn _ _ G1 tn1`
           (qspecl_then [`D`,`s.vs_inst_idx`]
             (ACCEPT_TAC o SIMP_RULE (srw_ss()) []))) >>
     qpat_assum `!D. inst_seq_ptr D lo ctx func PG G1 tn1 _ _ G2 tn2`
       (qspec_then `D` (ACCEPT_TAC o REWRITE_RULE [arithmeticTheory.ADD1]))) >>
  qexistsl_tac [`revert_state (set_returndata []
    (v with vs_inst_idx := s.vs_inst_idx+3))`,`G2`,`tn2`] >>
  gen_tac >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (v with vs_inst_idx := s.vs_inst_idx+3),G2,tn2)` by
    (`run_inst_seq_mem_ok prefix s` by
       (irule run_inst_seq_mem_ok_every >>
        Cases_on `tr` >>
        simp[Abbr `prefix`,mk_inst_def,inst_dload_in_section_def] >>
        rpt conj_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
     `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) prefix` by
       (Cases_on `tr` >> simp[Abbr `prefix`,mk_inst_def,is_terminator_def]) >>
     `(ctx_has_dalloca ctx ==> !pre i post u.
         prefix = pre ++ i::post /\ run_inst_seq pre s = OK u ==>
         dalloca_no_wrap i u)` by
       (rpt strip_tac >>
        qpat_x_assum `_ = _ ++ i::_` (mp_tac o Q.AP_TERM `MEM i`) >>
        Cases_on `tr` >> simp[Abbr `prefix`] >>
        disch_then (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) >>
        simp[dalloca_no_wrap_def,mk_inst_def]) >>
     qpat_assum `!D. inst_seq_ptr _ _ _ _ _ _ _ prefix _ _ _`
       (qspec_then `D` assume_tac) >>
     drule_all run_inst_seq_gas_origin_ptr_path >>
     Cases_on `tr` >> simp[Abbr `prefix`,mk_inst_def]) >>
  irule gas_origin_ptr_path_trans >> goal_assum (drule_at Any) >>
  `~v.vs_halted /\ v.vs_current_bb = s.vs_current_bb /\
    allocas_from lo v /\ lookup_var x2 v = SOME 0w` by
    (gvs[Abbr `v`,update_var_def,lookup_var_def,FLOOKUP_UPDATE,allocas_from_def] >>
     first_assum ACCEPT_TAC) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp (v with vs_inst_idx := s.vs_inst_idx+3)` by
    (simp[Abbr `v`, allocas_below_fmp_def, update_var_def] >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     simp[NoAsms, allocas_below_fmp_def] >> metis_tac[]) >>
  irule exit_inst_origin_ptr >> simp[exit_result_def] >>
  `lookup_var x2 (v with vs_inst_idx := s.vs_inst_idx+3) = SOME 0w` by
    fs[lookup_var_def] >>
  `step_inst_base (mk_inst (id+3) ASSERT [Var x2] [])
    (v with vs_inst_idx := s.vs_inst_idx+3) =
    Abort Revert_abort (revert_state (set_returndata []
      (v with vs_inst_idx := s.vs_inst_idx+3)))` by simp[pop_step_ASSERT] >>
  `ptr_inst_ok D lo 0 ctx func G2 tn2 (mk_inst (id+3) ASSERT [Var x2] [])
    (v with vs_inst_idx := s.vs_inst_idx+3)` by
    (irule ptr_inst_ok_lower_bound_transport >>
     conj_tac >- (simp[allocas_from_def] >>
       qpat_assum `allocas_from lo v`
         (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
     qexists_tac `0` >> simp[] >> irule bop_assert_ptr_inst_ok >> simp[]) >>
  simp[step_inst_non_invoke,pop_step_ASSERT,lookup_var_def,
    gas_events_step_def,gas_count_step_def,mem_safe_step_non_invoke,
    dalloca_no_wrap_def,mk_inst_def,
    inst_mem_below_frontier_def,inst_dload_in_section_def,
    source_memory_read_ranges_def,source_memory_write_ranges_def]
QED

Theorem pop_vv_full_of_target[local]:
  !DF lo d PG tops ctx shadow_ctx func shadow_func cenv cx env ty ann bt es.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_place_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx env bt es ==>
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Pop ann bt) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[expr_vv_sim_full_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `compile_get_target_ptr compile_expr cenv bt sa` >>
  rename1 `compile_get_target_ptr compile_expr cenv bt sa = (rb,sm)` >>
  PairCases_on `rb` >>
  qpat_x_assum `compile_expr cenv ty (Pop ann bt) sa = _` mp_tac >>
  simp[Once nested_pop_compile_eq] >> pairarg_tac >> simp[] >> strip_tac >>
  `?shadow_sm.
     compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
       (gas_shadow_target bt) shadow_sa = ((rb0,rb1,rb2),shadow_sm) /\
     gas_shadow_state sm shadow_sm` by
    (`gas_shadow_compiles (compile_get_target_ptr compile_expr cenv bt)
       (compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
          (gas_shadow_target bt))` by irule gas_shadow_stmt_get_target_ptr_env >>
     qpat_x_assum `gas_shadow_compiles _ _`
       (qspecl_then [`sa`, `shadow_sa`] mp_tac o
        REWRITE_RULE [gas_shadow_compiles_def]) >>
     simp[] >> strip_tac >>
     Cases_on `compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
       (gas_shadow_target bt) shadow_sa` >> gvs[]) >>
  drule nested_pop_target_admissible >> strip_tac >>
  `?n. type_place_target env bt = SOME (Type (ArrayT ann (Dynamic n)))` by
    (irule well_typed_expr_Pop_dynamic_target >>
     gvs[expr_body_pre_def]) >>
  `ci_mono sa sm` by
    (mp_tac (Q.SPECL [`bt`, `cenv`, `sa`] ci_mono_compile_get_target_ptr) >> simp[]) >>
  `ci_mono sm sb` by
    (qpat_assum `compile_dynarray_pop _ _ _ _ _ _ _ = _` mp_tac >>
     qpat_assum `sb' = sb` (SUBST1_TAC o SYM) >>
     metis_tac[ci_mono_compile_dynarray_pop, pairTheory.SND]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> gvs[ci_mono_def]) >>
  `cs_extends shadow_sm shadow_sb` by
    (qpat_x_assum `compile_expr _ _ (gas_shadow_expr (Pop ann bt)) _ = _` mp_tac >>
     simp[gas_shadow_expr_def, Once nested_pop_compile_eq] >>
     pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
     metis_tac[ci_mono_compile_dynarray_pop, pairTheory.SND, ci_mono_def]) >>
  `cs_extends shadow_sa shadow_sm` by
    (mp_tac (Q.SPECL [`gas_shadow_target bt`, `gas_shadow_env T cenv`, `shadow_sa`]
       ci_mono_compile_get_target_ptr) >> simp[ci_mono_def]) >>
  `fn_has_code shadow_sa shadow_sm shadow_func` by
    (drule_all fn_has_code_split >> simp[]) >>
  qpat_x_assum `target_place_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [target_place_sim_full_def]) >>
  disch_then (qspecl_then [`st0`, `ArrayT ann (Dynamic n)`, `sa`, `sm`,
     `shadow_sa`, `shadow_sm`, `(rb0,rb1,rb2)`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ baseQ baseR` >>
  `eval_expr cx (Pop ann bt) = bind (eval_target_place cx bt) (pop_place cx)` by
    simp[FUN_EQ_THM, Once evaluate_def, bind_def] >>
  asm_rewrite_tac[] >> irule gas_outcome_full_bind_all >>
  `!res : place + exception. !r.
     (?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r) <=>
       expr_exit res r` by
    (Cases >- simp[] >> simp[] >>
     qspecl_then [`(\x:place. ARB:eval_result)`, `INR y : place + exception`]
       mp_tac exprSimDefsTheory.expr_exit_success_map >> simp[FUN_EQ_THM]) >>
  simp[] >> rpt conj_tac
  >~ [`storage_trace_frame (eval_target_place _ _)`]
  >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]
  >~ [`storage_trace_frame (pop_place _ _)`]
  >- simp[vyperStorageTraceTheory.storage_trace_frame_pop_place]
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_place >>
      qexistsl_tac [`mid`, `t`, `v`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_place >> simp[]) >>
  qexists_tac `\H res ee G tn t. baseQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac
  >~ [`storage_trace_domain _ _ _`]
  >- suspend "pop_suffix" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[Abbr `baseR`] >>
  simp[Abbr `baseQ`, Abbr `baseR`] >>
  rpt gen_tac >> Cases_on `res` >> simp[] >>
  qpat_x_assum `!res r. _ <=> expr_exit res r`
    (qspecl_then [`INR y`, `r`] mp_tac) >>
  simp[exprSimDefsTheory.halt_exit_def] >> strip_tac >> simp[]
QED

Resume pop_vv_full_of_target[pop_suffix]:
  qx_genl_tac [`marks`, `res`, `mid`, `G1`, `tn1`, `t`] >>
  strip_tac >> fs[] >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    gvs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `baseQ (storage_trace_horizon mid.storage_trace) res mid G1 tn1 t` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> baseQ H _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
  qpat_x_assum `baseQ _ _ _ _ _ _` mp_tac >>
  simp[Abbr `baseQ`, NoAsms] >> strip_tac >> gvs[] >>
  `~t.vs_halted /\ mid.gas_obs = []` by metis_tac[] >>
  `eval_target_place cx bt (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL p,mid)` by
    (`mid with gas_obs := [] = mid` by
       (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
     qpat_x_assum `!tail. eval_target_place _ _ _ = _` (qspec_then `[]` mp_tac) >>
     simp[]) >>
  `expr_body_pre cenv cx env (Pop ann bt)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_all pop_target_source_facts >> strip_tac >>
  Cases_on `p`
  >~ [`StoragePlace _ _ _`] >- suspend "storage_suffix"
  >~ [`MemoryPlace _ _`] >- suspend "memory_suffix" >>
  qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  simp[target_post_def, place_ptr_rel_def]
QED

Resume pop_vv_full_of_target[memory_suffix]:
  rename1 `MemoryPlace local_name local_path` >>
  `target_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx
     es sa sm s0 mid (PlaceR (MemoryPlace local_name local_path))
     (Type (ArrayT ann (Dynamic n))) (rb0,rb1,rb2) t` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
  drule_all writable_memory_entry_typed >> strip_tac >>
  qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[target_post_def, place_ptr_rel_def, NoAsms] >> strip_tac >> gvs[] >>
  `!entry err. lookup_scopes local_name mid.scopes = SOME entry /\
     evaluate_subscripts entry.type entry.value local_path = INR err ==>
     read_popped entry.type local_path entry.popped = NONE` by
    (rpt strip_tac >> gvs[]) >>
  drule_at (Pat `eval_target_place _ _ _ = _`) pop_target_live_array >>
  simp[] >> disch_then drule >> strip_tac >> gvs[] >>
  `?root_ty. cenv.ce_var_type local_name = SOME root_ty /\
     evaluate_type (get_tenv cx) root_ty = SOME entry.type` by
    (irule pop_target_entry_compile_type >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`ann`, `bt`, `env`,
       `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
       `MemoryPlace local_name local_path`] >> simp[]) >>
  `target_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx
     es sa sm s0 mid (PlaceR (MemoryPlace local_name local_path))
     (Type (ArrayT ann (Dynamic n)))
     (rb0,SOME LocMemory,SOME (value_type_place (Type (ArrayT ann (Dynamic n))))) t` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
  drule_all memory_target_encoding_handoff >> strip_tac >> gvs[] >>
  gvs[value_type_place_def, word_scale_def, elem_size_in_location_def,
      is_slot_addressed_def] >>
  qmatch_assum_rename_tac
    `subscripts_type entry.type local_path = SOME (ArrayTV etv (Dynamic capacity))` >>
  `tv = ArrayTV etv (Dynamic capacity)` by
    (drule exprSimPropsTheory.mem_path_offset_sound >> simp[]) >> gvs[] >>
  `ghost_inv_at (DF (storage_trace_horizon mid.storage_trace)) lo d cenv cx
      mid G1 tn1 t` by metis_tac[] >>
  drule_all pop_full_memory_entry >> strip_tac >>
  `op_taint tn1 rb0 = {} /\ op_prov G1 rb0 = FLOOKUP G1 p` by
    (fs[target_ptr_ok_def] >> metis_tac[]) >>
  `?hdr_var. rb0 = Var hdr_var /\ ptr_covers G1 tn1 hdr_var t 32` by
    (irule pop_full_header_coverage >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`b`, `k`, `p`, `sz`] >>
     gvs[valueEncodingTheory.type_memory_size_def]) >>
  drule memory_pop_shape >> strip_tac >>
  `allocas_from lo t` by fs[ghost_inv_at_def] >>
  `w2n b + sz <= t.vs_alloca_next` by
    (irule abi_encode_local_region_frontier >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any)) >>
  `w2n (b + n2w k) + 32 <= t.vs_alloca_next` by
    (gvs[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
  `val_in_memory (ArrayTV etv (Dynamic capacity)) (ArrayV (DynArrayV vs))
     (w2n b + k) t.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `mload (w2n (b + n2w k)) t = n2w (LENGTH vs)` by
    (fs[valueEncodingDefsTheory.val_in_memory_def, mem_word_at_eq_mload] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  drule_all fn_has_code_code >> strip_tac >>
  Cases_on `vs = []`
  >- (qpat_x_assum `vs = []` SUBST_ALL_TAC >>
      `lookup_var hdr_var t = SOME (b + n2w k)` by fs[eval_operand_def] >>
      `isPREFIX [mk_inst sm.cs_next_id MLOAD [Var hdr_var] [x0];
        mk_inst (sm.cs_next_id+1) ISZERO [Var x0] [x1];
        mk_inst (sm.cs_next_id+2) ISZERO [Var x1] [x2]]
        (DROP t.vs_inst_idx bb.bb_instructions)` by
        (irule listTheory.isPREFIX_TRANS >>
         qexists_tac `memory_pop_insts rb0 sm.cs_next_id (type_memory_bytes cenv ann)
           x0 x1 x2 x3 x4 x5 x6` >>
         conj_tac >- simp[memory_pop_insts_def] >>
         metis_tac[]) >>
      `get_instruction bb (t.vs_inst_idx+3) =
        SOME (mk_inst (sm.cs_next_id+3) ASSERT [Var x2] [])` by
        (drule_all fn_has_code_same_block >> strip_tac >>
         gvs[] >> first_x_assum (qspec_then `3` mp_tac) >>
         simp[memory_pop_insts_def]) >>
      `mem_word_taint tn1.t_mem (w2n (b + n2w k)) = {} /\
       mload (w2n (b + n2w k)) t = 0w /\
       lookup_block t.vs_current_bb func.fn_blocks = SOME bb` by
        (simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
      drule_all pop_full_memory_empty_path >>
      disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`, `PG`] strip_assume_tac) >>
      `!tail. pop_place cx (MemoryPlace local_name local_path)
          (mid with gas_obs := tail) =
        (INR (Error (RuntimeError "pop empty memory array")),
         mid with gas_obs := tail)` by
        (gen_tac >> drule lookup_scopes_find_containing_scope >> strip_tac >>
         irule pop_memory_place_live_empty >> simp[] >> metis_tac[]) >>
      irule gas_outcome_full_exit >>
      reverse conj_tac >- simp[] >>
      qexistsl_tac [`G'`, `mid`, `Abort Revert_abort v`,
        `INR (Error (RuntimeError "pop empty memory array"))`, `tn'`] >>
      simp[exit_result_def] >> rpt strip_tac >>
      simp[exprSimDefsTheory.expr_exit_def, exprSimDefsTheory.halt_exit_def]) >>
  `EVERY (\x. x <> hdr_var) [x0;x1;x2;x3;x4;x5;x6]` by
    (fs[] >> metis_tac[]) >>
  `well_formed_type_value (ArrayTV etv (Dynamic capacity))` by
    metis_tac[vyperPlaceStatePreservationTheory.subscripts_type_well_formed] >>
  `value_has_type (ArrayTV etv (Dynamic capacity)) (ArrayV (DynArrayV vs))` by
    metis_tac[vyperPlaceStatePreservationTheory.evaluate_subscripts_type] >>
  `LENGTH vs < dimword (:256)` by
    (fs[vyperTypingTheory.value_has_type_def,
        vyperTypingTheory.well_formed_type_value_def] >> decide_tac) >>
  `mem_word_taint tn1.t_mem (w2n (b + n2w k)) = {}` by
    metis_tac[arithmeticTheory.ADD_COMM] >>
  `mload (w2n (b + n2w k)) t <> 0w` by
    (simp[] >> simp[wordsTheory.n2w_11] >> Cases_on `vs` >> gvs[]) >>
  `lookup_var hdr_var t = SOME (b + n2w k)` by
    fs[eval_operand_def] >>
  drule_all pop_full_memory_checked_run >>
  disch_then (qspecl_then [`sm.cs_next_id`, `func`, `type_memory_bytes cenv ann`, `PG`]
    strip_assume_tac) >>
  `ALL_DISTINCT [x6;x5;x4;x3;x2;x1;x0] /\
   EVERY (\x. rb0 <> Var x) [x0;x1;x2;x3;x4;x5;x6]` by
    (fs[] >> metis_tac[]) >>
  drule_all memory_pop_run >>
  disch_then (qspecl_then [`sm.cs_next_id`, `type_memory_bytes cenv ann`] strip_assume_tac) >>
  `rb0 = Var hdr_var` by simp[] >>
  gvs[] >>
  `run_inst_seq_mem_ok
     (memory_pop_insts (Var hdr_var) sm.cs_next_id
       (type_memory_bytes cenv ann) x0 x1 x2 x3 x4 x5 x6) t` by
    (irule pop_full_memory_mem_ok >> simp[] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  `!D. gas_origin_ptr_path
     (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (t,G1,tn1) []
     (OK (u with vs_inst_idx := t.vs_inst_idx + 9),G',tn')` by
    (gen_tac >>
     `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
       (memory_pop_insts (Var hdr_var) sm.cs_next_id
         (type_memory_bytes cenv ann) x0 x1 x2 x3 x4 x5 x6)` by
       simp[memory_pop_insts_def, mk_inst_def, is_terminator_def] >>
     `lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
      isPREFIX (memory_pop_insts (Var hdr_var) sm.cs_next_id
        (type_memory_bytes cenv ann) x0 x1 x2 x3 x4 x5 x6)
        (DROP t.vs_inst_idx bb.bb_instructions)` by simp[] >>
     `(ctx_has_dalloca ctx ==> !pre i post u.
         memory_pop_insts (Var hdr_var) sm.cs_next_id
           (type_memory_bytes cenv ann) x0 x1 x2 x3 x4 x5 x6 = pre ++ i::post /\
         run_inst_seq pre t = OK u ==> dalloca_no_wrap i u)` by
       (rpt strip_tac >>
        qpat_x_assum `_ = _ ++ i::_` (mp_tac o Q.AP_TERM `MEM i`) >>
        simp[memory_pop_insts_def] >>
        disch_then (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) >>
        simp[dalloca_no_wrap_def,mk_inst_def]) >>
     qpat_assum `!D. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `D` assume_tac) >>
     drule_all run_inst_seq_gas_origin_ptr_path >>
     simp[memory_pop_insts_def, mk_inst_def]) >>
  drule lookup_scopes_find_containing_scope >> strip_tac >>
  qmatch_assum_rename_tac
    `find_containing_scope local_name mid.scopes = SOME (pre,local_scope,entry,rest)` >>
  drule_all exprSimPopNestedLocalPropsTheory.pop_memory_live_transition >>
  disch_then (qspec_then `cx` strip_assume_tac) >>
  qpat_x_assum `let t = _ in _`
    (strip_assume_tac o BETA_RULE o REWRITE_RULE [LET_THM]) >>
  drule_all pop_array_element_layout >> strip_tac >>
  `val_wf (ArrayTV etv (Dynamic capacity)) (ArrayV (DynArrayV vs))` by
    (drule_all val_in_memory_mutable_path >> simp[]) >>
  drule_all exprSimPopNestedLocalPostTheory.pop_path_result_bounds >> strip_tac >>
  `val_store_size etv (LAST vs) <= type_memory_size etv` by
    metis_tac[exprSimPropsTheory.val_store_size_le] >>
  `k + 32 + (LENGTH vs - 1) * type_memory_size etv +
      type_memory_size etv <= sz` by
    (`LENGTH vs <= capacity` by fs[valueEncodingDefsTheory.val_wf_def] >>
     `LENGTH vs * type_memory_size etv <= capacity * type_memory_size etv` by
       simp[] >>
     `(LENGTH vs - 1) * type_memory_size etv + type_memory_size etv =
        LENGTH vs * type_memory_size etv` by
       (Cases_on `vs` >> gvs[arithmeticTheory.MULT_CLAUSES]) >>
     qpat_assum `k + type_memory_size _ <= sz` mp_tac >>
     PURE_REWRITE_TAC [valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
  `k + 32 + (LENGTH vs - 1) * type_memory_size etv <= sz` by
    (`LENGTH vs <= capacity` by fs[valueEncodingDefsTheory.val_wf_def] >>
     `(LENGTH vs - 1) * type_memory_size etv <= capacity * type_memory_size etv` by
       (irule arithmeticTheory.LESS_MONO_MULT >> decide_tac) >>
     qpat_x_assum `(LENGTH vs - 1) * _ <= _` mp_tac >>
     qpat_x_assum `k + type_memory_size _ <= sz` mp_tac >>
     rpt (pop_assum kall_tac) >>
     pure_rewrite_tac[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
  `w2n (b + n2w k) = w2n b + k /\ w2n b + sz < dimword (:256)` by
    simp[arithmeticTheory.ADD_COMM] >>
  `lookup_var x6 u = SOME (b + n2w k + 32w +
      (n2w (LENGTH vs) - 1w) * n2w (type_memory_size etv))` by simp[] >>
  drule_at (Pat `lookup_var _ _ = _`) memory_pop_result_address >>
  disch_then (qspecl_then [`sz`, `w2n b`, `k`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `?prov_base prov_size. FLOOKUP G1 p = SOME (prov_base,prov_size) /\
     prov_base <= w2n b /\ w2n b + sz <= prov_base + prov_size` by
    (qpat_assum `ptr_covers G1 tn1 p t sz` mp_tac >>
     qpat_assum `lookup_var p t = SOME b` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[ptr_covers_def] >> metis_tac[]) >>
  `FLOOKUP G' x6 = SOME (prov_base,prov_size) /\
   prov_base <= w2n (b + n2w k + 32w +
      (n2w (LENGTH vs) - 1w) * n2w (type_memory_size etv)) /\
   w2n (b + n2w k + 32w +
      (n2w (LENGTH vs) - 1w) * n2w (type_memory_size etv)) +
      type_memory_size etv <= prov_base + prov_size` by
    (gvs[op_prov_def] >> decide_tac) >>
  `u.vs_memory = (mstore (w2n b + k) (n2w (LENGTH vs - 1)) t).vs_memory` by
    (`1 <= LENGTH vs` by (Cases_on `vs` >> gvs[]) >>
     (metis_tac[wordsTheory.n2w_sub, wordsTheory.WORD_SUB_INTRO])) >>
  `tn1.t_mem DIFF {i | w2n b + k <= i /\ i < w2n b + k + 32} = tn1.t_mem` by
    (irule pop_full_clean_word_diff >> simp[arithmeticTheory.ADD_COMM]) >>
  `!mem. mem_agree_outside tn1.t_mem u.vs_memory mem ==>
     val_in_memory entry.type updated (w2n b) mem /\
     val_in_memory etv (LAST vs)
       (w2n b + k + 32 + (LENGTH vs - 1) * type_memory_size etv) mem` by
    (gen_tac >> disch_tac >>
     `mem_agree_outside
       (tn1.t_mem DIFF {i | w2n b + k <= i /\ i < w2n b + k + 32})
       (mstore (w2n b + k) (n2w (LENGTH vs - 1)) t).vs_memory mem` by
       (qpat_assum `tn1.t_mem DIFF _ = tn1.t_mem`
          (fn th => PURE_REWRITE_TAC [th]) >>
        qpat_assum `u.vs_memory =
          (mstore (w2n b + k) (n2w (LENGTH vs - 1)) t).vs_memory`
          (fn th => PURE_REWRITE_TAC [GSYM th]) >>
        first_assum ACCEPT_TAC) >>
     drule clean_mstore_restore_witness >>
     disch_then (qx_choose_then `mix` strip_assume_tac) >>
     `val_in_memory entry.type entry.value (w2n b) mix` by
       (qpat_assum `!mem. mem_agree_outside _ _ mem ==>
          val_in_memory entry.type entry.value _ mem` irule >> simp[]) >>
     `val_in_memory entry.type updated (w2n b)
       (mstore (w2n b + k) (n2w (LENGTH vs - 1))
         (t with vs_memory := mix)).vs_memory` by
       (irule val_in_memory_pop_path >> simp[] >>
        qexistsl_tac [`entry.value`, `etv`, `capacity`, `local_path`] >> simp[]) >>
     `val_in_memory etv (LAST vs)
       (w2n b + k + 32 + (LENGTH vs - 1) * type_memory_size etv)
       (mstore (w2n b + k) (n2w (LENGTH vs - 1))
         (t with vs_memory := mix)).vs_memory` by
       (irule pop_path_elem_in_memory >> simp[] >>
        qexistsl_tac [`entry.value`, `capacity`, `local_path`, `entry.type`] >> simp[]) >>
     conj_tac >> irule val_in_memory_relative_transport >>
     goal_assum (drule_at Any) >>
     drule memory_byte_agree_window >> simp[]) >>
  qmatch_asmsub_abbrev_tac `pop_place cx _ mid = (INL result,fin)` >>
  qabbrev_tac `updated_scopes = pre ++ local_scope |+ (local_name,entry with
    <|value := updated; popped := record_pop local_path
      (ArrayV (DynArrayV vs)) (LAST vs) entry.popped|>) :: rest` >>
  `fin = mid with scopes := updated_scopes` by
    simp[Abbr `fin`, Abbr `updated_scopes`, evaluation_state_component_equality] >>
  `read_result cx result fin = (INL (LAST vs),fin)` by
    fs[Abbr `result`, Abbr `fin`] >>
  drule find_containing_scope_structure >> strip_tac >>
  drule find_containing_scope_pre_none >> strip_tac >>
  `mid.scopes = pre ++ local_scope::rest` by first_assum ACCEPT_TAC >>
  `local_name IN FDOM local_scope` by
    (qpat_assum `FLOOKUP local_scope local_name = SOME entry` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[FLOOKUP_DEF]) >>
  `MAP FDOM mid.scopes = MAP FDOM updated_scopes` by
    (qpat_assum `mid.scopes = pre ++ local_scope::rest`
       (fn th => PURE_REWRITE_TAC [th]) >>
     simp[NoAsms, Abbr `updated_scopes`, FDOM_FUPDATE] >>
     qpat_x_assum `local_name IN FDOM local_scope` mp_tac >>
     rpt (pop_assum kall_tac) >> SET_TAC[]) >>
  `lookup_scopes local_name updated_scopes = SOME (entry with
      <|value := updated; popped := record_pop local_path
          (ArrayV (DynArrayV vs)) (LAST vs) entry.popped|>)` by
    simp[Abbr `updated_scopes`, Abbr `fin`, lookup_scopes_update] >>
  `!j. j <> local_name ==>
      lookup_scopes j updated_scopes = lookup_scopes j mid.scopes` by
    (simp[Abbr `updated_scopes`, Abbr `fin`] >>
     metis_tac[lookup_scopes_update_other]) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (mp_tac (Q.SPECL [`cx`, `bt`,
      `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
      `INL (MemoryPlace local_name local_path)`, `mid`]
      vyperEvalExprPreservesScopesDomTheory.eval_target_place_preserves_scopes_dom) >>
     simp[]) >>
  `expr_sim_inv cenv cx env es` by
    (qpat_assum `expr_body_pre cenv cx env (Pop ann bt) es`
       (mp_tac o REWRITE_RULE [expr_body_pre_def]) >>
     rpt strip_tac >> first_assum ACCEPT_TAC) >>
  `popped_keys_indexed mid.scopes` by
    (mp_tac (Q.SPECL [`cx`, `bt`,
      `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
      `INL (MemoryPlace local_name local_path)`, `mid`]
      stmtPoppedKeysTheory.eval_target_place_popped_keys_indexed) >>
     qpat_assum `expr_sim_inv cenv cx env es`
       (strip_assume_tac o REWRITE_RULE [expr_sim_inv_def]) >> simp[]) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >>
     qexists_tac `sa` >>
     qpat_assum `ci_mono sa sm` mp_tac >>
     qpat_assum `local_ptrs_reserved cenv sa` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[ci_mono_def]) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    (qpat_assum `ci_mono sa sm` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[ci_mono_def]) >>
  `k + 32 <= sz` by decide_tac >>
  `u = t with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory|>` by
    (qpat_assum `u = t with <|vs_memory := _; vs_vars := _|>` mp_tac >>
     simp[NoAsms, venom_state_component_equality] >> rpt strip_tac >> simp[]) >>
  `!q. not_fresh_at sm q ==> lookup_var q u = lookup_var q t` by
    (qx_gen_tac `q` >> strip_tac >>
     qpat_assum `!q. _ ==> lookup_var q u = lookup_var q t` irule >>
     rpt conj_tac >> strip_tac >>
     qpat_assum `not_fresh_at sm q` mp_tac >>
     qpat_assum `q = _` (fn th => PURE_REWRITE_TAC [th]) >> simp[]) >>
  `!q. not_fresh_at sm q ==>
     FLOOKUP G' q = FLOOKUP G1 q /\ op_taint tn' (Var q) = op_taint tn1 (Var q)` by
    (qx_gen_tac `q` >> disch_tac >>
     qpat_assum `!q. _ ==> FLOOKUP G' q = FLOOKUP G1 q /\ _` irule >>
     simp[] >> rpt conj_tac >> strip_tac >>
     qpat_assum `not_fresh_at sm q` mp_tac >>
     qpat_assum `q = _` (fn th => PURE_REWRITE_TAC [th]) >> simp[]) >>
  `!q. not_fresh_at sa q ==>
     lookup_var q u = lookup_var q t /\
     FLOOKUP G' q = FLOOKUP G1 q /\ op_taint tn' (Var q) = op_taint tn1 (Var q)` by
    (rpt strip_tac >>
     `not_fresh_at sm q` by
       (irule loweringShapeDefsTheory.not_fresh_at_mono >>
        qexists_tac `sa` >> simp[]) >> simp[]) >>
  `local_place_at cenv cx local_name
     (k + 32 + (LENGTH vs - 1) * type_memory_size etv) etv result` by
    (`mem_step_offset (ArrayTV etv (Dynamic capacity))
        (ValueSubscript (IntV &(LENGTH vs - 1))) =
       SOME (32 + (LENGTH vs - 1) * type_memory_size etv,etv)` by
       (simp[mem_step_offset_def] >>
        qpat_assum `val_wf (ArrayTV etv (Dynamic capacity)) (ArrayV (DynArrayV vs))`
          mp_tac >>
        qpat_assum `vs <> []` mp_tac >> rpt (pop_assum kall_tac) >>
        Cases_on `vs` >> simp[valueEncodingDefsTheory.val_wf_def] >>
        rpt strip_tac >> decide_tac) >>
     `mem_path_offset entry.type
        (local_path ++ [ValueSubscript (IntV &(LENGTH vs - 1))]) =
       SOME (k + 32 + (LENGTH vs - 1) * type_memory_size etv,etv)` by
       (drule_all exprSimPropsTheory.mem_path_offset_snoc >> simp[]) >>
     simp[Abbr `result`, local_place_at_def] >>
     qexistsl_tac [`root_ty`, `entry.type`] >> simp[]) >>
  `fin.storage_trace = mid.storage_trace /\ (fin with gas_obs := []) = fin` by
    simp[Abbr `fin`, evaluation_state_component_equality] >>
  `!tail. pop_place cx (MemoryPlace local_name local_path)
       (mid with gas_obs := tail) = (INL result,fin with gas_obs := tail)` by
    (gen_tac >>
     mp_tac (Q.SPECL [`cx`, `mid with gas_obs := tail`, `local_name`,
       `local_path`, `pre`, `local_scope`, `entry`, `rest`, `vs`, `updated`]
       exprSimPopNestedLocalPropsTheory.pop_memory_place_live) >>
     simp[NoAsms] >> (impl_tac >- simp[]) >>
     disch_then (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
     simp[Abbr `result`, Abbr `fin`, Abbr `updated_scopes`,
       evaluation_state_component_equality]) >>
  irule gas_outcome_full_pure >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`G'`, `fin`, `INL result`,
    `u with vs_inst_idx := t.vs_inst_idx + 9`, `tn'`] >>
  simp[NoAsms] >> conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `(fin with gas_obs := []) = fin`
    (fn th => PURE_REWRITE_TAC [th]) >>
  conj_tac
  >- (qpat_assum `!D. gas_origin_ptr_path _ _ _ _`
        (qspec_then `DF H` ACCEPT_TAC)) >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (qpat_assum `valid_horizon cx st0 H fin.storage_trace` mp_tac >>
     simp[NoAsms, Abbr `fin`]) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (qpat_assum `valid_horizon cx st0 H mid.storage_trace` mp_tac >>
     qpat_assum `eval_target_place cx bt _ =
       (INL (MemoryPlace local_name local_path),mid)` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     `storage_trace_frame (eval_target_place cx bt)` by
       simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
     drule_all vyperStorageFootprintTheory.valid_horizon_frame >> simp[]) >>
  qpat_assum `valid_horizon cx st0 H es.storage_trace`
    (fn vh => qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
      (fn fam => strip_assume_tac (MP (Q.SPEC `H` fam) vh))) >>
  qpat_assum `valid_horizon cx st0 H mid.storage_trace`
    (fn vh => qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
      (fn fam => strip_assume_tac (MP (Q.SPEC `H` fam) vh))) >>
  `stmt_state_rel H ctx func cenv cx mid t /\
   storage_well_formed_on cx mid (FST H)` by
    (qpat_x_assum `target_post H _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     PURE_REWRITE_TAC [target_post_def] >> rpt strip_tac >>
     first_assum ACCEPT_TAC) >>
  conj_tac
  >- (PURE_REWRITE_TAC [exprSimVVFrameTheory.vv_post_inst_idx] >>
      qpat_assum `fin = mid with scopes := updated_scopes`
        (fn th => PURE_REWRITE_TAC [th]) >>
      qpat_assum `Abbrev (result = _)`
        (fn th => PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
      irule (pop_memory_live_suffix_post |>
        Q.INST [`e` |-> `Pop ann bt`] |>
        SRULE [exprSimVVFrameTheory.vv_post_inst_idx, expr_type_def,
          loweringPostsTheory.expr_has_effect_thm]) >>
      qpat_assum `expr_sim_inv cenv cx env es` (irule_at Any) >>
      qpat_assum `mem_path_offset entry.type local_path =
        SOME (k,ArrayTV etv (Dynamic capacity))` (irule_at Any) >>
      qpat_assum `FLOOKUP cenv.ce_vars local_name = SOME (PtrVar (Var p) sz)`
        (irule_at Any) >>
      qpat_assum `evaluate_subscripts entry.type entry.value local_path =
        INL (ArrayV (DynArrayV vs))` (irule_at Any) >>
      qpat_assum `wb_frame cenv es mid sa s0 t` (irule_at Any) >>
      qpat_assum `local_ptrs_reserved cenv sm` (irule_at Any) >>
      simp[record_pop_def, Abbr `fin`, Abbr `updated_scopes`, Abbr `result`] >>
      conj_tac
      >- (qpat_assum `w2n (b + n2w k + 32w + _) = _` mp_tac >>
          SIMP_TAC pure_ss [wordsTheory.word_sub_def,
            AC wordsTheory.WORD_ADD_ASSOC wordsTheory.WORD_ADD_COMM,
            wordsTheory.WORD_MULT_COMM,
            AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM,
            arithmeticTheory.MULT_COMM] >> simp[] >> metis_tac[]) >>
      qpat_assum `mid.scopes = pre ++ local_scope::rest`
        (fn sc => qpat_assum `local_region cenv mid.scopes t local_name (w2n b) sz`
          (ACCEPT_TAC o REWRITE_RULE [sc]))) >>
  conj_tac >- suspend "memory_store_bound" >>
  conj_tac
  >- (qpat_assum `u = t with <|vs_vars := _; vs_memory := _|>`
        (fn th => PURE_ONCE_REWRITE_TAC [th]) >> simp[]) >>
  conj_tac >- simp[memory_pop_insts_def] >>
  conj_tac >- suspend "memory_alloca_history" >>
  conj_tac
  >- (qpat_assum `u = t with <|vs_vars := _; vs_memory := _|>`
        (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
      qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp t` mp_tac >>
      simp[NoAsms, allocas_below_fmp_def] >> metis_tac[]) >>
  conj_tac
  >- (qpat_assum `u = t with <|vs_vars := _; vs_memory := _|>`
        (fn th => PURE_ONCE_REWRITE_TAC [th]) >> simp[]) >>
  conj_tac >- suspend "memory_ghost" >>
  conj_tac >- suspend "memory_pointer" >>
  conj_tac >- simp[Abbr `result`, NoAsms] >>
  simp[contextTheory.vv_location_def, contextTheory.mk_ptr_def] >>
  conj_tac >- suspend "memory_buffer" >>
  irule ghost_kept_at_clean_suffix >>
  qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1` (irule_at Any) >>
  simp[] >> rpt strip_tac >>
  qpat_assum `!q. not_fresh_at sa q ==> _ /\ _ /\ _`
    (qspec_then `x` mp_tac) >> simp[]
QED

Resume pop_vv_full_of_target[memory_store_bound]:
  `u.vs_alloca_next = t.vs_alloca_next` by
    (qpat_assum `u = t with <|vs_vars := _; vs_memory := _|>`
       (fn th => PURE_ONCE_REWRITE_TAC [th]) >> simp[]) >>
  qpat_assum `read_result cx result fin = (INL (LAST vs),fin)` mp_tac >>
  qpat_assum `evaluate_type (get_tenv cx) ann = SOME etv` mp_tac >>
  qpat_assum `eval_operand (Var x6) u = SOME _` mp_tac >>
  qpat_assum `w2n (b + n2w k + 32w + _) = _` mp_tac >>
  qpat_assum `sz + w2n b <= t.vs_alloca_next` mp_tac >>
  qpat_assum `k + 32 + (LENGTH vs - 1) * type_memory_size etv +
      type_memory_size etv <= sz` mp_tac >>
  qpat_assum `val_store_size etv (LAST vs) <= type_memory_size etv` mp_tac >>
  qpat_assum `u.vs_alloca_next = t.vs_alloca_next` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  simp[exprSimMemDefsTheory.vv_store_bound_def, expr_type_def,
    lowered_value_type_def, contextTheory.mk_ptr_def] >>
  conj_tac >> gvs[]
QED

Resume pop_vv_full_of_target[memory_alloca_history]:
  `alloca_inv t` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx mid t`
       (mp_tac o REWRITE_RULE [stmt_state_rel_def]) >>
     rpt strip_tac >> first_assum ACCEPT_TAC) >>
  `t.vs_inst_idx + 9 = LENGTH sb.cs_current_insts` by
    simp[memory_pop_insts_def] >>
  pop_assum (fn th => PURE_REWRITE_TAC [th]) >>
  irule emitted_alloca_history >>
  qpat_assum `run_inst_seq (memory_pop_insts _ _ _ _ _ _ _ _ _ _) t = OK u`
    (irule_at Any) >>
  qpat_assum `fn_has_code sm sb func` (irule_at Any) >>
  simp[memory_pop_insts_def, mk_inst_def, is_terminator_def]
QED

Resume pop_vv_full_of_target[memory_pointer]:
  qpat_assum `read_result cx result fin = (INL (LAST vs),fin)` mp_tac >>
  qpat_assum `evaluate_type (get_tenv cx) ann = SOME etv` mp_tac >>
  qpat_assum `op_taint tn' (Var x6) = {}` mp_tac >>
  qpat_assum `FLOOKUP G' x6 = SOME (prov_base,prov_size)` mp_tac >>
  qpat_assum `eval_operand (Var x6) u = SOME _` mp_tac >>
  qpat_assum `w2n (b + n2w k + 32w + _) = _` mp_tac >>
  qpat_assum `!mem. mem_agree_outside tn1.t_mem u.vs_memory mem ==> _ /\ _` mp_tac >>
  qpat_assum `tn'.t_mem = tn1.t_mem` mp_tac >>
  qpat_assum `val_store_size etv (LAST vs) <= type_memory_size etv` mp_tac >>
  qpat_assum `prov_base <= w2n (b + n2w k + 32w + _)` mp_tac >>
  qpat_assum `w2n (b + n2w k + 32w + _) + type_memory_size etv <=
    prov_base + prov_size` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  simp[NoAsms, ptr_vv_ok_def, contextTheory.mk_ptr_def, expr_type_def,
    post_value_type_def] >>
  conj_tac >- simp[] >>
  qexists_tac `LAST vs` >> simp[] >>
  simp[ptr_mem_ok_def] >> rpt gen_tac >> strip_tac >>
  gvs[]
QED

Resume pop_vv_full_of_target[memory_buffer]:
  qpat_assum `type_memory_bytes cenv ann = type_memory_size etv` mp_tac >>
  qpat_assum `FLOOKUP G' x6 = SOME (prov_base,prov_size)` mp_tac >>
  qpat_assum `eval_operand (Var x6) u = SOME _` mp_tac >>
  qpat_assum `prov_base <= w2n (b + n2w k + 32w + _)` mp_tac >>
  qpat_assum `w2n (b + n2w k + 32w + _) + type_memory_size etv <=
    prov_base + prov_size` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  simp[ptr_buf_ok_def, lowered_value_type_def, expr_type_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >> decide_tac
QED

Resume pop_vv_full_of_target[memory_ghost]:
  `local_ptrs_rel func cenv mid.scopes t` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx mid t`
       (mp_tac o REWRITE_RULE [stmt_state_rel_def, state_rel_def]) >>
     rpt strip_tac >> first_assum ACCEPT_TAC) >>
  `0 < sz` by decide_tac >>
  `lo <= w2n b` by
    (`dead_lo_ok H (DF H) lo cenv cx` by
       (qpat_assum `!H. dead_lo_ok H (DF H) lo cenv cx`
          (qspec_then `H` ACCEPT_TAC)) >>
     qpat_assum `body_inv tops ctx cenv cx` mp_tac >>
     qpat_assum `expr_sim_inv cenv cx env es` mp_tac >>
     qpat_assum `stmt_state_rel H ctx func cenv cx mid t` mp_tac >>
     qpat_assum `local_region cenv mid.scopes t local_name (w2n b) sz` mp_tac >>
     qpat_assum `0 < sz` mp_tac >>
     qpat_assum `dead_lo_ok H (DF H) lo cenv cx` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     metis_tac[body_full_local_region_lower_bound]) >>
  `mem_bytes_at 0 lo
     (mstore (w2n b + k) (n2w (LENGTH vs - 1)) t).vs_memory =
   mem_bytes_at 0 lo t.vs_memory` by
    (irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  qpat_assum `ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` mp_tac >>
  qpat_assum `local_ptrs_rel func cenv mid.scopes t` mp_tac >>
  qpat_assum `local_region cenv mid.scopes t local_name (w2n b) sz` mp_tac >>
  qpat_assum `lookup_scopes local_name mid.scopes = SOME entry` mp_tac >>
  qpat_assum `FLOOKUP cenv.ce_vars local_name = SOME (PtrVar (Var p) sz)` mp_tac >>
  qpat_assum `lookup_var p t = SOME b` mp_tac >>
  qpat_assum `ptr_covers G1 tn1 p t sz` mp_tac >>
  qpat_assum `k + 32 <= sz` mp_tac >>
  qpat_assum `lo <= w2n b` mp_tac >>
  qpat_assum `mem_bytes_at 0 lo (mstore (w2n b + k) _ t).vs_memory = _` mp_tac >>
  qpat_assum `tn1.t_mem DIFF _ = tn1.t_mem` mp_tac >>
  qpat_assum `!mem. mem_agree_outside tn1.t_mem u.vs_memory mem ==> _ /\ _` mp_tac >>
  qpat_assum `lookup_scopes local_name updated_scopes = SOME _` mp_tac >>
  qpat_assum `!j. j <> local_name ==> lookup_scopes j updated_scopes = _` mp_tac >>
  qpat_assum `fin = mid with scopes := updated_scopes` mp_tac >>
  qpat_assum `Abbrev (fin = _)` mp_tac >>
  qpat_assum `Abbrev (updated_scopes = _)` mp_tac >>
  qpat_assum `u.vs_memory = (mstore (w2n b + k) _ t).vs_memory` mp_tac >>
  qpat_assum `u = t with <|vs_vars := _; vs_memory := _|>` mp_tac >>
  qpat_assum `!q. not_fresh_at sa q ==> _ /\ _ /\ _` mp_tac >>
  qpat_assum `local_ptrs_reserved cenv sa` mp_tac >>
  qpat_assum `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> _` mp_tac >>
  qpat_assum `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> _` mp_tac >>
  qpat_assum `tn'.t_mem = tn1.t_mem` mp_tac >>
  qpat_assum `tn'.t_stor = tn1.t_stor` mp_tac >>
  qpat_assum `tn'.t_trans = tn1.t_trans` mp_tac >>
  qpat_assum `tn'.t_imm = tn1.t_imm` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  `!name new_entry q cap.
     lookup_scopes name updated_scopes = SOME new_entry /\
     FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var q) cap) ==>
     ptr_covers G1 tn1 q t cap /\
     !w mem. lookup_var q t = SOME w /\
       mem_agree_outside tn1.t_mem u.vs_memory mem ==>
       val_in_memory new_entry.type new_entry.value (w2n w) mem` by
    (qx_genl_tac [`name`, `new_entry`, `q`, `cap`] >> strip_tac >>
     Cases_on `name = local_name`
     >- (gvs[] >> rpt strip_tac >>
         qpat_assum `!mem. mem_agree_outside tn1.t_mem u.vs_memory mem ==> _ /\ _`
           (drule o Q.SPEC `mem`) >> simp[]) >>
     `lookup_scopes name mid.scopes = SOME new_entry` by metis_tac[] >>
     qpat_assum `ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [ghost_inv_at_def]) >>
     disch_then (qspecl_then [`name`, `new_entry`, `q`, `cap`] mp_tac) >>
     simp[] >> strip_tac >>
     qx_genl_tac [`w`, `mem`] >> strip_tac >>
     `local_region cenv mid.scopes t name (w2n w) cap` by
       (simp[local_region_def] >> metis_tac[]) >>
     `regions_disjoint (w2n b) sz (w2n w) cap` by
       (qpat_assum `local_ptrs_rel func cenv mid.scopes t`
          (mp_tac o CONJUNCT2 o REWRITE_RULE [local_ptrs_rel_def]) >>
        disch_then (qspecl_then [`local_name`, `name`, `w2n (b:bytes32)`, `sz`,
          `w2n (w:bytes32)`, `cap`] mp_tac) >> simp[]) >>
     mp_tac (Q.SPECL [`func`, `cenv`, `mid.scopes`, `t`, `name`, `new_entry`,
       `q`, `cap`, `w2n (b:bytes32) + k`, `w`, `n2w (LENGTH (vs:value list) - 1)`,
       `tn1.t_mem`, `tn1.t_mem`] mstore_local_robust) >>
     impl_tac
     >- (simp[] >> fs[regions_disjoint_def] >> decide_tac) >>
     disch_then (qspec_then `mem` mp_tac) >>
     qpat_assum `u.vs_memory = (mstore (w2n b + k) _ t).vs_memory`
       (fn th => PURE_REWRITE_TAC [GSYM th]) >> simp[arithmeticTheory.ADD_COMM]) >>
  `ghost_inv_at (DF H) lo d cenv cx fin G1 tn1
      (mstore (w2n b + k) (n2w (LENGTH vs - 1)) t)` by
    (qpat_assum `ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` mp_tac >>
     PURE_REWRITE_TAC [ghost_inv_at_def] >> strip_tac >>
     PURE_REWRITE_TAC [ghost_inv_at_def] >> conj_tac
     >- (qx_genl_tac [`new_name`, `updated_entry`, `local_var`, `local_size`] >>
         strip_tac >>
         `lookup_scopes new_name updated_scopes = SOME updated_entry` by
           fs[Abbr `fin`, Abbr `updated_scopes`] >>
         qpat_assum `!name new_entry q cap.
           lookup_scopes name updated_scopes = SOME new_entry /\ _ ==> _`
           (qspecl_then [`new_name`, `updated_entry`, `local_var`, `local_size`] mp_tac) >>
         (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
         conj_tac
         >- gvs[ptr_covers_def, lookup_var_def, mstore_def] >>
         rpt gen_tac >> strip_tac >>
         qpat_assum `!w mem. _ ==>
            val_in_memory updated_entry.type updated_entry.value _ mem`
           irule >> gvs[lookup_var_def, mstore_def]) >>
     conj_tac
     >- (Cases_on `d` >- simp[return_buf_ptr_def] >>
         PairCases_on `x` >>
         gvs[return_buf_ptr_def, ptr_covers_def, lookup_var_def, mstore_def] >>
         metis_tac[]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- gvs[stor_taint_ok_at_def, mstore_def] >>
     conj_tac >- simp[] >>
     gvs[allocas_from_def, mstore_def] >> first_assum ACCEPT_TAC) >>
  irule ghost_inv_at_exterior_frame >>
  qpat_assum `ghost_inv_at (DF H) lo d cenv cx fin G1 tn1 _` (irule_at Any) >>
  qexists_tac `sa` >> simp[lookup_var_def, mstore_def] >>
  qpat_assum `u = t with <|vs_vars := _; vs_memory := _|>`
    (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
  simp[lookup_var_def, mstore_def] >>
  rpt strip_tac >>
  qpat_assum `!q. not_fresh_at sa q ==> _ /\ _ /\ _`
    (fn th => ACCEPT_TAC (REWRITE_RULE [lookup_var_def]
      (CONJUNCT1 (MATCH_MP (Q.SPEC `x` th)
        (ASSUME ``not_fresh_at sa x``)))))
QED

Theorem pop_full_storage_static_path[local]:
  ALL_DISTINCT [x0;x1;x2;x3;x4;x5;x6] /\
  (!q. hdr = Var q ==> ~MEM q [x0;x1;x2;x3;x4;x5;x6]) /\
  eval_operand hdr s = SOME slot /\ op_prov G hdr = NONE /\ op_taint tn hdr = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  (if tr then tload slot s else sload slot s) <> 0w /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ s.vs_call_ctx.cc_static /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (TAKE 5 (nested_pop_suffix hdr tr id esz x0 x1 x2 x3 x4 x5 x6))
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  get_instruction bb (s.vs_inst_idx+5) =
    SOME (mk_inst (id+5) (if tr then TSTORE else SSTORE) [hdr;Var x3] []) ==>
  ?v G' tn'. !D.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (Abort ExHalt_abort v,G',tn')
Proof
  strip_tac >>
  mp_tac (Q.INST [`out` |-> `x0`, `fn` |-> `func`]
    (SPEC_ALL pop_full_storage_load)) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`s1`,`G1`,`tn1`] strip_assume_tac) >>
  qabbrev_tac `lenw = if tr then tload slot s else sload slot s` >>
  `lookup_var x0 s1 = SOME lenw /\ allocas_from lo s1` by
    (qpat_assum `s1 = update_var x0 _ s` (fn th => PURE_REWRITE_TAC [th]) >>
     simp[lookup_var_def,update_var_def,FLOOKUP_UPDATE,Abbr `lenw`,allocas_from_def] >>
     qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s1` by
    (qpat_assum `s1 = update_var x0 _ s` (fn th => PURE_REWRITE_TAC [th]) >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     simp[NoAsms, allocas_below_fmp_def, update_var_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`s` |-> `s1`,`G` |-> `G1`,`tn` |-> `tn1`,
    `n` |-> `lenw`,`id` |-> `id+1`,`p` |-> `x0`,`fn` |-> `func`]
    (SPEC_ALL pop_full_memory_scalar_chunk)) >>
  (impl_tac >- (simp[Abbr `lenw`] >> fs[])) >>

  disch_then (qx_choosel_then [`s2`,`G2`,`tn2`] strip_assume_tac) >>
  `!D k. inst_seq_ptr D lo ctx func PG G1 tn1
    [mk_inst (id+1) ISZERO [Var x0] [x1];
     mk_inst (id+1+1) ISZERO [Var x1] [x2];
     mk_inst (id+1+2) ASSERT [Var x2] [];
     mk_inst (id+1+3) SUB [Var x0;Lit 1w] [x3]]
    (s1 with vs_inst_idx := k) G2 tn2` by
    (mp_tac (Q.INST [`p` |-> `x0`,`s` |-> `s1`,`G` |-> `G1`,
       `tn` |-> `tn1`,`id` |-> `id+1`,`H` |-> `G2`,`tm` |-> `tn2`,
       `n` |-> `lenw`,`D0` |-> `ARB`,`fn` |-> `func`]
       (SPEC_ALL pop_full_memory_scalar_chunk_uniform)) >>
     impl_tac >- (fs[] >> metis_tac[]) >> simp[]) >>
  suspend "prefix"
QED

Resume pop_full_storage_static_path[prefix]:
  qabbrev_tac `load = [mk_inst id (if tr then TLOAD else SLOAD) [hdr] [x0]]` >>
  qmatch_asmsub_abbrev_tac `run_inst_seq chunk s1 = OK s2` >>
  qabbrev_tac `prefix = load ++ chunk` >>
  `run_inst_seq load s = OK s1` by simp[Abbr `load`,run_inst_seq_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) load /\
   EVERY (\i. ~is_terminator i.inst_opcode) chunk` by
    (Cases_on `tr` >> simp[Abbr `load`,Abbr `chunk`,mk_inst_def,is_terminator_def]) >>
  `run_inst_seq prefix s = OK s2` by
    metis_tac[run_inst_seq_append] >>
  `!D k. inst_seq_ptr D lo ctx func PG G tn prefix
    (s with vs_inst_idx := k) G2 tn2` by
    (simp[Abbr `prefix`] >> metis_tac[inst_seq_ptr_uniform_append]) >>
  `prefix = TAKE 5 (nested_pop_suffix hdr tr id esz x0 x1 x2 x3 x4 x5 x6)` by
    simp[Abbr `prefix`,Abbr `load`,Abbr `chunk`,nested_pop_suffix_def,
      arithmeticTheory.ADD_ASSOC] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (s2 with vs_inst_idx := s.vs_inst_idx+5),G2,tn2)` by
    (gen_tac >>
     `run_inst_seq_mem_ok prefix s` by
       (irule run_inst_seq_mem_ok_every >> Cases_on `tr` >>
        simp[Abbr `prefix`,Abbr `load`,Abbr `chunk`,mk_inst_def,inst_dload_in_section_def] >>
        rpt conj_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
     `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) prefix` by
       (Cases_on `tr` >> simp[Abbr `prefix`,Abbr `load`,Abbr `chunk`,mk_inst_def,is_terminator_def]) >>
     `inst_seq_ptr D lo ctx func PG G tn prefix s G2 tn2` by
       (`(s with vs_inst_idx := s.vs_inst_idx) = s` by
          simp[venom_state_component_equality] >>
        qpat_assum `(s with vs_inst_idx := s.vs_inst_idx) = s`
          (fn eq => qpat_assum `!D k. inst_seq_ptr _ _ _ _ _ G tn prefix _ _ _`
            (qspecl_then [`D`,`s.vs_inst_idx`]
              (ACCEPT_TAC o REWRITE_RULE [eq])))) >>
     `isPREFIX prefix (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
     `(ctx_has_dalloca ctx ==> !pre i post u.
         prefix = pre ++ i::post /\ run_inst_seq pre s = OK u ==>
         dalloca_no_wrap i u)` by
       (rpt strip_tac >>
        qpat_x_assum `_ = _ ++ i::_` (mp_tac o Q.AP_TERM `MEM i`) >>
        Cases_on `tr` >> simp[Abbr `prefix`,Abbr `load`,Abbr `chunk`] >>
        disch_then (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) >>
        simp[dalloca_no_wrap_def,mk_inst_def]) >>
     drule_all run_inst_seq_gas_origin_ptr_path >>
     Cases_on `tr` >> simp[Abbr `prefix`,Abbr `load`,Abbr `chunk`,mk_inst_def,
       nested_pop_suffix_def]) >>
  qexistsl_tac [`halt_state (set_returndata [] (s2 with vs_inst_idx := s.vs_inst_idx+5))`,
    `G2`,`tn2`] >> gen_tac >>
  qpat_assum `!D. gas_origin_ptr_path _ _ [] _` (qspec_then `D` assume_tac) >>
  irule gas_origin_ptr_path_trans >> goal_assum (drule_at Any) >>
  suspend "exit"
QED

Resume pop_full_storage_static_path[exit]:
  `s2.vs_call_ctx = s.vs_call_ctx /\ s2.vs_halted = s.vs_halted /\
   s2.vs_current_bb = s.vs_current_bb /\ s2.vs_labels = s.vs_labels /\
   allocas_from lo s2` by
    (qpat_assum `s2 with vs_vars := s1.vs_vars = s1` mp_tac >>
     simp[venom_state_component_equality,update_var_def,allocas_from_def] >>
     fs[allocas_from_def] >> metis_tac[]) >>
  `eval_operand hdr s2 = SOME slot /\ op_taint tn2 hdr = {}` by
    (Cases_on `hdr` >> fs[eval_operand_def,op_taint_def,lookup_var_def,
       update_var_def,FLOOKUP_UPDATE] >> metis_tac[]) >>
  qabbrev_tac `u = s2 with vs_inst_idx := s.vs_inst_idx+5` >>
  qabbrev_tac `i = mk_inst (id+5) (if tr then TSTORE else SSTORE) [hdr;Var x3] []` >>
  `eval_operand hdr u = SOME slot /\ eval_operand (Var x3) u = SOME (lenw-1w)` by
    (conj_tac
     >- simp[Abbr `u`,ghostPcTransportPtrTheory.eval_operand_inst_idx] >>
     fs[Abbr `u`,eval_operand_def,lookup_var_def]) >>
  `step_inst_base i u = Abort ExHalt_abort (halt_state (set_returndata [] u))` by
    (`u.vs_call_ctx.cc_static` by simp[Abbr `u`] >>
     Cases_on `tr` >> simp[Abbr `i`] >>
     metis_tac[loweringHaltTheory.step_TSTORE,emitHelperPropsTheory.step_SSTORE]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s2` by
    (qpat_assum `(s2 with vs_vars := _) = s1` mp_tac >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s1` mp_tac >>
     simp[NoAsms, venom_state_component_equality, allocas_below_fmp_def] >>
     metis_tac[]) >>
  `ptr_inst_ok D lo 0 ctx func G2 tn2 i u` by
    (Cases_on `tr` >>
     simp[ptrSafeRunTheory.ptr_inst_ok_def,access_ok_def,taint_ok_def,Abbr `i`,Abbr `u`,
       allocas_from_def,allocas_below_fmp_def,mk_inst_def,source_memory_write_ranges_def,
       source_memory_read_ranges_def] >>
     fs[] >> simp[GSYM mk_inst_def,step_inst_non_invoke] >>
     rpt strip_tac >> gvs[]) >>
  irule exit_inst_origin_ptr >> Cases_on `tr` >> fs[Abbr `i`,Abbr `u`] >>
  simp[exit_result_def,step_inst_non_invoke,
    mem_safe_step_non_invoke,dalloca_no_wrap_def,
    gas_events_step_def,gas_count_step_def,mk_inst_def,
    inst_mem_below_frontier_def,inst_dload_in_section_def,
    source_memory_read_ranges_def,source_memory_write_ranges_def] >>
  fs[GSYM mk_inst_def,step_inst_non_invoke]
QED

Finalise pop_full_storage_static_path[local]

Resume pop_vv_full_of_target[storage_suffix]:
  rename1 `StoragePlace tr slot tv` >>
  `target_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx
     es sa sm s0 mid (PlaceR (StoragePlace tr slot tv))
     (Type (ArrayT ann (Dynamic n))) (rb0,rb1,rb2) t` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
  drule nested_pop_storage_target_metadata >> strip_tac >> gvs[] >>
  rename1 `evaluate_type (get_tenv cx) ann = SOME etv` >>
  `op_taint tn1 rb0 = {} /\ op_prov G1 rb0 = NONE` by
    (fs[target_ptr_ok_def] >> metis_tac[]) >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule_all exprSimPopStorageTheory.pop_storage_element_size >>
  disch_then (qspec_then `tr` assume_tac) >>
  fs[GSYM slot_loc_def, value_type_place_def] >>
  `word_scale (slot_loc tr) = 1` by
    (Cases_on `tr` >> simp[slot_loc_def,word_scale_def]) >>
  gvs[] >>
  `?offset root_tv path delta.
     MEM (StorageRoot tr offset root_tv) mid.storage_trace /\
     storage_subregion root_tv path delta (ArrayTV etv (Dynamic n)) /\
     slot = n2w offset + n2w delta` by
    (irule vyperFiniteStoragePreservationTheory.eval_target_place_observed_region >>
     goal_assum (drule_at Any)) >>
  `ghost_inv_at (DF (storage_trace_horizon mid.storage_trace)) lo d cenv cx
      mid G1 tn1 t` by metis_tac[] >>
  `allocas_from lo t` by fs[ghost_inv_at_def] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    (?root rtv path delta.
       MEM (tr,root,rtv) (FST H) /\
       storage_subregion rtv path delta (ArrayTV etv (Dynamic n)) /\
       w2n slot = w2n root + delta) /\
    w2n slot + type_slot_size (ArrayTV etv (Dynamic n)) <= dimword(:256) /\
    slots_in_range (vyperStorageBackend$get_storage cx mid tr) (w2n slot)
      (ArrayTV etv (Dynamic n)) /\
    storage_read_live H tr (vyperStorageBackend$get_storage cx mid tr) slot
      (ArrayTV etv (Dynamic n))` by
    (qx_gen_tac `H` >> disch_tac >>
     `storage_well_formed_on cx mid (FST H)` by
       (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
          (qspec_then `H` mp_tac) >>
        (impl_tac >- first_assum ACCEPT_TAC) >>
        PURE_REWRITE_TAC [target_post_def] >> rpt strip_tac >>
        first_assum ACCEPT_TAC) >>
     `regions_consistent (FST H) /\
      storage_observations_ok cx H mid.storage_trace` by
       fs[vyperStorageFootprintTheory.valid_horizon_def] >>
     `MEM (tr,n2w offset,root_tv) (FST H)` by
       (irule vyperFiniteStoragePreservationTheory.storage_observations_ok_root >>
        goal_assum (drule_at Any) >> simp[]) >>
     `w2n (n2w offset : bytes32) + type_slot_size root_tv <= dimword(:256)` by
       metis_tac[vyperStorageFootprintTheory.regions_consistent_def] >>
     drule vyperStoragePlaceRegionTheory.storage_subregion_bounds >> strip_tac >>
     `0 < type_slot_size (ArrayTV etv (Dynamic n))` by
       simp[vyperValueTheory.type_slot_size_def] >>
     `w2n slot = w2n (n2w offset : bytes32) + delta` by
       (`w2n (n2w offset : bytes32) + delta < dimword(:256)` by decide_tac >>
        qpat_assum `slot = _` (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
        irule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >>
        first_assum ACCEPT_TAC) >>
     conj_tac
     >- (qexistsl_tac [`n2w offset`, `root_tv`, `path`, `delta`] >> simp[]) >>
     conj_tac >- decide_tac >>
     conj_tac
     >- (qpat_assum `w2n slot = _` (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
         irule vyperStorageRegionWriteTheory.storage_subregion_slots_in_range >>
         goal_assum (drule_at Any) >>
         metis_tac[vyperStorageFootprintTheory.storage_well_formed_on_def]) >>
     irule accountsRelPropsTheory.storage_subregion_read_live >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     conj_tac >- gvs[] >>
     irule accountsRelPropsTheory.observed_storage_region_read_live >> simp[]) >>
  qpat_assum `compile_dynarray_pop rb0 1 (type_slot_size etv) _ _ _ sm = _`
    (assume_tac o REWRITE_RULE [slot_loc_def]) >>
  drule nested_pop_suffix_shape >> strip_tac >> suspend "storage_live"
QED

Resume pop_vv_full_of_target[storage_live]:
  qabbrev_tac `H0 = storage_trace_horizon mid.storage_trace` >>
  `valid_horizon cx st0 H0 mid.storage_trace` by simp[Abbr `H0`] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
     (?root rtv path delta. _) /\ _`
    (fn th => qpat_assum `valid_horizon cx st0 H0 mid.storage_trace`
      (strip_assume_tac o CONJUNCT2 o MP (Q.SPEC `H0` th))) >>
  `stmt_state_rel H0 ctx func cenv cx mid t /\
   ghost_inv_at (DF H0) lo d cenv cx mid G1 tn1 t /\
   dead_lo_ok H0 (DF H0) lo cenv cx` by
    (simp[Abbr `H0`] >> metis_tac[]) >>
  drule_all nested_pop_live_array_agree >> strip_tac >>
  drule nested_pop_array_header_load >> strip_tac >>
  `(t.vs_call_ctx.cc_static <=> cx.txn.is_static) /\
   t.vs_call_ctx.cc_address = cx.txn.target` by
    (qpat_assum `stmt_state_rel H0 ctx func cenv cx mid t`
       (strip_assume_tac o REWRITE_RULE
         [stmt_state_rel_def,state_rel_def,call_ctx_rel_def]) >> simp[]) >>
  `MEM (tr,n2w offset,root_tv) (FST H0)` by
    (irule vyperFiniteStoragePreservationTheory.storage_observations_ok_root >>
     qexistsl_tac [`cx`, `mid.storage_trace`] >>
     simp[] >> fs[vyperStorageFootprintTheory.valid_horizon_def]) >>
  `storage_read_live H0 tr
     (if tr then contract_transient t else contract_storage t) slot
     (ArrayTV etv (Dynamic n))` by
    (irule accountsRelPropsTheory.storage_place_observed_read_live >>
     simp[vyperValueTheory.type_slot_size_def,
       vyperStoragePlaceObservedTheory.storage_place_observed_def] >>
     qexistsl_tac [`n2w offset`, `root_tv`, `path`, `delta`] >> simp[]) >>
  `key_taint (if tr then tn1.t_trans else tn1.t_stor) slot = {}` by
    (irule (INST_TYPE [alpha |-> ``:256``] storage_dead_key_taint_empty) >>
     qexistsl_tac [`H0`, `if tr then contract_transient t else contract_storage t`,
       `tr`, `ArrayTV etv (Dynamic n)`] >>
     simp[vyperValueTheory.type_slot_size_def] >>
     qpat_assum `ghost_inv_at (DF H0) lo d cenv cx mid G1 tn1 t`
       (mp_tac o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
         REWRITE_RULE [ghost_inv_at_def]) >>
     qpat_assum `dead_lo_ok H0 (DF H0) lo cenv cx` mp_tac >>
     qpat_assum `t.vs_call_ctx.cc_address = cx.txn.target` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     Cases_on `tr` >>
     gvs[dead_lo_ok_def,stor_taint_ok_at_def,sourceUnitExecutionTheory.cx_dead_def,
       contract_storage_def,contract_transient_def,vfmStateTheory.lookup_account_def]) >>
  `ALL_DISTINCT [x6;x5;x4;x3;x2;x1;x0] /\
   (!x. rb0 = Var x ==> ~MEM x [x0;x1;x2;x3;x4;x5;x6])` by
    (fs[] >> metis_tac[]) >>
  Cases_on `lookup_storage slot (vyperStorageBackend$get_storage cx mid tr) = 0w`
  >- suspend "storage_empty" >>
  Cases_on `cx.txn.is_static`
  >- suspend "storage_static" >>
  `~t.vs_call_ctx.cc_static` by simp[] >> suspend "storage_positive"
QED

Resume pop_vv_full_of_target[storage_empty]:
  drule_all fn_has_code_code >> strip_tac >>
  `isPREFIX
    [mk_inst sm.cs_next_id (if tr then TLOAD else SLOAD) [rb0] [x0];
     mk_inst (sm.cs_next_id+1) ISZERO [Var x0] [x1];
     mk_inst (sm.cs_next_id+2) ISZERO [Var x1] [x2]]
    (DROP t.vs_inst_idx bb.bb_instructions)` by
    (irule listTheory.isPREFIX_TRANS >>
     qexists_tac `nested_pop_suffix rb0 tr sm.cs_next_id (type_slot_size etv)
       x0 x1 x2 x3 x4 x5 x6` >>
     conj_tac >- simp[nested_pop_suffix_def] >> metis_tac[]) >>
  `get_instruction bb (t.vs_inst_idx+3) =
    SOME (mk_inst (sm.cs_next_id+3) ASSERT [Var x2] [])` by
    (drule_all fn_has_code_same_block >> strip_tac >> gvs[] >>
     first_x_assum (qspec_then `3` mp_tac) >> simp[nested_pop_suffix_def]) >>
  `(if tr then tload slot t else sload slot t) = 0w /\
   lookup_block t.vs_current_bb func.fn_blocks = SOME bb` by metis_tac[] >>
  mp_tac (Q.INST [`s` |-> `t`, `id` |-> `sm.cs_next_id`,
    `hdr` |-> `rb0`, `G` |-> `G1`, `tn` |-> `tn1`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    (SPEC_ALL pop_full_storage_empty_path)) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`v`,`G'`,`tn'`] strip_assume_tac) >>
  `pop_place cx (StoragePlace tr slot (ArrayTV etv (Dynamic n))) mid =
    (INR (Error (RuntimeError "pop empty storage array")),mid)` by
    (qpat_assum `lookup_storage slot (vyperStorageBackend$get_storage cx mid tr) = 0w`
       mp_tac >> rpt (pop_assum kall_tac) >> disch_tac >>
     simp[pop_place_def,vyperStorageBackendTheory.get_storage_backend_eq,
       bind_def,ignore_bind_def,
       check_def,assert_def,return_def,raise_def]) >>
  `!tail. pop_place cx (StoragePlace tr slot (ArrayTV etv (Dynamic n)))
    (mid with gas_obs := tail) =
    (INR (Error (RuntimeError "pop empty storage array")),mid with gas_obs := tail)` by
    metis_tac[nested_pop_storage_gas_obs] >>
  irule gas_outcome_full_exit >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G'`,`mid`,`Abort Revert_abort v`,
    `INR (Error (RuntimeError "pop empty storage array"))`,`tn'`] >>
  simp[exit_result_def] >> rpt strip_tac >>
  simp[exprSimDefsTheory.expr_exit_def,exprSimDefsTheory.halt_exit_def]
QED

Resume pop_vv_full_of_target[storage_static]:
  drule_all fn_has_code_code >> strip_tac >>
  `isPREFIX
    (TAKE 5 (nested_pop_suffix rb0 tr sm.cs_next_id (type_slot_size etv)
      x0 x1 x2 x3 x4 x5 x6))
    (DROP t.vs_inst_idx bb.bb_instructions)` by
    (irule listTheory.isPREFIX_TRANS >>
     qexists_tac `nested_pop_suffix rb0 tr sm.cs_next_id (type_slot_size etv)
       x0 x1 x2 x3 x4 x5 x6` >>
     conj_tac >- simp[nested_pop_suffix_def] >> metis_tac[]) >>
  `get_instruction bb (t.vs_inst_idx+5) =
    SOME (mk_inst (sm.cs_next_id+5) (if tr then TSTORE else SSTORE) [rb0;Var x3] [])` by
    (drule_all fn_has_code_same_block >> strip_tac >> gvs[] >>
     first_x_assum (qspec_then `5` mp_tac) >> simp[nested_pop_suffix_def]) >>
  `(if tr then tload slot t else sload slot t) <> 0w /\
   lookup_block t.vs_current_bb func.fn_blocks = SOME bb` by metis_tac[] >>
  mp_tac (Q.INST [`s` |-> `t`, `id` |-> `sm.cs_next_id`,
    `esz` |-> `type_slot_size etv`,
    `hdr` |-> `rb0`, `G` |-> `G1`, `tn` |-> `tn1`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    (SPEC_ALL pop_full_storage_static_path)) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`v`,`G'`,`tn'`] strip_assume_tac) >>
  `pop_place cx (StoragePlace tr slot (ArrayTV etv (Dynamic n))) mid =
    (INR (Error (RuntimeError "write in static context")),mid)` by
    (qpat_assum `lookup_storage slot (vyperStorageBackend$get_storage cx mid tr) <> 0w`
       mp_tac >> qpat_assum `cx.txn.is_static` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     `0 < w2n (lookup_storage slot (vyperStorageBackend$get_storage cx mid tr))` by
       (Cases_on `lookup_storage slot (vyperStorageBackend$get_storage cx mid tr)` >> fs[]) >>
     simp[pop_place_def,vyperStorageBackendTheory.get_storage_backend_eq,
       write_storage_slot_def,check_not_static_def,bind_def,ignore_bind_def,
       check_def,assert_def,return_def,raise_def]) >>
  `!tail. pop_place cx (StoragePlace tr slot (ArrayTV etv (Dynamic n)))
    (mid with gas_obs := tail) =
    (INR (Error (RuntimeError "write in static context")),mid with gas_obs := tail)` by
    metis_tac[nested_pop_storage_gas_obs] >>
  irule gas_outcome_full_exit >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G'`,`mid`,`Abort ExHalt_abort v`,
    `INR (Error (RuntimeError "write in static context"))`,`tn'`] >>
  simp[exit_result_def] >> rpt strip_tac >>
  simp[exprSimDefsTheory.expr_exit_def,exprSimDefsTheory.halt_exit_def]
QED

Resume pop_vv_full_of_target[storage_positive]:
  qpat_x_assum `elem = Var x6` SUBST_ALL_TAC >>
  qpat_assum `EVERY (\x. ~not_fresh_at sm x) [x0;x1;x2;x3;x4;x5;x6]`
    (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  `(if tr then tload slot t else sload slot t) <> 0w` by metis_tac[] >>
  mp_tac (Q.INST [`s` |-> `t`, `G` |-> `G1`, `tn` |-> `tn1`,
    `hdr` |-> `rb0`, `id` |-> `sm.cs_next_id`, `esz` |-> `type_slot_size etv`,
    `fn` |-> `func`] (SPEC_ALL pop_full_storage_checked_run)) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`u`,`G'`,`tn'`] strip_assume_tac) >>
  drule_all nested_pop_suffix_run >>
  disch_then (qspecl_then [`sm.cs_next_id`,`type_slot_size etv`]
    (qx_choose_then `raw` strip_assume_tac)) >>
  `raw = u` by
    (qpat_assum `run_inst_seq _ t = OK raw` mp_tac >>
     qpat_assum `run_inst_seq _ t = OK u` (fn th => PURE_REWRITE_TAC [th]) >> simp[]) >>
  qpat_x_assum `raw = u` SUBST_ALL_TAC >>
  qabbrev_tac `lenw = lookup_storage slot (vyperStorageBackend$get_storage cx mid tr)` >>
  `lenw <> 0w` by simp[Abbr `lenw`] >>
  `0 < w2n lenw` by
    (qpat_assum `lenw <> 0w` mp_tac >> rpt (pop_assum kall_tac) >>
     Cases_on `lenw` >> simp[]) >>
  `lenw - 1w = n2w (w2n lenw - 1)` by simp[wordsTheory.n2w_sub] >>
  `w2n lenw <= n` by
    (simp[NoAsms,Abbr `lenw`] >> irule exprSimPopStorageTheory.pop_array_length_bound >>
     qexists_tac `etv` >> first_assum ACCEPT_TAC) >>
  `u = (if tr then tstore slot (n2w (w2n lenw - 1)) t
         else sstore slot (n2w (w2n lenw - 1)) t) with vs_vars := u.vs_vars` by
    (Cases_on `tr` >> fs[] >> metis_tac[]) >>
  `!q. not_fresh_at sm q ==> lookup_var q u = lookup_var q t` by
    (qx_gen_tac `q` >> disch_tac >>
     qpat_assum `!x. ~MEM x _ ==> lookup_var x u = lookup_var x t` irule >>
     simp[] >> rpt conj_tac >> strip_tac >>
     qpat_assum `not_fresh_at sm q` mp_tac >>
     qpat_assum `q = _` (fn th => PURE_REWRITE_TAC [th]) >> simp[]) >>
  `!q. not_fresh_at sm q ==>
    FLOOKUP G' q = FLOOKUP G1 q /\ op_taint tn' (Var q) = op_taint tn1 (Var q)` by
    (qx_gen_tac `q` >> disch_tac >>
     qpat_assum `!q. ~MEM q _ ==> FLOOKUP G' q = FLOOKUP G1 q /\ _` irule >>
     simp[] >> rpt conj_tac >> strip_tac >>
     qpat_assum `not_fresh_at sm q` mp_tac >>
     qpat_assum `q = _` (fn th => PURE_REWRITE_TAC [th]) >> simp[]) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    (qpat_assum `ci_mono sa sm` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[ci_mono_def]) >>
  `!q. not_fresh_at sa q ==>
    lookup_var q u = lookup_var q t /\ FLOOKUP G' q = FLOOKUP G1 q /\
    op_taint tn' (Var q) = op_taint tn1 (Var q)` by
    (rpt strip_tac >>
     `not_fresh_at sm q` by
       (irule loweringShapeDefsTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
     simp[]) >>
  qabbrev_tac `fin = vyperStorageBackend$set_storage cx mid tr
    (apply_writes slot [(0,n2w (w2n lenw - 1))]
      (vyperStorageBackend$get_storage cx mid tr))` >>
  qabbrev_tac `last_slot = slot + n2w (1 + (w2n lenw - 1) * type_slot_size etv)` >>
  qabbrev_tac `result = PlaceR (StoragePlace tr last_slot etv)` >>
  `pop_place cx (StoragePlace tr slot (ArrayTV etv (Dynamic n))) mid =
    (INL result,fin)` by
    (mp_tac (Q.INST [`len` |-> `w2n (lenw:bytes32)`,`es` |-> `mid`,
       `tv` |-> `etv`,`cap` |-> `n`]
       (SPEC_ALL exprSimPopStorageTheory.pop_storage_positive_source)) >>
     impl_tac >- (conj_tac >- simp[NoAsms,Abbr `lenw`] >>
       conj_tac >> first_assum ACCEPT_TAC) >>
     simp[NoAsms,Abbr `fin`,Abbr `result`,Abbr `last_slot`]) >>
  `!tail. pop_place cx (StoragePlace tr slot (ArrayTV etv (Dynamic n)))
      (mid with gas_obs := tail) = (INL result,fin with gas_obs := tail)` by
    metis_tac[nested_pop_storage_gas_obs] >>
  `fin.storage_trace = mid.storage_trace /\ fin.scopes = mid.scopes /\
    (fin with gas_obs := []) = fin` by
    (Cases_on `tr` >> simp[Abbr `fin`,vyperStorageBackendTheory.set_storage_def,
      evaluation_state_component_equality]) >>
  `u.vs_memory = t.vs_memory /\ u.vs_allocas = t.vs_allocas /\
    u.vs_alloca_next = t.vs_alloca_next /\ u.vs_current_bb = t.vs_current_bb /\
    ~u.vs_halted` by
    (qpat_assum `u = _ with vs_vars := u.vs_vars`
       (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
     Cases_on `tr` >> simp[sstore_def,tstore_def]) >>
  `lookup_var x6 u = SOME last_slot` by
    (qpat_assum `lookup_var x6 u = _` mp_tac >>
     qpat_assum `(if tr then tload slot t else sload slot t) = _`
       (fn th => PURE_REWRITE_TAC [th]) >>
     simp[Abbr `last_slot`,GSYM wordsTheory.n2w_sub,
       wordsTheory.word_mul_n2w,GSYM wordsTheory.word_add_n2w,wordsTheory.WORD_ADD_ASSOC]) >>
  `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (t,G1,tn1) [] (OK (u with vs_inst_idx := t.vs_inst_idx+9),G',tn')` by
    (gen_tac >> drule_all fn_has_code_code >> strip_tac >>
     `lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
      isPREFIX (nested_pop_suffix rb0 tr sm.cs_next_id (type_slot_size etv)
        x0 x1 x2 x3 x4 x5 x6) (DROP t.vs_inst_idx bb.bb_instructions)` by simp[] >>
     `run_inst_seq_mem_ok
       (nested_pop_suffix rb0 tr sm.cs_next_id (type_slot_size etv)
         x0 x1 x2 x3 x4 x5 x6) t` by
       (irule run_inst_seq_mem_ok_every >> Cases_on `tr` >>
        simp[nested_pop_suffix_def,mk_inst_def,inst_dload_in_section_def] >>
        rpt conj_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
     `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
       (nested_pop_suffix rb0 tr sm.cs_next_id (type_slot_size etv)
         x0 x1 x2 x3 x4 x5 x6)` by
       (Cases_on `tr` >> simp[nested_pop_suffix_def,mk_inst_def,is_terminator_def]) >>
     `(ctx_has_dalloca ctx ==> !pre i post u.
         nested_pop_suffix rb0 tr sm.cs_next_id (type_slot_size etv)
           x0 x1 x2 x3 x4 x5 x6 = pre ++ i::post /\
         run_inst_seq pre t = OK u ==> dalloca_no_wrap i u)` by
       (rpt strip_tac >>
        qpat_x_assum `_ = _ ++ i::_` (mp_tac o Q.AP_TERM `MEM i`) >>
        Cases_on `tr` >> simp[nested_pop_suffix_def] >>
        disch_then (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) >>
        simp[dalloca_no_wrap_def,mk_inst_def]) >>
     qpat_assum `!D. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `D` assume_tac) >>
     drule_all run_inst_seq_gas_origin_ptr_path >>
     Cases_on `tr` >> simp[nested_pop_suffix_def,mk_inst_def]) >>
  irule gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G'`,`fin`,`INL result`,`u with vs_inst_idx := t.vs_inst_idx+9`,`tn'`] >>
  PURE_REWRITE_TAC [slot_loc_def] >>
  simp[NoAsms] >> conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `(fin with gas_obs := []) = fin` (fn th => PURE_REWRITE_TAC [th]) >>
  conj_tac >- (qpat_assum `!D. gas_origin_ptr_path _ _ _ _` (qspec_then `DF H` ACCEPT_TAC)) >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (qpat_assum `valid_horizon cx st0 H fin.storage_trace` mp_tac >>
     qpat_assum `fin.storage_trace = mid.storage_trace`
       (fn th => PURE_REWRITE_TAC [th]) >> simp[]) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (qpat_assum `valid_horizon cx st0 H mid.storage_trace` mp_tac >>
     qpat_assum `eval_target_place cx bt _ =
       (INL (StoragePlace tr slot (ArrayTV etv (Dynamic n))),mid)` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     `storage_trace_frame (eval_target_place cx bt)` by
       simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
     drule_all vyperStorageFootprintTheory.valid_horizon_frame >> simp[]) >>
  qpat_assum `valid_horizon cx st0 H es.storage_trace`
    (fn vh => qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
      (fn fam => strip_assume_tac (MP (Q.SPEC `H` fam) vh))) >>
  qpat_assum `valid_horizon cx st0 H mid.storage_trace`
    (fn vh => qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       target_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
      (fn fam => strip_assume_tac (MP (Q.SPEC `H` fam) vh))) >>
  `stmt_state_rel H ctx func cenv cx mid t /\ storage_well_formed_on cx mid (FST H)` by
    (qpat_assum `target_post H _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     PURE_REWRITE_TAC [target_post_def] >> rpt strip_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- suspend "storage_vv" >>
  conj_tac >- (Cases_on `tr` >> simp[exprSimMemDefsTheory.vv_store_bound_def,
    contextTheory.mk_ptr_def]) >>
  conj_tac >- simp[] >> conj_tac >- simp[nested_pop_suffix_def] >>
  conj_tac >- suspend "storage_history" >>
  conj_tac
  >- (qpat_assum `u = _ with vs_vars := u.vs_vars`
        (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
      qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp t` mp_tac >>
      Cases_on `tr` >> simp[NoAsms, sstore_def, tstore_def, allocas_below_fmp_def] >>
      metis_tac[]) >>
  conj_tac >- simp[] >>
  conj_tac >- suspend "storage_ghost" >> conj_tac >- suspend "storage_pointer" >>
  conj_tac >- simp[Abbr `result`, NoAsms] >>
  Cases_on `tr` >> simp[contextTheory.vv_location_def,contextTheory.mk_ptr_def] >>
  irule ghost_kept_at_clean_suffix >>
  qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1` (irule_at Any) >>
  simp[] >> rpt strip_tac >>
  qpat_assum `!q. not_fresh_at sa q ==> _ /\ _ /\ _` (qspec_then `x` mp_tac) >> simp[]
QED

Resume pop_vv_full_of_target[storage_vv]:
  `?hroot hrtv hpath hoff. MEM (tr,hroot,hrtv) (FST H) /\
    storage_subregion hrtv hpath hoff (ArrayTV etv (Dynamic n)) /\
    w2n slot = w2n hroot + hoff` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       (?root rtv path delta. _) /\ _`
      (fn fam => qpat_assum `valid_horizon cx st0 H mid.storage_trace`
        (ACCEPT_TAC o CONJUNCT1 o MP (Q.SPEC `H` fam)))) >>
  `stmt_state_rel H ctx func cenv cx fin u` by
    (simp[NoAsms,Abbr `fin`,Abbr `lenw`] >> irule nested_pop_updated_state_rel >>
     qpat_assum `stmt_state_rel H ctx func cenv cx mid t` (irule_at Any) >>
     qpat_assum `MEM (tr,hroot,hrtv) (FST H)` (irule_at Any) >>
     qpat_assum `storage_subregion hrtv hpath hoff _` (irule_at Any) >>
     qpat_assum `local_ptrs_reserved cenv sa` (irule_at Any) >> simp[]) >>
  `well_formed_type_value (ArrayTV etv (Dynamic n))` by
    first_assum ACCEPT_TAC >>
  `storage_well_formed_on cx fin (FST H)` by
    (qpat_assum `valid_horizon cx st0 H mid.storage_trace` mp_tac >>
     qpat_assum `storage_well_formed_on cx mid (FST H)` mp_tac >>
     qpat_assum `MEM (StorageRoot tr offset root_tv) mid.storage_trace` mp_tac >>
     qpat_assum `storage_subregion root_tv path delta (ArrayTV etv (Dynamic n))` mp_tac >>
     qpat_assum `slot = n2w offset + n2w delta` mp_tac >>
     qpat_assum `well_formed_type_value (ArrayTV etv (Dynamic n))` mp_tac >>
     qpat_assum `pop_place cx _ mid = (INL result,fin)` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt disch_tac >>
     mp_tac (Q.INST [`p` |-> `StoragePlace tr slot (ArrayTV etv (Dynamic n))`,
      `st` |-> `mid`,`st'` |-> `fin`,`res` |-> `INL result`,
      `observations` |-> `mid.storage_trace`]
      (SPEC_ALL vyperFiniteStoragePreservationTheory.pop_place_preserves_storage_well_formed_on)) >>
     impl_tac
     >- (simp[vyperPlaceTypingTheory.runtime_place_typed_storage] >>
         fs[vyperStorageFootprintTheory.valid_horizon_def] >> metis_tac[]) >>
     simp[]) >>
  `storage_holds cx tr ann result last_slot fin u` by
    (mp_tac (Q.INST [`es` |-> `mid`,`s` |-> `t`,`w` |-> `slot`,
       `tv` |-> `etv`,`len` |-> `w2n (lenw:bytes32)`,`elem` |-> `last_slot`]
       (SPEC_ALL nested_pop_positive_holds)) >>
     impl_tac
     >- (conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- simp[NoAsms,Abbr `lenw`] >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- simp[NoAsms,Abbr `last_slot`] >> first_assum ACCEPT_TAC) >>
     simp[NoAsms,Abbr `fin`,Abbr `result`]) >>
  PURE_REWRITE_TAC [exprSimVVFrameTheory.vv_post_inst_idx] >>
  irule nested_pop_suffix_vv_post >>
  qpat_assum `target_post H _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[Abbr `result`, vv_place_ptr_def, contextTheory.mk_ptr_def,
    slot_loc_def, eval_operand_def]
QED

Resume pop_vv_full_of_target[storage_history]:
  `alloca_inv t` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx mid t`
       (mp_tac o REWRITE_RULE [stmt_state_rel_def]) >>
     rpt strip_tac >> first_assum ACCEPT_TAC) >>
  `t.vs_inst_idx + 9 = LENGTH sb.cs_current_insts` by simp[nested_pop_suffix_def] >>
  pop_assum (fn th => PURE_REWRITE_TAC [th]) >>
  irule emitted_alloca_history >>
  qpat_assum `run_inst_seq (nested_pop_suffix _ _ _ _ _ _ _ _ _ _ _) t = OK u`
    (irule_at Any) >>
  qpat_assum `fn_has_code sm sb func` (irule_at Any) >>
  Cases_on `tr` >> simp[nested_pop_suffix_def,mk_inst_def,is_terminator_def]
QED

Theorem pop_full_storage_header_taint[local]:
  stor_taint_ok_at D tn s /\
  D.d_stor = (sourceUnitExecution$cx_dead H cx).d_stor /\
  D.d_trans = (sourceUnitExecution$cx_dead H cx).d_trans /\
  s.vs_call_ctx.cc_address = cx.txn.target /\
  MEM (tr,root,rtv) (FST H) /\
  storage_subregion rtv path delta (ArrayTV etv (Dynamic n)) /\
  w2n slot = w2n root + delta ==>
  stor_taint_ok_at D
    (if tr then tn with t_trans := key_update tn.t_trans slot {}
     else tn with t_stor := key_update tn.t_stor slot {})
    (if tr then tstore slot (n2w (w2n (tload slot s) - 1)) s
     else sstore slot (n2w (w2n (sload slot s) - 1)) s)
Proof
  strip_tac >>
  `key_update (if tr then tn.t_trans else tn.t_stor) slot {} SUBSET
    {(k,b) | storage_dead H tr
      (update_storage slot
        (n2w (w2n (lookup_storage slot
          (if tr then contract_transient s else contract_storage s)) - 1))
        (if tr then contract_transient s else contract_storage s)) (w2n k) b}` by
    (pure_rewrite_tac [pred_setTheory.SUBSET_DEF] >>
     qx_gen_tac `entry` >> PairCases_on `entry` >>
     rename1 `(key,byte) IN key_update _ slot {}` >>
     simp[key_update_def] >> strip_tac >>
     irule nested_pop_storage_dead_header >>
     conj_tac >- metis_tac[] >>
     qpat_assum `stor_taint_ok_at D tn s` mp_tac >>
     qpat_assum `D.d_stor = _` mp_tac >>
     qpat_assum `D.d_trans = _` mp_tac >>
     qpat_assum `s.vs_call_ctx.cc_address = cx.txn.target` mp_tac >>
     qpat_assum `(key,byte) IN _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> Cases_on `tr` >>
     gvs[stor_taint_ok_at_def,sourceUnitExecutionTheory.cx_dead_def,
       contract_storage_def,contract_transient_def,vfmStateTheory.lookup_account_def,
       pred_setTheory.SUBSET_DEF] >| [
       qpat_assum `!x. x IN tn.t_trans ==> _`
         (qspec_then `(key,byte)` mp_tac) >>
       impl_tac >- first_assum ACCEPT_TAC >> strip_tac >> gvs[],
       qpat_assum `!x. x IN tn.t_stor ==> _`
         (qspec_then `(key,byte)` mp_tac) >>
       impl_tac >- first_assum ACCEPT_TAC >> strip_tac >> gvs[]]) >>
  Cases_on `tr` >>
  gvs[stor_taint_ok_at_def,sourceUnitExecutionTheory.cx_dead_def,sstore_def,tstore_def,
    sload_def,tload_def,contract_storage_def,contract_transient_def,
    vfmStateTheory.lookup_account_def,combinTheory.APPLY_UPDATE_THM]
QED

Resume pop_vv_full_of_target[storage_ghost]:
  `?hroot hrtv hpath hoff. MEM (tr,hroot,hrtv) (FST H) /\
    storage_subregion hrtv hpath hoff (ArrayTV etv (Dynamic n)) /\
    w2n slot = w2n hroot + hoff` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       (?root rtv path delta. _) /\ _`
      (fn fam => qpat_assum `valid_horizon cx st0 H mid.storage_trace`
        (ACCEPT_TAC o CONJUNCT1 o MP (Q.SPEC `H` fam)))) >>
  `dead_lo_ok H (DF H) lo cenv cx` by
    (qpat_assum `!H. dead_lo_ok H (DF H) lo cenv cx` (qspec_then `H` ACCEPT_TAC)) >>
  qabbrev_tac `stored = if tr then tstore slot (n2w (w2n lenw - 1)) t
    else sstore slot (n2w (w2n lenw - 1)) t` >>
  qabbrev_tac `tm = if tr then tn1 with t_trans := key_update tn1.t_trans slot {}
    else tn1 with t_stor := key_update tn1.t_stor slot {}` >>
  `stor_taint_ok_at (DF H) tm stored` by
    (simp[NoAsms,Abbr `stored`,Abbr `tm`] >>
     qpat_assum `(if tr then tload slot t else sload slot t) = _` mp_tac >>
     qpat_assum `ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t`
       (mp_tac o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
         REWRITE_RULE [ghost_inv_at_def]) >>
     qpat_assum `dead_lo_ok H (DF H) lo cenv cx` mp_tac >>
     qpat_assum `t.vs_call_ctx.cc_address = cx.txn.target` mp_tac >>
     qpat_assum `MEM (tr,hroot,hrtv) (FST H)` mp_tac >>
     qpat_assum `storage_subregion hrtv hpath hoff _` mp_tac >>
     qpat_assum `w2n slot = w2n hroot + hoff` mp_tac >>
     qpat_assum `Abbrev (lenw = _)` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     mp_tac (Q.INST [`D` |-> `DF H`,`tn` |-> `tn1`,`s` |-> `t`,
       `root` |-> `hroot`,`rtv` |-> `hrtv`,`path` |-> `hpath`,`delta` |-> `hoff`]
       (SPEC_ALL (INST_TYPE [alpha |-> ``:256``] pop_full_storage_header_taint))) >>
     impl_tac >- fs[dead_lo_ok_def] >>
     Cases_on `tr` >> gvs[Abbr `lenw`]) >>
  `ghost_inv_at (DF H) lo d cenv cx fin G1 tm stored` by
    (qpat_assum `ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` mp_tac >>
     qpat_assum `stor_taint_ok_at (DF H) tm stored` mp_tac >>
     qpat_assum `fin.scopes = mid.scopes` mp_tac >>
     qpat_assum `Abbrev (stored = _)` mp_tac >>
     qpat_assum `Abbrev (tm = _)` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> Cases_on `tr` >>
     (gvs[Abbr `stored`,Abbr `tm`,ghost_inv_at_def,sstore_def,tstore_def,
       return_buf_ptr_def,ptr_covers_def,op_taint_def,lookup_var_def,
       allocas_from_def] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac
     >- (Cases_on `d` >- simp[return_buf_ptr_def] >>
         rename1 `return_buf_ptr (SOME rb) _ _ _ _` >> PairCases_on `rb` >>
         gvs[return_buf_ptr_def,ptr_covers_def,lookup_var_def,op_taint_def] >>
         metis_tac[]) >>
     first_assum ACCEPT_TAC)) >>
  irule ghost_inv_at_exterior_frame >>
  qpat_assum `ghost_inv_at (DF H) lo d cenv cx fin G1 tm stored` (irule_at Any) >>
  qexists_tac `sa` >>
  qpat_assum `u = _ with vs_vars := u.vs_vars`
    (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
  Cases_on `tr` >> simp[Abbr `stored`,Abbr `tm`,sstore_def,tstore_def,
    lookup_var_def,op_taint_def] >>
  rpt strip_tac >>
  qpat_assum `!q. not_fresh_at sa q ==> _ /\ _ /\ _`
    (fn fam => qpat_assum `not_fresh_at sa x`
      (strip_assume_tac o MP (Q.SPEC `x` fam))) >>
  fs[lookup_var_def,op_taint_def]
QED

Resume pop_vv_full_of_target[storage_pointer]:
  `MEM (tr,n2w offset,root_tv) (FST H)` by
    (irule vyperFiniteStoragePreservationTheory.storage_observations_ok_root >>
     qexistsl_tac [`cx`,`mid.storage_trace`] >>
     simp[] >> fs[vyperStorageFootprintTheory.valid_horizon_def]) >>
  `storage_read_live H tr (if tr then contract_transient t else contract_storage t)
    slot (ArrayTV etv (Dynamic n))` by
    (irule accountsRelPropsTheory.storage_place_observed_read_live >>
     simp[vyperValueTheory.type_slot_size_def,
       vyperStoragePlaceObservedTheory.storage_place_observed_def] >>
     qexistsl_tac [`n2w offset`,`root_tv`,`path`,`delta`] >> simp[]) >>
  `(if tr then lookup_storage slot (contract_transient t)
    else lookup_storage slot (contract_storage t)) = lenw` by
    (simp[NoAsms,Abbr `lenw`] >>
     qpat_assum `(if tr then tload slot t else sload slot t) = _`
       (ACCEPT_TAC o REWRITE_RULE [sload_def,tload_def])) >>
  `storage_read_live H tr (if tr then contract_transient t else contract_storage t)
    last_slot etv` by
    (mp_tac (Q.SPECL [`H`,`tr`,
       `if tr then contract_transient t else contract_storage t`,`slot`,`etv`,`n`,
       `w2n (lenw:bytes32)-1`]
       (INST_TYPE [alpha |-> ``:256``] targetPlaceLiveTheory.nested_pop_live_dynamic_element)) >>
     impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >>
       Cases_on `tr` >> gvs[] >> decide_tac) >>
     simp[NoAsms,Abbr `last_slot`] >>
     disch_then (ACCEPT_TAC o ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM])) >>
  `w2n last_slot + type_slot_size etv <= dimword(:256) /\
    (type_slot_size etv = 0 \/ w2n slot < w2n last_slot)` by
    (mp_tac (Q.INST [`len` |-> `w2n (lenw:bytes32)`,`w` |-> `slot`,`tv` |-> `etv`]
       (SPEC_ALL exprSimPopStorageTheory.pop_array_last_bounds)) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     simp[NoAsms,Abbr `last_slot`]) >>
  `(if tr then tn1.t_trans else tn1.t_stor) SUBSET
    {(key,byte) | storage_dead H tr
      (if tr then contract_transient t else contract_storage t) (w2n key) byte}` by
    (qpat_assum `ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t`
       (mp_tac o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
         REWRITE_RULE [ghost_inv_at_def]) >>
     qpat_assum `!H. dead_lo_ok H (DF H) lo cenv cx` (mp_tac o Q.SPEC `H`) >>
     qpat_assum `t.vs_call_ctx.cc_address = cx.txn.target` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> Cases_on `tr` >>
     gvs[dead_lo_ok_def,stor_taint_ok_at_def,sourceUnitExecutionTheory.cx_dead_def,
       contract_storage_def,contract_transient_def,vfmStateTheory.lookup_account_def]) >>
  `!key byte. w2n last_slot <= w2n key /\
     w2n key < w2n last_slot + type_slot_size etv /\ byte < 32 /\
     (key,byte) IN key_update (if tr then tn1.t_trans else tn1.t_stor) slot {} ==>
     dead_bytes
       (update_storage slot (n2w (w2n lenw - 1))
         (if tr then contract_transient t else contract_storage t))
       (w2n last_slot) etv (w2n key) byte` by
    (qx_genl_tac [`key`,`byte`] >> strip_tac >>
     `(key,byte) IN (if tr then tn1.t_trans else tn1.t_stor)` by
       (qpat_assum `(key,byte) IN key_update _ _ _` mp_tac >>
        rpt (pop_assum kall_tac) >> simp[key_update_def]) >>
     `storage_dead H tr (if tr then contract_transient t else contract_storage t)
        (w2n key) byte` by
       (qpat_assum `_ SUBSET _`
          (mp_tac o Q.SPEC `(key:bytes32,byte:num)` o
            REWRITE_RULE [pred_setTheory.SUBSET_DEF]) >>
        impl_tac >- first_assum ACCEPT_TAC >> simp[NoAsms]) >>
     `dead_bytes (if tr then contract_transient t else contract_storage t)
        (w2n last_slot) etv (w2n key) byte` by
       (qpat_assum `storage_read_live H tr _ last_slot etv`
          (mp_tac o REWRITE_RULE [storage_read_live_def]) >>
        disch_then (qspecl_then [`w2n (key:bytes32)`,`byte`] mp_tac) >> simp[]) >>
     `dead_bytes
        (update_storage slot (n2w (w2n lenw - 1))
          (if tr then contract_transient t else contract_storage t))
        (w2n last_slot) etv (w2n key) byte =
      dead_bytes (if tr then contract_transient t else contract_storage t)
        (w2n last_slot) etv (w2n key) byte` by
       (irule (cj 1 accountsRelPropsTheory.dead_bytes_frame) >>
        mp_tac (Q.INST [`off` |-> `w2n (last_slot:bytes32)`,
          `sz` |-> `type_slot_size etv`,`slot` |-> `slot:bytes32`,
          `u` |-> `n2w (w2n (lenw:bytes32) - 1):bytes32`,
          `st` |-> `if tr then contract_transient t else contract_storage t`]
          (SPEC_ALL targetPlaceLiveTheory.nested_pop_lookup_frame)) >>
        impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >> decide_tac) >>
        disch_then ACCEPT_TAC) >>
     simp[]) >>
  qpat_assum `!key byte. _ ==> dead_bytes _ _ _ _ _` mp_tac >>
  qpat_assum `lookup_var x6 u = SOME last_slot` mp_tac >>
  qpat_assum `evaluate_type (get_tenv cx) ann = SOME etv` mp_tac >>
  qpat_assum `op_taint tn' (Var x6) = {}` mp_tac >>
  qpat_assum `tn'.t_stor = _` mp_tac >>
  qpat_assum `tn'.t_trans = _` mp_tac >>
  qpat_assum `u = _ with vs_vars := u.vs_vars` mp_tac >>
  qpat_assum `Abbrev (result = _)` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >> Cases_on `tr` >>
  gvs[ptr_vv_ok_def,contextTheory.mk_ptr_def,expr_type_def,post_value_type_def,
    Abbr `result`,sstore_def,tstore_def,contract_storage_def,contract_transient_def,
    vfmStateTheory.lookup_account_def,combinTheory.APPLY_UPDATE_THM,
    eval_operand_def,lookup_var_def] >>
  qpat_assum `u = _` (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
  simp[combinTheory.APPLY_UPDATE_THM] >> metis_tac[]
QED

Finalise pop_vv_full_of_target[local]

(* The target producer selects one endpoint with its place and pointer.
   The pop suffix reads and updates the dynamic length at that pointer. *)
Theorem pop_expr_full_ok:
  !cx v10 bt. body_base_target_full_ok cx bt ==> body_expr_full_ok cx (Pop v10 bt)
Proof
  rpt gen_tac >> strip_tac >>
  simp[body_expr_full_ok_def] >> rpt gen_tac >> strip_tac >>
  `target_pre cenv cx env bt es` by
    (irule pop_full_target_pre >> goal_assum (drule_at Any)) >>
  `target_place_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx env bt es` by
    (irule body_target_place_sim_full >> simp[] >>
     qexists_tac `tops` >> simp[]) >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty (Pop v10 bt) es` by
    (irule pop_vv_full_of_target >> metis_tac[]) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  irule expr_sim_full_of_vv >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> drule_all exprSimHypsTheory.expr_body_pre_copy_ok >> simp[]) >>
  qpat_assum `expr_body_pre _ _ _ (Pop _ _) _`
    (mp_tac o MATCH_MP expr_body_pre_type_evaluates) >>
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  qexists_tac `x` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env (Pop v10 bt) (es with gas_obs := gs)` by simp[] >>
  drule_all exprSimSourceTheory.expr_body_pre_runtime_typed >>
  strip_tac >> gvs[] >> metis_tac[]
QED
