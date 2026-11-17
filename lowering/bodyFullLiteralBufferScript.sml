(*
 * A bytes or string literal's own buffer (compile_bytelike_literal) on the
 * finite-horizon joint judgment: the ALLOCA, the length word and the
 * 32-byte chunks run once, to an endpoint fixed before the horizon, and
 * at every valid horizon H the run is a pointer-safe instruction
 * sequence at (DF H, lo), constructor frames included.
 *
 * TOP-LEVEL:
 *   literal_bytelike_full_run -- shared by the Literal leaf and the
 *     builtins that lower to a literal buffer (method_id)
 *)
Theory bodyFullLiteralBuffer
Ancestors ptrSafeRun[qualified,ignore_grammar]
  exprSimPtrLiteralPayload exprLoweringProps list
  exprSimPtrLiteralBuffer fragGasSeqPtr instSeqPtrLo bodyPtrDefs vyperStorageFootprint
  exprLowering compileEnv loweringStateRelDefs venomState finite_map words
  exprSimLiteralBuffer ptrSafetyTransport venomExecSemantics venomInst ptrDiscipline
  context emitHelper exprLoweringProps bodyFullHashKeccakFixed

Theorem literal_full_ptr_transport[local]:
  !ptr bs off sa sb D ctx0 ctx fn PG G tn s G' tn'.
  compile_store_byte_chunks ptr bs off sa = ((),sb) /\
  inst_seq_ptr D 0 ctx0 fn PG G tn (emitted_insts sa sb) s G' tn' /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G' tn'
Proof
  recInduct compile_store_byte_chunks_ind >> rpt gen_tac >> strip_tac
  >- gvs[compile_store_byte_chunks_def, comp_return_def,
         emitted_insts_def, inst_seq_ptr_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `compile_store_byte_chunks data_ptr (hd::tl) offset sa = ((),sb)` >>
  qpat_x_assum `compile_store_byte_chunks _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once compile_store_byte_chunks_def, LET_THM,
                   comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >> strip_tac >>
  rename1 `emit_void MSTORE _ mid = (u,post)` >> Cases_on `u` >>
  drule_all exprSimPtrLiteralChunksTheory.literal_chunk_head_shape >> strip_tac >>
  first_x_assum (qspecl_then
    [`TAKE 32 (hd::tl ++ REPLICATE 31 0w)`,
     `word_of_bytes T 0w (TAKE 32 (hd::tl ++ REPLICATE 31 0w))`] mp_tac) >>
  simp_tac bool_ss [] >> disch_tac >>
  drule literal_payload_chunks_shape >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa post ++ emitted_insts post sb` by
    (irule emitted_insts_append >> simp[]) >>
  gvs[] >>
  qmatch_asmsub_abbrev_tac `inst_seq_ptr _ _ _ _ _ _ _ (i1::i2::rest)` >>
  `!G tn s. ptr_inst_ok D 0 0 ctx0 fn G tn i1 s /\
     (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
     ptr_inst_ok D 0 0 ctx fn G tn i1 s` by
    simp[ptrSafeRunTheory.ptr_inst_ok_def, Abbr `i1`, mk_inst_def,
         step_inst_non_invoke] >>
  `!G tn s. ptr_inst_ok D 0 0 ctx0 fn G tn i2 s /\
     (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
     ptr_inst_ok D 0 0 ctx fn G tn i2 s` by
    simp[ptrSafeRunTheory.ptr_inst_ok_def, Abbr `i2`, mk_inst_def,
         step_inst_non_invoke] >>
  gvs[Once inst_seq_ptr_def] >>
  simp_tac bool_ss [Once inst_seq_ptr_def] >> conj_tac >- metis_tac[] >>
  Cases_on `step_inst_base i1 s` >> gvs[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp
     (v with vs_inst_idx := SUC s.vs_inst_idx)` by
    (qpat_x_assum `step_inst_base i1 s = OK v` mp_tac >>
     simp[Abbr `i1`, step_inst_base_def, mk_inst_def, exec_pure2_def,
          eval_operand_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[allocas_below_fmp_def, update_var_def] >> metis_tac[]) >>
  gvs[Once inst_seq_ptr_def] >>
  simp_tac bool_ss [Once inst_seq_ptr_def] >> conj_tac >- metis_tac[] >>
  Cases_on `step_inst_base i2 (v with vs_inst_idx := SUC s.vs_inst_idx)` >> gvs[] >>
  rename1 `step_inst_base i2 _ = OK z` >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp
     (z with vs_inst_idx := SUC (SUC s.vs_inst_idx))` by
    (qpat_x_assum `step_inst_base i2 _ = OK z` mp_tac >>
     simp[Abbr `i2`, step_inst_base_def, mk_inst_def, exec_write2_def,
          eval_operand_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[allocas_below_fmp_def, mstore_def] >> metis_tac[]) >>
  fs[Abbr `rest`] >> first_x_assum irule >> metis_tac[]
QED

(* The pointer twin is exprSimPtrLiteralBuffer's literal_bytelike_ptr_run at
   lo = 0.  What changes at lo > 0 (a constructor frame): the ALLOCA's base
   is at or above lo (ghost_inv_at's allocas_from lo / lo <= vs_alloca_next),
   so the stores stay off the immutable section below lo.  Everything but
   the pointer-safety of the run and the state relation of the post-ALLOCA
   state is horizon-free (allocation, stores, provenance and taint are
   deterministic), so those are fixed before H; storage_trace_domain gives
   one valid horizon to read the run's facts at. *)
Theorem literal_full_prefix_exists[local]:
  compile_bytelike_literal bs (LENGTH bs) sa = (buf,sb) /\
  compile_alloc_buffer (32+32*word_size (LENGTH bs)) sa = (buf,sm) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  32+32*word_size (LENGTH bs) < dimword (:256) /\
  stmt_state_rel H ctx func cenv cx es s ==>
  ?u. run_inst_seq (emitted_insts sa sm) s = OK u
Proof
  strip_tac >>
  drule_all literal_ptr_bytelike_alloca_mem >> strip_tac >>
  drule_all alloc_buffer_frame_run >> metis_tac[]
QED

Theorem literal_full_prefix_frame[local]:
  compile_bytelike_literal bs (LENGTH bs) sa = (buf,sb) /\
  compile_alloc_buffer (32+32*word_size (LENGTH bs)) sa = (buf,sm) /\
  buf.buf_operand = Var p /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  32+32*word_size (LENGTH bs) < dimword (:256) /\
  stmt_state_rel H ctx func cenv cx es s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  run_inst_seq (emitted_insts sa sm) s = OK u ==>
  stmt_state_rel H ctx func cenv cx es u /\
  step_inst_base (mk_inst sa.cs_next_id ALLOCA
    [Lit (n2w (32+32*word_size (LENGTH bs)))] [p]) s = OK u /\
  ?b. lookup_var p u = SOME (n2w b) /\
    b+32+32*word_size (LENGTH bs) < dimword (:256) /\
    u.vs_memory = s.vs_memory /\
    FLOOKUP u.vs_allocas sa.cs_next_id =
      SOME (b,32+32*word_size (LENGTH bs)) /\ lo <= b /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid a len. aid < sa.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
       regions_disjoint b (32+32*word_size (LENGTH bs)) a len) /\
    (!name a len. local_region cenv es.scopes u name a len ==>
       regions_disjoint b (32+32*word_size (LENGTH bs)) a len) /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    u.vs_labels = s.vs_labels /\ wb_frame cenv es es sa s u
Proof
  strip_tac >>
  drule_all literal_ptr_bytelike_alloca_mem >> strip_tac >>
  drule_all alloc_buffer_frame_run >> strip_tac >> gvs[] >>
  drule literal_ptr_bytelike_shape >> strip_tac >> gvs[] >>
  rename1 `run_inst_seq _ s = OK u` >>
  qmatch_asmsub_abbrev_tac `buf.buf_operand = Var p` >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA
    [Lit (n2w (32+32*word_size (LENGTH bs)))] [p]) s = OK u` by
    (qpat_x_assum `run_inst_seq _ s = OK u` mp_tac >>
     simp[run_inst_seq_def, mk_inst_def, is_terminator_def, AllCaseEqs()]) >>
  `allocas_from lo u` by
    (irule (cj 1 step_inst_allocas_from) >>
     qexistsl_tac [`ctx`, `0`, `mk_inst sa.cs_next_id ALLOCA
       [Lit (n2w (32+32*word_size (LENGTH bs)))] [p]`, `s`] >>
     simp[step_inst_non_invoke, mk_inst_def]) >>
  gvs[eval_operand_def, allocas_from_def] >> metis_tac[]
QED

(* Recover the payload frame for the actual, pinned ALLOCA endpoint. *)
Theorem literal_full_payload_frame[local]:
  compile_store_byte_chunks (Var p) bs 32 sh = ((),sb) /\
  not_fresh_at sh p /\
  emitted_insts sa sb =
    [mk_inst sa.cs_next_id ALLOCA
       [Lit (n2w (32+32*word_size (LENGTH bs)))] [p];
     mk_inst sm.cs_next_id MSTORE [Var p; Lit (n2w (LENGTH bs))] []] ++
    emitted_insts sh sb /\
  step_inst_base (mk_inst sa.cs_next_id ALLOCA
    [Lit (n2w (32+32*word_size (LENGTH bs)))] [p]) s = OK u /\
  lookup_var p u = SOME (n2w b) /\
  b+32+32*word_size (LENGTH bs) < dimword (:256) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  (t with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory|>) = u /\
  LENGTH u.vs_memory <= LENGTH t.vs_memory /\
  (!x. not_fresh_at sh x ==> lookup_var x t = lookup_var x u) /\
  (!a len. a+len <= b \/ b+32+32*word_size (LENGTH bs) <= a ==>
    mem_bytes_at a len t.vs_memory = mem_bytes_at a len u.vs_memory) /\
  mem_word_at b t.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (b+32) (LENGTH bs) t.vs_memory = bs /\
  lookup_var p t = SOME (n2w b)
Proof
  strip_tac >>
  `run_inst_seq
     (mk_inst sm.cs_next_id MSTORE [Var p; Lit (n2w (LENGTH bs))] [] ::
      emitted_insts sh sb) u = OK t` by
    (qpat_x_assum `run_inst_seq (emitted_insts sa sb) s = _` mp_tac >>
     asm_simp_tac bool_ss [APPEND, run_inst_seq_def] >> simp[]) >>
  drule_all literal_header_chunks_functional >> strip_tac >>
  metis_tac[]
QED

(* Static allocation and the literal stores preserve the conditional FMP
   bound. The domain horizon supplies the entry resource through
   stmt_state_rel; allocation room supplies the post-ALLOCA resource.
   An empty-function context can be used for lower pointer runs only:
   stmt_state_rel itself needs the actual function lookup. *)
Theorem literal_bytelike_full_run:
  !bs sa buf sb DF lo d PG ctx func cenv cx st0 es s G tn.
    compile_bytelike_literal bs (LENGTH bs) sa = (buf,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    32 + 32 * word_size (LENGTH bs) < dimword (:256) /\
    storage_trace_domain cx st0 es.storage_trace /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s /\
       ghost_inv_at (DF H) lo d cenv cx es G tn s) ==>
    ?u t b p sh G' tn'.
      buf.buf_operand = Var p /\ not_fresh_at sh p /\
      (!x. not_fresh_at sa x ==> not_fresh_at sh x) /\
      run_inst_seq (emitted_insts sa sb) s = OK t /\
      u.vs_memory = s.vs_memory /\
      FLOOKUP u.vs_allocas sa.cs_next_id =
        SOME (b, 32 + 32 * word_size (LENGTH bs)) /\
      lo <= b /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
         FLOOKUP u.vs_allocas aid = SOME entry) /\
      (!aid a len. aid < sa.cs_next_id /\
         FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
         regions_disjoint b (32 + 32 * word_size (LENGTH bs)) a len) /\
      (!name a len. local_region cenv es.scopes u name a len ==>
         regions_disjoint b (32 + 32 * word_size (LENGTH bs)) a len) /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
      u.vs_labels = s.vs_labels /\ wb_frame cenv es es sa s u /\
      (t with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory|>) = u /\
      LENGTH u.vs_memory <= LENGTH t.vs_memory /\
      (!x. not_fresh_at sh x ==> lookup_var x t = lookup_var x u) /\
      (!a len. a + len <= b \/ b + 32 + 32 * word_size (LENGTH bs) <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len u.vs_memory) /\
      FLOOKUP G' p = SOME (b, 32 + 32 * word_size (LENGTH bs)) /\
      lookup_var p t = SOME (n2w b) /\ op_taint tn' (Var p) = {} /\
      b + 32 + 32 * word_size (LENGTH bs) < dimword (:256) /\
      mem_word_at b t.vs_memory = n2w (LENGTH bs) /\
      mem_bytes_at (b + 32) (LENGTH bs) t.vs_memory = bs /\
      tn'.t_mem =
        tn.t_mem DIFF {i | b <= i /\ i < b + 32 + 32 * word_size (LENGTH bs)} /\
      tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
      tn'.t_imm = tn.t_imm /\
      (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
         FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x) /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      !H. valid_horizon cx st0 H es.storage_trace ==>
        inst_seq_ptr (DF H) lo ctx func PG G tn (emitted_insts sa sb) s G' tn' /\
        stmt_state_rel H ctx func cenv cx es u
Proof
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace)
     es.storage_trace` by gvs[storage_trace_domain_def] >>
  first_assum (drule_then strip_assume_tac) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by
    gvs[ghost_inv_at_def] >>
  drule literal_ptr_bytelike_shape >> strip_tac >>
  drule_all literal_ptr_bytelike_alloca_mem >> strip_tac >>
  drule_all literal_bytelike_run >> strip_tac >>
  `?u. run_inst_seq (emitted_insts sa sm) s = OK u` by
    (irule (INST_TYPE [alpha |-> ``:256``] literal_full_prefix_exists) >>
     asm_simp_tac (bool_ss ++ SFY_ss) []) >>
  pop_assum strip_assume_tac >>
  drule_all literal_full_prefix_frame >> strip_tac >>
  drule_all literal_full_payload_frame >> strip_tac >>
  `MEM (mk_inst sa.cs_next_id ALLOCA
     [Lit (n2w (32+32*word_size (LENGTH bs)))] [p]) (fn_insts func)` by metis_tac[] >>
  drule_all literal_ptr_alloca_ghost >>
  disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >>
  suspend "payload"
QED

Resume literal_bytelike_full_run[payload]:
  `b' = b` by metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ] >>
  qpat_x_assum `p = STRING _ _` kall_tac >>
  gvs[] >>
  qabbrev_tac `Ga = G |+ (p,(b,32+32*word_size (LENGTH bs)))` >>
  qabbrev_tac `ta = tn with <|t_var := tn.t_var |+ (p,{}); t_mem := tn.t_mem UNION dirty|>` >>
  qabbrev_tac `uh = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `ctx0 = ctx with ctx_functions := []` >>
  `lookup_var p uh = SOME (n2w b) /\
   FLOOKUP Ga p = SOME (b,32+32*word_size (LENGTH bs)) /\
   op_taint ta (Var p) = {}` by
    (simp[Abbr `uh`, Abbr `Ga`, Abbr `ta`, lookup_var_def, op_taint_def, FLOOKUP_UPDATE] >>
     metis_tac[lookup_var_def]) >>
  `~ctx_has_dalloca ctx0` by simp[Abbr `ctx0`, ctx_has_dalloca_def] >>
  `?t G' tn'.
    run_inst_seq (mk_inst sm.cs_next_id MSTORE [Var p; Lit (n2w (LENGTH bs))] [] ::
      emitted_insts sh sb) uh = OK t /\
    inst_seq_ptr (DF (storage_trace_horizon es.storage_trace)) 0 ctx0 func PG Ga ta
      (mk_inst sm.cs_next_id MSTORE [Var p; Lit (n2w (LENGTH bs))] [] ::
       emitted_insts sh sb) uh G' tn' /\
    tn'.t_mem = ta.t_mem DIFF {i | b <= i /\ i < b+32+32*word_size (LENGTH bs)} /\
    tn'.t_stor = ta.t_stor /\ tn'.t_trans = ta.t_trans /\ tn'.t_imm = ta.t_imm /\
    (!v. not_fresh_at sh v ==> FLOOKUP G' v = FLOOKUP Ga v /\
      FLOOKUP tn'.t_var v = FLOOKUP ta.t_var v)` by
    (irule literal_header_chunks_ptr >> simp[] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  suspend "assemble"
QED

Resume literal_bytelike_full_run[assemble]:
  `FLOOKUP G' p = SOME (b,32+32*word_size (LENGTH bs)) /\
   op_taint tn' (Var p) = {}` by
    (qpat_x_assum `!v. not_fresh_at sh v ==> _` (qspec_then `p` mp_tac) >>
     simp[Abbr `Ga`, Abbr `ta`, FLOOKUP_UPDATE, op_taint_def]) >>
  `tn'.t_mem = tn.t_mem DIFF {i | b <= i /\ i < b+32+32*word_size (LENGTH bs)}` by
    (simp[Abbr `ta`] >> qpat_x_assum `dirty SUBSET _` mp_tac >> SET_TAC[]) >>
  `!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
    FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x` by
    (rpt strip_tac >> `x <> p` by metis_tac[] >>
     `not_fresh_at sh x` by metis_tac[] >>
     qpat_x_assum `!v. not_fresh_at sh v ==> _` drule >>
     simp[Abbr `Ga`, Abbr `ta`, FLOOKUP_UPDATE]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _ t` (mp_tac o MATCH_MP stmt_state_rel_allocas_below_fmp) >> simp[]) >>
  qexistsl_tac [`u`, `b`, `sh`, `G'`, `tn'`] >>
  simp[Abbr `ta`] >>
  ntac 3 (conj_tac >- (first_assum ACCEPT_TAC)) >>
  suspend "horizon"
QED

Resume literal_bytelike_full_run[horizon]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` drule >> strip_tac >>
  `32 + 32 * word_size (LENGTH bs) < dimword (:256)` by decide_tac >>
  reverse conj_tac
  >- (irule (cj 1 literal_full_prefix_frame) >> simp[] >>
      goal_assum (drule_at (Pat `compile_bytelike_literal _ _ _ = _`)) >>
      goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `allocas_from _ _`)) >>
      simp[SF SFY_ss]) >>
  qabbrev_tac `ta = tn with <|t_var := tn.t_var |+ (p,{}); t_mem := tn.t_mem UNION dirty|>` >>
  `?z g tt. run_inst_seq
    (mk_inst sm.cs_next_id MSTORE [Var p; Lit (n2w (LENGTH bs))] [] :: emitted_insts sh sb) uh = OK z /\
    inst_seq_ptr (DF H) 0 ctx0 func PG Ga ta
    (mk_inst sm.cs_next_id MSTORE [Var p; Lit (n2w (LENGTH bs))] [] :: emitted_insts sh sb) uh g tt /\
    tt.t_mem = ta.t_mem DIFF {i | b <= i /\ i < b+32+32*word_size (LENGTH bs)} /\
    tt.t_stor = ta.t_stor /\ tt.t_trans = ta.t_trans /\ tt.t_imm = ta.t_imm /\
    (!v. not_fresh_at sh v ==> FLOOKUP g v = FLOOKUP Ga v /\
      FLOOKUP tt.t_var v = FLOOKUP ta.t_var v)` by
    (irule literal_header_chunks_ptr >> simp[] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  `g = G' /\ tt = tn'` by
    (irule inst_seq_ptr_ghost_unique >> metis_tac[]) >>
  qpat_x_assum `g = G'` SUBST_ALL_TAC >>
  qpat_x_assum `tt = tn'` SUBST_ALL_TAC >>
  suspend "restore"
QED

Resume literal_bytelike_full_run[restore]:
  `ctx_has_dalloca ctx ==> allocas_below_fmp uh` by
    (simp[Abbr `uh`, allocas_below_fmp_def] >>
     metis_tac[stmt_state_rel_allocas_below_fmp, allocas_below_fmp_def]) >>
  `inst_seq_ptr (DF H) 0 ctx func PG Ga ta
    (mk_inst sm.cs_next_id MSTORE [Var p; Lit (n2w (LENGTH bs))] [] ::
      emitted_insts sh sb) uh G' tn'` by
    suspend "restore_payload" >>
  suspend "prepend"
QED

Resume literal_bytelike_full_run[restore_payload]:
  qpat_x_assum `inst_seq_ptr (DF H) _ ctx0 _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [Once inst_seq_ptr_def] >> strip_tac >>
  simp_tac bool_ss [Once inst_seq_ptr_def] >> conj_tac
  >- (simp[ptrSafeRunTheory.ptr_inst_ok_def, mk_inst_def, step_inst_non_invoke] >>
      (bossLib.gvs [ptrSafeRunTheory.ptr_inst_ok_def , venomInstTheory.mk_inst_def , venomExecSemanticsTheory.step_inst_non_invoke])) >>
  qpat_x_assum `case step_inst_base _ _ of OK _ => _ | _ => _` mp_tac >>
  Cases_on `step_inst_base (mk_inst sm.cs_next_id MSTORE
    [Var p; Lit (n2w (LENGTH bs))] []) uh` >> simp[] >> strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp
    (v with vs_inst_idx := SUC uh.vs_inst_idx)` by
    (qpat_x_assum `step_inst_base _ uh = OK v` mp_tac >>
     simp[step_inst_base_def, mk_inst_def, exec_write2_def,
          eval_operand_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[allocas_below_fmp_def, mstore_def] >> metis_tac[]) >>
  irule literal_full_ptr_transport >> metis_tac[]
QED

Resume literal_bytelike_full_run[prepend]:
  qmatch_goalsub_abbrev_tac `ia::rest` >>
  `ptr_inst_ok (DF H) 0 0 ctx func G tn ia s` by
    suspend "alloca" >>
  `inst_seq_ptr (DF H) 0 ctx func PG G tn (ia::rest) s G' tn'` by
    (simp_tac bool_ss [Once inst_seq_ptr_def] >> conj_tac >- simp[] >>
     simp[Abbr `ia`] >>
     gvs[Abbr `rest`, Abbr `Ga`, Abbr `ta`, Abbr `uh`]) >>
  irule inst_seq_ptr_zero_to_lo >>
  simp[] >> qexists_tac `DF H` >> simp[]
QED

Resume literal_bytelike_full_run[alloca]:
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    metis_tac[stmt_state_rel_allocas_below_fmp] >>
  qpat_x_assum `step_inst_base ia s = OK u` mp_tac >>
  qpat_x_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
  simp[Abbr `ia`] >> POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
  simp[ptrSafeRunTheory.ptr_inst_ok_def, access_ok_def, taint_ok_def,
    mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
    contextCodegenRelTheory.source_memory_read_ranges_def,
    allocas_from_def, op_taint_def, step_inst_non_invoke] >>
  simp[step_inst_base_opcode_eqs, exec_alloca_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base _ s = OK u` mp_tac >>
  simp[mk_inst_def] >>
  simp[step_inst_base_opcode_eqs, exec_alloca_def, AllCaseEqs()] >>
  strip_tac >> gvs[update_var_def]
QED

Finalise literal_bytelike_full_run
