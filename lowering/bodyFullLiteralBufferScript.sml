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
Ancestors
  exprSimPtrLiteralPayload exprLoweringProps list
  exprSimPtrLiteralBuffer fragGasSeqPtr instSeqPtrLo bodyPtrDefs vyperStorageFootprint
  exprLowering compileEnv loweringStateRelDefs venomState finite_map words
  exprSimLiteralBuffer ptrSafetyTransport venomExecSemantics venomInst ptrDiscipline
  context emitHelper exprLoweringProps

Theorem literal_full_ptr_transport[local]:
  compile_bytelike_literal bs (LENGTH bs) sa = (buf,sb) /\
  stmt_state_rel H ctx func cenv cx es s /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ 32+32*word_size (LENGTH bs) < dimword (:256) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  inst_seq_ptr D0 0 ctx func PG G tn (emitted_insts sa sb) s G' tn' ==>
  inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s G' tn'
Proof
  strip_tac >>
  drule_all literal_bytelike_ptr_run >>
  disch_then (qspecl_then [`tn`, `func`, `PG`, `G`, `D`] strip_assume_tac) >>
  `G' = G'' /\ tn' = tn''` by
    (irule inst_seq_ptr_ghost_unique >> metis_tac[]) >>
  gvs[] >> irule inst_seq_ptr_zero_to_lo >> simp[] >>
  qexists_tac `D` >> simp[]
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

Theorem literal_bytelike_full_run:
  !bs sa buf sb DF lo d PG ctx func cenv cx st0 es s G tn.
    compile_bytelike_literal bs (LENGTH bs) sa = (buf,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
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
      !H. valid_horizon cx st0 H es.storage_trace ==>
        inst_seq_ptr (DF H) lo ctx func PG G tn (emitted_insts sa sb) s G' tn' /\
        stmt_state_rel H ctx func cenv cx es u
Proof
  cheat
QED
