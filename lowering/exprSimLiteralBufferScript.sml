(*
 * Expression simulation: bytes and string literals (#636, Leaves)
 *
 * A bytes or string literal not of a word type is lowered to a buffer of
 * its own (compile_bytelike_literal): an ALLOCA, the length word, and the
 * bytes in 32-byte chunks.  This theory proves that case of the
 * expression simulation; exprSimLeaves uses it for compile_literal_memory_sim and
 * compile_literal_case_sim.
 *
 * TOP-LEVEL:
 *   compile_literal_other_vv_sim — the buffer simulates the literal
 *                              (expr_vv_ok)
 *)

Theory exprSimLiteralBuffer
Ancestors
  list finite_map
  exprSim exprSimOps exprSimHyps exprLowering compileEnv loweringSlice
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTypeCallGraph
  vyperValueOperation valueEncoding fragExec venomState

(* Bytes and string literals not of a word type: a buffer of their own.
   compile_bytelike_literal allocates 32 + 32 * word_size (LENGTH bytes)
   bytes with an ALLOCA, stores the length at the base and the bytes,
   padded to whole words, in 32-byte chunks after it, and hands out the
   base as a pointer into memory.

   Why it holds:
   - expr_sim_pre's alloc_limits_expr bounds the buffer below 2 ** 64, so
     the ALLOCA's literal size does not wrap; stmt_state_rel's alloca_room
     keeps base + size below 2 ** 256 (stmt_state_rel_exec_alloca), so the
     ADDs of the chunk addresses do not wrap either.  The ALLOCA may run
     fresh or again (a loop body): stmt_state_rel's last conjunct says a
     recorded allocation of it has the size it asks for.
   - The ALLOCA's output is a fresh variable, no live local's pointer
     (local_ptrs_reserved), so its allocation misses every live local
     (local_ptrs_rel_alloca_disjoint) and the MSTOREs keep local_ptrs_rel
     (local_ptrs_rel_mstore).  immutable_alloca_sep additionally keeps the
     buffer off each initialized constructor immutable's full capacity
     region, even when the ALLOCA reuses an existing allocation.  The
     stores never shrink memory, so capacity-sized memory agreement keeps
     immutables_rel, including its capacity bound and byte relation.
   - The allocation's id is sa.cs_next_id, one of the expression's own, as
     vv_at asks; alloca_inv's disjointness keeps the memory of every other
     allocation, which vv_post's frame asks for those below sa.cs_next_id.
   - The value is BytesV bs at BaseTV (BytesT (Dynamic n)) or StringV str
     at BaseTV (StringT n) (well_typed_literal: LENGTH <= n), whose
     val_footprint is exactly the buffer's size; val_wf holds since
     type_memory_size is 32 + 32 * word_size n.
   - es' = es: a literal's evaluation leaves the state alone. *)
Theorem literal_padded_chunk_length[local]:
  !bs:word8 list. bs <> [] ==>
    LENGTH (TAKE 32 (bs ++ REPLICATE 31 0w)) = 32
Proof
  rpt strip_tac >> simp[LENGTH_TAKE_EQ] >> Cases_on `bs` >> gvs[]
QED

Theorem literal_padded_chunk_store[local]:
  !bs off s. bs <> [] ==>
    mem_bytes_at off 32
      (mstore off (word_of_bytes T (0w:bytes32)
        (TAKE 32 (bs ++ REPLICATE 31 0w))) s).vs_memory =
    TAKE 32 (bs ++ REPLICATE 31 0w)
Proof
  rpt strip_tac >> rewrite_tac[valueEncodingPropsTheory.mem_bytes_at_mstore_same] >>
  irule venomMemPropsTheory.word_bytes_roundtrip_256 >>
  irule literal_padded_chunk_length >> simp[]
QED

Theorem literal_chunk_prefix[local]:
  !bs off s. bs <> [] ==>
    mem_bytes_at off (MIN 32 (LENGTH bs))
      (mstore off (word_of_bytes T (0w:bytes32)
        (TAKE 32 (bs ++ REPLICATE 31 0w))) s).vs_memory = TAKE 32 bs
Proof
  rpt strip_tac >>
  drule literal_padded_chunk_store >>
  disch_then (qspecl_then [`off`, `s`] mp_tac) >>
  strip_tac >> irule LIST_EQ >> simp[LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF] >>
  qx_gen_tac `i` >> strip_tac >>
  `EL i (mem_bytes_at off 32
      (mstore off (word_of_bytes T (0w:bytes32)
        (TAKE 32 (bs ++ REPLICATE 31 0w))) s).vs_memory) =
    EL i (TAKE 32 (bs ++ REPLICATE 31 0w))` by simp[] >>
  gvs[valueEncodingProofsTheory.EL_mem_bytes_at, EL_TAKE, rich_listTheory.EL_APPEND1]
QED

Theorem literal_chunk_quotient_step[local]:
  !n q r q' r'.
    32 <= n /\ n + 31 = 32*q+r /\ n-1 = 32*q'+r' /\
    r < 32 /\ r' < 32 ==> 32*q'+32 = 32*q
Proof
  rpt strip_tac >> intLib.ARITH_TAC
QED

Theorem literal_chunk_suffix_size[local]:
  !n. 32 <= n ==> 32 + 32 * word_size (n - 32) = 32 * word_size n
Proof
  rpt strip_tac >> simp[vfmConstantsTheory.word_size_def] >>
  qspec_then `32` mp_tac arithmeticTheory.DIVISION >> simp[] >>
  disch_then (fn th => map_every (fn q => qspec_then q strip_assume_tac th)
    [`n + 31`, `n - 1`]) >>
  `(n + 31) MOD 32 < 32 /\ (n - 1) MOD 32 < 32` by simp[] >>
  metis_tac[literal_chunk_quotient_step]
QED

Theorem literal_buffer_range:
  !n b off lim. b + off + 32 * word_size n < lim ==>
    b + off + n < lim /\ (n <> 0 ==> b + off + 32 < lim)
Proof
  rpt gen_tac >> rewrite_tac[vfmConstantsTheory.word_size_def] >>
  strip_tac >>
  qspec_then `32` mp_tac arithmeticTheory.DIVISION >> simp[] >>
  disch_then (qspec_then `n + 31` strip_assume_tac) >>
  `(n + 31) MOD 32 < 32` by simp[] >>
  intLib.ARITH_TAC
QED

Theorem literal_mstore_state_rel:
  !func cenv cx es s a (w:bytes32) inst b sz.
    stmt_state_rel func cenv cx es s /\ b <= a /\ a + 32 <= b + sz /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
    (!name lb lsz. local_region cenv es.scopes s name lb lsz ==>
       b + sz <= lb \/ lb + lsz <= b) ==>
    stmt_state_rel func cenv cx es (mstore a w s)
Proof
  rpt strip_tac >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _` mp_tac >>
  rewrite_tac[Once exprLoweringPropsTheory.stmt_state_rel_def] >> strip_tac >>
  `local_ptrs_rel func cenv es.scopes (mstore a w s)` by
    (irule localPtrsPropsTheory.local_ptrs_rel_mstore >>
     reverse conj_tac >- gvs[state_rel_def] >>
     rpt strip_tac >>
     qpat_x_assum `!name lb lsz. local_region _ _ _ _ _ _ ==> _` drule >>
     decide_tac) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es
     (mstore a w s)` by
    (irule immutables_rel_mstore_alloca >> conj_tac
     >- (qexistsl_tac [`b`, `func`, `inst`, `sz`] >> simp[]) >>
     gvs[state_rel_def]) >>
  rewrite_tac[exprLoweringPropsTheory.stmt_state_rel_def] >>
  conj_tac
  >- (irule exprLoweringPropsTheory.state_rel_frame >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`es`, `s`] >> simp[] >> simp[mstore_def]) >>
  conj_tac
  >- (irule localPtrsPropsTheory.alloca_inv_fields >>
      qexists_tac `s` >> simp[mstore_def]) >>
  conj_tac
  >- (irule exprLoweringPropsTheory.alloca_room_fields >>
      qexists_tac `s` >> simp[mstore_def]) >>
  conj_tac
  >- (irule exprLoweringPropsTheory.immutable_alloca_sep_fields >>
      qexistsl_tac [`s`, `es`] >> simp[mstore_def] >>
      rpt strip_tac >> qexists_tac `id` >>
      fs[local_region_def, lookup_var_def]) >>
  simp[mstore_def] >> metis_tac[]
QED

Theorem literal_emit_mstore_run:
  !sa sb pop value s addr w.
    emit_void MSTORE [pop; value] sa = ((), sb) /\
    eval_operand pop s = SOME addr /\ eval_operand value s = SOME w ==>
    run_inst_seq (emitted_insts sa sb) s = OK (mstore (w2n addr) w s)
Proof
  rpt strip_tac >>
  drule emitHelperPropsTheory.emitted_insts_emit_void >> strip_tac >>
  `step_inst_base (mk_inst sa.cs_next_id MSTORE [pop; value] []) s =
    OK (mstore (w2n addr) w s)` by
    (irule emitHelperPropsTheory.step_MSTORE >> simp[]) >>
  simp[exprLoweringPropsTheory.run_inst_seq_def]
QED

(* ALLOCA may reuse its instruction's existing region.  In either case it
   preserves memory and all old entries, and supplies a disjoint buffer. *)
Theorem literal_alloca_run[local]:
  !func cenv cx es s inst p (n:bytes32).
    stmt_state_rel func cenv cx es s /\ fn_inst_ids_distinct func /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\ inst.inst_outputs = [p] /\
    not_local_ptr cenv es.scopes p ==>
    ?t w. exec_alloca inst s n = OK t /\
      stmt_state_rel func cenv cx es t /\ lookup_var p t = SOME w /\
      FLOOKUP t.vs_allocas inst.inst_id = SOME (w2n w, w2n n) /\
      w2n w + w2n n < dimword (:256) /\ t.vs_memory = s.vs_memory /\
      (!x. x <> p ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
         FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!aid b sz. aid <> inst.inst_id /\
         FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
         regions_disjoint (w2n w) (w2n n) b sz) /\
      (!name b sz. local_region cenv es.scopes t name b sz ==>
         regions_disjoint (w2n w) (w2n n) b sz)
Proof
  rpt strip_tac >>
  `?t. exec_alloca inst s n = OK t` by
    (Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
     >- simp[venomExecSemanticsTheory.exec_alloca_def] >>
     rename1 `FLOOKUP s.vs_allocas inst.inst_id = SOME entry` >>
     PairCases_on `entry` >> simp[venomExecSemanticsTheory.exec_alloca_def]) >>
  drule_all stmt_state_rel_exec_alloca >> strip_tac >>
  `alloca_inv t /\ local_ptrs_rel func cenv es.scopes t` by
    gvs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def] >>
  qexistsl_tac [`t`, `w`] >> simp[] >>
  conj_tac
  >- (`t.vs_alloca_next < dimword (:256)` by
        metis_tac[exprLoweringPropsTheory.alloca_room_next_lt,
                  exprLoweringPropsTheory.stmt_state_rel_def] >>
      gvs[venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >>
      first_x_assum drule >> decide_tac) >>
  `t.vs_memory = s.vs_memory /\
   (!x. x <> p ==> lookup_var x t = lookup_var x s) /\
   (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
     FLOOKUP t.vs_allocas aid = SOME entry)` by
    (qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
     Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
     >- (simp[venomExecSemanticsTheory.exec_alloca_def] >> strip_tac >>
         gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
         rpt strip_tac >> Cases_on `inst.inst_id = aid` >> gvs[]) >>
     rename1 `FLOOKUP s.vs_allocas inst.inst_id = SOME entry` >>
     PairCases_on `entry` >>
     simp[venomExecSemanticsTheory.exec_alloca_def] >> strip_tac >>
     gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      `FLOOKUP t.vs_allocas aid = SOME (b,sz)` by metis_tac[] >>
      gvs[venomMemDefsTheory.alloca_inv_def,
          venomMemDefsTheory.allocas_non_overlapping_def,
          compileEnvTheory.regions_disjoint_def] >>
      qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _` drule >>
      disch_then (qspecl_then [`b`, `sz`, `w2n w`, `w2n n`] mp_tac) >>
      simp[arithmeticTheory.ADD_COMM]) >>
  rpt strip_tac >> irule localPtrsPropsTheory.local_ptrs_rel_alloca_disjoint >>
  goal_assum drule >> simp[] >> metis_tac[]
QED

Theorem literal_alloc_buffer_run:
  !func cenv cx es sa sm buf sz s.
    compile_alloc_buffer sz sa = (buf,sm) /\
    stmt_state_rel func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ sz < dimword (:256) /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
    ?t w. run_inst_seq (emitted_insts sa sm) s = OK t /\
      stmt_state_rel func cenv cx es t /\
      eval_operand buf.buf_operand t = SOME w /\
      FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
      w2n w + sz < dimword (:256) /\ t.vs_memory = s.vs_memory /\
      sa.cs_next_id < sm.cs_next_id /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
         FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!aid b len. aid < sa.cs_next_id /\
         FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
         regions_disjoint (w2n w) sz b len) /\
      (!name b len. local_region cenv es.scopes t name b len ==>
         regions_disjoint (w2n w) sz b len) /\
      (?p. buf.buf_operand = Var p /\ not_fresh_at sm p)
Proof
  rpt strip_tac >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp[contextTheory.compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
  `not_local_ptr cenv es.scopes (STRING #"%" (toString sa.cs_next_var))` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_fresh >>
     qexists_tac `sa` >> simp[]) >>
  qmatch_asmsub_abbrev_tac `MEM inst (fn_insts func)` >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit (n2w sz)] /\
   inst.inst_outputs = [STRING #"%" (toString sa.cs_next_var)] /\
   inst.inst_id = sa.cs_next_id` by simp[Abbr `inst`, venomInstTheory.mk_inst_def] >>
  drule_all literal_alloca_run >> strip_tac >>
  gvs[Abbr `inst`, venomInstTheory.mk_inst_def,
      wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  qexistsl_tac [`t`, `w`] >>
  simp[exprLoweringPropsTheory.run_inst_seq_def,
       venomExecSemanticsTheory.step_inst_base_def,
       venomInstTheory.mk_inst_def, eval_operand_def,
       wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!aid b sz'. aid <> sa.cs_next_id /\ _ ==> _` irule >>
      qexists_tac `aid` >> simp[]) >>
  simp[not_fresh_at_def, ASCIInumbersTheory.toString_11] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem literal_chunk_nonempty_span[local]:
  !n. 0 < n ==> 32 + 32 * word_size (n - 32) = 32 * word_size n
Proof
  rpt strip_tac >> Cases_on `32 <= n`
  >- (irule literal_chunk_suffix_size >> simp[]) >>
  `n - 32 = 0` by decide_tac >>
  `word_size n = 1` by
    (simp[vfmConstantsTheory.word_size_def] >>
     irule arithmeticTheory.DIV_UNIQUE >> qexists_tac `n - 1` >> decide_tac) >>
  simp[vfmConstantsTheory.word_size_def]
QED

Theorem literal_chunk_assemble[local]:
  !a bs m.
    mem_bytes_at a (MIN 32 (LENGTH bs)) m = TAKE 32 bs /\
    mem_bytes_at (a+32) (LENGTH (DROP 32 bs)) m = DROP 32 bs ==>
    mem_bytes_at a (LENGTH bs) m = bs
Proof
  rpt strip_tac >> Cases_on `LENGTH bs < 32`
  >- gvs[arithmeticTheory.MIN_DEF, TAKE_LENGTH_TOO_LONG] >>
  `MIN 32 (LENGTH bs) = 32` by
    (simp[arithmeticTheory.MIN_DEF] >> decide_tac) >>
  `32 + (LENGTH bs - 32) = LENGTH bs` by decide_tac >>
  qspec_then `a` mp_tac valueEncodingProofsTheory.mem_bytes_at_split_padded >>
  disch_then (qspecl_then [`32`, `LENGTH bs - 32`, `m`] mp_tac) >>
  gvs[LENGTH_DROP] >> simp[TAKE_DROP]
QED

Theorem literal_chunk_head_run[local]:
  !ptr off value sa dst sm sb s w.
    emit_op ADD [ptr; Lit off] sa = (dst,sm) /\
    emit_void MSTORE [dst; Lit value] sm = ((),sb) /\
    eval_operand ptr s = SOME w ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sb.cs_next_var = sa.cs_next_var + 1 /\
    sa.cs_next_id <= sb.cs_next_id /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      t.vs_memory = (mstore (w2n (w + off)) value s).vs_memory /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def, comp_bind_def, comp_ignore_bind_def,
      fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  simp[exprLoweringPropsTheory.emitted_insts_def, exprLoweringPropsTheory.same_blocks_def, rich_listTheory.DROP_APPEND1,
       exprLoweringPropsTheory.run_inst_seq_def,
       venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_pure2_def,
       venomExecSemanticsTheory.exec_write2_def, eval_operand_def,
       venomExecSemanticsTheory.bind_outputs_def, emitHelperPropsTheory.lookup_var_update_var] >>
  conj_tac >- simp[mstore_def, update_var_def] >>
  conj_tac
  >- simp[immutableMemoryFrameTheory.immutable_mstore_capacity,
          update_var_def, arithmeticTheory.MAX_DEF] >>
  simp[mstore_def, update_var_def] >>
  rpt strip_tac >> gvs[not_fresh_at_def]
QED

Theorem literal_operand_frame:
  !op sa s t.
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!x. op = Var x ==> not_fresh_at sa x) ==>
    eval_operand op t = eval_operand op s
Proof
  rpt strip_tac >>
  `t.vs_labels = s.vs_labels` by
    (qpat_x_assum `_ with <|vs_vars := _; vs_memory := _|> = _`
       (mp_tac o AP_TERM ``\z. z.vs_labels``) >> simp[]) >>
  Cases_on `op` >> simp[eval_operand_def]
QED

Theorem literal_chunks_run[local]:
  !ptr bs off sa sb s b.
    compile_store_byte_chunks ptr bs off sa = ((),sb) /\
    (!x. ptr = Var x ==> not_fresh_at sa x) /\
    eval_operand ptr s = SOME (n2w b) /\ b < dimword (:256) /\
    b + off + 32 * word_size (LENGTH bs) < dimword (:256) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      mem_bytes_at (b+off) (LENGTH bs) t.vs_memory = bs /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= b + off \/
         b + off + 32 * word_size (LENGTH bs) <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)
Proof
  recInduct compile_store_byte_chunks_ind >> rpt gen_tac >> strip_tac
  >- gvs[compile_store_byte_chunks_def, comp_return_def,
         exprLoweringPropsTheory.emitted_insts_def,
         exprLoweringPropsTheory.same_blocks_def,
         exprLoweringPropsTheory.run_inst_seq_def,
         valueEncodingTheory.mem_bytes_at_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `compile_store_byte_chunks data_ptr (hd::tl) offset sa = ((),sb)` >>
  qpat_x_assum `compile_store_byte_chunks _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once compile_store_byte_chunks_def, LET_THM,
                   comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >> strip_tac >>
  rename1 `emit_void MSTORE [dst; Lit (word_of_bytes T 0w
    (TAKE 32 (hd::tl ++ REPLICATE 31 0w)))] mid = (u,post)` >> Cases_on `u` >>
  drule_all literal_chunk_head_run >> strip_tac >>
  `32 + 32 * word_size (LENGTH (DROP 32 (hd::tl))) =
     32 * word_size (LENGTH (hd::tl))` by
    (rewrite_tac[LENGTH_DROP] >> irule literal_chunk_nonempty_span >> simp[]) >>
  `b + (offset + 32) + 32 * word_size (LENGTH (DROP 32 (hd::tl))) < dimword (:256)` by
    (qpat_x_assum `32 + _ = _` mp_tac >>
     qpat_x_assum `b + offset + _ < _` mp_tac >>
     rpt (pop_assum kall_tac) >> decide_tac) >>
  `(!x. data_ptr = Var x ==> not_fresh_at post x)` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `eval_operand data_ptr t = SOME (n2w b)` by
    (`eval_operand data_ptr t = eval_operand data_ptr s` by
       (irule literal_operand_frame >> simp[] >> qexists_tac `sa` >> simp[]) >> simp[]) >>
  first_x_assum (qspecl_then
    [`TAKE 32 (hd::tl ++ REPLICATE 31 0w)`,
     `word_of_bytes T 0w (TAKE 32 (hd::tl ++ REPLICATE 31 0w))`] mp_tac) >>
  simp_tac bool_ss [] >> disch_then drule_all >> strip_tac >>
  suspend "compose"
QED

Resume literal_chunks_run[compose]:
  `emitted_insts sa sb = emitted_insts sa post ++ emitted_insts post sb` by
    (irule exprLoweringPropsTheory.emitted_insts_append >> simp[]) >>
  conj_tac >- simp[APPEND_ASSOC] >>
  conj_tac >- metis_tac[exprLoweringPropsTheory.same_blocks_trans] >>
  conj_tac >- decide_tac >> conj_tac >- decide_tac >>
  rename1 `run_inst_seq (emitted_insts post sb) t = OK final` >>
  qexists_tac `final` >> conj_tac
  >- (asm_rewrite_tac[] >>
      qpat_x_assum `run_inst_seq (emitted_insts sa post) s = OK t`
        (mp_tac o MATCH_MP exprLoweringPropsTheory.run_inst_seq_append) >>
      disch_then (qspec_then `emitted_insts post sb` mp_tac) >> simp[]) >>
  `b + offset + 32 < dimword (:256)` by
    (drule literal_buffer_range >> simp[] >> metis_tac[NOT_CONS_NIL]) >>
  `w2n ((n2w b:bytes32) + n2w offset) = b + offset` by
    (simp[wordsTheory.word_add_n2w, wordsTheory.w2n_n2w] >>
     irule arithmeticTheory.LESS_MOD >> decide_tac) >>
  `mem_bytes_at (b+offset) (MIN 32 (LENGTH (hd::tl))) final.vs_memory = TAKE 32 (hd::tl)` by
    (`mem_bytes_at (b+offset) (MIN 32 (LENGTH (hd::tl))) final.vs_memory =
      mem_bytes_at (b+offset) (MIN 32 (LENGTH (hd::tl))) t.vs_memory` by
      (qpat_x_assum `!a len. _ ==> mem_bytes_at _ _ final.vs_memory = _` irule >>
       disj1_tac >> rpt (pop_assum kall_tac) >>
       simp[arithmeticTheory.MIN_DEF]) >>
     asm_simp_tac bool_ss [] >> irule literal_chunk_prefix >> simp[]) >>
  conj_tac
  >- (irule literal_chunk_assemble >>
      asm_simp_tac bool_ss [GSYM arithmeticTheory.ADD_ASSOC]) >>
  conj_tac >- decide_tac >>
  conj_tac
  >- (qpat_x_assum `final with <|vs_vars := _; vs_memory := _|> = t`
       (mp_tac o AP_TERM ``\z. z with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>``) >>
      simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at post x` by
        (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
      metis_tac[]) >>
  rpt gen_tac >> disch_tac >>
  `mem_bytes_at a len final.vs_memory = mem_bytes_at a len t.vs_memory` by
    (qpat_x_assum `!a len. _ ==> mem_bytes_at _ _ final.vs_memory = _` irule >>
     qpat_x_assum `32 + _ = _` mp_tac >>
     qpat_x_assum `a + len <= _ \/ _ <= a` mp_tac >>
     rpt (pop_assum kall_tac) >> decide_tac) >>
  asm_simp_tac bool_ss [] >>
  irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
  qpat_x_assum `32 + _ = _` mp_tac >>
  qpat_x_assum `a + len <= _ \/ _ <= a` mp_tac >>
  rpt (pop_assum kall_tac) >> decide_tac
QED

Finalise literal_chunks_run

Theorem literal_state_memory_frame:
  !func cenv cx es s t.
    stmt_state_rel func cenv cx es s /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!name entry p sz. lookup_scopes name es.scopes = SOME entry /\
       FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
       lookup_var p t = lookup_var p s) /\
    (!name b sz. local_region cenv es.scopes s name b sz ==>
       mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    (cenv.ce_is_ctor ==> !name tv v off.
      FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
        SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
      mem_bytes_at off (type_memory_size tv) t.vs_memory =
        mem_bytes_at off (type_memory_size tv) s.vs_memory) ==>
    stmt_state_rel func cenv cx es t
Proof
  rpt strip_tac >>
  `t = s with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|>` by
    (qpat_x_assum `_ with <|vs_vars := _; vs_memory := _|> = _`
      (mp_tac o AP_TERM ``\z. z with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|>``) >>
     simp[]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `_ with <|vs_vars := _; vs_memory := _|> = _`
      (mp_tac o AP_TERM ``\z. (z.vs_allocas,z.vs_alloca_next)``) >> simp[]) >>
  `local_ptrs_rel func cenv es.scopes t` by
    (irule localPtrsPropsTheory.local_ptrs_rel_mem_agree >> qexists_tac `s` >>
     qpat_assum `t = _ with <|vs_vars := _; vs_memory := _|>`
       (fn th => once_rewrite_tac[th]) >>
     gvs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def,
         lookup_var_def] >> rpt conj_tac >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `alloca_inv t` by
    (irule localPtrsPropsTheory.alloca_inv_fields >> qexists_tac `s` >>
     gvs[exprLoweringPropsTheory.stmt_state_rel_def]) >>
  `alloca_room func t` by
    (irule exprLoweringPropsTheory.alloca_room_fields >> qexists_tac `s` >>
     gvs[exprLoweringPropsTheory.stmt_state_rel_def]) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es t` by
    (irule immutables_rel_mem_agree >> qexists_tac `s` >>
     qpat_assum `t = _ with <|vs_vars := _; vs_memory := _|>`
       (fn th => once_rewrite_tac[th]) >>
     gvs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def] >>
     first_assum ACCEPT_TAC) >>
  `immutable_alloca_sep func cenv cx es t` by
    (irule exprLoweringPropsTheory.immutable_alloca_sep_fields >>
     qexistsl_tac [`s`, `es`] >>
     gvs[exprLoweringPropsTheory.stmt_state_rel_def] >>
     rpt strip_tac >> qexists_tac `id` >>
     fs[local_region_def] >> metis_tac[]) >>
  rewrite_tac[exprLoweringPropsTheory.stmt_state_rel_def] >>
  conj_tac
  >- (irule exprLoweringPropsTheory.state_rel_frame >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`es`, `s`] >> simp[] >>
      qpat_assum `t = _ with <|vs_vars := _; vs_memory := _|>`
        (fn th => once_rewrite_tac[th]) >>
      gvs[exprLoweringPropsTheory.stmt_state_rel_def]) >>
  gvs[exprLoweringPropsTheory.stmt_state_rel_def] >> first_assum ACCEPT_TAC
QED

Theorem literal_buffer_prefix_shape[local]:
  !sz sa buf sm sh value.
    compile_alloc_buffer sz sa = (buf,sm) /\
    emit_void MSTORE [buf.buf_operand; Lit value] sm = ((),sh) ==>
    sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
    sh.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sh /\
    same_blocks sa sm /\ same_blocks sm sh /\
    sm.cs_next_var = sa.cs_next_var + 1 /\
    sh.cs_next_var = sm.cs_next_var /\ sm.cs_next_id <= sh.cs_next_id
Proof
  rpt strip_tac >>
  gvs[contextTheory.compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
      emitHelperTheory.emit_void_def, comp_bind_def, comp_ignore_bind_def,
      fresh_id_def, fresh_var_def, emit_def, comp_return_def,
      exprLoweringPropsTheory.emitted_insts_def,
      exprLoweringPropsTheory.same_blocks_def, rich_listTheory.DROP_APPEND1]
QED

Theorem literal_buffer_exterior[local]:
  !b pad v t u.
    (!a len. a + len <= b + 32 \/ b + 32 + pad <= a ==>
      mem_bytes_at a len u.vs_memory =
      mem_bytes_at a len (mstore b v t).vs_memory) ==>
    !a len. a + len <= b \/ b + 32 + pad <= a ==>
      mem_bytes_at a len u.vs_memory = mem_bytes_at a len t.vs_memory
Proof
  rpt gen_tac >> disch_tac >> rpt gen_tac >> disch_tac >>
  `mem_bytes_at a len u.vs_memory =
   mem_bytes_at a len (mstore b v t).vs_memory` by
    (first_x_assum irule >> decide_tac) >>
  asm_simp_tac bool_ss [] >>
  irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >> decide_tac
QED

Theorem literal_buffer_header[local]:
  !b pad v t u.
    (!a len. a + len <= b + 32 \/ b + 32 + pad <= a ==>
      mem_bytes_at a len u.vs_memory =
      mem_bytes_at a len (mstore b v t).vs_memory) ==>
    mem_word_at b u.vs_memory = v
Proof
  rpt gen_tac >> disch_tac >>
  `mem_bytes_at b 32 u.vs_memory =
   mem_bytes_at b 32 (mstore b v t).vs_memory` by
    (first_x_assum irule >> simp[]) >>
  `mem_word_at b u.vs_memory =
   mem_word_at b (mstore b v t).vs_memory` by
    gvs[valueEncodingTheory.mem_word_at_def, valueEncodingTheory.mem_bytes_at_def] >>
  simp[valueEncodingPropsTheory.mstore_mem_word_at_same]
QED

Theorem literal_buffer_reset[local]:
  !b v t u.
    u with <|vs_vars := (mstore b v t).vs_vars;
             vs_memory := (mstore b v t).vs_memory|> = mstore b v t ==>
    u with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|> = t
Proof
  rpt gen_tac >>
  disch_then (mp_tac o AP_TERM
    ``\z. z with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|>``) >>
  simp[mstore_def]
QED

Theorem literal_bytelike_run[local]:
  !func cenv cx es bs sa sb buf s.
    compile_bytelike_literal bs (LENGTH bs) sa = (buf,sb) /\
    stmt_state_rel func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    32 + 32 * word_size (LENGTH bs) < dimword (:256) /\
    MEM (mk_inst sa.cs_next_id ALLOCA
      [Lit (n2w (32 + 32 * word_size (LENGTH bs)))]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
    ?t w. run_inst_seq (emitted_insts sa sb) s = OK t /\
      stmt_state_rel func cenv cx es t /\
      eval_operand buf.buf_operand t = SOME w /\
      FLOOKUP t.vs_allocas sa.cs_next_id =
        SOME (w2n w,32 + 32 * word_size (LENGTH bs)) /\
      sa.cs_next_id < sb.cs_next_id /\
      w2n w + (32 + 32 * word_size (LENGTH bs)) < dimword (:256) /\
      mem_word_at (w2n w) t.vs_memory = n2w (LENGTH bs) /\
      mem_bytes_at (w2n w+32) (LENGTH bs) t.vs_memory = bs /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
         FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!aid b len. aid < sa.cs_next_id /\
         FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
         mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
      (!name b len. local_region cenv es.scopes s name b len ==>
         mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
      (!name b len. local_region cenv es.scopes t name b len ==>
         regions_disjoint (w2n w) (32 + 32 * word_size (LENGTH bs)) b len)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_bytelike_literal _ _ _ = _` mp_tac >>
  simp_tac (bool_ss ++ pairSimps.PAIR_ss)
    [compile_bytelike_literal_def, LET_THM, comp_bind_def, comp_ignore_bind_def,
     GSYM vfmConstantsTheory.word_size_def] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [comp_return_def] >>
  strip_tac >>
  gvs[] >>
  rename1 `compile_alloc_buffer _ sa = (buf,sm)` >>
  rename1 `emit_void MSTORE [buf.buf_operand; Lit (n2w (LENGTH bs))] sm = (u,sh)` >>
  Cases_on `u` >>
  rename1 `compile_store_byte_chunks buf.buf_operand bs 32 sh = (v,sb)` >>
  Cases_on `v` >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  `run_inst_seq (emitted_insts sm sh) t =
     OK (mstore (w2n w) (n2w (LENGTH bs)) t)` by
    (irule literal_emit_mstore_run >> simp[eval_operand_def] >>
     qexistsl_tac [`buf.buf_operand`, `Lit (n2w (LENGTH bs))`] >>
     simp[eval_operand_def]) >>
  `stmt_state_rel func cenv cx es (mstore (w2n w) (n2w (LENGTH bs)) t)` by
    (irule literal_mstore_state_rel >> simp[] >> qexistsl_tac
      [`w2n w`, `mk_inst sa.cs_next_id ALLOCA
        [Lit (n2w (32 + 32 * word_size (LENGTH bs)))]
        [STRING #"%" (toString sa.cs_next_var)]`,
       `32 + 32 * word_size (LENGTH bs)`] >>
     gvs[venomInstTheory.mk_inst_def] >>
     rpt strip_tac >>
     qpat_x_assum `!name b len. local_region _ _ _ _ _ _ ==> _` drule >>
     simp[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  suspend "chunks"
QED

Resume literal_bytelike_run[chunks]:
  drule_all literal_buffer_prefix_shape >> strip_tac >>
  `not_fresh_at sh p` by gvs[not_fresh_at_def] >>
  `eval_operand buf.buf_operand (mstore (w2n w) (n2w (LENGTH bs)) t) = SOME (n2w (w2n w))` by
    gvs[mstore_def, eval_operand_def, lookup_var_def] >>
  `w2n w + 32 + 32 * word_size (LENGTH bs) < dimword (:256)` by decide_tac >>
  `(!x. buf.buf_operand = Var x ==> not_fresh_at sh x)` by simp[] >>
  `w2n w < dimword (:256)` by simp[] >>
  drule_all literal_chunks_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sh sb) _ = OK final` >>
  drule literal_buffer_exterior >> strip_tac >>
  drule literal_buffer_header >> strip_tac >>
  drule literal_buffer_reset >> strip_tac >>
  qpat_x_assum `fn_inst_ids_distinct _` kall_tac >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` kall_tac >>
  qpat_x_assum `emit_void _ _ _ = _` kall_tac >>
  qpat_x_assum `compile_store_byte_chunks _ _ _ _ = _` kall_tac >>
  qpat_x_assum `stmt_state_rel _ _ _ _ (mstore _ _ _)` kall_tac >>
  qpat_x_assum `final with <|vs_vars := (mstore _ _ _).vs_vars; vs_memory := _|> = _` kall_tac >>
  qpat_x_assum `!a len. _ ==> _ = mem_bytes_at _ _ (mstore _ _ _).vs_memory` kall_tac >>
  qpat_x_assum `eval_operand _ (mstore _ _ _) = _` kall_tac >>
  `(!x. not_fresh_at sh x ==> lookup_var x final = lookup_var x t)` by
    (rpt strip_tac >> first_x_assum drule >> simp[mstore_def, lookup_var_def]) >>
  qpat_x_assum `!x. _ ==> _ = lookup_var _ (mstore _ _ _)` kall_tac >>
  suspend "frame"
QED

Resume literal_bytelike_run[frame]:
  `!x. not_fresh_at sa x ==> lookup_var x final = lookup_var x t` by
    (rpt strip_tac >> first_x_assum irule >> gvs[not_fresh_at_def]) >>
  `stmt_state_rel func cenv cx es final` by
    (qspecl_then [`func`, `cenv`, `cx`, `es`, `t`, `final`]
       mp_tac literal_state_memory_frame >>
     impl_tac >- (rpt conj_tac
       >- first_assum ACCEPT_TAC
       >- first_assum ACCEPT_TAC
       >- (map_every qx_gen_tac [`nm`, `ent`, `lp`, `lsz`] >> strip_tac >>
           `not_fresh_at sa lp` by
             (gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
           first_x_assum irule >> simp[])
       >- (rpt strip_tac >>
           qpat_x_assum `!a len. _ ==> mem_bytes_at _ _ final.vs_memory = _` irule >>
           qpat_x_assum `!name b len. local_region _ _ _ _ _ _ ==> _` drule >>
           simp[regions_disjoint_def] >> decide_tac)
       >- (qpat_x_assum `LENGTH (mstore _ _ _).vs_memory <= _` mp_tac >>
           simp[immutableMemoryFrameTheory.immutable_mstore_capacity,
                arithmeticTheory.MAX_DEF] >> IF_CASES_TAC >> decide_tac) >>
       rpt strip_tac >>
       `regions_disjoint off (type_memory_size tv) (w2n w)
          (32 + 32 * word_size (LENGTH bs))` by
         (qpat_x_assum `stmt_state_rel _ _ _ _ t` mp_tac >>
          simp[exprLoweringPropsTheory.stmt_state_rel_def,
               exprLoweringPropsTheory.immutable_alloca_sep_def] >>
          strip_tac >> first_x_assum drule_all >> strip_tac >>
          qpat_x_assum `!inst b sz. MEM inst _ /\ _ ==> regions_disjoint _ _ b sz` irule >>
          goal_assum (drule_at Any) >>
          simp[venomInstTheory.mk_inst_def]) >>
       qpat_x_assum `!a len. _ ==> mem_bytes_at _ _ final.vs_memory = _` irule >>
       gvs[regions_disjoint_def] >> decide_tac) >> simp[]) >>
  suspend "finish"
QED

Resume literal_bytelike_run[finish]:
  `!nm lb llen. local_region cenv es.scopes t nm lb llen ==>
     mem_bytes_at lb llen final.vs_memory = mem_bytes_at lb llen t.vs_memory` by
    (rpt strip_tac >>
     qpat_x_assum `!a len. _ ==> mem_bytes_at _ _ final.vs_memory = _` irule >>
     qpat_x_assum `!name b len. local_region _ _ _ _ _ _ ==> _` drule >>
     simp[regions_disjoint_def] >> decide_tac) >>
  `final.vs_allocas = t.vs_allocas` by
    (qpat_x_assum `final with <|vs_vars := _; vs_memory := _|> = t`
      (mp_tac o AP_TERM ``\z. z.vs_allocas``) >> simp[]) >>
  `eval_operand buf.buf_operand final = SOME w` by
    (gvs[eval_operand_def] >> metis_tac[]) >>
  `emitted_insts sa sh = emitted_insts sa sm ++ emitted_insts sm sh` by
    (irule exprLoweringPropsTheory.emitted_insts_append >> simp[]) >>
  `sh.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sh` by
    simp[APPEND_ASSOC] >>
  `emitted_insts sa sb = emitted_insts sa sh ++ emitted_insts sh sb` by
    (irule exprLoweringPropsTheory.emitted_insts_append >> simp[]) >>
  `run_inst_seq (emitted_insts sa sh) s =
     OK (mstore (w2n w) (n2w (LENGTH bs)) t)` by
    (qpat_x_assum `run_inst_seq (emitted_insts sa sm) s = OK t`
       (mp_tac o MATCH_MP exprLoweringPropsTheory.run_inst_seq_append) >>
     disch_then (qspec_then `emitted_insts sm sh` mp_tac) >> simp[]) >>
  `run_inst_seq (emitted_insts sa sb) s = OK final` by
    (qpat_x_assum `run_inst_seq (emitted_insts sa sh) s = _`
       (mp_tac o MATCH_MP exprLoweringPropsTheory.run_inst_seq_append) >>
     disch_then (qspec_then `emitted_insts sh sb` mp_tac) >> simp[]) >>
  `!name b len. local_region cenv es.scopes final name b len ==>
     regions_disjoint (w2n w) (32 + 32 * word_size (LENGTH bs)) b len` by
    (rpt strip_tac >>
     `local_region cenv es.scopes t name b len` by
       (irule exprSimOpsTheory.local_region_frame >> conj_tac
        >- (qexists_tac `func` >>
            gvs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def]) >>
        qexistsl [`sa`, `es.scopes`, `final`] >> simp[] >> metis_tac[]) >>
     qpat_x_assum `!name b len. local_region _ _ t _ _ _ ==> regions_disjoint _ _ _ _`
       drule >> pure_rewrite_tac[regions_disjoint_def] >> decide_tac) >>
  qexistsl_tac [`final`, `w`] >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `mem_bytes_at b len final.vs_memory = mem_bytes_at b len t.vs_memory` by
        (qpat_x_assum `!a len. _ ==> mem_bytes_at _ _ final.vs_memory = _` irule >>
         qpat_x_assum `!aid b len. _ ==> regions_disjoint _ _ _ _` drule_all >>
         simp[regions_disjoint_def] >> decide_tac) >>
      simp[]) >>
  reverse conj_tac
  >- (qpat_x_assum `!name b len. local_region _ _ final _ _ _ ==> regions_disjoint _ _ _ _`
        mp_tac >> pure_rewrite_tac[regions_disjoint_def] >>
      rpt strip_tac >> first_x_assum drule >> decide_tac) >>
  (* the locals' regions: the buffer's ALLOCA leaves their pointers *)
  map_every qx_gen_tac [`nm`, `lb`, `llen`] >> strip_tac >>
  `local_region cenv es.scopes t nm lb llen` by
    (irule exprSimOpsTheory.local_region_frame_fwd >>
     qexistsl [`s`, `sa`, `es.scopes`] >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Finalise literal_bytelike_run

Theorem literal_chunks_shape[local]:
  !ptr bs off sa sb.
    compile_store_byte_chunks ptr bs off sa = ((),sb) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb)
Proof
  recInduct compile_store_byte_chunks_ind >> rpt gen_tac >> strip_tac
  >- gvs[compile_store_byte_chunks_def, comp_return_def,
         exprLoweringPropsTheory.emitted_insts_def,
         exprLoweringPropsTheory.same_blocks_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `compile_store_byte_chunks data_ptr (hd::tl) offset sa = ((),sb)` >>
  qpat_x_assum `compile_store_byte_chunks _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once compile_store_byte_chunks_def, LET_THM,
                   comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >> strip_tac >>
  rename1 `emit_void MSTORE _ mid = (u,post)` >> Cases_on `u` >>
  first_x_assum (qspecl_then
    [`TAKE 32 (hd::tl ++ REPLICATE 31 0w)`,
     `word_of_bytes T 0w (TAKE 32 (hd::tl ++ REPLICATE 31 0w))`] mp_tac) >>
  simp_tac bool_ss [] >> disch_then drule >> strip_tac >>
  `post.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa post /\
   same_blocks sa post /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa post)` by
    (gvs[emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
         comp_bind_def, comp_ignore_bind_def, fresh_id_def, fresh_var_def,
         emit_def, comp_return_def] >>
     simp[exprLoweringPropsTheory.emitted_insts_def, rich_listTheory.DROP_APPEND1,
          exprLoweringPropsTheory.same_blocks_def, venomInstTheory.mk_inst_def,
          venomInstTheory.is_terminator_def]) >>
  `emitted_insts sa sb = emitted_insts sa post ++ emitted_insts post sb` by
    (irule exprLoweringPropsTheory.emitted_insts_append >> simp[]) >>
  simp[] >> metis_tac[exprLoweringPropsTheory.same_blocks_trans, APPEND_ASSOC]
QED

Theorem literal_bytelike_run_frag[local]:
  !bs ml sa buf sb ctx P Q R.
    compile_bytelike_literal bs ml sa = (buf,sb) /\
    (!s. P s ==> ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      Q (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
    frag_exec ctx sa sb P Q R
Proof
  `!ptr bs off sa sb.
    compile_store_byte_chunks ptr bs off sa = ((),sb) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb)` by metis_tac[literal_chunks_shape] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_bytelike_literal _ _ _ = _` mp_tac >>
  simp_tac (bool_ss ++ pairSimps.PAIR_ss)
    [compile_bytelike_literal_def, LET_THM, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [comp_return_def] >>
  strip_tac >> gvs[] >>
  rename1 `compile_alloc_buffer _ sa = (buf,sm)` >>
  rename1 `emit_void MSTORE _ sm = (u,sh)` >> Cases_on `u` >>
  rename1 `compile_store_byte_chunks _ _ _ sh = (v,sb)` >> Cases_on `v` >>
  qpat_x_assum `!ptr bs off sa sb. _` drule >> strip_tac >>
  `sh.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sh /\
   same_blocks sa sh /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sh)` by suspend "header_shape" >>
  `emitted_insts sa sb = emitted_insts sa sh ++ emitted_insts sh sb` by
    (irule exprLoweringPropsTheory.emitted_insts_append >> simp[]) >>
  irule fragExecTheory.frag_exec_run_inst_seq >>
  gvs[exprLoweringPropsTheory.same_blocks_def, rich_listTheory.IS_PREFIX_APPEND] >>
  metis_tac[APPEND_ASSOC]
QED

Resume literal_bytelike_run_frag[header_shape]:
  gvs[contextTheory.compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
      emitHelperTheory.emit_void_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  simp[exprLoweringPropsTheory.emitted_insts_def, rich_listTheory.DROP_APPEND1,
       exprLoweringPropsTheory.same_blocks_def, venomInstTheory.mk_inst_def,
       venomInstTheory.is_terminator_def]
QED

Finalise literal_bytelike_run_frag

Theorem literal_bytelike_alloca_mem[local]:
  !bs sa buf sb func.
    compile_bytelike_literal bs (LENGTH bs) sa = (buf,sb) /\
    fn_has_code sa sb func ==>
    MEM (mk_inst sa.cs_next_id ALLOCA
      [Lit (n2w (32 + 32 * word_size (LENGTH bs)))]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_bytelike_literal _ _ _ = _` mp_tac >>
  simp_tac (bool_ss ++ pairSimps.PAIR_ss)
    [compile_bytelike_literal_def, LET_THM, comp_bind_def, comp_ignore_bind_def,
     GSYM vfmConstantsTheory.word_size_def] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [comp_return_def] >>
  strip_tac >> gvs[] >>
  rename1 `compile_store_byte_chunks _ _ _ sh = (u,sb)` >> Cases_on `u` >>
  drule literal_chunks_shape >> strip_tac >>
  gvs[contextTheory.compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
      emitHelperTheory.emit_void_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_id_def, fresh_var_def, emit_def,
      exprLoweringPropsTheory.same_blocks_def] >>
  qpat_x_assum `compile_store_byte_chunks _ _ _ _ = _` kall_tac >>
  qpat_x_assum `EVERY _ _` kall_tac >>
  gvs[fragExecTheory.fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
  irule fragExecTheory.lookup_block_fn_insts >>
  goal_assum (drule_at Any) >> simp[MEM_APPEND]
QED

Theorem literal_memory_vv_post[local]:
  !func cenv cx e es sa sb s0 t v tvt buf w sz.
    ~is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
    val_wf tvt v /\ val_in_memory tvt v (w2n w) t.vs_memory /\
    stmt_state_rel func cenv cx es t /\
    eval_operand buf.buf_operand t = SOME w /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    sa.cs_next_id < sb.cs_next_id /\ val_footprint tvt v <= sz /\
    (!name b len. local_region cenv es.scopes t name b len ==>
       regions_disjoint (w2n w) sz b len) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s0) /\
    (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sa.cs_next_id /\
       FLOOKUP s0.vs_allocas aid = SOME (b,len) ==>
       mem_bytes_at b len t.vs_memory = mem_bytes_at b len s0.vs_memory) /\
    (!name b len. local_region cenv es.scopes s0 name b len ==>
       mem_bytes_at b len t.vs_memory = mem_bytes_at b len s0.vs_memory) ==>
    vv_post func cenv cx e es sa sb s0 es (Value v)
      (LocatedValue (expr_type e) (base_ptr buf))
      (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >>
  `locals_kept cenv es s0 t` by
    (irule locals_kept_regions >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `!name b len. local_region _ _ s0 _ _ _ ==> _` kall_tac >>
  simp[vv_post_def, exprLoweringPropsTheory.stmt_state_rel_inst_idx,
       vv_holds_def, vv_at_def, contextTheory.base_ptr_def,
       read_result_def, return_def, eval_operand_def, lookup_var_def] >>
  `eval_operand buf.buf_operand (t with vs_inst_idx := LENGTH sb.cs_current_insts) = SOME w` by
    (Cases_on `buf.buf_operand` >> gvs[eval_operand_def, lookup_var_def]) >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (qexists_tac `w` >> simp[] >> disj1_tac >>
      qexistsl_tac [`sa.cs_next_id`, `w2n w`, `sz`] >> simp[] >>
      rpt strip_tac >>
      `local_region cenv es.scopes t n lb lsz` by
        gvs[local_region_def, lookup_var_def] >>
      qpat_x_assum `!name b len. local_region _ _ _ _ _ _ ==> regions_disjoint _ _ _ _`
        drule >> simp[regions_disjoint_def] >> decide_tac) >>
  conj_tac
  >- (rpt strip_tac >> gvs[lookup_var_def]) >>
  rpt strip_tac >> first_x_assum irule >> metis_tac[]
QED

Theorem compile_literal_other_vv_sim:
  !cenv ann l.
    ((?bs. l = BytesL bs /\ ~is_word_type ann) \/ (?str. l = StringL str)) ==>
    expr_vv_ok cenv (Literal ann l)
Proof
  rpt gen_tac >> strip_tac >> rw[expr_vv_ok_def] >>
  gvs[expr_sim_pre_def, well_typed_expr_def] >>
  Cases_on `ann` >> gvs[well_typed_literal_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> gvs[well_typed_literal_def, is_word_type_def]
  >~ [`BytesT bd`] >- (Cases_on `bd` >>
    gvs[is_word_type_def, well_formed_type_def, vyperValueTheory.evaluate_type_def] >>
    rename1 `BytesT (Dynamic n)` >> suspend "bytes") >>
  rename1 `StringT n` >> suspend "string"
QED

Resume compile_literal_other_vv_sim[bytes]:
  rw[expr_vv_sim_def] >>
  gvs[compile_expr_def, compile_literal_vv_def, is_word_type_def,
      vyperASTTheory.expr_type_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  gvs[Once evaluate_def, return_def, evaluate_literal_def,
      alloc_limits_expr_def, literal_alloc_ok_def] >>
  irule literal_bytelike_run_frag >>
  first_assum (irule_at Any) >>
  rpt strip_tac >> gvs[] >>
  drule_all literal_bytelike_alloca_mem >> strip_tac >>
  `32 + 32 * word_size (LENGTH bs) < dimword (:256)` by
    (simp[wordsTheory.dimword_def] >> decide_tac) >>
  drule_all literal_bytelike_run >> strip_tac >>
  goal_assum (drule_at Any) >>
  irule (SRULE [vyperASTTheory.expr_type_def]
    (Q.INST [`e` |-> `Literal (BaseT (BytesT (Dynamic n))) (BytesL bs)`]
      (SPEC_ALL literal_memory_vv_post))) >>
  goal_assum (drule_at Any) >>
  simp[vyperASTTheory.expr_type_def, is_word_type_def,
       vyperValueTheory.evaluate_type_def] >>
  simp[val_footprint_def, valueEncodingTheory.val_wf_def,
       valueEncodingTheory.val_in_memory_def, valueEncodingTheory.type_memory_size_def] >>
  gvs[vyperValueTheory.compatible_bound_def, vfmConstantsTheory.word_size_def] >>
  qspec_then `32` mp_tac arithmeticTheory.DIVISION >> simp[] >>
  disch_then (qspec_then `n + 31` strip_assume_tac) >>
  `(n + 31) MOD 32 < 32` by simp[] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >> decide_tac
QED

Resume compile_literal_other_vv_sim[string]:
  rw[expr_vv_sim_def] >>
  gvs[compile_expr_def, compile_literal_vv_def, is_word_type_def,
      vyperASTTheory.expr_type_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  gvs[Once evaluate_def, return_def, evaluate_literal_def,
      alloc_limits_expr_def, literal_alloc_ok_def] >>
  irule literal_bytelike_run_frag >>
  first_assum (irule_at Any) >>
  rpt strip_tac >> gvs[] >>
  drule_all (SRULE []
    (Q.SPEC `MAP (n2w o ORD) str : word8 list` literal_bytelike_alloca_mem)) >> strip_tac >>
  `32 + 32 * word_size (LENGTH (MAP (n2w o ORD) str : word8 list)) < dimword (:256)` by
    (simp[wordsTheory.dimword_def] >> decide_tac) >>
  gvs[] >>
  drule (SRULE []
    (Q.INST [`bs` |-> `MAP (n2w o ORD) str : word8 list`]
      (SPEC_ALL literal_bytelike_run))) >>
  disch_then drule >> (impl_tac >- simp[]) >> strip_tac >>
  goal_assum (drule_at Any) >>
  irule (SRULE [vyperASTTheory.expr_type_def]
    (Q.INST [`e` |-> `Literal (BaseT (StringT n)) (StringL str)`]
      (SPEC_ALL literal_memory_vv_post))) >>
  goal_assum (drule_at Any) >>
  simp[vyperASTTheory.expr_type_def, is_word_type_def,
       vyperValueTheory.evaluate_type_def] >>
  simp[val_footprint_def, valueEncodingTheory.val_wf_def,
       valueEncodingTheory.val_in_memory_def, valueEncodingTheory.type_memory_size_def] >>
  gvs[well_formed_type_def, vyperValueTheory.evaluate_type_def,
      vfmConstantsTheory.word_size_def] >>
  qspec_then `32` mp_tac arithmeticTheory.DIVISION >> simp[] >>
  disch_then (qspec_then `n + 31` strip_assume_tac) >>
  `(n + 31) MOD 32 < 32` by simp[] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >> decide_tac
QED

Finalise compile_literal_other_vv_sim

(* The new shared contract and literal simulation must not depend on the
   legacy expression-correctness admissions in exprLoweringProps. *)
val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles then ()
     else raise Fail "admitted constructor-safe literal-buffer interface"
  end)
  [exprLoweringPropsTheory.immutable_alloca_sep_fields,
   exprLoweringPropsTheory.immutable_alloca_sep_cenv_cong,
   exprLoweringPropsTheory.immutable_alloca_sep_exec_alloca,
   stmt_state_rel_exec_alloca, immutables_rel_mem_agree,
   immutables_rel_mstore_alloca, compile_literal_other_vv_sim];
