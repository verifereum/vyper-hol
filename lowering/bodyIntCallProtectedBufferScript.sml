(* Allocation and length-header stores retain protected runtime resources. *)
Theory bodyIntCallProtectedBuffer
Ancestors
  bodyIntCallProtectedAlloc bodyIntCallProtectedLiteral exprSimAlloc
  exprSimLiteralBuffer context emitHelperProps freshWrites
  exprLoweringProps compileEnv loweringStateRelDefs venomState venomInst valueEncodingProps
  finite_map list words intCallFrame exprSimPrecompiles

Theorem protected_alloc_header_run:
  compile_alloc_buffer sz sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; Lit value] sm = ((),sh) /\
  fn_has_code sa sm func /\ stmt_state_rel ctx func ce cx es s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  32 <= sz /\ sz < dimword (:256) /\ allocas_above lo s /\
  (!a len. P a len ==> a + len <= lo) /\
  (!op x. reserved op /\ op = Var x ==> not_fresh_at sa x) ==>
  ?t w u. run_inst_seq (emitted_insts sa sm) s = OK t /\
    run_inst_seq (emitted_insts sm sh) t = OK u /\
    u = mstore (w2n w) value t /\
    stmt_state_rel ctx func ce cx es u /\
    eval_operand buf.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    lo <= w2n w /\ w2n w + sz < dimword (:256) /\
    t.vs_memory = s.vs_memory /\
    (!a len. P a len ==>
      mem_bytes_at a len u.vs_memory = mem_bytes_at a len s.vs_memory) /\
    (!op. reserved op ==> eval_operand op u = eval_operand op s) /\
    allocas_above lo u /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sm p) /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (!name lb len. local_region ce es.scopes u name lb len ==>
       regions_disjoint (w2n w) sz lb len)
Proof
  strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  `allocas_above lo t` by (drule_all alloc_buffer_allocas_above >> simp[]) >>
  `lo <= w2n w` by (fs[allocas_above_def] >> metis_tac[]) >>
  `t.vs_labels = s.vs_labels` by (drule_all hash_alloc_buffer_labels >> simp[]) >>
  `run_inst_seq (emitted_insts sm sh) t = OK (mstore (w2n w) value t)` by
    (drule literal_emit_mstore_run >> disch_then drule >> simp[eval_operand_def]) >>
  `stmt_state_rel ctx func ce cx es (mstore (w2n w) value t)` by
    (irule literal_mstore_state_rel >> reverse conj_tac >- simp[] >>
     qexistsl_tac [`w2n w`,
       `mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
         [STRING #"%" (toString sa.cs_next_var)]`, `sz`] >>
     simp[mk_inst_def] >> rpt strip_tac >>
     fs[regions_disjoint_def] >> metis_tac[]) >>
  qexistsl_tac [`t`, `w`, `mstore (w2n w) value t`] >>
  fs[eval_operand_def] >>
  simp[mstore_def, lookup_var_def, allocas_above_def] >>
  conj_tac
  >- (rpt strip_tac >>
      `a + len <= w2n w` by metis_tac[arithmeticTheory.LESS_EQ_TRANS] >>
      `mem_bytes_at a len (mstore (w2n w) value t).vs_memory =
       mem_bytes_at a len t.vs_memory` by
        (irule mstore_mem_bytes_at_disjoint >> simp[]) >>
      gvs[mstore_def]) >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `op` >>
      gvs[eval_operand_def, mstore_def, lookup_var_def] >>
      metis_tac[lookup_var_def]) >>
  gvs[mstore_def, allocas_above_def] >>
  conj_tac >- metis_tac[] >>
  simp[local_region_def, lookup_var_def] >>
  rpt strip_tac >> first_x_assum irule >>
  simp[local_region_def, lookup_var_def] >> metis_tac[]
QED

(* A resource run confined to one allocation preserves the source relation.
   In particular, constructor immutables use allocation separation, not
   a bound by the current memory length. *)
Theorem allocated_region_state_frame:
  stmt_state_rel ctx func ce cx es s /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  (!name lb len. local_region ce es.scopes s name lb len ==>
     regions_disjoint b sz lb len) /\ local_ptrs_reserved ce sa /\
  (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  (!a len. regions_disjoint a len b sz ==>
     mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) ==>
  stmt_state_rel ctx func ce cx es t
Proof
  strip_tac >>
  irule literal_state_memory_frame >> qexists_tac `s` >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      fs[regions_disjoint_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      drule_all local_ptrs_reserved_imm_base >> simp[]) >>
  rpt strip_tac >> first_x_assum irule >>
  drule_all precompile_alloca_immutable_disjoint >>
  simp[regions_disjoint_def]
QED

Theorem allocated_literal_chunks_run:
  !ptr bs off sa sb s b sz ctx func ce cx es inst.
  compile_store_byte_chunks ptr bs off sa = ((),sb) /\
  (!x. ptr = Var x ==> not_fresh_at sa x) /\
  eval_operand ptr s = SOME (n2w b) /\ b < dimword (:256) /\
  b + off + 32 * word_size (LENGTH bs) < dimword (:256) /\
  off + 32 * word_size (LENGTH bs) <= sz /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  (!name lb len. local_region ce es.scopes s name lb len ==>
     regions_disjoint b sz lb len) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
  sa.cs_next_id <= sb.cs_next_id /\
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func ce cx es t /\
    mem_bytes_at (b+off) (LENGTH bs) t.vs_memory = bs /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!a len. a + len <= b + off \/
       b + off + 32 * word_size (LENGTH bs) <= a ==>
       mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >> drule_all literal_chunks_run >> strip_tac >> simp[] >>
  reverse conj_tac
  >- (conj_tac >- gvs[venom_state_component_equality] >>
      metis_tac[arithmeticTheory.ADD_ASSOC]) >>
  irule allocated_region_state_frame >>
  qexistsl_tac [`b`, `inst`, `s`, `sa`, `sz`] >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >> first_x_assum irule >>
  fs[regions_disjoint_def] >> decide_tac
QED
