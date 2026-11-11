Theory bodyPtrIfExpRuntimeFrame
Ancestors immutableCopyExecution abiDecodeStaticProps venomMemProps
  exprSimCopy exprSimStorageCopy valueEncodingProps venomState words arithmetic
  compileEnv loweringStateRelDefs finite_map bodyPtrIfExpAllocSource exprLoweringProps loweringHalt

Theorem ifexp_runtime_transfers_exterior:
  !n off s.
  w2n d+off+32*n < dimword (:256) ==>
  !b len. b+len <= w2n d+off \/ w2n d+off+32*n <= b ==>
    mem_bytes_at b len (immutable_transfers F F a d n off s).vs_memory =
    mem_bytes_at b len s.vs_memory
Proof
  Induct >- simp[immutable_transfers_def] >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  simp[Once immutable_transfers_def] >>
  `w2n d+(off+32)+32*n < dimword (:256)` by
    (fs[MULT_SUC] >> decide_tac) >>
  `b+len <= w2n d+(off+32) \/ w2n d+(off+32)+32*n <= b` by
    (fs[MULT_SUC] >> decide_tac) >>
  simp[immutable_word_transfer_fields] >>
  `w2n (d+n2w off) = w2n d+off` by
    (`off < dimword (:256) /\ w2n d+off < dimword (:256)` by decide_tac >>
     irule w2n_add_n2w_lt >> simp[]) >>
  simp[] >> irule mstore_mem_bytes_at_disjoint >>
  fs[MULT_SUC] >> decide_tac
QED

Theorem ifexp_runtime_frame_fields:
  copy_runtime_frame ca q cb (t with vs_inst_idx := q.vs_inst_idx) ==>
  t.vs_allocas = q.vs_allocas /\ t.vs_accounts = q.vs_accounts /\
  t.vs_call_ctx = q.vs_call_ctx /\ t.vs_transient = q.vs_transient /\
  t.vs_data_section = q.vs_data_section /\
  (!x. not_fresh_at ca x ==> lookup_var x t = lookup_var x q)
Proof
  simp[copy_runtime_frame_def] >> strip_tac >>
  qpat_x_assum `copy_static _ = copy_static _` mp_tac >>
  simp[copy_static_def, venom_state_component_equality] >>
  strip_tac >> fs[lookup_var_def]
QED

Theorem ifexp_runtime_frame_static:
  copy_runtime_frame ca q cb (t with vs_inst_idx := q.vs_inst_idx) ==>
  copy_static t = copy_static q /\
  (!x. not_fresh_at ca x ==> lookup_var x t = lookup_var x q)
Proof
  simp[copy_runtime_frame_def, copy_static_def, lookup_var_def] >>
  strip_tac >> simp[]
QED

Theorem ifexp_runtime_allocation_frame:
  stmt_state_rel ctx fn ce cx ee s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce sb /\
  compile_alloc_buffer (32*n) sb = (buf,cs) /\ fn_has_code sb cs fn /\
  buf.buf_operand = Var out /\ 32*n < dimword (:256) /\
  step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w (32*n))] [out]) s = OK u /\
  copy_runtime_frame cs (u with vs_inst_idx := SUC s.vs_inst_idx) sd
    (t with vs_inst_idx := (u with vs_inst_idx := SUC s.vs_inst_idx).vs_inst_idx) /\
  t.vs_memory = (immutable_transfers F F a d n 0
    (u with vs_inst_idx := SUC s.vs_inst_idx)).vs_memory /\ 
  w2n d+32*n < dimword (:256) ==>
  (!x. not_fresh_at sb x ==> lookup_var x t = lookup_var x s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP t.vs_allocas aid = SOME entry) /\
  (!b len. b+len <= w2n d \/ w2n d+32*n <= b ==>
    mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
  t.vs_accounts = s.vs_accounts /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_transient = s.vs_transient
Proof
  strip_tac >> drule_all compile_alloc_buffer_raw_resources >> strip_tac >>
  drule_all alloca_step_contracts >> strip_tac >>
  drule_all ifexp_runtime_frame_fields >> strip_tac >>
  `sb.cs_next_var <= cs.cs_next_var` by
    (drule compile_alloc_buffer_parts >> strip_tac >> decide_tac) >>
  `!x. not_fresh_at sb x ==> not_fresh_at cs x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum drule >> decide_tac) >>
  conj_tac >- (gvs[lookup_var_def] >> metis_tac[]) >>
  conj_tac >- gvs[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `mem_bytes_at b len (immutable_transfers F F a d n 0
         (u with vs_inst_idx := SUC s.vs_inst_idx)).vs_memory =
       mem_bytes_at b len (u with vs_inst_idx := SUC s.vs_inst_idx).vs_memory` by
        (irule ifexp_runtime_transfers_exterior >> simp[]) >> gvs[]) >>
  gvs[]
QED

Theorem ifexp_runtime_transfers_length:
  !n off s. LENGTH s.vs_memory <=
    LENGTH (immutable_transfers F F a d n off s).vs_memory
Proof
  Induct >- simp[immutable_transfers_def] >> rpt gen_tac >>
  simp[Once immutable_transfers_def] >>
  first_x_assum (qspecl_then [`off+32`, `immutable_word_transfer F F a d off s`] mp_tac) >>
  simp[immutable_word_transfer_fields, LENGTH_mstore_eq]
QED
