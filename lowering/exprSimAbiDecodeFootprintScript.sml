Theory exprSimAbiDecodeFootprint
Ancestors
  exprSimHash exprSimAlloc exprSimProps actualDecoderSites
  loweringPosts exprLoweringProps valueEncoding vyperValue words

Theorem abi_decode_bytes_footprint:
  stmt_state_rel ctx fn ce cx es s /\
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (BytesT (Dynamic n))) /\
  ~is_word_type ty /\
  expr_val_rel cx ty (BytesV bs) op s /\
  expr_val_at ce cx ty sa sb es (BytesV bs) op s ==>
  ?p. eval_operand op s = SOME (n2w p) /\
      val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) p s.vs_memory /\
      p + 32 + LENGTH bs < dimword (:256) /\
      ((?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
          sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
          b <= p /\ p + 32 + LENGTH bs <= b + sz /\
          (!name lb lsz. local_region ce es.scopes s name lb lsz ==>
                        b + sz <= lb \/ lb + lsz <= b)) \/
       (?name b sz. local_region ce es.scopes s name b sz /\
          b <= p /\ p + 32 + LENGTH bs <= b + sz /\
          local_val_at ce cx name (p-b) (BaseTV (BytesT (Dynamic n))) (BytesV bs)))
Proof
  strip_tac >>
  gvs[expr_val_rel_def] >>
  qexists `w2n w` >> simp[] >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def, val_footprint_def] >> strip_tac >>
  `w2n w + (32 + LENGTH bs) < dimword (:256)` by
    (irule hash_live_footprint_bound >>
     goal_assum (drule_at Any) >>
     metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]) >>
  simp[] >> metis_tac[]
QED

Theorem abi_decode_bytes_post_footprint:
  expr_post ctx fn ce cx e es0 sa sb s0 es (BytesV bs) op s /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic n))) /\
  ~is_word_type (expr_type e) ==>
  ?p. eval_operand op s = SOME (n2w p) /\
      val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) p s.vs_memory /\
      p + 32 + LENGTH bs < dimword (:256) /\
      ((?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
          sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
          b <= p /\ p + 32 + LENGTH bs <= b + sz /\
          (!name lb lsz. local_region ce es.scopes s name lb lsz ==>
                        b + sz <= lb \/ lb + lsz <= b)) \/
       (?name b sz. local_region ce es.scopes s name b sz /\
          b <= p /\ p + 32 + LENGTH bs <= b + sz /\
          local_val_at ce cx name (p-b) (BaseTV (BytesT (Dynamic n))) (BytesV bs)))
Proof
  strip_tac >> irule abi_decode_bytes_footprint >>
  gvs[expr_post_def] >> metis_tac[]
QED

Theorem abi_decode_bytes_alloc_buffer_setup:
  stmt_state_rel ctx fn ce cx es s /\
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (BytesT (Dynamic n))) /\
  ~is_word_type ty /\
  expr_val_rel cx ty (BytesV bs) op s /\
  expr_val_at ce cx ty sa sb es (BytesV bs) op s /\
  compile_alloc_buffer sz sc = (buf,sd) /\
  sb.cs_next_id <= sc.cs_next_id /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce sc /\ sz < dimword (:256) /\
  MEM (mk_inst sc.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sc.cs_next_var)]) (fn_insts fn) ==>
  ?p t w.
    eval_operand op s = SOME (n2w p) /\
    val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) p s.vs_memory /\
    p + 32 + LENGTH bs < dimword (:256) /\
    run_inst_seq (emitted_insts sc sd) s = OK t /\
    stmt_state_rel ctx fn ce cx es t /\ decode_site_resources ctx fn t /\
    eval_operand buf.buf_operand t = SOME w /\
    FLOOKUP t.vs_allocas sc.cs_next_id = SOME (w2n w,sz) /\
    w2n w + sz < dimword (:256) /\ t.vs_memory = s.vs_memory /\
    val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) p t.vs_memory /\
    (sz = 0 \/ p + 32 + LENGTH bs <= w2n w \/ w2n w + sz <= p) /\
    sc.cs_next_id < sd.cs_next_id /\
    (!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry)
Proof
  strip_tac >>
  drule_all abi_decode_bytes_footprint >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  qexistsl_tac [`p`, `t`, `w`] >>
  simp[] >>
  (conj_tac >- metis_tac[stmt_state_rel_decode_site_resources])
  >- (`aid < sc.cs_next_id` by decide_tac >>
      `regions_disjoint (w2n w) sz b sz'` by metis_tac[] >>
      gvs[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  `local_region ce es.scopes t name b sz'` by
    (irule local_region_frame_fwd >>
     goal_assum (drule_at Any) >>
     qexists_tac `sc` >> simp[]) >>
  `regions_disjoint (w2n w) sz b sz'` by metis_tac[] >>
  gvs[compileEnvTheory.regions_disjoint_def] >> decide_tac
QED
