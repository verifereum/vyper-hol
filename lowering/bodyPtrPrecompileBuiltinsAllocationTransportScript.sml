Theory bodyPtrPrecompileBuiltinsAllocationTransport
Ancestors bodyPtrPrecompileBuiltinsAllocationFrame bodyPtrDefs
          ptrDiscipline pred_set

Theorem allocation_clean_range:
  tn'.t_mem = tn.t_mem UNION new_site_bytes s t /\
  (!i. lo <= i /\ i < lo + len ==> i NOTIN tn.t_mem) /\
  (!i. lo <= i /\ i < lo + len ==> i NOTIN new_site_bytes s t) ==>
  (!i. lo <= i /\ i < lo + len ==> i NOTIN tn'.t_mem)
Proof
  strip_tac >> gvs[] >> metis_tac[IN_UNION]
QED

Theorem emitted_allocation_transport:
  compile_alloc_buffer n sa = (buf,sb) /\
  stmt_state_rel ctx fn cenv cx es s /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
        [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
  n < dimword (:256) /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?out G' tn'. buf.buf_operand = Var out /\ not_fresh_at sb out /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) G' tn') /\
    ptr_covers G' tn' out t n /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p)) /\
    (!p len. not_fresh_at sa p /\ ptr_covers G tn p s len ==>
      ptr_covers G' tn' p t len) /\
    tn'.t_mem = tn.t_mem UNION new_site_bytes s t /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient
Proof
  strip_tac >> drule_all emitted_allocation_frames >>
  disch_then (mp_tac o SPEC_ALL) >>
  disch_then (qx_choose_then `out` (qx_choose_then `Gf`
    (qx_choose_then `tnf` strip_assume_tac))) >>
  qexistsl [`out`, `Gf`, `tnf`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!p. not_fresh_at sa p ==> _`
    (qspec_then `p` mp_tac) >>
  simp[] >> strip_tac >> gvs[ptr_covers_def]
QED
