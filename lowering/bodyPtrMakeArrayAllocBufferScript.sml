(* Compiler-facing counted allocation prelude for materialized buffers. *)
Theory bodyPtrMakeArrayAllocBuffer
Ancestors
  bodyPtrMakeArrayAllocationPost exprSimAlloc fragGasPathPtr exprLoweringProps
  context compileEnv emitHelperProps venomInst venomState list rich_list
  fragGasSeqAbort venomExecProps venomInstProps arithmetic venomExecSemantics

Theorem alloc_buffer_emitted:
  compile_alloc_buffer sz sa = (buf,sm) ==>
  emitted_insts sa sm =
    [mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sa.cs_next_var)]] /\
  buf.buf_operand = Var (STRING #"%" (toString sa.cs_next_var))
Proof
  simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule emitted_insts_emit_op >> simp[]
QED

Theorem literal_alloc_buffer_ptr_run:
  compile_alloc_buffer sz sa = (buf,sm) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ sz < dimword (:256) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?u w G1 tn1.
    run_inst_seq (emitted_insts sa sm) s = OK u /\
    stmt_state_rel ctx func cenv cx es u /\
    eval_operand buf.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    w2n w + sz < dimword (:256) /\ u.vs_memory = s.vs_memory /\
    sa.cs_next_id < sm.cs_next_id /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sa.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n w) sz b len) /\
    (!name b len. local_region cenv es.scopes u name b len ==>
      regions_disjoint (w2n w) sz b len) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sm p /\
      ptr_covers G1 tn1 p (u with vs_inst_idx := SUC s.vs_inst_idx) sz) /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G1 tn1
      (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> drule_all literal_alloc_buffer_run >> strip_tac >>
  drule alloc_buffer_emitted >> strip_tac >>
  qmatch_asmsub_abbrev_tac `emitted_insts sa sm = [inst]` >>
  `step_inst_base inst s = OK t` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  `get_instruction bb s.vs_inst_idx = SOME inst` by
    (irule (cj 1 instruction_prefix_cursor) >>
     qexists_tac `[]` >> gvs[]) >>
  `gas_path_ptr_edge D 0 ctx func PG G tn s 0
     (step_prov PG G inst t) (step_taint inst s t tn)
     (OK (t with vs_inst_idx := SUC s.vs_inst_idx)) /\
   ptr_covers (step_prov PG G inst t) (step_taint inst s t tn)
     (STRING #"%" (toString sa.cs_next_var))
     (t with vs_inst_idx := SUC s.vs_inst_idx) sz` by
    (simp[Abbr `inst`] >> irule literal_alloca_ptr_capacity >>
     metis_tac[]) >>
  qexistsl_tac [`t`, `w`, `step_prov PG G inst t`, `step_taint inst s t tn`] >>
  gvs[] >>
  `~t.vs_halted` by
    (`step_inst 0 ctx inst s = OK t` by
       simp[step_inst_non_invoke, Abbr `inst`, mk_inst_def] >>
     drule step_preserves_halted >>
     simp[Abbr `inst`, mk_inst_def, is_terminator_def]) >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  `gas_path_ptr D 0 ctx func PG (step_prov PG G inst t)
     (step_taint inst s t tn) (t with vs_inst_idx := SUC s.vs_inst_idx)
     0 (step_prov PG G inst t) (step_taint inst s t tn)
     (OK (t with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
  drule (cj 2 gas_path_ptr_rules) >> disch_then drule >> simp[]
QED
