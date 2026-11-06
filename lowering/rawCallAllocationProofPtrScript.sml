(* Output-allocation boundaries for the counted raw_call pointer proof. *)
Theory rawCallAllocationProofPtr
Ancestors
  rawCallPrefixPtr rawCallBufferPtr builtinSystem context emitHelper compileEnv
  fragGasSeqPtr fragExecPtr typedCopyPtr exprSimAlloc exprSimPtrLiteralBuffer
  exprLoweringProps venomInst

Theorem raw_call_outbuf_steps:
  0 < cap /\ compile_raw_call_outbuf cap sa = ((ov,op),sb) ==>
  ?buf sm.
    compile_alloc_buffer (((cap + 31) DIV 32) * 32 + 32) sa = (buf,sm) /\
    ov = buf.buf_operand /\ emit_op ADD [ov; Lit 32w] sm = (op,sb)
Proof
  strip_tac >> qpat_x_assum `compile_raw_call_outbuf _ _ = _` mp_tac >>
  simp[compile_raw_call_outbuf_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[comp_bind_def, comp_return_def]) >>
  strip_tac >> gvs[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem raw_call_outbuf_zero_steps:
  compile_raw_call_outbuf 0 sa = ((ov,op),sb) ==>
  ?buf. compile_alloc_buffer 0 sa = (buf,sb) /\
    ov = buf.buf_operand /\ op = buf.buf_operand
Proof
  simp[compile_raw_call_outbuf_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem raw_call_outbuf_positive_code:
  0 < cap /\ compile_raw_call_outbuf cap sa = ((ov,op),sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++
    [mk_inst sa.cs_next_id ALLOCA
       [Lit (n2w (((cap+31) DIV 32)*32+32))]
       [STRING #"%" (toString sa.cs_next_var)];
     mk_inst (SUC sa.cs_next_id) ADD [ov; Lit 32w]
       [STRING #"%" (toString (SUC sa.cs_next_var))]] /\
  sb.cs_current_bb = sa.cs_current_bb /\ sb.cs_blocks = sa.cs_blocks
Proof
  strip_tac >> qpat_x_assum `compile_raw_call_outbuf _ _ = _` mp_tac >>
  simp[compile_raw_call_outbuf_def, compile_alloc_buffer_def,
    emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  simp[arithmeticTheory.ADD1, listTheory.APPEND_ASSOC]
QED

(* Allocation succeeds by the semantic allocation invariant at its caller;
   this boundary checks that actual successful step, not an erased run. *)
Theorem raw_call_alloca_path_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ALLOCA [Lit n] [out]) /\
  step_inst_base (mk_inst id ALLOCA [Lit n] [out]) s = OK u ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst id ALLOCA [Lit n] [out]) u)
    (step_taint (mk_inst id ALLOCA [Lit n] [out]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx func G tn
     (mk_inst id ALLOCA [Lit n] [out]) s` by simp[ptr_inst_ok_alloca] >>
  `(mk_inst id ALLOCA [Lit n] [out]).inst_opcode <> INVOKE /\
    ~is_terminator (mk_inst id ALLOCA [Lit n] [out]).inst_opcode` by
    simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def] >>
  drule_all straight_line_ptr_edge >>
  disch_then (qspec_then `PG` mp_tac) >>
  simp[venomInstTheory.mk_inst_def] >> strip_tac >>
  drule (cj 2 fragGasPathPtrTheory.gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >> simp[] >> disch_then irule >>
  irule (cj 1 fragGasPathPtrTheory.gas_path_ptr_rules) >>
  `step_inst 0 ctx (mk_inst id ALLOCA [Lit n] [out]) s = OK u` by
    simp[venomExecSemanticsTheory.step_inst_non_invoke] >>
  drule_all venomInstProofsTheory.step_preserves_halted >> simp[]
QED

Theorem raw_call_emit_alloca_path_ptr:
  compile_alloc_buffer n sa = (buf,sb) /\ fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString sa.cs_next_var)]) s = OK u ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString sa.cs_next_var)]) u)
    (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString sa.cs_next_var)]) s u tn)
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
       [STRING #"%" (toString sa.cs_next_var)]]` by
    (gvs[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
      comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def,
      comp_return_def]) >>
  drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
       [STRING #"%" (toString sa.cs_next_var)])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `LENGTH sb.cs_current_insts = SUC s.vs_inst_idx` by simp[] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  drule_all raw_call_alloca_path_ptr >> simp[]
QED

Theorem raw_call_alloc_buffer_stage:
  compile_alloc_buffer n sa = (buf,sb) /\ fn_has_code sa sb func /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ n < dimword(:256) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx ==>
  ?u b dirty.
    step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString sa.cs_next_var)]) s = OK u /\
    stmt_state_rel ctx func cenv cx es u /\ u.vs_memory = s.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid a len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
      regions_disjoint b n a len) /\
    (!name a len. local_region cenv es.scopes u name a len ==>
      regions_disjoint b n a len) /\
    b+n < dimword(:256) /\
    lookup_var (STRING #"%" (toString sa.cs_next_var)) u = SOME (n2w b) /\
    step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString sa.cs_next_var)]) u =
      G |+ (STRING #"%" (toString sa.cs_next_var),(b,n)) /\
    step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString sa.cs_next_var)]) s u tn =
      tn with <|t_var := tn.t_var |+ (STRING #"%" (toString sa.cs_next_var),{});
        t_mem := tn.t_mem UNION dirty|> /\
    dirty SUBSET {i | b <= i /\ i < b+n} /\
    gas_path_ptr D 0 ctx func PG G tn s 0
      (G |+ (STRING #"%" (toString sa.cs_next_var),(b,n)))
      (tn with <|t_var := tn.t_var |+ (STRING #"%" (toString sa.cs_next_var),{});
        t_mem := tn.t_mem UNION dirty|>)
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >> drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  `emitted_insts sa sb =
    [mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString sa.cs_next_var)]]` by
    (gvs[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
      comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def,
      comp_return_def, emitted_insts_def] >>
     simp[rich_listTheory.DROP_LENGTH_APPEND]) >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString sa.cs_next_var)]) s = OK t` by
    (gvs[run_inst_seq_def, AllCaseEqs()]) >>
  drule_all literal_ptr_alloca_ghost >>
  disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >>
  qexistsl_tac [`t`, `b`, `dirty`] >> simp[] >>
  drule_all raw_call_emit_alloca_path_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] mp_tac) >> simp[] >>
  strip_tac >> gvs[] >> metis_tac[]
QED
