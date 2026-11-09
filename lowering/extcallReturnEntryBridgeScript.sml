(* Caller-side witnesses for allocated return decoding. *)
Theory extcallReturnEntryBridge
Ancestors
  compileEnv venomState finite_map pred_set ASCIInumbers list arithmetic
  abiReturnPrefixTransport abiValidAllocatedContract abiMalformedRecursiveInterface
  abiDecoderReentry exprSafeOperand placeMemoryStaging exprSimAlloc loweringHalt
  exprLoweringProps emitHelperProps venomInst venomExecSemantics fragGasMode words

Theorem return_decoder_ceiling_exists:
  !s en. ?ceiling. en.cs_next_var <= ceiling.cs_next_var /\
    fresh_vars_wrt ceiling s
Proof
  rpt gen_tac >>
  qabbrev_tac `bound = MAX_SET (IMAGE (\x. toNum (TL x)) (FDOM s.vs_vars))` >>
  qexists_tac `en with cs_next_var := en.cs_next_var + bound + 1` >>
  simp[fresh_vars_wrt_def] >> rpt strip_tac >>
  `n <= bound` suffices_by decide_tac >>
  qunabbrev_tac `bound` >> irule in_max_set >> simp[] >>
  qexists_tac `STRING #"%" (toString n)` >> simp[]
QED

Theorem return_decoder_operand_live:
  (!x. op = Var x ==> not_fresh_at st x) ==>
  abi_decoder_operand_live st.cs_next_var op
Proof
  Cases_on `op` >>
  simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]
QED

Theorem return_allocated_decode_ready:
  compile_alloc_buffer n sa = (buf,sm) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ n < dimword (:256) /\
  fn_has_code sa sm func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  safe_operand sa base_op /\ eval_operand base_op s = SOME (n2w B) /\
  B + cap < dimword (:256) /\
  FLOOKUP s.vs_allocas live = SOME (B,bufsz) /\ cap <= bufsz /\
  live < sa.cs_next_id /\
  mem_bytes_at B (LENGTH (TAKE cap bs)) s.vs_memory = TAKE cap bs /\
  (!aid. aid IN sites ==> sm.cs_next_id <= aid) ==>
  ?r d. gas_marked_path F ctx func s 0 (OK r) /\
    abi_return_decode_ready ctx func cenv cx es sm sites sa.cs_next_id live
      base_op buf.buf_operand B cap bs d n r /\
    (!x. not_fresh_at sa x ==> lookup_var x r = lookup_var x s) /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==>
       FLOOKUP r.vs_allocas aid = SOME e) /\
    (r with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
      vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|>) = s /\
    ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
    r.vs_inst_idx = LENGTH sm.cs_current_insts
Proof
  strip_tac >> drule_all compile_alloc_buffer_forward >> strip_tac >>
  (drule_all buffer_alloc_code >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `sa.cs_next_var <= sm.cs_next_var` by simp[] >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `safe_operand sm base_op` by metis_tac[safe_operand_mono] >>
  `eval_operand base_op r = SOME (n2w B)` by
    (Cases_on `base_op` >> gvs[safe_operand_def, eval_operand_def]) >>
  `abi_decoder_operand_live sm.cs_next_var buf.buf_operand /\
   abi_decoder_operand_live sm.cs_next_var base_op` by
    (conj_tac >> irule return_decoder_operand_live >> fs[safe_operand_def]) >>
  `abi_malformed_destination func cenv es.scopes sa.cs_next_id
     (w2n tw) n r` by
    (simp[abi_malformed_destination_def] >>
     qexistsl_tac [`mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
       [STRING #"%" (toString sa.cs_next_var)]`,
       `STRING #"%" (toString sa.cs_next_var)`] >>
     simp[mk_inst_def] >> irule local_ptrs_reserved_fresh >>
     qexists_tac `sa` >> simp[]) >>
  qexistsl_tac [`r`, `w2n tw`] >> simp[] >>
  simp[abi_return_decode_ready_def, abi_malformed_allocated_window_def] >>
  rpt conj_tac
  >- (qexists_tac `bufsz` >> simp[LENGTH_TAKE_EQ] >>
      Cases_on `cap <= LENGTH bs` >> simp[] >> decide_tac)
  >- (simp[LENGTH_TAKE_EQ] >>
      Cases_on `cap <= LENGTH bs` >> simp[] >> decide_tac)
  >- (strip_tac >> qpat_x_assum `!aid. aid IN sites ==> _` drule >> decide_tac)
  >- (strip_tac >> qpat_x_assum `!aid. aid IN sites ==> _` drule >> decide_tac)
  >- metis_tac[]
  >> gvs[]
  >> qpat_x_assum `w2n tw = _` (fn th => rewrite_tac[GSYM th, n2w_w2n]))
QED
