(* Caller-side witnesses for allocated return decoding. *)
Theory extcallReturnEntryBridge
Ancestors
  compileEnv venomState finite_map pred_set ASCIInumbers list arithmetic
  abiReturnPrefixTransport abiValidAllocatedContract abiMalformedRecursiveInterface
  abiDecoderReentry exprSafeOperand placeMemoryStaging exprSimAlloc loweringHalt
  exprLoweringProps emitHelperProps venomInst venomExecSemantics fragGasMode words
  abiReturnSize varsExt freshWrites builtinSimple rich_list exprLowering emitHelper
  appendStorageStageTransportPtr

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

Theorem return_size_vars_ext_ops[local]:
  compile_return_value_decode lo cap a = (hi,b) ==>
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
    ~is_ext_call_op i.inst_opcode) (emitted_insts a b)
Proof
  simp[compile_return_value_decode_def, compile_select_def,
       comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  gvs[emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pure_rewrite_tac[emitted_insts_def] >>
  simp_tac (srw_ss()) [] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, APPEND] >>
  simp[mk_inst_def, is_terminator_def, is_ext_call_op_def]
QED

Theorem return_size_actual_run:
  compile_return_value_decode lo cap a = (hi,b) /\
  lo < dimword (:256) /\ cap < dimword (:256) /\
  LENGTH s.vs_returndata < dimword (:256) ==>
  (if LENGTH s.vs_returndata < lo then
     ?u. run_inst_seq (emitted_insts a b) s = Abort Revert_abort u
   else
     ?u. run_inst_seq (emitted_insts a b) s = OK u /\
       eval_operand hi u = SOME (n2w (MIN (LENGTH s.vs_returndata) cap)) /\
       u = s with vs_vars := u.vs_vars /\
       (!x. not_fresh_at a x ==> lookup_var x u = lookup_var x s))
Proof
  strip_tac >>
  `fresh_vars_wrt a (drop_fresh a s)` by simp[fresh_vars_wrt_drop_fresh] >>
  `LENGTH (drop_fresh a s).vs_returndata < dimword (:256)` by
    simp[drop_fresh_def] >>
  drule_all abi_return_size_run >>
  simp[drop_fresh_def] >>
  Cases_on `LENGTH s.vs_returndata < lo` >> simp[] >> strip_tac >>
  `vars_ext (drop_fresh a s) s` by simp[vars_ext_drop_fresh] >>
  drule return_size_vars_ext_ops >> strip_tac >>
  drule_all run_inst_seq_vars_ext >>
  simp[drop_fresh_def, vars_ext_result_def] >> strip_tac
  >- metis_tac[] >>
  qexists_tac `t'` >> simp[] >>
  conj_tac >- (gvs[] >> drule_all vars_ext_eval_operand >> simp[]) >>
  conj_tac >- (irule abi_return_size_frame >> goal_assum (drule_at Any) >>
    goal_assum (drule_at Any)) >>
  rpt strip_tac >> irule abi_return_size_reserved >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`cap`, `hi`, `lo`] >> simp[]
QED
