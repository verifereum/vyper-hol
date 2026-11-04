(* Registered cursor phases, supporting fresh and preallocated sites. *)
Theory abiEncoderWindowCursor
Ancestors
  abiEncoderWindowSequence abiEncoderWindowLeaves valueEncodingProps
  abiEncoderWindowContract abiEncoderPrimitiveEffect
  abiEncoderRegisteredEffect emitHelperProps exprLoweringProps
  emitHelper compileEnv fragExec freshWrites venomState venomExecSemantics
  venomMemDefs venomInst words finite_map list arithmetic

Theorem window_emit_alloca32_sequence:
  emit_op ALLOCA [Lit 32w] st = (out,st') /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  alloca_room ctx func s /\ alloca_inv s /\
  (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = 32) ==>
  ?t b. window_seq st st' s t /\
    eval_operand out t = SOME (n2w b) /\
    (!x. out = Var x ==> not_fresh_at st' x) /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (b,32) /\
    b+32 <= t.vs_alloca_next /\
    alloca_room ctx func t /\ alloca_inv t /\ window_alloca_growth s t /\
    abi_encoder_registered_effect {st.cs_next_id} [] s t /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_halted = s.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = s.vs_inst_idx
Proof
  strip_tac >>
  qpat_assum `MEM _ (fn_insts func)`
    (assume_tac o REWRITE_RULE [mk_inst_def]) >>
  `?t b. exec_alloca (mk_inst st.cs_next_id ALLOCA [Lit 32w]
      [STRING #"%" (toString st.cs_next_var)]) s (32w:bytes32) = OK t /\
    alloca_room ctx func t /\ alloca_inv t /\
    lookup_var (STRING #"%" (toString st.cs_next_var)) t = SOME (n2w b) /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (b,32) /\
    b+32 <= t.vs_alloca_next /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ window_alloca_growth s t /\
    abi_encoder_registered_effect {st.cs_next_id} [] s t` by
    (drule_at (Pos hd) window_alloca_site32_execute >>
     disch_then drule >>
     disch_then (qspecl_then [`STRING #"%" (toString st.cs_next_var)`,
       `mk_inst st.cs_next_id ALLOCA [Lit 32w] [STRING #"%" (toString st.cs_next_var)]`] mp_tac) >>
     simp_tac (srw_ss()) [mk_inst_def] >>
     asm_rewrite_tac[] >> strip_tac >> qexistsl_tac [`t`, `b`] >> asm_rewrite_tac[]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule inst_extends_emit_op >> strip_tac >>
  `st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb` by
    (qpat_assum `emit_op _ _ _ = _` mp_tac >>
     simp_tac (srw_ss()) [emit_op_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
     disch_then (SUBST1_TAC o GSYM o CONJUNCT2) >> simp[]) >>
  `run_inst_seq (emitted_insts st st') s = OK t` by
    (asm_rewrite_tac[run_inst_seq_def] >>
     simp_tac (srw_ss()) [Once step_inst_base_def, mk_inst_def,
       exec_read1_def, eval_operands_def, eval_operand_def] >>
     qpat_x_assum `exec_alloca _ _ _ = OK t` mp_tac >>
     simp_tac (srw_ss()) [mk_inst_def] >> strip_tac >> asm_rewrite_tac[]) >>
  qexistsl_tac [`t`, `b`] >>
  simp[window_seq_def, eval_operand_def, mk_inst_def, is_terminator_def,
    not_fresh_at_def] >>
  qpat_x_assum `exec_alloca _ _ _ = OK t` mp_tac >>
  simp_tac (srw_ss()) [exec_alloca_def, mk_inst_def] >>
  Cases_on `FLOOKUP s.vs_allocas st.cs_next_id` >>
  simp_tac (srw_ss()) [AllCaseEqs(), LET_THM] >> strip_tac >>
  qpat_x_assum `update_var _ _ _ = t` (SUBST1_TAC o GSYM) >>
  simp_tac (srw_ss()) [update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  metis_tac[LESS_EQ_ANTISYM, LESS_EQ_TRANS, LESS_EQ_LESS_TRANS]
QED

Theorem window_cursor_load_sequence:
  emit_op MLOAD [ptr_op] st = (out,st') /\
  eval_operand ptr_op s = SOME (n2w b) /\ b < dimword (:256) ==>
  ?t. window_pure_seq st st' s t /\
    eval_operand out t = SOME (mload b s) /\
    (!x. out = Var x ==> not_fresh_at st' x)
Proof
  metis_tac[window_emit_load_pure]
QED

Theorem window_emit_alloca32_protected:
  emit_op ALLOCA [Lit 32w] st = (out,st') /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  alloca_room ctx func s /\ alloca_inv s /\
  (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = 32) /\
  q+n <= s.vs_alloca_next /\
  (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==>
    venomMemDefs$regions_disjoint (q,n) (b,sz)) ==>
  ?t b. window_seq st st' s t /\
    eval_operand out t = SOME (n2w b) /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (b,32) /\
    b+32 <= t.vs_alloca_next /\
    alloca_room ctx func t /\ alloca_inv t /\ window_alloca_growth s t /\
    abi_encoder_registered_effect {st.cs_next_id} [] s t /\
    venomMemDefs$regions_disjoint (q,n) (b,32)
Proof
  strip_tac >> drule_all window_emit_alloca32_sequence >> strip_tac >>
  qexistsl_tac [`t`, `b`] >> asm_rewrite_tac[] >>
  irule window_alloca_growth_protected >>
  qexistsl_tac [`st.cs_next_id`, `{st.cs_next_id}`, `s`, `t`] >>
  simp_tac (srw_ss()) [] >> asm_rewrite_tac[] >>
  metis_tac[abi_encoder_registered_effect_allocated]
QED

Theorem window_cursor_store_sequence:
  emit_void MSTORE [ptr_op;value] st = ((),st') /\
  eval_operand ptr_op s = SOME (n2w b) /\ eval_operand value s = SOME w /\
  b < dimword (:256) /\ FLOOKUP s.vs_allocas id = SOME (b,32) ==>
  window_seq st st' s (mstore b w s) /\
  abi_encoder_registered_effect {id} [] s (mstore b w s) /\
  mem_word_at b (mstore b w s).vs_memory = w
Proof
  strip_tac >> drule_all window_emit_store_run >> strip_tac >>
  `st'.cs_next_var = st.cs_next_var` by
    (qpat_assum `emit_void _ _ _ = _` mp_tac >>
     simp_tac (srw_ss()) [emit_void_def, fresh_id_def, emit_def,
       comp_bind_def, comp_return_def, LET_THM] >>
     disch_then (SUBST1_TAC o GSYM) >> simp[]) >>
  simp[window_seq_def, abi_encoder_registered_slot_store,
    mstore_mem_word_at_same] >>
  simp_tac (srw_ss()) [lookup_var_def, mstore_def,
    write_memory_with_expansion_def, LET_THM]
QED

Theorem window_cursor_init_sequence:
  emit_op ALLOCA [Lit 32w] st = (cursor,ready) /\
  emit_void MSTORE [cursor;value] ready = ((),final) /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  alloca_room ctx func s /\ alloca_inv s /\
  (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = 32) /\
  eval_operand value s = SOME w /\
  (!x. value = Var x ==> not_fresh_at st x) ==>
  ?t b. window_seq st final s t /\
    eval_operand cursor t = SOME (n2w b) /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (b,32) /\
    b+32 <= t.vs_alloca_next /\ mem_word_at b t.vs_memory = w /\
    alloca_room ctx func t /\ alloca_inv t /\ window_alloca_growth s t /\
    abi_encoder_registered_effect {st.cs_next_id} [] s t
Proof
  strip_tac >> drule_all window_emit_alloca32_sequence >> strip_tac >>
  `eval_operand value t = SOME w` by metis_tac[window_seq_eval] >>
  `t.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  `b < dimword (:256)` by decide_tac >>
  drule_all window_cursor_store_sequence >> strip_tac >>
  qexistsl_tac [`mstore b w t`, `b`] >>
  conj_tac >- metis_tac[window_seq_chain] >>
  conj_tac >-
    (irule window_seq_eval >> qexistsl_tac [`t`, `ready`, `final`] >> asm_rewrite_tac[]) >>
  asm_rewrite_tac[] >>
  `alloca_room ctx func (mstore b w t)` by
    (irule alloca_room_fields >> qexists_tac `t` >>
     simp_tac (srw_ss()) [mstore_def, write_memory_with_expansion_def, LET_THM] >>
     asm_rewrite_tac[]) >>
  `alloca_inv (mstore b w t)` by
    metis_tac[abi_encoder_primitive_alloca_inv] >>
  `window_alloca_growth s (mstore b w t)` by
    (qpat_x_assum `window_alloca_growth s t` mp_tac >>
     simp_tac (srw_ss()) [window_alloca_growth_def, mstore_def,
       write_memory_with_expansion_def, LET_THM] >> metis_tac[]) >>
  `abi_encoder_registered_effect {st.cs_next_id} [] s (mstore b w t)` by
    metis_tac[abi_encoder_registered_effect_trans] >>
  asm_rewrite_tac[] >>
  simp_tac (srw_ss()) [mstore_def, write_memory_with_expansion_def, LET_THM] >>
  asm_rewrite_tac[]
QED
