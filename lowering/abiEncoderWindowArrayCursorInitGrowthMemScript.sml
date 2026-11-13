(* Shared cursor initialization with growth at its actual execution witness. *)
Theory abiEncoderWindowArrayCursorInitGrowthMem
Ancestors
  abiEncoderWindowArrayEntry windowPhaseMem windowTransitionMem
  abiEncoderWindowPhaseFrameMem abiEncoderWindowMemFrame
  abiEncoderWindowSequenceFrameMem abiEncoderSharedArrayOuter abiDecoderVarSequence
  abiEncoderWindowLoopMem abiEncoderRegisteredEffect abiEncoderPrimitiveEffect
  abiEncoderWindowPhase abiEncoderWindowArrayInvariant abiEncoderWindowArrayBody freshWrites
  abiEncoderWindowStructuralMembers abiDecoderIndexInit context compileEnv emitHelper fragExec
  emitHelperProps exprLoweringProps valueEncodingProps venomState finite_map pred_set
  words arithmetic abiEncoderWindowArrayFinish abiEncoderArrayPhases
  abiEncoderWindowSequence windowSequenceMem fragExecMem allocaFootprint
  instMemFrontier venomExecSemantics venomMemDefs venomInst list abiEncoderWindowLeaves
  abiEncoderWindowContract immutableMemoryFrame

Theorem window_array_cursor_init_phase_growth_mem:
  emit_op ALLOCA [Lit 32w] st = (cursor,mid) /\
  emit_void MSTORE [cursor;value_op] mid = ((),en) /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  fn_has_code st mid func /\ fn_has_code mid en func /\
  alloca_room ctx func s /\ alloca_inv s /\
  (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = 32) /\
  eval_operand value_op s = SOME w /\
  (!x. value_op = Var x ==> not_fresh_at st x) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t b. window_phase ctx func st en {st.cs_next_id} [] s t /\
    window_array_transition ctx func st {st.cs_next_id} [] s t /\
    eval_operand cursor t = SOME (n2w b) /\
    (!x. cursor = Var x ==> not_fresh_at en x) /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (b,32) /\
    b+32 <= t.vs_alloca_next /\ b < dimword (:256) /\
    mem_word_at b t.vs_memory = w /\ mem_cont_sim ctx func s t /\
    (fn_inst_ids_distinct func ==> window_mem_frame ctx func s t) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  strip_tac >> drule_all window_emit_alloca32_phase_mem_conditional_frame >> strip_tac >>
  `alloca_inv t /\ alloca_room ctx func t /\ ~t.vs_halted /\
   t.vs_current_bb = mid.cs_current_bb /\
   t.vs_inst_idx = LENGTH mid.cs_current_insts` by
    metis_tac[window_phase_resources, window_phase_control] >>
  `b < dimword (:256)` by (drule alloca_room_next_lt >> decide_tac) >>
  `eval_operand value_op t = SOME w` by metis_tac[window_phase_operand] >>
  `window_phase ctx func mid en {st.cs_next_id} [] t
     ((mstore b w t) with vs_inst_idx := LENGTH en.cs_current_insts) /\
   mem_cont_sim ctx func t
     ((mstore b w t) with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (irule window_cursor_store_phase_mem >> asm_rewrite_tac[] >> metis_tac[]) >>
  `st.cs_next_var <= mid.cs_next_var /\ mid.cs_next_var <= en.cs_next_var` by
    metis_tac[ci_mono_emit_op, ci_mono_emit_void, ci_mono_def, pairTheory.SND] >>
  `window_phase ctx func st en {st.cs_next_id} [] s
     ((mstore b w t) with vs_inst_idx := LENGTH en.cs_current_insts) /\
   mem_cont_sim ctx func s
     ((mstore b w t) with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (irule window_phase_chain_mem >>
     qexistsl_tac [`{st.cs_next_id}`, `[]`, `mid`, `{st.cs_next_id}`, `[]`, `t`] >> simp[]) >>
  qmatch_asmsub_abbrev_tac `window_phase ctx func st en {st.cs_next_id} [] s u` >>
  `u.vs_allocas = t.vs_allocas /\ u.vs_alloca_next = t.vs_alloca_next` by
    simp[Abbr `u`, mstore_def, write_memory_with_expansion_def] >>
  `window_sizes32 {st.cs_next_id} u` by simp[window_sizes32_def] >>
  `abi_encoder_registered_effect {st.cs_next_id} [] s u` by metis_tac[window_phase_effect] >>
  `!R. window_sizes32 R s ==> window_sizes32 R u` by
    (qpat_assum `abi_encoder_registered_effect {st.cs_next_id} [] s u` mp_tac >>
     qpat_assum `window_sizes32 {st.cs_next_id} u` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> pure_rewrite_tac [window_sizes32_def] >>
     rpt strip_tac >> drule_all window_registered_sizes_transport >> metis_tac[]) >>
  `fn_inst_ids_distinct func ==> window_mem_frame ctx func s u` by
    (strip_tac >> `window_mem_frame ctx func s t` by metis_tac[] >>
     `window_mem_frame ctx func t u` by
       (simp[Abbr `u`] >> drule_all window_cursor_store_phase_mem_frame >>
        metis_tac[]) >>
     metis_tac[window_mem_frame_trans]) >>
  `LENGTH s.vs_memory <= LENGTH u.vs_memory` by
    simp[Abbr `u`, immutable_mstore_capacity] >>
  qexistsl_tac [`u`, `b`] >> asm_rewrite_tac[] >> conj_tac
  >- metis_tac[window_array_phase_transition] >>
  conj_tac >- metis_tac[window_phase_operand] >>
  conj_tac >- metis_tac[not_fresh_at_mono] >>
  simp[Abbr `u`, mstore_mem_word_at_same]
QED

Theorem window_array_index_init_run_growth_mem:
  abi_decode_index_init st = (ip,en) /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  fn_has_code st en func /\ alloca_room ctx func s /\ alloca_inv s /\
  (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = 32) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t b. window_phase ctx func st en {st.cs_next_id} [] s t /\
    window_array_transition ctx func st {st.cs_next_id} [] s t /\
    eval_operand ip t = SOME (n2w b) /\
    (!x. ip = Var x ==> not_fresh_at en x) /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (b,32) /\
    b+32 <= t.vs_alloca_next /\ b < dimword (:256) /\
    mem_word_at b t.vs_memory = 0w /\ mem_cont_sim ctx func s t /\
    (fn_inst_ids_distinct func ==> window_mem_frame ctx func s t) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  strip_tac >>
  `?mid. emit_op ALLOCA [Lit 32w] st = (ip,mid) /\
    emit_void MSTORE [ip;Lit 0w] mid = ((),en)` by
    (qpat_x_assum `abi_decode_index_init _ = _` mp_tac >>
     simp_tac bool_ss [abi_decode_index_init_def, contextTheory.compile_alloc_buffer_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
     pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
     Cases_on `emit_op ALLOCA [Lit 32w] st` >> gvs[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `cs_extends st mid /\ cs_extends mid en` by
    metis_tac[ci_mono_emit_op, ci_mono_emit_void, ci_mono_def, pairTheory.SND] >>
  drule_all fn_has_code_split >> strip_tac >>
  `eval_operand (Lit 0w) s = SOME (0w:bytes32) /\
   (!x. Lit 0w = Var x ==> not_fresh_at st x)` by simp[eval_operand_def] >>
  drule_all window_array_cursor_init_phase_growth_mem >> simp[]
QED
