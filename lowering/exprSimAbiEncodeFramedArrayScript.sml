Theory exprSimAbiEncodeFramedArray
Ancestors
  exprSimAbiEncodeFramedArrayControl exprSimAbiEncodeFramedArrayBody
  exprSimAbiEncodeExecFrame abiEncoderWindowArray abiEncoderWindowArrayExit
  abiEncoderWindowArrayBody abiEncoderWindowArrayInvariant abiEncoderWindowArrayLayout
  abiEncoderWindowArrayRound abiEncoderArrayLoopCode abiEncoderWindowArrayFinish
  abiEncoderRegisteredEffect abiEncoderPrimitiveEffect venomMemDefs finite_map pred_set
  venomExecSemantics venomInstProofs1 exprSimAbiEncodeFramedLeaves
  abiEncoderWindowSequence abiEncoderWindowPhase abiEncoderWindowContract
  abiEncoderArrayCode abiEncoderArrayPhases abiEncoderArrayContext
  emitHelper compileEnv freshWrites venomState venomInst
  exprLoweringProps emitHelperProps fragExec list rich_list arithmetic words
  exprSimAbiEncodeFramedPhases abiEncoderWindowCursor abiEncoderWindowArrayEntry
  valueEncodingProps abiEncoderWindowStructuralMembers abiDecoderIndexInit context

Theorem abi_encode_framed_array_exit_opcodes:
  (if active then abi_encode_array_dynamic_exit src dp st
   else abi_encode_array_static_exit src asz st) = (out,en) ==>
  EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode /\
    ~is_ext_call_op i.inst_opcode /\ i.inst_opcode <> INVOKE /\
    i.inst_opcode <> SETFMP /\ i.inst_opcode <> DALLOCA) (emitted_insts st en)
Proof
  Cases_on `active` >>
  simp[abi_encode_array_dynamic_exit_def, abi_encode_array_static_exit_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
    fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def, is_alloca_op_def,
    is_ext_call_op_def]
QED

Theorem abi_encode_framed_array_scalar_exit_run:
  abi_encoder_window_input (AbiDynArray ei asz msz active)
    (Array NONE ty) (ListV avs) sb cap s.vs_memory /\
  abi_encoder_array_prefix ty avs (LENGTH avs) d s.vs_memory /\
  (if active then abi_encode_array_dynamic_exit src dp st
   else abi_encode_array_static_exit src asz st) = (out,en) /\
  eval_operand src s = SOME (n2w sb) /\ sb < dimword (:256) /\
  (active ==> eval_operand dp s = SOME (n2w slot) /\ slot < dimword (:256) /\
    (!x. dp = Var x ==> not_fresh_at st x) /\
    mload slot s = n2w (LENGTH avs * abi_member_head_size ty +
       SUM (MAP (abi_member_tail_size ty) avs))) /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st en {} [] s t /\
    window_array_transition ctx func st {} [] s t /\
    mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) t.vs_memory =
      enc (Array NONE ty) (ListV avs) /\
    eval_operand out t = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    (!x. out = Var x ==> not_fresh_at en x) /\
    abi_encode_exec_frame func s t
Proof
  strip_tac >> drule_all window_array_scalar_exit_pure >> strip_tac >>
  drule abi_encode_framed_array_exit_opcodes >> strip_tac >>
  `abi_encode_exec_frame func s t` by
    (drule_all abi_encode_framed_ordinary_pure_sequence >> simp[]) >>
  `mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) s.vs_memory =
    enc (Array NONE ty) (ListV avs)` by metis_tac[window_array_prefix_complete] >>
  `window_phase ctx func st en {} [] s
    (t with vs_inst_idx := LENGTH en.cs_current_insts)` by
    metis_tac[window_pure_seq_phase] >>
  qexists_tac `t with vs_inst_idx := LENGTH en.cs_current_insts` >>
  asm_rewrite_tac[] >> conj_tac
  >- metis_tac[window_array_pure_phase_transition] >>
  `t.vs_memory = s.vs_memory` by fs[window_pure_seq_def] >>
  simp_tac (srw_ss()) [] >> asm_rewrite_tac[] >>
  Cases_on `out` >> fs[eval_operand_def, lookup_var_def]
QED

Theorem abi_encode_framed_array_completed_exit:
  window_array_inv ctx func owner ids ei asz msz active ty avs src dst
    ip isite islot dp dsite dslot count_op exit_st.cs_current_bb sb cap d (LENGTH avs) s /\
  exit_st.cs_current_insts = [] /\ owner.cs_next_var <= exit_st.cs_next_var /\
  (if active then abi_encode_array_dynamic_exit src dp exit_st
   else abi_encode_array_static_exit src asz exit_st) = (out,en) /\
  fn_has_code exit_st en func ==>
  ?t. window_array_transition ctx func owner {} [] s t /\
    mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) t.vs_memory =
      enc (Array NONE ty) (ListV avs) /\
    eval_operand out t = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    (!x. out = Var x ==> not_fresh_at en x) /\
    t.vs_current_bb = en.cs_current_bb /\ t.vs_inst_idx = LENGTH en.cs_current_insts /\
    abi_encode_exec_frame func s t
Proof
  strip_tac >>
  `abi_encoder_window_input (AbiDynArray ei asz msz active)
     (Array NONE ty) (ListV avs) sb cap s.vs_memory /\
   abi_encoder_array_prefix ty avs (LENGTH avs) d s.vs_memory /\
   eval_operand src s = SOME (n2w sb) /\ sb < dimword (:256) /\
   alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
   s.vs_current_bb = exit_st.cs_current_bb /\
   s.vs_inst_idx = LENGTH exit_st.cs_current_insts` by
    (fs[window_array_inv_def, window_array_root_def] >>
     `s.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >> decide_tac) >>
  `(active ==> eval_operand dp s = SOME (n2w dslot) /\ dslot < dimword (:256) /\
      (!x. dp = Var x ==> not_fresh_at exit_st x) /\
      mload dslot s = n2w (LENGTH avs * abi_member_head_size ty +
        SUM (MAP (abi_member_tail_size ty) avs)))` by
    (strip_tac >> fs[window_array_inv_def, window_array_cursor_def,
        mload_def, valueEncodingTheory.mem_word_at_def] >> metis_tac[not_fresh_at_mono]) >>
  drule_all abi_encode_framed_array_scalar_exit_run >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac[] >> conj_tac
  >- (irule window_array_transition_owner_weaken >> goal_assum (drule_at Any) >>
      metis_tac[not_fresh_at_mono]) >>
  metis_tac[window_phase_control]
QED

Theorem abi_encode_framed_array_loop_parent:
  abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels /\
  (if active then abi_encode_array_dynamic_body ip dp src dst ei asz msz body_st = (idx,body_end)
   else abi_encode_array_static_body ip src dst ei asz msz body_st = (idx,body_end)) /\
  abi_encode_framed_contract ei /\
  window_alloca_sites func (frag_ids body_st body_end) SUBSET ids /\
  isite IN ids /\ isite NOTIN window_alloca_sites func (frag_ids body_st body_end) /\
  (active ==> dsite IN ids /\ dsite NOTIN window_alloca_sites func (frag_ids body_st body_end) /\
    dsite <> isite) /\ psite NOTIN ids /\
  window_array_inv ctx func owner ids ei asz msz active ty avs src dst
    ip isite islot dp dsite dslot count_op (FST labels) sb cap d 0 s /\
  window_array_cursor T owner pp psite pb 0 sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) s ==>
  ?t. window_array_transition ctx func owner ids
      [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] s t /\
    window_array_inv ctx func owner ids ei asz msz active ty avs src dst
      ip isite islot dp dsite dslot count_op (SND (SND labels)) sb cap d (LENGTH avs) t /\
    window_array_cursor T owner pp psite pb 0 sb cap d
      (LENGTH (enc (Array NONE ty) (ListV avs))) t /\
    abi_encode_exec_frame func s t
Proof
  strip_tac >> `0 <= LENGTH avs` by simp[] >>
  drule_all abi_encode_framed_array_actual_control_loop >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac[] >> irule window_array_cursor_frame >>
  qexistsl_tac [`ids`, `ctx`, `func`,
    `[(d,LENGTH (enc (Array NONE ty) (ListV avs)))]`, `s`] >>
  asm_rewrite_tac[] >> fs[window_array_cursor_def, venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem abi_encode_framed_array_finish_opcodes:
  abi_encode_array_finish pp size_op st = (out,en) ==>
  EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode /\
    ~is_ext_call_op i.inst_opcode /\ i.inst_opcode <> INVOKE /\
    i.inst_opcode <> SETFMP /\ i.inst_opcode <> DALLOCA) (emitted_insts st en)
Proof
  simp[abi_encode_array_finish_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def, is_alloca_op_def,
    is_ext_call_op_def]
QED

Theorem abi_encode_framed_array_parent_finish:
  abi_encode_array_finish pp size_op st = (out,en) /\
  eval_operand pp s = SOME (n2w slot) /\ slot < dimword (:256) /\
  mload slot s = 0w /\ eval_operand size_op s = SOME (n2w n) /\
  (!x. pp = Var x \/ size_op = Var x ==> not_fresh_at st x) /\
  FLOOKUP s.vs_allocas site = SOME (slot,32) /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st en {site} [] s t /\
    window_array_transition ctx func st {site} [] s t /\
    eval_operand out t = SOME (n2w n) /\
    (!x. out = Var x ==> not_fresh_at en x) /\
    abi_encode_exec_frame func s t
Proof
  strip_tac >> drule_all window_array_parent_finish_seq >> strip_tac >>
  `raw.vs_allocas = s.vs_allocas /\ raw.vs_alloca_next = s.vs_alloca_next /\
   raw.vs_halted = s.vs_halted /\ raw.vs_current_bb = s.vs_current_bb` by
    fs[window_pure_seq_def, mstore_def, write_memory_with_expansion_def] >>
  `abi_encode_exec_frame func s raw` by
    (`run_inst_seq (emitted_insts st en) s = OK raw` by fs[window_seq_def] >>
     drule abi_encode_framed_array_finish_opcodes >> strip_tac >>
     `raw.vs_fmp = s.vs_fmp` by
       (irule (BETA_RULE (Q.ISPEC `\s:venom_state. s.vs_fmp`
         run_inst_seq_preserves_field)) >>
        qexists_tac `emitted_insts st en` >> asm_rewrite_tac[] >>
        rpt strip_tac >> irule step_inst_base_preserves_fmp_ordinary >>
        qexists_tac `i` >> simp[] >> fs[EVERY_MEM]) >>
     fs[window_pure_seq_def, abi_encode_exec_frame_def, pending_alloca_size_def,
        mstore_def, write_memory_with_expansion_def]) >>
  suspend "effect"
QED

Resume abi_encode_framed_array_parent_finish[effect]:
  `abi_encoder_registered_effect {site} [] s raw` by
    (`abi_encoder_registered_effect {site} [] s t2` by
       metis_tac[window_pure_seq_registered_effect] >>
     `abi_encoder_registered_effect {site} [] t2 (mstore slot (n2w n) t2)` by
       (irule abi_encoder_registered_slot_store >> fs[window_pure_seq_def]) >>
     `abi_encoder_registered_effect {site} [] (mstore slot (n2w n) t2) raw` by
       metis_tac[window_pure_seq_registered_effect] >>
     metis_tac[abi_encoder_registered_effect_trans]) >>
  `window_alloca_growth s raw` by metis_tac[window_alloca_growth_fields] >>
  `alloca_inv raw /\ alloca_room ctx func raw` by
    (fs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
        alloca_room_def, pending_alloca_size_def] >> metis_tac[]) >>
  `window_phase ctx func st en {site} [] s
     (raw with vs_inst_idx := LENGTH en.cs_current_insts)` by metis_tac[window_seq_phase] >>
  qexists_tac `raw with vs_inst_idx := LENGTH en.cs_current_insts` >>
  asm_rewrite_tac[] >> conj_tac
  >- (irule window_array_phase_transition >> conj_tac
      >- simp[window_sizes32_def] >> goal_assum (drule_at Any)) >>
  Cases_on `out` >> fs[eval_operand_def, lookup_var_def]
QED

Finalise abi_encode_framed_array_parent_finish

Theorem abi_encode_framed_array_exit_parent:
  window_array_inv ctx func owner ids ei asz msz active ty avs src dst
    ip isite islot dp dsite dslot count_op exit_st.cs_current_bb sb cap d (LENGTH avs) s /\
  window_array_cursor T owner pp psite pb 0 sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) s /\
  exit_st.cs_current_insts = [] /\ owner.cs_next_var <= exit_st.cs_next_var /\
  (if active then abi_encode_array_dynamic_exit src dp exit_st
   else abi_encode_array_static_exit src asz exit_st) = (size_op,mid) /\
  abi_encode_array_finish pp size_op mid = (out,en) /\
  fn_has_code exit_st mid func /\ fn_has_code mid en func ==>
  ?t. window_array_transition ctx func owner {psite} [] s t /\
    mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) t.vs_memory =
      enc (Array NONE ty) (ListV avs) /\
    eval_operand out t = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    t.vs_current_bb = en.cs_current_bb /\ t.vs_inst_idx = LENGTH en.cs_current_insts /\
    abi_encode_exec_frame func s t
Proof
  strip_tac >> drule_all abi_encode_framed_array_completed_exit >> strip_tac >>
  rename1 `window_array_transition ctx func owner {} [] s u` >>
  `window_array_cursor T owner pp psite pb 0 sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) u` by
    (irule window_array_cursor_frame >>
     qexistsl_tac [`{}`, `ctx`, `func`, `[]`, `s`] >> asm_rewrite_tac[] >> simp[]) >>
  `exit_st.cs_next_var <= mid.cs_next_var` by
    (Cases_on `active` >> full_simp_tac bool_ss []
     >- (drule (cj 2 abi_encode_array_exit_shape) >> simp[]) >>
     drule (cj 1 abi_encode_array_exit_shape) >> simp[]) >>
  `!x. not_fresh_at owner x ==> not_fresh_at mid x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `owner` >>
     asm_rewrite_tac[] >> decide_tac) >>
  `eval_operand pp u = SOME (n2w pb) /\ pb < dimword (:256) /\
   mload pb u = 0w /\ FLOOKUP u.vs_allocas psite = SOME (pb,32) /\
   (!x. pp = Var x \/ size_op = Var x ==> not_fresh_at mid x) /\
   alloca_inv u /\ alloca_room ctx func u /\ ~u.vs_halted` by
    (fs[window_array_cursor_def, window_array_transition_def,
        mload_def, valueEncodingTheory.mem_word_at_def] >> metis_tac[]) >>
  drule_all abi_encode_framed_array_parent_finish >> strip_tac >>
  `abi_encode_exec_frame func s t` by
    (irule abi_encode_exec_frame_trans >> qexists_tac `u` >> asm_rewrite_tac[]) >>
  suspend "finish"
QED

Resume abi_encode_framed_array_exit_parent[finish]:
  `window_array_transition ctx func owner {psite} [] u t` by
    (irule window_array_transition_owner_weaken >> goal_assum (drule_at Any) >>
     asm_rewrite_tac[]) >>
  `mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) t.vs_memory =
    mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) u.vs_memory` by
    (irule abi_encoder_window_effect_bytes >> qexistsl_tac [`{psite}`, `[]`] >>
     `abi_encoder_registered_effect {psite} [] u t` by
       metis_tac[window_array_transition_effect] >>
     asm_rewrite_tac[EVERY_DEF, IN_SING] >> rpt strip_tac >>
     `FLOOKUP t.vs_allocas psite = SOME (pb,32)` by
       metis_tac[window_array_transition_effect, abi_encoder_registered_effect_allocated] >>
     gvs[window_array_cursor_def]) >>
  qexists_tac `t` >> asm_rewrite_tac[] >> conj_tac
  >- (irule window_array_transition_trans >> qexists_tac `u` >> asm_rewrite_tac[] >>
      irule window_array_transition_enlarge >> qexistsl_tac [`{}`, `[]`] >>
      asm_rewrite_tac[] >> simp[]) >>
  metis_tac[window_phase_control]
QED

Finalise abi_encode_framed_array_exit_parent

Theorem abi_encode_framed_array_cursor_init_phase:
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
    mem_word_at b t.vs_memory = w /\ abi_encode_exec_frame func s t
Proof
  strip_tac >> drule_all abi_encode_framed_alloca32_phase_observed >> strip_tac >>
  `alloca_inv t /\ alloca_room ctx func t /\ ~t.vs_halted /\
   t.vs_current_bb = mid.cs_current_bb /\
   t.vs_inst_idx = LENGTH mid.cs_current_insts` by
    metis_tac[window_phase_resources, window_phase_control] >>
  `b < dimword (:256)` by (drule alloca_room_next_lt >> decide_tac) >>
  `eval_operand value_op t = SOME w` by metis_tac[window_phase_operand] >>
  `window_phase ctx func mid en {st.cs_next_id} [] t
    ((mstore b w t) with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (irule window_cursor_store_phase >> asm_rewrite_tac[] >> metis_tac[]) >>
  `st.cs_next_var <= mid.cs_next_var /\ mid.cs_next_var <= en.cs_next_var` by
    metis_tac[ci_mono_emit_op, ci_mono_emit_void, ci_mono_def, pairTheory.SND] >>
  `window_phase ctx func st en {st.cs_next_id} [] s
    ((mstore b w t) with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (irule window_phase_chain >>
     qexistsl_tac [`{st.cs_next_id}`, `[]`, `mid`, `{st.cs_next_id}`, `[]`, `t`] >> simp[]) >>
  qmatch_asmsub_abbrev_tac `window_phase ctx func st en {st.cs_next_id} [] s u` >>
  `abi_encode_exec_frame func t u` by
    simp[Abbr `u`, abi_encode_exec_frame_def, pending_alloca_size_def,
      mstore_def, write_memory_with_expansion_def] >>
  `abi_encode_exec_frame func s u` by
    (irule abi_encode_exec_frame_trans >> qexists_tac `t` >> asm_rewrite_tac[]) >>
  `u.vs_allocas = t.vs_allocas /\ u.vs_alloca_next = t.vs_alloca_next` by
    simp[Abbr `u`, mstore_def, write_memory_with_expansion_def] >>
  `window_sizes32 {st.cs_next_id} u` by simp[window_sizes32_def] >>
  `abi_encoder_registered_effect {st.cs_next_id} [] s u` by metis_tac[window_phase_effect] >>
  `!R. window_sizes32 R s ==> window_sizes32 R u` by
    (qpat_assum `abi_encoder_registered_effect {st.cs_next_id} [] s u` mp_tac >>
     qpat_assum `window_sizes32 {st.cs_next_id} u` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> pure_rewrite_tac [window_sizes32_def] >>
     rpt strip_tac >> drule_all window_registered_sizes_transport >> metis_tac[]) >>
  qexistsl_tac [`u`, `b`] >> asm_rewrite_tac[] >> conj_tac
  >- metis_tac[window_array_phase_transition] >>
  conj_tac >- metis_tac[window_phase_operand] >>
  conj_tac >- metis_tac[not_fresh_at_mono] >>
  simp[Abbr `u`, mstore_mem_word_at_same]
QED

Theorem abi_encode_framed_array_index_init_run:
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
    mem_word_at b t.vs_memory = 0w /\ abi_encode_exec_frame func s t
Proof
  strip_tac >>
  `?mid. emit_op ALLOCA [Lit 32w] st = (ip,mid) /\
    emit_void MSTORE [ip;Lit 0w] mid = ((),en)` by
    (qpat_x_assum `abi_decode_index_init _ = _` mp_tac >>
     simp_tac bool_ss [abi_decode_index_init_def, compile_alloc_buffer_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
     pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
     Cases_on `emit_op ALLOCA [Lit 32w] st` >> gvs[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `cs_extends st mid /\ cs_extends mid en` by
    metis_tac[ci_mono_emit_op, ci_mono_emit_void, ci_mono_def, pairTheory.SND] >>
  drule_all fn_has_code_split >> strip_tac >>
  `eval_operand (Lit 0w) s = SOME (0w:bytes32) /\
   (!x. Lit 0w = Var x ==> not_fresh_at st x)` by simp[eval_operand_def] >>
  drule_all abi_encode_framed_array_cursor_init_phase >> simp[]
QED
