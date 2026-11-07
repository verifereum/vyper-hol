Theory exprSimAbiEncodeFramedArray
Ancestors
  exprSimAbiEncodeFramedArrayControl exprSimAbiEncodeFramedArrayBody
  exprSimAbiEncodeExecFrame exprSimAbiEncodeSemantic
  abiEncoderWindowArray abiEncoderWindowArrayExit
  abiEncoderWindowArrayBody abiEncoderWindowArrayInvariant abiEncoderWindowArrayLayout
  abiEncoderWindowArrayRound abiEncoderArrayLoopCode abiEncoderWindowArrayFinish
  abiEncoderRegisteredEffect abiEncoderPrimitiveEffect venomMemDefs finite_map pred_set
  venomExecSemantics venomInstProofs1 exprSimAbiEncodeFramedLeaves
  abiEncoderWindowSequence abiEncoderWindowPhase abiEncoderWindowContract
  abiEncoderArrayCode abiEncoderArrayPhases abiEncoderArrayContext
  emitHelper compileEnv freshWrites venomState venomInst
  exprLoweringProps emitHelperProps fragExec list rich_list arithmetic words
  exprSimAbiEncodeFramedPhases abiEncoderWindowCursor abiEncoderWindowArrayEntry
  valueEncodingProps abiEncoderWindowStructuralMembers abiDecoderIndexInit context instIdxIndep
  abiEncoderWindow abiEncoderArrayPrefix abiEncoderArrayTailInit abiEncoderProps
  abiEncoderExtendSim

Theorem abi_encode_framed_array_exit_opcodes:
  (if active then abi_encode_array_dynamic_exit src dp st
   else abi_encode_array_static_exit src asz st) = (out,en) ==>
  EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode /\
    ~is_ext_call_op i.inst_opcode /\ i.inst_opcode <> INVOKE /\
    i.inst_opcode <> SETFMP /\ i.inst_opcode <> DALLOCA /\
    i.inst_opcode <> ISTORE /\ i.inst_opcode <> CALL /\
    i.inst_opcode <> STATICCALL /\ i.inst_opcode <> DELEGATECALL /\
    i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (emitted_insts st en)
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
    i.inst_opcode <> SETFMP /\ i.inst_opcode <> DALLOCA /\
    i.inst_opcode <> ISTORE /\ i.inst_opcode <> CALL /\
    i.inst_opcode <> STATICCALL /\ i.inst_opcode <> DELEGATECALL /\
    i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (emitted_insts st en)
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
     drule_all abi_encode_semantic_ordinary_sequence >> strip_tac >>
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
  >- (irule window_array_phase_transition >> asm_rewrite_tac[] >> qexists_tac `en` >> asm_rewrite_tac[]) >>
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

Theorem abi_encode_framed_array_length_copy_phase:
  emit_op MLOAD [src] st = (count_op,mid) /\
  emit_void MSTORE [dst;count_op] mid = ((),en) /\
  eval_operand src s = SOME (n2w sb) /\ sb < dimword (:256) /\
  mem_word_at sb s.vs_memory = n2w n /\
  eval_operand dst s = SOME (n2w d) /\ d < dimword (:256) /\
  (!x. dst = Var x ==> not_fresh_at st x) /\
  fn_has_code st mid func /\ fn_has_code mid en func /\
  alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st en {} [(d,32)] s t /\
    window_array_transition ctx func st {} [(d,32)] s t /\
    eval_operand count_op t = SOME (n2w n) /\
    (!x. count_op = Var x ==> not_fresh_at en x) /\
    mem_word_at d t.vs_memory = n2w n /\ abi_encode_exec_frame func s t
Proof
  strip_tac >> drule_all abi_encode_framed_cursor_load_phase_observed >> strip_tac >>
  `eval_operand count_op t = SOME (n2w n)` by fs[mload_def, valueEncodingTheory.mem_word_at_def] >>
  `eval_operand dst t = SOME (n2w d)` by metis_tac[window_phase_operand] >>
  `alloca_inv t /\ alloca_room ctx func t /\ ~t.vs_halted /\
   t.vs_current_bb = mid.cs_current_bb /\
   t.vs_inst_idx = LENGTH mid.cs_current_insts` by
    metis_tac[window_phase_resources, window_phase_control] >>
  drule_all window_output_store_phase >> strip_tac >>
  `st.cs_next_var <= mid.cs_next_var /\ mid.cs_next_var <= en.cs_next_var` by
    metis_tac[ci_mono_emit_op, ci_mono_emit_void, ci_mono_def, pairTheory.SND] >>
  `window_phase ctx func st en {} [(d,32)] s
    ((mstore d (n2w n) t) with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (irule window_phase_chain >>
     qexistsl_tac [`{}`, `[]`, `mid`, `{}`, `[(d,32)]`, `t`] >> simp[]) >>
  qmatch_asmsub_abbrev_tac `window_phase ctx func st en {} [(d,32)] s u` >>
  `abi_encode_exec_frame func t u` by
    simp[Abbr `u`, abi_encode_exec_frame_def, pending_alloca_size_def,
      mstore_def, write_memory_with_expansion_def] >>
  `abi_encode_exec_frame func s u` by
    (irule abi_encode_exec_frame_trans >> qexists_tac `t` >> asm_rewrite_tac[]) >>
  `!R. window_sizes32 R s ==> window_sizes32 R u` by
    (`abi_encoder_registered_effect {} [(d,32)] s u` by metis_tac[window_phase_effect] >>
     qpat_assum `abi_encoder_registered_effect {} [(d,32)] s u` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> pure_rewrite_tac [window_sizes32_def] >> rpt strip_tac >>
     `!i b sz. i IN ({}:num set) /\ FLOOKUP u.vs_allocas i = SOME (b,sz) ==> sz = 32` by simp[] >>
     drule_all window_registered_sizes_transport >> metis_tac[]) >>
  qexists_tac `u` >> asm_rewrite_tac[] >> conj_tac
  >- (irule window_array_phase_transition >> asm_rewrite_tac[] >> qexists_tac `en` >> asm_rewrite_tac[]) >>
  conj_tac >- metis_tac[window_phase_operand] >>
  conj_tac >- metis_tac[not_fresh_at_mono] >>
  simp[Abbr `u`, mstore_mem_word_at_same]
QED

Theorem abi_encode_framed_array_mul_phase:
  emit_op MUL [lhs;rhs] st = (out,en) /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st en {} [] s t /\
    eval_operand out t = SOME (a*b) /\
    (!x. out = Var x ==> not_fresh_at en x) /\ abi_encode_exec_frame func s t
Proof
  strip_tac >> drule_all window_array_mul_pure_observed >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode /\
    ~is_ext_call_op i.inst_opcode /\ i.inst_opcode <> INVOKE /\
    i.inst_opcode <> SETFMP /\ i.inst_opcode <> DALLOCA /\
    i.inst_opcode <> ISTORE /\ i.inst_opcode <> CALL /\
    i.inst_opcode <> STATICCALL /\ i.inst_opcode <> DELEGATECALL /\
    i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (emitted_insts st en)` by
    (drule emitted_insts_emit_op >> simp[mk_inst_def, is_terminator_def,
       is_alloca_op_def, is_ext_call_op_def]) >>
  `abi_encode_exec_frame func s t` by
    (drule_all abi_encode_framed_ordinary_pure_sequence >> simp[]) >>
  qexists_tac `t with vs_inst_idx := LENGTH en.cs_current_insts` >>
  (conj_tac >- metis_tac[window_pure_seq_phase]) >>
  simp_tac (srw_ss()) [eval_op_inst_idx, abi_encode_exec_frame_def,
    pending_alloca_size_def] >> asm_rewrite_tac[] >>
  gvs[abi_encode_exec_frame_def, pending_alloca_size_def]
QED

Theorem abi_encode_framed_array_dynamic_cursor_phase:
  emit_op ALLOCA [Lit 32w] st = (dp,c1) /\
  emit_op MUL [count_op;Lit (n2w asz)] c1 = (offset,c2) /\
  emit_void MSTORE [dp;offset] c2 = ((),en) /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  fn_has_code st c1 func /\ fn_has_code c1 c2 func /\ fn_has_code c2 en func /\
  alloca_room ctx func s /\ alloca_inv s /\
  (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = 32) /\
  eval_operand count_op s = SOME (n2w n) /\
  (!x. count_op = Var x ==> not_fresh_at st x) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t b. window_phase ctx func st en {st.cs_next_id} [] s t /\
    window_array_transition ctx func st {st.cs_next_id} [] s t /\
    eval_operand dp t = SOME (n2w b) /\
    (!x. dp = Var x ==> not_fresh_at en x) /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (b,32) /\
    b+32 <= t.vs_alloca_next /\ b < dimword (:256) /\
    mem_word_at b t.vs_memory = n2w (n*asz) /\ abi_encode_exec_frame func s t
Proof
  strip_tac >> drule_all abi_encode_framed_alloca32_phase_observed >> strip_tac >>
  `alloca_inv t /\ alloca_room ctx func t /\ ~t.vs_halted /\
   t.vs_current_bb = c1.cs_current_bb /\
   t.vs_inst_idx = LENGTH c1.cs_current_insts` by
    metis_tac[window_phase_resources, window_phase_control] >>
  `b < dimword (:256)` by (drule alloca_room_next_lt >> decide_tac) >>
  `eval_operand count_op t = SOME (n2w n)` by metis_tac[window_phase_operand] >>
  `eval_operand (Lit (n2w asz)) t = SOME (n2w asz)` by simp[eval_operand_def] >>
  drule_all abi_encode_framed_array_mul_phase >> strip_tac >>
  rename1 `window_phase ctx func c1 c2 {} [] t u` >>
  `abi_encode_exec_frame func s u` by
    (irule abi_encode_exec_frame_trans >> qexists_tac `t` >> asm_rewrite_tac[]) >>
  `alloca_inv u /\ alloca_room ctx func u /\ ~u.vs_halted /\
   u.vs_current_bb = c2.cs_current_bb /\
   u.vs_inst_idx = LENGTH c2.cs_current_insts` by
    metis_tac[window_phase_resources, window_phase_control] >>
  `eval_operand dp u = SOME (n2w b)` by metis_tac[window_phase_operand] >>
  `FLOOKUP u.vs_allocas st.cs_next_id = SOME (b,32)` by
    metis_tac[window_phase_effect, abi_encoder_registered_effect_allocated] >>
  `b+32 <= u.vs_alloca_next` by
    metis_tac[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
  `window_phase ctx func c2 en {st.cs_next_id} [] u
    ((mstore b (n2w (n*asz)) u) with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (irule window_cursor_store_phase >> asm_rewrite_tac[] >>
     qexistsl_tac [`dp`, `offset`] >> fs[word_mul_n2w, MULT_COMM]) >>
  `st.cs_next_var <= c1.cs_next_var /\ c1.cs_next_var <= c2.cs_next_var /\
   c2.cs_next_var <= en.cs_next_var` by
    metis_tac[ci_mono_emit_op, ci_mono_emit_void, ci_mono_def, pairTheory.SND] >>
  `window_phase ctx func st c2 {st.cs_next_id} [] s u` by
    (irule window_phase_chain >>
     qexistsl_tac [`{st.cs_next_id}`, `[]`, `c1`, `{}`, `[]`, `t`] >> simp[]) >>
  `window_phase ctx func st en {st.cs_next_id} [] s
    ((mstore b (n2w (n*asz)) u) with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (irule window_phase_chain >>
     qexistsl_tac [`{st.cs_next_id}`, `[]`, `c2`, `{st.cs_next_id}`, `[]`, `u`] >> simp[]) >>
  qmatch_asmsub_abbrev_tac `window_phase ctx func st en {st.cs_next_id} [] s v` >>
  `abi_encode_exec_frame func u v` by
    simp[Abbr `v`, abi_encode_exec_frame_def, pending_alloca_size_def,
      mstore_def, write_memory_with_expansion_def] >>
  `abi_encode_exec_frame func s v` by
    (irule abi_encode_exec_frame_trans >> qexists_tac `u` >> asm_rewrite_tac[]) >>
  suspend "finish"
QED

Resume abi_encode_framed_array_dynamic_cursor_phase[finish]:
  `v.vs_allocas = u.vs_allocas /\ v.vs_alloca_next = u.vs_alloca_next` by
    simp[Abbr `v`, mstore_def, write_memory_with_expansion_def] >>
  `window_sizes32 {st.cs_next_id} v` by simp[window_sizes32_def] >>
  `abi_encoder_registered_effect {st.cs_next_id} [] s v` by metis_tac[window_phase_effect] >>
  `!R. window_sizes32 R s ==> window_sizes32 R v` by
    (qpat_assum `abi_encoder_registered_effect {st.cs_next_id} [] s v` mp_tac >>
     qpat_assum `window_sizes32 {st.cs_next_id} v` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> pure_rewrite_tac [window_sizes32_def] >>
     rpt strip_tac >> drule_all window_registered_sizes_transport >> metis_tac[]) >>
  qexistsl_tac [`v`, `b`] >> asm_rewrite_tac[] >> conj_tac
  >- (irule window_array_phase_transition >> asm_rewrite_tac[] >> qexists_tac `en` >> asm_rewrite_tac[]) >>
  conj_tac
  >- (qpat_x_assum `eval_operand dp u = _` mp_tac >>
      simp_tac (srw_ss()) [Abbr `v`, mstore_def, write_memory_with_expansion_def] >>
      POP_ASSUM_LIST (K all_tac) >> Cases_on `dp` >> simp[eval_operand_def, lookup_var_def]) >>
  conj_tac >- metis_tac[not_fresh_at_mono] >>
  simp[Abbr `v`, mstore_mem_word_at_same]
QED

Finalise abi_encode_framed_array_dynamic_cursor_phase

Theorem abi_encode_framed_array_prefix_phase:
  abi_decode_index_init st = (pp,c1) /\
  emit_op MLOAD [src] c1 = (count_op,c2) /\
  emit_void MSTORE [dst;count_op] c2 = ((),en) /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  fn_has_code st c1 func /\ fn_has_code c1 c2 func /\ fn_has_code c2 en func /\
  alloca_room ctx func s /\ alloca_inv s /\
  (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,32) (b,sz) /\
    venomMemDefs$regions_disjoint (d,32) (b,sz)) /\
  sb+32 <= s.vs_alloca_next /\ d+32 <= s.vs_alloca_next /\
  eval_operand src s = SOME (n2w sb) /\
  mem_word_at sb s.vs_memory = n2w n /\
  eval_operand dst s = SOME (n2w d) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t b. window_phase ctx func st en {st.cs_next_id} [(d,32)] s t /\
    window_array_transition ctx func st {st.cs_next_id} [(d,32)] s t /\
    eval_operand pp t = SOME (n2w b) /\
    (!x. pp = Var x \/ count_op = Var x ==> not_fresh_at en x) /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (b,32) /\
    b+32 <= t.vs_alloca_next /\ b < dimword (:256) /\
    mem_word_at b t.vs_memory = 0w /\
    eval_operand count_op t = SOME (n2w n) /\
    mem_word_at d t.vs_memory = n2w n /\ abi_encode_exec_frame func s t
Proof
  strip_tac >>
  `!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = 32` by metis_tac[] >>
  drule_all abi_encode_framed_array_index_init_run >> strip_tac >>
  `alloca_inv t /\ alloca_room ctx func t /\ ~t.vs_halted /\
   t.vs_current_bb = c1.cs_current_bb /\
   t.vs_inst_idx = LENGTH c1.cs_current_insts` by
    metis_tac[window_phase_resources, window_phase_control] >>
  `sb < dimword (:256) /\ d < dimword (:256)` by
    (qpat_assum `alloca_room ctx func s` (mp_tac o MATCH_MP alloca_room_next_lt) >> decide_tac) >>
  `eval_operand src t = SOME (n2w sb) /\ eval_operand dst t = SOME (n2w d)` by
    metis_tac[window_phase_operand] >>
  `mem_bytes_at sb 32 t.vs_memory = mem_bytes_at sb 32 s.vs_memory` by
    (`window_alloca_growth s t` by metis_tac[window_phase_resources] >>
     irule window_alloca_growth_frame >> asm_rewrite_tac[] >>
     qexistsl_tac [`{st.cs_next_id}`, `[]`] >>
     simp_tac (srw_ss()) [IN_SING, EVERY_DEF] >> metis_tac[window_phase_effect]) >>
  `mem_word_at sb t.vs_memory = n2w n` by
    (qpat_x_assum `mem_word_at sb s.vs_memory = _` mp_tac >>
     qpat_x_assum `mem_bytes_at sb 32 _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[valueEncodingTheory.mem_word_at_def, GSYM valueEncodingTheory.mem_bytes_at_def]) >>
  `st.cs_next_var <= c1.cs_next_var` by
    (drule abi_decode_index_init_shape >> strip_tac >> decide_tac) >>
  `!x. dst = Var x ==> not_fresh_at c1 x` by metis_tac[not_fresh_at_mono] >>
  drule_all abi_encode_framed_array_length_copy_phase >> strip_tac >>
  `abi_encode_exec_frame func s t'` by
    (irule abi_encode_exec_frame_trans >> qexists_tac `t` >> asm_rewrite_tac[]) >>
  suspend "finish"
QED

Resume abi_encode_framed_array_prefix_phase[finish]:
  `window_alloca_growth s t /\
   (!i r. FLOOKUP s.vs_allocas i = SOME r ==> FLOOKUP t.vs_allocas i = SOME r)` by
    metis_tac[window_phase_resources, window_phase_effect, abi_encoder_registered_effect_allocated] >>
  `!i b sz. i IN {st.cs_next_id} /\ FLOOKUP t.vs_allocas i = SOME (b,sz) ==>
    venomMemDefs$regions_disjoint (d,32) (b,sz)` by
    (rpt strip_tac >> irule window_alloca_growth_protected >>
     qexistsl_tac [`i`, `{st.cs_next_id}`, `s`, `t`] >>
     full_simp_tac bool_ss [IN_SING] >> asm_rewrite_tac[] >>
     rpt strip_tac >> qpat_x_assum `!b sz. _ ==> _ /\ _` drule >> simp_tac bool_ss []) >>
  `venomMemDefs$regions_disjoint (b,32) (d,32)` by
    (`venomMemDefs$regions_disjoint (d,32) (b,32)` by
       (qpat_assum `!i b sz. i IN _ /\ _ ==> _` mp_tac >>
        simp_tac (srw_ss()) [IN_SING] >> metis_tac[]) >>
     qpat_x_assum `venomMemDefs$regions_disjoint (d,32) (b,32)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[venomMemDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
  `mem_word_at b t'.vs_memory = 0w` by
    (`mem_word_at b t'.vs_memory = mem_word_at b t.vs_memory` by
       (irule window_array_transition_cursor_frame >>
        qexistsl_tac [`ctx`, `func`, `{}`, `[(d,32)]`, `c1`, `st.cs_next_id`] >>
        simp_tac (srw_ss()) [EVERY_DEF] >> metis_tac[]) >> metis_tac[]) >>
  `c1.cs_next_var <= c2.cs_next_var /\ c2.cs_next_var <= en.cs_next_var` by
    metis_tac[ci_mono_emit_op, ci_mono_emit_void, ci_mono_def, pairTheory.SND] >>
  `window_phase ctx func st en {st.cs_next_id} [(d,32)] s t'` by
    (irule window_phase_chain >>
     qexistsl_tac [`{st.cs_next_id}`, `[]`, `c1`, `{}`, `[(d,32)]`, `t`] >>
     simp_tac (srw_ss()) [SUBSET_REFL, EMPTY_SUBSET] >> metis_tac[]) >>
  `!R. window_sizes32 R s ==> window_sizes32 R t'` by metis_tac[window_array_transition_sizes] >>
  `window_array_transition ctx func st {st.cs_next_id} [(d,32)] s t'` by
    metis_tac[window_array_phase_transition] >>
  `FLOOKUP t'.vs_allocas st.cs_next_id = SOME (b,32)` by
    metis_tac[window_phase_effect, abi_encoder_registered_effect_allocated] >>
  `b+32 <= t'.vs_alloca_next` by
    (`window_alloca_growth t t'` by metis_tac[window_phase_resources] >>
     drule_all window_alloca_growth_frontier >> simp[]) >>
  qexistsl_tac [`t'`, `b`] >> asm_rewrite_tac[] >>
  conj_tac >- metis_tac[window_phase_operand] >> metis_tac[not_fresh_at_mono]
QED

Finalise abi_encode_framed_array_prefix_phase

Theorem abi_encode_framed_array_prefix_trace[local]:
  abi_encode_array_prefix src dst st = ((pp,count_op),en) ==>
  ?c1 c2. abi_decode_index_init st = (pp,c1) /\
    emit_op MLOAD [src] c1 = (count_op,c2) /\
    emit_void MSTORE [dst;count_op] c2 = ((),en)
Proof
  simp_tac bool_ss [abi_encode_array_prefix_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem abi_encode_framed_array_prefix_run:
  abi_encode_array_prefix src dst st = ((pp,count_op),en) /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  fn_has_code st en func /\ alloca_room ctx func s /\ alloca_inv s /\
  (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,32) (b,sz) /\
    venomMemDefs$regions_disjoint (d,32) (b,sz)) /\
  sb+32 <= s.vs_alloca_next /\ d+32 <= s.vs_alloca_next /\
  eval_operand src s = SOME (n2w sb) /\
  mem_word_at sb s.vs_memory = n2w n /\
  eval_operand dst s = SOME (n2w d) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t b. window_phase ctx func st en {st.cs_next_id} [(d,32)] s t /\
    window_array_transition ctx func st {st.cs_next_id} [(d,32)] s t /\
    eval_operand pp t = SOME (n2w b) /\
    (!x. pp = Var x \/ count_op = Var x ==> not_fresh_at en x) /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (b,32) /\
    b+32 <= t.vs_alloca_next /\ b < dimword (:256) /\
    mem_word_at b t.vs_memory = 0w /\
    eval_operand count_op t = SOME (n2w n) /\
    mem_word_at d t.vs_memory = n2w n /\ abi_encode_exec_frame func s t
Proof
  strip_tac >> drule abi_encode_framed_array_prefix_trace >> strip_tac >>
  `cs_extends st c1` by
    (drule abi_decode_index_init_shape >> simp_tac bool_ss [] >> strip_tac >>
     fs[inst_extends_def, cs_extends_def] >> decide_tac) >>
  `cs_extends c1 c2 /\ cs_extends c2 en` by
    metis_tac[ci_mono_emit_op, ci_mono_emit_void, ci_mono_def, pairTheory.SND] >>
  `fn_has_code st c1 func /\ fn_has_code c1 c2 func /\ fn_has_code c2 en func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  drule_all abi_encode_framed_array_prefix_phase >> simp_tac bool_ss []
QED

Theorem abi_encode_framed_array_root_index_init_run:
  window_array_root ctx func st ids ei asz msz active ty avs src dst sb cap d s /\
  abi_decode_index_init st = (ip,en) /\ st.cs_next_id IN ids /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  fn_has_code st en func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t b. window_phase ctx func st en {st.cs_next_id} [] s t /\
    window_array_transition ctx func st {st.cs_next_id} [] s t /\
    window_array_root ctx func st ids ei asz msz active ty avs src dst sb cap d t /\
    window_array_cursor T en ip st.cs_next_id b 0 sb cap d
      (LENGTH (enc (Array NONE ty) (ListV avs))) t /\ abi_encode_exec_frame func s t
Proof
  strip_tac >>
  `alloca_room ctx func s /\ alloca_inv s /\
   (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = 32)` by
    (fs[window_array_root_def, window_sizes32_def] >> metis_tac[]) >>
  drule_all abi_encode_framed_array_index_init_run >> strip_tac >>
  `{st.cs_next_id} SUBSET ids` by simp[SUBSET_DEF] >>
  `EVERY (\r. venomMemDefs$regions_disjoint (sb,cap) r) []` by simp[] >>
  drule_all window_array_root_transition >> strip_tac >>
  qexistsl_tac [`t`, `b`] >> asm_rewrite_tac[] >>
  simp_tac bool_ss [window_array_cursor_def] >> asm_rewrite_tac[] >>
  qpat_x_assum `window_array_root _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t` mp_tac >>
  simp_tac bool_ss [window_array_root_def] >> metis_tac[]
QED

Theorem abi_encode_framed_array_root_prefix_run:
  window_array_root ctx func st ids ei asz msz active ty avs src dst sb cap d s /\
  abi_encode_array_prefix src dst st = ((pp,count_op),en) /\
  st.cs_next_id IN ids /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  fn_has_code st en func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t b. window_phase ctx func st en {st.cs_next_id} [(d,32)] s t /\
    window_array_transition ctx func st {st.cs_next_id} [(d,32)] s t /\
    window_array_root ctx func st ids ei asz msz active ty avs src dst sb cap d t /\
    abi_encoder_array_prefix ty avs 0 d t.vs_memory /\
    window_array_cursor T en pp st.cs_next_id b 0 sb cap d
      (LENGTH (enc (Array NONE ty) (ListV avs))) t /\
    eval_operand count_op t = SOME (n2w (LENGTH avs)) /\
    (!x. count_op = Var x ==> not_fresh_at en x) /\ abi_encode_exec_frame func s t
Proof
  strip_tac >>
  `abi_encoder_window_input (AbiDynArray ei asz msz active)
     (Array NONE ty) (ListV avs) sb cap s.vs_memory` by fs[window_array_root_def] >>
  `32 <= cap /\ mem_word_at sb s.vs_memory = n2w (LENGTH avs)` by
    (qpat_assum `abi_encoder_window_input _ _ _ _ _ _` mp_tac >>
     simp_tac (srw_ss()) [abi_encoder_window_array_iff] >> metis_tac[]) >>
  `32 <= LENGTH (enc (Array NONE ty) (ListV avs))` by
    (drule window_array_layout >> decide_tac) >>
  `?t b. window_phase ctx func st en {st.cs_next_id} [(d,32)] s t /\
    window_array_transition ctx func st {st.cs_next_id} [(d,32)] s t /\
    eval_operand pp t = SOME (n2w b) /\
    (!x. pp = Var x \/ count_op = Var x ==> not_fresh_at en x) /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (b,32) /\
    b+32 <= t.vs_alloca_next /\ b < dimword (:256) /\
    mem_word_at b t.vs_memory = 0w /\
    eval_operand count_op t = SOME (n2w (LENGTH avs)) /\
    mem_word_at d t.vs_memory = n2w (LENGTH avs) /\ abi_encode_exec_frame func s t` by
    (irule abi_encode_framed_array_prefix_run >> asm_rewrite_tac[] >>
     qpat_x_assum `window_array_root _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_array_root_def, window_sizes32_def] >> strip_tac >>
     asm_rewrite_tac[] >> conj_tac >- decide_tac >>
     qexistsl_tac [`dst`, `sb`, `src`] >> asm_rewrite_tac[] >>
     reverse conj_tac >- decide_tac >> rpt strip_tac >>
     `sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz) /\
       venomMemDefs$regions_disjoint
         (d,LENGTH (enc (Array NONE ty) (ListV avs))) (b,sz)` by metis_tac[] >>
     asm_rewrite_tac[] >>
     qpat_x_assum `venomMemDefs$regions_disjoint (sb,cap) (b,sz)` mp_tac >>
     qpat_x_assum `venomMemDefs$regions_disjoint (d,_) (b,sz)` mp_tac >>
     qpat_x_assum `32 <= cap` mp_tac >>
     qpat_x_assum `32 <= LENGTH _` mp_tac >>
     qpat_x_assum `sz = 32` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp_tac bool_ss [venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  suspend "finish"
QED

Resume abi_encode_framed_array_root_prefix_run[finish]:
  `{st.cs_next_id} SUBSET ids` by simp[SUBSET_DEF] >>
  `EVERY (\r. venomMemDefs$regions_disjoint (sb,cap) r) [(d,32)]` by
    (simp_tac (srw_ss()) [EVERY_DEF] >>
     `venomMemDefs$regions_disjoint (sb,cap)
        (d,LENGTH (enc (Array NONE ty) (ListV avs)))` by fs[window_array_root_def] >>
     qpat_x_assum `venomMemDefs$regions_disjoint (sb,cap) _` mp_tac >>
     qpat_x_assum `32 <= LENGTH _` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp_tac bool_ss [venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  drule_all window_array_root_transition >> strip_tac >>
  qexistsl_tac [`t`, `b`] >> asm_rewrite_tac[] >> conj_tac
  >- metis_tac[window_array_prefix_zero] >>
  conj_tac >- (simp_tac bool_ss [window_array_cursor_def] >> asm_rewrite_tac[] >>
    qpat_x_assum `window_array_root _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t` mp_tac >>
    simp_tac bool_ss [window_array_root_def] >> metis_tac[]) >> metis_tac[]
QED

Finalise abi_encode_framed_array_root_prefix_run

Theorem abi_encode_framed_array_root_dynamic_cursor_phase:
  window_array_root ctx func st ids ei asz msz active ty avs src dst sb cap d s /\
  emit_op ALLOCA [Lit 32w] st = (dp,c1) /\
  emit_op MUL [count_op;Lit (n2w asz)] c1 = (offset,c2) /\
  emit_void MSTORE [dp;offset] c2 = ((),en) /\ st.cs_next_id IN ids /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  fn_has_code st c1 func /\ fn_has_code c1 c2 func /\ fn_has_code c2 en func /\
  eval_operand count_op s = SOME (n2w (LENGTH avs)) /\
  (!x. count_op = Var x ==> not_fresh_at st x) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t b. window_phase ctx func st en {st.cs_next_id} [] s t /\
    window_array_transition ctx func st {st.cs_next_id} [] s t /\
    window_array_root ctx func st ids ei asz msz active ty avs src dst sb cap d t /\
    window_array_cursor T en dp st.cs_next_id b
      (LENGTH avs * abi_member_head_size ty) sb cap d
      (LENGTH (enc (Array NONE ty) (ListV avs))) t /\ abi_encode_exec_frame func s t
Proof
  strip_tac >>
  `alloca_room ctx func s /\ alloca_inv s /\
   (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = 32)` by
    (fs[window_array_root_def, window_sizes32_def] >> metis_tac[]) >>
  `asz = abi_member_head_size ty` by
    (qpat_assum `window_array_root _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s` mp_tac >>
     simp_tac bool_ss [window_array_root_def] >> strip_tac >>
     qpat_x_assum `abi_encoder_window_input _ _ _ _ _ _` mp_tac >>
     simp_tac (srw_ss()) [abi_encoder_window_array_iff] >> metis_tac[]) >>
  drule_all abi_encode_framed_array_dynamic_cursor_phase >> strip_tac >>
  `{st.cs_next_id} SUBSET ids` by simp[SUBSET_DEF] >>
  `EVERY (\r. venomMemDefs$regions_disjoint (sb,cap) r) []` by simp[] >>
  drule_all window_array_root_transition >> strip_tac >>
  qexistsl_tac [`t`, `b`] >> asm_rewrite_tac[] >>
  simp_tac bool_ss [window_array_cursor_def] >> asm_rewrite_tac[] >>
  qpat_x_assum `window_array_root _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t` mp_tac >>
  simp_tac bool_ss [window_array_root_def] >> metis_tac[]
QED

Theorem abi_encode_framed_array_root_tail_init_run:
  window_array_root ctx func st ids ei asz msz active ty avs src dst sb cap d s /\
  abi_encode_array_tail_init count_op asz st = (dp,en) /\
  st.cs_next_id IN ids /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  fn_has_code st en func /\
  eval_operand count_op s = SOME (n2w (LENGTH avs)) /\
  (!x. count_op = Var x ==> not_fresh_at st x) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t b. window_phase ctx func st en {st.cs_next_id} [] s t /\
    window_array_transition ctx func st {st.cs_next_id} [] s t /\
    window_array_root ctx func st ids ei asz msz active ty avs src dst sb cap d t /\
    window_array_cursor T en dp st.cs_next_id b
      (LENGTH avs * abi_member_head_size ty) sb cap d
      (LENGTH (enc (Array NONE ty) (ListV avs))) t /\ abi_encode_exec_frame func s t
Proof
  strip_tac >> drule window_array_tail_init_trace >> strip_tac >>
  `cs_extends st c1 /\ cs_extends c1 c2 /\ cs_extends c2 en` by
    metis_tac[ci_mono_emit_op, ci_mono_emit_void, ci_mono_def, pairTheory.SND] >>
  `fn_has_code st c1 func /\ fn_has_code c1 c2 func /\ fn_has_code c2 en func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  drule_all abi_encode_framed_array_root_dynamic_cursor_phase >> simp_tac bool_ss []
QED

Theorem abi_encode_framed_array_root_dynamic_init_steps:
  window_array_root ctx func st ids ei asz msz active ty avs src dst sb cap d s /\
  abi_decode_index_init st = (ip,mid) /\
  abi_encode_array_tail_init count_op asz mid = (dp,en) /\
  st.cs_next_id IN ids /\ mid.cs_next_id IN ids /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  MEM (mk_inst mid.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString mid.cs_next_var)]) (fn_insts func) /\
  fn_has_code st mid func /\ fn_has_code mid en func /\
  eval_operand count_op s = SOME (n2w (LENGTH avs)) /\
  (!x. count_op = Var x ==> not_fresh_at st x) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?u v bi bd.
    window_phase ctx func st mid {st.cs_next_id} [] s u /\
    window_phase ctx func mid en {mid.cs_next_id} [] u v /\
    window_array_transition ctx func st {st.cs_next_id} [] s u /\
    window_array_transition ctx func mid {mid.cs_next_id} [] u v /\
    window_array_root ctx func en ids ei asz msz active ty avs src dst sb cap d v /\
    window_array_cursor T en ip st.cs_next_id bi 0 sb cap d
      (LENGTH (enc (Array NONE ty) (ListV avs))) v /\
    window_array_cursor T en dp mid.cs_next_id bd
      (LENGTH avs * abi_member_head_size ty) sb cap d
      (LENGTH (enc (Array NONE ty) (ListV avs))) v /\
    eval_operand count_op v = SOME (n2w (LENGTH avs)) /\
    (!x. count_op = Var x ==> not_fresh_at en x) /\ abi_encode_exec_frame func s v
Proof
  strip_tac >>
  drule abi_decode_index_init_shape >> simp_tac bool_ss [] >> strip_tac >>
  drule abi_encode_array_tail_init_shape >> strip_tac >>
  `!x. not_fresh_at st x ==> not_fresh_at mid x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `st` >> simp[]) >>
  `!x. not_fresh_at mid x ==> not_fresh_at en x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `mid` >> simp[]) >>
  drule_all abi_encode_framed_array_root_index_init_run >> strip_tac >>
  rename1 `window_phase ctx func st mid _ [] s u` >>
  `window_array_root ctx func mid ids ei asz msz active ty avs src dst sb cap d u` by
    (irule window_array_root_owner_mono >> metis_tac[]) >>
  `eval_operand count_op u = SOME (n2w (LENGTH avs))` by
    (drule_all window_array_transition_eval >> metis_tac[]) >>
  `!x. count_op = Var x ==> not_fresh_at mid x` by metis_tac[] >>
  `~u.vs_halted /\ u.vs_current_bb = mid.cs_current_bb /\
    u.vs_inst_idx = LENGTH mid.cs_current_insts` by fs[window_phase_def] >>
  drule_all abi_encode_framed_array_root_tail_init_run >> strip_tac >>
  rename1 `window_phase ctx func mid en _ [] u v` >>
  `abi_encode_exec_frame func s v` by
    (irule abi_encode_exec_frame_trans >> qexists_tac `u` >> asm_rewrite_tac[]) >>
  suspend "finish"
QED

Resume abi_encode_framed_array_root_dynamic_init_steps[finish]:
  `window_array_cursor T mid ip st.cs_next_id b 0 sb cap d
     (LENGTH (enc (Array NONE ty) (ListV avs))) u` by
    (irule window_array_cursor_owner_mono >> metis_tac[]) >>
  `window_array_cursor T mid ip st.cs_next_id b 0 sb cap d
     (LENGTH (enc (Array NONE ty) (ListV avs))) v` by
    (irule window_array_cursor_frame >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[]) >>
  `eval_operand count_op v = SOME (n2w (LENGTH avs))` by
    (drule_all window_array_transition_eval >> metis_tac[]) >>
  qexistsl_tac [`u`, `v`, `b`, `b'`] >> asm_rewrite_tac[] >> rpt conj_tac >>
  FIRST [irule window_array_root_owner_mono,
         irule window_array_cursor_owner_mono, all_tac] >> metis_tac[]
QED

Finalise abi_encode_framed_array_root_dynamic_init_steps

Theorem abi_encode_framed_array_dynamic_init_trace[local]:
  abi_encode_array_dynamic_init count_op asz st = ((ip,dp),en) ==>
  ?mid. abi_decode_index_init st = (ip,mid) /\
    abi_encode_array_tail_init count_op asz mid = (dp,en)
Proof
  rewrite_tac[abi_encode_array_dynamic_init_split] >>
  simp_tac bool_ss [comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem abi_encode_framed_array_root_dynamic_init_run:
  window_array_root ctx func st ids ei asz msz active ty avs src dst sb cap d s /\
  abi_encode_array_dynamic_init count_op asz st = ((ip,dp),en) /\
  st.cs_next_id IN ids /\ st.cs_next_id+2 IN ids /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  MEM (mk_inst (st.cs_next_id+2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (st.cs_next_var+1))]) (fn_insts func) /\
  fn_has_code st en func /\
  eval_operand count_op s = SOME (n2w (LENGTH avs)) /\
  (!x. count_op = Var x ==> not_fresh_at st x) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t bi bd.
    window_phase ctx func st en {st.cs_next_id;st.cs_next_id+2} [] s t /\
    window_array_transition ctx func st {st.cs_next_id;st.cs_next_id+2} [] s t /\
    window_array_root ctx func en ids ei asz msz active ty avs src dst sb cap d t /\
    window_array_cursor T en ip st.cs_next_id bi 0 sb cap d
      (LENGTH (enc (Array NONE ty) (ListV avs))) t /\
    window_array_cursor T en dp (st.cs_next_id+2) bd
      (LENGTH avs * abi_member_head_size ty) sb cap d
      (LENGTH (enc (Array NONE ty) (ListV avs))) t /\
    eval_operand count_op t = SOME (n2w (LENGTH avs)) /\
    (!x. count_op = Var x ==> not_fresh_at en x) /\ abi_encode_exec_frame func s t
Proof
  strip_tac >> drule abi_encode_framed_array_dynamic_init_trace >> strip_tac >>
  drule abi_decode_index_init_shape >> simp_tac bool_ss [] >> strip_tac >>
  drule abi_encode_array_tail_init_shape >> strip_tac >>
  `cs_extends st mid /\ cs_extends mid en` by fs[inst_extends_def, cs_extends_def] >>
  `fn_has_code st mid func /\ fn_has_code mid en func` by metis_tac[fn_has_code_split] >>
  `mid.cs_next_id IN ids` by metis_tac[] >>
  `MEM (mk_inst mid.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString mid.cs_next_var)]) (fn_insts func)` by metis_tac[] >>
  drule_all abi_encode_framed_array_root_dynamic_init_steps >> strip_tac >>
  `window_phase ctx func st en {st.cs_next_id;st.cs_next_id+2} [] s v` by
    (irule window_phase_chain >>
     qexistsl_tac [`{st.cs_next_id}`, `[]`, `mid`, `{mid.cs_next_id}`, `[]`, `u`] >>
     asm_simp_tac (srw_ss()) [SUBSET_DEF]) >>
  `!R. window_sizes32 R s ==> window_sizes32 R v` by metis_tac[window_array_transition_sizes] >>
  `window_array_transition ctx func st {st.cs_next_id;st.cs_next_id+2} [] s v` by
    (irule window_array_phase_transition >> asm_rewrite_tac[] >>
     qexists_tac `en` >> asm_rewrite_tac[]) >>
  qexistsl_tac [`v`, `bi`, `bd`] >> asm_rewrite_tac[] >> metis_tac[]
QED

Theorem abi_encode_framed_array_dynamic_entry_run:
  window_array_root ctx func st ids ei asz msz T ty avs src dst sb cap d s /\
  abi_encode_array_prefix src dst st = ((pp,count_op),mid) /\
  abi_encode_array_dynamic_init count_op asz mid = ((ip,dp),owner) /\
  abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels /\
  st.cs_next_id IN ids /\ mid.cs_next_id IN ids /\ mid.cs_next_id+2 IN ids /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  MEM (mk_inst mid.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString mid.cs_next_var)]) (fn_insts func) /\
  MEM (mk_inst (mid.cs_next_id+2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (mid.cs_next_var+1))]) (fn_insts func) /\
  fn_has_code st mid func /\ fn_has_code mid owner func /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t pb bi bd.
    window_array_transition ctx func st ids [(d,32)] s t /\
    window_array_inv ctx func owner ids ei asz msz T ty avs src dst
      ip mid.cs_next_id bi dp (mid.cs_next_id+2) bd count_op (FST labels) sb cap d 0 t /\
    window_array_cursor T owner pp st.cs_next_id pb 0 sb cap d
      (LENGTH (enc (Array NONE ty) (ListV avs))) t /\ abi_encode_exec_frame func s t
Proof
  strip_tac >> drule abi_encode_array_prefix_shape >> strip_tac >>
  drule_all abi_encode_framed_array_root_prefix_run >> strip_tac >>
  rename1 `window_phase ctx func st mid _ _ s u` >>
  `!x. not_fresh_at st x ==> not_fresh_at mid x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `st` >> simp[]) >>
  `window_array_root ctx func mid ids ei asz msz T ty avs src dst sb cap d u` by
    (irule window_array_root_owner_mono >> metis_tac[]) >>
  `u.vs_current_bb = mid.cs_current_bb /\
    u.vs_inst_idx = LENGTH mid.cs_current_insts /\ ~u.vs_halted` by fs[window_phase_def] >>
  drule_all abi_encode_framed_array_root_dynamic_init_run >> strip_tac >>
  rename1 `window_phase ctx func mid owner _ _ u v` >>
  `abi_encode_exec_frame func s v` by
    (irule abi_encode_exec_frame_trans >> qexists_tac `u` >> asm_rewrite_tac[]) >>
  `abi_encode_exec_frame func v (jump_to (FST labels) v)` by
    simp[jump_to_def, abi_encode_exec_frame_def, pending_alloca_size_def] >>
  `abi_encode_exec_frame func s (jump_to (FST labels) v)` by
    (irule abi_encode_exec_frame_trans >> qexists_tac `v` >> asm_rewrite_tac[]) >>
  suspend "finish"
QED

Resume abi_encode_framed_array_dynamic_entry_run[finish]:
  `!x. not_fresh_at mid x ==> not_fresh_at owner x` by
    (drule abi_encode_framed_array_dynamic_init_trace >> strip_tac >>
     drule abi_decode_index_init_shape >> simp_tac bool_ss [] >> strip_tac >>
     drule abi_encode_array_tail_init_shape >> strip_tac >>
     rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `mid` >> simp[]) >>
  `window_array_cursor T mid pp st.cs_next_id b 0 sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) u` by
    (irule window_array_cursor_owner_mono >> metis_tac[]) >>
  `{mid.cs_next_id;mid.cs_next_id+2} SUBSET ids /\
   st.cs_next_id NOTIN {mid.cs_next_id;mid.cs_next_id+2}` by
    (asm_simp_tac (srw_ss()) [SUBSET_DEF] >> decide_tac) >>
  drule_all window_array_entry_from_init >> strip_tac >>
  `window_array_transition ctx func st ids [(d,32)] s u` by
    (qpat_assum `window_array_transition ctx func st {st.cs_next_id} [(d,32)] s u` mp_tac >>
     qpat_assum `st.cs_next_id IN ids` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >> irule window_array_transition_region >>
     goal_assum (drule_at Any) >> asm_simp_tac (srw_ss()) [SUBSET_DEF]) >>
  `window_array_transition ctx func st ids [(d,32)] u (jump_to (FST labels) v)` by
    (irule window_array_transition_owner_weaken >> qexists_tac `mid` >>
     asm_rewrite_tac[] >> irule window_array_transition_region >>
     goal_assum (drule_at Any) >> simp[]) >>
  qexistsl_tac [`jump_to (FST labels) v`, `b`, `bi`, `bd`] >>
  asm_rewrite_tac[] >> irule window_array_transition_trans >> metis_tac[]
QED

Finalise abi_encode_framed_array_dynamic_entry_run

Theorem abi_encode_framed_array_static_entry_run:
  window_array_root ctx func st ids ei asz msz F ty avs src dst sb cap d s /\
  abi_encode_array_prefix src dst st = ((pp,count_op),mid) /\
  abi_decode_index_init mid = (ip,owner) /\
  abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels /\
  st.cs_next_id IN ids /\ mid.cs_next_id IN ids /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  MEM (mk_inst mid.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString mid.cs_next_var)]) (fn_insts func) /\
  fn_has_code st mid func /\ fn_has_code mid owner func /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t pb bi.
    window_array_transition ctx func st ids [(d,32)] s t /\
    window_array_inv ctx func owner ids ei asz msz F ty avs src dst
      ip mid.cs_next_id bi (Lit 0w) 0 0 count_op (FST labels) sb cap d 0 t /\
    window_array_cursor T owner pp st.cs_next_id pb 0 sb cap d
      (LENGTH (enc (Array NONE ty) (ListV avs))) t /\ abi_encode_exec_frame func s t
Proof
  strip_tac >> drule abi_encode_array_prefix_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> simp_tac bool_ss [] >> strip_tac >>
  drule_all abi_encode_framed_array_root_prefix_run >> strip_tac >>
  rename1 `window_phase ctx func st mid _ _ s u` >>
  `!x. not_fresh_at st x ==> not_fresh_at mid x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `st` >> simp[]) >>
  `!x. not_fresh_at mid x ==> not_fresh_at owner x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `mid` >> simp[]) >>
  `window_array_root ctx func mid ids ei asz msz F ty avs src dst sb cap d u` by
    (irule window_array_root_owner_mono >> metis_tac[]) >>
  `u.vs_current_bb = mid.cs_current_bb /\
    u.vs_inst_idx = LENGTH mid.cs_current_insts /\ ~u.vs_halted` by fs[window_phase_def] >>
  drule_all abi_encode_framed_array_root_index_init_run >> strip_tac >>
  rename1 `window_phase ctx func mid owner _ _ u v` >>
  `abi_encode_exec_frame func s v` by
    (irule abi_encode_exec_frame_trans >> qexists_tac `u` >> asm_rewrite_tac[]) >>
  `abi_encode_exec_frame func v (jump_to (FST labels) v)` by
    simp[jump_to_def, abi_encode_exec_frame_def, pending_alloca_size_def] >>
  `abi_encode_exec_frame func s (jump_to (FST labels) v)` by
    (irule abi_encode_exec_frame_trans >> qexists_tac `v` >> asm_rewrite_tac[]) >>
  suspend "finish"
QED

Resume abi_encode_framed_array_static_entry_run[finish]:
  `window_array_root ctx func owner ids ei asz msz F ty avs src dst sb cap d v` by
    (irule window_array_root_owner_mono >> metis_tac[]) >>
  `eval_operand count_op v = SOME (n2w (LENGTH avs))` by
    (drule_all window_array_transition_eval >> metis_tac[]) >>
  `!x. count_op = Var x ==> not_fresh_at owner x` by metis_tac[] >>
  `window_array_cursor F owner (Lit 0w) 0 0
     (LENGTH avs * abi_member_head_size ty) sb cap d
     (LENGTH (enc (Array NONE ty) (ListV avs))) v` by simp[window_array_cursor_def] >>
  `{mid.cs_next_id} SUBSET ids /\ st.cs_next_id NOTIN {mid.cs_next_id}` by
    (asm_simp_tac (srw_ss()) [SUBSET_DEF] >> decide_tac) >>
  drule_all window_array_entry_from_init >> strip_tac >>
  `window_array_transition ctx func st ids [(d,32)] s u` by
    (qpat_assum `window_array_transition ctx func st {st.cs_next_id} [(d,32)] s u` mp_tac >>
     qpat_assum `st.cs_next_id IN ids` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >> irule window_array_transition_region >>
     goal_assum (drule_at Any) >> asm_simp_tac (srw_ss()) [SUBSET_DEF]) >>
  `window_array_transition ctx func st ids [(d,32)] u (jump_to (FST labels) v)` by
    (irule window_array_transition_owner_weaken >> qexists_tac `mid` >>
     asm_rewrite_tac[] >> irule window_array_transition_region >>
     goal_assum (drule_at Any) >> simp[]) >>
  `window_array_transition ctx func st ids [(d,32)] s (jump_to (FST labels) v)` by
    (irule window_array_transition_trans >> metis_tac[]) >>
  qexistsl_tac [`jump_to (FST labels) v`, `b`, `b'`] >> asm_rewrite_tac[] >> metis_tac[]
QED

Finalise abi_encode_framed_array_static_entry_run

Theorem abi_encode_framed_array_entry_run:
  window_array_root ctx func st ids ei asz msz active ty avs src dst sb cap d s /\
  abi_encode_array_prefix src dst st = ((pp,count_op),mid) /\
  (if active then abi_encode_array_dynamic_init count_op asz mid = ((ip,dp),owner)
   else abi_decode_index_init mid = (ip,owner) /\ dp = Lit 0w) /\
  abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels /\
  st.cs_next_id IN ids /\ mid.cs_next_id IN ids /\
  (active ==> mid.cs_next_id+2 IN ids) /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  MEM (mk_inst mid.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString mid.cs_next_var)]) (fn_insts func) /\
  (active ==> MEM (mk_inst (mid.cs_next_id+2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (mid.cs_next_var+1))]) (fn_insts func)) /\
  fn_has_code st mid func /\ fn_has_code mid owner func /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t pb bi bd.
    window_array_transition ctx func st ids [(d,32)] s t /\
    window_array_inv ctx func owner ids ei asz msz active ty avs src dst
      ip mid.cs_next_id bi dp (if active then mid.cs_next_id+2 else 0) bd
      count_op (FST labels) sb cap d 0 t /\
    window_array_cursor T owner pp st.cs_next_id pb 0 sb cap d
      (LENGTH (enc (Array NONE ty) (ListV avs))) t /\ abi_encode_exec_frame func s t
Proof
  Cases_on `active` >> simp_tac bool_ss [] >> strip_tac
  >- (drule_all abi_encode_framed_array_dynamic_entry_run >> simp_tac bool_ss []) >>
  drule_all abi_encode_framed_array_static_entry_run >> strip_tac >>
  qexistsl_tac [`t`, `pb`, `bi`, `0`] >> asm_rewrite_tac[]
QED

Theorem abi_encode_framed_array_constructor_entry:
  window_array_root ctx func st (window_alloca_sites func (frag_ids st en))
    ei asz msz active ty avs src dst sb cap d s /\
  abi_encode_array_prefix src dst st = ((pp,count_op),mid) /\
  (if active then abi_encode_array_dynamic_init count_op asz mid = ((ip,dp),owner)
   else abi_decode_index_init mid = (ip,owner) /\ dp = Lit 0w) /\
  abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels /\
  fn_has_code st mid func /\ fn_has_code mid owner func /\
  mid.cs_next_id = st.cs_next_id+4 /\
  owner.cs_next_id = mid.cs_next_id+(if active then 5 else 2) /\
  owner.cs_next_id <= en.cs_next_id /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  st.cs_next_id IN window_alloca_sites func (frag_ids st en) /\
  mid.cs_next_id IN window_alloca_sites func (frag_ids st en) /\
  (active ==> mid.cs_next_id+2 IN window_alloca_sites func (frag_ids st en)) /\
  ?t pb bi bd.
    window_array_transition ctx func st (window_alloca_sites func (frag_ids st en))
      [(d,32)] s t /\
    window_array_inv ctx func owner (window_alloca_sites func (frag_ids st en))
      ei asz msz active ty avs src dst ip mid.cs_next_id bi dp
      (if active then mid.cs_next_id+2 else 0) bd count_op (FST labels) sb cap d 0 t /\
    window_array_cursor T owner pp st.cs_next_id pb 0 sb cap d
      (LENGTH (enc (Array NONE ty) (ListV avs))) t /\ abi_encode_exec_frame func s t
Proof
  strip_tac >>
  `MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func)` by
    metis_tac[window_array_prefix_alloca_member] >>
  `MEM (mk_inst mid.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString mid.cs_next_var)]) (fn_insts func) /\
   (active ==> MEM (mk_inst (mid.cs_next_id+2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (mid.cs_next_var+1))]) (fn_insts func))` by
    (Cases_on `active` >> full_simp_tac bool_ss []
     >- (drule_all window_array_dynamic_alloca_members >> simp[]) >>
     drule_all window_array_index_alloca_member >> simp[]) >>
  `st.cs_next_id IN window_alloca_sites func (frag_ids st en)` by
    (simp_tac (srw_ss()) [window_alloca_sites_def, frag_ids_def] >>
     (conj_tac >- (Cases_on `active` >> gvs[] >> decide_tac)) >>
     qexists_tac `mk_inst st.cs_next_id ALLOCA [Lit 32w]
       [STRING #"%" (toString st.cs_next_var)]` >> asm_simp_tac (srw_ss()) [mk_inst_def]) >>
  `mid.cs_next_id IN window_alloca_sites func (frag_ids st en)` by
    (simp_tac (srw_ss()) [window_alloca_sites_def, frag_ids_def] >>
     (conj_tac >- (Cases_on `active` >> gvs[] >> decide_tac)) >>
     qexists_tac `mk_inst mid.cs_next_id ALLOCA [Lit 32w]
       [STRING #"%" (toString mid.cs_next_var)]` >> asm_simp_tac (srw_ss()) [mk_inst_def]) >>
  `(active ==> mid.cs_next_id+2 IN window_alloca_sites func (frag_ids st en))` by
    (strip_tac >> simp_tac (srw_ss()) [window_alloca_sites_def, frag_ids_def] >>
     (conj_tac >- (gvs[] >> decide_tac)) >>
     qexists_tac `mk_inst (mid.cs_next_id+2) ALLOCA [Lit 32w]
       [STRING #"%" (toString (mid.cs_next_var+1))]` >> asm_simp_tac (srw_ss()) [mk_inst_def]) >>
  drule_all abi_encode_framed_array_entry_run >> strip_tac >> asm_rewrite_tac[] >>
  qexistsl_tac [`t`, `pb`, `bi`, `bd`] >> gvs[]
QED

Theorem abi_encode_framed_array_contract:
  abi_encode_framed_contract ei ==>
  abi_encode_framed_contract (AbiDynArray ei asz msz active)
Proof
  strip_tac >> simp_tac bool_ss [abi_encode_framed_contract_def] >>
  rpt gen_tac >> strip_tac >>
  drule window_array_pre_root >> strip_tac >> gvs[] >>
  `fn_has_code st st' func /\ abi_encoder_admissible (AbiDynArray ei asz msz active)` by
    fs[abi_encoder_window_pre_def] >>
  drule_all abi_encode_array_context >> strip_tac >>
  drule_all window_array_loop_context >> strip_tac >>
  PairCases_on `ops` >>
  rename1 `abi_encode_array_prefix src dst st = ((pp,count_op),loop_st)` >>
  suspend "code"
QED

Resume abi_encode_framed_array_contract[code]:
  full_simp_tac bool_ss [pairTheory.FST, pairTheory.SND] >>
  drule window_array_loop_code_bounds >> strip_tac >>
  `owner.cs_next_id <= st'.cs_next_id` by decide_tac >>
  `~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
   s.vs_inst_idx = LENGTH st.cs_current_insts` by fs[abi_encoder_window_pre_def] >>
  drule_all abi_encode_framed_array_constructor_entry >> strip_tac >>
  rename1 `window_array_transition ctx func st _ [(d,32)] s entry` >>
  qabbrev_tac `ids = window_alloca_sites func (frag_ids st st')` >>
  qabbrev_tac `loop_ids = ids DELETE st.cs_next_id` >>
  `window_alloca_sites func (frag_ids body_st body_end) SUBSET ids /\
   loop_st.cs_next_id NOTIN window_alloca_sites func (frag_ids body_st body_end) /\
   loop_st.cs_next_id+2 NOTIN window_alloca_sites func (frag_ids body_st body_end) /\
   st.cs_next_id NOTIN window_alloca_sites func (frag_ids body_st body_end)` by
    (simp_tac bool_ss [Abbr `ids`] >> irule window_array_body_sites >>
     conj_tac >- decide_tac >>
     conj_tac >- (qexists_tac `loop_end` >> asm_rewrite_tac[] >> decide_tac) >>
     qexistsl_tac [`active`, `count_op`, `exit_st`, `ip`, `labels`, `owner`] >>
     asm_rewrite_tac[]) >>
  `window_alloca_sites func (frag_ids body_st body_end) SUBSET loop_ids /\
   loop_st.cs_next_id IN loop_ids /\
   (active ==> (if active then loop_st.cs_next_id+2 else 0) IN loop_ids /\
    (if active then loop_st.cs_next_id+2 else 0) <> loop_st.cs_next_id) /\
   st.cs_next_id NOTIN loop_ids /\ loop_ids SUBSET ids` by
    (simp_tac (srw_ss()) [Abbr `loop_ids`, SUBSET_DEF] >>
     rpt conj_tac >> rpt strip_tac >> gvs[] >> fs[SUBSET_DEF] >> metis_tac[]) >>
  `window_array_inv ctx func owner loop_ids ei asz msz active ty avs src dst
    ip loop_st.cs_next_id bi dp (if active then loop_st.cs_next_id+2 else 0) bd
    count_op (FST labels) sb cap d 0 entry` by
    (irule window_array_inv_sites_subset >> goal_assum (drule_at Any) >> asm_rewrite_tac[]) >>
  suspend "loop"
QED

Resume abi_encode_framed_array_contract[loop]:
  `(active ==> (if active then loop_st.cs_next_id+2 else 0) NOTIN
    window_alloca_sites func (frag_ids body_st body_end))` by (Cases_on `active` >> gvs[]) >>
  `(active ==> (if active then loop_st.cs_next_id+2 else 0) IN loop_ids /\
    (if active then loop_st.cs_next_id+2 else 0) NOTIN
      window_alloca_sites func (frag_ids body_st body_end) /\
    (if active then loop_st.cs_next_id+2 else 0) <> loop_st.cs_next_id)` by metis_tac[] >>
  drule_all abi_encode_framed_array_loop_parent >> strip_tac >>
  rename1 `window_array_transition ctx func owner loop_ids _ entry completed` >>
  `abi_encode_exec_frame func s completed` by
    (irule abi_encode_exec_frame_trans >> qexists_tac `entry` >> asm_rewrite_tac[]) >>
  `window_array_inv ctx func owner loop_ids ei asz msz active ty avs src dst
    ip loop_st.cs_next_id bi dp (if active then loop_st.cs_next_id+2 else 0) bd
    count_op exit_st.cs_current_bb sb cap d (LENGTH avs) completed` by metis_tac[] >>
  drule_all abi_encode_framed_array_exit_parent >> strip_tac >>
  `abi_encode_exec_frame func s t` by
    (irule abi_encode_exec_frame_trans >> qexists_tac `completed` >> asm_rewrite_tac[]) >>
  suspend "package"
QED

Resume abi_encode_framed_array_contract[package]:
  `!x. not_fresh_at st x ==> not_fresh_at owner x` by
    (rpt strip_tac >> irule not_fresh_at_mono >>
     qexists_tac `st` >> asm_rewrite_tac[] >> decide_tac) >>
  `window_array_transition ctx func st ids
    [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] entry completed` by
    (irule window_array_transition_owner_weaken >> qexists_tac `owner` >>
     asm_rewrite_tac[] >> irule window_array_transition_region >>
     qexistsl_tac [`loop_ids`, `[(d,LENGTH (enc (Array NONE ty) (ListV avs))) ]`] >>
     asm_rewrite_tac[] >> simp[]) >>
  `window_array_transition ctx func st ids
    [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] completed t` by
    (irule window_array_transition_owner_weaken >> qexists_tac `owner` >>
     asm_rewrite_tac[] >> irule window_array_transition_region >>
     qexistsl_tac [`{st.cs_next_id}`, `[]`] >> asm_rewrite_tac[] >> simp[]) >>
  `32 <= LENGTH (enc (Array NONE ty) (ListV avs))` by
    (`abi_encoder_window_input (AbiDynArray ei asz msz active)
       (Array NONE ty) (ListV avs) sb cap s.vs_memory` by fs[window_array_root_def] >>
     drule window_array_layout >> decide_tac) >>
  `window_array_transition ctx func st ids
    [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] s entry` by
    (irule window_array_transition_region >> qexistsl_tac [`ids`, `[(d,32)]`] >>
     asm_rewrite_tac[] >> simp[]) >>
  `window_array_transition ctx func st ids
    [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] s t` by
    (irule window_array_transition_trans >> qexists_tac `entry` >> asm_rewrite_tac[] >>
     irule window_array_transition_trans >> qexists_tac `completed` >> asm_rewrite_tac[]) >>
  suspend "result"
QED

Resume abi_encode_framed_array_contract[result]:
  `window_sizes32 ids s` by fs[window_array_root_def] >>
  `window_sizes32 ids t` by
    (qpat_x_assum `window_array_transition ctx func st ids _ s t` mp_tac >>
     simp_tac bool_ss [window_array_transition_def] >>
     strip_tac >> first_x_assum irule >> asm_rewrite_tac[]) >>
  qpat_x_assum `window_array_transition ctx func st ids _ s t` mp_tac >>
  simp_tac bool_ss [window_array_transition_def] >> strip_tac >>
  `abi_encoder_registered_effect (frag_ids st st')
    [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] s t` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl_tac [`ids`, `[(d,LENGTH (enc (Array NONE ty) (ListV avs))) ]`] >>
     asm_rewrite_tac[] >> simp_tac bool_ss [Abbr `ids`] >> irule window_alloca_sites_subset) >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  simp_tac bool_ss [window_strong_result_def, abi_encoder_window_result_def] >>
  asm_rewrite_tac[] >>
  conj_tac >- metis_tac[abi_encoder_extend_sim_sim] >>
  qpat_x_assum `window_sizes32 ids t` mp_tac >>
  simp_tac bool_ss [window_sizes32_def, Abbr `ids`] >> strip_tac >> asm_rewrite_tac[]
QED

Finalise abi_encode_framed_array_contract
