(* Shared-witness safe allocation and initialization of array cursors. *)
Theory abiEncoderWindowArrayCursorMem
Ancestors
  abiEncoderWindowArrayCursorInitGrowthMem
  abiEncoderWindowArrayEntry windowPhaseMem windowTransitionMem
  abiEncoderWindowPhaseFrameMem abiEncoderWindowMemFrame
  abiEncoderWindowSequenceFrameMem abiEncoderSharedArrayOuter abiDecoderVarSequence
  abiEncoderWindowLoopMem abiEncoderRegisteredEffect abiEncoderPrimitiveEffect
  abiEncoderWindowPhase abiEncoderWindowArrayInvariant abiEncoderWindowArrayBody freshWrites
  abiEncoderWindowStructuralMembers abiDecoderIndexInit context compileEnv emitHelper fragExec
  emitHelperProps exprLoweringProps valueEncodingProps venomState finite_map pred_set
  words arithmetic abiEncoderWindowArrayFinish abiEncoderArrayPhases
  abiEncoderWindowSequence windowSequenceMem fragExecMem allocaFootprint
  instMemFrontier venomExecSemantics venomMemDefs venomInst list abiEncoderWindowLeaves abiEncoderWindowContract

Theorem window_array_cursor_init_phase_mem:
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
    (fn_inst_ids_distinct func ==> window_mem_frame ctx func s t)
Proof
  strip_tac >> drule_all
    abiEncoderWindowArrayCursorInitGrowthMemTheory.window_array_cursor_init_phase_growth_mem >>
  strip_tac >> qexistsl [`t`, `b`] >> asm_rewrite_tac[]
QED

Theorem window_array_index_init_run_mem:
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
    (fn_inst_ids_distinct func ==> window_mem_frame ctx func s t)
Proof
  strip_tac >> drule_all
    abiEncoderWindowArrayCursorInitGrowthMemTheory.window_array_index_init_run_growth_mem >>
  strip_tac >> qexistsl [`t`, `b`] >> asm_rewrite_tac[]
QED

Theorem window_array_finish_mem_checks[local]:
  abi_encode_array_finish pp size_op st = (out,en) /\
  eval_operand pp s = SOME (n2w slot) /\ slot < dimword (:256) /\
  slot+32 <= s.vs_alloca_next /\ eval_operand size_op s = SOME w /\
  (!x. pp = Var x \/ size_op = Var x ==> not_fresh_at st x) ==>
  run_inst_seq_mem_ok (emitted_insts st en) s
Proof
  simp_tac bool_ss [abi_encode_array_finish_def, comp_bind_def,
    comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  rename1 `emit_op MLOAD [pp] st = (old,c1)` >>
  rename1 `emit_op ADD [old;size_op] c1 = (next,c2)` >>
  rename1 `emit_void MSTORE [pp;next] c2 = ((),c3)` >>
  `inst_extends st c1 /\ inst_extends c1 c2 /\
   inst_extends c2 c3 /\ inst_extends c3 en` by
    metis_tac[inst_extends_emit_op, inst_extends_emit_void] >>
  `emitted_insts st en = emitted_insts st c1 ++
    (emitted_insts c1 c2 ++ (emitted_insts c2 c3 ++ emitted_insts c3 en))` by
    metis_tac[emitted_insts_append, inst_extends_def, inst_extends_trans] >>
  qpat_x_assum `emitted_insts st en = _` (fn th => pure_rewrite_tac [th]) >>
  match_mp_tac run_inst_seq_mem_ok_append >> conj_tac
  >- (qpat_assum `emit_op MLOAD [pp] st = _` (mp_then Any mp_tac emit_mload_mem_ok) >>
      disch_then irule >> simp[]) >>
  rpt strip_tac >>
  `?t. window_pure_seq st c1 s t /\ eval_operand old t = SOME (mload slot s)` by
    metis_tac[window_emit_load_pure] >>
  `t = s'` by fs[window_pure_seq_def, window_seq_def] >> gvs[] >>
  `eval_operand size_op s' = SOME w` by
    metis_tac[window_seq_eval, window_pure_seq_def] >>
  `?u. window_pure_seq c1 c2 s' u /\
       eval_operand next u = SOME (mload slot s + w)` by
    metis_tac[window_emit_add_pure] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  match_mp_tac run_inst_seq_mem_ok_append >> conj_tac
  >- (qpat_assum `emit_op ADD _ _ = _` (mp_then Any mp_tac emit_op_mem_ok) >>
      disch_then irule >> simp[] >> irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  rpt strip_tac >>
  `u = s''` by fs[window_pure_seq_def, window_seq_def] >> gvs[] >>
  `eval_operand pp s'' = SOME (n2w slot) /\
   slot+32 <= s''.vs_alloca_next` by
    (conj_tac >- metis_tac[window_seq_eval, window_pure_seq_chain, window_pure_seq_def] >>
     fs[window_pure_seq_def]) >>
  match_mp_tac run_inst_seq_mem_ok_append >> conj_tac
  >- (drule emit_mstore_mem_ok >> disch_then irule >> simp[]) >>
  rpt strip_tac >>
  drule_all window_emit_store_run >> strip_tac >> gvs[] >>
  qpat_assum `emit_op MLOAD [pp] c3 = _` (mp_then Any mp_tac emit_mload_mem_ok) >>
  disch_then irule >>
  simp[eval_operand_mstore, mstore_def, write_memory_with_expansion_def]
QED

Theorem window_array_parent_finish_mem:
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
    (!x. out = Var x ==> not_fresh_at en x) /\ mem_cont_sim ctx func s t /\
    (fn_inst_ids_distinct func ==> window_mem_frame ctx func s t)
Proof
  strip_tac >>
  `slot+32 <= s.vs_alloca_next` by
    (irule alloca_region_below_frontier >>
     fs[alloca_inv_def] >> goal_assum (drule_at Any) >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts st en) s` by
    metis_tac[window_array_finish_mem_checks] >>
  drule_all window_array_parent_finish_seq >> strip_tac >>
  `raw.vs_allocas = s.vs_allocas /\ raw.vs_alloca_next = s.vs_alloca_next /\
   raw.vs_halted = s.vs_halted /\ raw.vs_current_bb = s.vs_current_bb` by
    fs[window_pure_seq_def, mstore_def, write_memory_with_expansion_def] >>
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
     (raw with vs_inst_idx := LENGTH en.cs_current_insts)` by
    metis_tac[window_seq_phase] >>
  `mem_cont_sim ctx func s (raw with vs_inst_idx := LENGTH en.cs_current_insts)` by
    metis_tac[window_seq_mem_cont] >>
  `fn_inst_ids_distinct func ==>
   window_mem_frame ctx func s (raw with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (strip_tac >> drule abi_encoder_array_finish_opcodes >> strip_tac >>
     irule window_seq_mem_frame >> simp[] >> qexists `st` >> simp[] >>
     fs[EVERY_MEM, abi_decoder_reentry_opcode_def] >> metis_tac[]) >>
  qexists_tac `raw with vs_inst_idx := LENGTH en.cs_current_insts` >>
  asm_rewrite_tac[] >> conj_tac
  >- (irule window_array_phase_transition >> conj_tac
      >- simp[window_sizes32_def] >> goal_assum (drule_at Any)) >>
  Cases_on `out` >> fs[eval_operand_def, lookup_var_def]
QED
