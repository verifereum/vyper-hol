(* Bounded same-endpoint memory companions for finite array body phases. *)
Theory abiEncoderWindowArrayBodyMem
Ancestors
  abiEncoderWindowArrayBody abiEncoderWindowArrayCursorMem windowPhaseMem
  windowSequenceMem allocaFootprint instMemFrontier abiEncoderArrayTail
  abiEncoderArrayCode abiEncoderArrayBodyCode abiDecoderDynamicLoopSetup
  abiEncoderWindowSequence abiEncoderWindowPhase emitHelperProps emitHelper
  compileEnv loweringStateRelDefs exprLoweringProps fragExec fragExecMem venomState venomExecSemantics venomInst
  words list rich_list pred_set finite_map instIdxIndep memSafeRun
  abiEncoderWindowChild abiEncoderWindowArrayInvariant abiEncoderRegisteredEffect
  valueEncoding valueEncodingProps venomMemDefs windowTransitionMem memContinuation
  abiEncoderWindowContract abiEncoderInputFrame

Theorem window_array_tail_seq_mem[local]:
  abi_encode_array_tail data_op dp st = (ops,en) /\
  eval_operand dp s = SOME (n2w slot) /\ slot < dimword (:256) /\
  slot+32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts st en) s
Proof
  simp_tac bool_ss [abi_encode_array_tail_def, comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  rename1 `emit_op MLOAD [dp] st = (offset,mid)` >>
  rename1 `emit_op ADD [data_op;offset] mid = (child_dst,en)` >>
  `inst_extends st mid /\ inst_extends mid en` by metis_tac[inst_extends_emit_op] >>
  `emitted_insts st en = emitted_insts st mid ++ emitted_insts mid en` by
    metis_tac[emitted_insts_append, inst_extends_def, inst_extends_trans] >>
  asm_rewrite_tac[] >> match_mp_tac run_inst_seq_mem_ok_append >> conj_tac
  >- (drule emit_mload_mem_ok >> disch_then irule >> simp[]) >>
  rpt strip_tac >> drule emit_op_mem_ok >> disch_then irule >> simp[] >>
  irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem window_array_tail_phase_mem:
  abi_encode_array_tail data_op dp st = (ops,en) /\
  eval_operand dp s = SOME (n2w slot) /\ slot < dimword (:256) /\
  slot+32 <= s.vs_alloca_next /\
  mload slot s = n2w off /\ eval_operand data_op s = SOME (n2w d) /\
  (!x. data_op = Var x ==> not_fresh_at st x) /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st en {} [] s t /\
    eval_operand (FST ops) t = SOME (n2w off) /\
    eval_operand (SND ops) t = SOME (n2w (d+off)) /\
    (!x. FST ops = Var x \/ SND ops = Var x ==> not_fresh_at en x) /\
    mem_cont_sim ctx func s t
Proof
  strip_tac >> drule_all window_array_tail_pure >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts st en) s` by
    (drule_all window_array_tail_seq_mem >> simp[]) >>
  `mem_cont_sim ctx func s (t with vs_inst_idx := LENGTH en.cs_current_insts)` by
    metis_tac[window_seq_mem_cont, window_pure_seq_def] >>
  qexists_tac `t with vs_inst_idx := LENGTH en.cs_current_insts` >>
  (conj_tac >- metis_tac[window_pure_seq_phase]) >>
  simp_tac (srw_ss()) [eval_op_inst_idx] >> asm_rewrite_tac[]
QED

Theorem window_array_load_arithmetic_mem[local]:
  eval_operand op s = SOME (n2w slot) /\ slot < dimword (:256) /\
  slot+32 <= s.vs_alloca_next /\ EVERY (\i. i.inst_opcode = ADD \/ i.inst_opcode = MUL) rest ==>
  run_inst_seq_mem_ok (mk_inst id MLOAD [op] outs :: rest) s
Proof
  strip_tac >>
  `run_inst_seq_mem_ok [mk_inst id MLOAD [op] outs] s` by
    simp[run_inst_seq_mem_ok_last, below_frontier_MLOAD, inst_dload_in_section_def,
      mk_inst_def] >>
  `run_inst_seq_mem_ok ([mk_inst id MLOAD [op] outs] ++ rest) s` suffices_by simp[] >>
  match_mp_tac run_inst_seq_mem_ok_append >> asm_rewrite_tac[] >> rpt strip_tac >>
  irule run_inst_seq_mem_ok_every >> fs[EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  simp[inst_dload_in_section_def] >> irule below_frontier_no_ranges >> simp[]
QED

Theorem window_array_addresses_seq_mem[local]:
  abi_encode_array_addresses ip src dst asz msz st = (coords,en) /\
  eval_operand ip s = SOME (n2w slot) /\ slot < dimword (:256) /\
  slot+32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts st en) s
Proof
  simp[abi_encode_array_addresses_def, abi_decode_array_head_setup_def,
    abi_decode_indexed_coordinates_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND] >>
  irule window_array_load_arithmetic_mem >> simp[mk_inst_def] >>
  qexists_tac `slot` >> simp[]
QED

Theorem window_array_addresses_phase_mem:
  abi_encode_array_addresses ip src dst asz msz st = (coords,en) /\
  eval_operand ip s = SOME (n2w slot) /\ slot < dimword (:256) /\
  slot+32 <= s.vs_alloca_next /\
  mload slot s = n2w j /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand dst s = SOME (n2w d) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st en {} [] s t /\
    eval_operand (FST (FST coords)) t = SOME (n2w j) /\
    eval_operand (SND (FST coords)) t = SOME (n2w (sb+32+j*msz)) /\
    eval_operand (FST (SND coords)) t = SOME (n2w (d+32)) /\
    eval_operand (SND (SND coords)) t = SOME (n2w (d+32+j*asz)) /\
    (!x. FST (FST coords) = Var x \/ SND (FST coords) = Var x \/
         FST (SND coords) = Var x \/ SND (SND coords) = Var x ==> not_fresh_at en x) /\
    mem_cont_sim ctx func s t
Proof
  strip_tac >> drule_all window_array_addresses_pure >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts st en) s` by
    (drule_all window_array_addresses_seq_mem >> simp[]) >>
  `mem_cont_sim ctx func s (t with vs_inst_idx := LENGTH en.cs_current_insts)` by
    metis_tac[window_seq_mem_cont, window_pure_seq_def] >>
  qexists_tac `t with vs_inst_idx := LENGTH en.cs_current_insts` >>
  (conj_tac >- metis_tac[window_pure_seq_phase]) >>
  simp_tac (srw_ss()) [eval_op_inst_idx] >> asm_rewrite_tac[]
QED

Theorem window_array_suffix_prefix_mem[local]:
  emit_void MSTORE [head;offset] st = ((),a) /\
  emit_op ADD [offset;len] a = (next,b) /\ a.cs_next_var = st.cs_next_var /\
  fn_has_code st a func /\ fn_has_code a b func /\
  eval_operand head s = SOME (n2w h) /\ eval_operand offset s = SOME (n2w off) /\
  eval_operand dp s = SOME (n2w slot) /\ eval_operand len s = SOME (n2w n) /\
  (!x. dp = Var x \/ len = Var x ==> not_fresh_at st x) /\
  h < dimword (:256) /\ h+32 <= s.vs_alloca_next /\
  alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st b {} [(h,32)] s t /\ mem_cont_sim ctx func s t /\
    eval_operand next t = SOME (n2w (off+n)) /\
    eval_operand dp t = SOME (n2w slot) /\ eval_operand len t = SOME (n2w n) /\
    mem_word_at h t.vs_memory = n2w off
Proof
  strip_tac >>
  drule_all window_output_store_phase_mem >> strip_tac >>
  qabbrev_tac `u = (mstore h (n2w off) s) with vs_inst_idx := LENGTH a.cs_current_insts` >>
  `eval_operand offset u = SOME (n2w off) /\ eval_operand dp u = SOME (n2w slot) /\
   eval_operand len u = SOME (n2w n)` by
    (simp[Abbr `u`, eval_operand_def, lookup_var_def, mstore_def,
      write_memory_with_expansion_def] >> Cases_on `offset` >> Cases_on `dp` >> Cases_on `len` >>
     fs[eval_operand_def, lookup_var_def]) >>
  `alloca_inv u /\ alloca_room ctx func u /\ ~u.vs_halted /\
   u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts` by
    metis_tac[window_phase_resources, window_phase_control] >>
  drule_all window_emit_add_phase_mem >> strip_tac >>
  `eval_operand dp t = SOME (n2w slot) /\ eval_operand len t = SOME (n2w n)` by
    (conj_tac >> irule window_phase_eval >>
     goal_assum (drule_at Any) >> simp[] >> fs[not_fresh_at_def] >> metis_tac[]) >>
  `mem_word_at h t.vs_memory = n2w off` by
    (`mem_bytes_at h 32 t.vs_memory = mem_bytes_at h 32 u.vs_memory` by
       (irule abi_encoder_window_effect_bytes >> qexistsl_tac [`{}`, `[]`] >>
        simp[] >> metis_tac[window_phase_effect]) >>
     drule abiEncoderInputFrameTheory.abi_encoder_window_word >>
     disch_then (qspec_then `0` mp_tac) >> simp[Abbr `u`, mstore_mem_word_at_same]) >>
  qexists_tac `t` >> simp[GSYM word_add_n2w] >> irule window_phase_chain_mem >>
  qexistsl_tac [`{}`, `[(h,32)]`, `a`, `{}`, `[]`, `u`] >> simp[]
QED

Theorem window_array_suffix_run_mem:
  abi_encode_child_suffix head dp offset len st = (out,en) /\
  fn_has_code st en func /\
  eval_operand head s = SOME (n2w h) /\ eval_operand offset s = SOME (n2w off) /\
  eval_operand dp s = SOME (n2w slot) /\ eval_operand len s = SOME (n2w n) /\
  (!x. dp = Var x \/ len = Var x ==> not_fresh_at st x) /\
  FLOOKUP s.vs_allocas site = SOME (slot,32) /\
  h < dimword (:256) /\ slot < dimword (:256) /\
  h+32 <= s.vs_alloca_next /\ (h+32 <= slot \/ slot+32 <= h) /\
  alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_array_transition ctx func st {site} [(h,32)] s t /\
    mem_word_at h t.vs_memory = n2w off /\
    mem_word_at slot t.vs_memory = n2w (off+n) /\
    FLOOKUP t.vs_allocas site = SOME (slot,32) /\
    eval_operand out t = SOME (n2w n) /\
    t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts /\ mem_cont_sim ctx func s t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all window_child_suffix_context >> strip_tac >>
  qpat_x_assum `out = len` SUBST_ALL_TAC >>
  drule_all window_array_suffix_prefix_mem >> strip_tac >>
  `alloca_inv t /\ alloca_room ctx func t /\ ~t.vs_halted /\
   t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts` by
    metis_tac[window_phase_resources, window_phase_control] >>
  `FLOOKUP t.vs_allocas site = SOME (slot,32)` by
    (irule abi_encoder_registered_effect_allocated >>
     qexistsl_tac [`{}`, `[(h,32)]`, `s`] >> simp[] >> metis_tac[window_phase_effect]) >>
  `slot+32 <= t.vs_alloca_next` by
    (irule alloca_region_below_frontier >> fs[alloca_inv_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  drule_all window_cursor_store_phase_mem >> strip_tac >>
  qabbrev_tac `u = (mstore slot (n2w (off+n)) t) with vs_inst_idx := LENGTH en.cs_current_insts` >>
  `window_phase ctx func st en {site} [(h,32)] s u /\ mem_cont_sim ctx func s u` by
    (irule window_phase_chain_mem >>
     qexistsl_tac [`{}`, `[(h,32)]`, `b`, `{site}`, `[]`, `t`] >> simp[]) >>
  `FLOOKUP u.vs_allocas site = SOME (slot,32)` by
    simp[Abbr `u`, mstore_def, write_memory_with_expansion_def] >>
  `window_sizes32 {site} u` by simp[window_sizes32_def] >>
  qexists_tac `u` >> asm_rewrite_tac[] >> rpt conj_tac
  >- metis_tac[window_array_phase_sizes_transition]
  >- (simp[Abbr `u`] >> metis_tac[mstore_mem_word_at_disjoint])
  >- simp[Abbr `u`, mstore_mem_word_at_same]
  >- (Cases_on `len` >> fs[Abbr `u`, eval_operand_def, lookup_var_def,
        mstore_def, write_memory_with_expansion_def]) >>
  metis_tac[window_phase_control]
QED
