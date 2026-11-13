(* The counted encoder endpoint feeds the external-call calldata suffix. *)
Theory extcallCalldataSuffixMemory
Ancestors
  exprSimAbiEncodeExecFrame
  abiEncoderWindowRunMem abiEncoderWindowContract abiEncoderWindowPhase
  windowPhaseMem extcallCalldataOpsMemory fragGasPathMem fragGasPathFrameMem
  abiEncoderRegisteredEffect abiEncoderProps allocaSiteResource
  memoryReadProps abiCanonicalHeadSize valueEncodingProps valueEncodingProofs
  exprLoweringProps emitHelperProps emitHelper compileEnv freshWrites venomState venomMemDefs
  venomExecSemantics words finite_map pred_set list arithmetic memContinuation

Theorem extcall_selector_prefix_frame[local]:
  window_phase ctx func st en ids [(b+32,len)] s t /\
  FLOOKUP s.vs_allocas site = SOME (b,registered_size) /\ 32 <= registered_size /\ site NOTIN ids ==>
  mem_bytes_at b 32 t.vs_memory = mem_bytes_at b 32 s.vs_memory
Proof
  strip_tac >>
  `abi_encoder_registered_effect ids [(b+32,len)] s t /\ alloca_inv t` by
    metis_tac[window_phase_effect, window_phase_resources] >>
  `FLOOKUP t.vs_allocas site = SOME (b,registered_size)` by
    metis_tac[abi_encoder_registered_effect_allocated] >>
  irule abi_encoder_window_effect_bytes >>
  qexistsl_tac [`ids`, `[(b+32,len)]`] >>
  simp[venomMemDefsTheory.regions_disjoint_def] >> rpt strip_tac >>
  `venomMemDefs$regions_disjoint (b,registered_size) (b',sz)` by
    (irule alloca_site_registered_disjoint >> metis_tac[]) >>
  gvs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem extcall_encoded_calldata_suffix_resources_mem:
  compile_abi_encode_to_buf dst argbuf ei se = (encoded,sen) /\
  abi_encoder_window_pre ctx func se sen dst argbuf ei at av tb cap (b+32) s /\
  emit_op ADD [encoded; Lit 4w] sen = (call_len,slen) /\
  emit_op ADD [buf; Lit 28w] slen = (call_offset,sp) /\
  fn_has_code sen slen func /\ fn_has_code slen sp func /\
  eval_operand buf s = SOME (n2w b) /\
  (!x. buf = Var x ==> not_fresh_at se x) /\
  FLOOKUP s.vs_allocas buf_id = SOME (b,MAX args_size ret_size+32) /\
  buf_id < se.cs_next_id /\ LENGTH (enc at av) <= args_size /\
  mem_bytes_at b 32 s.vs_memory = word_to_bytes (n2w method_id : bytes32) T /\
  alloca_history func s ==>
  ?encoded_state t path_count.
    window_strong_result ctx func se sen encoded at av (b+32) s encoded_state /\
    abi_encode_exec_frame func s encoded_state /\ abi_encode_exec_frame func s t /\
    window_phase ctx func sen sp {} [] encoded_state t /\
    window_phase ctx func se sp (window_alloca_sites func (frag_ids se sen))
      [(b+32,LENGTH (enc at av))] s t /\
    gas_path_mem ctx func s path_count (OK t) /\ mem_cont_sim ctx func s t /\
    alloca_history func t /\
    eval_operand buf t = SOME (n2w b) /\
    eval_operand call_offset t = SOME (n2w (b+28)) /\
    eval_operand call_len t = SOME (n2w (LENGTH (enc at av)+4)) /\
    FLOOKUP t.vs_allocas buf_id = SOME (b,MAX args_size ret_size+32) /\
    read_memory (b+28) (4+LENGTH (enc at av)) t =
      DROP 28 (word_to_bytes (n2w method_id : bytes32) T) ++ enc at av /\
    (b+28)+(4+LENGTH (enc at av)) <= t.vs_alloca_next /\
    b+28 < dimword (:256) /\ LENGTH (enc at av)+4 < dimword (:256)
Proof
  strip_tac >>
  `abi_encoder_admissible ei /\ alloca_inv s /\ alloca_room ctx func s /\
   fn_inst_ids_distinct func` by
    (qpat_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[abi_encoder_window_pre_def] >> strip_tac >> asm_rewrite_tac[]) >>
  `b+(MAX args_size ret_size+32) <= s.vs_alloca_next` by
    metis_tac[alloca_site_registered_below] >>
  `s.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  `b+(MAX args_size ret_size+32) < dimword (:256)` by decide_tac >>
  drule_all extcall_calldata_bounds >> strip_tac >>
  drule_all compile_abi_encode_to_buf_window_strong_counted_mem >>
  disch_then (qx_choosel_then [`encoded_state`, `encode_count`] strip_assume_tac) >>
  `window_phase ctx func se sen (window_alloca_sites func (frag_ids se sen))
    [(b+32,LENGTH (enc at av))] s encoded_state` by metis_tac[window_phase_strong_result] >>
  `alloca_inv encoded_state /\ alloca_room ctx func encoded_state /\ ~encoded_state.vs_halted /\
   encoded_state.vs_current_bb = sen.cs_current_bb /\ encoded_state.vs_inst_idx = LENGTH sen.cs_current_insts /\
   eval_operand encoded encoded_state = SOME (n2w (LENGTH (enc at av)))` by
    (qpat_assum `window_strong_result _ _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[window_strong_result_def, abi_encoder_window_result_def] >>
     strip_tac >> asm_rewrite_tac[]) >>
  `eval_operand (Lit 4w) encoded_state = SOME (4w:bytes32)` by simp[eval_operand_def] >>
  drule_all window_emit_add_phase_counted_mem >>
  disch_then (qx_choosel_then [`u`, `length_count`] strip_assume_tac) >>
  `se.cs_next_var <= sen.cs_next_var /\ sen.cs_next_var <= slen.cs_next_var` by
    metis_tac[ci_mono_compile_abi_encode, ci_mono_emit_op, ci_mono_def, pairTheory.SND] >>
  `eval_operand buf encoded_state = SOME (n2w b)` by metis_tac[window_phase_eval, window_phase_labels] >>
  `!x. buf = Var x ==> not_fresh_at sen x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `eval_operand buf u = SOME (n2w b)` by metis_tac[window_phase_eval] >>
  `alloca_inv u /\ alloca_room ctx func u /\ ~u.vs_halted /\
   u.vs_current_bb = slen.cs_current_bb /\ u.vs_inst_idx = LENGTH slen.cs_current_insts` by
    metis_tac[window_phase_resources, window_phase_control] >>
  `eval_operand (Lit 28w) u = SOME (28w:bytes32)` by simp[eval_operand_def] >>
  drule_all window_emit_add_phase_counted_mem >>
  disch_then (qx_choosel_then [`t`, `offset_count`] strip_assume_tac) >>
  suspend "join"
QED

Resume extcall_encoded_calldata_suffix_resources_mem[join]:
  `window_phase ctx func sen sp {} [] encoded_state t` by
    (irule window_phase_chain >>
     qexistsl_tac [`{}`, `[]`, `slen`, `{}`, `[]`, `u`] >> simp[]) >>
  `window_phase ctx func se sp (window_alloca_sites func (frag_ids se sen))
    [(b+32,LENGTH (enc at av))] s t` by
    (irule window_phase_chain >>
     qexistsl_tac [`window_alloca_sites func (frag_ids se sen)`,
       `[(b+32,LENGTH (enc at av))]`, `sen`, `{}`, `[]`, `encoded_state`] >> simp[]) >>
  `gas_path_mem ctx func s (encode_count+length_count+offset_count) (OK t)` by
    metis_tac[gas_path_mem_then, ADD_ASSOC] >>
  `mem_cont_sim ctx func s t` by metis_tac[mem_cont_sim_trans] >>
  `alloca_history func t` by metis_tac[gas_path_mem_allocation_state] >>
  `eval_operand buf t = SOME (n2w b)` by metis_tac[window_phase_eval, window_phase_labels] >>
  `eval_operand call_len t = SOME (n2w (LENGTH (enc at av)+4))` by
    (`eval_operand call_len u = SOME (n2w (LENGTH (enc at av)+4))` by
       simp[word_add_n2w] >> metis_tac[window_phase_eval]) >>
  `FLOOKUP t.vs_allocas buf_id = SOME (b,MAX args_size ret_size+32)` by
    metis_tac[window_phase_effect, abi_encoder_registered_effect_allocated] >>
  `buf_id NOTIN window_alloca_sites func (frag_ids se sen)` by
    (simp[window_alloca_sites_def, frag_ids_def] >> decide_tac) >>
  `mem_bytes_at b 32 t.vs_memory = word_to_bytes (n2w method_id : bytes32) T` by
    (`32 <= MAX args_size ret_size+32` by decide_tac >>
     drule_all extcall_selector_prefix_frame >> simp[]) >>
  `mem_bytes_at (b+32) (LENGTH (enc at av)) t.vs_memory = enc at av` by
    (`mem_bytes_at (b+32) (LENGTH (enc at av)) encoded_state.vs_memory = enc at av` by
       (qpat_assum `window_strong_result _ _ _ _ _ _ _ _ _ _` mp_tac >>
        pure_rewrite_tac[window_strong_result_def, abi_encoder_window_result_def] >>
        strip_tac >> asm_rewrite_tac[]) >>
     irule EQ_TRANS >> goal_assum (drule_at Any) >>
     irule abi_encoder_window_effect_bytes >> qexistsl_tac [`{}`, `[]`] >>
     simp[] >> metis_tac[window_phase_effect]) >>
  suspend "bytes"
QED

Resume extcall_encoded_calldata_suffix_resources_mem[bytes]:
  `read_memory (b+28) 4 t = DROP 28 (word_to_bytes (n2w method_id : bytes32) T)` by
    (qspecl_then [`b`, `32`, `28`, `4`, `t`] mp_tac read_memory_subwindow >>
     simp[read_memory_eq_mem_bytes_at, byteTheory.LENGTH_word_to_bytes]) >>
  `read_memory (b+28) (4+LENGTH (enc at av)) t =
    DROP 28 (word_to_bytes (n2w method_id : bytes32) T) ++ enc at av` by
    (simp[read_memory_split, read_memory_eq_mem_bytes_at, ADD_ASSOC]) >>
  `(b+28)+(4+LENGTH (enc at av)) <= t.vs_alloca_next` by
    (drule_all window_phase_resources >> strip_tac >>
     fs[window_alloca_growth_def] >> decide_tac) >>
  `abi_encode_exec_frame func s t` by metis_tac[abi_encode_exec_frame_trans] >>
  qexistsl_tac [`encoded_state`, `t`, `encode_count+length_count+offset_count`] >>
  simp[word_add_n2w]
QED

Finalise extcall_encoded_calldata_suffix_resources_mem


Theorem extcall_encoded_calldata_suffix_mem:
  compile_abi_encode_to_buf dst argbuf ei se = (encoded,sen) /\
  abi_encoder_window_pre ctx func se sen dst argbuf ei at av tb cap (b+32) s /\
  emit_op ADD [encoded; Lit 4w] sen = (call_len,slen) /\
  emit_op ADD [buf; Lit 28w] slen = (call_offset,sp) /\
  fn_has_code sen slen func /\ fn_has_code slen sp func /\
  eval_operand buf s = SOME (n2w b) /\
  (!x. buf = Var x ==> not_fresh_at se x) /\
  FLOOKUP s.vs_allocas buf_id = SOME (b,MAX args_size ret_size+32) /\
  buf_id < se.cs_next_id /\ LENGTH (enc at av) <= args_size /\
  mem_bytes_at b 32 s.vs_memory = word_to_bytes (n2w method_id : bytes32) T /\
  alloca_history func s ==>
  ?encoded_state t path_count.
    window_strong_result ctx func se sen encoded at av (b+32) s encoded_state /\
    abi_encode_exec_frame func s encoded_state /\ abi_encode_exec_frame func s t /\
    window_phase ctx func se sp (window_alloca_sites func (frag_ids se sen))
      [(b+32,LENGTH (enc at av))] s t /\
    gas_path_mem ctx func s path_count (OK t) /\ mem_cont_sim ctx func s t /\
    alloca_history func t /\
    eval_operand buf t = SOME (n2w b) /\
    eval_operand call_offset t = SOME (n2w (b+28)) /\
    eval_operand call_len t = SOME (n2w (LENGTH (enc at av)+4)) /\
    FLOOKUP t.vs_allocas buf_id = SOME (b,MAX args_size ret_size+32) /\
    read_memory (b+28) (4+LENGTH (enc at av)) t =
      DROP 28 (word_to_bytes (n2w method_id : bytes32) T) ++ enc at av /\
    (b+28)+(4+LENGTH (enc at av)) <= t.vs_alloca_next /\
    b+28 < dimword (:256) /\ LENGTH (enc at av)+4 < dimword (:256)
Proof
  strip_tac >> drule_all extcall_encoded_calldata_suffix_resources_mem >>
  strip_tac >> qexistsl_tac [`encoded_state`, `t`, `path_count`] >> simp[]
QED
