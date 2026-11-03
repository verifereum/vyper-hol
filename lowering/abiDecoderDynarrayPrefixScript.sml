(* The emitted count clamp and optional endpoint guard, before array writes. *)
Theory abiDecoderDynarrayPrefix
Ancestors
  abiDecoderRange abiDecoderBytesBound abiDecoderDynarrayBound abiDecoderGuards abiDecoderContract compileEnv emitHelper
  venomExecSemantics venomState words

Definition abi_decode_dynarray_prefix_def:
  abi_decode_dynarray_prefix src opc hi maxn abi_sz =
    do cnt <- abi_decode_count_guard opc src maxn;
       abi_decode_dynarray_end_guard src cnt abi_sz hi
    od
End

Theorem abi_decode_dynarray_prefix_sequence:
  abi_decode_dynarray_prefix src opc hi maxn abi_sz st = ((),st') /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME (n2w sb) /\
  abi_decode_load opc (n2w sb : bytes32) s = n2w n /\
  n <= maxn /\ maxn < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
                     sb + 32 + n * abi_sz <= h /\ h < dimword (:256)) /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st'
Proof
  Cases_on `hi = Lit 0w`
  >- (simp[abi_decode_dynarray_prefix_def, abi_decode_dynarray_end_guard_def,
           comp_bind_def, comp_return_def] >>
      pairarg_tac >> strip_tac >> gvs[] >>
      drule_all abi_decode_count_guard_sequence >> strip_tac >>
      drule abi_decode_count_guard_shape >> strip_tac >> metis_tac[]) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_decode_dynarray_prefix _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_decode_dynarray_prefix_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `abi_decode_count_guard opc src maxn st = (cnt,c1)` >>
  rename1 `eval_operand hi s = SOME (n2w h)` >>
  drule_all abi_decode_count_guard_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand src s1 = SOME (n2w sb) /\
   eval_operand hi s1 = SOME (n2w h)` by metis_tac[] >>
  mp_tac (Q.INST [`st` |-> `c1`, `s` |-> `s1`]
    abi_decode_dynarray_end_guard_sequence) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> qexists_tac `h` >> simp[]) >>
  strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 st') s1 = OK t` >>
  drule abi_decode_count_guard_shape >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >> qexists_tac `t` >>
  gvs[] >> metis_tac[]
QED

Definition abi_decode_dynarray_checked_prefix_def:
  abi_decode_dynarray_checked_prefix src opc hi maxn abi_sz =
    do head <- abi_decode_bytes_head src hi;
       cnt <- abi_decode_count_guard opc src maxn;
       abi_decode_dynarray_payload_guard head cnt abi_sz hi
    od
End

Theorem abi_decode_dynarray_checked_prefix_sequence:
  abi_decode_dynarray_checked_prefix src opc hi maxn abi_sz st = ((),st') /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME (n2w sb) /\
  abi_decode_load opc (n2w sb : bytes32) s = n2w n /\
  n <= maxn /\ maxn < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
                     sb + 32 + n * abi_sz <= h /\ h < dimword (:256)) /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st'
Proof
  Cases_on `hi = Lit 0w`
  >- (simp[abi_decode_dynarray_checked_prefix_def, abi_decode_bytes_head_def,
           abi_decode_dynarray_payload_guard_def, comp_bind_def, comp_return_def] >>
      pairarg_tac >> strip_tac >> gvs[] >>
      drule_all abi_decode_count_guard_sequence >> strip_tac >>
      drule abi_decode_count_guard_shape >> strip_tac >> metis_tac[]) >>
  simp[abi_decode_dynarray_checked_prefix_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `abi_decode_bytes_head src hi st = (head,c1)` >>
  rename1 `abi_decode_count_guard opc src maxn c1 = (cnt,c2)` >>
  `sb + 32 <= h` by decide_tac >>
  drule_all abi_decode_bytes_head_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand src s1 = SOME (n2w sb)` by metis_tac[] >>
  `abi_decode_load opc (n2w sb : bytes32) s1 = n2w n` by
    gvs[abi_decode_load_def, abi_decode_source_def, mload_def] >>
  drule_all abi_decode_count_guard_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `eval_operand head s2 = SOME (n2w (sb + 32)) /\
   eval_operand hi s2 = SOME (n2w h)` by metis_tac[] >>
  mp_tac (Q.INST [`st` |-> `c2`, `s` |-> `s2`]
    abi_decode_dynarray_payload_guard_sequence) >>
  (impl_tac >- (simp[] >> qexistsl_tac [`sb + 32`, `n`, `h`] >> simp[])) >>
  strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 st') s2 = OK t` >>
  drule abi_decode_count_guard_shape >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  `run_inst_seq (emitted_insts st st') s = OK t /\ inst_extends st st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`, `c1`] >> simp[]) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
