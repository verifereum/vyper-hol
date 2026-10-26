(* Dynamic-array child bounds: no-wrap, endpoint ADD, and upper-bound assertion. *)
Theory abiDecoderArrayBound
Ancestors
  abiDecoderArrayPtr abiDecoderGuard abiDecoderBytesBound abiDecoderGuards abiDecoderContract
  abiEncoder compileEnv emitHelper venomExecSemantics venomState words arithmetic

Definition abi_decode_array_pointer_guard_def:
  abi_decode_array_pointer_guard child_op src_data hi abi_sz =
    do abi_decode_ge_guard child_op src_data;
       end_op <- emit_op ADD [child_op; Lit (n2w abi_sz)];
       abi_decode_le_guard end_op hi
    od
End

Theorem abi_decode_array_pointer_guard_sequence:
  abi_decode_array_pointer_guard child_op src_data hi abi_sz st = ((),st') /\
  eval_operand child_op s = SOME (n2w child_base) /\
  eval_operand src_data s = SOME (n2w data_base) /\
  eval_operand hi s = SOME (n2w hb) /\
  data_base <= child_base /\ child_base + abi_sz <= hb /\ hb < dimword (:256) /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st'
Proof
  simp[abi_decode_array_pointer_guard_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `abi_decode_ge_guard child_op src_data st = (guard_result,c1)` >>
  rename1 `emit_op ADD [child_op; Lit (n2w abi_sz)] c1 = (end_op,c2)` >>
  Cases_on `guard_result` >> gvs[] >>
  `data_base < dimword (:256) /\ child_base < dimword (:256) /\
   child_base + abi_sz < dimword (:256)` by decide_tac >>
  `w2n (n2w data_base : bytes32) <= w2n (n2w child_base : bytes32)` by simp[w2n_n2w] >>
  drule_all abi_decode_ge_guard_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand child_op s1 = SOME (n2w child_base)` by metis_tac[] >>
  `eval_operand (Lit (n2w abi_sz)) s1 = SOME (n2w abi_sz)` by simp[eval_operand_def] >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `eval_operand hi s2 = SOME (n2w hb)` by metis_tac[] >>
  `w2n ((n2w child_base : bytes32) + n2w abi_sz) <= w2n (n2w hb : bytes32)` by
    simp[word_add_n2w, w2n_n2w] >>
  drule_all abi_decode_le_guard_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 st') s2 = OK t` >>
  drule abi_decode_ge_guard_shape >> strip_tac >>
  drule abi_decode_le_guard_shape >> strip_tac >>
  `run_inst_seq (emitted_insts c1 st') s1 = OK t /\ inst_extends c1 st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s2`, `c2`] >> simp[]) >>
  `run_inst_seq (emitted_insts st st') s = OK t /\ inst_extends st st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`, `c1`] >> simp[]) >>
  qexists_tac `t` >> gvs[] >> metis_tac[]
QED

Theorem abi_decode_bounded_array_pointer_phases:
  hi <> Lit 0w ==>
  compile_abi_decode_dyn_elem_ptr opc elem_src src_data hi abi_sz =
    do child_op <- compile_abi_decode_dyn_elem_ptr opc elem_src src_data (Lit 0w) abi_sz;
       abi_decode_array_pointer_guard child_op src_data hi abi_sz;
       return child_op
    od
Proof
  strip_tac >> simp[FUN_EQ_THM, compile_abi_decode_dyn_elem_ptr_def,
    abi_decode_array_pointer_guard_def, abi_decode_ge_guard_def,
    abi_decode_le_guard_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem abi_decode_bounded_array_pointer:
  compile_abi_decode_dyn_elem_ptr opc elem_src src_data hi abi_sz st = (child_op,st') /\
  hi <> Lit 0w /\ abi_decode_source_opcode opc /\
  eval_operand elem_src s = SOME p /\ eval_operand src_data s = SOME (n2w data_base) /\
  abi_decode_load opc (p:bytes32) s = n2w child_off /\
  eval_operand hi s = SOME (n2w hb) /\
  data_base + child_off + abi_sz <= hb /\ hb < dimword (:256) /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand child_op t = SOME (n2w (data_base + child_off)) /\
    fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st'
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_abi_decode_dyn_elem_ptr _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_bounded_array_pointer_phases, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `compile_abi_decode_dyn_elem_ptr opc elem_src src_data (Lit 0w) abi_sz st =
    (child_op,c1)` >>
  rename1 `abi_decode_array_pointer_guard child_op src_data hi abi_sz c1 =
    (guard_result,st')` >> Cases_on `guard_result` >> gvs[] >>
  drule_all abi_decode_array_pointer_sentinel >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand src_data s1 = SOME (n2w data_base) /\
   eval_operand hi s1 = SOME (n2w hb)` by metis_tac[] >>
  mp_tac (Q.INST [`st` |-> `c1`, `s` |-> `s1`,
    `child_base` |-> `data_base + child_off`] abi_decode_array_pointer_guard_sequence) >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 st') s1 = OK t` >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  qexists_tac `t` >> gvs[] >> metis_tac[]
QED
