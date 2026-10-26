(* The bounded-memory bytestring endpoint, including both emitted additions. *)
Theory abiDecoderBytesBound
Ancestors
  abiDecoderGuard abiDecoderGuards emitHelperProps exprLoweringProps compileEnv emitHelper
  venomExecSemantics venomState words arithmetic

Theorem abi_decode_add_sequence:
  !a b va vb st v st' s.
  emit_op ADD [a;b] st = (v,st') /\
  eval_operand a s = SOME va /\ eval_operand b s = SOME vb /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand v t = SOME (va + vb) /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st'
Proof
  rpt strip_tac >> drule_all emit_op_ADD_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') s = OK t` >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `ADD`] abi_decode_pure_emit_frame)) >> strip_tac >>
  drule inst_extends_emit_op >> strip_tac >> qexists_tac `t` >> simp[]
QED

Definition abi_decode_bytes_end_def:
  abi_decode_bytes_end src len =
    do data_start <- emit_op ADD [src; Lit 32w];
       emit_op ADD [data_start; len]
    od
End

Theorem abi_decode_bytes_end_sequence:
  abi_decode_bytes_end src len st = (end_op,st') /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand len s = SOME (n2w cnt) /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand end_op t = SOME (n2w (sb + 32 + cnt)) /\
    fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st'
Proof
  simp[abi_decode_bytes_end_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD [src; Lit 32w] st = (data_start,c1)` >>
  `eval_operand (Lit 32w) s = SOME 32w` by simp[eval_operand_def] >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand len s1 = SOME (n2w cnt)` by metis_tac[] >>
  qspecl_then [`data_start`, `len`, `(n2w sb : bytes32) + 32w`, `n2w cnt`,
    `c1`, `end_op`, `st'`, `s1`] mp_tac abi_decode_add_sequence >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 st') s1 = OK t` >>
  drule_all abi_decode_sequence_chain >> strip_tac >> qexists_tac `t` >>
  gvs[word_add_n2w] >> metis_tac[]
QED

Definition abi_decode_bytes_end_guard_def:
  abi_decode_bytes_end_guard src len hi =
    if hi = Lit 0w then return ()
    else do end_op <- abi_decode_bytes_end src len;
            abi_decode_le_guard end_op hi
         od
End

Theorem abi_decode_bytes_end_guard_sequence:
  abi_decode_bytes_end_guard src len hi st = ((),st') /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand len s = SOME (n2w cnt) /\
  (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
                     sb + 32 + cnt <= h /\ h < dimword (:256)) /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st'
Proof
  Cases_on `hi = Lit 0w`
  >- (simp[abi_decode_bytes_end_guard_def, comp_return_def] >> strip_tac >>
      gvs[] >> qexists_tac `s` >> simp[emitted_insts_def, run_inst_seq_def,
        inst_extends_refl]) >>
  simp[abi_decode_bytes_end_guard_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `abi_decode_bytes_end src len st = (end_op,c1)` >>
  rename1 `eval_operand hi s = SOME (n2w h)` >>
  drule_all abi_decode_bytes_end_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand hi s1 = SOME (n2w h)` by metis_tac[] >>
  `sb + 32 + cnt < dimword (:256)` by decide_tac >>
  `w2n (n2w (sb + 32 + cnt) : bytes32) <= w2n (n2w h : bytes32)` by
    simp[w2n_n2w] >>
  drule_all abi_decode_le_guard_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 st') s1 = OK t` >>
  drule abi_decode_le_guard_shape >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >> qexists_tac `t` >>
  gvs[] >> metis_tac[]
QED
