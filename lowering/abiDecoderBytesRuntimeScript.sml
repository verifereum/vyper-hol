(* Word arithmetic and execution of the bounded-position memory bytes tail. *)
Theory abiDecoderBytesRuntime
Ancestors
  abiDecoderBytesMemory abiEncoderRounding abiDecoderRange abiDecoderBytesPhases
  abiDecoderContract
  emitHelperProps exprLoweringProps compileEnv loweringStateRelDefs emitHelper
  venomState venomExecSemantics venomExecProofs venomInst words arithmetic list
Libs wordsLib

Theorem abi_decode_bytes_round_bounds:
  c <= 32*((c+31) DIV 32) /\ 32*((c+31) DIV 32) < c+32
Proof
  mp_tac (Q.INST [`cnt` |-> `c`] abi_encoder_ceil32_bounds) >>
  pure_rewrite_tac [contractABITheory.ceil32_def] >> simp_tac bool_ss []
QED

Theorem abi_decode_bytes_round_capacity:
  c <= n ==>
  32*((c+31) DIV 32) + 32 <= 32 + 32*((n+31) DIV 32)
Proof
  strip_tac >>
  `(c+31) DIV 32 <= (n+31) DIV 32` by
    (irule arithmeticTheory.DIV_LE_MONOTONE >> decide_tac) >>
  decide_tac
QED

Theorem abi_decode_bytes_round_word:
  c+31 < dimword (:256) ==>
  ((n2w c:bytes32) + 31w) && word_1comp 31w = n2w (32*((c+31) DIV 32))
Proof
  strip_tac >>
  `(word_1comp 31w:bytes32) = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w` by EVAL_TAC >>
  `((n2w c:bytes32) + 31w) = n2w (c+31)` by simp[word_add_n2w] >>
  asm_rewrite_tac [] >> once_rewrite_tac [WORD_AND_COMM] >>
  irule abi_encoder_round_mask_n2w >> asm_rewrite_tac []
QED

(* NOT is the only new pure opcode in the bytes tail. *)
Theorem abi_decode_NOT_emit_frame:
  emit_op NOT ops st = (v,st') /\
  run_inst_seq (emitted_insts st st') s = OK t ==>
  t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_data_section = s.vs_data_section
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  qpat_x_assum `emit_op _ _ _ = _` kall_tac >>
  qpat_x_assum `st'.cs_current_insts = _` kall_tac >>
  rpt (qpat_x_assum `emitted_insts _ _ = _` SUBST1_TAC) >>
  simp[run_inst_seq_def, mk_inst_def, Once step_inst_base_def] >>
  simp[exec_pure1_def, AllCaseEqs(), update_var_def] >> rw[] >> simp[]
QED

Theorem abi_decode_bytes_runtime_pointer_sequence:
  emit_op ADD [cnt;Lit 31w] st = (up,c1) /\
  emit_op NOT [Lit 31w] c1 = (mask,c2) /\
  emit_op AND [up;mask] c2 = (rounded,c3) /\
  emit_op ADD [dst;rounded] c3 = (lastptr,c4) /\
  eval_operand cnt s = SOME (n2w c) /\ eval_operand dst s = SOME (n2w d) /\
  c+31 < dimword (:256) /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st c4) s = OK t /\
    eval_operand lastptr t = SOME (n2w (d+32*((c+31) DIV 32))) /\
    fresh_vars_wrt c4 t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section
Proof
  strip_tac >>
  `eval_operand (Lit 31w) s = SOME 31w` by simp[eval_operand_def] >>
  drule_all emit_op_ADD_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand (Lit 31w) s1 = SOME 31w` by simp[eval_operand_def] >>
  drule_all emit_op_NOT_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `eval_operand up s2 = SOME ((n2w c:bytes32)+31w)` by metis_tac[] >>
  drule_all emit_op_AND_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  `eval_operand dst s3 = SOME (n2w d)` by metis_tac[] >>
  drule_all abi_decode_bytes_round_word >> strip_tac >>
  drule_all emit_op_ADD_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c3 c4) s3 = OK t` >>
  rpt (qpat_x_assum `!a. a < LENGTH _ ==> _` kall_tac) >>
  rpt (qpat_x_assum `LENGTH _.vs_memory = _` kall_tac) >>
  rpt (qpat_x_assum `same_blocks _ _` kall_tac) >>
  imp_res_tac (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `ADD`] abi_decode_pure_emit_frame)) >>
  drule_all abi_decode_NOT_emit_frame >> strip_tac >>
  drule_all abi_decode_AND_emit_frame >> strip_tac >>
  imp_res_tac inst_extends_emit_op >>
  ntac 3 (drule_all abi_decode_sequence_chain >> strip_tac) >>
  qexists_tac `t` >> asm_simp_tac (srw_ss()) [word_add_n2w] >>
  metis_tac []
QED

Theorem abi_decode_bytes_runtime_copy_sequence:
  emit_void MSTORE [lastptr;Lit 0w] st = ((),c1) /\
  emit_op ADD [Lit 32w;cnt] c1 = (sz,c2) /\
  emit_void MCOPY [dst;addr;sz] c2 = ((),c3) /\
  eval_operand lastptr s = SOME (n2w (d+q)) /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand addr s = SOME (n2w a) /\
  eval_operand cnt s = SOME (n2w c) /\
  d+q < dimword (:256) /\ d < dimword (:256) /\ a < dimword (:256) /\
  32+c < dimword (:256) /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st c3) s = OK t /\ fresh_vars_wrt c3 t /\
    t.vs_memory = (mcopy d a (32+c) (mstore (d+q) 0w s)).vs_memory /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  strip_tac >>
  `run_inst_seq (emitted_insts st c1) s = OK (mstore (d+q) 0w s)` by
    (qpat_assum `emit_void MSTORE _ _ = _`
       (mp_then Any mp_tac emitted_insts_emit_void) >> strip_tac >>
     simp[run_inst_seq_def, Once step_inst_base_def, exec_write2_def,
          mk_inst_def, eval_operand_def, w2n_n2w]) >>
  `fresh_vars_wrt c1 (mstore (d+q) 0w s)` by
    (drule_all fresh_vars_wrt_emit_void_ss >> simp[fresh_vars_wrt_mstore]) >>
  `!op. eval_operand op (mstore (d+q) 0w s) = eval_operand op s` by
    (Cases >> simp[eval_operand_def, lookup_var_def, mstore_def,
                   write_memory_with_expansion_def]) >>
  `eval_operand cnt (mstore (d+q) 0w s) = SOME (n2w c) /\
   eval_operand (Lit 32w) (mstore (d+q) 0w s) = SOME 32w` by simp[eval_operand_def] >>
  drule_all emit_op_ADD_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) _ = OK prepared` >>
  `eval_operand dst prepared = SOME (n2w d) /\
   eval_operand addr prepared = SOME (n2w a)` by metis_tac[] >>
  `w2n (32w+(n2w c:bytes32)) = 32+c` by
    (asm_simp_tac bool_ss [word_add_n2w, w2n_n2w, LESS_MOD]) >>
  `w2n ((n2w c:bytes32)+32w) = 32+c` by
    (once_rewrite_tac [WORD_ADD_COMM] >> asm_rewrite_tac []) >>
  `run_inst_seq (emitted_insts c2 c3) prepared =
     OK (mcopy d a (32+c) prepared)` by
    (drule emitted_insts_emit_void >> strip_tac >>
     asm_simp_tac (srw_ss()) [run_inst_seq_def, Once step_inst_base_def,
          mk_inst_def, w2n_n2w, LESS_MOD]) >>
  rpt (qpat_x_assum `!a. a < LENGTH _ ==> _` kall_tac) >>
  rpt (qpat_x_assum `LENGTH _.vs_memory = _` kall_tac) >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `ADD`] abi_decode_pure_emit_frame)) >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  ntac 2 (drule_all abi_decode_sequence_chain >> strip_tac) >>
  `fresh_vars_wrt c3 prepared` by
    (drule_all fresh_vars_wrt_emit_void_ss >> simp[]) >>
  qexists_tac `mcopy d a (32+c) prepared` >>
  asm_simp_tac (srw_ss()) [] >> conj_tac
  >- (full_simp_tac (srw_ss()) [fresh_vars_wrt_def, lookup_var_def, mcopy_def,
        write_memory_with_expansion_def, LET_THM]) >>
  conj_tac
  >- (asm_simp_tac (srw_ss()) [mcopy_def, write_memory_with_expansion_def, LET_THM]) >>
  conj_tac
  >- (asm_simp_tac (srw_ss()) [mcopy_def, mstore_def,
        write_memory_with_expansion_def, LET_THM]) >>
  conj_tac
  >- (asm_simp_tac (srw_ss()) [mcopy_def, mstore_def,
        write_memory_with_expansion_def, LET_THM]) >>
  rpt strip_tac >>
  `eval_operand op prepared = SOME w` by metis_tac[] >>
  Cases_on `op` >> full_simp_tac (srw_ss()) [eval_operand_def, lookup_var_def,
      mcopy_def, write_memory_with_expansion_def, LET_THM]
QED

Theorem abi_decode_bytes_runtime_tail_sequence:
  abi_decode_bytes_runtime_tail dst addr cnt st = ((),st') /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand addr s = SOME (n2w a) /\
  eval_operand cnt s = SOME (n2w c) /\ c+31 < dimword (:256) /\
  d+32*((c+31) DIV 32) < dimword (:256) /\
  d < dimword (:256) /\ a < dimword (:256) /\ 32+c < dimword (:256) /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\ fresh_vars_wrt st' t /\
    t.vs_memory = (mcopy d a (32+c) (mstore (d+32*((c+31) DIV 32)) 0w s)).vs_memory /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_bytes_runtime_tail _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_decode_bytes_runtime_tail_def, comp_bind_def,
      comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  `c+31 < dimword (:256) /\ d < dimword (:256)` by (simp[] >> decide_tac) >>
  drule_all abi_decode_bytes_runtime_pointer_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st ready) s = OK prepared` >>
  `eval_operand dst prepared = SOME (n2w d) /\
   eval_operand addr prepared = SOME (n2w a) /\
   eval_operand cnt prepared = SOME (n2w c)` by metis_tac[] >>
  `d+32*((c+31) DIV 32) < dimword (:256) /\
   a < dimword (:256) /\ 32+c < dimword (:256)` by
    (asm_simp_tac (srw_ss()) [ADD_COMM]) >>
  drule_all abi_decode_bytes_runtime_copy_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts ready st') prepared = OK t` >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends st ready /\ inst_extends ready st'` by
    metis_tac [inst_extends_trans] >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  qexists_tac `t` >> asm_simp_tac (srw_ss()) [] >>
  asm_simp_tac (srw_ss()) [mcopy_def, mstore_def,
    write_memory_with_expansion_def, LET_THM, ADD_COMM]
QED

Theorem abi_decode_bytes_runtime_tail_memory:
  abi_decode_bytes_runtime_tail dst addr cnt st = ((),st') /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand addr s = SOME (n2w a) /\
  eval_operand cnt s = SOME (n2w c) /\ c <= n /\ c+31 < dimword (:256) /\
  a < dimword (:256) /\ d+(32+32*((n+31) DIV 32)) < dimword (:256) /\
  (a+32+c <= d \/ d+(32+32*((n+31) DIV 32)) <= a) /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\ fresh_vars_wrt st' t /\
    mem_bytes_at d (32+c) t.vs_memory = mem_bytes_at a (32+c) s.vs_memory /\
    mem_bytes_at (d+32+c) (32*((c+31) DIV 32)-c) t.vs_memory =
      REPLICATE (32*((c+31) DIV 32)-c) 0w /\
    abi_decode_frame d (32+32*((n+31) DIV 32)) s t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qspec_then `c` strip_assume_tac (GEN_ALL abi_decode_bytes_round_bounds) >>
  qpat_assum `c <= n` (mp_then Any mp_tac abi_decode_bytes_round_capacity) >> strip_tac >>
  `d+32*((c+31) DIV 32) < dimword (:256) /\
   d < dimword (:256) /\ 32+c < dimword (:256)` by decide_tac >>
  drule_all abi_decode_bytes_runtime_tail_sequence >> strip_tac >>
  qexists_tac `t` >> asm_simp_tac bool_ss [] >> conj_tac
  >- (asm_rewrite_tac [] >> irule abi_decode_bytes_store_copy_prefix >>
      qexists_tac `32+32*((n+31) DIV 32)` >> asm_rewrite_tac []) >>
  conj_tac
  >- (asm_rewrite_tac [] >> irule abi_decode_bytes_store_copy_padding >> decide_tac) >>
  `abi_decode_frame d (32+32*((n+31) DIV 32)) s
     (mcopy d a (32+c) (mstore (d+32*((c+31) DIV 32)) 0w s))` by
    (irule abi_decode_bytes_store_copy_frame >> decide_tac) >>
  gvs[abi_decode_frame_def] >> metis_tac []
QED
