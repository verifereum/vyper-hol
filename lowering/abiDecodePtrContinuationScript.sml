(* Compiler phase continuations keep checks at the actual instruction index. *)
Theory abiDecodePtrContinuation
Ancestors
  abiDecodePtrNormalized assignTuplePtrCopyLen instSeqComposePtr
  assignTuplePtrLocalBytesCopy emitHelperProps exprLoweringProps
  venomExecSemantics venomState instIdxIndep fragExec list

Theorem abi_decode_run_continue_normalized:
  EVERY (\i. ~is_terminator i.inst_opcode) xs /\
  EVERY (\i. ~is_terminator i.inst_opcode) ys /\
  run_inst_seq xs s = OK (t with vs_inst_idx := s.vs_inst_idx) /\
  run_inst_seq (xs ++ ys) s = OK u ==>
  run_inst_seq ys t = OK (u with vs_inst_idx := t.vs_inst_idx)
Proof
  strip_tac >>
  `run_inst_seq ys (t with vs_inst_idx := s.vs_inst_idx) = OK u` by
    (qpat_assum `run_inst_seq xs s = _`
      (mp_then Any (qspec_then `ys` mp_tac) run_inst_seq_append) >> simp[]) >>
  qspec_then `ys` mp_tac run_inst_seq_inst_idx >>
  disch_then (qspecl_then [`t with vs_inst_idx := s.vs_inst_idx`,
    `t.vs_inst_idx`] mp_tac) >>
  simp[exec_result_map_def, venom_state_component_equality]
QED

Theorem abi_decode_compile_continue_abort_ptr:
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  sc.cs_current_insts = sb.cs_current_insts ++ emitted_insts sb sc /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sb sc) /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK (t with vs_inst_idx := s.vs_inst_idx) /\
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G1 tn1 /\
  run_inst_seq (emitted_insts sb sc) t = Abort a u /\
  inst_seq_ptr D 0 ctx fn PG G1 tn1 (emitted_insts sb sc) t G2 tn2 ==>
  run_inst_seq (emitted_insts sa sc) s =
    Abort a (u with vs_inst_idx := s.vs_inst_idx) /\
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sc) s G2 tn2
Proof
  strip_tac >>
  `emitted_insts sa sc = emitted_insts sa sb ++ emitted_insts sb sc` by
    (irule emitted_insts_append >> simp[]) >>
  `t.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts sa sb)` by simp[] >>
  conj_tac
  >- (qpat_assum `run_inst_seq (emitted_insts sa sb) s = _`
        (mp_then Any (qspec_then `emitted_insts sb sc` mp_tac) run_inst_seq_append) >>
      simp[run_inst_seq_inst_idx, exec_result_map_def]) >>
  simp[] >> irule inst_seq_ptr_append_run >> conj_tac >- simp[] >>
  qexistsl_tac [`G1`, `t with vs_inst_idx := s.vs_inst_idx`, `tn1`] >>
  `t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb) = t` by
    (simp_tac (srw_ss()) [NoAsms, venom_state_component_equality] >> metis_tac[]) >>
  gvs[]
QED

Theorem abi_decode_compile_abort_suffix_ptr:
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  sc.cs_current_insts = sb.cs_current_insts ++ emitted_insts sb sc /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
  run_inst_seq (emitted_insts sa sb) s = Abort a t /\
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G1 tn1 ==>
  run_inst_seq (emitted_insts sa sc) s = Abort a t /\
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sc) s G1 tn1
Proof
  strip_tac >>
  `emitted_insts sa sc = emitted_insts sa sb ++ emitted_insts sb sc` by
    (irule emitted_insts_append >> simp[]) >>
  conj_tac
  >- (simp[] >>
      `!v. run_inst_seq (emitted_insts sa sb) s <> OK v` by simp[] >>
      drule run_inst_seq_append_err >>
      disch_then (qspec_then `emitted_insts sb sc` mp_tac) >> simp[]) >>
  simp[] >> irule inst_seq_ptr_abort_append >> metis_tac[]
QED
