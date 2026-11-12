(* Fixed two-edge transfer: the GAS count is not an instruction count.
   The two explicit edges below fix the stopping point even in a function
   that can later return to the same block. *)
Theory assignBasePtrWidenEndpoint
Ancestors assignBasePtrWidenAllocation fragGasSeqPtr fragGasPathPtr exprSimAlloc
  exprSimBufferStore exprLoweringProps emitHelperProps fragExec instIdxIndep
  venomExecSemantics venomInst venomState words list compileEnv context

Theorem assign_base_edge_sequence:
  gas_path_ptr_edge D lo ctx fn PG G tn s n G1 tn1 (OK u) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode ==>
  run_inst_seq [i] s = OK (u with vs_inst_idx := s.vs_inst_idx)
Proof
  rpt strip_tac >>
  gvs[gas_path_ptr_edge_def, step_inst_non_invoke,
      run_inst_seq_def]
  >- (drule_all step_inst_base_preserves_inst_idx >> strip_tac >> simp[venom_state_component_equality]) >>
  qpat_x_assum `OK _ = _` (assume_tac o SYM) >>
  gvs[exit_result_def]
QED

Theorem assign_base_two_edge_endpoint:
  gas_path_ptr_edge D lo ctx fn PG G tn s n G1 tn1 (OK u) /\
  gas_path_ptr_edge D lo ctx fn PG G1 tn1 u m G2 tn2 (OK t) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  lookup_block u.vs_current_bb fn.fn_blocks = SOME cc /\
  get_instruction cc u.vs_inst_idx = SOME j /\
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  j.inst_opcode <> INVOKE /\ ~is_terminator j.inst_opcode /\
  run_inst_seq [i;j] s = OK q ==>
  t = q with vs_inst_idx := s.vs_inst_idx + 2
Proof
  rpt strip_tac >>
  `run_inst_seq [i] s = OK (u with vs_inst_idx := s.vs_inst_idx)` by
    (metis_tac[assign_base_edge_sequence]) >>
  `run_inst_seq [j] u = OK (t with vs_inst_idx := u.vs_inst_idx)` by
    (metis_tac[assign_base_edge_sequence]) >>
  `run_inst_seq [j] (u with vs_inst_idx := s.vs_inst_idx) =
     OK (t with vs_inst_idx := s.vs_inst_idx)` by
    simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  `q = t with vs_inst_idx := s.vs_inst_idx` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  `u.vs_inst_idx = SUC s.vs_inst_idx /\
   t.vs_inst_idx = SUC u.vs_inst_idx` by
    (gvs[gas_path_ptr_edge_def, step_inst_non_invoke] >>
     qpat_x_assum `OK _ = _` (assume_tac o SYM) >>
     gvs[exit_result_def]) >>
  simp[venom_state_component_equality]
QED

Theorem assign_base_widen_sequence_bound:
  !ctx func cenv cx es sm sb s x op p d k.
    compile_bytestring_widen_copy d x k sm = (op,sb) /\
    0 < k /\ d < dimword (:256) /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
    (!z. x = Var z ==> not_fresh_at sm z) /\
    eval_operand x s = SOME p ==>
    ?q w. run_inst_seq (emitted_insts sm sb) s = OK q /\
      eval_operand op q = SOME w /\
      FLOOKUP q.vs_allocas sm.cs_next_id = SOME (w2n w,d) /\
      w2n w + d < dimword (:256)
Proof
  rpt strip_tac >> drule_all assignBasePtrWidenLayoutTheory.assign_base_widen_code >> strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  `t.vs_labels = s.vs_labels` by (drule_all hash_alloc_buffer_labels >> simp[]) >>
  `eval_operand x t = SOME p` by
    (Cases_on `x` >> gvs[eval_operand_def]) >>
  `run_inst_seq (emitted_insts mid sb) t =
      OK (mcopy (w2n w) (w2n p) (w2n (n2w k : bytes32)) t)` by
    (irule buffer_emit_mcopy_run >>
     qexistsl_tac [`Var p'`, `x`, `Lit (n2w k)`] >>
     gvs[eval_operand_def]) >>
  `emit_op ALLOCA [Lit (n2w d)] sm = (buf.buf_operand,mid)` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> strip_tac >> gvs[]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `emitted_insts sm sb = emitted_insts sm mid ++ emitted_insts mid sb` by
    (irule emitted_insts_append >> simp[]) >>
  qexistsl_tac [`mcopy (w2n w) (w2n p) (w2n (n2w k : bytes32)) t`, `w`] >>
  conj_tac
  >- (qpat_x_assum `emitted_insts sm sb = _` (fn th => pure_rewrite_tac[th]) >>
      qpat_x_assum `run_inst_seq (emitted_insts sm mid) s = _`
        (mp_tac o MATCH_MP run_inst_seq_append) >>
      disch_then (qspec_then `emitted_insts mid sb` (fn th => rewrite_tac[th])) >>
      first_assum ACCEPT_TAC) >>
  gvs[mcopy_def, write_memory_with_expansion_def, eval_operand_def, lookup_var_def]
QED

(* Exactly the emitted two-instruction segment, not merely a path whose
   final block and index happen to agree with the compiler endpoint. *)
Theorem assign_base_widen_counted_bound:
  !ctx func cenv cx es sm sb s x op p d k i j u t bb cc
    D lo PG G tn n G1 tn1 m G2 tn2.
    compile_bytestring_widen_copy d x k sm = (op,sb) /\
    0 < k /\ d < dimword (:256) /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
    (!z. x = Var z ==> not_fresh_at sm z) /\ eval_operand x s = SOME p /\
    s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts /\
    emitted_insts sm sb = [i;j] /\
    i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    j.inst_opcode <> INVOKE /\ ~is_terminator j.inst_opcode /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME i /\
    lookup_block u.vs_current_bb func.fn_blocks = SOME cc /\
    get_instruction cc u.vs_inst_idx = SOME j /\
    gas_path_ptr_edge D lo ctx func PG G tn s n G1 tn1 (OK u) /\
    gas_path_ptr_edge D lo ctx func PG G1 tn1 u m G2 tn2 (OK t) ==>
    ?w. eval_operand op t = SOME w /\
      FLOOKUP t.vs_allocas sm.cs_next_id = SOME (w2n w,d) /\
      w2n w + d < dimword (:256)
Proof
  rpt strip_tac >> drule_all assign_base_widen_sequence_bound >> strip_tac >>
  `run_inst_seq [i;j] s = OK q` by metis_tac[] >>
  `t = q with vs_inst_idx := s.vs_inst_idx + 2` by
    (drule_all assign_base_two_edge_endpoint >> simp[]) >>
  qexists_tac `w` >> gvs[eval_op_inst_idx]
QED
