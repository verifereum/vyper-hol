(* Shift only the proof cursor of the checked flag-and-copy sequence. *)
Theory bodyRawTupleCopyIndexedMods
Ancestors
  bodyFullRawCallTupleCopy ghostPcTransportPtr fragExec ptrDiscipline
  venomExecSemantics venomState instIdxIndep dynCopyExec

Theorem tuple_copy_index_transport[local]:
  (mcopy d a len (s with vs_inst_idx := j) =
     ((mcopy d a len s) with vs_inst_idx := j)) /\
  ((mcopy d a len (mstore b w r)).vs_inst_idx = r.vs_inst_idx)
Proof
  conj_tac >- simp[mcopy_def] >>
  simp[dynCopyExecTheory.mcopy_control_fields, dynCopyExecTheory.mstore_control_fields]
QED

Theorem raw_tuple_copy_indexed_effects:
  emit_void MSTORE [Var p;ok] s5 = ((),s1) /\
  emit_op ADD [Var p;Lit 32w] s1 = (dst,s2) /\
  emit_void MCOPY [dst;Var x;Lit (n2w (32 + ((n+31) DIV 32)*32))]
    s2 = ((),sb) /\
  safe_operand s5 (Var p) /\ safe_operand s5 (Var x) /\ safe_operand s5 ok /\
  0 < n /\ LENGTH bs <= n /\
  64 + ((n+31) DIV 32)*32 < dimword (:256) /\
  a + (32 + ((n+31) DIV 32)*32) < dimword (:256) /\
  b + (64 + ((n+31) DIV 32)*32) < dimword (:256) /\
  lookup_var x r = SOME (n2w a) /\ lookup_var p r = SOME (n2w b) /\
  ptr_covers G2 tn2 x r (32 + ((n+31) DIV 32)*32) /\
  ptr_covers G2 tn2 p r (64 + ((n+31) DIV 32)*32) /\
  eval_operand ok r = SOME (if success then 1w else 0w) /\ op_taint tn2 ok = {} /\
  (a+32+LENGTH bs <= b \/ b+32 <= a) /\
  (!mem. mem_agree_outside tn2.t_mem r.vs_memory mem ==>
     val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) a mem) /\
  allocas_from lo r /\ (ctx_has_dalloca ctx ==> allocas_below_fmp r) /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts s5 sb) /\
  run_inst_seq (emitted_insts s5 sb) r = OK t ==>
  ?Gf tnf.
    (!D. inst_seq_ptr D lo ctx func PG G2 tn2 (emitted_insts s5 sb)
       (r with vs_inst_idx := j) Gf tnf) /\
    ptr_covers Gf tnf p t (64 + ((n+31) DIV 32)*32) /\
    (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
       val_in_memory (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))])
         (ArrayV (TupleV [BoolV success;BytesV bs])) b mem) /\
    tnf.t_mem =
      ((tn2.t_mem DIFF {i | b <= i /\ i < b+32}) DIFF
        {i | b+32 <= i /\ i < b+32+(32 + ((n+31) DIV 32)*32)}) UNION
      {b+32+i | i | i < (32 + ((n+31) DIV 32)*32) /\
        a+i IN (tn2.t_mem DIFF {i | b <= i /\ i < b+32})} /\
    tnf.t_stor = tn2.t_stor /\ tnf.t_trans = tn2.t_trans /\ tnf.t_imm = tn2.t_imm /\
    (!v. not_fresh_at s5 v ==>
       lookup_var v t = lookup_var v r /\ FLOOKUP Gf v = FLOOKUP G2 v /\
       op_taint tnf (Var v) = op_taint tn2 (Var v)) /\
    (t with vs_vars := r.vs_vars) =
      mcopy (b+32) a (32 + ((n+31) DIV 32)*32)
        (mstore b (val_to_w256 (BoolV success)) r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!k. run_inst_seq (emitted_insts s5 sb) (r with vs_inst_idx := k) =
       OK (t with vs_inst_idx := k)` by
    simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  `(t with vs_inst_idx := r.vs_inst_idx) = t` by
    (qpat_x_assum `!k. run_inst_seq _ _ = _` (qspec_then `r.vs_inst_idx` mp_tac) >>
     simp[venom_state_fupdselfid]) >>
  `t.vs_inst_idx = r.vs_inst_idx` by
    (qpat_x_assum `(t with vs_inst_idx := _) = _`
       (mp_tac o Q.AP_TERM `\v. v.vs_inst_idx`) >> simp[]) >>
  qpat_x_assum `!k. run_inst_seq _ _ = _` (qspec_then `j` assume_tac) >>
  `lookup_var x (r with vs_inst_idx := j) = SOME (n2w a) /\
   lookup_var p (r with vs_inst_idx := j) = SOME (n2w b)` by
    fs[lookup_var_def] >>
  `allocas_from lo (r with vs_inst_idx := j)` by
    (qpat_assum `allocas_from lo r` mp_tac >> simp[NoAsms, allocas_from_def]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp (r with vs_inst_idx := j))` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp r` mp_tac >>
     simp[NoAsms, allocas_below_fmp_def] >> tautLib.TAUT_TAC) >>
  qpat_assum `run_inst_seq _ (r with vs_inst_idx := j) = _`
    (mp_then (Pat `run_inst_seq _ _ = _`) mp_tac raw_call_tuple_copy_checked) >>
  disch_then (drule_at (Pat `emit_void MSTORE _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_op ADD _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_void MCOPY _ _ = _`)) >>
  disch_then (drule_at (Pat `lookup_var x _ = _`)) >>
  disch_then (drule_at (Pat `lookup_var p _ = _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `ctx_has_dalloca _ ==> allocas_below_fmp _`)) >>
  disch_then (mp_tac o SIMP_RULE bool_ss
    [ptr_covers_inst_idx, eval_operand_inst_idx]) >>
  disch_then (drule_at (Pat `ptr_covers _ _ x r _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (qspecl_then [`func`,`bs`,`PG`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  simp_tac (srw_ss()) [lookup_var_def] >>
  disch_then (qx_choose_then `Gf` (qx_choose_then `tnf` strip_assume_tac)) >>
  qexistsl_tac [`Gf`,`tnf`] >> simp[] >>
  qpat_x_assum `(t with <|vs_vars := _; vs_inst_idx := j|>) = _`
    (mp_tac o Q.AP_TERM `\v. v with vs_inst_idx := r.vs_inst_idx`) >>
  simp[tuple_copy_index_transport, venom_state_fupdselfid] >>
  simp[venom_state_component_equality,
       dynCopyExecTheory.mcopy_control_fields, dynCopyExecTheory.mstore_control_fields]
QED
