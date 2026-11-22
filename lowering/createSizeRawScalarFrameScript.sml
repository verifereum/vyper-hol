(* The scalar loads and address computation after a raw CREATE snapshot. *)
Theory createSizeRawScalarFrame
Ancestors
  emitHelperProps exprLoweringProps exprSimCopy exprSimStorageCopy
  loweringStateRelDefs stmtReasonMemory ssaOperandFrame instMemFrontier
  venomInst venomState venomExecSemantics finite_map words arithmetic

Theorem scalar_reset_update_frame[local]:
  update_var out w s = (t with vs_inst_idx := k) ==>
  copy_static t = copy_static s /\ t.vs_memory = s.vs_memory /\
  (!x. lookup_var x t = if x = out then SOME w else lookup_var x s)
Proof
  simp[venom_state_component_equality,update_var_def] >> strip_tac >>
  simp[copy_static_def,venom_state_component_equality,lookup_var_def,FLOOKUP_UPDATE] >>
  qpat_x_assum `_ = t.vs_vars` (fn th => rewrite_tac[GSYM th]) >>
  simp[FLOOKUP_UPDATE,EQ_SYM_EQ]
QED

Theorem create_raw_snapshot_scalar_frame:
  emit_op MLOAD [snap] b = (len_op,c) /\
  emit_op ADD [snap; Lit 32w] c = (data_op,ac) /\
  run_inst_seq (emitted_insts b c) z = OK (l with vs_inst_idx := z.vs_inst_idx) /\
  run_inst_seq (emitted_insts c ac) l = OK (r with vs_inst_idx := l.vs_inst_idx) /\
  copy_old_operand b snap /\ eval_operand snap z = SOME (n2w B) /\
  eval_operand len_op l = SOME (n2w n) ==>
  ?len data. len_op = Var len /\ data_op = Var data /\ len <> data /\
    ~not_fresh_at b len /\ ~not_fresh_at b data /\
    not_fresh_at ac len /\ not_fresh_at ac data /\
    lookup_var len r = SOME (n2w n) /\ lookup_var data r = SOME (n2w (B+32)) /\
    copy_static r = copy_static z /\ r.vs_memory = z.vs_memory /\
    (!x. not_fresh_at b x ==> lookup_var x r = lookup_var x z)
Proof
  strip_tac >>
  qpat_assum `emit_op MLOAD _ _ = _` (strip_assume_tac o MATCH_MP (SPEC_ALL emitted_insts_emit_op)) >>
  qpat_assum `emit_op ADD _ _ = _` (strip_assume_tac o MATCH_MP (SPEC_ALL emitted_insts_emit_op)) >>
  gvs[run_inst_seq_def,step_mload_eq] >>
  qabbrev_tac `len = STRING #"%" (toString b.cs_next_var)` >>
  qabbrev_tac `data = STRING #"%" (toString (b.cs_next_var + 1))` >>
  `len <> data` by simp[Abbr `len`,Abbr `data`,fresh_var_distinct] >>
  `~not_fresh_at b len /\ ~not_fresh_at b data` by
    (simp[Abbr `len`,Abbr `data`,not_fresh_at_def] >>
     metis_tac[LESS_EQ_REFL,LESS_EQ_ADD]) >>
  `not_fresh_at ac len /\ not_fresh_at ac data` by
    (simp[Abbr `len`,Abbr `data`,not_fresh_at_def] >>
     rpt strip_tac >> irule fresh_var_distinct >> decide_tac) >>
  drule scalar_reset_update_frame >> strip_tac >>
  `snap <> Var len` by (strip_tac >> fs[copy_old_operand_def]) >>
  `eval_operand snap l = SOME (n2w B)` by
    (`eval_operand snap (l with vs_inst_idx := z.vs_inst_idx) = SOME (n2w B)`
       suffices_by simp[] >>
     qpat_assum `update_var len _ _ = _` (fn th => rewrite_tac[GSYM th]) >>
     simp[eval_operand_update_var_avoids]) >>
  `lookup_var len l = SOME (n2w n)` by fs[eval_operand_def] >>
  fs[step_add_eq,eval_operand_def,word_add_n2w] >>
  qpat_assum `update_var data _ _ = _` (strip_assume_tac o MATCH_MP (SPEC_ALL scalar_reset_update_frame)) >>
  simp[] >> rpt strip_tac >>
  `x <> len /\ x <> data` by metis_tac[] >> simp[]
QED
