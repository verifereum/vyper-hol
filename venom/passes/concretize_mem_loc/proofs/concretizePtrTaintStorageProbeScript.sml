Theory concretizePtrTaintStorageProbe
Ancestors concretizePtrTaintContent venomExecSemantics venomState ptrDiscipline
  venomInst finite_map list words pred_set

Theorem ptr_taint_sstore_execution:
  ptr_taint_content tn s t /\ inst.inst_opcode = SSTORE /\
  inst.inst_operands = [a; d] /\
  eval_operand a s = SOME k /\ eval_operand a t = SOME k /\
  eval_operand d s = SOME u /\ eval_operand d t = SOME v /\
  word_agree_except (op_taint tn d) u v /\
  step_inst fuel Ct inst t = OK t' ==>
  ?s'. step_inst 0 C inst s = OK s' /\
       ptr_taint_content (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    metis_tac[ptr_taint_content_control, ptr_taint_control_call_ctx] >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[step_inst_non_invoke] >> PURE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[] >> simp[Once opcode_case_def] >>
  simp[eval_operands_def, exec_write2_def] >> strip_tac >>
  gvs[AllCaseEqs()] >>
  drule_all ptr_taint_content_sstore >>
  disch_then (qspec_then `k` mp_tac) >>
  simp[ptr_taint_content_def, step_taint_def, store_taint_def,
       adopt_reset_def, imm_taint_def]
QED

Theorem ptr_taint_tstore_execution:
  ptr_taint_content tn s t /\ inst.inst_opcode = TSTORE /\
  inst.inst_operands = [a; d] /\
  eval_operand a s = SOME k /\ eval_operand a t = SOME k /\
  eval_operand d s = SOME u /\ eval_operand d t = SOME v /\
  word_agree_except (op_taint tn d) u v /\
  step_inst fuel Ct inst t = OK t' ==>
  ?s'. step_inst 0 C inst s = OK s' /\
       ptr_taint_content (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    metis_tac[ptr_taint_content_control, ptr_taint_control_call_ctx] >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[step_inst_non_invoke] >> PURE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[] >> simp[Once opcode_case_def] >>
  simp[eval_operands_def, exec_write2_def] >> strip_tac >>
  gvs[AllCaseEqs()] >>
  drule_all ptr_taint_content_tstore >>
  disch_then (qspec_then `k` mp_tac) >>
  simp[ptr_taint_content_def, step_taint_def, store_taint_def,
       adopt_reset_def, imm_taint_def]
QED

Theorem ptr_taint_storage_load_execution:
  ptr_taint_content tn s t /\ MEM inst.inst_opcode [SLOAD; TLOAD] /\
  inst.inst_operands = [a] /\ inst.inst_outputs = [out] /\
  eval_operand a s = SOME k /\ eval_operand a t = SOME k /\
  step_inst fuel Ct inst t = OK t' ==>
  ?u v. step_inst 0 C inst s = OK (update_var out u s) /\
        t' = update_var out v t /\
        word_agree_except (out_taint tn inst s) u v /\
        ptr_taint_content
          (step_taint inst s (update_var out u s) tn)
          (update_var out u s) t'
Proof
  strip_tac >> fs[MEM] >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[step_inst_non_invoke] >> PURE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[] >> simp[Once opcode_case_def] >>
  simp[exec_read1_def] >> strip_tac >> gvs[] >>
  qexistsl [`if inst.inst_opcode = SLOAD then sload k s else tload k s`,
            `if inst.inst_opcode = SLOAD then sload k t else tload k t`] >>
  simp[out_taint_def, ptr_taint_content_update_var] >>
  (conj_tac >- metis_tac[ptr_taint_content_sload, ptr_taint_content_tload] >>
   gvs[ptr_taint_content_def, step_taint_def,
       store_taint_def, adopt_reset_def, imm_taint_def])
QED

Theorem ptr_taint_storage_static_no_success:
  MEM inst.inst_opcode [SSTORE; TSTORE] /\
  s.vs_call_ctx.cc_static /\ eval_operands inst.inst_operands s = SOME args ==>
  step_inst fuel C inst s <> OK s'
Proof
  strip_tac >> fs[MEM] >>
  simp[step_inst_non_invoke] >> PURE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[] >> simp[Once opcode_case_def]
QED

(* All bytes may be tainted: related writes need not have equal data. *)
Theorem ptr_taint_nonempty_store_probe:
  ptr_taint_content
    (tn with t_stor := key_update tn.t_stor k {b | b < 32})
    (sstore k 1w s) (sstore k 2w s) /\
  (1w:bytes32) <> 2w /\ {b:num | b < 32} <> {}
Proof
  conj_tac
  >- (irule ptr_taint_content_sstore >>
      simp[word_agree_except_def]) >>
  simp[EXTENSION] >> wordsLib.WORD_DECIDE_TAC
QED

Theorem ptr_taint_overwrite_clear_probe:
  key_taint (key_update (key_update X k {b | b < 32}) k {}) k = {}
Proof
  simp[key_taint_def, key_update_def, EXTENSION]
QED
