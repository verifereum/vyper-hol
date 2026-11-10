(* Footprint-local preservation of external-call default values. *)
Theory extCallSeamFrame
Ancestors
  extCallSeamOracle exprSimProps loweringPosts valueCopy compileEnv
  venomState valueEncoding words list loweringStateRelDefs

Theorem extcall_default_write_frame:
  expr_val_rel cx ty d op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ val_wf tv d /\
  eval_operand op s = SOME w /\ eval_operand op t = SOME w /\
  t.vs_memory = (write_memory_with_expansion dst payload s).vs_memory /\
  (~is_word_type ty ==>
    regions_disjoint dst (LENGTH payload) (w2n w) (val_footprint tv d)) ==>
  expr_val_rel cx ty d op t
Proof
  strip_tac >> Cases_on `is_word_type ty`
  >- gvs[expr_val_rel_def] >>
  irule expr_val_rel_footprint_agree >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s`,`tv`,`w`] >> simp[] >>
  irule EQ_SYM >> irule mem_bytes_at_write_disjoint >>
  fs[regions_disjoint_def] >> decide_tac
QED

(* Covers fresh-result updates and control-only changes uniformly. *)
Theorem extcall_default_operand_frame:
  expr_val_rel cx ty d op s /\
  eval_operand op t = eval_operand op s /\ t.vs_memory = s.vs_memory ==>
  expr_val_rel cx ty d op t
Proof
  simp[expr_val_rel_def]
QED
