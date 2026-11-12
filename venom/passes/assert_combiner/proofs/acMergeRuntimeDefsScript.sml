(* Shared raw-state certificate and pointwise runtime interface.
   The laws are a predicate to be established by the concrete producer,
   not an assertion that arbitrary certificates satisfy them. *)
Theory acMergeRuntimeDefs
Ancestors
  acMergeCursorDefs acRuntimeInvariantDefs assertCombinerDefs
  venomExecSemantics venomInst venomState finite_map pred_set list

Definition ac_merge_safe_labels_def:
  ac_merge_safe_labels fn s <=>
    !inst l. MEM inst (fn_insts fn) /\ ac_is_safe_between inst /\
      MEM (Label l) inst.inst_operands ==> l IN FDOM s.vs_labels
End

Definition ac_merge_runtime_cert_def:
  ac_merge_runtime_cert fn bb offset n s <=>
    ac_merge_runtime fn bb offset n s /\ ac_merge_safe_labels fn s
End

Definition ac_merge_runtime_laws_def:
  ac_merge_runtime_laws xs dfg fuel ctx cert <=>
    (!n s t. n < LENGTH xs /\ cert n s /\
      step_inst fuel ctx (EL n xs) s = OK t ==> cert (SUC n) t) /\
    (!n s. n < LENGTH xs /\ cert n s /\
      (EL n xs).inst_opcode = ASSERT ==> cert (SUC n) s) /\
    (!n s. n < LENGTH xs /\ cert n s /\ ac_is_safe_between (EL n xs) ==>
      ?t. step_inst fuel ctx (EL n xs) s = OK t) /\
    (!n s c p. n < LENGTH xs /\ cert n s /\
      (EL n xs).inst_opcode = ASSERT /\ (EL n xs).inst_operands = [c] /\
      ac_get_iszero_operand dfg {} c = SOME p ==>
      ?w. eval_operand p s = SOME w /\
        eval_operand c s = SOME (bool_to_word (w = 0w))) /\
    (!a n c p s t. a < n /\ n < LENGTH xs /\
      (EL a xs).inst_opcode = ASSERT /\ (EL a xs).inst_operands = [c] /\
      ac_get_iszero_operand dfg {} c = SOME p /\
      step_inst fuel ctx (EL n xs) s = OK t ==>
      eval_operand p t = eval_operand p s)
End

Theorem ac_merge_safe_labels_frame:
  s.vs_labels = t.vs_labels ==>
  (ac_merge_safe_labels fn s <=> ac_merge_safe_labels fn t)
Proof
  simp[ac_merge_safe_labels_def]
QED

Theorem ac_merge_runtime_cert_entry:
  ac_cursor_inv fn bb 0 s /\ ac_merge_safe_labels fn s ==>
  ac_merge_runtime_cert fn bb 0 0 s
Proof
  simp[ac_merge_runtime_cert_def, ac_merge_runtime_entry]
QED

Theorem ac_merge_runtime_cert_runtime:
  ac_merge_runtime_cert fn bb offset n s ==>
  ac_merge_runtime fn bb offset n s
Proof
  simp[ac_merge_runtime_cert_def]
QED

Theorem ac_merge_runtime_cert_labels:
  ac_merge_runtime_cert fn bb offset n s ==> ac_merge_safe_labels fn s
Proof
  simp[ac_merge_runtime_cert_def]
QED

Theorem ac_merge_runtime_laws_step:
  ac_merge_runtime_laws xs dfg fuel ctx cert /\
  n < LENGTH xs /\ cert n s /\ step_inst fuel ctx (EL n xs) s = OK t ==>
  cert (SUC n) t
Proof
  simp[ac_merge_runtime_laws_def] >> metis_tac[]
QED

Theorem ac_merge_runtime_laws_skip_assert:
  ac_merge_runtime_laws xs dfg fuel ctx cert /\
  n < LENGTH xs /\ cert n s /\ (EL n xs).inst_opcode = ASSERT ==>
  cert (SUC n) s
Proof
  simp[ac_merge_runtime_laws_def] >> metis_tac[]
QED

Theorem ac_merge_runtime_laws_safe_total:
  ac_merge_runtime_laws xs dfg fuel ctx cert /\
  n < LENGTH xs /\ cert n s /\ ac_is_safe_between (EL n xs) ==>
  ?t. step_inst fuel ctx (EL n xs) s = OK t
Proof
  simp[ac_merge_runtime_laws_def] >> metis_tac[]
QED

Theorem ac_merge_runtime_laws_query:
  ac_merge_runtime_laws xs dfg fuel ctx cert /\
  n < LENGTH xs /\ cert n s /\
  (EL n xs).inst_opcode = ASSERT /\ (EL n xs).inst_operands = [c] /\
  ac_get_iszero_operand dfg {} c = SOME p ==>
  ?w. eval_operand p s = SOME w /\
    eval_operand c s = SOME (bool_to_word (w = 0w))
Proof
  simp[ac_merge_runtime_laws_def] >> metis_tac[]
QED

Theorem ac_merge_runtime_laws_prior_operand:
  ac_merge_runtime_laws xs dfg fuel ctx cert /\
  a < n /\ n < LENGTH xs /\
  (EL a xs).inst_opcode = ASSERT /\ (EL a xs).inst_operands = [c] /\
  ac_get_iszero_operand dfg {} c = SOME p /\
  step_inst fuel ctx (EL n xs) s = OK t ==>
  eval_operand p t = eval_operand p s
Proof
  simp[ac_merge_runtime_laws_def] >> metis_tac[]
QED
