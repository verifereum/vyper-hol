(* Original-name operand relations: scalar bytes and site-relative pointers. *)
Theory lowerDloadOperand
Ancestors
  lowerDloadRelocation accountsRelProps venomState ptrDiscipline byte
  finite_map pred_set list

Definition ld_mask_word_def:
  ld_mask_word Ms Mt (x:bytes32) y <=>
    Mt SUBSET Ms /\
    !k. k < 32 /\ k NOTIN Ms ==>
      EL k (word_to_bytes x T) = EL k (word_to_bytes y T)
End

Definition ld_value_def:
  ld_value B ps pt Ms Mt (x:bytes32) y <=>
    case ps of
      NONE => pt = NONE /\ ld_mask_word Ms Mt x y
    | SOME (bs,sz) => pt = SOME (B (bs,sz),sz) /\ Mt SUBSET Ms /\
                     ld_ptr_rel bs (B (bs,sz)) x y
End

Definition ld_vars_def:
  ld_vars V B G H tn un s t <=>
    s.vs_labels = t.vs_labels /\
    !v. v IN V ==>
      (lookup_var v s = NONE <=> lookup_var v t = NONE) /\
      (!x y. lookup_var v s = SOME x /\ lookup_var v t = SOME y ==>
        ld_value B (FLOOKUP G v) (FLOOKUP H v)
          (op_taint tn (Var v)) (op_taint un (Var v)) x y)
End

Theorem ld_mask_word_identity:
  ld_mask_word M M x x
Proof
  simp[ld_mask_word_def]
QED

Theorem ld_mask_word_clean:
  ld_mask_word {} Mt x y ==> Mt = {} /\ x = y
Proof
  simp[ld_mask_word_def] >> strip_tac >>
  irule word_to_bytes_EL_eq >> simp[]
QED

Theorem ld_operand_defined:
  ld_vars V B G H tn un s t /\ (!v. op = Var v ==> v IN V) ==>
  (eval_operand op s = NONE <=> eval_operand op t = NONE)
Proof
  Cases_on `op` >> simp[eval_operand_def, ld_vars_def] >> metis_tac[]
QED

Theorem ld_operand_value:
  ld_vars V B G H tn un s t /\ (!v. op = Var v ==> v IN V) /\
  eval_operand op s = SOME x /\ eval_operand op t = SOME y ==>
  ld_value B (op_prov G op) (op_prov H op)
    (op_taint tn op) (op_taint un op) x y
Proof
  Cases_on `op` >>
  simp[eval_operand_def, op_prov_def, op_taint_def, ld_vars_def] >>
  rpt strip_tac >> gvs[ld_value_def, ld_mask_word_def] >> metis_tac[]
QED
