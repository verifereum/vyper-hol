Theory bodyPtrBytestringBuiltinsOpcodeCallbacks
Ancestors bodyPtrBytestringBuiltinsOpcodeState
          bodyPtrBytestringBuiltinsOpcodeCallStaging exprCallBounds

Theorem no_extcode_invalid_expr_call:
  !ty s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (invalid_expr_call ty s))
Proof
  rpt strip_tac >> simp[invalid_expr_call_def] >>
  irule no_extcode_pair >> simp[no_extcode_emit_inst]
QED

(* P retains the consumer's support restriction at the recursion boundary. *)
Theorem no_extcode_expr_child_callback:
  !P bound cfn.
    (!ce ty e s. P e /\ expr_size e < bound /\ compiler_no_extcode s ==>
      compiler_no_extcode (SND (cfn ce ty e s))) ==>
    !ce ty e s. P e /\ compiler_no_extcode s ==>
      compiler_no_extcode (SND (expr_child_callback bound cfn ce ty e s))
Proof
  rpt strip_tac >> simp[expr_child_callback_def] >>
  IF_CASES_TAC >> simp[no_extcode_invalid_expr_call]
QED

Theorem no_extcode_builtin_child_callback:
  !P bound bfn.
    (!ce rt ty bi es s. P rt bi es /\ list_size expr_size es < bound /\ compiler_no_extcode s ==>
      compiler_no_extcode (SND (bfn ce rt ty bi es s))) ==>
    !ce rt ty bi es s. P rt bi es /\ compiler_no_extcode s ==>
      compiler_no_extcode (SND (builtin_child_callback bound bfn ce rt ty bi es s))
Proof
  rpt strip_tac >> simp[builtin_child_callback_def] >>
  IF_CASES_TAC >> simp[no_extcode_invalid_expr_call]
QED

Theorem no_extcode_type_child_callback:
  !P bound tfn.
    (!ce vt ty tb rt es s. P vt tb rt es /\ list_size expr_size es < bound /\ compiler_no_extcode s ==>
      compiler_no_extcode (SND (tfn ce vt ty tb rt es s))) ==>
    !ce vt ty tb rt es s. P vt tb rt es /\ compiler_no_extcode s ==>
      compiler_no_extcode (SND (type_child_callback bound tfn ce vt ty tb rt es s))
Proof
  rpt strip_tac >> simp[type_child_callback_def] >>
  IF_CASES_TAC >> simp[no_extcode_invalid_expr_call]
QED
