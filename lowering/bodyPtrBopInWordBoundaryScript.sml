(* Word-result interface probes.  No compiler invariant beyond the existing
   result judgment is needed to rule out provenance on numeric operands. *)
Theory bodyPtrBopInWordBoundary
Ancestors bodyPtrDefs wordArgsPtr ptrDiscipline compileEnv

Theorem membership_word_result:
  ptr_val_ok cx t v op G tn s /\ is_word_type t ==>
  op_taint tn op = {} /\ op_prov G op = NONE
Proof
  simp[ptr_val_ok_def]
QED

Theorem ghost_kept_operand_prov:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  (!x. op = Var x ==> not_fresh_at sa x) ==>
  op_prov G op = op_prov G0 op
Proof
  Cases_on `op` >> simp[ghost_kept_def, op_prov_def] >> metis_tac[]
QED

Theorem membership_word_result_kept:
  ptr_val_ok cx t v op G0 tn0 s0 /\ is_word_type t /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  (!x. op = Var x ==> not_fresh_at sa x) ==>
  op_taint tn op = {} /\ op_prov G op = NONE
Proof
  strip_tac >> drule_all membership_word_result >> strip_tac >>
  drule_all ghost_kept_operand >> drule_all ghost_kept_operand_prov >> simp[]
QED

Theorem membership_empty_word_post:
  ptr_val_ok cx (BaseT BoolT) (BoolV F) (Lit 0w) G tn s /\
  ptr_val_ok cx (BaseT BoolT) (BoolV T) (Lit 1w) G tn s
Proof
  simp[ptr_val_ok_def, op_taint_def, op_prov_def, is_word_type_def]
QED
