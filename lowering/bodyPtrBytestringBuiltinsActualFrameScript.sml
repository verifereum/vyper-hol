Theory bodyPtrBytestringBuiltinsActualFrame
Ancestors
  bodyPtrBytestringBuiltinsActualUnit bodyPtrBytestringBuiltinsPtrFrame bodySim

(* Checked admissibility probe: compilation success alone does not imply
   the supported_program premise required by body_inv. *)
Theorem order_actual_program_not_supported:
  ~supported_program order_unit_tops
Proof
  EVAL_TAC
QED

Theorem order_actual_no_body_inv:
  !ctx cenv cx. ~body_inv order_unit_tops ctx cenv cx
Proof
  simp[body_inv_def, order_actual_program_not_supported]
QED
