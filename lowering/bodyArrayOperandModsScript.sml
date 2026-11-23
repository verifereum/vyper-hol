(* Linked expression-list judgment for consumers of literal array operands. *)
Theory bodyArrayOperandMods
Ancestors
  bodyFullPredsMods vyperAST

Theorem make_array_operand_elements_mods:
  body_expr_full_ok_mods mods exps cx (Builtin a (MakeArray t n) elems) /\
  builtin_args_length_ok (MakeArray t n) (LENGTH elems) ==>
  body_exprs_full_ok_mods mods exps cx elems
Proof
  strip_tac >>
  qpat_x_assum `body_expr_full_ok_mods _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  first_x_assum irule >> simp[]
QED
