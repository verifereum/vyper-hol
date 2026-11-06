(* Owner decision 17: the sole task-authorized residual admission.
   Keep this theory independent of the retained counterexample theories. *)
Theory bodyPtrTypeBuiltinsResidual
Ancestors
  bodyPtrPreds vyperAST vyperInterpreter vyperTypeSystem

(* RESIDUAL: signed Convert from dynamic bytestring; MUL by nonempty selector on padding-tainted data, ptrDiscipline fix pending *)
Theorem signed_bytestring_convert_residual:
  !cx v11 tb typ es.
    (tb = Empty \/ tb = MaxValue \/ tb = MinValue \/ tb = Epsilon \/
     tb = Convert \/ tb = Extract32) /\
    (type_builtin_args_length_ok tb (LENGTH es) ==> body_exprs_ptr_ok cx es) /\
    (tb = Convert /\
     (?e. es = [e] /\ is_bytestring_type (expr_type e)) /\
     ((?n. typ = BaseT (IntT n)) \/ typ = BaseT DecimalT)) ==>
    body_expr_ptr_ok cx (TypeBuiltin v11 tb typ es)
Proof
  cheat
QED
