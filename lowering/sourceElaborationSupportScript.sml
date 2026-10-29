(* #543 support boundary. TOP-LEVEL: checked_source_builtin_support,
   source_expr_method_id_erased, source_expr_power_supported,
   source_expr_local_tuple_index, supported_local_tuple_read,
   checked_local_tuple_read_support. No global whitelist is weakened.
   Local tuple reads use the main nested-place support rules; checking supplies
   the literal-index gate, while supported place types remain required. *)
Theory sourceElaborationSupport
Ancestors
  sourceExprProps sourceExprElaborate sourceExprDefs sourceSyntax
  supportedExprForms supportedExprs supportedTypes exprLowering
  vyperTypeSystem vyperAST list integer sourceBuiltinSupport

(* Exactly the builtin-form remainder after discharging residual MethodId
   and the Exp literal-operand gate. All other operations, widths, effects,
   conversions and storage shapes retain their original restrictions. This
   is only a builtin-form predicate, NOT a program whitelist replacement. *)
Definition source_builtin_support_remainder_def:
  source_builtin_support_remainder tops ty blt es <=>
    source_builtin_remainder tops ty blt es
End

(* The whole-program checker-only core is the same transparent builtin
   remainder as this original expression-elaboration API. *)
Theorem source_builtin_support_remainder_eq:
  source_builtin_support_remainder tops ty blt es <=>
  source_builtin_remainder tops ty blt es
Proof
  simp[source_builtin_support_remainder_def]
QED

(* The original-source API supplies the genuine typing premise; there is no
   additional readiness assumption and no runtime evaluation used as meaning. *)
Theorem checked_source_builtin_support:
  source_expr_elaborate fuel env scopes table constants bindings expected original =
    SC_Value (Builtin ty blt es) ==>
  (source_builtin_support_remainder tops ty blt es <=>
   supported_builtin_form tops ty blt es)
Proof
  strip_tac >> drule source_expr_elaborate_typed >> strip_tac >>
  drule typed_builtin_remainder >> simp[source_builtin_support_remainder_def]
QED

Theorem source_expr_method_id_erased:
  source_expr_elaborate fuel env scopes table constants bindings ty original <>
    SC_Value (Builtin ret MethodId es)
Proof
  strip_tac >> drule source_expr_elaborate_typed >>
  simp[typed_method_id_rejected]
QED

Theorem source_expr_power_supported:
  source_expr_elaborate fuel env scopes table constants bindings expected original =
    SC_Value (Builtin ty (Bop Exp) [base_e; exponent]) ==>
  (supported_builtin_form tops ty (Bop Exp) [base_e; exponent] <=>
   supported_integer_type (expr_type base_e))
Proof
  strip_tac >> drule source_expr_elaborate_typed >> strip_tac >>
  drule typed_power_support >> simp[]
QED

(* The checker already requires a literal tuple index, not merely an integer
   result type. Local tuple reads cannot take the storage-place alternative. *)
Theorem type_place_local_name_none:
  type_place_expr env (Name ty name) = NONE
Proof
  simp[well_typed_expr_def]
QED

Theorem well_typed_local_tuple_index:
  well_typed_expr env (Subscript ty (Name (TupleT ts) name) index) ==>
  ?ity n. index = Literal ity (IntL n) /\ is_int_type ity /\
          0 <= n /\ Num n < LENGTH ts /\ EL (Num n) ts = ty
Proof
  simp[Once well_typed_expr_def, type_place_local_name_none, expr_type_def] >>
  Cases_on `index` >> simp[subscript_type_ok_def] >>
  rename1 `Literal ity lit` >> Cases_on `lit` >> simp[subscript_type_ok_def]
QED

Theorem source_expr_local_tuple_index:
  source_expr_elaborate fuel env scopes table constants bindings expected original =
    SC_Value (Subscript ty (Name (TupleT ts) name) index) ==>
  ?ity n. index = Literal ity (IntL n) /\ is_int_type ity /\
          0 <= n /\ Num n < LENGTH ts /\ EL (Num n) ts = ty
Proof
  strip_tac >> drule source_expr_elaborate_typed >> strip_tac >>
  drule well_typed_local_tuple_index >> simp[]
QED

(* Both pure and effectful index branches retain the same place-type gates.
   In particular, the tuple base may itself contain nested supported places;
   support is not restricted to the flat supported_tuple_type class. *)
Theorem supported_local_tuple_read:
  supported_expr tops (Subscript ty (Name (TupleT ts) name) index) <=>
  supported_place_type tops ty /\ supported_place_type tops (TupleT ts) /\
  supported_expr tops index
Proof
  simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
       supported_subscript_place_def, supported_place_info_def, place_type_name] >>
  metis_tac[]
QED

(* The checker supplies a literal index, hence a pure supported expression.
   It does not discharge the independent type/width/layout support gates. *)
Theorem checked_local_tuple_read_support:
  well_typed_expr env (Subscript ty (Name (TupleT ts) name) index) ==>
  (supported_expr tops (Subscript ty (Name (TupleT ts) name) index) <=>
   supported_place_type tops ty /\ supported_place_type tops (TupleT ts))
Proof
  strip_tac >> drule well_typed_local_tuple_index >> strip_tac >>
  gvs[supported_local_tuple_read, supported_expr_def, supported_pure_expr_def]
QED

Theorem checked_tuple_read_supported:
  well_typed_expr env (Name (TupleT [BaseT BoolT; BaseT (UintT 256)]) "t") ==>
  well_typed_expr env
    (Subscript (BaseT (UintT 256))
      (Name (TupleT [BaseT BoolT; BaseT (UintT 256)]) "t")
      (Literal (BaseT (UintT 256)) (IntL 1))) /\
  supported_expr tops
    (Subscript (BaseT (UintT 256))
      (Name (TupleT [BaseT BoolT; BaseT (UintT 256)]) "t")
      (Literal (BaseT (UintT 256)) (IntL 1)))
Proof
  simp[supported_local_tuple_read] >> EVAL_TAC >> simp[]
QED

val () = List.app (fn (name,th) => let
    val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null (hyp th) andalso null axioms andalso
    List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail ("source elaboration support kernel audit: " ^ name) end)
  (DB.thms "sourceElaborationSupport");
