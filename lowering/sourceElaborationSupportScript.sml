(* #543 support boundary. TOP-LEVEL: checked_source_builtin_support,
   source_expr_method_id_erased, source_expr_power_supported,
   source_expr_local_tuple_index. No global whitelist is weakened.
   The tuple constructor boundary below is deliberately recorded: a literal
   index is NOT enough to make a local tuple read supported_program. *)
Theory sourceElaborationSupport
Ancestors
  sourceExprProps sourceExprElaborate sourceExprDefs sourceSyntax
  supportedExprForms supportedExprs vyperTypeSystem vyperAST list integer
  sourceBuiltinSupport

(* Exactly the builtin-form remainder after discharging residual MethodId
   and the Exp literal-operand gate. All other operations, widths, effects,
   conversions and storage shapes retain their original restrictions. This
   is only a builtin-form predicate, NOT a program whitelist replacement. *)
Definition source_builtin_support_remainder_def:
  source_builtin_support_remainder tops ty blt es <=>
    case (blt, es) of
      (Bop op, [a; b]) =>
        if op = Exp then supported_integer_type (expr_type a)
        else supported_binop op (expr_type a) (expr_type b)
          (supported_integer_literal a) (supported_nonnegative_literal b)
    | (MethodId, args) => T
    | (Not, [a]) => ty = BaseT BoolT \/ ty = BaseT (UintT 256)
    | (Neg, [a]) => supported_signed_type ty \/ ty = BaseT DecimalT
    | (Abs, [a]) => ty = BaseT (IntT 256)
    | (AsWeiValue d, [a]) => supported_unsigned_type (expr_type a)
    | (AddMod, [a; b; c]) => EVERY (supported_unsigned_type o expr_type) es
    | (MulMod, [a; b; c]) => EVERY (supported_unsigned_type o expr_type) es
    | (PowMod256, [a; b]) => EVERY (supported_unsigned_type o expr_type) es
    | (Env item, []) => item <> MsgGas
    | (Acc item, [a]) => item <> Code
    | (BlockHash, [a]) => T
    | (BlobHash, [a]) => T
    | (ECRecover, [a; b; c; d]) => T
    | (ECAdd, [a; b]) => T
    | (ECMul, [a; b]) => T
    | (MakeArray NONE (Fixed n), args) => supported_value_type tops ty
    | (MakeArray (SOME elem_ty) bnd, args) => supported_value_type tops ty
    | (Uint2Str n, [a]) => supported_unsigned_type (expr_type a)
    | (CalldataSlice n, [a]) => T
    | _ => F
End

(* The whole-program checker-only core is the same transparent builtin
   remainder as this original expression-elaboration API. *)
Theorem source_builtin_support_remainder_eq:
  source_builtin_support_remainder tops ty blt es <=>
  source_builtin_remainder tops ty blt es
Proof
  Cases_on `blt` >>
  simp[source_builtin_support_remainder_def, source_builtin_remainder_def]
QED

Theorem well_typed_method_id_rejected:
  ~well_typed_expr env (Builtin ty MethodId es)
Proof
  simp[Once well_typed_expr_def, well_typed_builtin_app_def]
QED

Theorem source_builtin_support_other:
  blt <> MethodId /\ blt <> Bop Exp ==>
  (source_builtin_support_remainder tops ty blt es <=>
   supported_builtin_form tops ty blt es)
Proof
  Cases_on `blt` >>
  simp[source_builtin_support_remainder_def, supported_builtin_form_def]
QED

Theorem checked_power_support:
  well_typed_expr env (Builtin ty (Bop Exp) [base_e; exponent]) ==>
  (supported_builtin_form tops ty (Bop Exp) [base_e; exponent] <=>
   supported_integer_type (expr_type base_e))
Proof
  strip_tac >> drule well_typed_power_operands >>
  simp[power_operands_ok_def, integer_literal_expr_cases,
       power_exponent_ok_cases] >>
  rw[] >> simp[supported_builtin_form_def, supported_binop_def,
                supported_integer_literal_def, supported_nonnegative_literal_def]
QED

Theorem checked_builtin_support:
  well_typed_expr env (Builtin ty blt es) ==>
  (source_builtin_support_remainder tops ty blt es <=>
   supported_builtin_form tops ty blt es)
Proof
  strip_tac >> Cases_on `blt = MethodId`
  >- gvs[well_typed_method_id_rejected] >>
  Cases_on `blt = Bop Exp`
  >- (gvs[] >> drule well_typed_power_arguments >> strip_tac >> gvs[] >>
      drule checked_power_support >>
      simp[source_builtin_support_remainder_def]) >>
  irule source_builtin_support_other >> simp[]
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
  drule checked_builtin_support >> simp[]
QED

Theorem source_expr_method_id_erased:
  source_expr_elaborate fuel env scopes table constants bindings ty original <>
    SC_Value (Builtin ret MethodId es)
Proof
  strip_tac >> drule source_expr_elaborate_typed >>
  simp[well_typed_method_id_rejected]
QED

Theorem source_expr_power_supported:
  source_expr_elaborate fuel env scopes table constants bindings expected original =
    SC_Value (Builtin ty (Bop Exp) [base_e; exponent]) ==>
  (supported_builtin_form tops ty (Bop Exp) [base_e; exponent] <=>
   supported_integer_type (expr_type base_e))
Proof
  strip_tac >> drule source_expr_elaborate_typed >> strip_tac >>
  drule checked_power_support >> simp[]
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

(* This remaining base-shape exclusion is independent of the index gate.
   Thus the two builtin clauses above cannot be advertised as discharging
   the local tuple-read constructor of the unchanged supported_program. *)
Theorem supported_local_tuple_read_rejected:
  ~supported_expr tops (Subscript ty (Name (TupleT ts) name) index)
Proof
  simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def]
QED

Theorem checked_tuple_read_still_rejected:
  well_typed_expr env (Name (TupleT [BaseT BoolT; BaseT (UintT 256)]) "t") ==>
  well_typed_expr env
    (Subscript (BaseT (UintT 256))
      (Name (TupleT [BaseT BoolT; BaseT (UintT 256)]) "t")
      (Literal (BaseT (UintT 256)) (IntL 1))) /\
  ~supported_expr tops
    (Subscript (BaseT (UintT 256))
      (Name (TupleT [BaseT BoolT; BaseT (UintT 256)]) "t")
      (Literal (BaseT (UintT 256)) (IntL 1)))
Proof
  simp[supported_local_tuple_read_rejected] >> EVAL_TAC >> simp[]
QED

val () = List.app (fn (name,th) => let
    val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null (hyp th) andalso null axioms andalso
    List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail ("source elaboration support kernel audit: " ^ name) end)
  (DB.thms "sourceElaborationSupport");
