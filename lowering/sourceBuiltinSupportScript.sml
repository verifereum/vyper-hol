(* #543: checker-derived builtin gates, independent of source elaboration. *)
Theory sourceBuiltinSupport
Ancestors
  supportedExprForms supportedExprs vyperTypeSystem vyperAST list integer

Definition source_builtin_remainder_def:
  source_builtin_remainder tops ty blt es <=>
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

Theorem typed_method_id_rejected:
  ~well_typed_expr env (Builtin ty MethodId es)
Proof
  simp[Once well_typed_expr_def, well_typed_builtin_app_def]
QED

Theorem builtin_remainder_other:
  blt <> MethodId /\ blt <> Bop Exp ==>
  (source_builtin_remainder tops ty blt es <=> supported_builtin_form tops ty blt es)
Proof
  Cases_on `blt` >> simp[source_builtin_remainder_def, supported_builtin_form_def]
QED

Theorem typed_power_support:
  well_typed_expr env (Builtin ty (Bop Exp) [base_e; exponent]) ==>
  (supported_builtin_form tops ty (Bop Exp) [base_e; exponent] <=>
   supported_integer_type (expr_type base_e))
Proof
  strip_tac >> drule well_typed_power_operands >>
  simp[power_operands_ok_def, integer_literal_expr_cases, power_exponent_ok_cases] >>
  rw[] >> simp[supported_builtin_form_def, supported_binop_def,
                supported_integer_literal_def, supported_nonnegative_literal_def]
QED

Theorem typed_builtin_remainder:
  well_typed_expr env (Builtin ty blt es) ==>
  (source_builtin_remainder tops ty blt es <=> supported_builtin_form tops ty blt es)
Proof
  strip_tac >> Cases_on `blt = MethodId`
  >- gvs[typed_method_id_rejected] >>
  Cases_on `blt = Bop Exp`
  >- (gvs[] >> drule well_typed_power_arguments >> strip_tac >> gvs[] >>
      drule typed_power_support >> simp[source_builtin_remainder_def]) >>
  irule builtin_remainder_other >> simp[]
QED

val () = List.app (fn (name,th) => let
    val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null (hyp th) andalso null axioms andalso
    List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail ("source builtin support kernel audit: " ^ name) end)
  (DB.thms "sourceBuiltinSupport");
