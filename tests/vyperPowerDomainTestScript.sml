(* Raw-AST power-domain regressions, including the production conversion and
   the deliberately separate runtime/deploy checker boundaries. *)
Theory vyperPowerDomainTest
Ancestors
  integer vyperAST vyperValue vyperValueOperation vyperTypeSystem
Libs
  vyperCheckContractLib

Theorem power_dynamic_operands_rejected:
  ~well_typed_expr env (Builtin (BaseT (UintT 256)) (Bop Exp)
    [Name (BaseT (UintT 256)) "x"; Name (BaseT (UintT 256)) "y"])
Proof
  simp[Once well_typed_expr_def, builtin_operands_ok_def,
       power_operands_ok_def, integer_literal_expr_def, power_exponent_ok_def]
QED

Theorem power_uint256_boundary_accepted:
  well_typed_expr env (Name (BaseT (UintT 256)) "x") ==>
  well_typed_expr env (Builtin (BaseT (UintT 256)) (Bop Exp)
    [Name (BaseT (UintT 256)) "x"; Literal (BaseT (UintT 256)) (IntL 256)])
Proof
  EVAL_TAC >> simp[]
QED

Theorem power_uint256_above_boundary_rejected:
  ~well_typed_expr env (Builtin (BaseT (UintT 256)) (Bop Exp)
    [Name (BaseT (UintT 256)) "x"; Literal (BaseT (UintT 256)) (IntL 257)])
Proof
  EVAL_TAC >> simp[]
QED

Theorem power_int256_boundary_accepted:
  well_typed_expr env (Name (BaseT (IntT 256)) "x") ==>
  well_typed_expr env (Builtin (BaseT (IntT 256)) (Bop Exp)
    [Name (BaseT (IntT 256)) "x"; Literal (BaseT (IntT 256)) (IntL 255)])
Proof
  EVAL_TAC >> simp[]
QED

Theorem power_int256_above_boundary_rejected:
  ~well_typed_expr env (Builtin (BaseT (IntT 256)) (Bop Exp)
    [Name (BaseT (IntT 256)) "x"; Literal (BaseT (IntT 256)) (IntL 256)])
Proof
  EVAL_TAC >> simp[]
QED

Theorem power_negative_literal_exponent_rejected:
  ~well_typed_expr env (Builtin (BaseT (IntT 256)) (Bop Exp)
    [base_e; Literal (BaseT (IntT 256)) (IntL (-1))])
Proof
  simp[Once well_typed_expr_def, builtin_operands_ok_def, power_operands_ok_def]
QED

Theorem power_literal_base_dynamic_exponent_accepted:
  well_typed_expr env (Name (BaseT (IntT 256)) "y") ==>
  well_typed_expr env (Builtin (BaseT (IntT 256)) (Bop Exp)
    [Literal (BaseT (IntT 256)) (IntL (-2)); Name (BaseT (IntT 256)) "y"])
Proof
  EVAL_TAC >> simp[]
QED

(* The exponent bound must not reject a literal base with a large exponent. *)
Theorem power_literal_base_large_exponent_accepted:
  well_typed_expr env (Builtin (BaseT (UintT 256)) (Bop Exp)
    [Literal (BaseT (UintT 256)) (IntL 1);
     Literal (BaseT (UintT 256)) (IntL 257)])
Proof
  EVAL_TAC
QED

Theorem power_augassign_dynamic_exponent_rejected:
  type_stmt env ret_ty (AugAssign (BaseT (UintT 256)) (NameTarget "x") Exp
    (Name (BaseT (UintT 256)) "y")) = NONE
Proof
  simp[Once type_stmt_def, augassign_operand_ok_def, power_exponent_ok_def]
QED

Theorem power_augassign_negative_exponent_rejected:
  type_stmt env ret_ty (AugAssign (BaseT (IntT 256)) (NameTarget "x") Exp
    (Literal (BaseT (IntT 256)) (IntL (-1)))) = NONE
Proof
  EVAL_TAC >> simp[]
QED

(* A valid bounded exponent still needs a runtime overflow check: clamping an
   already wrapped EVM power cannot establish this mathematical result. *)
Theorem power_runtime_overflow_not_wrapped_zero:
  evaluate_binop (Unsigned 256) tv Exp (IntV 2) (IntV 256) =
    INR (RuntimeError "bounded_int_op bound")
Proof
  EVAL_TAC
QED

Theorem power_runtime_negative_exponent_error:
  evaluate_binop (Signed 256) tv Exp (IntV 2) (IntV (-1)) =
    INR (RuntimeError "Exp~")
Proof
  EVAL_TAC
QED

(* No JSON frontend or support whitelist is used below. These conversions
   deliberately exercise checker_defs, not EVAL's global rewrite set. *)
val u256 = ``BaseT (UintT 256)``;
val i256 = ``BaseT (IntT 256)``;
val u8 = ``BaseT (UintT 8)``;
val i8 = ``BaseT (IntT 8)``;
fun name ty id = ``Name ^ty ^(stringSyntax.fromMLstring id)``;
fun lit ty n = ``Literal ^ty (IntL ^(intSyntax.term_of_int (Arbint.fromInt n)))``;
fun power ty base exponent = ``Builtin ^ty (Bop Exp) [^base; ^exponent]``;
fun check_body in_deploy vis ty body =
  vyperCheckContractLib.check_contract_conv
    (vyperCheckContractLib.mk_check_contract
      {in_deploy = in_deploy, address = ``0w : address``,
       layouts = ``[] : (address # (storage_layout # storage_layout)) list``,
       modules = ``[(NONE, [FunctionDecl ^vis Nonpayable F F "test"
         [("x", ^ty); ("y", ^ty)] [] NoneT ^body])]
         : (num option # toplevel list) list``});
fun expect label accepted th = let
  val result = rhs (concl th)
in
  if (if accepted then optionSyntax.is_some result else optionSyntax.is_none result)
  then () else raise Fail ("power domain regression: " ^ label)
end;
fun expression_case label ty base exponent accepted =
  expect label accepted (check_body false ``External`` ty
    ``[Expr ^(power ty base exponent)]``);
fun augassign_case label ty exponent accepted =
  expect label accepted (check_body false ``External`` ty
    ``[AnnAssign "z" ^ty ^(name ty "x");
       AugAssign ^ty (NameTarget "z") Exp ^exponent]``);

val () = List.app (fn (label, ty, bound) => let
  val x = name ty "x"
  val y = name ty "y"
in
  expression_case (label ^ " dynamic/dynamic") ty x y false;
  expression_case (label ^ " zero") ty x (lit ty 0) true;
  expression_case (label ^ " boundary") ty x (lit ty bound) true;
  expression_case (label ^ " above boundary") ty x (lit ty (bound + 1)) false;
  expression_case (label ^ " literal/dynamic") ty (lit ty 2) y true;
  augassign_case (label ^ " augmented dynamic") ty y false;
  augassign_case (label ^ " augmented boundary") ty (lit ty bound) true;
  augassign_case (label ^ " augmented above boundary") ty (lit ty (bound + 1)) false
end) [("uint256", u256, 256), ("int256", i256, 255),
      ("uint8", u8, 8), ("int8", i8, 7)];
val () = expression_case "negative exponent" i256 (name i256 "x") (lit i256 (~1)) false;
val () = expression_case "both literal negative exponent" i256 (lit i256 2) (lit i256 (~1)) false;
val () = expression_case "negative literal base" i256 (lit i256 (~2)) (name i256 "y") true;
val () = expression_case "literal base large exponent" u256 (lit u256 1) (lit u256 257) true;
val () = expression_case "computed exponent is not a literal" u256 (name u256 "x")
  ``Builtin ^u256 (Bop Add) [^(lit u256 1); ^(lit u256 2)]`` false;
val () = augassign_case "augmented negative exponent" i256 (lit i256 (~1)) false;
val () = expect "ordinary dynamic addition unchanged" true
  (check_body false ``External`` u256
    ``[Expr (Builtin ^u256 (Bop Add) [^(name u256 "x"); ^(name u256 "y")])]``);
val () = expect "modular dynamic power unchanged" true
  (check_body false ``External`` u256
    ``[Expr (Builtin ^u256 PowMod256 [^(name u256 "x"); ^(name u256 "y")])]``);

(* Runtime checking intentionally skips constructor bodies; deploy checking
   must reject the same malformed raw AST. Both checks are required at deploy. *)
fun deploy_case label ty body accepted = (
  expect (label ^ " runtime skip") true (check_body false ``Deploy`` ty body);
  expect (label ^ " deploy") accepted (check_body true ``Deploy`` ty body));
val () = deploy_case "constructor dynamic power" u256
  ``[Expr ^(power u256 (name u256 "x") (name u256 "y"))]`` false;
val () = deploy_case "constructor bounded power" u256
  ``[Expr ^(power u256 (name u256 "x") (lit u256 256))]`` true;
val () = deploy_case "constructor negative exponent" i256
  ``[Expr ^(power i256 (lit i256 2) (lit i256 (~1)))]`` false;
val () = deploy_case "constructor augmented dynamic power" u256
  ``[AnnAssign "z" ^u256 ^(name u256 "x");
     AugAssign ^u256 (NameTarget "z") Exp ^(name u256 "y")]`` false;
val () = deploy_case "constructor augmented bounded power" u256
  ``[AnnAssign "z" ^u256 ^(name u256 "x");
     AugAssign ^u256 (NameTarget "z") Exp ^(lit u256 256)]`` true;
