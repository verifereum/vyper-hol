Theory vyperConstEvalWitness
Ancestors
  jsonToVyper jsonToVyperExpr vyperConstEval vyperConstEvalProps vyperAST vyperInterpreter
  vyperState vyperValue
Libs
  jsonASTLib vyperConstEvalLib vyperCheckContractFrontendLib

(* The frontend computes constants from the source expressions it decodes, so
   neither missing nor malformed compiler folding metadata may change what a
   contract translates to. *)
fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [
  "../tests/fixtures/check_contract/constant_bound.json",
  "../tests/fixtures/check_contract/constant_shifts.json",
  "../tests/fixtures/check_contract/constant_shift_overflow.json",
  "../tests/fixtures/check_contract/constant_refs/main.json",
  "../tests/fixtures/check_contract/constant_unevaluated_range.json",
  "../tests/fixtures/check_contract/constant_unevaluated_flag.json",
  "../tests/fixtures/check_contract/constant_undecodable_bound.json",
  "../tests/fixtures/check_contract/constant_nested/main.json",
  "../tests/fixtures/check_contract/constant_widened.json",
  "../tests/fixtures/check_contract/constant_undecodable_import/main.json",
  "../tests/fixtures/check_contract/constant_minmax_bound.json",
  "../tests/fixtures/check_contract/constant_interface_stub.json"];

val fixture_dir = "../tests/fixtures/check_contract/";

fun remove_folded (JSON.OBJECT fields) = JSON.OBJECT
      (List.map (fn (key,v) => (key,remove_folded v))
        (List.filter (fn (key,_) => key <> "folded_value") fields))
  | remove_folded (JSON.ARRAY values) = JSON.ARRAY (List.map remove_folded values)
  | remove_folded value = value;
fun poison_folded (JSON.OBJECT fields) = JSON.OBJECT
      (("folded_value", JSON.STRING "untrusted") ::
       List.map (fn (key,v) => (key,poison_folded v))
        (List.filter (fn (key,_) => key <> "folded_value") fields))
  | poison_folded (JSON.ARRAY values) = JSON.ARRAY (List.map poison_folded values)
  | poison_folded value = value;

fun translate name = let
  val json = JSONDecode.decodeFile JSONDecode.raw (fixture_dir ^ name)
  val ast = JSONDecode.decode jsonASTLib.annotated_ast json
  val () = app (fn modified =>
    if aconv ast (JSONDecode.decode jsonASTLib.annotated_ast modified) then ()
    else raise Fail (name ^ ": decoding depends on folded_value"))
    [remove_folded json, poison_folded json]
in EVAL ``translate_annotated_ast ^ast`` end;

fun contains label tm th =
  if can (find_term (aconv tm)) (rhs (concl th)) then ()
  else raise Fail ("missing " ^ label ^ ": " ^ term_to_string tm ^ "\nin: " ^ term_to_string (rhs (concl th)));

fun checked name = let
  val th = vyperCheckContractFrontendLib.check_contract_file
    {in_deploy = false, address = ``0w : address``, path = fixture_dir ^ name}
in
  if optionSyntax.is_some (rhs (concl th)) then th
  else raise Fail (name ^ " rejected by check_contract")
end;

val uint256 = ``BaseT (UintT 256)``;

(* N = 1 + 2 sizes the array and is the exponent of x ** N. *)
val bound = translate "constant_bound.json";
val () = contains "array bound" ``ArrayT ^uint256 (Fixed 3)`` bound;
val () = contains "constant exponent"
  ``Builtin ^uint256 (Bop Exp) [Name ^uint256 "x"; Literal ^uint256 (IntL 3)]``
  bound;
Theorem constant_bound_translation = bound;
Theorem constant_bound_contract_checked = checked "constant_bound.json";

(* N = 1 << 1 sizes the array. *)
val shifts = translate "constant_shifts.json";
val () = contains "shift bound" ``ArrayT ^uint256 (Fixed 2)`` shifts;
Theorem constant_shifts_translation = shifts;
Theorem constant_shifts_contract_checked = checked "constant_shifts.json";

(* ((1 << 256) >> 255) + 1 is 3 in the compiler's unbounded arithmetic but 1
   under uint256 shifts. The evaluated annotation disagrees with the compiler's
   type, so the contract is rejected rather than given the wrong bound. *)
val overflow = translate "constant_shift_overflow.json";
val () = if optionSyntax.is_none (rhs (concl overflow)) then ()
  else raise Fail "wrapping shift bound accepted";
Theorem constant_shift_overflow_rejected = overflow;

(* M = N + 1 refers to N declared after it; lib.W bounds an annotation through
   its module alias. Both sizes and the range bound evaluate. *)
fun has_for_bound n = can (find_term (fn t =>
  case strip_comb t of
    (h, [_, _, _, b, _]) => is_const h andalso fst (dest_const h) = "For"
                            andalso aconv b (numSyntax.term_of_int n)
  | _ => false));
val refs = translate "constant_refs/main.json";
val () = contains "forward reference bound" ``ArrayT ^uint256 (Fixed 3)`` refs;
val () = contains "module constant bound" ``ArrayT ^uint256 (Fixed 4)`` refs;
val () = if has_for_bound 3 (rhs (concl refs)) then ()
  else raise Fail "range(M) bound is not 3";
Theorem constant_refs_translation = refs;
Theorem constant_refs_contract_checked = checked "constant_refs/main.json";

(* outer.inner.N reaches a constant through an import of an import. *)
val nested = translate "constant_nested/main.json";
val () = contains "nested module constant bound" ``ArrayT ^uint256 (Fixed 3)`` nested;
val () = contains "nested module constant sum bound" ``ArrayT ^uint256 (Fixed 4)`` nested;
Theorem constant_nested_translation = nested;
Theorem constant_nested_contract_checked = checked "constant_nested/main.json";

(* max_value(int8) bounds the parameter's annotation, which the compiler
   leaves untyped, so it takes its type from its argument: 127, not uint256's
   maximum. LOW = min_value(int8) is -128. *)
val int8 = ``BaseT (IntT 8)``;
val minmax = translate "constant_minmax_bound.json";
val () = contains "max_value bound" ``ArrayT ^int8 (Fixed 127)`` minmax;
val () = contains "min_value constant"
  ``Literal ^int8 (IntL ^(intSyntax.term_of_int (Arbint.fromInt ~128)))`` minmax;
Theorem constant_minmax_bound_translation = minmax;
Theorem constant_minmax_bound_contract_checked = checked "constant_minmax_bound.json";

(* The builtin IERC20Detailed interface declares name() -> String[...]. *)
Theorem constant_interface_stub_contract_checked =
  checked "constant_interface_stub.json";

(* A: constant(Bytes[10]) = B with B: constant(Bytes[5]): the references to
   B in A's initializer and to A in x == A are Bytes[10] literals, so both
   type-check. *)
val widened = translate "constant_widened.json";
val () = if can (find_term (fn t =>
    case strip_comb t of
      (h, [ty, _]) => is_const h andalso fst (dest_const h) = "Literal" andalso
                      aconv ty ``BaseT (BytesT (Dynamic 10))``
    | _ => false)) (rhs (concl widened)) then ()
  else raise Fail "A is not a Bytes[10] literal";
Theorem constant_widened_translation = widened;
Theorem constant_widened_contract_checked = checked "constant_widened.json";

(* Positions whose value must be known at compile time but that the evaluator
   leaves alone are rejected, not given a default: range(N) with
   N = uint256_addmod(1, 2, 7), and is_static_call=True or False. *)
val unevaluated_range = translate "constant_unevaluated_range.json";
val () = if optionSyntax.is_none (rhs (concl unevaluated_range)) then ()
  else raise Fail "unevaluated range bound accepted";
Theorem constant_unevaluated_range_rejected = unevaluated_range;
val unevaluated_flag = translate "constant_unevaluated_flag.json";
val () = contains "rejected raw_call" ``rejected_expr``
  (CONV_RULE (RAND_CONV (REWRITE_CONV [GSYM rejected_expr_def])) unevaluated_flag);
val () = if (checked "constant_unevaluated_flag.json"; false)
              handle Fail msg => msg = "check_contract returned NONE"
  then () else raise Fail "unevaluated raw_call flag accepted";
Theorem constant_unevaluated_flag_translation = unevaluated_flag;

(* An annotation that is present but does not decode (here the bound
   len(b"abc"), whose untyped bytes literal the decoder does not accept) fails
   the decoding; it is not read as absent, which would trust the compiler's
   inferred type. *)
val () = if can translate "constant_undecodable_bound.json"
  then raise Fail "undecodable annotation read as absent" else ();
(* The same in an imported module fails the whole decoding; it does not drop
   the imports. *)
val () = if can translate "constant_undecodable_import/main.json"
  then raise Fail "undecodable imported module dropped" else ();

Theorem constant_initializer_runtime:
  eval_expr cx
    (Builtin (BaseT (UintT 256)) (Bop Add)
      [Literal (BaseT (UintT 256)) (IntL 1);
       Literal (BaseT (UintT 256)) (IntL 2)]) st =
  (INL (Value (IntV 3)), st)
Proof
  irule eval_constant_sound >> EVAL_TAC
QED

(* Operations the interpreter rejects have no compile-time value. *)
fun lit ty i = ``Literal ^ty (IntL ^(intSyntax.term_of_int (Arbint.fromInt i)))``;
fun op2 ty bop a b = ``Builtin ^ty (Bop ^bop) [^a; ^b]``;
val uint8 = ``BaseT (UintT 8)``;
val int8 = ``BaseT (IntT 8)``;
val () = app (fn (label, e) =>
  if optionSyntax.is_none (rhs (concl (EVAL ``eval_constant ^e``))) then ()
  else raise Fail ("evaluated " ^ label))
  [("division by zero", op2 uint256 ``vyperAST$Div`` (lit uint256 1) (lit uint256 0)),
   ("overflow", op2 uint8 ``vyperAST$Add`` (lit uint8 255) (lit uint8 1)),
   ("negative shift count",
    op2 uint256 ``vyperAST$ShR`` (lit uint256 1) (lit int8 (~1))),
   ("runtime name", op2 uint256 ``vyperAST$Add`` (lit uint256 1) ``Name ^uint256 "x"``)];
