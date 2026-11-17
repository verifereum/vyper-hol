Theory vyperConstEvalWitness
Ancestors
  jsonToVyper jsonToVyperExpr vyperConstEval vyperConstEvalProps vyperPinFold
  vyperPinFoldProps vyperOriginFold
  vyperAST vyperInterpreter
  vyperState vyperValue
Libs
  jsonASTLib vyperConstEvalLib vyperCheckContractFrontendLib

(* The frontend computes constants from the source expressions it decodes, so
   neither missing nor malformed compiler folding metadata may change what a
   contract translates to. *)
fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [
  "../tests/fixtures/check_contract/constant_general_builtins.json",
  "../tests/fixtures/check_contract/constant_mixed_bytes_equality.json",
  "../tests/fixtures/check_contract/constant_hexand.json",
  "../tests/fixtures/check_contract/constant_hexinvert.json",
  "../tests/fixtures/check_contract/constant_hexeq.json",
  "../tests/fixtures/check_contract/constant_origin.json",
  "../tests/fixtures/check_contract/constant_origin_import/main.json",
  "../tests/fixtures/check_contract/constant_mixed_bytes_select.json",
  "../tests/fixtures/check_contract/constant_mixed_bytes_offset.json",
  "../tests/fixtures/check_contract/constant_mixed_high_offset.json",
  "../tests/fixtures/check_contract/constant_bound.json",
  "../tests/fixtures/check_contract/constant_shifts.json",
  "../tests/fixtures/check_contract/constant_shift_bound.json",
  "../tests/fixtures/check_contract/constant_refs/main.json",
  "../tests/fixtures/check_contract/constant_unevaluated_range.json",
  "../tests/fixtures/check_contract/constant_unevaluated_flag.json",
  "../tests/fixtures/check_contract/constant_undecodable_bound.json",
  "../tests/fixtures/check_contract/constant_nested/main.json",
  "../tests/fixtures/check_contract/constant_widened.json",
  "../tests/fixtures/check_contract/constant_widened_subscript.json",
  "../tests/fixtures/check_contract/constant_undecodable_import/main.json",
  "../tests/fixtures/check_contract/constant_minmax_bound.json",
  "../tests/fixtures/check_contract/constant_interface_stub.json",
  "../tests/fixtures/check_contract/constant_typed_sizes/main.json"];

val fixture_dir = "../tests/fixtures/check_contract/";

fun remove_folded (JSON.OBJECT fields) = JSON.OBJECT
      (List.map (fn (key,v) => (key,remove_folded v))
        (List.filter (fn (key,_) => key <> "folded_value" andalso key <> "_folded_value") fields))
  | remove_folded (JSON.ARRAY values) = JSON.ARRAY (List.map remove_folded values)
  | remove_folded value = value;
fun poison_folded (JSON.OBJECT fields) = JSON.OBJECT
      (("folded_value", JSON.STRING "untrusted") ::
       ("_folded_value", JSON.STRING "untrusted") ::
       List.map (fn (key,v) => (key,poison_folded v))
        (List.filter (fn (key,_) => key <> "folded_value" andalso key <> "_folded_value") fields))
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

Theorem exponent_operand_original_residual:
  exponent_operand JBop_Pow
    (Builtin (BaseT (UintT 256)) (Bop UnsafeAdd)
      [Builtin (BaseT (UintT 256)) (Bop Add)
        [Literal (BaseT (UintT 256)) (IntL 1);
         Literal (BaseT (UintT 256)) (IntL 2)];
       Name (BaseT (UintT 256)) "x"]) =
    Builtin (BaseT (UintT 256)) (Bop UnsafeAdd)
      [Builtin (BaseT (UintT 256)) (Bop Add)
        [Literal (BaseT (UintT 256)) (IntL 1);
         Literal (BaseT (UintT 256)) (IntL 2)];
       Name (BaseT (UintT 256)) "x"] /\
  exponent_operand JBop_Pow
    (Builtin (BaseT (UintT 256)) (Bop Add)
      [Literal (BaseT (UintT 256)) (IntL 1);
       Literal (BaseT (UintT 256)) (IntL 2)]) =
    Literal (BaseT (UintT 256)) (IntL 3)
Proof
  EVAL_TAC
QED

val residual = ``Builtin (BaseT (UintT 256)) (Bop UnsafeAdd)
  [Builtin (BaseT (UintT 256)) (Bop Add)
     [Literal (BaseT (UintT 256)) (IntL 1);
      Literal (BaseT (UintT 256)) (IntL 2)];
   Name (BaseT (UintT 256)) "x"]``;
val residual_json = ``JE_Call
  (JE_Name "unsafe_add" NONE JMissingSource (JT_Integer 256 F))
  [JE_BinOp (JE_Int 1 (JT_Integer 256 F)) JBop_Add
     (JE_Int 2 (JT_Integer 256 F)) (JT_Integer 256 F);
   JE_Name "x" NONE JMissingSource (JT_Integer 256 F)]
  [] (JT_Integer 256 F) JMissingSource``;
val residual_ctx_raw = ``module_expr_ctx [] (0:int) NONE [] [] [] []``;
val residual_ctx = Term.inst
  (match_type (type_of residual_ctx_raw) (fst (dom_rng (type_of ``translate_expr``))))
  residual_ctx_raw;

val projection_residual = EVAL ``
  fold_pin_constant ^residual = ^residual /\
  make_builtin_call (BaseT (BytesT (Dynamic 8))) "slice"
    [Literal (BaseT (BytesT (Dynamic 8))) (BytesL []);
     Literal (BaseT (UintT 256)) (IntL 0); ^residual] [] (JT_Bytes 8) =
    Builtin (BaseT (BytesT (Dynamic 8))) (Slice 8)
      [Literal (BaseT (BytesT (Dynamic 8))) (BytesL []);
       Literal (BaseT (UintT 256)) (IntL 0); ^residual] /\
  make_builtin_call (BaseT (BytesT (Fixed 4))) "method_id"
    [^residual] [] (JT_BytesM 4) =
    Builtin (BaseT (BytesT (Fixed 4))) MethodId [^residual] /\
  translate_expr ^residual_ctx
    (JE_Subscript
      (JE_Tuple [JE_Int 1 (JT_Integer 256 F)]
        (JT_Tuple [JT_Integer 256 F])) ^residual_json (JT_Integer 256 F)) =
    Subscript (BaseT (UintT 256))
      (Builtin (TupleT [BaseT (UintT 256)]) (MakeArray NONE (Fixed 1))
        [Literal (BaseT (UintT 256)) (IntL 1)]) ^residual /\
  translate_iter ^residual_ctx (BaseT (UintT 256))
    (JIter_Range [^residual_json; ^residual_json] NONE) =
    Range ^residual ^residual``;
val () = if aconv (rhs (concl projection_residual)) ``T`` then ()
         else raise Fail "runtime consumer changed a nonliteral residual";
Theorem runtime_consumers_original_residual = EQT_ELIM projection_residual;

(* The pin widens each literal's annotation to the list element type;
   decoding must retain that bound rather than derive it from the payload. *)
val widened_subscript = translate "constant_widened_subscript.json";
val () = contains "selected literal retains the inferred element bound"
  ``Literal (BaseT (BytesT (Dynamic 2))) (BytesL [97w])`` widened_subscript;
Theorem constant_widened_subscript_translation = widened_subscript;

(* Runtime-safe evaluation has different values and coverage from the pin's
   AST folder. These witnesses keep that distinction explicit. *)
Theorem bounded_shift_constant:
  eval_constant
    (Builtin (BaseT (UintT 256)) (Bop Add)
      [Builtin (BaseT (UintT 256)) (Bop ShR)
        [Builtin (BaseT (UintT 256)) (Bop ShL)
          [Literal (BaseT (UintT 256)) (IntL 1);
           Literal (BaseT (UintT 256)) (IntL 256)];
         Literal (BaseT (UintT 256)) (IntL 255)];
       Literal (BaseT (UintT 256)) (IntL 1)]) = SOME (IntV 1)
Proof
  EVAL_TAC
QED

Theorem unsafe_add_constant:
  eval_constant
    (Builtin (BaseT (UintT 256)) (Bop UnsafeAdd)
      [Literal (BaseT (UintT 256))
        (IntL 115792089237316195423570985008687907853269984665640564039457584007913129639935);
       Literal (BaseT (UintT 256)) (IntL 0)]) =
    SOME (IntV 115792089237316195423570985008687907853269984665640564039457584007913129639935)
Proof
  EVAL_TAC
QED

Theorem as_wei_constant_omitted:
  eval_constant
    (Builtin (BaseT (UintT 256)) (AsWeiValue Gwei)
      [Literal (BaseT (UintT 256))
        (IntL 115792089237316195423570985008687907853269984665640564039457584007913)]) = NONE
Proof
  EVAL_TAC
QED

Theorem addmod_constant_omitted:
  eval_constant
    (Builtin (BaseT (UintT 256)) AddMod
      [Literal (BaseT (UintT 256)) (IntL 1);
       Literal (BaseT (UintT 256)) (IntL 2);
       Literal (BaseT (UintT 256)) (IntL 5)]) = NONE
Proof
  EVAL_TAC
QED

Theorem pin_fold_wei_and_addmod:
  pin_fold_expr
    (Builtin (BaseT (UintT 256)) (AsWeiValue Gwei)
      [Literal (BaseT DecimalT) (DecimalL 30)]) =
      Literal (BaseT (UintT 256)) (IntL 3) /\
  pin_fold_expr
    (Builtin (BaseT (UintT 256)) AddMod
      [Literal (BaseT (UintT 256)) (IntL 1);
       Literal (BaseT (UintT 256)) (IntL 2);
       Literal (BaseT (UintT 256)) (IntL 5)]) =
      Literal (BaseT (UintT 256)) (IntL 3)
Proof
  EVAL_TAC
QED

Theorem pin_fold_runtime_provenance:
  ~is_int_literal (pin_fold_expr
    (Builtin (BaseT (UintT 256)) (Bop UnsafeAdd)
      [Literal (BaseT (UintT 256)) (IntL 1);
       Literal (BaseT (UintT 256)) (IntL 0)])) /\
  ~is_int_literal (pin_fold_expr
    (TypeBuiltin (BaseT (UintT 256)) Convert (BaseT (UintT 256))
      [Literal (BaseT (UintT 256)) (IntL 1)])) /\
  ~is_int_literal (pin_fold_expr
    (Builtin (BaseT (UintT 256)) (Bop Exp)
      [Literal (BaseT (UintT 256)) (IntL 1);
       Builtin (BaseT (UintT 256)) (Bop UnsafeAdd)
         [Literal (BaseT (UintT 256)) (IntL 1);
          Literal (BaseT (UintT 256)) (IntL 0)]]))
Proof
  EVAL_TAC
QED

Theorem pin_fold_list_selection:
  pin_fold_expr
    (Subscript (BaseT (UintT 256))
      (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2))
        (MakeArray (SOME (BaseT (UintT 256))) (Fixed 2))
        [Literal (BaseT (UintT 256)) (IntL 0);
         Literal (BaseT (UintT 256)) (IntL 2)])
      (Literal (BaseT (UintT 256)) (IntL 0))) =
    Literal (BaseT (UintT 256)) (IntL 0)
Proof
  EVAL_TAC
QED

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

(* The compiler type-checks the intermediate shift, which fits uint256. *)
val shift_bound = translate "constant_shift_bound.json";
val () = contains "bounded shift annotation" ``ArrayT ^uint256 (Fixed 3)`` shift_bound;
Theorem constant_shift_bound_translation = shift_bound;
Theorem constant_shift_bound_contract_checked = checked "constant_shift_bound.json";

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

(* max_value(int8) retains the bound of its type argument: 127, not uint256's
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

(* Literal-result initializers supply constants without trusting folded_value.
   BoolOp syntax folds before translation to runtime IfExp. *)
val unevaluated_range = translate "constant_unevaluated_range.json";
val () = if has_for_bound 3 (rhs (concl unevaluated_range)) then ()
  else raise Fail "folded addmod range bound is not 3";
Theorem constant_addmod_range_translation = unevaluated_range;
Theorem constant_addmod_range_contract_checked =
  checked "constant_unevaluated_range.json";
Theorem constant_unevaluated_flag_contract_checked =
  checked "constant_unevaluated_flag.json";

(* Formerly untyped annotation bytes now decode from the compiler's type
   metadata. Both main and imported annotation bounds evaluate to 3. *)
val bytes_bound = translate "constant_undecodable_bound.json";
val () = contains "bytes length annotation" ``ArrayT ^uint256 (Fixed 3)`` bytes_bound;
Theorem constant_bytes_bound_translation = bytes_bound;
Theorem constant_bytes_bound_contract_checked = checked "constant_undecodable_bound.json";
val imported_bytes_bound = translate "constant_undecodable_import/main.json";
val () = contains "imported bytes length annotation"
  ``ArrayT ^uint256 (Fixed 3)`` imported_bytes_bound;
Theorem constant_imported_bytes_bound_translation = imported_bytes_bound;
Theorem constant_imported_bytes_bound_contract_checked =
  checked "constant_undecodable_import/main.json";

(* A malformed annotation must still fail decoding, including in an import.
   Removing the bytes type reconstructs the old undecodable input explicitly. *)
fun untype_bytes (JSON.OBJECT fields) = let
      val is_bytes = List.exists
        (fn ("ast_type", JSON.STRING "Bytes") => true | _ => false) fields
      val fields = if is_bytes
        then List.filter (fn (key, _) => key <> "type") fields else fields
    in JSON.OBJECT (map (fn (key, value) => (key, untype_bytes value)) fields) end
  | untype_bytes (JSON.ARRAY values) = JSON.ARRAY (map untype_bytes values)
  | untype_bytes value = value;
val () = app (fn name => let
  val json = JSONDecode.decodeFile JSONDecode.raw (fixture_dir ^ name)
in
  if can (JSONDecode.decode jsonASTLib.annotated_ast) (untype_bytes json)
  then raise Fail (name ^ ": malformed annotation read as absent") else ()
end) ["constant_undecodable_bound.json", "constant_undecodable_import/main.json"];

val typed_sizes = translate "constant_typed_sizes/main.json";
fun sized_variable (name, ty) =
  if can (find_term (fn tm =>
    case strip_comb tm of
      (head, [_, _, id, declared, _]) =>
        is_const head andalso fst (dest_const head) = "VariableDecl" andalso
        aconv id (stringSyntax.fromMLstring name) andalso aconv declared ty
    | _ => false)) (rhs (concl typed_sizes)) then ()
  else raise Fail ("incorrect typed annotation for " ^ name);
val () = app sized_variable
  [("static_size", ``ArrayT ^uint256 (Fixed 3)``),
   ("bytes_size", ``BaseT (BytesT (Dynamic 3))``),
   ("string_size", ``BaseT (StringT 3)``),
   ("dynamic_size", ``ArrayT ^uint256 (Dynamic 3)``),
   ("selected_size", ``ArrayT ^uint256 (Fixed 3)``),
   ("forward_size", ``ArrayT ^uint256 (Fixed 3)``),
   ("imported_size", ``ArrayT ^uint256 (Fixed 4)``),
   ("rounded_size", ``BaseT (StringT 1)``),
   ("minmax_size", ``ArrayT ^uint256 (Fixed 3)``),
   ("named_array_size", ``ArrayT ^uint256 (Fixed 3)``),
   ("closed_shift_size", ``ArrayT ^uint256 (Fixed 4)``)];
val () = contains "imported forward struct annotation"
  ``StructDecl "Sized" [("data", BaseT (BytesT (Dynamic 4))) ]`` typed_sizes;
Theorem constant_typed_sizes_translation = typed_sizes;
Theorem constant_typed_sizes_contract_checked = checked "constant_typed_sizes/main.json";

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

(* These fixtures were accepted by the pin. Hex spelling remains relevant to
   membership after aliases, imports and selectors; topic arrays stay closed. *)
val origins = translate "constant_origin.json";
val () = contains "case-sensitive Hex membership"
  ``VariableDecl Private (Constant (Literal (BaseT BoolT) (BoolL F)))
      "FOUND" (BaseT BoolT) NONE`` origins;
val () = contains "forward closed-container reference"
  ``VariableDecl Private (Constant (Literal (BaseT BoolT) (BoolL T)))
      "FORWARD" (BaseT BoolT) NONE`` origins;
(* Check the actual translated call, since check_contract accepts both the
   declaration bound 2 and the compiler's reference-position bound 4. *)
fun check_raw_log_topics expected th = let
  val calls = find_terms (fn tm =>
    case strip_comb tm of
    | (head, [_, target, _, _]) =>
        same_const head ``vyperAST$Call`` andalso aconv target ``vyperAST$RawLog``
    | _ => false) (rhs (concl th))
  val () = if length calls = expected then ()
           else raise Fail ("unexpected number of translated RawLog calls: " ^
             Int.toString (length calls))
  fun check call = let
    val args = List.nth (#2 (strip_comb call), 2)
    val topics = hd (#1 (listSyntax.dest_list args))
    val result = EVAL ``
      expr_type ^topics = ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic 4) /\
      case ^topics of
      | Builtin _ (MakeArray (SOME elem) bd) es =>
          elem = BaseT (BytesT (Fixed 32)) /\ bd = Dynamic 4 /\
          pin_literal_trees es
      | _ => F``
  in EQT_ELIM result end
in LIST_CONJ (map check calls) end;
Theorem constant_origin_raw_log_reference_bounds = check_raw_log_topics 2 origins;
Theorem constant_origin_translation = origins;
Theorem constant_origin_contract_checked = checked "constant_origin.json";
val imported_origins = translate "constant_origin_import/main.json";
val () = contains "imported Hex alias retains spelling"
  ``VariableDecl Private (Constant (Literal (BaseT BoolT) (BoolL F)))
      "FOUND" (BaseT BoolT) NONE`` imported_origins;
Theorem constant_origin_import_raw_log_reference_bound =
  check_raw_log_topics 1 imported_origins;
Theorem constant_origin_import_translation = imported_origins;
Theorem constant_origin_import_contract_checked =
  checked "constant_origin_import/main.json";

fun json_field key (JSON.OBJECT fields) =
      Option.map #2 (List.find (fn (name, _) => name = key) fields)
  | json_field _ _ = NONE;
fun json_string key node =
  case json_field key node of SOME (JSON.STRING value) => value | _ => "";
fun first_body node =
  case json_field "body" node of SOME (JSON.ARRAY (head::_)) => head
  | _ => raise Fail "expected a nonempty module or function body";
fun check_offset_runtime name = let
  val json = JSONDecode.decodeFile JSONDecode.raw (fixture_dir ^ name)
  val call = valOf (json_field "value"
    (first_body (first_body (valOf (json_field "ast" json)))))
  val keywords = case json_field "keywords" call of
    SOME (JSON.ARRAY keywords) => keywords | _ => raise Fail "blueprint keywords"
  val keyword = valOf (List.find (fn kw => json_string "arg" kw = "code_offset") keywords)
  val node = JSONDecode.decode jsonASTLib.json_expr (valOf (json_field "value" keyword))
  val th = EVAL ``is_int_literal (origin_fold_value (translate_expr ^residual_ctx ^node))``
  val () = if aconv (rhs (concl th)) ``F`` then ()
           else raise Fail (name ^ ": source-refused selector acquired a literal marker")
  val _ = translate name
in EQF_ELIM th end;
Theorem mixed_bytes_offset_remains_runtime =
  check_offset_runtime "constant_mixed_bytes_offset.json";
Theorem mixed_high_offset_remains_runtime =
  check_offset_runtime "constant_mixed_high_offset.json";

fun returned_source name = let
  val json = JSONDecode.decodeFile JSONDecode.raw (fixture_dir ^ name)
  val value = valOf (json_field "value"
    (first_body (first_body (valOf (json_field "ast" json)))))
in JSONDecode.decode jsonASTLib.json_expr value end;
fun check_refused_fold name = let
  val node = returned_source name
  val th = EVAL ``origin_fold_value (translate_expr ^residual_ctx ^node)``
  val () = if can (find_term (fn term =>
      case strip_comb term of
      (head, _) => is_const head andalso fst (dest_const head) = "Literal"))
      (rhs (concl th)) then () else raise Fail (name ^ ": expected literal operands")
  val (head, _) = strip_comb (rhs (concl th))
  val () = if is_const head andalso fst (dest_const head) <> "Literal" then ()
           else raise Fail (name ^ ": source-refused expression became literal")
  val _ = translate name
in th end;
Theorem mixed_bytes_equality_remains_runtime =
  check_refused_fold "constant_mixed_bytes_equality.json";
Theorem hex_bitwise_remains_runtime = check_refused_fold "constant_hexand.json";
Theorem hex_inversion_remains_runtime = check_refused_fold "constant_hexinvert.json";
val same_class_hex = returned_source "constant_hexeq.json";
val same_class_hex_value = EVAL ``translate_expr ^residual_ctx ^same_class_hex``;
val () = if aconv (rhs (concl same_class_hex_value))
    ``Literal (BaseT BoolT) (BoolL T)`` then ()
  else raise Fail ("same-class Hex equality lost its case-insensitive fold: " ^
    term_to_string (rhs (concl same_class_hex_value)));
Theorem same_class_hex_equality = same_class_hex_value;

val general_builtins = translate "constant_general_builtins.json";
fun check_general_builtin_sites th = let
  val funcs = find_terms (fn tm =>
    case strip_comb tm of
    | (head, [_, _, _, _, _, _, _, _, _]) =>
        same_const head ``vyperAST$FunctionDecl``
    | _ => false) (rhs (concl th))
  fun check name location expected = let
    val decl = valOf (List.find (fn tm =>
      aconv (List.nth (#2 (strip_comb tm), 4))
        (stringSyntax.fromMLstring name)) funcs)
    val site = List.nth (#2 (strip_comb decl), location)
  in
    if can (find_term (aconv expected)) site then ()
    else raise Fail ("missing closed builtin in " ^ name)
  end
  val wei = ``Literal (BaseT (UintT 256)) (IntL 1000000000000000000)``
  val text = ``Literal (BaseT (StringT 78)) (StringL "1")``
  val () = check "wei_default" 6 wei
  val () = check "wei_body" 8 wei
  val () = check "text_default" 6 text
  val () = check "text_body" 8 text
in () end;
val () = check_general_builtin_sites general_builtins;
Theorem general_builtin_body_default_translation = general_builtins;
Theorem general_builtin_body_default_contract_checked =
  checked "constant_general_builtins.json";

Theorem aswei_runtime_original_residual:
  make_builtin_call (BaseT (UintT 256)) "as_wei_value"
    [Name (BaseT (UintT 256)) "amount";
     Literal (BaseT (StringT 5)) (StringL "ether")]
    [] (JT_Integer 256 F) =
  Builtin (BaseT (UintT 256)) (AsWeiValue Ether)
    [Name (BaseT (UintT 256)) "amount"]
Proof
  EVAL_TAC
QED
