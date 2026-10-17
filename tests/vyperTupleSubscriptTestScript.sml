(* Issue #337: tuple indices are literal, unlike array indices. *)
Theory vyperTupleSubscriptTest
Ancestors
  finite_map integer list vyperAST vyperTypeSystem jsonToVyperExpr
Libs
  jsonASTLib vyperCheckContractLib

Theorem homogeneous_tuple_dynamic_index_rejected:
  ~well_typed_expr env
    (Subscript (BaseT (UintT 256))
      (Name (TupleT [BaseT (UintT 256); BaseT (UintT 256)]) "pair")
      (Name (BaseT (UintT 256)) "index"))
Proof
  EVAL_TAC >> simp[]
QED

Theorem homogeneous_tuple_literal_index_accepted:
  well_typed_expr env
    (Name (TupleT [BaseT (UintT 256); BaseT (UintT 256)]) "pair") ==>
  well_typed_expr env
    (Subscript (BaseT (UintT 256))
      (Name (TupleT [BaseT (UintT 256); BaseT (UintT 256)]) "pair")
      (Literal (BaseT (UintT 256)) (IntL 1)))
Proof
  EVAL_TAC >> simp[]
QED

Theorem heterogeneous_tuple_first_literal_accepted:
  well_typed_expr env
    (Name (TupleT [BaseT (UintT 256); BaseT BoolT]) "pair") ==>
  well_typed_expr env
    (Subscript (BaseT (UintT 256))
      (Name (TupleT [BaseT (UintT 256); BaseT BoolT]) "pair")
      (Literal (BaseT (UintT 256)) (IntL 0)))
Proof
  EVAL_TAC >> simp[]
QED

Theorem heterogeneous_tuple_last_literal_accepted:
  well_typed_expr env
    (Name (TupleT [BaseT (UintT 256); BaseT BoolT]) "pair") ==>
  well_typed_expr env
    (Subscript (BaseT BoolT)
      (Name (TupleT [BaseT (UintT 256); BaseT BoolT]) "pair")
      (Literal (BaseT (UintT 256)) (IntL 1)))
Proof
  EVAL_TAC >> simp[]
QED

Theorem tuple_negative_literal_rejected:
  ~well_typed_expr env
    (Subscript (BaseT (UintT 256))
      (Name (TupleT [BaseT (UintT 256); BaseT (UintT 256)]) "pair")
      (Literal (BaseT (IntT 256)) (IntL (-1))))
Proof
  EVAL_TAC >> simp[]
QED

Theorem tuple_length_literal_rejected:
  ~well_typed_expr env
    (Subscript (BaseT (UintT 256))
      (Name (TupleT [BaseT (UintT 256); BaseT (UintT 256)]) "pair")
      (Literal (BaseT (UintT 256)) (IntL 2)))
Proof
  EVAL_TAC >> simp[]
QED

Theorem empty_tuple_literal_rejected:
  ~well_typed_expr env
    (Subscript (BaseT (UintT 256))
      (Name (TupleT []) "empty")
      (Literal (BaseT (UintT 256)) (IntL 0)))
Proof
  EVAL_TAC >> simp[]
QED

Theorem heterogeneous_tuple_wrong_result_rejected:
  ~well_typed_expr env
    (Subscript (BaseT (UintT 256))
      (Name (TupleT [BaseT (UintT 256); BaseT BoolT]) "pair")
      (Literal (BaseT (UintT 256)) (IntL 1)))
Proof
  EVAL_TAC >> simp[]
QED

Theorem tuple_noninteger_literal_rejected:
  ~well_typed_expr env
    (Subscript (BaseT (UintT 256))
      (Name (TupleT [BaseT (UintT 256)]) "single")
      (Literal (BaseT BoolT) (BoolL F)))
Proof
  EVAL_TAC >> simp[]
QED

Theorem tuple_computed_index_rejected:
  ~well_typed_expr env
    (Subscript (BaseT (UintT 256))
      (Name (TupleT [BaseT (UintT 256); BaseT (UintT 256)]) "pair")
      (IfExp (BaseT (UintT 256))
        (Literal (BaseT BoolT) (BoolL T))
        (Literal (BaseT (UintT 256)) (IntL 0))
        (Literal (BaseT (UintT 256)) (IntL 1))))
Proof
  EVAL_TAC >> simp[]
QED

Theorem fixed_array_dynamic_index_accepted:
  well_typed_expr env
    (Name (ArrayT (BaseT (UintT 256)) (Fixed 2)) "array") /\
  well_typed_expr env (Name (BaseT (UintT 256)) "index") ==>
  well_typed_expr env
    (Subscript (BaseT (UintT 256))
      (Name (ArrayT (BaseT (UintT 256)) (Fixed 2)) "array")
      (Name (BaseT (UintT 256)) "index"))
Proof
  EVAL_TAC >> simp[]
QED

Theorem dynamic_array_dynamic_index_accepted:
  well_typed_expr env
    (Name (ArrayT (BaseT (UintT 256)) (Dynamic 2)) "array") /\
  well_typed_expr env (Name (BaseT (UintT 256)) "index") ==>
  well_typed_expr env
    (Subscript (BaseT (UintT 256))
      (Name (ArrayT (BaseT (UintT 256)) (Dynamic 2)) "array")
      (Name (BaseT (UintT 256)) "index"))
Proof
  EVAL_TAC >> simp[]
QED

Theorem tuple_signed_nonnegative_literal_accepted:
  well_typed_expr env
    (Name (TupleT [BaseT (UintT 256); BaseT BoolT]) "pair") ==>
  well_typed_expr env
    (Subscript (BaseT BoolT)
      (Name (TupleT [BaseT (UintT 256); BaseT BoolT]) "pair")
      (Literal (BaseT (IntT 256)) (IntL 1)))
Proof
  EVAL_TAC >> simp[]
QED

(* Array bounds remain a runtime check, not a tuple-style static check. *)
Theorem array_out_of_bounds_literal_still_typed:
  well_typed_expr env
    (Name (ArrayT (BaseT (UintT 256)) (Fixed 2)) "array") ==>
  well_typed_expr env
    (Subscript (BaseT (UintT 256))
      (Name (ArrayT (BaseT (UintT 256)) (Fixed 2)) "array")
      (Literal (BaseT (UintT 256)) (IntL 2)))
Proof
  EVAL_TAC >> simp[]
QED

(* Exercise the production checker conversion, not only EVAL's rewrite set. *)
val tuple_value =
  ``Builtin (TupleT [BaseT (UintT 256); BaseT BoolT])
      (MakeArray NONE (Fixed 2))
      [Literal (BaseT (UintT 256)) (IntL 7); Literal (BaseT BoolT) (BoolL T)]``;
fun check_tuple_index index = vyperCheckContractLib.check_contract_conv
  (vyperCheckContractLib.mk_check_contract
  {in_deploy = false, address = ``0w : address``,
   layouts = ``[] : (address # (storage_layout # storage_layout)) list``,
   modules = ``[(NONE, [FunctionDecl External Pure F F "select"
     [("index", BaseT (UintT 256))] [] (BaseT BoolT)
     [Return (SOME (Subscript (BaseT BoolT) ^tuple_value ^index))]])]
       : (num option # toplevel list) list``});
val () = if optionSyntax.is_some (rhs (concl
  (check_tuple_index ``Literal (BaseT (UintT 256)) (IntL 1)``)))
  then () else raise Fail "checker rejected heterogeneous literal tuple index";
val () = if optionSyntax.is_none (rhs (concl
  (check_tuple_index ``Name (BaseT (UintT 256)) "index"``)))
  then () else raise Fail "checker accepted dynamic tuple index";

(* Compiler-folded tuple indices become literals; ordinary array indexing
   continues to translate the expression rather than its folded metadata. *)
val uint_json =
  "{\"typeclass\":\"integer\",\"bits\":256,\"is_signed\":false}";
val computed_index_json =
  "{\"ast_type\":\"BinOp\",\"left\":{\"ast_type\":\"Int\",\"value\":0}," ^
  "\"op\":{\"ast_type\":\"Add\"},\"right\":{\"ast_type\":\"Int\",\"value\":1}," ^
  "\"type\":" ^ uint_json ^ ",\"folded_value\":{\"ast_type\":\"Int\"," ^
  "\"value\":1,\"type\":" ^ uint_json ^ "}}";
fun decode_subscript base_type index_json = let
  val source = "{\"ast_type\":\"Subscript\",\"value\":{\"ast_type\":\"Name\"," ^
    "\"id\":\"xs\",\"type\":" ^ base_type ^ "},\"slice\":" ^
    index_json ^ ",\"type\":" ^ uint_json ^ "}"
  val ast = JSONDecode.decodeString jsonASTLib.annotated_ast
    ("{\"ast\":{\"body\":[{\"ast_type\":\"FunctionDef\",\"name\":\"test\",\"decorator_list\":[]," ^
     "\"args\":{\"ast_type\":\"arguments\",\"args\":[]},\"func_type\":{\"argument_types\":[],\"return_type\":null}," ^
     "\"body\":[{\"ast_type\":\"Expr\",\"value\":" ^ source ^ "}]}]}}")
  val subscript_tm = prim_mk_const {Thy = "jsonAST", Name = "JE_Subscript"}
in
  case find_terms (fn tm => let val (head, args) = strip_comb tm in
    aconv head subscript_tm andalso length args = 3 end) ast of
    [subscript] => subscript
  | _ => raise Fail "expected one decoded subscript"
end;
val folded_tuple = decode_subscript
  ("{\"typeclass\":\"tuple\",\"member_types\":[" ^ uint_json ^ "," ^ uint_json ^ "]}")
  computed_index_json;
val translated_tuple = rhs (concl (EVAL
  ``translate_expr (0,NONE,[],[],[],[]) ^folded_tuple``));
val () = if aconv translated_tuple
  ``Subscript (BaseT (UintT 256))
      (Name (TupleT [BaseT (UintT 256); BaseT (UintT 256)]) "xs")
      (Literal (BaseT (UintT 256)) (IntL 1))``
  then () else raise Fail "folded tuple index was not translated as a literal";
val folded_array = decode_subscript
  ("{\"typeclass\":\"static_array\",\"value_type\":" ^ uint_json ^ ",\"length\":2}")
  computed_index_json;
val translated_array = rhs (concl (EVAL
  ``translate_expr (0,NONE,[],[],[],[]) ^folded_array``));
val () = if can (find_term (aconv ``Bop Add``)) translated_array
  then () else raise Fail "array index expression was unexpectedly folded";

(* Optional folded annotations must not erase a known slice type. Keep an
   explicit folded type authoritative, and reject indices with no known type. *)
fun check_folded_index label source expected accepted = let
  val decoded = decode_subscript
    ("{\"typeclass\":\"tuple\",\"member_types\":[" ^ uint_json ^ "," ^ uint_json ^ "]}")
    source
  val translated = rhs (concl (EVAL
    ``translate_expr (0,NONE,[],[],[],[]) ^decoded``))
  val index = case strip_comb translated of
      (_, [_, _, index]) => index
    | _ => raise Fail ("expected translated subscript: " ^ label)
  val checked = rhs (concl (check_tuple_index index))
in
  if aconv index expected andalso optionSyntax.is_some checked = accepted
  then () else raise Fail ("folded index type regression: " ^ label)
end;
val typed_index_prefix =
  "{\"ast_type\":\"Int\",\"value\":1,\"type\":" ^ uint_json;
val untyped_folded_index =
  ",\"folded_value\":{\"ast_type\":\"Int\",\"value\":1}}";
val uint_index = ``Literal (BaseT (UintT 256)) (IntL 1)``;
val () = check_folded_index "literal inherits slice type"
  (typed_index_prefix ^ untyped_folded_index) uint_index true;
val () = check_folded_index "computed index inherits slice type"
  ("{\"ast_type\":\"BinOp\",\"left\":{\"ast_type\":\"Int\",\"value\":0}," ^
   "\"op\":{\"ast_type\":\"Add\"},\"right\":{\"ast_type\":\"Int\",\"value\":1}," ^
   "\"type\":" ^ uint_json ^ untyped_folded_index) uint_index true;
val () = check_folded_index "null folded type inherits slice type"
  (typed_index_prefix ^
   ",\"folded_value\":{\"ast_type\":\"Int\",\"value\":1,\"type\":null}}")
  uint_index true;
val () = check_folded_index "explicit invalid folded type is not replaced"
  (typed_index_prefix ^
   ",\"folded_value\":{\"ast_type\":\"Int\",\"value\":1,\"type\":{\"name\":\"bool\"}}}")
  ``Literal (BaseT BoolT) (IntL 1)`` false;
val () = check_folded_index "missing both types remains rejected"
  ("{\"ast_type\":\"Int\",\"value\":1" ^ untyped_folded_index)
  ``Literal NoneT (IntL 1)`` false;
