Theory sourceConstASTLibTest
Ancestors
  sourceConstAST sourceConstAnnotation sourceConstEval sourceSyntaxLibTest
Libs
  sourceConstASTLib intLib

(* These are decoder/evaluator boundary tests, not a runtime bridge certificate.
   All source arithmetic below is evaluated by HOL, never by test ML code. *)
fun obj fields = JSON.OBJECT fields;
fun str s = JSON.STRING s;
fun arr xs = JSON.ARRAY xs;
fun ast kind fields = obj (("ast_type",str kind)::fields);
fun integer n = ast "Int" [("value",JSON.INT (IntInf.fromInt n))];
fun name s = ast "Name" [("id",str s)];
fun attribute base s = ast "Attribute" [("value",base),("attr",str s)];
fun literal kind s = ast kind [("value",str s)];
fun boolean b = ast "NameConstant" [("value",JSON.BOOL b)];
fun bin kind l r = ast "BinOp"
  [("left",l),("op",ast kind []),("right",r)];
fun unary kind e = ast "UnaryOp" [("op",ast kind []),("operand",e)];
fun compare kind l r = ast "Compare"
  [("left",l),("op",ast kind []),("right",r)];
fun boolop kind es = ast "BoolOp" [("op",ast kind []),("values",arr es)];
fun sequence kind es = ast kind [("elements",arr es)];
fun subscript base index = ast "Subscript" [("value",base),("slice",index)];
fun kw key value = obj [("arg",str key),("value",value)];
fun call callee args keywords = ast "Call"
  [("func",callee),("args",arr args),("keywords",arr keywords)];
fun qualify q inner = call (name q) [inner] [];
val de = JSONDecode.decode sourceConstASTLib.expression;
val da = JSONDecode.decode sourceConstASTLib.annotation;
fun checked label actual expected = let
  val th = EVAL (mk_eq (actual,expected))
in if aconv (rhs (concl th)) boolSyntax.T then EQT_ELIM th
   else raise Fail (label ^ ": " ^ term_to_string (concl th)) end;
fun test_expr (label,json,expected) = ignore (checked label (de json) expected);
fun test_ann (label,json,expected) = ignore (checked label (da json) expected);
fun rejects label decoder json =
  if (JSONDecode.decode decoder json; false) handle JSONDecode.JSONError _ => true
  then () else raise Fail ("accepted malformed source: " ^ label);

(* Two different, WELL-FORMED folded literals and inferred integer type claims,
   injected recursively. Neither deletion nor replacement may change syntax.
   Also poison the declaration flags/source identities that this API ignores. *)
fun metadata_key s = List.exists (fn key => s = key)
  ["folded_value","type","is_constant","is_immutable","is_public","source_id"];
fun metadata replacement bits (JSON.OBJECT fields) = obj
      (("folded_value",replacement)::
       ("type",obj [("typeclass",str "integer"),("bits",JSON.INT bits),
                    ("is_signed",JSON.BOOL false)])::
       ("is_constant",JSON.BOOL true)::("is_immutable",JSON.BOOL true)::
       ("is_public",JSON.BOOL true)::("source_id",JSON.INT 999)::
       List.map (fn (k,v) => (k,metadata replacement bits v))
         (List.filter (fn (k,_) => not (metadata_key k)) fields))
  | metadata replacement bits (JSON.ARRAY xs) =
      arr (List.map (metadata replacement bits) xs)
  | metadata _ _ value = value;
fun deleted (JSON.OBJECT fields) = obj (List.map (fn (k,v) => (k,deleted v))
      (List.filter (fn (k,_) => not (metadata_key k)) fields))
  | deleted (JSON.ARRAY xs) = arr (List.map deleted xs)
  | deleted value = value;
fun variants json = [json,deleted json,metadata (integer 7) 8 json,
                    metadata (integer 42) 256 json,
                    metadata (boolean true) 128 json];
fun independent label decoder json = let val expected = JSONDecode.decode decoder json in
  app (fn variant => if aconv expected (JSONDecode.decode decoder variant) then ()
    else raise Fail (label ^ " depends on metadata")) (variants json)
end;
fun reject_variants label decoder json =
  app (rejects label decoder) (variants json);

(* ===== Literals and every operator ===== *)
val () = app test_expr
  [("unbounded integer",JSONDecode.decodeString JSONDecode.raw
      "{\"ast_type\":\"Int\",\"value\":115792089237316195423570985008687907853269984665640564039457584007913129639936}",
      ``SCE_Literal (SCL_Int (2 ** 256))``),
   ("negative integer",integer (~7),``SCE_Literal (SCL_Int (-7))``),
   ("Boolean",boolean false,``SCE_Literal (SCL_Bool F)``),
   ("string without inferred capacity",literal "Str" "foo()",
      ``SCE_Literal (SCL_String "foo()")``),
   ("bytes hexadecimal encoding",literal "Bytes" "0x0001fF",
      ``SCE_Literal (SCL_Bytes [0;1;255])``),
   ("HexBytes",literal "HexBytes" "0xDeAd",``SCE_Literal (SCL_Bytes [222;173])``),
   ("empty bytes",literal "Bytes" "0x",``SCE_Literal (SCL_Bytes [])``),
   ("hex spelling remains distinct",literal "Hex" "0xaAbB",
      ``SCE_Literal (SCL_Hex "0xaAbB")``),
   ("exact decimal",literal "Decimal" "9007199254740993.0000000001",
      ``SCE_Literal (SCL_Decimal 90071992547409930000000001 10)``),
   ("decimal underscores",literal "Decimal" "-1_234.5_600",
      ``SCE_Literal (SCL_Decimal (-12345600) 4)``),
   ("decimal leading dot",literal "Decimal" ".0000000001",
      ``SCE_Literal (SCL_Decimal 1 10)``),
   ("decimal trailing dot",literal "Decimal" "12.",``SCE_Literal (SCL_Decimal 12 0)``),
   ("decimal negative exponent",literal "Decimal" "1.230e-2",
      ``SCE_Literal (SCL_Decimal 1230 5)``),
   ("decimal positive exponent",literal "Decimal" "+1.230E+5",
      ``SCE_Literal (SCL_Decimal 123000 0)``),
   ("decimal fractional exponent",literal "Decimal" "1.230e+2",
      ``SCE_Literal (SCL_Decimal 1230 1)``)];

val binary_ops = [("Add",``SCB_Add``),("Sub",``SCB_Sub``),("Mult",``SCB_Mul``),
  ("Div",``SCB_Div``),("FloorDiv",``SCB_FloorDiv``),("Mod",``SCB_Mod``),
  ("Pow",``SCB_Pow``),("LShift",``SCB_LShift``),("RShift",``SCB_RShift``),
  ("BitAnd",``SCB_BitAnd``),("BitOr",``SCB_BitOr``),("BitXor",``SCB_BitXor``)];
val comparison_ops = [("Eq",``SCC_Eq``),("NotEq",``SCC_NotEq``),("Lt",``SCC_Lt``),
  ("LtE",``SCC_Le``),("Gt",``SCC_Gt``),("GtE",``SCC_Ge``),
  ("In",``SCC_In``),("NotIn",``SCC_NotIn``)];
val () = app (fn (spelling,op_tm) => test_expr (spelling,
  bin spelling (integer 1) (integer 2),
  ``SCE_Binary ^op_tm (SCE_Literal (SCL_Int 1)) (SCE_Literal (SCL_Int 2))``)) binary_ops;
val () = app (fn (spelling,op_tm) => test_expr (spelling,
  compare spelling (integer 1) (integer 2),
  ``SCE_Compare ^op_tm (SCE_Literal (SCL_Int 1)) (SCE_Literal (SCL_Int 2))``)) comparison_ops;
val () = app (fn (spelling,op_tm) => test_expr (spelling,unary spelling (integer 1),
  ``SCE_Unary ^op_tm (SCE_Literal (SCL_Int 1))``))
  [("USub",``SCU_Neg``),("Not",``SCU_Not``),("Invert",``SCU_Invert``)];
val () = app (fn (spelling,op_tm) => test_expr (spelling,
  boolop spelling [name "a",name "b",name "c"],
  ``SCE_Boolean ^op_tm [SCE_Name ["a"]; SCE_Name ["b"]; SCE_Name ["c"]]``))
  [("And",``SCB_And``),("Or",``SCB_Or``)];

val nested = sequence "Tuple" [sequence "List" [integer 1,unary "USub" (integer 2)],
  subscript (attribute (attribute (name "lib") "constants") "N") (integer 0)];
Theorem source_decoder_preserves_aggregate_and_path = checked "nested source" (de nested)
  ``SCE_Tuple [SCE_List [SCE_Literal (SCL_Int 1);
      SCE_Unary SCU_Neg (SCE_Literal (SCL_Int 2))];
    SCE_Subscript (SCE_Name ["lib";"constants";"N"]) (SCE_Literal (SCL_Int 0))]``;
val () = independent "all expression forms" sourceConstASTLib.expression
  (sequence "List" [nested, boolop "And" [boolean false,
    compare "Eq" (bin "FloorDiv" (integer 1) (integer 0)) (integer 0)]]);

(* ===== Unresolved calls, ordered positional/keyword syntax ===== *)
val method_call = call (name "method_id") [literal "Str" "foo()"]
  [kw "output_type" (subscript (name "Bytes") (integer 4))];
Theorem source_decoder_does_not_resolve_builtin_spelling =
  checked "unresolved method_id" (de method_call)
    ``SCE_Call (SCE_Name ["method_id"]) [SCE_Literal (SCL_String "foo()")]
      [("output_type", SCE_Subscript (SCE_Name ["Bytes"]) (SCE_Literal (SCL_Int 4)))]``;
val () = app (fn spelling => test_expr ("unresolved " ^ spelling,
  call (name spelling) [integer 1] [],
  ``SCE_Call (SCE_Name [^(stringSyntax.fromMLstring spelling)])
      [SCE_Literal (SCL_Int 1)] []``))
  ["len","keccak256","sha256","min","max","convert","concat","abs"];
val indirect_call = call (subscript (name "factories") (integer 0))
  [name "x",name "y"] [kw "second" (boolean false),kw "first" (integer 3)];
val () = test_expr ("callee and keyword order",indirect_call,
  ``SCE_Call (SCE_Subscript (SCE_Name ["factories"]) (SCE_Literal (SCL_Int 0)))
    [SCE_Name ["x"]; SCE_Name ["y"]]
    [("second",SCE_Literal (SCL_Bool F)); ("first",SCE_Literal (SCL_Int 3))]``);
val () = app (independent "calls" sourceConstASTLib.expression) [method_call,indirect_call];

(* ===== Reusable source annotations: no inferred widths or lengths ===== *)
val bound3 = bin "Add" (bin "RShift"
  (bin "LShift" (integer 1) (integer 256)) (integer 255)) (integer 1);
val ann_bound = subscript (name "uint256") bound3;
Theorem source_decoder_preserves_bound = checked "source bound" (da ann_bound)
  ``SCA_StaticArray (SCA_Name ["uint256"])
    (SCE_Binary SCB_Add
      (SCE_Binary SCB_RShift
        (SCE_Binary SCB_LShift (SCE_Literal (SCL_Int 1)) (SCE_Literal (SCL_Int 256)))
        (SCE_Literal (SCL_Int 255))) (SCE_Literal (SCL_Int 1)))``;
Theorem source_decoder_bound_computes_without_wrapping = checked "unbounded source arithmetic"
  ``source_const_eval [] ^(de bound3)`` ``SC_Value (SCV_Int 3)``;
val complex_annotation = qualify "public" (subscript (name "HashMap")
  (sequence "Tuple" [name "address",subscript (name "DynArray")
    (sequence "Tuple" [subscript (name "Bytes") (bin "Add" (name "N") (integer 1)),
                       name "M"])]));
Theorem source_decoder_nested_annotations = checked "nested HashMap" (da complex_annotation)
  ``SCA_Qualified SCQ_Public (SCA_HashMap (SCA_Name ["address"])
    (SCA_DynArray (SCA_Bytes (SCE_Binary SCB_Add (SCE_Name ["N"])
      (SCE_Literal (SCL_Int 1)))) (SCE_Name ["M"])))``;
val () = app test_ann
  [("nested static array",subscript ann_bound (name "M"),
      ``SCA_StaticArray ^(da ann_bound) (SCE_Name ["M"])``),
   ("String source bound",subscript (name "String") (name "N"),
      ``SCA_String (SCE_Name ["N"])``),
   ("qualified nominal",attribute (name "lib") "Thing",``SCA_Name ["lib";"Thing"]``),
   ("tuple annotation",sequence "Tuple" [name "bool",subscript (name "Bytes") (integer 4)],
      ``SCA_Tuple [SCA_Name ["bool"];SCA_Bytes (SCE_Literal (SCL_Int 4))]``)];
val () = app (fn (spelling,qualifier) => test_ann (spelling,
  qualify spelling ann_bound,``SCA_Qualified ^qualifier ^(da ann_bound)``))
  [("constant",``SCQ_Constant``),("immutable",``SCQ_Immutable``),
   ("transient",``SCQ_Transient``),("indexed",``SCQ_Indexed``),("public",``SCQ_Public``)];
val () = app (independent "annotations" sourceConstASTLib.annotation)
  [ann_bound,complex_annotation,qualify "constant" (subscript (name "String") (integer 4))];

(* ===== Absence is not failed decoding ===== *)
val optional_annotation = sourceConstASTLib.annotation_field "annotation";
val () = app (fn json => case JSONDecode.decode optional_annotation json of
    NONE => () | SOME _ => raise Fail "absent optional annotation")
  [obj [],obj [("annotation",JSON.NULL)]];
val () = case JSONDecode.decode optional_annotation (obj [("annotation",ann_bound)]) of
    SOME term => ignore (checked "present optional annotation" term (da ann_bound))
  | NONE => raise Fail "present annotation became absent";
val () = rejects "null present optional expression" (sourceConstASTLib.optional_field
  "value" sourceConstASTLib.expression) (obj [("value",JSON.NULL)]);
val () = rejects "null required annotation" sourceConstASTLib.annotation JSON.NULL;

(* ===== Bad originals cannot be rescued by good folded/type metadata ===== *)
val malformed_expressions =
  [ast "Int" [("value",str "1")], ast "Int" [],
   literal "Decimal" "1.0 / 3.0", literal "Decimal" "1.2junk",
   literal "Decimal" "_1.0", literal "Decimal" "1_.0", literal "Decimal" "1._0",
   literal "Decimal" "1.0_", literal "Decimal" "1.0e", literal "Decimal" "1e_2",
   literal "Decimal" "NaN", literal "Decimal" "Infinity", literal "Decimal" "1e2e3",
   literal "Bytes" "abc",literal "Bytes" "0x0",literal "Bytes" "0x0g",
   literal "Hex" "0Xaa",literal "Hex" "0x",literal "Hex" "0x0_",
   ast "NameConstant" [("value",JSON.INT 1)], name "a.b",
   ast "Attribute" [("value",integer 1),("attr",str "x")],
   bin "Unknown" (integer 1) (integer 2),
   ast "BinOp" [("op",ast "Add" []),("left",integer 1)],
   subscript (name "x") JSON.NULL,
   ast "Call" [("func",name "len"),("args",arr [])],
   ast "Call" [("func",name "len"),("args",arr []),("keywords",JSON.NULL)],
   call (name "len") [] [obj [("arg",JSON.NULL),("value",integer 1)]],
   ast "IfExp" [], ast "Int" [("value",JSON.INT 1),("value",JSON.INT 2)]];
val () = app (reject_variants "expression" sourceConstASTLib.expression) malformed_expressions;
val malformed_annotations =
  [name "String",name "Bytes",name "DynArray",name "HashMap",
   subscript (name "String") JSON.NULL,
   ast "Subscript" [("value",name "Bytes")],
   subscript (name "DynArray") (sequence "Tuple" [name "uint256"]),
   subscript (name "DynArray") (sequence "Tuple" [name "uint256",integer 3,integer 4]),
   subscript (name "HashMap") (sequence "Tuple" [name "address",JSON.NULL]),
   subscript (name "HashMap") (sequence "Tuple" [name "address",name "bool",name "bool"]),
   call (name "constant") [] [],call (name "constant") [name "uint256",name "bool"] [],
   call (name "indexed") [name "uint256"] [kw "ignored" (integer 1)],
   call (name "mystery") [name "uint256"] [],
   subscript (name "Bytes") (literal "Decimal" "2+2")];
val () = app (reject_variants "annotation" sourceConstASTLib.annotation) malformed_annotations;
val () = app (fn annotation => reject_variants "malformed optional annotation"
  optional_annotation (obj [("annotation",annotation)])) malformed_annotations;

(* Domain errors are intentionally preserved, not repaired in ML. The HOL
   evaluator must still reject them after every well-formed metadata poison. *)
val divide_zero = bin "FloorDiv" (integer 1) (integer 0);
val eager_error = boolop "And" [boolean false,compare "Eq" divide_zero (integer 0)];
val bad_shift = bin "LShift" (integer 1) (integer 257);
val bad_domain = bin "Add" (boolean true) (integer 0);
val bad_precision = literal "Decimal" "0.00000000001";
val () = app (fn (json,expected) => app (fn variant =>
  ignore (checked "invalid source remains invalid"
    ``source_const_eval [] ^(de variant)`` expected)) (variants json))
  [(divide_zero,``SC_Invalid SCErr_ZeroDivisor : source_const_value source_const_result``),
   (eager_error,``SC_Invalid SCErr_ZeroDivisor : source_const_value source_const_result``),
   (bad_shift,``SC_Invalid SCErr_ShiftCount : source_const_value source_const_result``),
   (bad_domain,``SC_Invalid SCErr_Domain : source_const_value source_const_result``),
   (bad_precision,``SC_Invalid SCErr_DecimalPrecision : source_const_value source_const_result``)];
Theorem source_decoder_invalid_original_not_rescued =
  checked "invalid Boolean original with good metadata"
    ``source_const_eval [] ^(de (metadata (boolean true) 256 eager_error))``
    ``SC_Invalid SCErr_ZeroDivisor : source_const_value source_const_result``;
Theorem source_decoder_decimal_exact_in_HOL = checked "exact scaled decimal"
  ``source_const_eval [] ^(de (literal "Decimal" "9007199254740993.0000000001"))``
  ``SC_Value (SCV_Decimal 90071992547409930000000001)``;
