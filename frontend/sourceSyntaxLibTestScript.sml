Theory sourceSyntaxLibTest
Ancestors
  sourceSyntax sourceConstAnnotation
Libs
  sourceSyntaxLib

(* Decode/retention tests ONLY. All 37 sources must decode, INCLUDING the
   source-invalid method_id_var. No source evaluator/checker/compiler is run. *)
fun holbuild_extra_deps (_ : string list) = ();
val () = holbuild_extra_deps
  ["../lowering/defs/bytecode/folded-value-witnesses.txt",
   "../lowering/defs/bytecode/folded-value-oracle",
   "../tests/fixtures/check_contract/source_syntax",
   "../lowering/defs/bytecode/folded-value-sources",
   "../tests/fixtures/check_contract/imported_deploy/main.json",
   "../tests/fixtures/check_contract/defaults_control/main.json"];

fun obj fs = JSON.OBJECT fs;
fun str s = JSON.STRING s;
fun arr xs = JSON.ARRAY xs;
fun ast kind fs = obj (("ast_type",str kind)::fs);
fun integer n = ast "Int" [("value",JSON.INT (IntInf.fromInt n))];
fun name n = ast "Name" [("id",str n)];
fun bin oper l r = ast "BinOp" [("op",ast oper []),("left",l),("right",r)];
fun kw n v = ast "keyword" [("arg",str n),("value",v)];
fun call callee args kws = ast "Call" [("func",callee),("args",arr args),("keywords",arr kws)];
fun subscript base index = ast "Subscript" [("value",base),("slice",index)];
fun tuple es = ast "Tuple" [("elements",arr es)];
fun qualify q ann = call (name q) [ann] [];
fun module_json ds = ast "Module" [("body",arr ds)];
fun program_json ds imports = obj [("ast",module_json ds),("imports",arr imports)];
fun variable n ann value = ast "VariableDecl"
  [("target",name n),("annotation",ann),("value",value)];
fun func n args defaults ret body = ast "FunctionDef"
  [("name",str n),("decorator_list",arr [name "external"]),
   ("args",ast "arguments" [("args",arr args),("defaults",arr defaults)]),
   ("returns",ret),("body",arr body)];
fun ret e = ast "Return" [("value",e)];
fun arg n ann = ast "arg" [("arg",str n),("annotation",ann)];
val de = JSONDecode.decode sourceSyntaxLib.expression;
val ds = JSONDecode.decode sourceSyntaxLib.statement;
val dd = JSONDecode.decode sourceSyntaxLib.declaration;
val dp = JSONDecode.decode sourceSyntaxLib.annotated_ast;
val dap = JSONDecode.decode sourceSyntaxLib.annotated_ast_with_provenance;
fun checked label actual expected = let val th = EVAL (mk_eq (actual,expected)) in
  if aconv (rhs (concl th)) boolSyntax.T then EQT_ELIM th
  else raise Fail (label ^ ": " ^ term_to_string (concl th)) end;
fun rejects label decoder json =
  if (JSONDecode.decode decoder json; false) handle JSONDecode.JSONError _ => true
  then () else raise Fail ("accepted malformed present syntax: " ^ label);
fun contains expected tm = aconv expected tm orelse
  (is_comb tm andalso (contains expected (rator tm) orelse contains expected (rand tm)));
fun require_subterm label expected tm = if contains expected tm then ()
  else raise Fail (label ^ " lacks original syntax " ^ term_to_string expected);

(* Delete or inject DIFFERENT WELL-FORMED folds at every object, not merely
   malformed poison. Inferred claims/qualifier flags are separately poisoned.
   Source identities are provenance claims and never enter semantic terms. *)
val ignored = ["folded_value","type","func_type","is_constant","is_immutable",
  "is_public","is_transient","is_reentrant","source_id"];
fun transform inserts (JSON.OBJECT fs) = obj (inserts @ List.map
      (fn (k,v) => (k,transform inserts v))
      (List.filter (fn (k,_) => not (List.exists (fn s => k = s) ignored)) fs))
  | transform inserts (JSON.ARRAY xs) = arr (List.map (transform inserts) xs)
  | transform _ v = v;
fun poisoned fold = transform [("folded_value",fold),
  ("type",obj [("typeclass",str "integer"),("bits",JSON.INT 8)]),
  ("func_type",JSON.NULL),("is_constant",JSON.BOOL true),
  ("is_immutable",JSON.BOOL true),("is_public",JSON.BOOL true),
  ("is_transient",JSON.BOOL true),("source_id",JSON.INT 999)];
fun fold_only replacement (JSON.OBJECT fs) = obj
      ((case replacement of NONE => [] | SOME v => [("folded_value",v)]) @
       List.map (fn (k,v) => (k,fold_only replacement v))
         (List.filter (fn (k,_) => k <> "folded_value") fs))
  | fold_only replacement (JSON.ARRAY xs) = arr (List.map (fold_only replacement) xs)
  | fold_only _ v = v;
fun variants json = [json,transform [] json,poisoned (integer 7) json,
  poisoned (integer 42) json,
  poisoned (ast "NameConstant" [("value",JSON.BOOL false)]) json];
fun independent label decoder json = let val original = JSONDecode.decode decoder json in
  app (fn v => if aconv original (JSONDecode.decode decoder v) then ()
    else raise Fail (label ^ " depends on compiler metadata")) (variants json)
end;

(* Every row pins an ORIGINAL domain, not its compiler replacement result. *)
val expected_domains =
  [("pow_folded_exp", ``SX_Binary SCB_Add (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 2))``),
   ("pow_negfold_base", ``SX_Binary SCB_Sub (SX_Literal (SCL_Int 0)) (SX_Literal (SCL_Int 2))``),
   ("fold_add", ``SX_Binary SCB_Add (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 2))``),
   ("fold_pow_lit", ``SX_Binary SCB_Pow (SX_Literal (SCL_Int 2)) (SX_Literal (SCL_Int 8))``),
   ("fold_cmp", ``SX_Compare SCC_Lt (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 2))``),
   ("fold_not", ``SX_Unary SCU_Not (SX_Literal (SCL_Bool T))``),
   ("fold_shift", ``SX_Binary SCB_LShift (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 4))``),
   ("fold_minmax", ``SX_Call (SX_Name "min") [SX_Literal (SCL_Int 3);SX_Literal (SCL_Int 5)] []``),
   ("fold_powmod", ``SX_Call (SX_Name "pow_mod256") [SX_Literal (SCL_Int 2);SX_Literal (SCL_Int 10)] []``),
   ("fold_addmod", ``SX_Call (SX_Name "uint256_addmod") [SX_Literal (SCL_Int 5);SX_Literal (SCL_Int 6);SX_Literal (SCL_Int 7)] []``),
   ("fold_abs", ``SX_Call (SX_Name "abs") [SX_Literal (SCL_Int (-5))] []``),
   ("keccak_literal", ``SX_Call (SX_Name "keccak256") [SX_Literal (SCL_String "hello")] []``),
   ("len_string_lit", ``SX_Call (SX_Name "len") [SX_Literal (SCL_String "abcd")] []``),
   ("method_id_b4", ``SX_Call (SX_Name "method_id") [SX_Literal (SCL_String "transfer(address,uint256)")]
     [("output_type",SX_Name "bytes4")]``),
   ("method_id_bytes", ``SX_Call (SX_Name "method_id") [SX_Literal (SCL_String "transfer(address,uint256)")] []``),
   ("method_id_const", ``SX_Literal (SCL_String "foo()")``),
   ("method_id_storage", ``SX_Attribute (SX_Name "self") "m"``),
   ("method_id_var", ``SX_Call (SX_Name "method_id") [SX_Name "s"] [("output_type",SX_Name "bytes4")]``),
   ("enc_mid_const", ``SX_Call (SX_Name "abi_encode") [SX_Name "a"]
     [("ensure_tuple",SX_Literal (SCL_Bool F));("method_id",SX_Name "M")]``),
   ("enc_mid_methodid_call", ``SX_Call (SX_Name "method_id") [SX_Literal (SCL_String "foo()")] []``),
   ("enc_mid_bytes4lit", ``SX_Literal (SCL_Bytes [222;173;190;239])``),
   ("enc_ensF_string_mid", ``SourceArg "a" (SOME (SCA_String (SCE_Literal (SCL_Int 40))))``),
   ("enc_ensF_uint_mid", ``SX_Call (SX_Name "abi_encode") [SX_Name "a"]
     [("ensure_tuple",SX_Literal (SCL_Bool F));("method_id",SX_Literal (SCL_Hex "0xdeadbeef"))]``),
   ("enc_ensure_const", ``SX_Call (SX_Name "abi_encode") [SX_Name "a"]
     [("ensure_tuple",SX_Name "E");("method_id",SX_Literal (SCL_Hex "0xdeadbeef"))]``),
   ("dec_unwrap_const", ``SX_Call (SX_Name "abi_decode")
     [SX_Name "d";SX_Tuple [SX_Name "uint256";SX_Name "bool"]] [("unwrap_tuple",SX_Name "U")]``),
   ("ctl03_abi_method_id", ``SX_Literal (SCL_String "f(uint256)")``),
   ("enc_ensT_uint_mid", ``SourceArg "a" (SOME (SCA_Name ["address"]))``),
   ("neg_lit", ``SX_Literal (SCL_Int (-5))``),
   ("pow_neglit_base", ``SX_Literal (SCL_Int (-2))``),
   ("lt_mixed_lit", ``SX_Compare SCC_Lt (SX_Name "a") (SX_Literal (SCL_Int 5))``),
   ("boolop_and3", ``SX_Boolean SCB_Or [SX_Boolean SCB_And [SX_Name "a";SX_Name "b"];SX_Name "c"]``),
   ("i12_immut_with_storage", ``SCA_Qualified SCQ_Immutable (SCA_Name ["uint256"])``),
   ("p29_imm_multi", ``SX_Attribute (SX_Name "msg") "sender"``),
   ("c16_const_string_in_expr", ``SCA_Qualified SCQ_Constant (SCA_String (SCE_Literal (SCL_Int 5)))``),
   ("c27_const_binop_fold", ``SX_Binary SCB_Mul (SX_Name "A") (SX_Literal (SCL_Int 7))``),
   ("rc09_abi_encode_data", ``SX_Call (SX_Name "raw_call") [SX_Name "t";
     SX_Call (SX_Name "abi_encode") [SX_Name "x"] [("method_id",
       SX_Call (SX_Name "method_id") [SX_Literal (SCL_String "f(uint256)")] [])]] []``),
   ("rr03_abi", ``SX_Call (SX_Name "raw_revert") [
     SX_Call (SX_Name "abi_encode") [SX_Name "x"] [("method_id",
       SX_Call (SX_Name "method_id") [SX_Literal (SCL_String "E(uint256)")] [])]] []``)];
val manifest = TextIO.openIn "../lowering/defs/bytecode/folded-value-witnesses.txt";
val names = String.tokens Char.isSpace (TextIO.inputAll manifest);
val () = TextIO.closeIn manifest;
val () = if length names = 37 andalso length (Lib.mk_set names) = 37 andalso
  names = List.map #1 expected_domains then () else raise Fail "37 source domains/manifest diverged";
fun fixture n = "../tests/fixtures/check_contract/source_syntax/" ^ n ^ ".json";
val () = app (fn (n,domain) => let
    val json = JSONDecode.decodeFile JSONDecode.raw (fixture n)
    val {syntax,provenance,...} = dap json
  in independent n sourceSyntaxLib.annotated_ast json;
     require_subterm n domain syntax;
     app (fn replacement => let val changed = dap (fold_only replacement json) in
       if aconv syntax (#syntax changed) andalso provenance = #provenance changed
       then () else raise Fail (n ^ " folded metadata changed provenance or syntax") end)
       [NONE,SOME (integer 7),SOME (integer 42)];
     if null provenance then raise Fail (n ^ " lost provenance") else ()
  end) expected_domains;
(* Ordinary annotated JSON also decodes without folding/type trust. Its erased
   declaration qualifiers cannot be recovered: never invent them from flags. *)
val () = app (fn n => if n = "method_id_var" then () else
  independent (n ^ " ordinary JSON syntax") sourceSyntaxLib.annotated_ast
    (JSONDecode.decodeFile JSONDecode.raw
      ("../lowering/defs/bytecode/folded-value-oracle/" ^ n ^ ".json"))) names;

Theorem source_candidates_keep_unresolved_calls = checked "unresolved callee"
  ``source_constant_candidate (SX_Call (SX_Name "method_id") [SX_Name "s"]
     [("output_type",SX_Name "bytes4")])``
  ``SCE_Call (SCE_Name ["method_id"]) [SCE_Name ["s"]]
     [("output_type",SCE_Name ["bytes4"]) ]``;

(* ===== General expressions are not limited by the constant evaluator ===== *)
val receiver = call (name "factory") [name "x"] [kw "gas" (name "g")];
val general_attribute = ast "Attribute" [("value",receiver),("attr",str "member")];
val conditional = ast "IfExp" [("test",name "c"),("body",general_attribute),("orelse",integer 0)];
val () = ignore (checked "non-path attribute receiver" (de general_attribute)
  ``SX_Attribute (SX_Call (SX_Name "factory") [SX_Name "x"] [("gas",SX_Name "g")]) "member"``);
val () = app (fn (json,expected) =>
  (ignore (checked "general source syntax" (de json) expected);
   independent "general source expression" sourceSyntaxLib.expression json))
  [(conditional,``SX_IfExp (SX_Name "c") ^(de general_attribute) (SX_Literal (SCL_Int 0))``),
   (ast "ExtCall" [("value",receiver)],``SX_ExtCall ^(de receiver)``),
   (ast "StaticCall" [("value",receiver)],``SX_StaticCall ^(de receiver)``),
   (ast "NamedExpr" [("target",name "dep"),("value",name "other")],
     ``SX_NamedExpr (SX_Name "dep") (SX_Name "other")``),
   (ast "Dict" [("keys",arr [name "field"]),("values",arr [conditional])],
     ``SX_Dict [(SX_Name "field",^(de conditional))]``),
   (ast "Ellipsis" [],``SX_Ellipsis``)];
Theorem source_general_attribute_not_a_constant_path = checked "attribute unsupported candidate"
  ``source_constant_candidate ^(de general_attribute)``
  ``SCE_Unsupported "attribute" [SCE_Call (SCE_Name ["factory"]) [SCE_Name ["x"]]
    [("gas",SCE_Name ["g"])]]``;

(* ===== Original bounds and qualifiers in every declaration position ===== *)
val source_bound = bin "Add" (bin "RShift" (bin "LShift" (integer 1) (integer 256))
  (integer 255)) (integer 1);
val nested_annotation = qualify "public" (subscript (name "HashMap")
  (tuple [name "address",subscript (name "DynArray") (tuple
    [subscript (name "Bytes") (bin "Add" (name "N") (integer 1)),name "M"])]));
val typed_target = ast "AnnAssign" [("target",name "i"),("annotation",name "uint256"),("value",JSON.NULL)];
val iter = call (name "range") [call (name "start") [] [],name "end"]
  [kw "bound" source_bound];
val loop = ast "For" [("target",typed_target),("iter",iter),("body",arr [ast "Pass" []])];
Theorem source_range_retains_runtime_operands_and_bound = checked "range source call" (ds loop)
  ``SS_For "i" (SCA_Name ["uint256"])
    (SX_Call (SX_Name "range") [SX_Call (SX_Name "start") [] [];SX_Name "end"]
      [("bound",SX_Binary SCB_Add (SX_Binary SCB_RShift
        (SX_Binary SCB_LShift (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 256)))
        (SX_Literal (SCL_Int 255))) (SX_Literal (SCL_Int 1)))]) [SS_Pass]``;
val struct_decl = ast "StructDef" [("name",str "S"),
  ("body",arr [arg "items" (subscript (name "uint256") source_bound)])];
val event_decl = ast "EventDef" [("name",str "E"),
  ("body",arr [arg "items" (qualify "indexed" (subscript (name "Bytes") (name "N")))])];
val interface_decl = ast "InterfaceDef" [("name",str "I"),("body",arr
  [func "f" [arg "x" (subscript (name "String") (name "N"))] []
     (subscript (name "Bytes") (name "M")) [ast "Expr" [("value",name "view")]]])];
val declaration_program = program_json
  [variable "values" nested_annotation JSON.NULL,struct_decl,event_decl,interface_decl,
   variable "N" (qualify "constant" (name "uint256")) (integer 3),
   variable "X" (qualify "immutable" (name "uint256")) JSON.NULL,
   func "body" [arg "xs" (subscript (name "uint256") source_bound)]
     [bin "Add" (integer 1) (integer 2)] (subscript (name "Bytes") (name "N"))
     [ast "AnnAssign" [("target",name "local"),("annotation",subscript (name "String") (name "N")),
       ("value",ast "Str" [("value",str "abc")])],loop]] [];
val () = independent "all annotation consumers" sourceSyntaxLib.annotated_ast declaration_program;
val () = require_subterm "nested HashMap source" ``SCA_Qualified SCQ_Public
    (SCA_HashMap (SCA_Name ["address"]) (SCA_DynArray
      (SCA_Bytes (SCE_Binary SCB_Add (SCE_Name ["N"]) (SCE_Literal (SCL_Int 1)))) (SCE_Name ["M"])))``
  (dp declaration_program);
val () = ignore (checked "flags cannot invent qualifiers"
  (dd (poisoned (integer 7) (variable "plain" (name "uint256") JSON.NULL)))
  ``SD_Variable "plain" (SCA_Name ["uint256"]) NONE``);
val () = require_subterm "event indexed qualifier" ``SCA_Qualified SCQ_Indexed (SCA_Bytes (SCE_Name ["N"]))``
  (dp declaration_program);

(* ===== Structural imports/initializes/exports and default-override originals ===== *)
val import_decl = ast "Import" [("names",arr [ast "alias" [("name",str "package.lib"),("asname",str "lib")]]),
  ("import_infos",arr [obj [("alias",str "lib"),("source_id",JSON.INT 1),
    ("qualified_module_name",str "package.lib"),("resolved_path",str "package/lib.vy")]])];
val from_decl = ast "ImportFrom" [("module",str "package"),("level",JSON.INT 2),
  ("names",arr [ast "alias" [("name",str "lib"),("asname",JSON.NULL)]])];
val binding = subscript (name "lib") (ast "NamedExpr" [("target",name "dep"),("value",name "actual")]);
val original_default = bin "Add" (integer 1) (integer 2);
val original_program = program_json [import_decl,from_decl,
  ast "InitializesDecl" [("annotation",binding)],
  ast "ExportsDecl" [("annotation",ast "Attribute" [("value",name "lib"),("attr",str "f")])],
  ast "UsesDecl" [("annotation",name "lib")],
  func "f" [arg "x" (name "uint256")] [original_default] (name "uint256") [ret (name "x")]]
  [module_json [variable "N" (qualify "constant" (name "uint256")) original_default]];
val () = independent "source import/default structural view" sourceSyntaxLib.annotated_ast original_program;
val () = ignore (checked "source import syntax" (dd import_decl)
  ``SD_Import [SI_Import "package.lib" (SOME "lib")]``);
val () = ignore (checked "relative source import syntax" (dd from_decl)
  ``SD_Import [SI_FromImport "package" 2 "lib" NONE]``);
val original_term = dp original_program;
Theorem retained_source_default_override_is_structural = checked "original defaults are not value equality"
  ``source_default_syntax (SourceModule [SD_Function "f" [] [] [^(de original_default)] NONE []]) <>
    source_default_syntax (SourceModule [SD_Function "f" [] [] [SX_Literal (SCL_Int 3)] NONE []])`` ``T``;
Theorem retained_source_survives_executable_rewrite = checked "source retention"
  ``retained_source (replace_source_executable [SX_Literal (SCL_Int 3)]
       (SourceRetained ^original_term [^(de original_default)]))`` original_term;

(* Real existing imported/default/range fixtures, still without translator. *)
val () = app (fn path => let val json = JSONDecode.decodeFile JSONDecode.raw path in
    independent path sourceSyntaxLib.annotated_ast json;
    ignore (dap json)
  end) ["../tests/fixtures/check_contract/imported_deploy/main.json",
        "../tests/fixtures/check_contract/defaults_control/main.json"];

(* ===== Provenance is separate, keyed by structural position ===== *)
val traced = obj [("ast",ast "Module" [("body",arr []),("source_id",JSON.INT 5),
  ("node_id",JSON.INT 0),("src",str "0:12:5"),("lineno",JSON.INT 1),
  ("col_offset",JSON.INT 0),("end_lineno",JSON.INT 2),("end_col_offset",JSON.INT 0),
  ("path",str "main.vy"),("resolved_path",str "pkg/main.vy")]),("imports",arr [])];
val () = case #provenance (dap traced) of
    [{json_path=["ast"],source_id=SOME 5,node_id=SOME 0,src=SOME "0:12:5",
      lineno=SOME 1,col_offset=SOME 0,end_lineno=SOME 2,end_col_offset=SOME 0,
      path=SOME "main.vy",resolved_path=SOME "pkg/main.vy",...}] => ()
  | _ => raise Fail "provenance lost or confused with semantic identity";
val () = case #import_claims (dap original_program) of
    [{alias="lib",source_id=1,qualified_module_name="package.lib",resolved_path="package/lib.vy",...}] => ()
  | _ => raise Fail "import mapping claims not retained separately";

(* ===== Malformed PRESENT annotations fail at every consumer ===== *)
val bad_annotation = subscript (name "Bytes") (ast "Int" [("value",str "4")]);
val bad_present_programs =
  [program_json [variable "bad" bad_annotation JSON.NULL] [],
   program_json [func "f" [arg "bad" bad_annotation] [] JSON.NULL []] [],
   program_json [func "f" [] [] bad_annotation []] [],
   program_json [func "f" [] [] JSON.NULL [ast "AnnAssign"
     [("target",name "x"),("annotation",bad_annotation),("value",integer 0)]]] [],
   program_json [ast "StructDef" [("name",str "S"),("body",arr [arg "x" bad_annotation])]] [],
   program_json [ast "EventDef" [("name",str "E"),("body",arr [arg "x" (qualify "indexed" bad_annotation)])]] [],
   program_json [ast "InterfaceDef" [("name",str "I"),("body",arr
     [func "f" [] [] bad_annotation [ast "Pass" []]])]] [],
   program_json [variable "bad" (subscript (name "HashMap") (tuple [name "address",bad_annotation])) JSON.NULL] [],
   program_json [func "f" [] [] JSON.NULL [ast "For" [("target",ast "AnnAssign"
     [("target",name "i"),("annotation",bad_annotation)]),("iter",iter),("body",arr [])]]] []];
val () = app (fn json => app (rejects "annotation consumer" sourceSyntaxLib.annotated_ast)
  (variants json)) bad_present_programs;
val () = app (fn json => app (rejects "bad original + usable fold" sourceSyntaxLib.expression)
  (variants json))
  [ast "UnsupportedNode" [],ast "IfExp" [("test",name "c"),("body",integer 0)],
   ast "Attribute" [("value",receiver),("attr",JSON.INT 1)],
   ast "Dict" [("keys",arr [name "x"]),("values",arr [])],
   call (name "len") [] [kw "x" JSON.NULL],ast "Int" [("value",JSON.INT 1),("value",JSON.INT 2)]];
val () = app (rejects "missing required source annotation" sourceSyntaxLib.declaration)
  [ast "VariableDecl" [("target",name "x"),("value",integer 0)],
   variable "x" JSON.NULL (integer 0)];

(* New theories contain no oracle-backed theorem certificates. ML decoder tests
   complement these theorems; they do not prove JSON parsing correctness. *)
val () = app (fn theory => app (fn (n,th) =>
  if null (List.filter (fn oracle => oracle <> "DISK_THM")
    (#1 (Tag.dest_tag (Thm.tag th)))) then () else raise Fail (theory ^ "." ^ n ^ " has an oracle"))
  (DB.thms theory)) ["sourceSyntax","sourceSyntaxLibTest"];
