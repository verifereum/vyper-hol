Theory sourceOrdinaryClaimsTest
Ancestors
  sourceOrdinaryClaims sourceSyntax sourceConstAnnotation jsonAST
Libs
  sourceOrdinaryClaimsLib

fun obj fs = JSON.OBJECT fs;
fun str s = JSON.STRING s;
fun arr xs = JSON.ARRAY xs;
fun ast k fs = obj (("ast_type",str k)::fs);
fun name n = ast "Name" [("id",str n)];
fun integer n = ast "Int" [("value",JSON.INT n)];
fun kw n v = ast "keyword" [("arg",str n),("value",v)];
fun call f args kws = ast "Call" [("func",f),("args",arr args),("keywords",arr kws)];
fun put key v (JSON.OBJECT fs) = obj ((key,v)::List.filter (fn (k,_) => k <> key) fs)
  | put _ _ _ = raise Fail "test object";
fun bytes n = obj [("name",str "Bytes"),("length",JSON.INT n),("typeclass",str "bytes")];
val uint = obj [("name",str "uint256"),("typeclass",str "integer"),
  ("bits",JSON.INT 256),("is_signed",JSON.BOOL false)];
fun typed ty json = put "type" ty json;
fun checked label proposition = let val th = EVAL proposition in
  if aconv (rhs (concl th)) boolSyntax.T then EQT_ELIM th else raise Fail label end;
fun rejects label f = if (f (); false) handle JSONDecode.JSONError _ => true
  then () else raise Fail ("accepted " ^ label);
fun contains expected tm = aconv expected tm orelse
  (is_comb tm andalso (contains expected (rator tm) orelse contains expected (rand tm)));
val folded = prim_mk_const {Thy="jsonAST",Name="JE_Folded"};
fun no_folds tm = if contains folded tm then raise Fail "claim retained a folded branch" else ();
fun fold_everywhere value (JSON.OBJECT fs) = obj (("folded_value",value)::("folded_literal",value)::
      List.map (fn (k,v) => (k,fold_everywhere value v))
        (List.filter (fn (k,_) => k <> "folded_value" andalso k <> "folded_literal") fs))
  | fold_everywhere value (JSON.ARRAY xs) = arr (List.map (fold_everywhere value) xs)
  | fold_everywhere _ json = json;
val pair = sourceOrdinaryClaimsLib.pair_expression;
val concat_source = call (name "concat") [name "a",name "b"] [];
val concat_annotated = typed (bytes 8)
  (call (name "concat") [typed (bytes 4) (name "a"),typed (bytes 4) (name "b")] []);
val concat_pair = pair concat_source concat_annotated;
val concat_claims = #claims concat_pair;
Theorem dynamic_concat_source_projection = #projection concat_pair;
Theorem dynamic_concat_mirror_shape = #shape concat_pair;
Theorem dynamic_concat_inherited_claim = checked "concat claim"
  ``source_claims_legacy ^concat_claims = JE_Call
    (JE_Name "concat" NONE JMissingSource JT_None)
    [JE_Name "a" (SOME "bytes") JMissingSource (JT_Bytes 4);
     JE_Name "b" (SOME "bytes") JMissingSource (JT_Bytes 4)] [] (JT_Bytes 8) JMissingSource``;
val () = app (fn poison => let
  val changed = #claims (pair (fold_everywhere poison concat_source)
    (fold_everywhere poison concat_annotated))
  in if aconv concat_claims changed then no_folds changed
     else raise Fail "fold metadata changed paired concat" end)
  [integer 999,JSON.NULL,str "malformed folded AST",ast "Unsupported" []];
val () = if aconv concat_claims (#claims (pair concat_source
    (typed (bytes 9) concat_annotated))) then raise Fail "lost inherited concat result type" else ();

(* The pin's Bytes[INF] is metadata for the original msg.data syntax only.
   Keep the legacy optional-type result (JT_None), not a fabricated bound. *)
val calldata_source = ast "Attribute" [("value",name "msg"),("attr",str "data")];
val calldata_type = put "length" (str "INF") (bytes 0);
val calldata_annotated = typed calldata_type
  (put "value" (typed (obj [("name",str "msg")]) (name "msg")) calldata_source);
val calldata_pair = pair calldata_source calldata_annotated;
val calldata_claims = #claims calldata_pair;
Theorem calldata_inf_source_projection = #projection calldata_pair;
Theorem calldata_inf_mirror_shape = #shape calldata_pair;
Theorem calldata_inf_keeps_legacy_dispatch = checked "calldata legacy claim"
  ``source_claims_legacy ^calldata_claims = JE_Attribute
    (JE_Name "msg" NONE JMissingSource (JT_Named NONE "msg")) "data"
    (SOME "bytes") (SOME "msg") NONE JMissingSource JT_None``;
val () = app (fn poison => let
  val changed = #claims (pair (fold_everywhere poison calldata_source)
    (fold_everywhere poison calldata_annotated))
  in if aconv calldata_claims changed then no_folds changed
     else raise Fail "calldata INF depends on folds" end)
  [integer 999,JSON.NULL,str "not an AST",ast "Unsupported" []];
val () = if aconv calldata_claims (#claims (pair calldata_source
    (typed (bytes 4) calldata_annotated))) then raise Fail "invented calldata bound" else ();
val () = app (fn ty => rejects "malformed calldata type" (fn () => ignore
    (pair calldata_source (typed ty calldata_annotated))))
  [str "INF",put "length" (str "inf") calldata_type,
   put "length" (str "INF ") calldata_type,put "length" JSON.NULL calldata_type,
   put "length" (JSON.BOOL true) calldata_type,
   obj [("name",str "Bytes"),("typeclass",str "bytes")],
   obj [("name",str "Bytes"),("length",str "INF")],
   put "typeclass" (str "integer") calldata_type,
   put "name" (str "String") calldata_type,
   obj [("name",str "Bytes"),("typeclass",str "bytes"),
     ("length",str "INF"),("length",str "INF")]];
val other_data = ast "Attribute" [("value",name "other"),("attr",str "data")];
val other_attr = put "attr" (str "sender") calldata_source;
val () = app (fn source => rejects "INF on a bounded expression" (fn () => ignore
    (pair source (typed calldata_type source))))
  [name "x",integer 1,other_data,other_attr,concat_source];
val () = rejects "folded msg.data cannot authorize INF" (fn () => ignore
  (pair other_data (put "folded_value" calldata_annotated (typed calldata_type other_data))));
val () = rejects "replacement with msg.data cannot authorize INF" (fn () => ignore
  (pair other_data calldata_annotated));
val () = app (fn ty => rejects "nested INF is not a bounded type" (fn () => ignore
    (pair calldata_source (typed ty calldata_annotated))))
  [obj [("typeclass",str "tuple"),("member_types",arr [calldata_type])],
   obj [("typeclass",str "static_array"),("value_type",calldata_type),("length",JSON.INT 1)],
   obj [("name",str "DynArray"),("value_type",calldata_type),("length",JSON.INT 1)],
   obj [("name",str "function"),("argument_types",arr [calldata_type])],
   obj [("name",str "function"),("return_type",calldata_type)],
   put "type_t" calldata_type calldata_type];

(* Equal source syntax at different occurrences must NOT alias legacy claims. *)
val duplicate_source = ast "Tuple" [("elements",arr [name "x",name "x"])];
val duplicate_annotated = ast "Tuple" [("elements",arr
  [typed uint (name "x"),typed (bytes 4) (name "x")])];
val duplicates = #claims (pair duplicate_source duplicate_annotated);
Theorem occurrence_claims_are_not_expression_keys = checked "distinct occurrence claims"
  ``OPTION_MAP source_claims_legacy (source_claims_at [0] ^duplicates) <>
    OPTION_MAP source_claims_legacy (source_claims_at [1] ^duplicates)``;

(* Named and qualified calls preserve method_id syntax and keyword order. *)
val signature_json = ast "Str" [("value",str "foo()")];
val selector = call (name "method_id") [signature_json] [kw "output_type" (name "bytes4")];
val selector_ann = call (name "method_id")
  [typed (obj [("generic",str "string")]) signature_json] [kw "output_type" (name "bytes4")];
val method_claims = #claims (pair selector selector_ann);
Theorem method_id_designator_is_original = checked "method designator"
  ``OPTION_MAP source_claims_source (source_claims_at [0] ^method_claims) = SOME (SX_Name "method_id")``;
val attribute = ast "Attribute" [("value",name "lib"),("attr",str "f")];
val () = no_folds (#claims (pair (call attribute [name "a"] []) (call attribute [typed uint (name "a")] [])));
val kws = [kw "ensure_tuple" (ast "NameConstant" [("value",JSON.BOOL false)]),kw "method_id" selector];
val annkws = [hd kws,kw "method_id" selector_ann];
val abi = call (name "abi_encode") [name "x"] kws;
val abi_ann = call (name "abi_encode") [typed uint (name "x")] annkws;
val () = no_folds (#claims (pair abi abi_ann));
val () = app (fn (label,original,bad) => rejects label (fn () => ignore (pair original bad)))
  [("callee replacement",concat_source,put "func" (name "keccak256") concat_annotated),
   ("argument order",concat_source,put "args" (arr [name "b",name "a"]) concat_annotated),
   ("keyword order",abi,put "keywords" (arr (rev annkws)) abi_ann),
   ("keyword spelling",selector,put "keywords" (arr [kw "other" (name "bytes4")]) selector_ann),
   ("literal replacement",integer 1,integer 2),
   ("constructor replacement",name "x",integer 1),
   ("missing child",concat_source,put "args" (arr [name "a"]) concat_annotated),
   ("malformed present child",concat_source,put "args" JSON.NULL concat_annotated),
   ("malformed present type",name "x",typed (str "bad") (name "x")),
   ("malformed integer type",name "x",typed (obj [("name",str "uint256"),
       ("typeclass",str "integer")]) (name "x"))];
val bin = ast "BinOp" [("left",integer 1),("op",ast "Add" []),("right",integer 2)];
val () = rejects "operator mismatch hidden by fold" (fn () => ignore (pair bin
  (put "folded_value" (integer 3) (put "op" (ast "Mult" []) bin))));
val () = rejects "duplicate syntax field" (fn () => ignore (pair (name "x")
  (ast "Name" [("id",str "x"),("id",str "x")])));
val () = rejects "qualifier erasure in executable syntax" (fn () => ignore
  (pair (call (name "constant") [name "uint256"] []) (name "uint256")));
val () = rejects "hex spelling replacement" (fn () => ignore
  (pair (ast "Hex" [("value",str "0xaB")]) (ast "Hex" [("value",str "0xab")])));

(* Only matched Decimal literals admit exact numeric spelling equivalence.
   Scientific originals and their precision survive both source and legacy
   projections; even plausible folded claims cannot authorize replacement. *)
fun decimal token = ast "Decimal" [("value",str token)];
val decimal_source = decimal "1.25e-2";
val decimal_annotated = decimal "0.0125";
val decimal_pair = pair decimal_source decimal_annotated;
val decimal_claims = #claims decimal_pair;
Theorem scientific_decimal_source_projection = #projection decimal_pair;
Theorem scientific_decimal_source_match = #source_match decimal_pair;
Theorem scientific_decimal_mirror_shape = #shape decimal_pair;
Theorem scientific_decimal_retains_original_token = checked "original Decimal token"
  ``source_claims_legacy ^decimal_claims = JE_Decimal "1.25e-2"``;
Theorem scientific_decimal_retains_original_precision = checked "original Decimal precision"
  ``source_claims_source ^decimal_claims =
    SX_Literal (SCL_Decimal 125 (2 + 2))``;
val () = app (fn (original,annotated) => let
  val () = print ("DECIMAL_EQ " ^ original ^ " = " ^ annotated ^ "\n")
  val source = decimal original
  val expected = #claims (pair source source)
  val actual = #claims (pair source (decimal annotated))
  in if aconv expected actual then no_folds actual
     else raise Fail "Decimal canonicalization changed original token/precision" end)
  [("1.25e-2","0.0125"),("2e-10","0.0000000002"),
   ("1.25E+2","125.0"),("1_2.50e-1","1.25"),
   ("-1.25e-2","-0.0125"),("0.012500","1.25e-2")];
val () = app (fn poison => if aconv decimal_claims (#claims
  (pair (fold_everywhere poison decimal_source)
    (fold_everywhere poison decimal_annotated))) then ()
  else raise Fail "Decimal equivalence depends on folds")
  [integer 999,decimal "0.0126",str "bad",JSON.NULL];
val () = app (fn (original,annotated) => rejects "non-equivalent or invalid Decimal"
    (fn () => ignore (pair (decimal original) (decimal annotated))))
  [("1.25e-2","0.0126"),("1.25e-2","-0.0125"),
   ("1.25e-2","0.01250000001"),("1.25e-2","0.01250000000"),
   ("1.250000000e-2","0.0125"),("0e-11","0.0"),
   ("0.0125","0e-11"),("1e-11","0.0"),
   ("1.25e-2","0.0125junk"),("1.25e-2","0.01__25"),
   ("1.25e-2","min(0.0125, 1.0)"),("1.25e-","0.0125"),
   ("1.25e-2e0","0.0125")];
val () = rejects "bad Decimal spelling rescued by source-valued fold" (fn () => ignore
  (pair decimal_source (put "folded_value" decimal_source (decimal "0.0126"))));
val () = rejects "Decimal value is not a token" (fn () => ignore
  (pair decimal_source (put "value" (JSON.INT 125) decimal_annotated)));
val () = rejects "numeric equivalence cannot change a string literal" (fn () => ignore
  (pair (ast "Str" [("value",str "1.25e-2")])
    (ast "Str" [("value",str "0.0125")])));
val () = rejects "numeric equivalence cannot change a constructor" (fn () => ignore
  (pair decimal_source (integer 125)));

(* External wrapper dispatch retains its signature AND all source children. *)
val external_callee = ast "Attribute" [("value",name "contract"),("attr",str "f")];
val external_source = ast "ExtCall" [("value",call external_callee [name "x"] [])];
val external_signature = obj [("typeclass",str "contract_function"),("name",str "f"),
  ("argument_types",arr [uint]),("return_type",uint)];
val external_annotated = typed uint (ast "ExtCall" [("value",typed uint
  (call (typed external_signature external_callee) [typed uint (name "x")] []))]);
val external_pair = pair external_source external_annotated;
Theorem external_claims_keep_wrapper_source = #projection external_pair;
val () = no_folds (#claims external_pair);

(* Program pairing retains the exact loader record and pre-erasure qualifiers. *)
fun qualify q ann = call (name q) [ann] [];
fun variable ann value = ast "VariableDecl" [("node_id",JSON.INT 1),
  ("target",name "N"),("annotation",ann),("value",value)];
fun module_json body = ast "Module" [("body",arr body)];
fun program body = obj [("ast",module_json body),("imports",arr [])];
fun loaded json : sourceModuleLoaderLib.loaded =
  {program=JSONDecode.decode sourceSyntaxLib.annotated_ast json,
   keys=``[["main"]]``,nonreentrant_defaults=``[T]``,declaration_only=``[F]``,
   provenance=obj [("source_sha256sum",str "original hash"),("phase",str "pre-erasure")]};
val original_program = program [variable (qualify "public" (qualify "constant" (name "uint256"))) bin];
val annotated_program = program [put "is_immutable" (JSON.BOOL true) (variable (name "uint256") bin)];
val loader = loaded original_program;
val program_pair = sourceOrdinaryClaimsLib.pair_program loader original_program annotated_program;
val program_claims = #claims program_pair;
Theorem erased_qualifiers_keep_original_projection = #projection program_pair;
Theorem paired_program_source_match = #source_match program_pair;
Theorem paired_program_mirror_shape = #shape program_pair;
Theorem paired_program_retains_source = checked "retained program"
  ``retained_source ^(#retained program_pair) = ^(#program loader)``;
val () = if aconv (#keys (#original program_pair)) (#keys loader) andalso
  aconv (#nonreentrant_defaults (#original program_pair)) (#nonreentrant_defaults loader) andalso
  aconv (#declaration_only (#original program_pair)) (#declaration_only loader) then ()
  else raise Fail "changed loader policy";
val () = app (fn poison => if aconv program_claims (#claims
  (sourceOrdinaryClaimsLib.pair_program loader original_program
    (fold_everywhere poison annotated_program))) then () else raise Fail "program fold dependence")
  [integer 0,str "bad"];
val () = app (fn (label,bad) => rejects label (fn () => ignore
  (sourceOrdinaryClaimsLib.pair_program loader original_program bad)))
  [("declaration identity",program [put "node_id" (JSON.INT 99) (variable (name "uint256") bin)]),
   ("declaration name",program [put "target" (name "M") (variable (name "uint256") bin)]),
   ("declaration type",program [variable (name "uint8") bin]),
   ("declaration body",program [variable (name "uint256") (integer 3)]),
   ("invented qualifier",program [variable (qualify "immutable" (name "uint256")) bin])];
val () = rejects "loader/original mismatch" (fn () => ignore
  (sourceOrdinaryClaimsLib.pair_program loader (program []) annotated_program));
(* Program zipper uses the same Decimal-only rule and restores the original
   before decoding its source projection, including nested executable nodes. *)
val decimal_program = program [variable (qualify "constant" (name "decimal"))
  (call (name "min") [decimal_source,decimal "2e-10"] [])];
val decimal_program_ann = program [variable (name "decimal")
  (call (name "min") [decimal_annotated,decimal "0.0000000002"] [])];
val decimal_program_pair = sourceOrdinaryClaimsLib.pair_program
  (loaded decimal_program) decimal_program decimal_program_ann;
Theorem scientific_program_source_match = #source_match decimal_program_pair;
Theorem scientific_program_source_projection = #projection decimal_program_pair;
Theorem scientific_program_mirror_shape = #shape decimal_program_pair;
val () = rejects "program Decimal mismatch" (fn () => ignore
  (sourceOrdinaryClaimsLib.pair_program (loaded decimal_program) decimal_program
    (program [variable (name "decimal")
      (call (name "min") [decimal "0.0126",decimal "0.0000000002"] [])])));
fun function_json n defaults = ast "FunctionDef" [("name",str n),("decorator_list",arr []),
  ("args",ast "arguments" [("args",arr []),("defaults",arr defaults)]),
  ("returns",JSON.NULL),("body",arr [ast "Return" [("value",bin)]])];
val declarations = [function_json "f" [bin],function_json "g" []];
val declaration_program = program declarations;
val () = ignore (sourceOrdinaryClaimsLib.pair_program (loaded declaration_program)
  declaration_program declaration_program);
val () = app (fn (label,bad) => rejects label (fn () => ignore
  (sourceOrdinaryClaimsLib.pair_program (loaded declaration_program) declaration_program bad)))
  [("declaration order",program (rev declarations)),
   ("normalized default instead of original",program [function_json "f" [integer 3],hd (tl declarations)])];
fun import_json n = ast "Import" [("names",arr [ast "alias"
  [("name",str n),("asname",str "lib")]])];
val import_program = program [import_json "package.lib"];
val () = rejects "import spelling replacement" (fn () => ignore
  (sourceOrdinaryClaimsLib.pair_program (loaded import_program) import_program
    (program [import_json "package.other"])));

(* Real #543 syntax/legacy pairs: no evaluator, body-typing or #135 gate. *)
fun holbuild_extra_deps (_ : string list) = ();
val () = holbuild_extra_deps ["../lowering/defs/bytecode/folded-value-witnesses.txt",
  "../tests/fixtures/check_contract/source_syntax","../lowering/defs/bytecode/folded-value-oracle",
  "../tests/fixtures/check_contract/source_ordinary/calldata_slice.json",
  "../tests/fixtures/check_contract/source_ordinary/raw_call_calldata.json",
  "../tests/fixtures/check_contract/calldata_slice.json",
  "../tests/fixtures/check_contract/raw_call_calldata.json"];
val manifest = TextIO.openIn "../lowering/defs/bytecode/folded-value-witnesses.txt";
val names = String.tokens Char.isSpace (TextIO.inputAll manifest);
val () = TextIO.closeIn manifest;
val () = app (fn n => if n = "method_id_var" then () else let
  val source = JSONDecode.decodeFile JSONDecode.raw
    ("../tests/fixtures/check_contract/source_syntax/" ^ n ^ ".json")
  val annotated = JSONDecode.decodeFile JSONDecode.raw
    ("../lowering/defs/bytecode/folded-value-oracle/" ^ n ^ ".json")
  val original = loaded source
  val paired = sourceOrdinaryClaimsLib.pair_program original source annotated
  val () = no_folds (#claims paired)
  val () = app (fn poison => if aconv (#claims paired) (#claims
    (sourceOrdinaryClaimsLib.pair_program original source (fold_everywhere poison annotated)))
    then () else raise Fail (n ^ " folded metadata changed claims")) [integer 314159,str "bad"]
  in () end) names;
(* Exercise the original pinned calldata regressions, including fold deletion
   and poisoning, independently of the module/check integration harness. *)
val () = app (fn n => let
  val source = JSONDecode.decodeFile (JSONDecode.field "annotated_ast" JSONDecode.raw)
    ("../tests/fixtures/check_contract/source_ordinary/" ^ n ^ ".json")
  val annotated = JSONDecode.decodeFile JSONDecode.raw
    ("../tests/fixtures/check_contract/" ^ n ^ ".json")
  val original = loaded source
  fun claims annotated = #claims (sourceOrdinaryClaimsLib.pair_program original source annotated)
  val expected = claims annotated
  val () = no_folds expected
  val () = app (fn changed => if aconv expected (claims changed) then ()
    else raise Fail (n ^ " calldata claims depend on folds"))
    [sourceOrdinaryClaimsLib.without_folds annotated,
     fold_everywhere (str "not an AST") annotated]
  in () end) ["calldata_slice","raw_call_calldata"];
val () = app (fn theory => app (fn (n,th) =>
  if null (List.filter (fn oracle => oracle <> "DISK_THM")
    (#1 (Tag.dest_tag (Thm.tag th)))) then () else raise Fail (theory ^ "." ^ n ^ " has an oracle"))
  (DB.thms theory)) ["sourceOrdinaryClaims","sourceOrdinaryClaimsTest"];
