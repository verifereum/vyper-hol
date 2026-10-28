structure sourceSyntaxLib :> sourceSyntaxLib = struct

open HolKernel boolLib JSONDecode sourceSyntaxTheory

(* ===== Fail-closed shared source decoding ===== *)
fun error message = fail ("source syntax frontend: " ^ message)
val optional = sourceConstASTLib.optional_field
fun required key d = andThen (optional key d) (fn
    SOME value => succeed value | NONE => error ("missing field " ^ key))
fun optional_nullable key d = JSONDecode.map (fn NONE => NONE | SOME x => x)
  (optional key (nullable d))
fun node kind d = andThen (required "ast_type" string) (fn actual =>
  if actual = kind then d else error ("expected " ^ kind))
fun dispatch f = andThen (required "ast_type" string) f
fun construct name args = list_mk_comb
  (prim_mk_const {Thy="sourceSyntax",Name=name},args)
fun ty name = mk_thy_type {Thy="sourceSyntax",Tyop=name,Args=[]}
val expr_ty = ty "source_expr"
val stmt_ty = ty "source_stmt"
val decl_ty = ty "source_decl"
val arg_ty = ty "source_arg"
val module_ty = ty "source_module"
val import_ty = ty "source_import"
val ann_ty = mk_thy_type
  {Thy="sourceConstAnnotation",Tyop="source_const_annotation",Args=[]}
val keyword_ty = pairSyntax.mk_prod (stringSyntax.string_ty,expr_ty)
val entry_ty = pairSyntax.mk_prod (expr_ty,expr_ty)
fun terms ty xs = listSyntax.mk_list (xs,ty)
fun text s = stringSyntax.fromMLstring s
fun option ty NONE = optionSyntax.mk_none ty
  | option _ (SOME x) = optionSyntax.mk_some x
val identifier = andThen string (fn s =>
  if size s > 0 andalso
     (Char.isAlpha (String.sub (s,0)) orelse String.sub (s,0) = #"_") andalso
     List.all (fn c => Char.isAlphaNum c orelse c = #"_") (String.explode s)
  then succeed s else error "invalid identifier")
val target_name = node "Name" (required "id" identifier)
val annotation = sourceConstASTLib.annotation
fun annotation_option key = JSONDecode.map (option ann_ty)
  (sourceConstASTLib.annotation_field key)
fun expr_option key child = JSONDecode.map (option expr_ty)
  (optional_nullable key child)

(* ===== General source expressions ===== *)
(* Literal token validation and operator parsing are shared with the constant
   syntax decoder. Only a literal constructor is destructed here, never EVAL. *)
fun literal_decoder () = JSONDecode.map (fn e =>
  case strip_comb e of (_, [lit]) => construct "SX_Literal" [lit]
    | _ => raise Fail "source literal decoder invariant") sourceConstASTLib.expression
fun expression_decoder () : term decoder = let
  val child = delay expression_decoder
  fun unary name key = JSONDecode.map (fn e => construct name [e]) (required key child)
  fun two name key1 key2 = JSONDecode.map (fn (a,b) => construct name [a,b])
    (tuple2 (required key1 child,required key2 child))
  fun aggregate name = JSONDecode.map (fn es => construct name [terms expr_ty es])
    (required "elements" (array child))
  fun op_expr name opdec = JSONDecode.map (fn (l,oper,r) => construct name [oper,l,r])
    (tuple3 (required "left" child,required "op" opdec,required "right" child))
in dispatch (fn
    "Int" => literal_decoder () | "Decimal" => literal_decoder ()
  | "NameConstant" => literal_decoder () | "Str" => literal_decoder ()
  | "Bytes" => literal_decoder () | "HexBytes" => literal_decoder ()
  | "Hex" => literal_decoder ()
  | "Name" => JSONDecode.map (fn n => construct "SX_Name" [text n])
      (required "id" identifier)
  | "Attribute" => JSONDecode.map (fn (e,n) => construct "SX_Attribute" [e,text n])
      (tuple2 (required "value" child,required "attr" identifier))
  | "Subscript" => two "SX_Subscript" "value" "slice"
  | "NamedExpr" => two "SX_NamedExpr" "target" "value"
  | "UnaryOp" => JSONDecode.map (fn (oper,e) => construct "SX_Unary" [oper,e])
      (tuple2 (required "op" sourceConstASTLib.unary_operator,required "operand" child))
  | "BinOp" => op_expr "SX_Binary" sourceConstASTLib.binary_operator
  | "Compare" => op_expr "SX_Compare" sourceConstASTLib.comparison_operator
  | "BoolOp" => JSONDecode.map (fn (oper,es) => construct "SX_Boolean" [oper,terms expr_ty es])
      (tuple2 (required "op" sourceConstASTLib.boolean_operator,required "values" (array child)))
  | "List" => aggregate "SX_List" | "Tuple" => aggregate "SX_Tuple"
  | "Dict" => andThen (tuple2 (required "keys" (array child),required "values" (array child)))
      (fn (ks,vs) => if length ks <> length vs then error "dictionary keys/values length"
       else succeed (construct "SX_Dict" [terms entry_ty
         (ListPair.map pairSyntax.mk_pair (ks,vs))]))
  | "Call" => JSONDecode.map (fn (callee,args,kwargs) => construct "SX_Call"
      [callee,terms expr_ty args,terms keyword_ty kwargs])
      (tuple3 (required "func" child,required "args" (array child),
               required "keywords" (array (delay keyword_decoder))))
  | "ExtCall" => unary "SX_ExtCall" "value"
  | "StaticCall" => unary "SX_StaticCall" "value"
  | "IfExp" => JSONDecode.map (fn (c,t,e) => construct "SX_IfExp" [c,t,e])
      (tuple3 (required "test" child,required "body" child,required "orelse" child))
  | "Ellipsis" => succeed (construct "SX_Ellipsis" [])
  | kind => error ("unsupported expression " ^ kind)) end
and keyword_decoder () : term decoder = JSONDecode.map
  (fn (key,value) => pairSyntax.mk_pair (text key,value))
  (tuple2 (required "arg" identifier,required "value" (delay expression_decoder)))
val expression = delay expression_decoder

(* ===== Source statements, including untouched range calls ===== *)
fun statement_decoder () : term decoder = let
  val child = delay statement_decoder
  val body = required "body" (array child)
  fun nullary name = succeed (construct name [])
  fun expr name key = JSONDecode.map (fn e => construct name [e]) (required key expression)
  fun opt_expr name key = JSONDecode.map (fn e => construct name [e]) (expr_option key expression)
in dispatch (fn
    "Pass" => nullary "SS_Pass" | "Break" => nullary "SS_Break"
  | "Continue" => nullary "SS_Continue"
  | "Expr" => expr "SS_Expr" "value" | "Log" => expr "SS_Log" "value"
  | "Return" => opt_expr "SS_Return" "value" | "Raise" => opt_expr "SS_Raise" "exc"
  | "Assert" => JSONDecode.map (fn (e,msg) => construct "SS_Assert" [e,msg])
      (tuple2 (required "test" expression,expr_option "msg" expression))
  | "Assign" => JSONDecode.map (fn (target,value) => construct "SS_Assign" [target,value])
      (tuple2 (required "target" expression,required "value" expression))
  | "AnnAssign" => JSONDecode.map (fn (n,a,e) => construct "SS_AnnAssign" [text n,a,e])
      (tuple3 (required "target" target_name,required "annotation" annotation,
               expr_option "value" expression))
  | "AugAssign" => JSONDecode.map (fn (target,oper,value) => construct "SS_AugAssign" [target,oper,value])
      (tuple3 (required "target" expression,required "op" sourceConstASTLib.binary_operator,
               required "value" expression))
  | "If" => JSONDecode.map (fn (c,t,e) => construct "SS_If" [c,terms stmt_ty t,terms stmt_ty e])
      (tuple3 (required "test" expression,body,required "orelse" (array child)))
  | "For" => JSONDecode.map (fn ((n,a),iter,ss) => construct "SS_For" [text n,a,iter,terms stmt_ty ss])
      (tuple3 (required "target" (node "AnnAssign" (tuple2
                 (required "target" target_name,required "annotation" annotation))),
               required "iter" expression,body))
  | kind => error ("unsupported statement " ^ kind)) end
val statement = delay statement_decoder

(* ===== Declarations: qualifiers/initializers/defaults remain source syntax ===== *)
val argument = dispatch (fn
    "arg" => JSONDecode.map (fn (n,a) => construct "SourceArg" [text n,a])
      (tuple2 (required "arg" identifier,annotation_option "annotation"))
  | "AnnAssign" => JSONDecode.map (fn (n,a) => construct "SourceArg" [text n,a])
      (tuple2 (required "target" target_name,
               JSONDecode.map optionSyntax.mk_some (required "annotation" annotation)))
  | _ => error "unsupported argument/field declaration")
val import_alias = node "alias" (tuple2
  (required "name" string,optional_nullable "asname" identifier))
val natural = andThen intInf (fn n => if n < 0 then error "negative import level"
  else succeed (numSyntax.mk_numeral (Arbnum.fromLargeInt n)))
fun declaration_decoder () : term decoder = let
  fun named_fields ctor = JSONDecode.map (fn (n,fs) => construct ctor [text n,terms arg_ty fs])
    (tuple2 (required "name" identifier,required "body" (array argument)))
  fun structural ctor = JSONDecode.map (fn e => construct ctor [e]) (required "annotation" expression)
  fun imports from = JSONDecode.map (fn (prefix,aliases) => construct "SD_Import"
      [terms import_ty (List.map (fn (n,a) => if from then
        construct "SI_FromImport" [text (#1 prefix),#2 prefix,text n,option stringSyntax.string_ty (Option.map text a)]
        else construct "SI_Import" [text n,option stringSyntax.string_ty (Option.map text a)]) aliases)])
    (* A prefixless relative import is "" in Python AST captures and null
       in annotated Vyper ASTs. The field remains required and typed. *)
    (tuple2 (if from then tuple2 (JSONDecode.map (fn NONE => "" | SOME s => s)
               (required "module" (nullable string)),required "level" natural)
             else succeed ("",numSyntax.zero_tm),required "names" (array import_alias)))
in dispatch (fn
    "VariableDecl" => JSONDecode.map (fn (n,a,e) => construct "SD_Variable" [text n,a,e])
      (tuple3 (required "target" target_name,required "annotation" annotation,
               expr_option "value" expression))
  | "FunctionDef" => JSONDecode.map (fn ((n,decs),(args,defaults),ret,ss) =>
      construct "SD_Function" [text n,terms expr_ty decs,terms arg_ty args,
        terms expr_ty defaults,ret,terms stmt_ty ss])
      (tuple4 (tuple2 (required "name" identifier,required "decorator_list" (array expression)),
        required "args" (node "arguments" (tuple2
          (required "args" (array argument),required "defaults" (array expression)))),
        annotation_option "returns",required "body" (array statement)))
  | "StructDef" => named_fields "SD_Struct"
  | "EventDef" => andThen (required "body" (array raw)) (fn fields =>
      if length fields = 1 andalso
         JSONDecode.decode (optional "ast_type" string) (hd fields) = SOME "Pass"
      then JSONDecode.map (fn n => construct "SD_Event" [text n,terms arg_ty []])
        (required "name" identifier)
      else named_fields "SD_Event")
  | "InterfaceDef" => JSONDecode.map (fn (n,ds) => construct "SD_Interface" [text n,terms decl_ty ds])
      (tuple2 (required "name" identifier,required "body" (array (delay declaration_decoder))))
  | "FlagDef" => JSONDecode.map (fn (n,members) => construct "SD_Flag"
      [text n,terms stringSyntax.string_ty (List.map text members)])
      (tuple2 (required "name" identifier,required "body" (array
        (node "Expr" (required "value" target_name)))))
  | "Import" => imports false | "ImportFrom" => imports true
  | "ExportsDecl" => structural "SD_Exports"
  | "InitializesDecl" => structural "SD_Initializes"
  | "UsesDecl" => structural "SD_Uses"
  | "ImplementsDecl" => structural "SD_Implements"
  | kind => error ("unsupported declaration " ^ kind)) end
val declaration = delay declaration_decoder
val source_module = node "Module" (JSONDecode.map
  (fn ds => construct "SourceModule" [terms decl_ty ds]) (required "body" (array declaration)))
val annotated_ast = JSONDecode.map (fn (main,imports) =>
  construct "SourceProgram" [main,terms module_ty imports])
  (tuple2 (required "ast" source_module,
    JSONDecode.map (fn NONE => [] | SOME xs => xs) (optional "imports" (array source_module))))
val wrapped_annotated_ast = required "annotated_ast" annotated_ast

(* ===== Out-of-band provenance, never canonicalized or executed here ===== *)
type origin =
  {json_path : string list, source_id : IntInf.int option,
   node_id : IntInf.int option, src : string option,
   lineno : IntInf.int option, col_offset : IntInf.int option,
   end_lineno : IntInf.int option, end_col_offset : IntInf.int option,
   path : string option, resolved_path : string option,
   source_sha256sum : string option}
type import_claim =
  {json_path : string list, alias : string, source_id : IntInf.int,
   qualified_module_name : string, resolved_path : string, path : string option}
type decoded =
  {syntax : term, provenance : origin list, import_claims : import_claim list}
fun provenance path value = case value of
    JSON.OBJECT fields => let
      fun field key d = JSONDecode.decode (optional_nullable key d) value
      val here = case JSONDecode.decode (optional "ast_type" string) value of
        NONE => []
      | SOME _ => [{json_path=path,source_id=field "source_id" intInf,
          node_id=field "node_id" intInf,src=field "src" string,
          lineno=field "lineno" intInf,col_offset=field "col_offset" intInf,
          end_lineno=field "end_lineno" intInf,end_col_offset=field "end_col_offset" intInf,
          path=field "path" string,resolved_path=field "resolved_path" string,
          source_sha256sum=field "source_sha256sum" string} : origin]
      (* Traverse SOURCE child positions only. Never inspect compiler metadata,
         including import_infos, variable accesses, inferred types or folds. *)
      val child_keys = ["ast","imports","annotated_ast","body","orelse","test",
        "target","value","left","right","op","operand","values","elements",
        "keys","slice","func","args","keywords","annotation","returns",
        "decorator_list","defaults","iter","msg","exc","names"]
    in here @ List.concat (List.map (fn (k,v) => provenance (path @ [k]) v)
        (List.filter (fn (k,_) => List.exists (fn key => k = key) child_keys) fields)) end
  | JSON.ARRAY xs => let
      fun indexed _ [] = []
        | indexed i (v::vs) = provenance (path @ [Int.toString i]) v @ indexed (i+1) vs
    in indexed 0 xs end
  | _ => []
(* Compiler import mappings remain explicit CLAIMS, beside (not in) syntax.
   They cannot replace absent/malformed source names, annotations or bounds. *)
fun import_claims path value = case value of
    JSON.OBJECT fields => let
      fun claim i json = let fun field k d = JSONDecode.decode (required k d) json in
        {json_path=path @ ["import_infos",Int.toString i],alias=field "alias" string,
         source_id=field "source_id" intInf,
         qualified_module_name=field "qualified_module_name" string,
         resolved_path=field "resolved_path" string,
         path=JSONDecode.decode (optional_nullable "path" string) json} : import_claim
      end
      fun claims () = case JSONDecode.decode (optional "import_infos" (array raw)) value of
          NONE => []
        | SOME infos => let fun indexed _ [] = []
              | indexed i (j::js) = claim i j :: indexed (i+1) js
            in indexed 0 infos end
      val here = case JSONDecode.decode (optional "ast_type" string) value of
          SOME "Import" => claims () | SOME "ImportFrom" => claims () | _ => []
    in here @ List.concat (List.map (fn (k,v) => import_claims (path @ [k]) v)
        (List.filter (fn (k,_) => List.exists (fn key => k = key)
          ["ast","imports","body"]) fields)) end
  | JSON.ARRAY xs => let fun indexed _ [] = []
        | indexed i (v::vs) = import_claims (path @ [Int.toString i]) v @ indexed (i+1) vs
      in indexed 0 xs end
  | _ => []
val annotated_ast_with_provenance = andThen raw (fn json =>
  succeed {syntax=JSONDecode.decode annotated_ast json,provenance=provenance [] json,
           import_claims=import_claims [] json})

end
