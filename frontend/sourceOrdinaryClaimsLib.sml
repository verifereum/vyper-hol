structure sourceOrdinaryClaimsLib :> sourceOrdinaryClaimsLib = struct
open HolKernel boolLib bossLib JSONDecode sourceOrdinaryClaimsTheory

type expression_pair = {claims:term, projection:thm, shape:thm, source_match:thm}
type paired =
  {original:sourceModuleLoaderLib.loaded, annotated:JSON.value, claims:term, retained:term,
   projection:thm, shape:thm, source_match:thm,
   origins:sourceSyntaxLib.origin list,
   import_claims:sourceSyntaxLib.import_claim list}
fun fail_at path message = JSONDecode.decode
  (fail ("ordinary claims " ^ String.concatWith "/" path ^ ": " ^ message)) JSON.NULL
fun required key d = andThen (sourceConstASTLib.optional_field key d)
  (fn SOME v => succeed v | NONE => fail ("ordinary claims: missing " ^ key))
fun get key json = JSONDecode.decode (required key raw) json
fun kind json = JSONDecode.decode (required "ast_type" string) json
fun optional key d json = JSONDecode.decode (sourceConstASTLib.optional_field key d) json
fun put key value (JSON.OBJECT fs) = JSON.OBJECT
      ((key,value)::List.filter (fn (k,_) => k <> key) fs)
  | put _ _ _ = raise Fail "ordinary claims: object invariant"
fun without_folds (JSON.OBJECT fs) = JSON.OBJECT (List.map
      (fn (k,v) => (k,without_folds v))
      (List.filter (fn (k,_) => k <> "folded_value" andalso k <> "folded_literal") fs))
  | without_folds (JSON.ARRAY xs) = JSON.ARRAY (List.map without_folds xs)
  | without_folds v = v

(* Only source grammar fields are compared/traversed. Optional nullable source
   fields use null for absence, exactly as sourceSyntaxLib does. Metadata is
   never a source child. Unknown node kinds already fail source-only decoding. *)
fun fields k = case k of
    "Module" => ["body"]
  | "Int" => ["value"] | "Decimal" => ["value"]
  | "NameConstant" => ["value"] | "Str" => ["value"]
  | "Bytes" => ["value"] | "HexBytes" => ["value"] | "Hex" => ["value"]
  | "Name" => ["id"] | "Attribute" => ["value","attr"]
  | "Subscript" => ["value","slice"] | "NamedExpr" => ["target","value"]
  | "UnaryOp" => ["op","operand"]
  | "BinOp" => ["left","op","right"] | "Compare" => ["left","op","right"]
  | "BoolOp" => ["op","values"] | "List" => ["elements"] | "Tuple" => ["elements"]
  | "Dict" => ["keys","values"] | "Call" => ["func","args","keywords"]
  | "keyword" => ["arg","value"]
  | "ExtCall" => ["value"] | "StaticCall" => ["value"]
  | "IfExp" => ["test","body","orelse"]
  | "Expr" => ["value"] | "Log" => ["value"]
  | "Return" => ["value"] | "Raise" => ["exc"] | "Assert" => ["test","msg"]
  | "Assign" => ["target","value"] | "AnnAssign" => ["target","annotation","value"]
  | "AugAssign" => ["target","op","value"]
  | "If" => ["test","body","orelse"] | "For" => ["target","iter","body"]
  | "arg" => ["arg","annotation"] | "arguments" => ["args","defaults"]
  | "VariableDecl" => ["target","annotation","value"]
  | "FunctionDef" => ["name","decorator_list","args","returns","body"]
  | "StructDef" => ["name","body"] | "EventDef" => ["name","body"]
  | "InterfaceDef" => ["name","body"] | "FlagDef" => ["name","body"]
  | "Import" => ["names"] | "ImportFrom" => ["module","level","names"]
  | "alias" => ["name","asname"]
  | "ExportsDecl" => ["annotation"] | "InitializesDecl" => ["annotation"]
  | "UsesDecl" => ["annotation"] | "ImplementsDecl" => ["annotation"]
  | _ => [] (* operators and nullary syntax, validated by sourceSyntaxLib *)
fun nullable_field k key = List.exists (fn p => p = (k,key))
  [("Return","value"),("Raise","exc"),("Assert","msg"),("AnnAssign","value"),
   ("VariableDecl","value"),("arg","annotation"),("FunctionDef","returns"),("alias","asname")]
(* Python serializes a prefixless relative ImportFrom as "", whereas the
   annotated Vyper AST uses null. Both denote the same REQUIRED empty prefix;
   do not generalize this equivalence to other source strings or absence. *)
fun source_field k key json = if k = "ImportFrom" andalso key = "module" then
    (case get key json of JSON.NULL => JSON.STRING "" | value => value)
  else if nullable_field k key then
    (case optional key raw json of NONE => JSON.NULL | SOME v => v)
  else get key json
fun qualifier json = if kind json <> "Call" then NONE else let
  val callee = get "func" json
  val name = if kind callee = "Name" then
    JSONDecode.decode (required "id" string) callee else ""
in if List.exists (fn n => name = n) ["constant","immutable","public","transient"]
  then case (get "args" json,get "keywords" json) of
      (JSON.ARRAY [inner],JSON.ARRAY []) => SOME (name,inner)
    | _ => NONE
  else NONE end
fun syntax_wrapper (JSON.OBJECT fs) = JSON.OBJECT (List.filter (fn (k,_) =>
      k <> "type" andalso k <> "variable_reads" andalso k <> "variable_writes") fs)
  | syntax_wrapper _ = raise Fail "ordinary claims: qualifier wrapper invariant"
fun declaration k = List.exists (fn n => n = k)
  ["VariableDecl","FunctionDef","StructDef","EventDef","InterfaceDef","FlagDef",
   "arg","AnnAssign","alias","Import","ImportFrom","ExportsDecl","InitializesDecl","UsesDecl","ImplementsDecl"]
fun same_id path key original annotated =
  if optional key intInf original = optional key intInf annotated then ()
  else fail_at path ("origin mismatch: " ^ key)

(* Decimal serialization alone may canonicalize a source token. Reuse the
   source-only literal parser, check BOTH precisions independently, and compare
   exact integers at a common decimal scale. Never consult folded metadata or
   round a token to the runtime scale. The matched node keeps the ORIGINAL
   token (including its precision), not the annotated spelling. *)
fun decimal_value path original annotated = let
  val original_value = get "value" original
  val annotated_value = get "value" annotated
in if JSONDecode.decode string original_value = JSONDecode.decode string annotated_value
  then original_value else let
  fun parts json = case strip_comb
      (JSONDecode.decode sourceConstASTLib.expression json) of
      (_, [lit]) => (case strip_comb lit of (_, [coefficient,places]) =>
          (coefficient,places)
        | _ => raise Fail "ordinary claims: Decimal literal invariant")
    | _ => raise Fail "ordinary claims: Decimal expression invariant"
  val (oc,oplaces) = parts original
  val (ac,aplaces) = parts annotated
  fun require label proposition = let
    val result = (REWRITE_CONV [integerTheory.INT_EXP] THENC EVAL
      THENC intLib.REDUCE_CONV) proposition
  in if aconv (rhs (concl result)) boolSyntax.T then ()
     else fail_at path label end
  val () = require "original Decimal precision" ``^oplaces <= 10``
  val () = require "annotated Decimal precision" ``^aplaces <= 10``
  val () = require "Decimal value mismatch"
    ``^oc * &(10 ** ^aplaces) = ^ac * &(10 ** ^oplaces)``
in original_value end end

(* A zipper over the existing source grammar, NOT a new expression parser.
   Erasure is allowed only at a matched VariableDecl.annotation, recursively
   through its original outer qualifier wrappers. No runtime flag is consulted. *)
fun zip path erase original annotated =
  case (original,annotated) of
    (JSON.OBJECT _,JSON.OBJECT _) => let
      val okind = kind original
      val akind = kind annotated
      val erased = if erase then qualifier original else NONE
      val drop = case erased of NONE => false | SOME (q,_) =>
        (case qualifier annotated of SOME (r,_) => q <> r | NONE => true)
    in if drop then let
        val (_,inner) = valOf erased
        val paired = zip (path @ ["erased"]) true inner annotated
      in put "args" (JSON.ARRAY [paired])
        (put "func" (syntax_wrapper (get "func" original)) (syntax_wrapper original)) end
      else if okind <> akind then fail_at path "constructor mismatch"
      else let
        val () = if declaration okind orelse okind = "Module"
          then same_id path "node_id" original annotated else ()
        val () = if okind = "Module" then same_id path "source_id" original annotated else ()
        fun field key result = put key
          (if okind = "Decimal" andalso key = "value" then
             decimal_value (path @ [key]) original annotated
           else zip (path @ [key]) (okind = "VariableDecl" andalso key = "annotation" orelse
             erase andalso okind = "Call" andalso key = "args")
             (source_field okind key original) (source_field akind key annotated)) result
      in List.foldl (fn (key,result) => field key result) annotated (fields okind) end
    end
  | (JSON.ARRAY os,JSON.ARRAY anns) =>
      if length os <> length anns then fail_at path "child count mismatch"
      else let fun loop _ [] [] = []
          | loop i (o1::oss) (a1::ass) =
              zip (path @ [Int.toString i]) erase o1 a1 :: loop (i+1) oss ass
          | loop _ _ _ = raise Fail "ordinary claims: zip invariant"
      in JSON.ARRAY (loop 0 os anns) end
  | (JSON.STRING a,JSON.STRING b) => if a = b then annotated else fail_at path "spelling mismatch"
  | (JSON.INT a,JSON.INT b) => if a = b then annotated else fail_at path "literal mismatch"
  | (JSON.BOOL a,JSON.BOOL b) => if a = b then annotated else fail_at path "Boolean mismatch"
  | (JSON.NULL,JSON.NULL) => annotated
  | _ => fail_at path "source field mismatch"

fun construct name args = list_mk_comb
  (prim_mk_const {Thy="sourceOrdinaryClaims",Name=name},args)
val claims_ty = mk_thy_type {Thy="sourceOrdinaryClaims",Tyop="source_claims",Args=[]}
fun list ty xs = listSyntax.mk_list (xs,ty)
fun equation label a b = if aconv a b then REFL a
  else fail_at [] (label ^ " source projection mismatch")
(* Cache kernel certificates only, never parsing, zipper checks or metadata
   validation. Fold-deletion/poisoning gives identical large HOL claim trees. *)
val shape_certificates = ref ([] : thm list)
fun checked label proposition =
  case List.find (fn th => aconv (concl th) proposition) (!shape_certificates) of
    SOME th => th
  | NONE => let val equality = EVAL proposition in
      if aconv (rhs (concl equality)) boolSyntax.T then let
        val th = EQT_ELIM equality
        val () = shape_certificates := th :: List.take
          (!shape_certificates,Int.min (15,length (!shape_certificates)))
      in th end else fail_at [] (label ^ " mirror shape mismatch") end
fun decode_source json = JSONDecode.decode sourceSyntaxLib.expression json
fun array key json = JSONDecode.decode (required key (JSONDecode.array raw)) json
fun expression_children json = case kind json of
    "Attribute" => [get "value" json]
  | "Subscript" => [get "value" json,get "slice" json]
  | "NamedExpr" => [get "target" json,get "value" json]
  | "UnaryOp" => [get "operand" json]
  | "BinOp" => [get "left" json,get "right" json]
  | "Compare" => [get "left" json,get "right" json]
  | "BoolOp" => array "values" json
  | "List" => array "elements" json | "Tuple" => array "elements" json
  | "Dict" => List.concat (ListPair.map (fn (k,v) => [k,v])
      (array "keys" json,array "values" json))
  | "Call" => get "func" json :: (array "args" json @
      List.map (get "value") (array "keywords" json))
  | "ExtCall" => [get "value" json] | "StaticCall" => [get "value" json]
  | "IfExp" => [get "test" json,get "body" json,get "orelse" json]
  | _ => []
(* Legacy decoding historically defaults malformed present metadata. Validate
   present claims first, except the exact syntax-guarded calldata sentinel below.
   This is structural validation, not independent type inference. *)
val natural = andThen intInf (fn n => if n < 0 then
  fail "ordinary claims: negative natural claim" else succeed n)
fun validate_type _ JSON.NULL = ()
  | validate_type calldata json = let
      fun field key d = ignore (JSONDecode.decode (required key d) json)
      fun nested key = validate_type false (get key json)
      fun types key = app (validate_type false) (array key json)
      val tc = optional "typeclass" string json
      val name = optional "name" string json
      val _ = optional "generic" string json
      val () = case tc of
          SOME "integer" => (field "bits" natural; field "is_signed" bool)
        | SOME "bytes_m" => field "m" natural
        | SOME "static_array" => (nested "value_type"; field "length" natural)
        | SOME "$SArray" => (nested "value_type"; field "length" natural)
        | SOME "dynamic_array" => (nested "value_type"; field "length" natural)
        | SOME "tuple" => types "member_types"
        | SOME "hashmap" => (nested "key_type"; nested "value_type")
        | _ => ()
      val () = case name of
          SOME "Bytes" =>
            (* The pin marks msg.data as Bytes[INF]. This is not a bounded
               value type: retain the legacy optional-type decoding for the
               existing syntax-directed calldata dispatch, without admitting
               INF on other expressions or nested type claims. *)
            if calldata andalso tc = SOME "bytes" andalso
              (case optional "length" raw json of SOME (JSON.STRING "INF") => true
                | _ => false) then ()
            else ignore (JSONDecode.decode jsonASTLib.json_type json)
        | SOME "String" => ignore (JSONDecode.decode jsonASTLib.json_type json)
        | SOME "DynArray" => (nested "value_type"; field "length" natural)
        | _ => ()
      val () = case optional "type_t" raw json of NONE => () | SOME t => validate_type false t
      val () = case optional "type_decl_node" raw json of NONE => ()
        | SOME node => ignore (JSONDecode.decode (required "source_id" intInf) node)
      val () = case optional "argument_types" (JSONDecode.array raw) json of
          NONE => () | SOME ts => app (validate_type false) ts
      val () = case optional "return_type" raw json of NONE => () | SOME t => validate_type false t
      val () = if Option.isSome tc orelse Option.isSome name orelse
        Option.isSome (optional "generic" string json) orelse
        Option.isSome (optional "type_t" raw json) then ()
        else fail_at [] "malformed present type claim"
    in () end
fun validate_node syntax json = let
  (* syntax is decoded from, and checked against, the original source. Neither
     metadata nor a folded branch can grant this exception. *)
  val calldata = aconv syntax
    ``sourceSyntax$SX_Attribute (sourceSyntax$SX_Name "msg") "data"``
  val () = case optional "type" raw json of NONE => () | SOME t => validate_type calldata t
  fun accesses key = case optional key (JSONDecode.array raw) json of NONE => ()
    | SOME xs => app (fn access => ignore (JSONDecode.decode
        (required "decl_node" (required "source_id" intInf)) access)) xs
  val () = accesses "variable_reads"
  val () = accesses "variable_writes"
in () end
val source_expr_ty = mk_thy_type {Thy="sourceSyntax",Tyop="source_expr",Args=[]}
val legacy_expr_ty = mk_thy_type {Thy="jsonAST",Tyop="json_expr",Args=[]}
val legacy_keyword_ty = mk_thy_type {Thy="jsonAST",Tyop="json_keyword",Args=[]}
fun carries expr_ty ty = ty = expr_ty orelse
  (expr_ty = legacy_expr_ty andalso ty = legacy_keyword_ty) orelse
  (not (is_vartype ty) andalso List.exists (carries expr_ty) (#Args (dest_thy_type ty)))
(* Walk already-decoded constructor arguments, stopping at expression children.
   This does not parse/evaluate a second AST. In particular every ordinary
   source/legacy expression root is decoded once, not again at each child. *)
fun decoded_children expr_ty term = let
  fun collect tm = if type_of tm = expr_ty then [tm]
    else if carries expr_ty (type_of tm) then
      List.concat (List.map collect (snd (strip_comb tm))) else []
in List.concat (List.map collect (snd (strip_comb term))) end
fun tree_from resolve source json = let
  fun build syntax legacy node = let
    val () = validate_node syntax node
    val nodes = expression_children node
    val sources = decoded_children source_expr_ty syntax
    (* Legacy external wrappers omit their original Call/Attribute nodes.
       Decode that distinct source Call once too, to retain its own claims. *)
    val legacies = if kind node = "ExtCall" orelse kind node = "StaticCall" then
      [resolve (JSONDecode.decode jsonASTLib.json_expr (get "value" node))]
      else decoded_children legacy_expr_ty legacy
    val () = if length nodes = length sources andalso length nodes = length legacies
      then () else fail_at [] "decoded child coverage mismatch"
    val children = ListPair.map (fn (j,(s,l)) => build s l j)
      (nodes,ListPair.zip (sources,legacies))
  in construct "SourceClaims" [syntax,legacy,list claims_ty children] end
in build source (resolve (JSONDecode.decode jsonASTLib.json_expr json)) json end
fun tree resolve json = tree_from resolve (decode_source json) json
fun project claims = mk_comb (prim_mk_const
  {Thy="sourceOrdinaryClaims",Name="source_claims_source"},claims)
fun pair_expression original annotated = let
  val source = decode_source original
  val clean = without_folds annotated
  val _ = decode_source clean (* fail before using legacy metadata *)
  val matched = zip [] false (without_folds original) clean
  val source_match = equation "expression" (decode_source matched) source
  val claims = tree_from I source matched
in {claims=claims,source_match=source_match,
    projection=REWRITE_CONV [source_claims_source_def] (project claims),
    shape=checked "expression" (construct "source_claims_shape" [claims])}
end

fun expression_kind k = List.exists (fn n => n = k)
  ["Int","Decimal","NameConstant","Str","Bytes","HexBytes","Hex","Name",
   "Attribute","Subscript","NamedExpr","UnaryOp","BinOp","Compare","BoolOp",
   "List","Tuple","Dict","Call","ExtCall","StaticCall","IfExp","Ellipsis"]
fun number n = numSyntax.mk_numeral (Arbnum.fromInt n)
fun mapi f xs = let fun go _ [] = []
  | go i (x::rest) = f (i,x) :: go (i+1) rest
  in go 0 xs end
(* Read only declaration names and their paired module origins. A full legacy
   program decoder would also require inherited function/variable metadata on
   declarations which the source route deliberately elaborates independently.
   The upstream resolver still decides uniqueness, kind and recursive types. *)
fun module_source_id json =
  case optional "source_id" intInf json of SOME n => n | NONE => ~1
fun source_id_term n = intSyntax.term_of_int (Arbint.fromLargeInt n)
(* The inherited frontend removes repeated import bodies BEFORE allocating
   identities. Do not approximate that equality with source syntax: in collision
   mode require unique resolved paths, so no body deduplication is needed.
   Empty bodies below are identity-only skeletons, not legacy declarations. *)
fun nominal_import_sources main imports = let
  fun resolved json = case optional "resolved_path" raw json of
      NONE => NONE | SOME JSON.NULL => NONE
    | SOME value => SOME (JSONDecode.decode string value)
  val infos = List.map (fn j => (module_source_id j,resolved j)) imports
  val collision = List.exists (fn (sid,path) => Option.isSome path andalso
    List.exists (fn (other,other_path) => sid = other andalso
      Option.isSome other_path andalso path <> other_path) infos) infos
in if not collision then List.map (source_id_term o module_source_id) imports
  else let
    fun require_path j = case resolved j of SOME path => path
      | NONE => fail_at ["imports"]
          "canonical nominal identity repair requires resolved_path on every import when source IDs collide"
    val paths = List.map require_path imports
    fun unique [] = ()
      | unique (path::rest) = if List.exists (fn p => p = path) rest then
          fail_at ["imports"]
            ("canonical nominal identity repair rejects repeated resolved_path when source IDs collide: " ^ path)
        else unique rest
    val () = unique paths
    fun skeleton (j,path) = let
      val src = source_id_term (JSONDecode.decode (required "source_id" intInf) j)
      val resolved = stringSyntax.fromMLstring path
    in ``jsonAST$JImportedModule ^src "" ^resolved F []`` end
    (* ALL imports contribute to both the maximum and allocation position,
       including modules with no nominal declarations. *)
    val modules = list ``:jsonAST$json_imported_module``
      (ListPair.map skeleton (imports,paths))
    val main_src = source_id_term (module_source_id main)
    val identities = rhs (concl ((REWRITE_CONV
      [jsonToVyperTheory.build_module_identity_map_def] THENC EVAL)
      ``jsonToVyper$build_module_identity_map ^main_src ^modules``))
    fun lookup path = let
      val resolved = stringSyntax.fromMLstring path
      val result = rhs (concl (EVAL
        ``jsonToVyper$lookup_module_identity ^resolved ^identities``))
    in if optionSyntax.is_some result then optionSyntax.dest_some result
       else fail_at ["imports"] "canonical nominal identity lookup failed" end
  in List.map lookup paths end
end
fun nominal_declarations json = let
  fun declarations (module_json,src) = let
    fun declaration node = let
      val nominal = case kind node of
          "StructDef" => SOME ``jsonToVyperType$StructKind``
        | "FlagDef" => SOME ``jsonToVyperType$FlagKind``
        | _ => NONE
    in Option.map (fn k => pairSyntax.mk_pair
      (pairSyntax.mk_pair (k,stringSyntax.fromMLstring
        (JSONDecode.decode string (get "name" node))),src)) nominal end
  in List.mapPartial declaration (array "body" module_json) end
  val imports = case optional "imports" (JSONDecode.array raw) json of
      NONE => [] | SOME xs => xs
  val raw_import_decls = List.map (fn j =>
    declarations (j,source_id_term (module_source_id j))) imports
  (* Canonical import identities matter only for imported nominals. Preserve
     the ordinary path policy otherwise, including main-only nominal repair. *)
  val import_decls = if List.all List.null raw_import_decls then [] else
    List.concat (ListPair.map declarations
      (imports,nominal_import_sources (get "ast" json) imports))
in list ``:(jsonToVyperType$nominal_kind # string) # int``
  (declarations (get "ast" json,source_id_term (module_source_id (get "ast" json))) @
   import_decls) end
fun roots resolve path json = case json of
    JSON.OBJECT _ => let val k = kind json in
      if expression_kind k then [(path,tree resolve json)] else
      List.concat (mapi (fn (i,key) => roots resolve (path @ [i]) (source_field k key json)) (fields k))
    end
  | JSON.ARRAY xs => List.concat (mapi (fn (i,j) => roots resolve (path @ [i]) j) xs)
  | _ => []
fun pair_program original original_json annotated = let
  val _ = sourceModuleLoaderLib.policies original
  val original_program = JSONDecode.decode sourceSyntaxLib.annotated_ast original_json
  val _ = equation "loader" original_program (#program original)
  val clean = without_folds annotated
  val _ = JSONDecode.decode sourceSyntaxLib.annotated_ast clean
  val original_clean = without_folds original_json
  val main = zip ["ast"] false (get "ast" original_clean) (get "ast" clean)
  fun imports json = case optional "imports" raw json of NONE => JSON.ARRAY [] | SOME v => v
  val imports = zip ["imports"] false (imports original_clean) (imports clean)
  val matched = JSON.OBJECT [("ast",main),("imports",imports)]
  val decoded = JSONDecode.decode sourceSyntaxLib.annotated_ast_with_provenance matched
  val source_match = equation "program" (#syntax decoded) (#program original)
  val decls = nominal_declarations matched
  val no_nominals = List.null (fst (listSyntax.dest_list decls))
  fun resolve legacy = if no_nominals then legacy else rhs (concl (EVAL
    ``jsonNominalSources$resolve_json_expr ^decls ^legacy``))
  val entries = roots resolve [0] main @ roots resolve [1] imports
  val entry_ty = pairSyntax.mk_prod (listSyntax.mk_list_type numSyntax.num,claims_ty)
  val claims = construct "SourceProgramClaims" [#program original,list entry_ty
    (List.map (fn (path,c) => pairSyntax.mk_pair (list numSyntax.num (List.map number path),c)) entries)]
  val retained = mk_icomb (mk_icomb
    (prim_mk_const {Thy="sourceSyntax",Name="SourceRetained"},#program original),claims)
in {original=original,annotated=clean,claims=claims,retained=retained,source_match=source_match,
    projection=REWRITE_CONV [source_program_claims_source_def]
      (construct "source_program_claims_source" [claims]),
    shape=checked "program" (construct "source_program_claims_shape" [claims]),
    origins= #provenance decoded,import_claims= #import_claims decoded}
end
end
