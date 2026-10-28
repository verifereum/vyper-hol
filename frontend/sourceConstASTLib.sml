structure sourceConstASTLib :> sourceConstASTLib = struct

open HolKernel boolLib JSONDecode
open sourceConstASTTheory sourceConstAnnotationTheory

(* ===== Strict, source-only decoding helpers ===== *)

fun error message = fail ("source constant frontend: " ^ message)
fun construct thy name args =
  list_mk_comb (prim_mk_const {Thy=thy, Name=name}, args)
fun source name args = construct "sourceConstAST" name args
fun ann name args = construct "sourceConstAnnotation" name args
fun ty thy name = mk_thy_type {Thy=thy, Tyop=name, Args=[]}
val expr_ty = ty "sourceConstAST" "source_const_expr"
val ann_ty = ty "sourceConstAnnotation" "source_const_annotation"
val keyword_ty = pairSyntax.mk_prod (stringSyntax.string_ty, expr_ty)
fun exprs xs = listSyntax.mk_list (xs, expr_ty)
fun annotations xs = listSyntax.mk_list (xs, ann_ty)
fun strings xs = listSyntax.mk_list
  (List.map stringSyntax.fromMLstring xs, stringSyntax.string_ty)

(* JSONDecode.fieldO collapses null and absence. try/orElse would also hide a
   malformed present value. Inspect presence first instead, with no retry. *)
fun optional_field key d = andThen rawObject (fn fields =>
  case List.filter (fn (name,_) => name = key) fields of
    [] => succeed NONE
  | [(_,value)] => succeed (SOME (decode d value))
  | _ => error ("duplicate field " ^ key))
fun required key d = andThen (optional_field key d) (fn
    SOME value => succeed value
  | NONE => error ("missing field " ^ key))
fun node kind d = andThen (required "ast_type" string) (fn actual =>
  if actual = kind then d else error ("expected " ^ kind))
fun dispatch f = andThen (required "ast_type" string) f
fun exact_pair d1 d2 = andThen (array raw) (fn
    [a,b] => succeed (decode d1 a, decode d2 b)
  | _ => error "expected exactly two elements")

(* All integer conversion is literal parsing, never arithmetic evaluation. *)
val integer = JSONDecode.map
  (fn i => intSyntax.term_of_int (Arbint.fromLargeInt i)) intInf
val identifier = andThen string (fn s =>
  if size s > 0 andalso
     (Char.isAlpha (String.sub (s,0)) orelse String.sub (s,0) = #"_") andalso
     List.all (fn c => Char.isAlphaNum c orelse c = #"_") (String.explode s)
  then succeed s else error "invalid identifier")
fun path () = dispatch (fn
    "Name" => JSONDecode.map (fn s => [s]) (required "id" identifier)
  | "Attribute" => JSONDecode.map (fn (base,attr) => base @ [attr])
      (tuple2 (required "value" (delay path), required "attr" identifier))
  | _ => error "expected a name/attribute path")
val name_path = delay path

fun operator table = dispatch (fn spelling =>
  case List.find (fn (s,_) => spelling = s) table of
    SOME (_,name) => succeed (source name [])
  | NONE => error ("unsupported operator " ^ spelling))
val unary = operator [("USub","SCU_Neg"), ("Not","SCU_Not"),
                       ("Invert","SCU_Invert")]
val binary = operator [("Add","SCB_Add"), ("Sub","SCB_Sub"),
  ("Mult","SCB_Mul"), ("Div","SCB_Div"), ("FloorDiv","SCB_FloorDiv"),
  ("Mod","SCB_Mod"), ("Pow","SCB_Pow"), ("LShift","SCB_LShift"),
  ("RShift","SCB_RShift"), ("BitAnd","SCB_BitAnd"),
  ("BitOr","SCB_BitOr"), ("BitXor","SCB_BitXor")]
val boolean = operator [("And","SCB_And"), ("Or","SCB_Or")]
val unary_operator = unary
val binary_operator = binary
val boolean_operator = boolean
val comparison = operator [("Eq","SCC_Eq"), ("NotEq","SCC_NotEq"),
  ("Lt","SCC_Lt"), ("LtE","SCC_Le"), ("Gt","SCC_Gt"),
  ("GtE","SCC_Ge"), ("In","SCC_In"), ("NotIn","SCC_NotIn")]

val comparison_operator = comparison

(* ===== Exact literal tokens ===== *)

(* Underscores only between digits; validate the ENTIRE token before stripping
   punctuation. No floats, prefix parsing or filtering source expressions. *)
fun digits s = let
  fun tail [] = true
    | tail (#"_"::c::cs) = Char.isDigit c andalso tail cs
    | tail (c::cs) = Char.isDigit c andalso tail cs
in case String.explode s of [] => false
   | c::cs => Char.isDigit c andalso tail cs end
fun strip_underscores s = String.implode
  (List.filter (fn c => c <> #"_") (String.explode s))
fun unsigned s =
  if String.isPrefix "+" s orelse String.isPrefix "-" s
  then String.extract (s,1,NONE) else s
fun negative s = String.isPrefix "-" s
fun int_token neg s = intSyntax.term_of_int
  (Arbint.fromString ((if neg then "~" else "") ^ s))
fun nat_token s = numSyntax.mk_numeral (Arbnum.fromString s)

fun decimal_token token = let
  val (base,exp) = case String.fields (fn c => c = #"e" orelse c = #"E") token of
      [base] => (base,NONE)
    | [base,e] => (base,SOME e)
    | _ => ("",NONE)
  val mantissa = unsigned base
  val parts = String.fields (fn c => c = #".") mantissa
  val valid_base = case parts of
      [whole] => digits whole
    | [whole,frac] =>
        (digits whole andalso (frac = "" orelse digits frac)) orelse
        (whole = "" andalso digits frac)
    | _ => false
  val valid_exp = case exp of NONE => true | SOME e => digits (unsigned e)
in
  if not (valid_base andalso valid_exp) then error "invalid decimal token"
  else let
    val (whole,frac) = case parts of [w,f] => (w,f) | [w] => (w,"")
      | _ => raise Fail "validated decimal parts"
    val coefficient = int_token (negative base)
      (strip_underscores (whole ^ frac))
    val places = numSyntax.term_of_int (size (strip_underscores frac))
    (* Exponent scaling stays as closed HOL arithmetic, never host powers or
       floating point. This also avoids expanding huge positive exponents in
       ML. Normalization/precision checking belongs to HOL consumers. *)
    val (coefficient,places) = case exp of
        NONE => (coefficient,places)
      | SOME e => let val exponent = nat_token (strip_underscores (unsigned e)) in
          if negative e then (coefficient, numSyntax.mk_plus (places,exponent))
          else (intSyntax.mk_mult (coefficient,
                  intSyntax.mk_exp (int_token false "10",
                    numSyntax.mk_minus (exponent,places))),
                numSyntax.mk_minus (places,exponent))
        end
  in succeed (source "SCL_Decimal" [coefficient,places]) end
end

fun hex_octets s = let
  val body = if String.isPrefix "0x" s then String.extract (s,2,NONE) else ""
  fun pairs [] = []
    | pairs (a::b::rest) =
        numSyntax.mk_numeral (Arbnum.fromHexString (String.implode [a,b]))
        :: pairs rest
    | pairs _ = raise Fail "validated hex pairs"
in
  if not (String.isPrefix "0x" s) orelse size body mod 2 <> 0 orelse
     not (List.all Char.isHexDigit (String.explode body))
  then error "expected 0x followed by complete hexadecimal octets"
  else succeed (listSyntax.mk_list (pairs (String.explode body), numSyntax.num))
end

(* ===== Original expression syntax ===== *)

fun expression_decoder () : term decoder = let
  val child = delay expression_decoder
  fun literal name d = JSONDecode.map
    (fn x => source "SCE_Literal" [source name [x]]) (required "value" d)
  fun aggregate name = JSONDecode.map (fn es => source name [exprs es])
    (required "elements" (array child))
in dispatch (fn
    "Int" => literal "SCL_Int" integer
  | "Decimal" => JSONDecode.map (fn lit => source "SCE_Literal" [lit])
      (andThen (required "value" string) decimal_token)
  | "NameConstant" => literal "SCL_Bool" (JSONDecode.map boolSyntax.mk_bool bool)
  | "Str" => literal "SCL_String" (JSONDecode.map stringSyntax.fromMLstring string)
  | "Bytes" => literal "SCL_Bytes" (andThen string hex_octets)
  | "HexBytes" => literal "SCL_Bytes" (andThen string hex_octets)
  | "Hex" => andThen (required "value" string) (fn s =>
      if s = "0x" then error "empty Hex literal"
      else JSONDecode.map (fn _ => source "SCE_Literal"
        [source "SCL_Hex" [stringSyntax.fromMLstring s]]) (hex_octets s))
  | "Name" => JSONDecode.map (fn p => source "SCE_Name" [strings p]) name_path
  | "Attribute" => JSONDecode.map (fn p => source "SCE_Name" [strings p]) name_path
  | "UnaryOp" => JSONDecode.map (fn (op_tm,e) => source "SCE_Unary" [op_tm,e])
      (tuple2 (required "op" unary, required "operand" child))
  | "BinOp" => JSONDecode.map (fn (l,op_tm,r) => source "SCE_Binary" [op_tm,l,r])
      (tuple3 (required "left" child, required "op" binary, required "right" child))
  | "Compare" => JSONDecode.map (fn (l,op_tm,r) => source "SCE_Compare" [op_tm,l,r])
      (tuple3 (required "left" child, required "op" comparison, required "right" child))
  | "BoolOp" => JSONDecode.map (fn (op_tm,es) => source "SCE_Boolean" [op_tm,exprs es])
      (tuple2 (required "op" boolean, required "values" (array child)))
  | "List" => aggregate "SCE_List"
  | "Tuple" => aggregate "SCE_Tuple"
  | "Subscript" => JSONDecode.map (fn (base,index) => source "SCE_Subscript" [base,index])
      (tuple2 (required "value" child, required "slice" child))
  | "Call" => JSONDecode.map (fn (callee,args,kwargs) =>
      source "SCE_Call" [callee,exprs args,kwargs])
      (tuple3 (required "func" child, required "args" (array child),
               required "keywords" (delay keywords_decoder)))
  | kind => error ("unsupported expression " ^ kind)) end
and keyword_decoder () : term decoder = JSONDecode.map
  (fn (name,value) => pairSyntax.mk_pair (stringSyntax.fromMLstring name,value))
  (tuple2 (required "arg" identifier,
           required "value" (delay expression_decoder)))
and keywords_decoder () : term decoder = JSONDecode.map
  (fn xs => listSyntax.mk_list (xs,keyword_ty)) (array (delay keyword_decoder))

val expression = delay expression_decoder
val keyword = delay keyword_decoder
val keywords = delay keywords_decoder
val annotation_bound = expression

(* ===== Source annotations and qualifiers ===== *)

val containers = ["String","Bytes","DynArray","HashMap"]
fun annotation_decoder () : term decoder = let
  val child = delay annotation_decoder
  fun bounded ctor = JSONDecode.map (fn bound => ann ctor [bound])
    (required "slice" annotation_bound)
  fun pair_slice d1 d2 = required "slice"
    (node "Tuple" (required "elements" (exact_pair d1 d2)))
  fun subscript () = andThen (required "value" name_path) (fn path =>
    case path of
      ["String"] => bounded "SCA_String"
    | ["Bytes"] => bounded "SCA_Bytes"
    | ["DynArray"] => JSONDecode.map (fn (element,bound) =>
        ann "SCA_DynArray" [element,bound]) (pair_slice child annotation_bound)
    | ["HashMap"] => JSONDecode.map (fn (key,value) =>
        ann "SCA_HashMap" [key,value]) (pair_slice child child)
    | _ => static_array ())
  and static_array () = JSONDecode.map (fn (element,bound) =>
    ann "SCA_StaticArray" [element,bound])
    (tuple2 (required "value" child, required "slice" annotation_bound))
  (* The base of a static array can itself be subscript/tuple/qualified syntax;
     do not catch decoding errors and retry as another annotation kind. *)
  fun indexed () = andThen (required "value" (required "ast_type" string))
    (fn kind => if kind = "Name" orelse kind = "Attribute"
      then subscript () else static_array ())
  fun named () = andThen name_path (fn path =>
    if List.length path = 1 andalso List.exists (fn n => path = [n]) containers
    then error "annotation requires bound/type parameter syntax"
    else succeed (ann "SCA_Name" [strings path]))
  fun qualified () = andThen (required "func" name_path) (fn path =>
    case List.find (fn (s,_) => path = [s])
      [("constant","SCQ_Constant"), ("immutable","SCQ_Immutable"),
       ("public","SCQ_Public"), ("transient","SCQ_Transient"),
       ("indexed","SCQ_Indexed")] of
      NONE => error "unsupported annotation qualifier"
    | SOME (_,ctor) => andThen
        (tuple2 (required "args" (array child), required "keywords" (array raw)))
        (fn ([inner],[]) => succeed (ann "SCA_Qualified" [ann ctor [],inner])
          | _ => error "qualifier requires one annotation and no keywords"))
in dispatch (fn
    "Name" => named ()
  | "Attribute" => named ()
  | "Subscript" => indexed ()
  | "Tuple" => JSONDecode.map (fn xs => ann "SCA_Tuple" [annotations xs])
      (required "elements" (array child))
  | "Call" => qualified ()
  | kind => error ("unsupported annotation " ^ kind)) end

val annotation = delay annotation_decoder
fun annotation_field key = JSONDecode.map (fn NONE => NONE | SOME x => x)
  (optional_field key (nullable annotation))

end
