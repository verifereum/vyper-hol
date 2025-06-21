structure vyperTestLib :> vyperTestLib = struct

open HolKernel JSONDecode JSONUtil cv_transLib wordsLib
     pairSyntax listSyntax stringSyntax optionSyntax
     intSyntax wordsSyntax fcpSyntax
     vyperAbiTheory vyperAstTheory vyperTestRunnerTheory

fun astk s = prim_mk_const{Thy="vyperAst",Name=s}
val Fixed_tm        = astk"Fixed"
val Dynamic_tm      = astk"Dynamic"
val UintT_tm        = astk"UintT"
val IntT_tm         = astk"IntT"
val BoolT_tm        = astk"BoolT"
val StringT_tm      = astk"StringT"
val AddressT_tm     = astk"AddressT"
val BaseT_tm        = astk"BaseT"
val ArrayT_tm       = astk"ArrayT"
val NoneT_tm        = astk"NoneT"
val BoolL_tm        = astk"BoolL"
val BytesL_tm       = astk"BytesL"
val IntL_tm         = astk"IntL"
val In_tm           = astk"In"
val NotIn_tm        = astk"NotIn"
val Eq_tm           = astk"Eq"
val NotEq_tm        = astk"NotEq"
val Sender_tm       = astk"Sender"
val Lt_tm           = astk"Lt"
val Gt_tm           = astk"Gt"
val Bop_tm          = astk"Bop"
val Msg_tm          = astk"Msg"
val IntCall_tm      = astk"IntCall"
val Name_tm         = astk"Name"
val Literal_tm      = astk"Literal"
val ArrayLit_tm     = astk"ArrayLit"
val Subscript_tm    = astk"Subscript"
val Attribute_tm    = astk"Attribute"
val Builtin_tm      = astk"Builtin"
val AstCall_tm      = astk"Call"
val Array_tm        = astk"Array"
val Range_tm        = astk"Range"
val Pass_tm         = astk"Pass"
val Expr_tm         = astk"Expr"
val For_tm          = astk"For"
val If_tm           = astk"If"
val Assert_tm       = astk"Assert"
val Return_tm       = astk"Return"
val AnnAssign_tm    = astk"AnnAssign"
val External_tm     = astk"External"
val Internal_tm     = astk"Internal"
val Deploy_tm       = astk"Deploy"
val Pure_tm         = astk"Pure"
val View_tm         = astk"View"
val Nonpayable_tm   = astk"Nonpayable"
val Payable_tm      = astk"Payable"
val Public_tm       = astk"Public"
val Private_tm      = astk"Private"
val Constant_tm     = astk"Constant"
val Immutable_tm    = astk"Immutable"
val Transient_tm    = astk"Transient"
val Storage_tm      = astk"Storage"
val FunctionDecl_tm = astk"FunctionDecl"
val VariableDecl_tm = astk"VariableDecl"

fun from_term_option ty = lift_option (mk_option ty) I

val address_bits_ty = mk_int_numeric_type 160
val address_ty = mk_word_type address_bits_ty
val mk_num_tm = numSyntax.mk_numeral o Arbnum.fromHexString
fun mk_address_tm hex = mk_n2w(mk_num_tm hex, address_bits_ty)

val byte_bits_ty = mk_int_numeric_type 8
val byte_ty = mk_word_type byte_bits_ty
val bytes_ty = mk_list_type byte_ty
fun mk_bytes_tms hex = let
  val hex = if String.isPrefix "0x" hex then String.extract(hex,2,NONE) else hex
  fun loop i a = if i = 0 then a else let
    val i = i - 1
    val y = String.sub(hex, i)
    val i = i - 1
    val x = String.sub(hex, i)
    val b = Arbnum.fromHexString (String.implode [x, y])
    val t = mk_n2w(numSyntax.mk_numeral b, byte_bits_ty)
  in loop i (t::a) end
in
  loop (String.size hex) []
end
fun mk_bytes_tm hex = mk_list(mk_bytes_tms hex, byte_ty)

val toplevel_ty = mk_thy_type{Thy="vyperAst",Tyop="toplevel",Args=[]}
val type_ty = mk_thy_type{Thy="vyperAst",Tyop="type",Args=[]}
val stmt_ty = mk_thy_type{Thy="vyperAst",Tyop="stmt",Args=[]}
val expr_ty = mk_thy_type{Thy="vyperAst",Tyop="expr",Args=[]}
val identifier_ty = string_ty
val argument_ty = pairSyntax.mk_prod(identifier_ty, type_ty)
val bool_tm = mk_comb(BaseT_tm, BoolT_tm)
val uint256_tm = mk_comb(BaseT_tm, mk_comb(UintT_tm, numSyntax.term_of_int 256))
val int128_tm = mk_comb(BaseT_tm, mk_comb(IntT_tm, numSyntax.term_of_int 128))
val address_tm = mk_comb(BaseT_tm, AddressT_tm)
fun mk_Fixed n = mk_comb(Fixed_tm, n)
fun mk_FunctionDecl v m n a t b = list_mk_comb(FunctionDecl_tm, [v,m,n,a,t,b])
fun mk_VariableDecl v m n t = list_mk_comb(VariableDecl_tm, [v,m,n,t])
fun mk_String n = mk_comb(BaseT_tm, mk_comb(StringT_tm, n))
fun mk_Expr e = mk_comb(Expr_tm, e)
fun mk_For s t i n b = list_mk_comb(For_tm, [s,t,i,n,b])
fun mk_Name s = mk_comb(Name_tm, fromMLstring s)
fun mk_IntCall s = mk_comb(IntCall_tm, s)
fun mk_Call ct args = list_mk_comb(AstCall_tm, [ct, mk_list (args, expr_ty)])
fun mk_Assert e s = list_mk_comb(Assert_tm, [e, s])
fun mk_Subscript e1 e2 = list_mk_comb(Subscript_tm, [e1, e2])
fun mk_If e s1 s2 = list_mk_comb(If_tm, [e,s1,s2])
fun mk_li i = mk_comb(Literal_tm, mk_comb(IntL_tm, i))
fun mk_lb b = mk_comb(Literal_tm, mk_comb(BoolL_tm, b))
fun mk_Return tmo = mk_comb(Return_tm, lift_option (mk_option expr_ty) I tmo)
fun mk_AnnAssign s t e = list_mk_comb(AnnAssign_tm, [s, t, e])
fun mk_Hex s = let
  val s = if String.isPrefix "0x" s then String.extract(s,2,NONE) else s
  val n = numSyntax.term_of_int $ String.size s div 2
  val b = mk_comb(Fixed_tm, n)
in
  mk_comb(Literal_tm,
    list_mk_comb(BytesL_tm, [b, mk_bytes_tm s]))
end
fun mk_Builtin b es = list_mk_comb(Builtin_tm, [b, es])
fun mk_Bop b = mk_comb(Bop_tm, b)
fun mk_ArrayLit ls = let
  val n = numSyntax.term_of_int $ List.length ls
  val b = mk_comb(Fixed_tm, n)
in
  list_mk_comb(ArrayLit_tm, [b, mk_list(ls, expr_ty)])
end
val msg_sender_tm = list_mk_comb(Builtin_tm, [
  mk_comb(Msg_tm, Sender_tm), mk_list([], expr_ty)])


val abi_type_ty = mk_thy_type{Args=[],Thy="contractABI",Tyop="abi_type"}
val abiBool_tm = prim_mk_const{Name="Bool",Thy="contractABI"}
val abiString_tm = prim_mk_const{Name="String",Thy="contractABI"}
val abiBytes_tm = prim_mk_const{Name="Bytes",Thy="contractABI"}
val abiUint_tm = prim_mk_const{Name="Uint",Thy="contractABI"}
val abiInt_tm = prim_mk_const{Name="Int",Thy="contractABI"}
val abiArray_tm = prim_mk_const{Name="Array",Thy="contractABI"}
val abiTuple_tm = prim_mk_const{Name="Tuple",Thy="contractABI"}
val abiAddress_tm = prim_mk_const{Name="Address",Thy="contractABI"}

fun skip_to_matching_paren ss = let
  fun skip_to_close i = let
    val c = Substring.sub(ss, i)
    val i = i+1
  in
    if c = #"]" then i else skip_to_close i
  end
  fun loop n i = let
    val c = Substring.sub(ss, i)
    val i = i+1
  in
    if c = #"(" then loop (n+1) i else
    if c = #")" then
      if n = 1
      then if i < Substring.size ss andalso
              Substring.sub(ss, i) = #"["
           then skip_to_close (i+1)
           else i
      else loop (n-1) i
    else loop n i
  end
in
  Substring.splitAt(ss, loop 0 0)
end

fun split_on_outer_commas ss = let
  val (x,ss) =
    (if Substring.sub(ss, 0) = #"("
     then skip_to_matching_paren
     else Substring.splitl (not o equal #",")) ss
in
  if Substring.size ss = 0 then [x]
  else x :: split_on_outer_commas (Substring.triml 1 ss)
end

fun parse_optnum ns =
  case Int.fromString (Substring.string ns)
    of SOME n => optionSyntax.mk_some (numSyntax.term_of_int n)
     | NONE => optionSyntax.mk_none numSyntax.num

fun parse_abi_type s =
  if String.isSuffix "]" s then let
    val ss = Substring.full s
    val (ps, ns) = Substring.splitr (not o equal #"[") ss
    val bt = parse_optnum ns
    val s = Substring.string (Substring.trimr 1 ps)
    val t = parse_abi_type s
  in list_mk_comb(abiArray_tm, [bt, t]) end
  else if String.isPrefix "(" s then let
    val ss = Substring.trimr 1 $ Substring.triml 1 $ Substring.full s
    val tss = split_on_outer_commas ss
    val s = Substring.string(el 2 tss)
    val ts = List.map (parse_abi_type o Substring.string) tss
    val ls = listSyntax.mk_list(ts, abi_type_ty)
  in mk_comb(abiTuple_tm, ls) end
  else if String.isPrefix "uint" s then let
    val ss = Substring.full s
    val ns = Substring.triml 4 ss
    val SOME n = Int.fromString (Substring.string ns)
    val nt = numSyntax.term_of_int n
  in mk_comb(abiUint_tm, nt) end
  else if String.isPrefix "int" s then let
    val ss = Substring.full s
    val ns = Substring.triml 3 ss
    val SOME n = Int.fromString (Substring.string ns)
    val nt = numSyntax.term_of_int n
  in mk_comb(abiInt_tm, nt) end
  else if String.isPrefix "bytes" s then let
    val ss = Substring.full s
    val ns = Substring.triml 5 ss
    val bt = parse_optnum ns
  in mk_comb(abiBytes_tm, bt) end
  (* TODO: Fixed, Ufixed *)
  else if s = "bool" then abiBool_tm
  else if s = "address" then abiAddress_tm
  else if s = "string" then abiString_tm
  else raise Fail s

fun check cd pred err d =
  andThen (fn x => if pred x then d else fail err) cd

fun check_field lab req =
  check (field lab string) (equal req) (lab ^ " not " ^ req)

fun check_trace_type req = check_field "trace_type" req

fun check_ast_type req = check_field "ast_type" req

val numtm = JSONDecode.map numSyntax.term_of_int int
val stringtm = JSONDecode.map fromMLstring string
val booltm = JSONDecode.map mk_bool bool
val negbooltm = JSONDecode.map (mk_bool o not) bool

val address : term decoder = JSONDecode.map mk_address_tm string
val bytes : term decoder = JSONDecode.map mk_bytes_tm string

val Call_tm = prim_mk_const{Thy="vyperTestRunner",Name="Call"}
val call_trace_ty = #1 $ dom_rng $ type_of Call_tm

val call : term decoder =
  check_trace_type "call" $
  andThen (fn (((s,c,v,g),(p,t,a)),e) => succeed $
              TypeBase.mk_record (call_trace_ty, [
                ("sender", s),
                ("target", t),
                ("callData", c),
                ("value", v),
                ("gasLimit", g),
                ("gasPrice", p),
                ("static", a),
                ("expectedOutput", e)]))
          (tuple2 (
            field "call_args" (tuple2 (
              tuple4 (field "sender" address,
                      field "calldata" bytes,
                      field "value" numtm,
                      field "gas" numtm),
              tuple3 (field "gas_price" numtm,
                      field "to" address,
                      field "is_modifying" negbooltm))),
            field "output" (JSONDecode.map (from_term_option bytes_ty) $
                            nullable bytes)))

fun achoose err ls = orElse(choose ls, fail err)

fun d_astType () : term decoder =
  achoose "astType" [
    check_ast_type "Name" $
    achoose "astType Name" [
      check_field "id" "uint256" $ succeed uint256_tm, (* TODO: handle arbitrary bit sizes *)
      check_field "id" "int128" $ succeed int128_tm,
      check_field "id" "bool" $ succeed bool_tm,
      check_field "id" "address" $ succeed address_tm
    ],
    check_ast_type "Subscript" $
    andThen (succeed o mk_String) $
    check (field "value" (check_ast_type "Name" $ field "id" string))
    (equal "String") "not a String" $
    field "slice" $
    check_ast_type "Int" $
    field "value" $ JSONDecode.map numSyntax.term_of_int int,
    check_ast_type "Subscript" $
    andThen (fn (t,b) => succeed $ list_mk_comb(ArrayT_tm, [t,b])) $
    tuple2 (
      field "value" (delay d_astType),
      field "slice" $
      check_ast_type "Int" $
      field "value" (JSONDecode.map (mk_Fixed o numSyntax.term_of_int) int)
    ),
    null NoneT_tm
  ]

val astType = delay d_astType

val arg : term decoder =
  check_ast_type "arg" $
  andThen (fn (n,ty) => succeed $ mk_pair(n,ty))
    (tuple2 (field "arg" stringtm,
             field "annotation" astType))

val args : term decoder =
  andThen (fn ls => succeed $ mk_list(ls, argument_ty))
    (array arg)

fun theoptstring NONE = "" | theoptstring (SOME s) = s

val binop : term decoder = achoose "binop" [
  check_ast_type "In" $ succeed In_tm,
  check_ast_type "NotIn" $ succeed NotIn_tm,
  check_ast_type "Eq" $ succeed Eq_tm,
  check_ast_type "NotEq" $ succeed NotEq_tm,
  check_ast_type "Lt" $ succeed Lt_tm,
  check_ast_type "Gt" $ succeed Gt_tm
]

fun d_expression () : term decoder = achoose "expr" [
    check_ast_type "Name" $
    field "id" (JSONDecode.map mk_Name string),
    check_ast_type "NameConstant" $
    field "value" (JSONDecode.map mk_lb booltm),
    check_ast_type "Int" $
    field "value" (JSONDecode.map (mk_li o intSyntax.term_of_int o Arbint.fromInt) int),
    check_ast_type "Hex" $
    field "value" (JSONDecode.map mk_Hex string),
    check_ast_type "Compare" $
    andThen (fn (l,b,r) => succeed $
      mk_Builtin (mk_Bop b) $
      mk_list ([l,r], expr_ty)
    ) $
    tuple3 (
      field "left" (delay d_expression),
      field "op" binop,
      field "right" (delay d_expression)
    ),
    check_ast_type "List" $
    andThen (succeed o mk_ArrayLit) $ (* TODO: also handle dynamic arrays *)
    field "elements" (array (delay d_expression)),
    check_ast_type "Subscript" $
    andThen (fn (e1,e2) => succeed $ mk_Subscript e1 e2) $
    tuple2 (field "value" (delay d_expression),
            field "slice" (delay d_expression)),
    check_ast_type "Attribute" $
    check (field "value" (tuple2 (field "ast_type" string,
                                  field "id" string)))
          (equal ("Name", "msg"))
          "Attribute not msg"
          (check (field "attr" string)
                 (equal "sender")
                 "not msg.sender"
                 (succeed msg_sender_tm)),
    check_ast_type "Call" $
    andThen (fn (i,a) => succeed $ mk_Call (mk_IntCall i) a) $
    tuple2 (
      field "func" (
        check_ast_type "Attribute" $
        check (field "value" (tuple2 (field "ast_type" string,
                                      field "id" string)))
              (equal ("Name", "self"))
              "non-internal Call"
              (field "attr" stringtm)),
      field "args" (array (delay d_expression))
    )
  ]
val expression = delay d_expression

(* TODO: support variable (expr) args with explicit bounds *)
fun rangeArgs ls = let
  val (s, e) = case ls of [x,y] => (x,y) | [x] => (0,x) | _ => (0,0)
  val b = e - s
  val [s,e] = List.map (intSyntax.term_of_int o Arbint.fromInt) [s,e]
  val t = list_mk_comb(Range_tm, [mk_li s, mk_li e])
in (t, numSyntax.term_of_int b) end

val iterator : (term * term) decoder = achoose "iterator" [
  check_ast_type "Call" $
  check (field "func" (field "id" string))
        (equal "range") "not range" $
  andThen (succeed o rangeArgs) $
  field "args" (array (check_ast_type "Int" (field "value" int)))
]

fun mk_statements ls = mk_list(ls, stmt_ty)
val d_statements = andThen (succeed o mk_statements) o array

fun d_statement () : term decoder = achoose "stmt" [
    check_ast_type "Pass" $ succeed Pass_tm,
    check_ast_type "Expr" $
    field "value" (JSONDecode.map mk_Expr expression),
    check_ast_type "For" $
    andThen (fn ((s,t),(i,n),b) => succeed $ mk_For s t i n b) $
    tuple3 (field "target" $
            check_ast_type "AnnAssign" $
            tuple2 (field "target" $
                    check_ast_type "Name" $
                    field "id" stringtm,
                    field "annotation" astType),
            field "iter" iterator,
            field "body" (d_statements (delay d_statement))),
    check_ast_type "If" $
    andThen (fn (e,s1,s2) => succeed $ mk_If e s1 s2) $
    tuple3 (field "test" expression,
            field "body" (d_statements (delay d_statement)),
            field "orelse" (d_statements (delay d_statement))),
    check_ast_type "Assert" $
    andThen (fn (e,s) => succeed $ mk_Assert e s)
      (tuple2 (field "test" expression,
               field "msg" $
                 orElse(check_ast_type "Str" (field "value" stringtm),
                        null emptystring_tm))),
    check_ast_type "Return" $
    field "value" (JSONDecode.map mk_Return (try expression)),
    check_ast_type "AnnAssign" $
    andThen (fn (s,t,e) => succeed $ mk_AnnAssign s t e) $
    tuple3 (
      field "target" (check_ast_type "Name" (field "id" stringtm)),
      field "annotation" astType,
      field "value" expression
    )
  ]

val statement = delay d_statement

val statements : term decoder = d_statements statement

val functionDef : term decoder =
  check_ast_type "FunctionDef" $
  andThen (fn ((decs, id, args),(ret,body)) => let
             val vis =
               if List.exists (equal "external") decs then External_tm else
               if List.exists (equal "deploy") decs then Deploy_tm else
               Internal_tm
             val mut =
               if List.exists (equal "pure") decs then Pure_tm else
               if List.exists (equal "view") decs then View_tm else
               if List.exists (equal "payable") decs then Payable_tm else
               Nonpayable_tm
             in
               succeed $ mk_FunctionDecl vis mut id args ret body
             end)
    (tuple2 (tuple3 (field "decorator_list" (array (field "id" string)),
                     field "name" stringtm,
                     field "args" (
                       check_ast_type "arguments" $
                       field "args" args)),
             tuple2 (field "returns" astType,
                     field "body" statements)))

val variableDecl : term decoder =
  check_ast_type "VariableDecl" $
  andThen (fn (vis,mut,id,typ) => succeed $
             mk_VariableDecl vis mut id typ) $
  tuple4 (
    field "is_public" (JSONDecode.map
      (fn b => if b then Public_tm else Private_tm) bool),
    andThen (fn (im,tr,con) => succeed (
      if im then Immutable_tm else
      if tr then Transient_tm else
      case con of SOME e => mk_comb(Constant_tm, e)
                | NONE => Storage_tm)) $
    tuple3 (
      field "is_immutable" bool,
      field "is_transient" bool,
      andThen (fn b => (if b then field "value" (JSONDecode.map SOME expression)
                        else succeed NONE)) (field "is_constant" bool)),
    field "target" (check_ast_type "Name" (field "id" stringtm)),
    field "annotation" astType)

val toplevel : term decoder = achoose "tl" [
    functionDef,
    variableDecl
  ]

(*
decode (field "decorator_list" (array (field "id" string))) obj
decode (field "name" stringtm) obj
decode (field "args" (
                     check_ast_type "arguments" $
                     field "args" args)) obj
decode (field "returns" astType) obj
decode (field "body" statements) obj
*)

val toplevels : term decoder =
  andThen (fn ls => succeed $ mk_list(ls, toplevel_ty))
    (array toplevel)

val abiType : term decoder =
  andThen (succeed o parse_abi_type) string

val abiArg : term decoder =
  andThen (succeed o mk_pair) $
  tuple2 (field "name" stringtm,
          field "type" abiType)

val abiMutability : term decoder =
  andThen (fn s =>
    if s = "nonpayable" then succeed Nonpayable_tm else
    if s = "view" then succeed View_tm else
    if s = "payable" then succeed Payable_tm else
    fail ("abiMutability: " ^ s)) string

val Function_tm = prim_mk_const{Thy="vyperTestRunner",Name="Function"}
val (abi_function_ty, abi_entry_ty) = dom_rng $ type_of $ Function_tm
val abi_arg_ty = mk_prod(string_ty, abi_type_ty)

val abiEntry : term decoder = achoose "abiEntry" [
    check_field "type" "function" $
    andThen (fn (n,is,os,m) => succeed $ mk_comb(Function_tm,
             TypeBase.mk_record (abi_function_ty, [
               ("name", n),
               ("inputs", mk_list(is, abi_arg_ty)),
               ("outputs", mk_list(os, abi_arg_ty)),
               ("mutability", m)])))
      (tuple4 (field "name" stringtm,
               field "inputs" (array abiArg),
               field "outputs" (array abiArg),
               field "stateMutability" abiMutability))
  ]

val Deployment_tm = prim_mk_const{Thy="vyperTestRunner",Name="Deployment"}
val deployment_trace_ty = #1 $ dom_rng $ type_of Deployment_tm

val deployment : term decoder =
  check_trace_type "deployment" $
  andThen (fn ((c,i,(s,a),(d,v)),e) => succeed $
             TypeBase.mk_record (deployment_trace_ty, [
               ("sourceAst", c),
               ("contractAbi", mk_list(i, abi_entry_ty)),
               ("deployedAddress", a),
               ("deployer", s),
               ("deploymentSuccess", e),
               ("value", v),
               ("callData", d)
             ]))
          (tuple2 (tuple4 (field "annotated_ast"
                             (field "ast" (field "body" toplevels)),
                           field "contract_abi" (array abiEntry),
                           tuple2 (field "deployer" address,
                                   field "deployed_address" address),
                           tuple2 (field "calldata" $
                                   JSONDecode.map (mk_bytes_tm o theoptstring)
                                     (nullable string),
                                   field "value" numtm)),
                   field "deployment_succeeded" booltm))

val trace : term decoder =
  orElse (JSONDecode.map (curry mk_comb Call_tm) call,
          JSONDecode.map (curry mk_comb Deployment_tm) deployment)

fun read_test_json json_path = let
  val test_jsons = decodeFile rawObject json_path
  val decoder = (check_field "item_type" "test" $
                 field "traces" (array trace))
  fun mapthis (name, json) = (name, decode decoder json)
in
  List.map mapthis test_jsons
end

val trace_ty = mk_thy_type{Thy="vyperTestRunner",Tyop="trace",Args=[]}
val run_test_tm = prim_mk_const{Thy="vyperTestRunner",Name="run_test"}

fun run_test (name, trtms) = let
  val trs = mk_list(trtms, trace_ty)
  val ttm = mk_comb(run_test_tm, trs)
  val () = Feedback.HOL_MESG ("Testing " ^ name)
  val eth = cv_eval ttm
  val result = if sumSyntax.is_inr $ rhs $ concl eth
               then "Failed"
               else "Passed"
in
  Feedback.HOL_MESG result
end

(*
  val json_path = "test_comparison.json"
  val tests = read_test_json json_path
  val () = List.app run_test tests

  val json_path = "test_assert.json"
  val tests = read_test_json json_path
  val () = List.app run_test tests

  val json_path = "test_conditionals.json"
  val tests = read_test_json json_path

  val test_jsons = decodeFile rawObject json_path
  val (name, json) = el 1 test_jsons
  val traces = decode (field "traces" (array trace)) json
  val traces = decode (field "traces" (array raw)) json
  val tr = el 1 traces
  decode (field "contract_abi" (array abiEntry)) tr
  val tr = decode trace tr
  val tls = decode (field "annotated_ast" (field "ast" (field "body" (array raw)))) tr
  val tl = el 1 tls
  val stmts = decode (field "body" statements) tl

  val stmts = decode (field "body" (array raw)) tl
  val stmt = el 1 stmts
  decode statement stmt
  val stmts = decode (field "body" (array raw)) stmt
  val stmt = el 1 stmts
  val expr = decode (field "test" raw) stmt
  decode (field "right" expression) expr
  decode expression expr

  decode (field "iter" (field "args" (array (field "value" int)))) stmt
  val ls = [3]

  val stmt = decode statement stmt
  val stmts = decode (field "body" (array raw)) stmt
  val stmt = el 1 stmts
  decode (field "value" expression) stmt

  val estmts = decode (field "orelse" (array raw)) (el 1 stmts)
  val estmt = el 1 estmts
  decode (statement) estmt

  val obj =
  (read_test_json json_path; JSON.NULL)
  handle JSONError (_, obj) => obj
*)

end
