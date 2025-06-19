structure vyperTestLib :> vyperTestLib = struct

open HolKernel JSONDecode JSONUtil cv_transLib wordsLib
     pairSyntax listSyntax stringSyntax optionSyntax
     intSyntax wordsSyntax fcpSyntax
     vyperAbiTheory vyperAstTheory vyperTestRunnerTheory

fun check_field lab req d =
  andThen (fn x => if x <> req then fail (lab ^ " not " ^ req) else d)
    (field lab string)

fun check_trace_type req = check_field "trace_type" req

fun check_ast_type req = check_field "ast_type" req

val numtm = JSONDecode.map numSyntax.term_of_int int
val stringtm = JSONDecode.map fromMLstring string
val booltm = JSONDecode.map mk_bool bool
val negbooltm = JSONDecode.map (mk_bool o not) bool

fun from_term_option ty = lift_option (mk_option ty) I

val address_bits_ty = mk_int_numeric_type 160
val address_ty = mk_word_type address_bits_ty
val mk_num_tm = numSyntax.mk_numeral o Arbnum.fromHexString
fun mk_address_tm hex = mk_n2w(mk_num_tm hex, address_bits_ty)
val address : term decoder = JSONDecode.map mk_address_tm string

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

val toplevel_ty = mk_thy_type{Thy="vyperAst",Tyop="toplevel",Args=[]}
val type_ty = mk_thy_type{Thy="vyperAst",Tyop="type",Args=[]}
val stmt_ty = mk_thy_type{Thy="vyperAst",Tyop="stmt",Args=[]}
val expr_ty = mk_thy_type{Thy="vyperAst",Tyop="expr",Args=[]}
val identifier_ty = string_ty
val argument_ty = pairSyntax.mk_prod(identifier_ty, type_ty)
val BaseT_tm = prim_mk_const{Name="BaseT",Thy="vyperAst"}
val BoolT_tm = prim_mk_const{Name="BoolT",Thy="vyperAst"}
val UintT_tm = prim_mk_const{Name="UintT",Thy="vyperAst"}
val NoneT_tm = prim_mk_const{Name="NoneT",Thy="vyperAst"}
val AddressT_tm = prim_mk_const{Name="AddressT",Thy="vyperAst"}
val bool_tm = mk_comb(BaseT_tm, BoolT_tm)
val uint256_tm = mk_comb(BaseT_tm, mk_comb(UintT_tm, numSyntax.term_of_int 256))
val address_tm = mk_comb(BaseT_tm, AddressT_tm)
val FunctionDecl_tm = prim_mk_const{Name="FunctionDecl",Thy="vyperAst"}
val VariableDecl_tm = prim_mk_const{Name="VariableDecl",Thy="vyperAst"}
val Public_tm = prim_mk_const{Name="Public",Thy="vyperAst"}
val Private_tm = prim_mk_const{Name="Private",Thy="vyperAst"}
val Immutable_tm = prim_mk_const{Name="Immutable",Thy="vyperAst"}
val Transient_tm = prim_mk_const{Name="Transient",Thy="vyperAst"}
val Storage_tm = prim_mk_const{Name="Storage",Thy="vyperAst"}
val Constant_tm = prim_mk_const{Name="Constant",Thy="vyperAst"}
val External_tm = prim_mk_const{Name="External",Thy="vyperAst"}
val Internal_tm = prim_mk_const{Name="Internal",Thy="vyperAst"}
val Deploy_tm = prim_mk_const{Name="Deploy",Thy="vyperAst"}
val Pure_tm = prim_mk_const{Name="Pure",Thy="vyperAst"}
val View_tm = prim_mk_const{Name="View",Thy="vyperAst"}
val Nonpayable_tm = prim_mk_const{Name="Nonpayable",Thy="vyperAst"}
val Payable_tm = prim_mk_const{Name="Payable",Thy="vyperAst"}
fun mk_FunctionDecl v m n a t b = list_mk_comb(FunctionDecl_tm, [v,m,n,a,t,b])
fun mk_VariableDecl v m n t = list_mk_comb(VariableDecl_tm, [v,m,n,t])
val Pass_tm = prim_mk_const{Name="Pass",Thy="vyperAst"}
val Assert_tm = prim_mk_const{Name="Assert",Thy="vyperAst"}
val AnnAssign_tm = prim_mk_const{Name="AnnAssign",Thy="vyperAst"}
val Name_tm = prim_mk_const{Name="Name",Thy="vyperAst"}
val Return_tm = prim_mk_const{Name="Return",Thy="vyperAst"}
val Literal_tm = prim_mk_const{Name="Literal",Thy="vyperAst"}
val Builtin_tm = prim_mk_const{Name="Builtin",Thy="vyperAst"}
val Bop_tm = prim_mk_const{Name="Bop",Thy="vyperAst"}
val In_tm = prim_mk_const{Name="In",Thy="vyperAst"}
val IntL_tm = prim_mk_const{Name="IntL",Thy="vyperAst"}
val Fixed_tm = prim_mk_const{Name="Fixed",Thy="vyperAst"}
val BytesL_tm = prim_mk_const{Name="BytesL",Thy="vyperAst"}
val ArrayLit_tm = prim_mk_const{Name="ArrayLit",Thy="vyperAst"}
fun mk_Name s = mk_comb(Name_tm, fromMLstring s)
fun mk_Assert e s = list_mk_comb(Assert_tm, [e, s])
fun mk_li i = mk_comb(Literal_tm, mk_comb(IntL_tm, intSyntax.term_of_int i))
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

val abiBool_tm = prim_mk_const{Name="Bool",Thy="contractABI"}
val abiUint_tm = prim_mk_const{Name="Uint",Thy="contractABI"}
val abiUint256_tm = mk_comb(abiUint_tm, numSyntax.term_of_int 256)
val abiAddress_tm = prim_mk_const{Name="Address",Thy="contractABI"}

fun achoose err ls = orElse(choose ls, fail err)

val astType : term decoder = achoose "astType" [
    check_field "id" "uint256" $ succeed uint256_tm,
    check_field "id" "bool" $ succeed bool_tm,
    check_field "id" "address" $ succeed address_tm,
    null NoneT_tm
  ]

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
  check_ast_type "In" $ succeed In_tm
]

fun d_expression () : term decoder = achoose "expr" [
    check_ast_type "Name" $
    field "id" (JSONDecode.map mk_Name string),
    check_ast_type "Int" $
    field "value" (JSONDecode.map (mk_li o Arbint.fromInt) int),
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
    field "elements" (array (delay d_expression))
  ]
val expression = delay d_expression

val statement : term decoder = achoose "stmt" [
    check_ast_type "Pass" $ succeed Pass_tm,
    check_ast_type "Assert" $
    andThen (fn (e,s) => succeed $ mk_Assert e s)
      (tuple2 (field "test" expression,
               field "msg" (check_ast_type "Str" (field "value" stringtm)))),
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

val statements : term decoder =
  andThen (fn ls => succeed $ mk_list(ls, stmt_ty)) (array statement)

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
  andThen (fn s =>
    if s = "bool" then succeed abiBool_tm else
    if s = "uint256" then succeed abiUint256_tm else
    if s = "address" then succeed abiAddress_tm else
    fail ("abiType: " ^ s)) string

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
val abi_type_ty = mk_thy_type{Args=[],Thy="contractABI",Tyop="abi_type"}
val abi_arg_ty = mk_prod(string_ty, abi_type_ty)

val abiEntry : term decoder = choose [
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

  (*
  val obj =
  (read_test_json json_path; JSON.NULL)
  handle JSONError (_, obj) => obj
  *)

  val tests = read_test_json json_path
  val (name, trtms) = el 1 tests

  List.app run_test tests
*)

end
