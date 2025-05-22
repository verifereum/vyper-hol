structure vyperTestLib = struct

open HolKernel JSONDecode JSONUtil
     pairSyntax listSyntax stringSyntax optionSyntax
     intSyntax wordsSyntax fcpSyntax
     contractABITheory vyperAstTheory

type abi_function = {
  name: string,
  inputs: (string * term) list,
  outputs: (string * term) list,
  mutability: term
}

datatype abi_entry = Function of abi_function (* TODO others *)

type deployment = {
  sourceCode: term,
  abi: abi_entry list,
  deployedAddress: term,
  expectSuccess: bool,
  value: string
}

type call = {
  sender: term,
  callData: term,
  value: string,
  gasLimit: string,
  gasPrice: string,
  target: term,
  static: bool,
  expectedOutput: term option
}

fun check_field lab req d =
  andThen (fn x => if x <> req then fail (lab ^ " not " ^ req) else d)
    (field lab string)

fun check_trace_type req = check_field "trace_type" req

fun check_ast_type req = check_field "ast_type" req

val intAsString = JSONDecode.map Int.toString JSONDecode.int
val stringtm = JSONDecode.map fromMLstring string

val address_bits_ty = mk_int_numeric_type 160
val address_ty = mk_word_type address_bits_ty
val mk_num_tm = numSyntax.mk_numeral o Arbnum.fromHexString
fun mk_address_tm hex = mk_n2w(mk_num_tm hex, address_bits_ty)
val address : term decoder = JSONDecode.map mk_address_tm string

val byte_bits_ty = mk_int_numeric_type 8
val byte_ty = mk_word_type byte_bits_ty
val bytes_ty = mk_list_type byte_ty
fun mk_bytes_tms hex = let
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

val call : call decoder =
  check_trace_type "call" $
  andThen (fn (((s,c,v,g),(p,t,m)),e) => succeed {
              sender=s, callData=c, value=v, gasLimit=g,
              gasPrice=p, target=t, static=not m, expectedOutput=e})
          (tuple2 (
            field "call_args" (tuple2 (
              tuple4 (field "sender" address,
                      field "calldata" bytes,
                      field "value" intAsString,
                      field "gas" intAsString),
              tuple3 (field "gas_price" intAsString,
                      field "to" address,
                      field "is_modifying" bool))),
            field "output" (nullable bytes)))

val toplevel_ty = mk_thy_type{Thy="vyperAst",Tyop="toplevel",Args=[]}
val type_ty = mk_thy_type{Thy="vyperAst",Tyop="type",Args=[]}
val stmt_ty = mk_thy_type{Thy="vyperAst",Tyop="stmt",Args=[]}
val expr_ty = mk_thy_type{Thy="vyperAst",Tyop="expr",Args=[]}
val identifier_ty = string_ty
val argument_ty = pairSyntax.mk_prod(identifier_ty, type_ty)
val BaseT_tm = prim_mk_const{Name="BaseT",Thy="vyperAst"}
val BoolT_tm = prim_mk_const{Name="BoolT",Thy="vyperAst"}
val UintT_tm = prim_mk_const{Name="UintT",Thy="vyperAst"}
val bool_tm = mk_comb(BaseT_tm, BoolT_tm)
val uint256_tm = mk_comb(BaseT_tm, mk_comb(UintT_tm, numSyntax.term_of_int 256))
val FunctionDecl_tm = prim_mk_const{Name="FunctionDecl",Thy="vyperAst"}
val External_tm = prim_mk_const{Name="External",Thy="vyperAst"}
val Internal_tm = prim_mk_const{Name="Internal",Thy="vyperAst"}
val Deploy_tm = prim_mk_const{Name="Deploy",Thy="vyperAst"}
val Pure_tm = prim_mk_const{Name="Pure",Thy="vyperAst"}
val View_tm = prim_mk_const{Name="View",Thy="vyperAst"}
val Nonpayable_tm = prim_mk_const{Name="Nonpayable",Thy="vyperAst"}
val Payable_tm = prim_mk_const{Name="Payable",Thy="vyperAst"}
fun mk_FunctionDecl v m n a t b = list_mk_comb(FunctionDecl_tm, [v,m,n,a,t,b])
val Pass_tm = prim_mk_const{Name="Pass",Thy="vyperAst"}
val Assert_tm = prim_mk_const{Name="Assert",Thy="vyperAst"}
val Name_tm = prim_mk_const{Name="Name",Thy="vyperAst"}
val Return_tm = prim_mk_const{Name="Return",Thy="vyperAst"}
val Literal_tm = prim_mk_const{Name="Literal",Thy="vyperAst"}
val IntL_tm = prim_mk_const{Name="IntL",Thy="vyperAst"}
fun mk_Name s = mk_comb(Name_tm, fromMLstring s)
fun mk_Assert e s = list_mk_comb(Assert_tm, [e, fromMLstring s])
fun mk_li i = mk_comb(Literal_tm, mk_comb(IntL_tm, intSyntax.term_of_int i))
fun mk_Return tmo = mk_comb(Return_tm, lift_option (mk_option expr_ty) I tmo)

val abiBool_tm = prim_mk_const{Name="Bool",Thy="contractABI"}
val abiUint_tm = prim_mk_const{Name="Uint",Thy="contractABI"}
val abiUint256_tm = mk_comb(abiUint_tm, numSyntax.term_of_int 256)

val astType : term decoder = choose [
    check_field "id" "uint256" $ succeed uint256_tm,
    check_field "id" "bool" $ succeed bool_tm
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

val expression : term decoder = choose [
    check_ast_type "Name" $
    field "id" (JSONDecode.map mk_Name string),
    check_ast_type "Int" $
    field "value" (JSONDecode.map (mk_li o Arbint.fromInt) int)
  ]

val statement : term decoder = choose [
    check_ast_type "Pass" $ succeed Pass_tm,
    check_ast_type "Assert" $
    andThen (fn (e,s) => succeed $ mk_Assert e s)
      (tuple2 (field "test" expression,
               field "msg" (JSONDecode.map theoptstring (nullable string)))),
    check_ast_type "Return" $
    field "value" (JSONDecode.map mk_Return (try expression))
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

val toplevel : term decoder = choose [
    functionDef
  ]

val toplevels : term decoder =
  andThen (fn ls => succeed $ mk_list(ls, toplevel_ty))
    (array toplevel)

val abiType : term decoder =
  andThen (fn s =>
    if s = "bool" then succeed abiBool_tm else
    if s = "uint256" then succeed abiUint256_tm else
    fail ("abiType: " ^ s)) string

val abiArg : (string * term) decoder =
  tuple2 (field "name" string,
          field "type" abiType)

val abiMutability : term decoder =
  andThen (fn s =>
    if s = "nonpayable" then succeed Nonpayable_tm else
    fail ("abiMutability: " ^ s)) string

val abi : abi_entry decoder = choose [
    check_field "type" "function" $
    andThen (fn (n,is,os,m) => succeed $ Function
               {name=n, inputs=is, outputs=os, mutability=m})
      (tuple4 (field "name" string,
               field "inputs" (array abiArg),
               field "outputs" (array abiArg),
               field "stateMutability" abiMutability))
  ]

val deployment : deployment decoder =
  check_trace_type "deployment" $
  andThen (fn ((c,i,a,v),e) => succeed {
             sourceCode=c, abi=i, deployedAddress=a,
             value=v, expectSuccess=e })
          (tuple2 (tuple4 (field "annotated_ast"
                             (field "ast" (field "body" toplevels)),
                           field "contract_abi" (array abi),
                           field "deployed_address" address,
                           field "value" intAsString),
                   field "deployment_succeeded" bool))

datatype trace =
    Deployment of deployment
  | Call of call

val trace : trace decoder =
  orElse (JSONDecode.map Call call,
          JSONDecode.map Deployment deployment)

fun read_test_json json_path = let
  val test_jsons = decodeFile rawObject json_path
  fun mapthis (name, json) = (name, decode (array trace) json)
in
  List.map mapthis test_jsons
end

end
