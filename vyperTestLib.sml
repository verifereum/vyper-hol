structure vyperTestLib = struct

open HolKernel JSONDecode JSONUtil
     pairSyntax listSyntax stringSyntax optionSyntax intSyntax
     contractABITheory vyperAstTheory

val json_path = "test_export.py.json"
val test_jsons = decodeFile rawObject json_path
val (test_name, test_json) = el 1 test_jsons

type deployment = {
  sourceCode: term,
  abi: JSON.value, (* TODO: SML value or HOL term? *)
  deployedAddress: string,
  expectSuccess: bool,
  value: string
}

type call = {
  sender: string,
  callData: string,
  value: string,
  gasLimit: string,
  gasPrice: string,
  target: string,
  static: bool,
  expectedOutput: string option
}

fun check_field lab req d =
  andThen (fn x => if x <> req then fail (lab ^ " not " ^ req) else d)
    (field lab string)

fun check_trace_type req = check_field "trace_type" req

fun check_ast_type req = check_field "ast_type" req

val intAsString = JSONDecode.map Int.toString JSONDecode.int
val stringtm = JSONDecode.map fromMLstring string

val call : call decoder =
  check_trace_type "call" $
  andThen (fn (((s,c,v,g),(p,t,m)),e) => succeed {
              sender=s, callData=c, value=v, gasLimit=g,
              gasPrice=p, target=t, static=not m, expectedOutput=e})
          (tuple2 (
            field "call_args" (tuple2 (
              tuple4 (field "sender" string,
                      field "calldata" string,
                      field "value" intAsString,
                      field "gas" intAsString),
              tuple3 (field "gas_price" intAsString,
                      field "to" string,
                      field "is_modifying" bool))),
            field "output" (nullable string)))

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

val deployment : deployment decoder =
  check_trace_type "deployment" $
  andThen (fn ((c,i,a,v),e) => succeed {
             sourceCode=c, abi=i, deployedAddress=a,
             value=v, expectSuccess=e })
          (tuple2 (tuple4 (field "annotated_ast"
                             (field "ast" (field "body" toplevels)),
                           field "contract_abi" raw,
                           field "deployed_address" string,
                           field "value" intAsString),
                   field "deployment_succeeded" bool))

datatype trace =
    Deployment of deployment
  | Call of call

val trace : trace decoder =
  orElse (JSONDecode.map Call call,
          JSONDecode.map Deployment deployment)

val traces = decode (array trace) test_json

end
