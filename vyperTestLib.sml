structure vyperTestLib :> vyperTestLib = struct

open HolKernel boolLib JSONDecode JSONUtil cv_transLib wordsLib
     pairSyntax listSyntax stringSyntax optionSyntax
     intSyntax wordsSyntax fcpSyntax
     vfmTypesSyntax byteStringCacheLib
     vyperABITheory vyperAstTheory vyperTestRunnerTheory
     local open Timeout in end

val export_theory_no_docs = fn () =>
  Feedback.set_trace "TheoryPP.include_docs" 0
  before export_theory ()

fun astk s = prim_mk_const{Thy="vyperAst",Name=s}
val Fixed_tm        = astk"Fixed"
val Dynamic_tm      = astk"Dynamic"
val UintT_tm        = astk"UintT"
val IntT_tm         = astk"IntT"
val BoolT_tm        = astk"BoolT"
val DecimalT_tm     = astk"DecimalT"
val StringT_tm      = astk"StringT"
val BytesT_tm       = astk"BytesT"
val AddressT_tm     = astk"AddressT"
val BaseT_tm        = astk"BaseT"
val TupleT_tm       = astk"TupleT"
val ArrayT_tm       = astk"ArrayT"
val StructT_tm      = astk"StructT"
val FlagT_tm        = astk"FlagT"
val NoneT_tm        = astk"NoneT"
val Signed_tm       = astk"Signed"
val Unsigned_tm     = astk"Unsigned"
val BoolL_tm        = astk"BoolL"
val StringL_tm      = astk"StringL"
val BytesL_tm       = astk"BytesL"
val IntL_tm         = astk"IntL"
val DecimalL_tm     = astk"DecimalL"
val Add_tm          = astk"Add"
val Sub_tm          = astk"Sub"
val Mul_tm          = astk"Mul"
val Div_tm          = astk"Div"
val Mod_tm          = astk"Mod"
val Exp_tm          = astk"Exp"
val And_tm          = astk"And"
val Or_tm           = astk"Or"
val XOr_tm          = astk"XOr"
val ShL_tm          = astk"ShL"
val ShR_tm          = astk"ShR"
val In_tm           = astk"In"
val NotIn_tm        = astk"NotIn"
val Eq_tm           = astk"Eq"
val NotEq_tm        = astk"NotEq"
val Lt_tm           = astk"Lt"
val LtE_tm          = astk"LtE"
val Gt_tm           = astk"Gt"
val GtE_tm          = astk"GtE"
val Sender_tm       = astk"Sender"
val SelfAddr_tm     = astk"SelfAddr"
val TimeStamp_tm    = astk"TimeStamp"
val Address_tm      = astk"Address"
val Balance_tm      = astk"Balance"
val Len_tm          = astk"Len"
val Not_tm          = astk"Not"
val Neg_tm          = astk"Neg"
val Keccak256_tm    = astk"Keccak256"
val Concat_tm       = astk"Concat"
val Slice_tm        = astk"Slice"
val MakeArray_tm    = astk"MakeArray"
val Floor_tm        = astk"Floor"
val Bop_tm          = astk"Bop"
val Env_tm          = astk"Env"
val Acc_tm          = astk"Acc"
val IntCall_tm      = astk"IntCall"
val Empty_tm        = astk"Empty"
val MaxValue_tm     = astk"MaxValue"
val MinValue_tm     = astk"MinValue"
val Epsilon_tm      = astk"Epsilon"
val Convert_tm      = astk"Convert"
val Name_tm         = astk"Name"
val TopLevelName_tm = astk"TopLevelName"
val IfExp_tm        = astk"IfExp"
val Literal_tm      = astk"Literal"
val StructLit_tm    = astk"StructLit"
val Subscript_tm    = astk"Subscript"
val Attribute_tm    = astk"Attribute"
val Builtin_tm      = astk"Builtin"
val TypeBuiltin_tm  = astk"TypeBuiltin"
val Pop_tm          = astk"Pop"
val AstCall_tm      = astk"Call"
val NameTarget_tm         = astk"NameTarget"
val TopLevelNameTarget_tm = astk"TopLevelNameTarget"
val SubscriptTarget_tm    = astk"SubscriptTarget"
val AttributeTarget_tm    = astk"AttributeTarget"
val BaseTarget_tm   = astk"BaseTarget"
val TupleTarget_tm  = astk"TupleTarget"
val Array_tm        = astk"Array"
val Range_tm        = astk"Range"
val Pass_tm         = astk"Pass"
val Continue_tm     = astk"Continue"
val Break_tm        = astk"Break"
val Expr_tm         = astk"Expr"
val For_tm          = astk"For"
val If_tm           = astk"If"
val Assert_tm       = astk"Assert"
val Log_tm          = astk"Log"
val Raise_tm        = astk"Raise"
val Return_tm       = astk"Return"
val Assign_tm       = astk"Assign"
val AugAssign_tm    = astk"AugAssign"
val Append_tm       = astk"Append"
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
val Type_tm         = astk"Type"
val HashMapT_tm     = astk"HashMapT"
val FunctionDecl_tm = astk"FunctionDecl"
val VariableDecl_tm = astk"VariableDecl"
val HashMapDecl_tm  = astk"HashMapDecl"
val StructDecl_tm   = astk"StructDecl"
val EventDecl_tm    = astk"EventDecl"
val FlagDecl_tm     = astk"FlagDecl"

fun from_term_option ty = lift_option (mk_option ty) I

val toplevel_ty = mk_thy_type{Thy="vyperAst",Tyop="toplevel",Args=[]}
val type_ty = mk_thy_type{Thy="vyperAst",Tyop="type",Args=[]}
val stmt_ty = mk_thy_type{Thy="vyperAst",Tyop="stmt",Args=[]}
val expr_ty = mk_thy_type{Thy="vyperAst",Tyop="expr",Args=[]}
val identifier_ty = string_ty
val argument_ty = pairSyntax.mk_prod(identifier_ty, type_ty)
val bool_tm = mk_comb(BaseT_tm, BoolT_tm)
val address_tm = mk_comb(BaseT_tm, AddressT_tm)
val decimal_tm = mk_comb(BaseT_tm, DecimalT_tm)
fun mk_Fixed n = mk_comb(Fixed_tm, n)
fun mk_Dynamic n = mk_comb(Dynamic_tm, n)
fun mk_Signed n = mk_comb(Signed_tm, n)
fun mk_Unsigned n = mk_comb(Unsigned_tm, n)
fun mk_uint n = mk_comb(BaseT_tm, mk_comb(UintT_tm, n))
fun mk_int n = mk_comb(BaseT_tm, mk_comb(IntT_tm, n))
fun mk_bytes n = mk_comb(BaseT_tm, mk_comb(BytesT_tm, mk_Fixed n))
fun mk_FunctionDecl v m n a t b = list_mk_comb(FunctionDecl_tm, [v,m,n,a,t,b])
fun mk_VariableDecl (v,m,n,t) = list_mk_comb(VariableDecl_tm, [v,m,n,t])
fun mk_HashMapDecl (v,bt,n,t,vt) = list_mk_comb(HashMapDecl_tm, [v,bt,n,t,vt])
fun mk_String n = mk_comb(BaseT_tm, mk_comb(StringT_tm, n))
fun mk_Bytes n = mk_comb(BaseT_tm, mk_comb(BytesT_tm, mk_Dynamic n))
fun mk_BytesM n = mk_comb(BaseT_tm, mk_comb(BytesT_tm, mk_Fixed n))
fun mk_Expr e = mk_comb(Expr_tm, e)
fun mk_For s t i n b = list_mk_comb(For_tm, [s,t,i,n,b])
fun mk_Name s = mk_comb(Name_tm, fromMLstring s)
fun mk_StructLit (s,ls) = list_mk_comb(StructLit_tm, [
  s, mk_list(ls, mk_prod(string_ty, expr_ty))])
fun mk_IfExp (e1,e2,e3) = list_mk_comb(IfExp_tm, [e1,e2,e3])
fun mk_IntCall s = mk_comb(IntCall_tm, s)
fun mk_Empty t = list_mk_comb(TypeBuiltin_tm, [
  Empty_tm, t, mk_list([], expr_ty)])
fun mk_MaxValue t = list_mk_comb(TypeBuiltin_tm, [
  MaxValue_tm, t, mk_list([], expr_ty)])
fun mk_MinValue t = list_mk_comb(TypeBuiltin_tm, [
  MinValue_tm, t, mk_list([], expr_ty)])
fun mk_Convert (t,v) = list_mk_comb(TypeBuiltin_tm, [
  Convert_tm, t, mk_list([v], expr_ty)])
fun mk_Call ct args = list_mk_comb(AstCall_tm, [ct, mk_list (args, expr_ty)])
fun mk_Assert (e,s) = list_mk_comb(Assert_tm, [e, s])
fun mk_Log (id,es) = list_mk_comb(Log_tm, [id, es])
fun mk_Subscript e1 e2 = list_mk_comb(Subscript_tm, [e1, e2])
fun mk_If e s1 s2 = list_mk_comb(If_tm, [e,s1,s2])
fun mk_li (b,i) = mk_comb(Literal_tm, list_mk_comb(IntL_tm, [b,i]))
fun mk_ld i = mk_comb(Literal_tm, mk_comb(DecimalL_tm, i))
fun mk_lb b = mk_comb(Literal_tm, mk_comb(BoolL_tm, b))
fun mk_ls (n,s) = mk_comb(Literal_tm,
  list_mk_comb(StringL_tm, [n, stringSyntax.fromMLstring s]))
val empty_lstr = mk_ls(numSyntax.zero_tm, "")
fun mk_Return tmo = mk_comb(Return_tm, lift_option (mk_option expr_ty) I tmo)
fun mk_AnnAssign (s,t,e) = list_mk_comb(AnnAssign_tm, [s, t, e])
fun mk_AugAssign t b e = list_mk_comb(AugAssign_tm, [t, b, e])
fun mk_Hex_dyn (n, s) = let
  val s = if String.isPrefix "0x" s then String.extract(s,2,NONE) else s
  val b = mk_comb(Dynamic_tm, n)
in
  mk_comb(Literal_tm,
    list_mk_comb(BytesL_tm, [b, cached_bytes_from_hex s]))
end
fun mk_Hex s = let
  val s = if String.isPrefix "0x" s then String.extract(s,2,NONE) else s
  val n = numSyntax.term_of_int $ String.size s div 2
  val b = mk_comb(Fixed_tm, n)
in
  mk_comb(Literal_tm,
    list_mk_comb(BytesL_tm, [b, cached_bytes_from_hex s]))
end
fun mk_Builtin b es = list_mk_comb(Builtin_tm, [b, es])
fun mk_Concat n = mk_comb(Concat_tm, n)
fun mk_Slice n = mk_comb(Slice_tm, n)
fun mk_Not t = mk_Builtin Not_tm (mk_list([t], expr_ty))
fun mk_Neg t = mk_Builtin Neg_tm (mk_list([t], expr_ty))
fun mk_Keccak256 t = mk_Builtin Keccak256_tm (mk_list([t], expr_ty))
fun mk_Floor e = mk_Builtin Floor_tm (mk_list([e], expr_ty))
fun mk_Bop b = mk_comb(Bop_tm, b)
fun mk_Len e = mk_Builtin Len_tm (mk_list([e], expr_ty))
fun mk_MakeArray (to,b,ls) =
  mk_Builtin (list_mk_comb(MakeArray_tm, [to,b]))
    (mk_list (ls, expr_ty))
fun mk_Tuple ls = let
  val n = numSyntax.term_of_int $ List.length ls
  val b = mk_comb(Fixed_tm, n)
in
  mk_MakeArray (optionSyntax.mk_none type_ty, b, ls)
end
fun mk_SArray (t,ls) = let
  val n = numSyntax.term_of_int $ List.length ls
  val b = mk_comb(Fixed_tm, n)
in
  mk_MakeArray (optionSyntax.mk_some t, b, ls)
end
val msg_sender_tm = list_mk_comb(Builtin_tm, [
  mk_comb(Env_tm, Sender_tm), mk_list([], expr_ty)])
val self_addr_tm = list_mk_comb(Builtin_tm, [
  mk_comb(Env_tm, SelfAddr_tm), mk_list([], expr_ty)])
val timestamp_tm = list_mk_comb(Builtin_tm, [
  mk_comb(Env_tm, TimeStamp_tm), mk_list([], expr_ty)])
(*
val msg_gas_tm = list_mk_comb(Builtin_tm, [
  mk_comb(Env_tm, Gas_tm), mk_list([], expr_ty)])
*)

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
  else raise Fail ("parse_abi_type: " ^ s)

fun check cd pred err d =
  andThen cd (fn x => if pred x then d else fail err)

fun check_field lab req =
  check (field lab string) (equal req) (lab ^ " not " ^ req)

fun check_trace_type req = check_field "trace_type" req

fun check_ast_type req = check_field "ast_type" req

val numOfLargeInt =
  intSyntax.dest_injected o
  intSyntax.term_of_int o
  Arbint.fromLargeInt

val numtm = JSONDecode.map numOfLargeInt intInf
val stringtm = JSONDecode.map fromMLstring string
val booltm = JSONDecode.map mk_bool bool
val negbooltm = JSONDecode.map (mk_bool o not) bool

val address : term decoder = JSONDecode.map address_from_hex string
val bytes : term decoder = JSONDecode.map cached_bytes_from_hex string

val Call_tm = prim_mk_const{Thy="vyperTestRunner",Name="Call"}
val call_trace_ty = #1 $ dom_rng $ type_of Call_tm

val call : term decoder =
  check_trace_type "call" $
  JSONDecode.map (fn ((a,c,v,t),(p,g,s),(m,e)) =>
              TypeBase.mk_record (call_trace_ty, [
                ("sender", s),
                ("target", t),
                ("callData", c),
                ("value", v),
                ("timeStamp", m),
                ("gasLimit", g),
                ("gasPrice", p),
                ("static", a),
                ("expectedOutput", e)]))
          (tuple3 (
            field "call_args" $
              tuple4 (field "is_modifying" negbooltm,
                      field "calldata" bytes,
                      field "value" numtm,
                      field "to" address),
            field "env" $ field "tx" $
              tuple3 (field "gas_price" numtm,
                      field "gas" numtm,
                      field "origin" address),
            tuple2 (
              field "env" $ field "block" $ field "timestamp" numtm,
              field "output" (JSONDecode.map (from_term_option bytes_ty) $
                              nullable bytes))))

fun achoose err ls = orElse(choose ls, fail err)

fun triml n s = String.extract(s,n,NONE)
val stringToNumTm =
  numSyntax.term_of_int o
  Option.valOf o Int.fromString

fun d_astType () : term decoder =
  achoose "astType" [
    check_ast_type "Name" $
    achoose "astType Name" [
      check (field "id" string) (String.isPrefix "uint") "not uint" $
        JSONDecode.map (mk_uint o stringToNumTm o triml 4) $
        field "id" string,
      check (field "id" string) (String.isPrefix "int") "not int" $
        JSONDecode.map (mk_int o stringToNumTm o triml 3) $
        field "id" string,
      check (field "id" string) (String.isPrefix "bytes") "not bytes" $
        JSONDecode.map (mk_bytes o stringToNumTm o triml 5) $
        field "id" string,
      check_field "id" "bool" $ succeed bool_tm,
      check_field "id" "address" $ succeed address_tm,
      check_field "id" "decimal" $ succeed decimal_tm,
      JSONDecode.map (curry mk_comb StructT_tm) $
        field "id" stringtm
    ],
    check_ast_type "Subscript" $
      JSONDecode.map mk_String $
      check (field "value" (check_ast_type "Name" $ field "id" string))
            (equal "String") "not a String" $
      field "slice" $
        check_ast_type "Int" $
        field "value" numtm,
    check_ast_type "Subscript" $
      JSONDecode.map mk_Bytes $
      check (field "value" (check_ast_type "Name" $ field "id" string))
            (equal "Bytes") "not a Bytes" $
      field "slice" $
        check_ast_type "Int" $
        field "value" numtm,
    check_ast_type "Subscript" $
      JSONDecode.map (fn (t,b) => list_mk_comb(ArrayT_tm, [t,b])) $
      check (field "value" (check_ast_type "Name" $ field "id" string))
            (equal "DynArray") "not a DynArray" $
      field "slice" $
      check_ast_type "Tuple" $
      field "elements" $
      tuple2 (
        JSONDecode.sub 0 (delay d_astType),
        JSONDecode.sub 1 $ achoose "DynArray slice"
        let val di = check_ast_type "Int" $
                     field "value" $
                     JSONDecode.map mk_Dynamic numtm in
          [di, field "folded_value" di]
        end
      ),
    check_ast_type "Subscript" $
      JSONDecode.map (fn (t,b) => list_mk_comb(ArrayT_tm, [t,b])) $
      tuple2 (
        field "value" (delay d_astType),
        field "slice" $
        achoose "Array slice"
        let val di = check_ast_type "Int" $
                     field "value" $
                     JSONDecode.map mk_Fixed numtm in
          [di, field "folded_value" di]
        end
      ),
    check_ast_type "Tuple" $
    JSONDecode.map (curry mk_comb TupleT_tm) $
      field "elements" $
      JSONDecode.map (fn ls => mk_list(ls, type_ty)) $
        array (delay d_astType),
    check_ast_type "Call" $
      check (field "func" (tuple2 (field "ast_type" string,
                                   field "id" string)))
            (equal ("Name", "indexed"))
            "not indexed" $
      field "args" $
      JSONDecode.sub 0 (delay d_astType),
    null NoneT_tm
  ]

val astType = delay d_astType

fun theoptstring NONE = "" | theoptstring (SOME s) = s

val binop : term decoder = achoose "binop" [
  check_ast_type "Add" $ succeed Add_tm,
  check_ast_type "Sub" $ succeed Sub_tm,
  check_ast_type "Mult" $ succeed Mul_tm,
  check_ast_type "FloorDiv" $ succeed Div_tm,
  check_ast_type "Div" $ succeed Div_tm,
  check_ast_type "Mod" $ succeed Mod_tm,
  check_ast_type "Pow" $ succeed Exp_tm,
  check_ast_type "And" $ succeed And_tm,
  check_ast_type "BitAnd" $ succeed And_tm,
  check_ast_type "Or" $ succeed Or_tm,
  check_ast_type "BitOr" $ succeed Or_tm,
  check_ast_type "BitXor" $ succeed XOr_tm,
  check_ast_type "LShift" $ succeed ShL_tm,
  check_ast_type "RShift" $ succeed ShR_tm,
  check_ast_type "In" $ succeed In_tm,
  check_ast_type "NotIn" $ succeed NotIn_tm,
  check_ast_type "Eq" $ succeed Eq_tm,
  check_ast_type "NotEq" $ succeed NotEq_tm,
  check_ast_type "Lt" $ succeed Lt_tm,
  check_ast_type "LtE" $ succeed LtE_tm,
  check_ast_type "Gt" $ succeed Gt_tm,
  check_ast_type "GtE" $ succeed GtE_tm
]

fun mk_BoolOp ("And", []) = mk_lb T
  | mk_BoolOp ("And", [e]) = e
  | mk_BoolOp ("And", e::es) = mk_IfExp (e, mk_BoolOp ("And", es), mk_lb F)
  | mk_BoolOp ("Or", []) = mk_lb F
  | mk_BoolOp ("Or", [e]) = e
  | mk_BoolOp ("Or", e::es) = mk_IfExp (e, mk_lb T, mk_BoolOp ("Or", es))

fun mk_BinOp (l,b,r) =
  mk_Builtin (mk_Bop b) $
  mk_list ([l,r], expr_ty)

fun parseDecimal s = let
  val ss = Substring.full s
  val (bd,dd) = Substring.splitl(not o equal #".") ss
  val ad = Substring.triml 1 dd
  val ad = StringCvt.padRight #"0" 10 (Substring.string ad)
  val ds = String.^(Substring.string bd,ad)
  val n = Arbint.fromString ds
  val t = intSyntax.term_of_int n
in
  t
end

fun mk_int_bound (s,b) =
  (if s then mk_Signed else mk_Unsigned) b
val Unsigned256 = mk_Unsigned (numOfLargeInt 256)

fun d_astHmType() : term decoder = achoose "astHmType" [
  check_field "name" "String" $
    JSONDecode.map mk_String (field "length" numtm),
  check_field "name" "Bytes" $
    JSONDecode.map mk_Bytes (field "length" numtm),
  check_field "typeclass" "bytes_m" $
    JSONDecode.map mk_BytesM $ field "m" numtm,
  check_field "name" "bool" $ succeed bool_tm,
  check_field "name" "address" $ succeed address_tm,
  check_field "name" "decimal" $ succeed decimal_tm,
  check_field "typeclass" "integer" $
    JSONDecode.map (fn (b,n) =>
      (if b then mk_int else mk_uint) n) $
    tuple2 (
      field "is_signed" bool,
      field "bits" numtm),
  check_field "typeclass" "dynamic_array" $
    JSONDecode.map(fn (t,b) => list_mk_comb(ArrayT_tm, [t,b])) $
    tuple2 (
      field "value_type" $ delay d_astHmType,
      JSONDecode.map mk_Dynamic (field "length" numtm)
    ),
  check_field "typeclass" "static_array" $
    JSONDecode.map(fn (t,b) => list_mk_comb(ArrayT_tm, [t,b])) $
    tuple2 (
      field "value_type" $ delay d_astHmType,
      JSONDecode.map mk_Fixed (field "length" numtm)
    ),
  check_field "typeclass" "struct" $
    JSONDecode.map (curry mk_comb StructT_tm) $
      field "name" stringtm,
  check_field "typeclass" "flag" $
    JSONDecode.map (curry mk_comb FlagT_tm) $
      field "name" stringtm,
  check_field "typeclass" "tuple" $
    JSONDecode.map (curry mk_comb TupleT_tm) $
      field "member_types" $
      JSONDecode.map (fn ls => mk_list(ls, type_ty)) $
        array (delay d_astHmType),
  null NoneT_tm
]
val astHmType = delay d_astHmType

fun d_expression () : term decoder = achoose "expr" [
    check_ast_type "Str" $
    JSONDecode.map mk_ls $
      tuple2 (
        field "type" (field "length" numtm),
        field "value" string
      ),
    check_ast_type "Int" $
    JSONDecode.map mk_li $
      tuple2 (
        JSONDecode.map mk_int_bound $
        field "type" $
          tuple2 (field "is_signed" bool, field "bits" numtm),
        JSONDecode.map
          (intSyntax.term_of_int o Arbint.fromLargeInt) $
          field "value" intInf),
    check_ast_type "Decimal" $
    field "value" (JSONDecode.map (mk_ld o parseDecimal) string),
    check_ast_type "Hex" $
    field "value" (JSONDecode.map mk_Hex string),
    check (field "ast_type" string)
          (Lib.C Lib.mem ["Bytes", "HexBytes"])
          "not bytes/hexbytes" $
    JSONDecode.map mk_Hex_dyn $
    tuple2 (
      field "type" $ check_field "name" "Bytes" $
        field "length" numtm,
      field "value" string
    ),
    check_ast_type "IfExp" $
    JSONDecode.map mk_IfExp $
    tuple3 (
      field "test" $ delay d_expression,
      field "body" $ delay d_expression,
      field "orelse" $ delay d_expression
    ),
    check_ast_type "UnaryOp" $
    check (field "op" (field "ast_type" string))
          (equal "USub")
          "not USub" $
    JSONDecode.map mk_Neg $
    field "operand" $ delay d_expression,
    check_ast_type "UnaryOp" $
    check (field "op" (field "ast_type" string))
          (equal "Invert")
          "not Invert" $
    JSONDecode.map mk_Not $
    field "operand" $ delay d_expression,
    check (field "ast_type" string)
          (Lib.C Lib.mem ["BinOp", "Compare"])
          "not binop/compare" $
    JSONDecode.map mk_BinOp $
    tuple3 (
      field "left" (delay d_expression),
      field "op" binop,
      field "right" (delay d_expression)
    ),
    check_ast_type "BoolOp" $
      JSONDecode.map mk_BoolOp $
      tuple2 (
        field "op" (field "ast_type" string),
        field "values" (array (delay d_expression))
      ),
    check_ast_type "Tuple" $
      JSONDecode.map mk_Tuple $
      field "elements" (array (delay d_expression)),
    check_ast_type "List" $
      check (field "type" (field "name" string))
            (equal "$SArray") "not a $SArray" $
      JSONDecode.map mk_SArray $
      tuple2 (
        field "type" $ field "value_type" $ astHmType,
        field "elements" (array (delay d_expression))
      ),
    check_ast_type "List" $
      check (field "type" (field "name" string))
            (equal "DynArray") "not a DynArray" $
      JSONDecode.map mk_MakeArray $
      tuple3 (
        JSONDecode.map optionSyntax.mk_some $
          field "type" $ field "value_type" $ astHmType,
        JSONDecode.map mk_Dynamic $
          field "type" (field "length" numtm),
        field "elements" (array (delay d_expression))
      ),
    check_ast_type "Subscript" $
    JSONDecode.map (uncurry mk_Subscript) $
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
    check_ast_type "Attribute" $
    check (field "value" (tuple2 (field "ast_type" string,
                                  field "id" string)))
          (equal ("Name", "block"))
          "Attribute not block"
          (check (field "attr" string)
                 (equal "timestamp")
                 "not block.timestamp"
                 (succeed timestamp_tm)),
    (*
    check_ast_type "Attribute" $
    check (field "value" (tuple2 (field "ast_type" string,
                                  field "id" string)))
          (equal ("Name", "msg"))
          "Attribute not msg"
          (check (field "attr" string)
                 (Lib.C Lib.mem ["gas","mana"])
                 "not msg.gas"
                 (succeed msg_gas_tm)),
    *)
    check_ast_type "Attribute" $
    check (field "value" (tuple2 (field "ast_type" string,
                                  field "id" string)))
          (equal ("Name", "self"))
          "Attribute not self" $
    JSONDecode.map (curry mk_comb TopLevelName_tm) $
    (field "attr" stringtm),
    check_ast_type "Attribute" $
    check (tuple2 (field "value" (field "type" (field "name" string)),
                   field "attr" string))
          (equal ("address", "balance"))
          "Attribute address.balance" $
    JSONDecode.map (fn e => mk_Builtin (mk_comb(Acc_tm, Balance_tm))
                                       (mk_list([e], expr_ty))) $
    field "value" (delay d_expression),
    check_ast_type "Attribute" $
    check (tuple2 (field "value" $ field "type" $ field "typeclass" string,
                   field "attr" string))
          (equal ("interface", "address"))
          "not interface.address" $
    JSONDecode.map (fn e => mk_Builtin (mk_comb(Acc_tm, Address_tm))
                                       (mk_list([e], expr_ty))) $
    field "value" (delay d_expression),
    check_ast_type "Attribute" $
    JSONDecode.map (fn (e,s) => list_mk_comb(Attribute_tm, [e,s])) $
    tuple2 (
      field "value" $
        check (tuple2 (field "ast_type" string, try (field "id" string)))
        (not o equal ("Name", SOME "msg"))
        "unhandled msg attribute" $
        delay d_expression,
      field "attr" stringtm
    ),
    check_ast_type "Call" $
      field "func" $
      check (tuple2 (field "ast_type" string,
                     field "type" (tuple2 (field "name" string,
                                           field "typeclass" string))))
            (equal ("Attribute", ("pop", "member_function")))
            "not pop" $
      JSONDecode.map (curry mk_comb Pop_tm) $
      field "value" $ delay d_baseAssignmentTarget,
    check_ast_type "Call" $
      check (field "func" $ tuple2 (field "ast_type" string,
                                    field "id" string))
            (equal ("Name", "len"))
            "not len" $
      JSONDecode.map mk_Len $
      field "args" $
      JSONDecode.sub 0 $
      delay d_expression,
    check_ast_type "Call" $
    JSONDecode.map (fn (n,es) => mk_Builtin (mk_Concat n) es) $
    tuple2 ( (* TODO: abstract out this builtin decoding *)
      check (field "func" (tuple2 (
               field "ast_type" string,
               field "id" string)))
            (equal ("Name", "concat"))
            "not concat" $
      field "type" $
        check (field "name" string)
          (Lib.C Lib.mem ["String","Bytes"])
          "concat type not String or Bytes" $
          field "length" numtm,
      field "args" $ JSONDecode.map
        (fn ls => mk_list(ls, expr_ty)) $
        array (delay d_expression)
    ),
    check_ast_type "Call" $
    JSONDecode.map (fn (b,es) => mk_Builtin (mk_Slice b) es) $
    tuple2 (
      check (field "func" (tuple2 (
               field "ast_type" string,
               field "id" string)))
            (equal ("Name", "slice"))
            "not slice" $
      field "type" $
        check (field "name" string)
          (Lib.C Lib.mem ["String","Bytes"])
          "concat type not String or Bytes" $
          field "length" numtm,
      field "args" $ JSONDecode.map
        (fn ls => mk_list(ls, expr_ty)) $
        array (delay d_expression)
    ),
    check_ast_type "Call" $
    check (field "func" $ tuple2 (
             field "ast_type" string,
             field "id" string))
          (equal ("Name", "empty"))
          "not empty" $
      field "args" $
      JSONDecode.sub 0 $
      JSONDecode.map mk_Empty astType,
    check_ast_type "Call" $
    check (field "func" $ tuple2 (
             field "ast_type" string,
             field "id" string))
          (equal ("Name", "keccak256"))
          "not keccak256" $
      field "args" $
      JSONDecode.sub 0 $
      JSONDecode.map mk_Keccak256 (delay d_expression),
    check_ast_type "Call" $
    check (field "func" $ tuple2 (
             field "ast_type" string,
             field "id" string))
          (equal ("Name", "floor"))
          "not floor" $
      field "args" $
      JSONDecode.sub 0 $
      JSONDecode.map mk_Floor (delay d_expression),
    check_ast_type "Call" $
    check (field "func" $ tuple2 (
             field "ast_type" string,
             field "id" string))
          (equal ("Name", "max_value"))
          "not max_value" $
      field "args" $
      JSONDecode.sub 0 $
      JSONDecode.map mk_MaxValue astType,
    check_ast_type "Call" $
    check (field "func" $ tuple2 (
             field "ast_type" string,
             field "id" string))
          (equal ("Name", "min_value"))
          "not min_value" $
      field "args" $
      JSONDecode.sub 0 $
      JSONDecode.map mk_MinValue astType,
    check_ast_type "Call" $
    JSONDecode.map mk_Convert $
    check (field "func" $ tuple2 (
             field "ast_type" string,
             field "id" string))
          (equal ("Name", "convert"))
          "not convert" $
    field "args" $
    tuple2 (
      JSONDecode.sub 1 astType,
      JSONDecode.sub 0 (delay d_expression)
    ),
    check_ast_type "Call" $
      check (field "type" $ field "typeclass" string)
            (equal "interface")
            "not an interface" $
      field "args" $ JSONDecode.sub 0 $ delay d_expression,
    check_ast_type "Call" $
      check (field "type" (field "typeclass" string))
            (equal "struct") "not a struct" $
      JSONDecode.map mk_StructLit $
      tuple2 (
        field "func" $ check_ast_type "Name" $
          field "id" stringtm,
        field "keywords" (array (delay d_keyword))
      ),
    check_ast_type "Name" $
    check (tuple2 (field "id" string, field "type" (field "name" string)))
          (equal ("self", "address"))
          "not self.address" $
          succeed $ self_addr_tm,
    check_ast_type "Name" $
    field "id" (JSONDecode.map mk_Name string),
    check_ast_type "NameConstant" $
    field "value" (JSONDecode.map mk_lb booltm),
    check_ast_type "Call" $
    JSONDecode.map (fn (i,a) => mk_Call (mk_IntCall i) a) $
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
and d_keyword () : term decoder =
  JSONDecode.map mk_pair $
  tuple2 (
    field "arg" stringtm,
    field "value" $ delay d_expression
  )
and d_baseAssignmentTarget () : term decoder = achoose "bt" [
  check_ast_type "Attribute" $
  check (field "value" (tuple2 (field "ast_type" string, field "id" string)))
        (equal ("Name", "self"))
        "not self.target" $
  JSONDecode.map (curry mk_comb TopLevelNameTarget_tm) $
    field "attr" stringtm,
  check_ast_type "Name" $
  JSONDecode.map (curry mk_comb NameTarget_tm) $
    field "id" stringtm,
  check_ast_type "Attribute" $
  JSONDecode.map
    (fn (t,n) => list_mk_comb(AttributeTarget_tm, [t,n])) $
    tuple2 (
      field "value" $ delay d_baseAssignmentTarget,
      field "attr" stringtm
    ),
  check_ast_type "Subscript" $
  JSONDecode.map
    (fn (t,e) => list_mk_comb(SubscriptTarget_tm, [t,e])) $
    tuple2 (
      field "value" $ delay d_baseAssignmentTarget,
      field "slice" $ delay d_expression
    )
]
val expression = delay d_expression
val baseAssignmentTarget = delay d_baseAssignmentTarget

fun bound_from_type y = let
  val bt = rand y (* y should be BaseT (U)IntT n, TODO check it *)
  val (uori, n) = dest_comb bt
in
  (if aconv uori UintT_tm then mk_Unsigned else mk_Signed) n
end

(* TODO: support variable (expr) args with explicit bounds *)
fun rangeArgs ls = let
  val (s, e) = case ls of [x,y] => (x,y) | [x] => (0,x) | _ => (0,0)
  val b = e - s
  val [s,e] = List.map (intSyntax.term_of_int o Arbint.fromLargeInt) [s,e]
  fun f y = let val a = bound_from_type y in
    list_mk_comb(Range_tm, [mk_li (a, s), mk_li (a, e)]) end
in (f, numOfLargeInt b) end

val iterator : ((term -> term) * term) decoder = achoose "iterator" [
  check_ast_type "Call" $
  check (field "func" (field "id" string))
        (equal "range") "not range" $
  JSONDecode.map rangeArgs $
  field "args" $ array $
    field "folded_value" $
    check_ast_type "Int" (field "value" intInf),
  check_ast_type "Call" $
  check (tuple2 (field "func" (field "id" string),
                 field "keywords" $ JSONDecode.sub 0 $ field "arg" string))
        (equal ("range", "bound")) "not bounded range" $
  JSONDecode.map
    (fn (ls, n) =>
     let val z = List.length ls
         fun args y =
           if z = 2 then ls
           else if z = 1 then
             mk_li (bound_from_type y, intSyntax.zero_tm) :: ls
           else raise Fail "bounded range wrong args"
         fun f y = list_mk_comb(Range_tm, args y)
     in (f, n) end) $
    tuple2 (
      field "args" (array expression),
      field "keywords" $ JSONDecode.sub 0 $ field "value" $
      field "folded_value" $ field "value" numtm),
  JSONDecode.map (fn (e,t) =>
    (K $ mk_comb(Array_tm, e), t)) $
  tuple2 (expression,
          field "type" $
          check (field "name" string)
                (Lib.C Lib.mem ["DynArray", "$SArray"])
                "not an array" $
          field "length" numtm)
]

val (_, assignment_target_ty) = dom_rng $ type_of TupleTarget_tm

fun d_assignmentTarget () : term decoder = achoose "tgt" [
  JSONDecode.map (curry mk_comb BaseTarget_tm) baseAssignmentTarget,
  JSONDecode.map (fn ls =>
    mk_comb(TupleTarget_tm, mk_list(ls, assignment_target_ty))) $
    field "elements" $ array (delay d_assignmentTarget)
]
val assignmentTarget = delay d_assignmentTarget

fun mk_statements ls = mk_list(ls, stmt_ty)
val d_statements = JSONDecode.map mk_statements o array

fun d_statement () : term decoder = achoose "stmt" [
    check_ast_type "Pass" $ succeed Pass_tm,
    check_ast_type "Break" $ succeed Break_tm,
    check_ast_type "Continue" $ succeed Continue_tm,
    check_ast_type "Expr" $
      field "value" $
      check_ast_type "Call" $
      check (field "func" $
             tuple2 (field "ast_type" string,
                     field "type" (tuple2 (field "name" string,
                                           field "typeclass" string))))
            (equal ("Attribute", ("append", "member_function")))
            "not append" $
      JSONDecode.map
        (fn (t,e) => list_mk_comb(Append_tm, [t,e])) $
      tuple2 (
        field "func" $ field "value" baseAssignmentTarget,
        field "args" $ JSONDecode.sub 0 $ expression),
    check_ast_type "Expr" $
    field "value" (JSONDecode.map mk_Expr expression),
    check_ast_type "For" $
    JSONDecode.map (fn ((s,t),(i,n),b) => mk_For s t (i t) n b) $
    tuple3 (field "target" $
            check_ast_type "AnnAssign" $
            tuple2 (field "target" $
                    check_ast_type "Name" $
                    field "id" stringtm,
                    field "target" $
                    field "type" $ astHmType),
            field "iter" iterator,
            field "body" (d_statements (delay d_statement))),
    check_ast_type "If" $
    JSONDecode.map (fn (e,s1,s2) => mk_If e s1 s2) $
    tuple3 (field "test" expression,
            field "body" (d_statements (delay d_statement)),
            field "orelse" (d_statements (delay d_statement))),
    check_ast_type "Raise" $
    JSONDecode.map (curry mk_comb Raise_tm) $
    field "exc" $ orElse(expression, null $ empty_lstr),
    check_ast_type "Assert" $
    JSONDecode.map mk_Assert
      (tuple2 (field "test" expression,
               field "msg" (orElse (expression, null $ empty_lstr)))),
    check_ast_type "Log" $
    JSONDecode.map mk_Log $
      field "value" $
      check_ast_type "Call" $
      tuple2 (
        field "func" $ check_ast_type "Name" $ field "id" stringtm,
        (* TODO: handle unnamed arguments? *)
        JSONDecode.map (fn ls => mk_list(ls, expr_ty)) $
          field "keywords" (array $ field "value" expression)
      ),
    check_ast_type "Return" $
    field "value" (JSONDecode.map mk_Return (nullable expression)),
    check_ast_type "AugAssign" $
    JSONDecode.map (fn (t,b,e) => mk_AugAssign t b e) $
    tuple3 (
      field "target" baseAssignmentTarget,
      field "op" binop,
      field "value" expression
    ),
    check_ast_type "AnnAssign" $
    JSONDecode.map mk_AnnAssign $
    tuple3 (
      field "target" (check_ast_type "Name" (field "id" stringtm)),
      field "target" $ field "type" astHmType,
      field "value" expression
    ),
    check_ast_type "Assign" $
    JSONDecode.map (fn (t,e) => list_mk_comb(Assign_tm, [t,e])) $
    tuple2 (
      field "target" assignmentTarget,
      field "value" expression
    )
  ]

val statement = delay d_statement

val statements : term decoder = d_statements statement

fun mk_FunctionDecl_from_args ((decs, id, argnms),((argtys,ret),body)) =
let
  val vis =
    if List.exists (equal "external") decs then External_tm else
    if List.exists (equal "deploy") decs then Deploy_tm else
    Internal_tm
  val mut =
    if List.exists (equal "pure") decs then Pure_tm else
    if List.exists (equal "view") decs then View_tm else
    if List.exists (equal "payable") decs then Payable_tm else
    Nonpayable_tm
  val args = mk_list(
               List.map mk_pair $
               ListPair.zip (argnms, argtys),
               argument_ty)
in
    mk_FunctionDecl vis mut id args ret body
end

val functionDef : term decoder =
  check_ast_type "FunctionDef" $
  JSONDecode.map mk_FunctionDecl_from_args $
  tuple2 (tuple3 (field "decorator_list" (array (field "id" string)),
                  field "name" stringtm,
                  field "args" $
                    check_ast_type "arguments" $
                    field "args" (array (field "arg" stringtm))),
          tuple2 (field "func_type" $
                    tuple2 (
                      field "argument_types" (array astHmType),
                      field "return_type" astHmType),
                  field "body" statements))

val variableVisibility : term decoder =
  field "is_public" (JSONDecode.map
    (fn b => if b then Public_tm else Private_tm) bool)

val variableDecl : term decoder =
  check_ast_type "VariableDecl" $
  JSONDecode.map mk_VariableDecl $
  tuple4 (
    variableVisibility,
    JSONDecode.map (fn (im,tr,con) =>
      if im then Immutable_tm else
      if tr then Transient_tm else
      case con of SOME e => mk_comb(Constant_tm, e)
                | NONE => Storage_tm) $
    tuple3 (
      field "is_immutable" bool,
      field "is_transient" bool,
      andThen (field "is_constant" bool)
              (fn b => if b then field "value" (JSONDecode.map SOME expression)
                       else succeed NONE)),
    field "target" (check_ast_type "Name" (field "id" stringtm)),
    field "target" $ field "type" astHmType)

fun d_astValueType () : term decoder = achoose "astValueType" [
  check_field "typeclass" "hashmap" $
    JSONDecode.map (fn (k,v) =>
      list_mk_comb(HashMapT_tm, [k,v])) $
    tuple2 (
      field "key_type" astHmType,
      field "value_type" $ delay d_astValueType),
  JSONDecode.map (fn t => mk_comb(Type_tm, t)) $
    astHmType
]
val astValueType = delay d_astValueType

val hashMapDecl : term decoder =
  check_ast_type "VariableDecl" $
  JSONDecode.map (fn (v,b,n,(kt,vt)) => mk_HashMapDecl (v,b,n,kt,vt)) $
  tuple4 (
    variableVisibility,
    field "is_transient" booltm,
    field "target" (check_ast_type "Name" (field "id" stringtm)),
    tuple2 (
      field "target" (field "type" (field "key_type" astHmType)),
      field "target" (field "type" (field "value_type" astValueType))
    )
  )

val eventArg : term decoder =
  check_ast_type "AnnAssign" $
  JSONDecode.map mk_pair $
  field "target" $
  tuple2 (
    check_ast_type "Name" $
      field "id" stringtm,
    field "type" astHmType)

val eventDef : term decoder =
  check_ast_type "EventDef" $
  JSONDecode.map (fn (n,a) =>
    list_mk_comb(EventDecl_tm, [n, mk_list(a, argument_ty)])) $
  tuple2 (
    field "name" stringtm,
    field "body" $ orElse (
      array eventArg,
      JSONDecode.sub 0 (check_ast_type "Pass" (succeed [])))
  )

val structDef : term decoder =
  check_ast_type "StructDef" $
  JSONDecode.map (fn (n,a) =>
    list_mk_comb(StructDecl_tm, [n, mk_list(a, argument_ty)])) $
  tuple2 (
    field "name" stringtm,
    field "body" (array eventArg)
  )

val flagDef : term decoder =
  check_ast_type "FlagDef" $
  JSONDecode.map (fn (n,a) =>
    list_mk_comb(FlagDecl_tm, [n, mk_list(a, string_ty)])) $
  tuple2 (
    field "name" stringtm,
    field "body" $ array $
      check_ast_type "Expr" $
      field "value" $
      check_ast_type "Name" $
      field "id" stringtm
  )

val toplevel : term decoder = achoose "tl" [
    functionDef,
    hashMapDecl,
    variableDecl,
    eventDef,
    structDef,
    flagDef,
    check_ast_type "InterfaceDef" (succeed F)
  ]

val toplevels : term decoder =
  JSONDecode.map (fn ls =>
    mk_list(List.filter (equal toplevel_ty o type_of) ls, toplevel_ty)
  ) (array toplevel)

val abiBaseType : term decoder =
  JSONDecode.map parse_abi_type string

fun tuple_brackets s =
  if Substring.isSuffix "]" s then let
    val (ps, ns) = Substring.splitr (not o equal #"[") s
    val bt = parse_optnum ns
    val s = Substring.trimr 1 ps
    val a = mk_comb(abiArray_tm, bt)
  in
    curry mk_comb a o tuple_brackets s
  end else if Substring.isEmpty s
  then I else raise Fail "not brackets"

fun d_abiType () : term decoder = achoose "abiType" [
  check (field "type" string)
        (String.isPrefix "tuple")
        "not tuple" $
    JSONDecode.map (fn (t, ls) =>
      (tuple_brackets $
       Substring.extract
         (t, String.size "tuple", NONE)) $
      mk_comb(abiTuple_tm, mk_list (ls, abi_type_ty))) $
    tuple2 (field "type" string,
            field "components" $ array $ delay d_abiType),
  field "type" abiBaseType
]
val abiType = delay d_abiType

val abiArg : term decoder =
  JSONDecode.map mk_pair $
  tuple2 (field "name" stringtm, abiType)

val abiMutability : term decoder =
  andThen string (fn s =>
    if s = "nonpayable" then succeed Nonpayable_tm else
    if s = "view" then succeed View_tm else
    if s = "payable" then succeed Payable_tm else
    if s = "pure" then succeed Pure_tm else
    fail ("abiMutability: " ^ s))

val Function_tm = prim_mk_const{Thy="vyperTestRunner",Name="Function"}
val Event_tm = prim_mk_const{Thy="vyperTestRunner",Name="Event"}
val (abi_function_ty, abi_entry_ty) = dom_rng $ type_of $ Function_tm
val abi_arg_ty = mk_prod(string_ty, abi_type_ty)

fun mk_Function (n,is,os,m) =
  mk_comb(Function_tm,
             TypeBase.mk_record (abi_function_ty, [
               ("name", n),
               ("inputs", mk_list(is, abi_arg_ty)),
               ("outputs", mk_list(os, abi_arg_ty)),
               ("mutability", m)]))

val abiEntry : term decoder = achoose "abiEntry" [
    check_field "type" "function" $
    JSONDecode.map mk_Function $
      tuple4 (field "name" stringtm,
              field "inputs" (array abiArg),
              field "outputs" (array abiArg),
              field "stateMutability" abiMutability),
    check_field "type" "constructor" $
    JSONDecode.map mk_Function $
      tuple4 (succeed $ fromMLstring "__init__",
              field "inputs" (array abiArg),
              field "outputs" (array abiArg),
              field "stateMutability" abiMutability),
    check_field "type" "fallback" $
    JSONDecode.map mk_Function $
      tuple4 (succeed $ fromMLstring "__default__",
              succeed $ [],
              succeed $ [],
              field "stateMutability" abiMutability),
    check_field "type" "event" $
    JSONDecode.map (fn s => mk_comb(Event_tm, s)) $
    field "name" stringtm
  ]

val Deployment_tm = prim_mk_const{Thy="vyperTestRunner",Name="Deployment"}
val deployment_trace_ty = #1 $ dom_rng $ type_of Deployment_tm

val SetBalance_tm = prim_mk_const{Thy="vyperTestRunner",Name="SetBalance"}
val ClearTransientStorage_tm =
  prim_mk_const{Thy="vyperTestRunner",Name="ClearTransientStorage"}

val unsupported_code = [
  "def boo(a: DynArray[uint256, 12] =", (* TODO: default argument values *)
  "def addition(a: uint256, b: uint256 = 1)", (* TODO: ditto *)
  "def test(a: uint256, b: String[50] =", (* TODO: ditto *)
  "def test2(l: bytes2 =", (* TODO: ditto *)
  "def test2(l: Bytes[2] =", (* TODO: ditto *)
  "def test2(l: Bytes[3] =", (* TODO: ditto *)
  "def test2(l: Bytes[4] =", (* TODO: ditto *)
  "def test2(l: bytes3 =", (* TODO: ditto *)
  "def test2(l: bytes4 =", (* TODO: ditto *)
  "def foo(a: Bytes[65] =", (* TODO: ditto *)
  "def foo(a: String[65] =", (* TODO: ditto *)
  "def foo(a: uint256 =", (* TODO: ditto *)
  "def foo(a: uint256[3] =", (* TODO: ditto *)
  "def foo(a: DynArray[uint256, 3] =", (* TODO: ditto *)
  "def fooBar(a: int128 =", (* TODO: ditto *)
  "def outer(xs: Bytes[256] = ", (* TODO: default arguments on external fns *)
  "def wycpnbqcyf(", (* TODO: investigate, something about call selector *)
  "def blockHashAskewLimitary(", (* TODO: investigate, something about call selector *)
  "+ -1e38", (* TODO: parse scientific notation *)
  "uint256[max_value(uint256)-1]", (* TODO: optimise *)
  "@raw_return\n", (* TODO: add *)
  "tx.gasprice", (* TODO: add *)
  "block.number", (* TODO: add *)
  "block.blobbasefee", (* TODO: add *)
  "convert(n, decimal)" (* TODO: conversion to decimal *)
]

val deployment : term decoder =
  check_trace_type "deployment" $
  check (field "source_code" string)
        (fn src => List.all (fn x => not $ String.isSubstring x src) unsupported_code)
        "has unsupported_code" $
  JSONDecode.map (fn ((c,i,(s,m,a),(d,v)),e) =>
             TypeBase.mk_record (deployment_trace_ty, [
               ("sourceAst", c),
               ("contractAbi", mk_list(i, abi_entry_ty)),
               ("deployedAddress", a),
               ("deployer", s),
               ("deploymentSuccess", e),
               ("value", v),
               ("timeStamp", m),
               ("callData", d)
             ]))
          (tuple2 (tuple4 (field "annotated_ast"
                             (field "ast" (field "body" toplevels)),
                           field "contract_abi" (array abiEntry),
                           tuple3 (field "env" $ field "tx" $ field "origin" address,
                                   field "env" $ field "block" $ field "timestamp" numtm,
                                   field "deployed_address" address),
                           tuple2 (field "calldata" $
                                   JSONDecode.map (cached_bytes_from_hex o theoptstring)
                                     (nullable string),
                                   field "value" numtm)),
                   field "deployment_succeeded" booltm))

val trace : term decoder =
  achoose "trace" [
    JSONDecode.map (curry mk_comb Call_tm) call,
    JSONDecode.map (curry mk_comb Deployment_tm) deployment,
    check_trace_type "clear_transient_storage" $
      succeed ClearTransientStorage_tm,
    JSONDecode.map (fn (a,b) => list_mk_comb(SetBalance_tm, [a,b])) $
    tuple2 (
      field "address" address,
      field "value" numtm)
  ]

val test_decoder =
  (check_field "item_type" "test" $
   field "traces" (array trace))

fun trydecode ((name,json),(s,f)) =
  ((name, decode test_decoder json)::s, f)
  handle JSONError e => (s, (name, e)::f)
         | e => (s, (name, (e, JSON.OBJECT [("source_code", JSON.STRING "")]))::f)

fun read_test_json json_path = let
  val test_jsons = decodeFile rawObject json_path
in
  List.foldl trydecode ([],[]) test_jsons
end

val trace_ty = mk_thy_type{Thy="vyperTestRunner",Tyop="trace",Args=[]}
val traces_ty = mk_list_type trace_ty
val run_test_tm = prim_mk_const{Thy="vyperTestRunner",Name="run_test"}

fun has_unsupported_source_code (name, (err, j)) = let
  val srcopt = decode (orElse(field "source_code" (nullable string),
                              succeed NONE)) j
  val p = case srcopt of NONE => K true | SOME src => C String.isSubstring src
in
  List.exists p (unsupported_code @ [
    "as_wei_value(", (* TODO: add support *)
    "unsafe_mul(", (* TODO: add support *)
    " blockhash(", (* TODO: add support *)
    " send(", (* TODO: add support *)
    "sqrt(", (* TODO: add support *)
    "extcall ",
    "staticcall ",
    "raw_call(",
    "raw_log(",
    "raw_revert(",
    "selfdestruct",
    "msg.mana", "msg.gas",
    "exports",
    "import ",
    "create_minimal_proxy_to(",
    "create_copy_of("
  ])
end

val time_limit = Time.fromSeconds 120

fun run_test_on_traces traces_const = let
  val (traces_name, _) = dest_const traces_const
  val suffix = String.extract(traces_name, String.size"traces", NONE)
  val result_name = String.concat ["result", suffix]
  val rtm = mk_comb(run_test_tm, traces_const)
  val rth = Timeout.apply time_limit cv_eval rtm
            handle Timeout.TIMEOUT _ => raise Fail (
              String.concat ["Timeout in test ", result_name])
  val ttm = sumSyntax.mk_isl $ rtm
  val eth = (RAND_CONV (REWR_CONV rth) THENC cv_eval) ttm
  val tth = EQT_ELIM eth handle HOL_ERR _ =>
            raise Fail (String.concat [
              "Failure in test ", result_name, ": ",
              term_to_string $ rand $ rhs $ concl rth ])
  val tth = save_thm (result_name, tth)
in
  ()
end

val test_files_with_prefixes = [
  ("../vyper/tests/export/functional/codegen/types/numbers",
   ["test_constants.json",
    "test_decimals.json",
    "test_division.json",
    "test_exponents.json",
    "test_isqrt.json",
    "test_modulo.json",
    "test_signed_ints.json",
    "test_sqrt.json",
    "test_unsigned_ints.json"]),
  ("../vyper/tests/export/functional/codegen/types",
   ["test_array_indexing.json",
    "test_bytes.json",
    "test_bytes_literal.json",
    "test_dynamic_array.json",
    "test_flag.json",
    "test_identifier_naming.json",
    "test_lists.json",
    "test_node_types.json",
    "test_string.json",
    "test_string_literal.json",
    "test_struct.json"]),
  ("../vyper/tests/export/functional/codegen/features",
   ["test_address_balance.json",
    "test_assert.json",
    "test_assert_unreachable.json",
    "test_assignment.json",
    "test_bytes_map_keys.json",
    (* TODO: slow
    "test_clampers.json",
    *)
    "test_comments.json",
    "test_comparison.json",
    "test_conditionals.json",
    "test_constructor.json",
    "test_flag_pure_functions.json",
    "test_gas.json",
    "test_immutable.json",
    "test_init.json",
    "test_logging.json",
    "test_logging_bytes_extended.json",
    "test_logging_from_call.json",
    "test_mana.json",
    "test_memory_alloc.json",
    "test_memory_dealloc.json",
    "test_packing.json",
    "test_reverting.json",
    "test_selfdestruct.json",
    "test_short_circuiting.json",
    "test_string_map_keys.json",
    "test_ternary.json",
    "test_transient.json"]),
  ("../vyper/tests/export/functional/codegen/features/decorators",
   ["test_nonreentrant.json",
    "test_payable.json",
    "test_private.json",
    "test_public.json",
    "test_pure.json",
    "test_raw_return.json",
    "test_view.json"]),
  ("../vyper/tests/export/functional/codegen/features/iteration",
   ["test_break.json",
    "test_continue.json",
    "test_for_in_list.json",
    "test_for_range.json",
    "test_range_in.json"])
]

fun make_test_files [] acc = List.rev acc
  | make_test_files ((pfx,ls)::r) acc =
    make_test_files r $ List.revAppend
      (List.map (curry OS.Path.concat pfx) ls, acc)
val test_files = make_test_files test_files_with_prefixes []

val num_test_files = List.length test_files

fun make_definitions_for_file n = let
  val nstr = Int.toString n
  val json_path = el n test_files
  val (tests, decode_fails) = read_test_json json_path
  val firstDf = List.find (not o has_unsupported_source_code) decode_fails
  val () = case firstDf of NONE => () | SOME (name, _) => raise Fail
             (String.concat ["decode failure in ", json_path, ": ", name])
  val traces_prefix = String.concat ["traces_", nstr, "_"]
  fun define_traces i (name, traces) = let
    val trs = mk_list(traces, trace_ty)
    val vn = traces_prefix ^ Int.toString i
    val var = mk_var(vn, traces_ty)
    val def = new_definition(vn ^ "_def", mk_eq(var, trs))
    val () = cv_trans def
  in () end
in
  Lib.appi define_traces tests
end

(*

  val json_path = "../vyper/tests/export/functional/codegen/features/decorators/test_private.json"
  val test_jsons = decodeFile rawObject json_path
  val SOME (name, json) = List.find (String.isPrefix "test_private_payable" o #1) test_jsons
  val traces = decode (field "traces" $ array raw) json
  val tr = el 1 traces
  decode trace tr
  decode (field "source_code" string) tr
  val tls = decode (field "annotated_ast" $ field "ast" $ field "body" $ array raw) tr
  val tl = el 3 tls
  decode toplevel tl
  val body = decode (field "body" (array raw)) tl
  val stmt = el 4 body
  decode statement stmt
  decode (field "ast_type" string) stmt
  val tgt = decode (field "target" raw) stmt
  decode (field "target" assignmentTarget) stmt

*)

end
