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
val DecimalT_tm     = astk"DecimalT"
val StringT_tm      = astk"StringT"
val BytesT_tm       = astk"BytesT"
val AddressT_tm     = astk"AddressT"
val BaseT_tm        = astk"BaseT"
val TupleT_tm       = astk"TupleT"
val ArrayT_tm       = astk"ArrayT"
val StructT_tm      = astk"StructT"
val NoneT_tm        = astk"NoneT"
val Signed_tm       = astk"Signed"
val Unsigned_tm     = astk"Unsigned"
val BoolL_tm        = astk"BoolL"
val StringL_tm      = astk"StringL"
val BytesL_tm       = astk"BytesL"
val IntL_tm         = astk"IntL"
val Add_tm          = astk"Add"
val Sub_tm          = astk"Sub"
val Mul_tm          = astk"Mul"
val Div_tm          = astk"Div"
val Mod_tm          = astk"Mod"
val Exp_tm          = astk"Exp"
val And_tm          = astk"And"
val Or_tm           = astk"Or"
val In_tm           = astk"In"
val NotIn_tm        = astk"NotIn"
val Eq_tm           = astk"Eq"
val NotEq_tm        = astk"NotEq"
val Lt_tm           = astk"Lt"
val Gt_tm           = astk"Gt"
val Sender_tm       = astk"Sender"
val SelfAddr_tm     = astk"SelfAddr"
val Balance_tm      = astk"Balance"
val Len_tm          = astk"Len"
val Not_tm          = astk"Not"
val Neg_tm          = astk"Neg"
val Concat_tm       = astk"Concat"
val Slice_tm        = astk"Slice"
val MakeArray_tm = astk"MakeArray"
val Bop_tm          = astk"Bop"
val Msg_tm          = astk"Msg"
val Acc_tm          = astk"Acc"
val IntCall_tm      = astk"IntCall"
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
val Expr_tm         = astk"Expr"
val For_tm          = astk"For"
val If_tm           = astk"If"
val Assert_tm       = astk"Assert"
val Log_tm          = astk"Log"
val Raise_tm        = astk"Raise"
val Return_tm       = astk"Return"
val Assign_tm       = astk"Assign"
val AugAssign_tm    = astk"AugAssign"
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
val FunctionDecl_tm = astk"FunctionDecl"
val VariableDecl_tm = astk"VariableDecl"
val HashMapDecl_tm  = astk"HashMapDecl"
val StructDecl_tm   = astk"StructDecl"
val EventDecl_tm    = astk"EventDecl"
val FlagDecl_tm     = astk"FlagDecl"

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
fun mk_Convert (t,v) = list_mk_comb(TypeBuiltin_tm, [
  Convert_tm, t, mk_list([v], expr_ty)])
fun mk_Call ct args = list_mk_comb(AstCall_tm, [ct, mk_list (args, expr_ty)])
fun mk_Assert (e,s) = list_mk_comb(Assert_tm, [e, s])
fun mk_Log (id,es) = list_mk_comb(Log_tm, [id, es])
fun mk_Subscript e1 e2 = list_mk_comb(Subscript_tm, [e1, e2])
fun mk_If e s1 s2 = list_mk_comb(If_tm, [e,s1,s2])
fun mk_li (b,i) = mk_comb(Literal_tm, list_mk_comb(IntL_tm, [b,i]))
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
    list_mk_comb(BytesL_tm, [b, mk_bytes_tm s]))
end
fun mk_Hex s = let
  val s = if String.isPrefix "0x" s then String.extract(s,2,NONE) else s
  val n = numSyntax.term_of_int $ String.size s div 2
  val b = mk_comb(Fixed_tm, n)
in
  mk_comb(Literal_tm,
    list_mk_comb(BytesL_tm, [b, mk_bytes_tm s]))
end
fun mk_Builtin b es = list_mk_comb(Builtin_tm, [b, es])
fun mk_Concat n = mk_comb(Concat_tm, n)
fun mk_Slice n = mk_comb(Slice_tm, n)
fun mk_Neg t = mk_Builtin Neg_tm (mk_list([t], expr_ty))
fun mk_Bop b = mk_comb(Bop_tm, b)
fun mk_Len e = mk_Builtin Len_tm (mk_list([e], expr_ty))
fun mk_MakeArray (b,ls) =
  mk_Builtin (mk_comb(MakeArray_tm, b))
    (mk_list (ls, expr_ty))
fun mk_Tuple ls = let
  val n = numSyntax.term_of_int $ List.length ls
  val b = mk_comb(Fixed_tm, n)
in
  mk_MakeArray (b, ls)
end
fun mk_DynArray ls = let
  val n = numSyntax.term_of_int $ List.length ls
  val b = mk_comb(Dynamic_tm, n)
in
  mk_MakeArray (b, ls)
end
val msg_sender_tm = list_mk_comb(Builtin_tm, [
  mk_comb(Msg_tm, Sender_tm), mk_list([], expr_ty)])
val self_addr_tm = list_mk_comb(Builtin_tm, [
  mk_comb(Msg_tm, SelfAddr_tm), mk_list([], expr_ty)])
(*
val msg_gas_tm = list_mk_comb(Builtin_tm, [
  mk_comb(Msg_tm, Gas_tm), mk_list([], expr_ty)])
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
  andThen (fn x => if pred x then d else fail err) cd

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
  check_ast_type "Add" $ succeed Add_tm,
  check_ast_type "Sub" $ succeed Sub_tm,
  check_ast_type "Mult" $ succeed Mul_tm,
  check_ast_type "FloorDiv" $ succeed Div_tm,
  check_ast_type "Div" $ succeed Div_tm,
  check_ast_type "Mod" $ succeed Mod_tm,
  check_ast_type "And" $ succeed And_tm,
  check_ast_type "Or" $ succeed Or_tm,
  check_ast_type "In" $ succeed In_tm,
  check_ast_type "NotIn" $ succeed NotIn_tm,
  check_ast_type "Eq" $ succeed Eq_tm,
  check_ast_type "NotEq" $ succeed NotEq_tm,
  check_ast_type "Lt" $ succeed Lt_tm,
  check_ast_type "Gt" $ succeed Gt_tm
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
    field "value" (JSONDecode.map (
      curry mk_li (mk_Signed (numOfLargeInt 168))
      o parseDecimal) string),
    check_ast_type "Hex" $
    field "value" (JSONDecode.map mk_Hex string),
    check_ast_type "Bytes" $
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
      JSONDecode.map mk_Tuple $
      field "elements" (array (delay d_expression)),
    check_ast_type "List" $
      check (field "type" (field "name" string))
            (equal "DynArray") "not a DynArray" $
      JSONDecode.map mk_MakeArray $
      tuple2 (
        JSONDecode.map mk_Dynamic $
          field "type" (field "length" numtm),
        field "elements" (array (delay d_expression))
      ),
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
    JSONDecode.map (fn (e,s) => list_mk_comb(Attribute_tm, [e,s])) $
    tuple2 (
      field "value" (delay d_expression),
      field "attr" stringtm
    ),
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
          "not self:address" $
          succeed $ self_addr_tm,
    check_ast_type "Name" $
    field "id" (JSONDecode.map mk_Name string),
    check_ast_type "NameConstant" $
    field "value" (JSONDecode.map mk_lb booltm),
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
and d_keyword () : term decoder =
  JSONDecode.map mk_pair $
  tuple2 (
    field "arg" stringtm,
    field "value" $ delay d_expression
  )
val expression = delay d_expression

(* TODO: support variable (expr) args with explicit bounds *)
fun rangeArgs ls = let
  val (s, e) = case ls of [x,y] => (x,y) | [x] => (0,x) | _ => (0,0)
  val b = e - s
  val [s,e] = List.map (intSyntax.term_of_int o Arbint.fromLargeInt) [s,e]
  val t = list_mk_comb(Range_tm, [mk_li (Unsigned256, s), mk_li (Unsigned256, e)])
in (t, numOfLargeInt b) end

val iterator : (term * term) decoder = achoose "iterator" [
  check_ast_type "Call" $
  check (field "func" (field "id" string))
        (equal "range") "not range" $
  andThen (succeed o rangeArgs) $
  field "args" (array (check_ast_type "Int" (field "value" intInf)))
]

fun d_baseAssignmentTarget () : term decoder = achoose "bt" [
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
      field "slice" expression
    )
]
val baseAssignmentTarget = delay d_baseAssignmentTarget

fun d_assignmentTarget () : term decoder = achoose "tgt" [
  JSONDecode.map (curry mk_comb BaseTarget_tm) baseAssignmentTarget
]
val assignmentTarget = delay d_assignmentTarget

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
      field "annotation" astType,
      field "value" expression
    ),
    check_ast_type "Assign" $
    andThen (fn (t,e) => succeed $ list_mk_comb(Assign_tm, [t,e])) $
    tuple2 (
      field "target" assignmentTarget,
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

val variableVisibility : term decoder =
  field "is_public" (JSONDecode.map
    (fn b => if b then Public_tm else Private_tm) bool)

val variableDecl : term decoder =
  check_ast_type "VariableDecl" $
  JSONDecode.map mk_VariableDecl $
  tuple4 (
    variableVisibility,
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

val astHmType : term decoder = achoose "astHmType" [
  check_field "name" "String" $
    JSONDecode.map mk_String (field "length" numtm),
  check_field "name" "Bytes" $
    JSONDecode.map mk_Bytes (field "length" numtm),
  check_field "typeclass" "bytes_m" $
    JSONDecode.map mk_BytesM $ field "m" numtm,
  check_field "name" "bool" $ succeed bool_tm,
  check_field "name" "uint256" $ succeed $ mk_uint $ stringToNumTm "256",
  check_field "name" "int128" $ succeed $ mk_int $ stringToNumTm "128",
  check_field "typeclass" "struct" $
    JSONDecode.map (curry mk_comb StructT_tm) $
      field "name" stringtm
]

val astValueType : term decoder = achoose "astValueType" [
  JSONDecode.map (fn t => mk_comb(Type_tm, t)) $
    astHmType
  (* TODO: add HashMapT *)
]

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
  tuple2 (
    field "target" $
    check_ast_type "Name" $
    field "id" stringtm,
    field "annotation" astType)

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
  JSONDecode.map (fn ls =>
    mk_list(List.filter (equal toplevel_ty o type_of) ls, toplevel_ty)
  ) (array toplevel)

val abiBaseType : term decoder =
  JSONDecode.map parse_abi_type string

fun d_abiType () : term decoder = achoose "abiType" [
  check_field "type" "tuple" $
    JSONDecode.map (curry mk_comb abiTuple_tm o
                    (curry $ flip mk_list) abi_type_ty) $
    field "components" (array (delay d_abiType)),
  field "type" abiBaseType
]
val abiType = delay d_abiType

val abiArg : term decoder =
  JSONDecode.map mk_pair $
  tuple2 (field "name" stringtm, abiType)

val abiMutability : term decoder =
  andThen (fn s =>
    if s = "nonpayable" then succeed Nonpayable_tm else
    if s = "view" then succeed View_tm else
    if s = "payable" then succeed Payable_tm else
    fail ("abiMutability: " ^ s)) string

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
    check_field "type" "event" $
    JSONDecode.map (fn s => mk_comb(Event_tm, s)) $
    field "name" stringtm
  ]

val Deployment_tm = prim_mk_const{Thy="vyperTestRunner",Name="Deployment"}
val deployment_trace_ty = #1 $ dom_rng $ type_of Deployment_tm

val SetBalance_tm = prim_mk_const{Thy="vyperTestRunner",Name="SetBalance"}
val ClearTransientStorage_tm =
  prim_mk_const{Thy="vyperTestRunner",Name="ClearTransientStorage"}

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

fun read_test_json json_path = let
  val test_jsons = decodeFile rawObject json_path
in
  List.foldl trydecode ([],[]) test_jsons
end

val trace_ty = mk_thy_type{Thy="vyperTestRunner",Tyop="trace",Args=[]}
val run_test_tm = prim_mk_const{Thy="vyperTestRunner",Name="run_test"}

fun run_test ((name, traces),(s,f)) = let
  val trs = mk_list(traces, trace_ty)
  val ttm = mk_comb(run_test_tm, trs)
  val () = Feedback.HOL_MESG ("Testing " ^ name)
  val eth = cv_eval ttm
  val pass = sumSyntax.is_inl $ rhs $ concl eth
  val () = Feedback.HOL_MESG (if pass then "Passed" else "Failed")
in
  if pass then (name::s,f) else (s,name::f)
end

val run_tests = List.foldl run_test ([],[])

val test_files = [
  "test_address_balance.json",
  "test_clampers.json",
  "test_logging_bytes_extended.json",
  "test_memory_dealloc.json",
  "test_string_map_keys.json",
  "test_assert.json",
  "test_comments.json",
  "test_exports.json",
  "test_logging_from_call.json",
  "test_packing.json",
  "test_ternary.json",
  "test_assert_unreachable.json",
  "test_comparison.json",
  "test_gas.json",
  "test_logging.json",
  "test_reverting.json",
  "test_transient.json",
  "test_assignment.json",
  "test_conditionals.json",
  "test_immutable.json",
  "test_mana.json",
  "test_selfdestruct.json",
  "test_bytes_map_keys.json",
  "test_constructor.json",
  "test_init.json",
  "test_memory_alloc.json",
  "test_short_circuiting.json"
]

(*

  val json_path = el 1 test_files
  val (tests, []) = read_test_json json_path
  val (passes, []) = run_tests tests

  val json_path = el 2 test_files
  val (tests, []) = read_test_json json_path
  val (tests1, tests2) = List.partition (String.isPrefix "test_multidimension" o #1) tests
  val (passes, fails) = run_tests tests2
  (* TODO: treat flags as structs better *)
  val SOME (name, traces) = List.find (equal (el 1 fails) o #1) tests
  (* TODO: test_multidimension tests too slow... *)

  val json_path = el 3 test_files
  val (tests, []) = read_test_json json_path
  val (passes, []) = run_tests tests

  val json_path = el 4 test_files
  val (tests, [extcall]) = read_test_json json_path
  (* unsupported: external call *)
  val true = String.isSubstring "extcall" $
             decode (field "source_code" string) (#2(#2 extcall))
  val (passes, []) = run_tests tests

  val json_path = el 5 test_files
  val (tests, []) = read_test_json json_path
  val (passes, []) = run_tests tests

  val json_path = el 6 test_files
  val (tests, [raw_call, proxy, static_call]) = read_test_json json_path
  (* unsupported: raw_call *)
  val true = String.isSubstring "raw_call" $
             decode (field "source_code" string) (#2(#2 raw_call))
  (* unsupported: create_minimal_proxy_to *)
  val true = String.isSubstring "create_minimal_proxy_to" $
             decode (field "source_code" string) (#2(#2 proxy))
  (* unsupported: static external call *)
  val true = String.isSubstring "staticcall" $
             decode (field "source_code" string) (#2(#2 static_call))
  val (passes, []) = run_tests tests

  val json_path = el 7 test_files
  val (tests, []) = read_test_json json_path
  val (passes, []) = run_tests tests

  val json_path = el 8 test_files
  val (tests, [exports]) = read_test_json json_path
  (* unsupported: exports *)
  val true = String.isSubstring "exports" $
             decode (field "source_code" string) (#2(#2 exports))
  val (passes, []) = run_tests tests

  val json_path = el 9 test_files
  val (tests, []) = read_test_json json_path
  val (passes, []) = run_tests tests

  val json_path = el 10 test_files
  val (tests, []) = read_test_json json_path
  val (passes, []) = run_tests tests

  val json_path = el 11 test_files
  val (tests, []) = read_test_json json_path
  val (passes, []) = run_tests tests

  val json_path = el 12 test_files
  val (tests, []) = read_test_json json_path
  val (passes, []) = run_tests tests

  val json_path = el 13 test_files
  val (tests, []) = read_test_json json_path
  val (passes, []) = run_tests tests

  val json_path = el 14 test_files
  val (tests, []) = read_test_json json_path
  val (passes, [msg_gas]) = run_tests tests

  val json_path = el 15 test_files
  val (tests, raw_logs) = read_test_json json_path
  val true = List.all (fn (_,(_,j)) =>
    String.isSubstring "raw_log" $
    decode (field "source_code" string) j) raw_logs
  val (passes, [block_timestamp1, block_timestamp2]) = run_tests tests
  (* TODO: block.timestamp builtin
  val SOME (_, traces) = List.find (equal block_timestamp1 o #1) tests
  *)

  val json_path = el 16 test_files
  val (tests, [raw_revert1, raw_revert2, raw_revert3]) = read_test_json json_path
  val true = String.isSubstring "raw_revert" $
             decode (field "source_code" string) (#2(#2 raw_revert1))
  val true = String.isSubstring "raw_revert" $
             decode (field "source_code" string) (#2(#2 raw_revert2))
  val true = String.isSubstring "raw_revert" $
             decode (field "source_code" string) (#2(#2 raw_revert3))
  val (passes, []) = run_tests tests

  val json_path = el 17 test_files
  val (tests, df) = read_test_json json_path
  (* unsupported: import *)
  val df2 = List.filter (fn (_,(_,j)) => not $
    String.isSubstring "import" $
    decode (field "source_code" string) j) df
  (* unsupported staticcall *)
  val true = List.all (fn (_,(_, j)) =>
    String.isSubstring "staticcall" $
    decode (field "source_code" string) j) df2
  val (passes, []) = run_tests tests

  val json_path = el 18 test_files
  (* TODO: decode pop *)
  val (tests, [TODO_pop, extcall1, extcall2, staticcall1]) = read_test_json json_path
  val true = String.isSubstring "pop" $
             decode (field "source_code" string) (#2(#2 TODO_pop))
  val true = String.isSubstring "extcall" $
             decode (field "source_code" string) (#2(#2 extcall1))
  val true = String.isSubstring "extcall" $
             decode (field "source_code" string) (#2(#2 extcall2))
  val true = String.isSubstring "staticcall" $
             decode (field "source_code" string) (#2(#2 staticcall1))
  val (passes, [TODO_fail]) = run_tests tests
  (* TODO
  val SOME (name, traces) = List.find (equal TODO_fail o #1) tests
  *)

  val json_path = el 19 test_files
  val (tests, [raw_call]) = read_test_json json_path
  val true = String.isSubstring "raw_call" $
             decode (field "source_code" string) (#2(#2 raw_call))
  val (passes, []) = run_tests tests

  val json_path = el 20 test_files
  val (tests, [TODO_raw_init_code, create_copy_of]) = read_test_json json_path
  val true = decode (field "source_code" (null true)) (#2(#2 TODO_raw_init_code))
  val true = String.isSubstring "create_copy_of" $
             decode (field "source_code" string) (#2(#2 create_copy_of))
  val (passes, []) = run_tests tests

  val json_path = el 21 test_files
  val (tests, []) = read_test_json json_path
  (* msg.mana unsupported *)
  val (passes, [TODO_msg_mana]) = run_tests tests

  val json_path = el 22 test_files
  val (tests, [selfdestruct1, selfdestruct2]) = read_test_json json_path
  val (passes, []) = run_tests tests

  val json_path = el 23 test_files
  val (tests, []) = read_test_json json_path
  val (passes, []) = run_tests tests

  val json_path = el 24 test_files
  val (tests, []) = read_test_json json_path
  val (passes, []) = run_tests tests

  val json_path = el 25 test_files
  val (tests, []) = read_test_json json_path
  val (passes, []) = run_tests tests

  val json_path = el 26 test_files
  val (tests, []) = read_test_json json_path
  val (passes, []) = run_tests tests

  val json_path = el 27 test_files
  val (tests, []) = read_test_json json_path
  val (passes, []) = run_tests tests

  val (_, (_, tr)) = el 1 df
  val (name, json) = el 133 test_jsons
  trydecode $ (el 133 test_jsons, ([],[]))

  val test_jsons = decodeFile rawObject json_path
  val (name, json) = el 3 test_jsons
  val traces = decode (field "traces" (array trace)) json
  val traces = decode (field "traces" (array raw)) json
  val tr = el 1 traces
  decode (field "contract_abi" (array abiEntry)) tr
  val cabi = decode (field "contract_abi" (array raw)) tr
  decode (field "name" stringtm) (el 2 cabi)
  val tr = decode trace tr

  val tls = decode (field "annotated_ast" (field "ast" (field "body" (array raw)))) tr
  val tl = el 2 tls
  decode toplevel tl
  decode (field "target" (field "type" (field "key_type" astHmType))) tl
  decode (field "ast_type" string) tl
  decode (field "annotation" astType) tl

  val ags = decode (field "body" (array raw)) tl
  decode (field "annotation" astType) (el 2 ags)
  print $ decode (field "source_code" string )tr

  decode (field "args" (field "args" (array (field "annotation" raw)))) tl

  val stmts = decode (field "body" statements) tl
  val stmts = decode (field "body" (array raw)) tl

  val stmt = el 1 stmts
  decode statement stmt
  decode (field "ast_type" string) stmt

  val expr = decode (field "value" expression) stmt
  val expr = decode (field "value" raw) stmt
  decode (field "ast_type" string) expr
  el 1 $ decode (field "elements" (array raw)) $ el 2 $ decode (field "elements" (array raw)) $ el 2 $ decode (field "elements" (array raw)) expr


  decode (field "annotation" (field "slice" astType)) stmt
  decode (field "annotation" astType) stmt
  decode (field "target" raw) stmt
  val tgt = decode (field "target" baseAssignmentTarget) stmt

  decode (field "ast_type" string) expr
  decode (field "op" binop) expr
  val expr = decode (field "left" raw) expr
  val kwds = decode (field "keywords" (array raw)) expr
  decode (field "arg" string) $ el 1 kwds
  decode (field "value" raw) $ el 1 kwds


  decode (field "slice" raw) expr
  val expr = decode (field "body" raw) expr

  decode (field "func" raw) expr
  val ags = decode (field "args" (array raw)) expr
  decode expression expr
  val decoder =
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
    )
  decode expression $ el 3 $
  decode (field "args" (array expression)) (el 1 ags)
  decode (field "func" raw) (el 1 ags)
  decode expression (el 1 ags)


  decode (field "orelse" expression) expr
  val expr = decode (field "orelse" raw) expr
  val expr = decode (field "right" raw) expr

  decode (field "target" (field "ast_type" string)) stmt
  decode (field "target" (field "slice" raw)) stmt

  val expr = decode (field "msg" raw) stmt

  decode (field "body" statements) stmt
  decode statement stmt

  val stmts = decode (field "body" (array raw)) stmt
  val stmt = el 1 stmts
  decode (field "value" (field "keywords" (array (field "value" raw)))) stmt
  val expr = decode (field "test" raw) stmt
  decode (field "right" expression) expr
  decode expression expr

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

  val (name, traces) = el 1 tests

  traces

cv_eval “let
  trs = ^trs;
  am = initial_machine_state;
  snss = [];
  tr = HD trs;
  (snss, res) = run_trace snss am tr;
  am = OUTL res;
  trs = TL trs;
  tr = HD trs;
  (snss, res) = run_trace snss am tr;
  am = OUTL res;
  trs = TL trs;
  tr = HD trs;
  ct = case tr of Call ct => ct;
  snsx = ALOOKUP snss ct.target;
  sns = THE snsx;
  cr = run_call sns am ct;
  call_res = FST cr;
  am = SND call_res;
  rets = SND cr;
  abiRetTys = FST rets;
  abiRetTy = Tuple abiRetTys;
  rawVyRetTy = SND rets;
  alreadyTuple = (rawVyRetTy = NoneT ∨ is_TupleT rawVyRetTy);
  vyRetTy = if alreadyTuple then rawVyRetTy
            else TupleT [rawVyRetTy];
  fna = THE $ ALOOKUP sns (TAKE 4 ct.callData);
    name = FST fna; argTys = FST (SND fna);
  ts = THE $ ALOOKUP am.sources ct.target;
  ar = compute_vyper_args ts name argTys (DROP 4 ct.callData)
in (ar, name, ts) ”

  vyRetTy = if is_TupleT rawVyRetTy
    then rawVyRetTy else TupleT [rawVyRetTy];
in (abiRetTy, vyRetTy)”

  abiRetTy = Tuple abiRetTys;
  vyRetTy = SND rets;
  out = THE ct.expectedOutput;
  abiret = dec abiRetTy out;
  vyret = abi_to_vyper (TupleT [vyRetTy]) abiret;
in (FST call_res, abiRetTy, vyRetTy, out, abiret, vyret)”

cv_eval “enc String (BytesV [119w; 111w; 114w; 108w; 100w])”

*)

end
