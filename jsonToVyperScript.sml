Theory jsonToVyper
Ancestors
  jsonAST vyperAST
Libs
  cv_transLib intLib

(* ===== Type Translation ===== *)

(* Define mutual recursion to handle lists explicitly *)
Definition translate_type_def:
  (translate_type (JT_Integer bits T) = BaseT (IntT bits)) /\
  (translate_type (JT_Integer bits F) = BaseT (UintT bits)) /\
  (translate_type (JT_BytesM m) = BaseT (BytesT (Fixed m))) /\
  (translate_type (JT_String n) = BaseT (StringT n)) /\
  (translate_type (JT_Bytes n) = BaseT (BytesT (Dynamic n))) /\
  (translate_type (JT_StaticArray vt len) = ArrayT (translate_type vt) (Fixed len)) /\
  (translate_type (JT_DynArray vt len) = ArrayT (translate_type vt) (Dynamic len)) /\
  (translate_type (JT_Struct name) = StructT name) /\
  (translate_type (JT_Flag name) = FlagT name) /\
  (translate_type (JT_Tuple tys) = TupleT (translate_type_list tys)) /\
  (translate_type (JT_HashMap _ _) = NoneT) /\
  (translate_type JT_None = NoneT) /\
  (translate_type (JT_Named name) =
     if name = "bool" then BaseT BoolT
     else if name = "address" then BaseT AddressT
     else if name = "decimal" then BaseT DecimalT
     else StructT name) /\
  (translate_type_list [] = []) /\
  (translate_type_list (t::ts) = translate_type t :: translate_type_list ts)
Termination
  WF_REL_TAC `measure (\x. case x of
    | INL t => json_type_size t
    | INR ts => list_size json_type_size ts)` >> simp[]
End

val () = cv_auto_trans translate_type_def;

(* ===== Helper: int_bound from type ===== *)

Definition int_bound_of_type_def:
  (int_bound_of_type (JT_Integer bits T) = Signed bits) /\
  (int_bound_of_type (JT_Integer bits F) = Unsigned bits) /\
  (int_bound_of_type _ = Unsigned 256)
End

val () = cv_auto_trans int_bound_of_type_def;

(* ===== Operator Translation ===== *)

Definition translate_binop_def:
  (translate_binop JBop_Add = Add) /\
  (translate_binop JBop_Sub = Sub) /\
  (translate_binop JBop_Mult = Mul) /\
  (translate_binop JBop_Div = Div) /\
  (translate_binop JBop_FloorDiv = Div) /\
  (translate_binop JBop_Mod = Mod) /\
  (translate_binop JBop_Pow = Exp) /\
  (translate_binop JBop_And = And) /\
  (translate_binop JBop_Or = Or) /\
  (translate_binop JBop_BitAnd = And) /\
  (translate_binop JBop_BitOr = Or) /\
  (translate_binop JBop_BitXor = XOr) /\
  (translate_binop JBop_LShift = ShL) /\
  (translate_binop JBop_RShift = ShR) /\
  (translate_binop JBop_Eq = Eq) /\
  (translate_binop JBop_NotEq = NotEq) /\
  (translate_binop JBop_Lt = Lt) /\
  (translate_binop JBop_LtE = LtE) /\
  (translate_binop JBop_Gt = Gt) /\
  (translate_binop JBop_GtE = GtE) /\
  (translate_binop JBop_In = In) /\
  (translate_binop JBop_NotIn = NotIn)
End

val () = cv_auto_trans translate_binop_def;

(* ===== Hex String to Word8 List Conversion ===== *)

Definition hex_digit_to_num_def:
  hex_digit_to_num c =
    if c = #"0" then 0n else
    if c = #"1" then 1 else
    if c = #"2" then 2 else
    if c = #"3" then 3 else
    if c = #"4" then 4 else
    if c = #"5" then 5 else
    if c = #"6" then 6 else
    if c = #"7" then 7 else
    if c = #"8" then 8 else
    if c = #"9" then 9 else
    if c = #"a" \/ c = #"A" then 10 else
    if c = #"b" \/ c = #"B" then 11 else
    if c = #"c" \/ c = #"C" then 12 else
    if c = #"d" \/ c = #"D" then 13 else
    if c = #"e" \/ c = #"E" then 14 else
    if c = #"f" \/ c = #"F" then 15 else 0
End

val () = cv_auto_trans hex_digit_to_num_def;

Definition hex_pair_to_word8_def:
  hex_pair_to_word8 hi lo = n2w (hex_digit_to_num hi * 16 + hex_digit_to_num lo) : word8
End

val () = cv_auto_trans hex_pair_to_word8_def;

Definition hex_string_to_bytes_def:
  (hex_string_to_bytes [] = []) /\
  (hex_string_to_bytes [_] = []) /\
  (hex_string_to_bytes (hi::lo::rest) = hex_pair_to_word8 hi lo :: hex_string_to_bytes rest)
Termination
  WF_REL_TAC `measure LENGTH` >> simp[]
End

val () = cv_auto_trans hex_string_to_bytes_def;

Definition strip_0x_def:
  (strip_0x [] = []) /\
  (strip_0x [c] = [c]) /\
  (strip_0x (c1::c2::rest) =
     if c1 = #"0" /\ (c2 = #"x" \/ c2 = #"X")
     then rest
     else c1::c2::rest)
End

val () = cv_auto_trans strip_0x_def;

(* ===== BoolOp Helpers ===== *)
(* These work on vyper expr lists (post-translation) *)

Definition boolop_and_def:
  (boolop_and [] = Literal (BoolL T)) /\
  (boolop_and [e] = e) /\
  (boolop_and (e::es) = IfExp e (boolop_and es) (Literal (BoolL F)))
Termination
  WF_REL_TAC `measure LENGTH` >> simp[]
End

val () = cv_auto_trans boolop_and_def;

Definition boolop_or_def:
  (boolop_or [] = Literal (BoolL F)) /\
  (boolop_or [e] = e) /\
  (boolop_or (e::es) = IfExp e (Literal (BoolL T)) (boolop_or es))
Termination
  WF_REL_TAC `measure LENGTH` >> simp[]
End

val () = cv_auto_trans boolop_or_def;

(* ===== Builtin Call Helper (non-recursive, defined before translate_expr) ===== *)
(* This takes already-translated args and kwargs *)

Definition make_builtin_call_def:
  make_builtin_call name args kwargs ret_ty =
    if name = "len" then Builtin Len args
    else if name = "concat" then
      (case ret_ty of JT_String n => Builtin (Concat n) args
                    | JT_Bytes n => Builtin (Concat n) args
                    | _ => Builtin (Concat 0) args)
    else if name = "slice" then
      (case ret_ty of JT_String n => Builtin (Slice n) args
                    | JT_Bytes n => Builtin (Slice n) args
                    | _ => Builtin (Slice 0) args)
    else if name = "keccak256" then Builtin Keccak256 args
    else if name = "floor" then Builtin Floor args
    else if name = "ceil" then Builtin Ceil args
    else if name = "blockhash" then Builtin BlockHash args
    else if name = "empty" then TypeBuiltin Empty (translate_type ret_ty) []
    else if name = "max_value" then TypeBuiltin MaxValue (translate_type ret_ty) []
    else if name = "min_value" then TypeBuiltin MinValue (translate_type ret_ty) []
    else if name = "convert" then
      (case args of (arg::_) => TypeBuiltin Convert (translate_type ret_ty) [arg]
                  | _ => TypeBuiltin Convert (translate_type ret_ty) [])
    else if name = "unsafe_add" then Builtin (Bop UAdd) args
    else if name = "unsafe_sub" then Builtin (Bop USub) args
    else if name = "unsafe_mul" then Builtin (Bop UMul) args
    else if name = "unsafe_div" then Builtin (Bop UDiv) args
    else if name = "addmod" then Builtin AddMod args
    else if name = "mulmod" then Builtin MulMod args
    else if name = "min" then Builtin (Bop Min) args
    else if name = "max" then Builtin (Bop Max) args
    else if name = "send" then Call Send args
    else if name = "uint2str" then
      (case ret_ty of JT_String n => Builtin (Uint2Str n) args
                    | _ => Builtin (Uint2Str 0) args)
    (* Struct constructor or regular call *)
    else (case ret_ty of
          | JT_Struct _ => StructLit name kwargs
          | _ => Call (IntCall name) args)
End

val () = cv_auto_trans make_builtin_call_def;

(* ===== Expression Translation ===== *)

Definition translate_expr_def:
  (translate_expr (JE_Int v ty) =
    Literal (IntL (int_bound_of_type ty) v)) /\

  (translate_expr (JE_Decimal s) =
    Literal (DecimalL (integer$int_of_num 0))) /\

  (translate_expr (JE_Str len s) =
    Literal (StringL len s)) /\

  (translate_expr (JE_Bytes len hex) =
    Literal (BytesL (Dynamic len) (hex_string_to_bytes (strip_0x hex)))) /\

  (translate_expr (JE_Hex hex) =
    let bytes = hex_string_to_bytes (strip_0x hex) in
    Literal (BytesL (Fixed (LENGTH bytes)) bytes)) /\

  (translate_expr (JE_Bool b) = Literal (BoolL b)) /\

  (translate_expr (JE_Name id) =
    if id = "self" then Builtin (Env SelfAddr) [] else Name id) /\

  (* Special attributes: msg.*, block.*, tx.*, self.* *)
  (translate_expr (JE_Attribute (JE_Name obj) attr) =
    if obj = "msg" /\ attr = "sender" then Builtin (Env Sender) []
    else if obj = "msg" /\ attr = "value" then Builtin (Env ValueSent) []
    else if obj = "block" /\ attr = "timestamp" then Builtin (Env TimeStamp) []
    else if obj = "block" /\ attr = "number" then Builtin (Env BlockNumber) []
    else if obj = "block" /\ attr = "prevhash" then Builtin (Env PrevHash) []
    else if obj = "block" /\ attr = "blobbasefee" then Builtin (Env BlobBaseFee) []
    else if obj = "tx" /\ attr = "gasprice" then Builtin (Env GasPrice) []
    else if obj = "self" then TopLevelName attr
    else Attribute (Name obj) attr) /\

  (* General attribute *)
  (translate_expr (JE_Attribute e attr) =
    Attribute (translate_expr e) attr) /\

  (* Subscript *)
  (translate_expr (JE_Subscript arr idx) =
    Subscript (translate_expr arr) (translate_expr idx)) /\

  (* BinOp *)
  (translate_expr (JE_BinOp l op r) =
    Builtin (Bop (translate_binop op)) [translate_expr l; translate_expr r]) /\

  (* BoolOp - convert to nested IfExp *)
  (translate_expr (JE_BoolOp JBoolop_And es) =
    boolop_and (translate_expr_list es)) /\
  (translate_expr (JE_BoolOp JBoolop_Or es) =
    boolop_or (translate_expr_list es)) /\

  (* UnaryOp *)
  (translate_expr (JE_UnaryOp JUop_USub e) =
    Builtin Neg [translate_expr e]) /\
  (translate_expr (JE_UnaryOp JUop_Not e) =
    Builtin Not [translate_expr e]) /\
  (translate_expr (JE_UnaryOp JUop_Invert e) =
    Builtin Not [translate_expr e]) /\

  (* IfExp (ternary) *)
  (translate_expr (JE_IfExp test body orelse) =
    IfExp (translate_expr test) (translate_expr body) (translate_expr orelse)) /\

  (* Tuple *)
  (translate_expr (JE_Tuple es) =
    Builtin (MakeArray NONE (Fixed (LENGTH es))) (translate_expr_list es)) /\

  (* List - array literal *)
  (translate_expr (JE_List es ty) =
    case ty of
    | JT_StaticArray vt len =>
        Builtin (MakeArray (SOME (translate_type vt)) (Fixed len)) (translate_expr_list es)
    | JT_DynArray vt len =>
        Builtin (MakeArray (SOME (translate_type vt)) (Dynamic len)) (translate_expr_list es)
    | _ =>
        Builtin (MakeArray NONE (Fixed (LENGTH es))) (translate_expr_list es)) /\

  (* Call - single case with internal dispatch to avoid pattern completion issues *)
  (translate_expr (JE_Call func args kwargs ret_ty) =
    let args' = translate_expr_list args in
    let kwargs' = translate_kwargs kwargs in
    case func of
    | JE_Name name => make_builtin_call name args' kwargs' ret_ty
    | JE_Attribute (JE_Name "self") fname => Call (IntCall fname) args'
    | _ => Call (IntCall "") args') /\

  (* Helper for translating expression lists *)
  (translate_expr_list [] = []) /\
  (translate_expr_list (e::es) = translate_expr e :: translate_expr_list es) /\

  (* Helper for translating keywords *)
  (translate_kwargs [] = []) /\
  (translate_kwargs (JKeyword k v :: rest) = (k, translate_expr v) :: translate_kwargs rest)
End

(* Skip cv_auto_trans for translate_expr - cv_auto doesn't handle mutual recursion well *)
(* val () = cv_auto_trans translate_expr_def; *)

(* ===== Assignment Target Translation ===== *)
(* Defined after translate_expr since it uses it for subscript indices *)

Definition translate_base_target_def:
  (translate_base_target (JBT_Name id) = NameTarget id) /\
  (translate_base_target (JBT_TopLevelName id) = TopLevelNameTarget id) /\
  (translate_base_target (JBT_Subscript tgt idx) =
    SubscriptTarget (translate_base_target tgt) (translate_expr idx)) /\
  (translate_base_target (JBT_Attribute tgt attr) =
    AttributeTarget (translate_base_target tgt) attr)
Termination
  WF_REL_TAC `measure json_base_target_size` >> simp[]
End

(* Skip cv_auto_trans for functions that depend on translate_expr *)
(* val () = cv_auto_trans translate_base_target_def; *)

Definition translate_target_def:
  (translate_target (JTgt_Base bt) = BaseTarget (translate_base_target bt)) /\
  (translate_target (JTgt_Tuple tgts) = TupleTarget (MAP translate_target tgts))
Termination
  WF_REL_TAC `measure json_target_size` >> simp[]
End

(* val () = cv_auto_trans translate_target_def; *)

(* ===== Iterator Translation ===== *)

Definition get_iter_bound_def:
  (get_iter_bound (JIter_Range args (SOME n)) = n) /\
  (get_iter_bound (JIter_Range _ NONE) = 0n) /\
  (get_iter_bound (JIter_Array _ (JT_StaticArray _ len)) = len) /\
  (get_iter_bound (JIter_Array _ (JT_DynArray _ len)) = len) /\
  (get_iter_bound (JIter_Array _ _) = 0)
End

val () = cv_auto_trans get_iter_bound_def;

Definition translate_iter_def:
  (translate_iter var_ty (JIter_Range [] _) =
    Range (Literal (IntL (int_bound_of_type var_ty) (integer$int_of_num 0)))
          (Literal (IntL (int_bound_of_type var_ty) (integer$int_of_num 0)))) /\
  (translate_iter var_ty (JIter_Range [e] _) =
    Range (Literal (IntL (int_bound_of_type var_ty) (integer$int_of_num 0)))
          (translate_expr e)) /\
  (translate_iter var_ty (JIter_Range (s::e::_) _) =
    Range (translate_expr s) (translate_expr e)) /\
  (translate_iter var_ty (JIter_Array e _) =
    Array (translate_expr e))
End

(* val () = cv_auto_trans translate_iter_def; *)

(* ===== Statement Translation ===== *)

Definition translate_stmt_def:
  (translate_stmt JS_Pass = Pass) /\
  (translate_stmt JS_Break = Break) /\
  (translate_stmt JS_Continue = Continue) /\
  (translate_stmt (JS_Expr e) = Expr (translate_expr e)) /\
  (translate_stmt (JS_Return NONE) = Return NONE) /\
  (translate_stmt (JS_Return (SOME e)) = Return (SOME (translate_expr e))) /\
  (translate_stmt (JS_Raise NONE) = Raise (Literal (StringL 0 ""))) /\
  (translate_stmt (JS_Raise (SOME e)) = Raise (translate_expr e)) /\
  (translate_stmt (JS_Assert test NONE) =
    Assert (translate_expr test) (Literal (StringL 0 ""))) /\
  (translate_stmt (JS_Assert test (SOME msg)) =
    Assert (translate_expr test) (translate_expr msg)) /\
  (translate_stmt (JS_Log event args) =
    Log event (MAP translate_expr args)) /\
  (translate_stmt (JS_If test body orelse) =
    If (translate_expr test)
       (MAP translate_stmt body)
       (MAP translate_stmt orelse)) /\
  (translate_stmt (JS_For var ty iter body) =
    For var (translate_type ty) (translate_iter ty iter)
        (get_iter_bound iter) (MAP translate_stmt body)) /\
  (translate_stmt (JS_Assign tgt val) =
    Assign (translate_target tgt) (translate_expr val)) /\
  (translate_stmt (JS_AnnAssign var ty val) =
    AnnAssign var (translate_type ty) (translate_expr val)) /\
  (translate_stmt (JS_AugAssign tgt op val) =
    AugAssign (translate_base_target tgt) (translate_binop op) (translate_expr val)) /\
  (translate_stmt (JS_Append tgt val) =
    Append (translate_base_target tgt) (translate_expr val))
Termination
  WF_REL_TAC `measure json_stmt_size` >>
  rw[] >> simp[json_stmt_size_def]
End

(* val () = cv_auto_trans translate_stmt_def; *)

(* ===== Top-level Translation ===== *)

Definition translate_visibility_def:
  translate_visibility decs =
    if MEM "external" decs then External
    else if MEM "deploy" decs then Deploy
    else Internal
End

(* val () = cv_auto_trans translate_visibility_def; *)

Definition translate_mutability_def:
  translate_mutability decs =
    if MEM "pure" decs then Pure
    else if MEM "view" decs then View
    else if MEM "payable" decs then Payable
    else Nonpayable
End

(* val () = cv_auto_trans translate_mutability_def; *)

Definition translate_arg_def:
  translate_arg (JArg name ty) = (name, translate_type ty)
End

val () = cv_auto_trans translate_arg_def;

Definition translate_value_type_def:
  (translate_value_type (JVT_Type ty) = Type (translate_type ty)) /\
  (translate_value_type (JVT_HashMap key_ty val_ty) =
    HashMapT (translate_type key_ty) (translate_value_type val_ty))
Termination
  WF_REL_TAC `measure json_value_type_size` >> simp[]
End

val () = cv_auto_trans translate_value_type_def;

Definition translate_var_mutability_def:
  translate_var_mutability is_immutable is_transient is_constant const_val =
    if is_immutable then Immutable
    else if is_transient then Transient
    else if is_constant then
      (case const_val of
         SOME e => Constant (translate_expr e)
       | NONE => Storage)
    else Storage
End

(* val () = cv_auto_trans translate_var_mutability_def; *)

Definition translate_toplevel_def:
  (translate_toplevel (JTL_FunctionDef name decs args (JFuncType arg_tys ret_ty) body) =
    SOME (FunctionDecl
      (translate_visibility decs)
      (translate_mutability decs)
      name
      (MAP translate_arg args)
      (translate_type ret_ty)
      (MAP translate_stmt body))) /\

  (translate_toplevel (JTL_VariableDecl name ty is_public is_immutable is_transient const_val) =
    SOME (VariableDecl
      (if is_public then Public else Private)
      (translate_var_mutability is_immutable is_transient
        (case const_val of SOME _ => T | NONE => F) const_val)
      name
      (translate_type ty))) /\

  (translate_toplevel (JTL_HashMapDecl name key_ty val_ty is_public is_transient) =
    SOME (HashMapDecl
      (if is_public then Public else Private)
      is_transient
      name
      (translate_type key_ty)
      (translate_value_type val_ty))) /\

  (translate_toplevel (JTL_EventDef name args) =
    SOME (EventDecl name (MAP translate_arg args))) /\

  (translate_toplevel (JTL_StructDef name args) =
    SOME (StructDecl name (MAP translate_arg args))) /\

  (translate_toplevel (JTL_FlagDef name members) =
    SOME (FlagDecl name members)) /\

  (translate_toplevel (JTL_InterfaceDef _) = NONE)
End

(* val () = cv_auto_trans translate_toplevel_def; *)

(* ===== Module Translation ===== *)

Definition filter_some_def:
  (filter_some [] = []) /\
  (filter_some (NONE :: rest) = filter_some rest) /\
  (filter_some (SOME x :: rest) = x :: filter_some rest)
End

val () = cv_auto_trans filter_some_def;

Definition translate_module_def:
  translate_module (JModule toplevels) =
    filter_some (MAP translate_toplevel toplevels)
End

(* val () = cv_auto_trans translate_module_def; *)

