Theory jsonToVyper
Ancestors
  integer alist jsonAST vyperAST
Libs
  cv_transLib intLib
  integerTheory[qualified]


(* Vyper uses negative source_ids for builtin modules (e.g., -2 for math).
   We add this offset to convert source_ids to non-negative nums.
   If Vyper adds more builtin modules, this value may need to increase. *)
Definition builtin_source_id_offset_def:
  builtin_source_id_offset = 2n
End
val () = cv_trans_deep_embedding EVAL builtin_source_id_offset_def;

(* Convert a JSON source_id (int) to a vyperAST source_id (num option).
   -1 maps to NONE (main module), others are offset to be non-negative. *)
Definition source_id_to_nsid_def:
  source_id_to_nsid (src_id:int) =
    if src_id = -1 then NONE
    else SOME (Num (src_id + &builtin_source_id_offset))
End
val () = cv_auto_trans source_id_to_nsid_def;

Definition json_nsid_to_nsid_def:
  json_nsid_to_nsid (src_id:int, name:string) =
    (source_id_to_nsid src_id, name) : nsid
End
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

(* ===== Decimal String Parsing ===== *)

Definition is_digit_def:
  is_digit c =
    (c = #"0" \/ c = #"1" \/ c = #"2" \/ c = #"3" \/ c = #"4" \/
     c = #"5" \/ c = #"6" \/ c = #"7" \/ c = #"8" \/ c = #"9")
End

val () = cv_auto_trans is_digit_def;

Definition digit_to_num_def:
  digit_to_num c =
    if c = #"0" then 0n else
    if c = #"1" then 1 else
    if c = #"2" then 2 else
    if c = #"3" then 3 else
    if c = #"4" then 4 else
    if c = #"5" then 5 else
    if c = #"6" then 6 else
    if c = #"7" then 7 else
    if c = #"8" then 8 else
    if c = #"9" then 9 else 0
End

val () = cv_auto_trans digit_to_num_def;

Definition num_of_digits_acc_def:
  (num_of_digits_acc acc [] = acc) /\
  (num_of_digits_acc acc (c::cs) =
     num_of_digits_acc (acc * 10 + digit_to_num c) cs)
End

val () = cv_auto_trans num_of_digits_acc_def;

Definition num_of_digits_def:
  num_of_digits cs = num_of_digits_acc 0 cs
End

val () = cv_auto_trans num_of_digits_def;

Definition strip_sign_def:
  (strip_sign [] = (F, [])) /\
  (strip_sign (c::cs) =
     if c = #"-" then (T, cs)
     else if c = #"+" then (F, cs)
     else (F, c::cs))
End

val () = cv_auto_trans strip_sign_def;

Definition drop_nondigit_def:
  (drop_nondigit [] = []) /\
  (drop_nondigit (c::cs) =
     if is_digit c then (c::cs) else drop_nondigit cs)
End

val () = cv_auto_trans drop_nondigit_def;

Definition split_at_e_def:
  (split_at_e [] = ([], [])) /\
  (split_at_e (c::cs) =
     if c = #"e" \/ c = #"E" then ([], cs)
     else let (l, r) = split_at_e cs in (c::l, r))
End

val () = cv_auto_trans split_at_e_def;

Definition split_at_dot_def:
  (split_at_dot [] = ([], [])) /\
  (split_at_dot (c::cs) =
     if c = #"." then ([], cs)
     else let (l, r) = split_at_dot cs in (c::l, r))
End

val () = cv_auto_trans split_at_dot_def;

Definition pad_right_zeros_def:
  pad_right_zeros n xs =
    if LENGTH xs < n then xs ++ REPLICATE (n - LENGTH xs) #"0" else xs
End

val () = cv_auto_trans pad_right_zeros_def;

Definition decimal_string_to_int_def:
  decimal_string_to_int s =
    let (base, exp) = split_at_e s in
    let (neg_exp, exp_rest) = strip_sign exp in
    let exp_digits = FILTER is_digit exp_rest in
    let exp_num = num_of_digits exp_digits in
    let exp_int = if neg_exp then &0 - &exp_num else &exp_num in
    let (bd, ad) = split_at_dot base in
    let target = &10 + exp_int in
    let pad_len =
      if target <= & (LENGTH ad) then LENGTH ad else Num target in
    let ad' = pad_right_zeros pad_len ad in
    let ds = bd ++ ad' in
    let (neg, ds_rest) = strip_sign ds in
    let digits = FILTER is_digit ds_rest in
    let n = num_of_digits digits in
      if neg then &0 - &n else &n
End

val () = cv_auto_trans decimal_string_to_int_def;

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

Definition is_prefix_def:
  (is_prefix [] _ = T) /\
  (is_prefix _ [] = F) /\
  (is_prefix (p::ps) (s::ss) = ((p = s) /\ is_prefix ps ss))
End

val () = cv_auto_trans is_prefix_def;

Definition is_capitalized_def:
  (is_capitalized [] = F) /\
  (is_capitalized (c::cs) = (#"A" <= c /\ c <= #"Z"))
End

val () = cv_auto_trans is_capitalized_def;

Definition is_cast_name_def:
  is_cast_name name =
    (is_capitalized name \/
     is_prefix "uint" name \/
     is_prefix "int" name \/
     is_prefix "bytes" name \/
     name = "decimal" \/
     name = "bool" \/
     name = "address")
End

val () = cv_auto_trans is_cast_name_def;

Definition is_builtin_cast_name_def:
  is_builtin_cast_name name =
    (is_prefix "uint" name \/ is_prefix "Uint" name \/
     is_prefix "int" name \/ is_prefix "Int" name \/
     is_prefix "bytes" name \/ is_prefix "Bytes" name \/
     name = "decimal" \/ name = "Decimal" \/
     name = "bool" \/ name = "Bool" \/
     name = "address" \/ name = "Address")
End

val () = cv_auto_trans is_builtin_cast_name_def;

Definition denomination_of_string_def:
  denomination_of_string s =
    if s = "wei" then SOME Wei else
    if s = "kwei" then SOME Kwei else
    if s = "mwei" then SOME Mwei else
    if s = "gwei" then SOME Gwei else
    if s = "szabo" then SOME Szabo else
    if s = "finney" then SOME Finney else
    if s = "ether" then SOME Ether else
    if s = "kether" then SOME KEther else
    if s = "mether" then SOME MEther else
    if s = "gether" then SOME GEther else
    if s = "tether" then SOME TEther else NONE
End

val () = cv_auto_trans denomination_of_string_def;

Definition denomination_of_expr_def:
  denomination_of_expr (Literal (StringL _ s)) = denomination_of_string s /\
  denomination_of_expr _ = NONE
End

val () = cv_auto_trans denomination_of_expr_def;

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
    else if name = "blobhash" then Builtin BlobHash args
    else if name = "isqrt" then Builtin Isqrt args
    else if name = "ecrecover" then Builtin ECRecover args
    else if name = "ecadd" then Builtin ECAdd args
    else if name = "ecmul" then Builtin ECMul args
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
    else if name = "uint256_addmod" then Builtin AddMod args
    else if name = "uint256_mulmod" then Builtin MulMod args
    else if name = "pow_mod256" then Builtin PowMod256 args
    else if name = "min" then Builtin (Bop Min) args
    else if name = "max" then Builtin (Bop Max) args
    else if name = "send" then Call Send args NONE
    else if name = "as_wei_value" then
      (case args of
         (v::d::_) =>
           (case denomination_of_expr d of
              SOME dn => Builtin (AsWeiValue dn) [v]
            | NONE => Builtin (AsWeiValue Wei) [v])
       | (v::_) => Builtin (AsWeiValue Wei) [v]
       | _ => Builtin (AsWeiValue Wei) [])
    else if name = "uint2str" then
      (case ret_ty of JT_String n => Builtin (Uint2Str n) args
                    | _ => Builtin (Uint2Str 0) args)
    else if name = "abi_decode" then
      TypeBuiltin AbiDecode (translate_type ret_ty) args
    else if name = "abi_encode" then
      TypeBuiltin AbiEncode (translate_type ret_ty) args
    else if name = "method_id" then
      Builtin MethodId args
    (* Struct constructor, cast, or regular call *)
    else (case ret_ty of
          | JT_Struct _ => StructLit (NONE, name) kwargs
          | JT_Named _ =>
              if kwargs <> [] /\ ~is_builtin_cast_name name then
                StructLit (NONE, name) kwargs
              else
                if is_cast_name name then
                  let ty' = translate_type ret_ty in
                    if is_builtin_cast_name name then
                      (case ty' of
                         BaseT _ =>
                           (case args of
                              (arg::_) => TypeBuiltin Convert ty' [arg]
                            | _ => TypeBuiltin Convert ty' [])
                       | _ =>
                           (case args of
                              (arg::_) => arg
                            | _ => Call (IntCall (NONE, name)) args NONE))
                    else
                      (case args of
                         (arg::_) => arg
                       | _ => Call (IntCall (NONE, name)) args NONE)
                else Call (IntCall (NONE, name)) args NONE
          | _ =>
              if is_cast_name name then
                let ty' = translate_type ret_ty in
                  if is_builtin_cast_name name then
                    (case ty' of
                       BaseT _ =>
                         (case args of
                            (arg::_) => TypeBuiltin Convert ty' [arg]
                          | _ => TypeBuiltin Convert ty' [])
                     | _ =>
                         (case args of
                            (arg::_) => arg
                          | _ => Call (IntCall (NONE, name)) args NONE))
                  else
                    (case args of
                       (arg::_) => arg
                     | _ => Call (IntCall (NONE, name)) args NONE)
              else Call (IntCall (NONE, name)) args NONE)
End

val () = cv_auto_trans make_builtin_call_def;

(* ===== Module Call Helpers ===== *)

(* Extract function name from a func expression *)
(* For JE_Attribute base fname, returns fname *)
Definition extract_func_name_def:
  (extract_func_name (JE_Attribute _ fname _ _) = fname) /\
  (extract_func_name (JE_Name name _ _) = name) /\
  (extract_func_name _ = "")
End

val () = cv_auto_trans extract_func_name_def;

(* Extract the innermost module's source_id from a module chain *)
(* For lib1: returns SOME 0 (from JE_Name) *)
(* For lib1.lib2: returns SOME 1 (from the .lib2 Attribute) *)
Definition extract_innermost_module_src_def:
  (* Attribute with module typeclass has source_id directly *)
  (extract_innermost_module_src (JE_Attribute _ _ (SOME tc) src_id_opt) =
    if tc = "module" then SOME src_id_opt else NONE) /\
  (* JE_Name with module typeclass *)
  (extract_innermost_module_src (JE_Name _ (SOME tc) src_id_opt) =
    if tc = "module" then SOME src_id_opt else NONE) /\
  (* Other cases *)
  (extract_innermost_module_src _ = NONE)
End

val () = cv_auto_trans extract_innermost_module_src_def;

(* Detect cross-module flag member pattern: lib1.Action.BUY or lib1.lib2.Roles3.NOBODY *)
(* Returns SOME (src_id_opt, flag_name) if it matches, NONE otherwise *)
(* e is the expression immediately under the flag member attribute (i.e., the flag type expression) *)
(* For lib1.Roles.ADMIN: e = JE_Attribute (JE_Name "lib1"...) "Roles" _ _ *)
(* For lib1.lib2.Roles3.NOBODY: e = JE_Attribute (JE_Attribute ... "lib2" (SOME "module") (SOME 1)) "Roles3" _ _ *)
Definition extract_module_flag_def:
  (* Attribute expression for the flag type - look inside for the module *)
  (extract_module_flag (JE_Attribute inner flag_name _ _) =
    case extract_innermost_module_src inner of
    | SOME src_id => SOME (source_id_to_nsid src_id, flag_name)
    | NONE => NONE) /\
  (extract_module_flag _ = NONE)
End

val () = cv_auto_trans extract_module_flag_def;

(* ===== Expression Translation ===== *)

(* Find a keyword by name in a keyword list, returns the json_expr if found *)
Definition find_keyword_def:
  find_keyword name [] = NONE ∧
  find_keyword name (JKeyword kw_name kw_val :: rest) =
    if kw_name = name then SOME kw_val
    else find_keyword name rest
End

val () = cv_auto_trans find_keyword_def;

(* Lemma: if find_keyword returns SOME v, then v is in the keyword list *)
Theorem find_keyword_MEM:
  ∀name kws v. find_keyword name kws = SOME v ⇒ ∃k. MEM (JKeyword k v) kws
Proof
  Induct_on `kws` >> rw[find_keyword_def] >>
  Cases_on `h` >> gvs[find_keyword_def] >>
  Cases_on `s = name` >> gvs[] >>
  metis_tac[]
QED

(* Size lemma for termination: keyword value is smaller than keyword list *)
Theorem find_keyword_size:
  ∀name kws v.
    find_keyword name kws = SOME v ⇒
    json_expr_size v < list_size json_keyword_size kws
Proof
  Induct_on `kws` >> rw[find_keyword_def] >>
  Cases_on `h` >> gvs[find_keyword_def, json_expr_size_def] >>
  Cases_on `s = name` >> gvs[json_expr_size_def] >>
  res_tac >> gvs[]
QED

Definition translate_expr_def:
  (translate_expr (JE_Int v ty) =
    Literal (IntL (int_bound_of_type ty) v)) /\

  (translate_expr (JE_Decimal s) =
    Literal (DecimalL (decimal_string_to_int s))) /\

  (translate_expr (JE_Str len s) =
    Literal (StringL len s)) /\

  (translate_expr (JE_Bytes len hex) =
    Literal (BytesL (Dynamic len) (hex_string_to_bytes (strip_0x hex)))) /\

  (translate_expr (JE_Hex hex) =
    let bytes = hex_string_to_bytes (strip_0x hex) in
    Literal (BytesL (Fixed (LENGTH bytes)) bytes)) /\

  (translate_expr (JE_Bool b) = Literal (BoolL b)) /\

  (translate_expr (JE_Name id tc src_id_opt) =
    if id = "self" then Builtin (Env SelfAddr) [] else Name id) /\

  (* Special attributes: msg.*, block.*, tx.*, self.*, module.*, flag members *)
  (* attr_src_id_opt is from variable_reads on the outer Attribute (for self.x storage access) *)
  (translate_expr (JE_Attribute (JE_Name obj tc src_id_opt) attr result_tc attr_src_id_opt) =
    (* Same-module flag member: Action.BUY where tc = SOME "flag" *)
    if tc = SOME "flag" /\ result_tc = SOME "flag" then FlagMember (source_id_to_nsid src_id_opt, obj) attr
    else if obj = "msg" /\ attr = "sender" then Builtin (Env Sender) []
    else if obj = "msg" /\ attr = "value" then Builtin (Env ValueSent) []
    else if obj = "block" /\ attr = "timestamp" then Builtin (Env TimeStamp) []
    else if obj = "block" /\ attr = "number" then Builtin (Env BlockNumber) []
    else if obj = "block" /\ attr = "prevhash" then Builtin (Env PrevHash) []
    else if obj = "block" /\ attr = "blobbasefee" then Builtin (Env BlobBaseFee) []
    else if obj = "tx" /\ attr = "gasprice" then Builtin (Env GasPrice) []
    else if obj = "self" /\ attr = "balance" then
      Builtin (Acc Balance) [Builtin (Env SelfAddr) []]
    (* self.x: use attr_src_id_opt from variable_reads for cross-module storage access *)
    else if obj = "self" then TopLevelName (source_id_to_nsid attr_src_id_opt, attr)
    (* Module variable access (lib1.x): use src_id_opt from module type *)
    else if tc = SOME "module" then TopLevelName (source_id_to_nsid src_id_opt, attr)
    else if attr = "balance" then Builtin (Acc Balance) [Name obj]
    else if attr = "address" then Builtin (Acc Address) [Name obj]
    else Attribute (Name obj) attr) /\

  (* General attribute - handles nested and simple cases *)
  (* Check for cross-module flag access: lib1.Action.BUY *)
  (translate_expr (JE_Attribute e attr result_tc _) =
    if result_tc = SOME "flag" then
      case extract_module_flag e of
      | SOME (src_id_opt, flag_name) => FlagMember (src_id_opt, flag_name) attr
      | NONE => Attribute (translate_expr e) attr
    else if attr = "balance" then Builtin (Acc Balance) [translate_expr e]
    else if attr = "address" then Builtin (Acc Address) [translate_expr e]
    else Attribute (translate_expr e) attr) /\

  (* Subscript *)
  (translate_expr (JE_Subscript arr idx) =
    Subscript (translate_expr arr) (translate_expr idx)) /\

  (* NamedExpr - only appears in initializes:/uses: annotations, not in executable code *)
  (translate_expr (JE_NamedExpr target value) =
    Literal (BoolL T)) /\

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
  (* JE_Call now includes source_id for module calls *)
  (translate_expr (JE_Call func args kwargs ret_ty src_id_opt) =
    let args' = translate_expr_list args in
    let kwargs' = translate_kwargs kwargs in
    case func of
    | JE_Name name (SOME "interface") _ => HD args'
    | JE_Name name _ _ => make_builtin_call name args' kwargs' ret_ty
    (* lib.__at__(addr) - interface instantiation, just returns the address *)
    | JE_Attribute _ "__at__" _ _ => HD args'
    | JE_Attribute base "pop" _ _ =>
        (case base of
         | JE_Name id _ _ => Pop (NameTarget id)
         | JE_Attribute (JE_Name "self" _ _) attr _ _ => Pop (TopLevelNameTarget (NONE, attr))
         | JE_Attribute (JE_Name id (SOME "module") src_id_opt) attr _ _ =>
             Pop (TopLevelNameTarget (source_id_to_nsid src_id_opt, attr))
         | JE_Attribute (JE_Name id _ _) attr _ _ =>
             Pop (AttributeTarget (NameTarget id) attr)
         | JE_Subscript (JE_Name id _ _) idx =>
             Pop (SubscriptTarget (NameTarget id) (translate_expr idx))
         | _ => Call (IntCall (NONE, "pop")) args' NONE)
    (* self.func(args) - internal call *)
    | JE_Attribute (JE_Name "self" _ _) fname _ _ => Call (IntCall (NONE, fname)) args' NONE
    (* Module struct constructor or module function call *)
    | _ => let nsid = source_id_to_nsid src_id_opt;
               fname = extract_func_name func in
           (case ret_ty of
              JT_Struct sname =>
                if fname = sname then
                  (* Struct constructor: library.SomeStruct(x=2) *)
                  let mod_nsid = case func of
                      JE_Attribute base _ _ _ =>
                        (case extract_innermost_module_src base of
                           SOME sid => source_id_to_nsid sid
                         | NONE => nsid)
                    | _ => nsid in
                  StructLit (mod_nsid, fname) kwargs'
                else
                  (* Function call that returns a struct: library.foo() *)
                  Call (IntCall (nsid, fname)) args' NONE
            | _ =>
              (* Module call: use source_id from type_decl_node *)
              Call (IntCall (nsid, fname)) args' NONE)) /\

  (* ExtCall - mutating external call (is_static = F) *)
  (* Convention: args = [target; value; arg1; arg2; ...] *)
  (translate_expr (JE_ExtCall func_name arg_types ret_ty args keywords) =
    let value_expr = case find_keyword "value" keywords of
                     | SOME v => translate_expr v
                     | NONE => Literal (IntL (Unsigned 256) 0) in
    let translated_args = translate_expr_list args in
    Call (ExtCall F (func_name, translate_type_list arg_types, translate_type ret_ty))
         (case translated_args of
          | (target :: rest) => target :: value_expr :: rest
          | [] => [])
         (OPTION_MAP translate_expr (find_keyword "default_return_value" keywords))) /\

  (* StaticCall - read-only external call (is_static = T) *)
  (* Convention: args = [target; arg1; arg2; ...] (no value) *)
  (translate_expr (JE_StaticCall func_name arg_types ret_ty args) =
    Call (ExtCall T (func_name, translate_type_list arg_types, translate_type ret_ty))
         (translate_expr_list args)
         NONE) /\

  (* Helper for translating expression lists *)
  (translate_expr_list [] = []) /\
  (translate_expr_list (e::es) = translate_expr e :: translate_expr_list es) /\

  (* Helper for translating keywords *)
  (translate_kwargs [] = []) /\
  (translate_kwargs (JKeyword k v :: rest) = (k, translate_expr v) :: translate_kwargs rest)
Termination
  WF_REL_TAC `measure (λx. case x of
    | INL e => json_expr_size e
    | INR (INL es) => list_size json_expr_size es
    | INR (INR kws) => list_size json_keyword_size kws)`
  >> rw[]
  >> imp_res_tac find_keyword_size
  >> gvs[]
End

(* Skip cv_auto_trans for translate_expr - cv_auto doesn't handle mutual recursion well *)
(* val () = cv_auto_trans translate_expr_def; *)

(* ===== Assignment Target Translation ===== *)
(* Defined after translate_expr since it uses it for subscript indices *)

Definition translate_base_target_def:
  (translate_base_target (JBT_Name id) = NameTarget id) /\
  (* JBT_TopLevelName is (source_id, name) for self.x and module.x *)
  (translate_base_target (JBT_TopLevelName nsid) = TopLevelNameTarget (json_nsid_to_nsid nsid)) /\
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

Definition json_expr_int_opt_def:
  (json_expr_int_opt (JE_Int v _) = SOME v) /\
  (json_expr_int_opt (JE_UnaryOp JUop_USub e) =
     case json_expr_int_opt e of
       SOME n => SOME (0 - n)
     | NONE => NONE) /\
  (json_expr_int_opt (JE_BinOp l JBop_Add r) =
     case (json_expr_int_opt l, json_expr_int_opt r) of
       (SOME n1, SOME n2) => SOME (n1 + n2)
     | _ => NONE) /\
  (json_expr_int_opt (JE_BinOp l JBop_Sub r) =
     case (json_expr_int_opt l, json_expr_int_opt r) of
       (SOME n1, SOME n2) => SOME (n1 - n2)
     | _ => NONE) /\
  (json_expr_int_opt _ = NONE)
End

val () = cv_auto_trans json_expr_int_opt_def;

Definition range_bound_of_args_def:
  (range_bound_of_args [] = NONE) /\
  (range_bound_of_args [e] =
     case json_expr_int_opt e of
       SOME n => if 0 <= n then SOME (Num n) else SOME 0
     | NONE => NONE) /\
  (range_bound_of_args (s::e::_) =
     case (json_expr_int_opt s, json_expr_int_opt e) of
       (SOME s', SOME e') =>
         if s' <= e' then SOME (Num (e' - s')) else SOME 0
     | _ => NONE)
End

val () = cv_auto_trans range_bound_of_args_def;

Definition get_iter_bound_def:
  (get_iter_bound (JIter_Range args (SOME n)) = n) /\
  (get_iter_bound (JIter_Range args NONE) =
     case range_bound_of_args args of SOME n => n | NONE => 0) /\
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
    Log (json_nsid_to_nsid event) (MAP translate_expr args)) /\
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

Definition translate_interface_func_def:
  translate_interface_func (JInterfaceFunc name args ret_ty decs) =
    (name,
     MAP translate_arg args,
     translate_type ret_ty,
     translate_mutability decs) : interface_func
End

(* val () = cv_auto_trans translate_interface_func_def; *)

Definition translate_args_with_types_def:
  translate_args_with_types args tys =
    case (args, tys) of
      ([], []) => []
    | (JArg name _ :: args', ty :: tys') =>
        (name, translate_type ty) ::
        translate_args_with_types args' tys'
    | _ => MAP translate_arg args
End

val () = cv_auto_trans translate_args_with_types_def;

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
  (translate_toplevel (JTL_FunctionDef name decs args defaults (JFuncType arg_tys ret_ty) body) =
    SOME (FunctionDecl
      (translate_visibility decs)
      (translate_mutability decs)
      name
      (translate_args_with_types args arg_tys)
      (MAP translate_expr defaults)
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

  (translate_toplevel (JTL_InterfaceDef name funcs) =
    SOME (InterfaceDecl name (MAP translate_interface_func funcs))) /\

  (* Module declarations are compiled away - the imported content is already inlined *)
  (translate_toplevel (JTL_Import _) = NONE) /\
  (translate_toplevel (JTL_ExportsDecl _) = NONE) /\
  (translate_toplevel (JTL_InitializesDecl _) = NONE) /\
  (translate_toplevel (JTL_UsesDecl _) = NONE) /\
  (translate_toplevel (JTL_ImplementsDecl _) = NONE)
End

(* val () = cv_auto_trans translate_toplevel_def; *)

(* ===== Exports Extraction ===== *)

(* Build alias -> source_id map from import info list *)
Definition build_import_map_def:
  build_import_map [] = [] ∧
  build_import_map (JImportInfo alias src_id _ :: rest) =
    (alias, Num (src_id + &builtin_source_id_offset)) :: build_import_map rest
End

val () = cv_auto_trans build_import_map_def;

(* Extract import infos from a toplevel (returns list since JTL_Import has list) *)
Definition get_import_infos_def:
  get_import_infos (JTL_Import infos) = infos ∧
  get_import_infos _ = []
End

val () = cv_auto_trans get_import_infos_def;

(* Collect all import infos from toplevels *)
Definition collect_imports_def:
  collect_imports [] = [] ∧
  collect_imports (t::ts) = get_import_infos t ++ collect_imports ts
End

val () = cv_auto_trans collect_imports_def;

(* Extract source_ids that a module depends on from its body *)
Definition get_module_deps_def:
  get_module_deps body =
    MAP (λinfo. case info of JImportInfo _ src_id _ => src_id) (collect_imports body)
End

val () = cv_auto_trans get_module_deps_def;

(* Check if imports are topologically sorted (dependencies come before dependents).
   seen: list of source_ids already processed
   Returns T if sorted, F otherwise. *)
Definition imports_topsorted_def:
  imports_topsorted seen [] = T ∧
  imports_topsorted seen (JImportedModule src_id _ body :: rest) =
    let deps = get_module_deps body in
    if EVERY (λd. MEM d seen) deps
    then imports_topsorted (src_id :: seen) rest
    else F
End

(* ===== Storage Layout Key Transformation ===== *)
(* Transform storage layout keys from (alias_opt, var_name) to (source_id_opt, var_name).
   Uses import_map to convert alias to source_id. *)

(* Transform a single storage layout key.
   (NONE, "counter") -> (NONE, "counter")  -- main module
   (SOME "lib1", "counter") -> (SOME 0, "counter")  -- if import_map has ("lib1", 0) *)
Definition transform_layout_key_def:
  transform_layout_key import_map (alias_opt, var_name) =
    case alias_opt of
    | NONE => (NONE, var_name)  (* Main module variable *)
    | SOME alias =>
        case ALOOKUP import_map alias of
        | NONE => (NONE, var_name)  (* Unknown alias, treat as main module *)
        | SOME src_id => (SOME src_id, var_name)
End

val () = cv_auto_trans transform_layout_key_def;

(* Transform all keys in a storage layout *)
Definition transform_storage_layout_def:
  transform_storage_layout import_map [] = [] ∧
  transform_storage_layout import_map ((key, slot) :: rest) =
    (transform_layout_key import_map key, slot) ::
    transform_storage_layout import_map rest
End

val () = cv_auto_trans transform_storage_layout_def;

(* Check if a function decl is external *)
Definition is_external_function_def:
  is_external_function (JTL_FunctionDef _ decs _ _ _ _) = MEM "external" decs ∧
  is_external_function _ = F
End

(* Get function name from a function decl *)
Definition get_function_name_def:
  get_function_name (JTL_FunctionDef name _ _ _ _ _) = SOME name ∧
  get_function_name _ = NONE
End

(* Get all external function names from a module's toplevels *)
Definition get_external_func_names_def:
  get_external_func_names [] = [] ∧
  get_external_func_names (t::ts) =
    if is_external_function t then
      case get_function_name t of
        SOME name => name :: get_external_func_names ts
      | NONE => get_external_func_names ts
    else get_external_func_names ts
End

(* Find module body by source_id in imports list *)
Definition find_module_body_def:
  find_module_body src_id [] = [] ∧
  find_module_body src_id (JImportedModule sid _ body :: rest) =
    if src_id = sid then body else find_module_body src_id rest
End

(* Get export annotation from a toplevel if it's an ExportsDecl *)
Definition get_export_annotation_def:
  get_export_annotation (JTL_ExportsDecl ann) = SOME ann ∧
  get_export_annotation _ = NONE
End

(* ===== Exports Extraction with Transitive Support =====

   When main has `exports: lib2.__interface__`, we need lib2's full exports,
   which includes lib2's external functions PLUS anything lib2 re-exports.

   Design: Build an exports_map by processing imports in topological order.
   When we see `lib.__interface__`, we look up lib's exports in the map.

   The imports list must be topologically sorted (leaf modules first, modules
   depending on them later). This is validated by imports_topsorted in
   translate_annotated_ast, which returns NONE if the ordering is invalid.
*)

(* Build a map from source_id to import_map for all imported modules *)
Definition build_all_import_maps_def:
  build_all_import_maps [] = [] ∧
  build_all_import_maps (JImportedModule src_id _ body :: rest) =
    let nsid = Num (src_id + &builtin_source_id_offset) in
    (nsid, build_import_map (collect_imports body)) ::
    build_all_import_maps rest
End

(* Resolve a module expression (possibly nested) to a source_id.
   e.g. lib1 -> SOME src_id_of_lib1
        lib2.lib1 -> SOME src_id_of_lib1 (via lib2's import_map)
   all_import_maps: source_id -> import_map for each module
   import_map: current module's alias -> source_id map *)
Definition resolve_module_expr_def:
  (resolve_module_expr all_import_maps import_map (JE_Name alias _ _) =
     ALOOKUP import_map alias) ∧
  (resolve_module_expr all_import_maps import_map (JE_Attribute inner alias _ _) =
     case resolve_module_expr all_import_maps import_map inner of
     | NONE => NONE
     | SOME parent_src_id =>
         case ALOOKUP all_import_maps parent_src_id of
         | NONE => NONE
         | SOME parent_import_map => ALOOKUP parent_import_map alias) ∧
  (resolve_module_expr _ _ _ = NONE)
Termination
  WF_REL_TAC `measure (λ(_,_,e). json_expr_size e)` >> simp[]
End

(* Expand a single export expression using pre-computed exports_map.
   exports_map: source_id -> list of (func_name, source_id) exports
   all_import_maps: source_id -> import_map for each module
   import_map: alias -> source_id for the current module's imports *)
Definition expand_single_export_def:
  expand_single_export exports_map all_import_maps import_map (JE_Attribute base func_name _ _) =
    (case resolve_module_expr all_import_maps import_map base of
     | NONE => []
     | SOME src_id =>
         if func_name = "__interface__" then
           case ALOOKUP exports_map src_id of
           | NONE => []
           | SOME exps => exps
         else
           (* Check if the function is re-exported from another module *)
           case ALOOKUP exports_map src_id of
           | SOME exps =>
               (case ALOOKUP exps func_name of
                | SOME final_src_id => [(func_name, final_src_id)]
                | NONE => [(func_name, src_id)])
           | NONE => [(func_name, src_id)]) ∧
  expand_single_export _ _ _ _ = []
End

(* Expand exports from a tuple of export expressions *)
Definition expand_tuple_exports_def:
  expand_tuple_exports exports_map all_import_maps import_map [] = [] ∧
  expand_tuple_exports exports_map all_import_maps import_map (e::es) =
    expand_single_export exports_map all_import_maps import_map e ++
    expand_tuple_exports exports_map all_import_maps import_map es
End

(* Expand exports from an ExportsDecl annotation *)
Definition expand_export_annotation_def:
  expand_export_annotation exports_map all_import_maps import_map (JE_Tuple exprs) =
    expand_tuple_exports exports_map all_import_maps import_map exprs ∧
  expand_export_annotation exports_map all_import_maps import_map (JE_Attribute base attr tc sid) =
    expand_single_export exports_map all_import_maps import_map (JE_Attribute base attr tc sid) ∧
  expand_export_annotation _ _ _ _ = []
End

(* Expand all exports from a module's toplevels *)
Definition expand_exports_from_toplevels_def:
  expand_exports_from_toplevels exports_map all_import_maps import_map [] = [] ∧
  expand_exports_from_toplevels exports_map all_import_maps import_map (t::ts) =
    (case get_export_annotation t of
     | SOME ann => expand_export_annotation exports_map all_import_maps import_map ann
     | NONE => []) ++
    expand_exports_from_toplevels exports_map all_import_maps import_map ts
End

(* Compute a single module's full exports: its external functions + expanded re-exports *)
Definition compute_module_exports_def:
  compute_module_exports exports_map all_import_maps src_id body =
    let ext_funcs = MAP (λn. (n, src_id)) (get_external_func_names body) in
    let import_map = build_import_map (collect_imports body) in
    let reexports = expand_exports_from_toplevels exports_map all_import_maps import_map body in
    ext_funcs ++ reexports
End

(* Build exports_map by processing imports in topological order.
   Requires: imports list is topologically sorted (validated by imports_topsorted).
   This ensures when we process module M, any module M references via
   __interface__ has already been added to the accumulator. *)
Definition build_exports_map_def:
  build_exports_map all_import_maps acc [] = acc ∧
  build_exports_map all_import_maps acc (JImportedModule src_id _ body :: rest) =
    let nsid = Num (src_id + &builtin_source_id_offset) in
    let exps = compute_module_exports acc all_import_maps nsid body in
    build_exports_map all_import_maps ((nsid, exps) :: acc) rest
End

(* Main function: extract exports from main module given imports *)
Definition extract_exports_def:
  extract_exports (JModule toplevels) imports =
    let all_import_maps = build_all_import_maps imports in
    let exports_map = build_exports_map all_import_maps [] imports in
    let import_map = build_import_map (collect_imports toplevels) in
    expand_exports_from_toplevels exports_map all_import_maps import_map toplevels
End

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

Definition translate_imported_module_def:
  translate_imported_module (JImportedModule src_id path body) =
    (SOME (Num (src_id + &builtin_source_id_offset)), filter_some (MAP translate_toplevel body))
End

(* Extract toplevels from a JModule (needed to get import infos) *)
Definition main_toplevels_def:
  main_toplevels (JModule toplevels) = toplevels
End

val () = cv_auto_trans main_toplevels_def;

(* Translate annotated AST, returning:
   - sources: (source_id, toplevels) alist
   - exports: func_name -> source_id
   - import_map: alias -> source_id (for storage layout key transformation)
   Returns NONE if imports are not topologically sorted. *)
Definition translate_annotated_ast_def:
  translate_annotated_ast (JAnnotatedAST main imports) =
    if ¬imports_topsorted [] imports then NONE else
    let import_infos = collect_imports (main_toplevels main) in
    let import_map = build_import_map import_infos in
    let sources = (NONE, translate_module main) :: MAP translate_imported_module imports in
    let exports = extract_exports main imports in
    SOME (sources, exports, import_map)
End
