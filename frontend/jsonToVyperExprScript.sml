Theory jsonToVyperExpr
Ancestors
  ASCIInumbers integer alist jsonAST vyperAST jsonToVyperType vyperConstEval
  vyperOriginFold vyperPinFold
Libs
  intLib

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


(* ===== Hex String to Word8 List Conversion ===== *)

Definition hex_pair_to_word8_def:
  hex_pair_to_word8 hi lo = n2w (UNHEX hi * 16 + UNHEX lo) : word8
End


Definition hex_string_to_bytes_def:
  (hex_string_to_bytes [] = []) /\
  (hex_string_to_bytes [_] = []) /\
  (hex_string_to_bytes (hi::lo::rest) = hex_pair_to_word8 hi lo :: hex_string_to_bytes rest)
Termination
  WF_REL_TAC `measure LENGTH` >> simp[]
End


Definition strip_0x_def:
  (strip_0x [] = []) /\
  (strip_0x [c] = [c]) /\
  (strip_0x (c1::c2::rest) =
     if c1 = #"0" /\ (c2 = #"x" \/ c2 = #"X")
     then rest
     else c1::c2::rest)
End


(* ===== Decimal String Parsing ===== *)

Definition strip_sign_def:
  (strip_sign [] = (F, [])) /\
  (strip_sign (c::cs) =
     if c = #"-" then (T, cs)
     else if c = #"+" then (F, cs)
     else (F, c::cs))
End


Definition split_at_e_def:
  (split_at_e [] = ([], [])) /\
  (split_at_e (c::cs) =
     if c = #"e" \/ c = #"E" then ([], cs)
     else let (l, r) = split_at_e cs in (c::l, r))
End


Definition split_at_dot_def:
  (split_at_dot [] = ([], [])) /\
  (split_at_dot (c::cs) =
     if c = #"." then ([], cs)
     else let (l, r) = split_at_dot cs in (c::l, r))
End


Definition pad_right_zeros_def:
  pad_right_zeros n xs =
    if LENGTH xs < n then xs ++ REPLICATE (n - LENGTH xs) #"0" else xs
End


(* Parses an unsigned decimal literal ("1.5", "15e-10"); a leading sign is
   honoured too. *)
Definition decimal_literal_to_int_def:
  decimal_literal_to_int s : int =
    let (obj, exp) = split_at_e s in
    let (neg_exp, exp_rest) = strip_sign exp in
    let exp_digits = FILTER isDigit exp_rest in
    let exp_num = num_from_dec_string exp_digits in
    let exp_int : int = if neg_exp then &0 - &exp_num else &exp_num in
    let (bd, ad) = split_at_dot obj in
    let ad = FILTER isDigit ad in
    let target = &10 + exp_int in
    let pad_len =
      if target <= & (LENGTH ad) then LENGTH ad else Num target in
    let ad' = pad_right_zeros pad_len ad in
    let ds = bd ++ ad' in
    let (neg, ds_rest) = strip_sign ds in
    let digits = FILTER isDigit ds_rest in
    let n = num_from_dec_string digits in
      if neg then &0 - &n else &n
End


(* Python comments run from "#" to the end of the line. *)
Definition strip_comments_def:
  (strip_comments in_comment [] = []) /\
  (strip_comments in_comment (c::cs) =
     if c = #"\n" then c :: strip_comments F cs
     else if in_comment \/ c = #"#" then strip_comments T cs
     else c :: strip_comments F cs)
End


(* Splits off what precedes the first digit or ".", and says whether it holds
   an odd number of minus signs. *)
Definition split_sign_prefix_def:
  (split_sign_prefix [] = (F, [])) /\
  (split_sign_prefix (c::cs) =
     if isDigit c \/ c = #"." then (F, c::cs)
     else let (neg, r) = split_sign_prefix cs in
       ((if c = #"-" then ~neg else neg), r))
End


(* A Decimal node's value is its source span, which covers any unary minus
   signs Vyper folded into the literal and any comments between them:
   "--1.5", "-(-2.25)", "-( # note\n 3.0)". *)
Definition decimal_string_to_int_def:
  decimal_string_to_int s : int =
    let (neg, lit) = split_sign_prefix (strip_comments F s) in
    let n = decimal_literal_to_int lit in
      if neg then &0 - n else n
End


(* ===== BoolOp Helpers ===== *)
(* These work on vyper expr lists (post-translation) *)

Definition boolop_and_def:
  (boolop_and [] = Literal (BaseT BoolT) (BoolL T)) /\
  (boolop_and [e] = e) /\
  (boolop_and (e::es) = IfExp (BaseT BoolT) e (boolop_and es) (Literal (BaseT BoolT) (BoolL F)))
Termination
  WF_REL_TAC `measure LENGTH` >> simp[]
End


Definition boolop_or_def:
  (boolop_or [] = Literal (BaseT BoolT) (BoolL F)) /\
  (boolop_or [e] = e) /\
  (boolop_or (e::es) = IfExp (BaseT BoolT) e (Literal (BaseT BoolT) (BoolL T)) (boolop_or es))
Termination
  WF_REL_TAC `measure LENGTH` >> simp[]
End


(* ===== Builtin Call Helper (non-recursive, defined before translate_expr) ===== *)
(* This takes already-translated args and kwargs *)

Definition is_prefix_def:
  (is_prefix [] _ = T) /\
  (is_prefix _ [] = F) /\
  (is_prefix (p::ps) (s::ss) = ((p = s) /\ is_prefix ps ss))
End


Definition is_capitalized_def:
  (is_capitalized [] = F) /\
  (is_capitalized (c::cs) = (#"A" <= c /\ c <= #"Z"))
End


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


Definition is_builtin_cast_name_def:
  is_builtin_cast_name name =
    (is_prefix "uint" name \/ is_prefix "Uint" name \/
     is_prefix "int" name \/ is_prefix "Int" name \/
     is_prefix "bytes" name \/ is_prefix "Bytes" name \/
     name = "decimal" \/ name = "Decimal" \/
     name = "bool" \/ name = "Bool" \/
     name = "address" \/ name = "Address")
End


Definition denomination_of_string_def:
  denomination_of_string s =
    if s = "wei" then SOME Wei else
    if s = "kwei" then SOME Kwei else
    if s = "babbage" then SOME Kwei else
    if s = "femtoether" then SOME Kwei else
    if s = "mwei" then SOME Mwei else
    if s = "lovelace" then SOME Mwei else
    if s = "picoether" then SOME Mwei else
    if s = "gwei" then SOME Gwei else
    if s = "shannon" then SOME Gwei else
    if s = "nanoether" then SOME Gwei else
    if s = "szabo" then SOME Szabo else
    if s = "microether" then SOME Szabo else
    if s = "finney" then SOME Finney else
    if s = "milliether" then SOME Finney else
    if s = "ether" then SOME Ether else
    if s = "kether" then SOME KEther else
    if s = "grand" then SOME KEther else
    if s = "mether" then SOME MEther else
    if s = "gether" then SOME GEther else
    if s = "tether" then SOME TEther else NONE
End


Definition denomination_of_expr_def:
  denomination_of_expr (Literal _ (StringL s)) = denomination_of_string s /\
  denomination_of_expr _ = NONE
End


(* ===== Keyword Argument Helpers ===== *)

(* Compile-time keyword values (flags, max_outsize, method_id) are evaluated
   from their translated source expressions. *)
Definition pin_fold_value_def:
  pin_fold_value e =
    case origin_fold_value e of
    | Literal ty l => SOME (evaluate_literal l)
    | _ => NONE
End

Definition kwarg_bool_def:
  kwarg_bool key (kwargs : (identifier # expr) list) default =
    case OPTION_BIND (ALOOKUP kwargs key) pin_fold_value of
      SOME (BoolV b) => b
    | _ => default
End


Definition kwarg_num_def:
  kwarg_num key (kwargs : (identifier # expr) list) (default : num) =
    case OPTION_BIND (ALOOKUP kwargs key) pin_fold_value of
      SOME (IntV n) => if n >= 0 then Num n else default
    | _ => default
End


(* Extract expression kwarg with default *)
Definition kwarg_expr_def:
  kwarg_expr key (kwargs : (identifier # expr) list) default =
    case ALOOKUP kwargs key of
      SOME e => e
    | NONE => default
End



Definition kwarg_method_id_def:
  kwarg_method_id key (kwargs : (identifier # expr) list) =
    case OPTION_BIND (ALOOKUP kwargs key) pin_fold_value of
      SOME (BytesV bs) => if LENGTH bs = 4 then SOME bs else NONE
    | _ => NONE
End

(* Rejection marker for the total translator: the type checker rejects
   CalldataSlice 0 regardless of operands. *)
Definition rejected_expr_def:
  rejected_expr = Builtin (BaseT (BytesT (Dynamic 0))) (CalldataSlice 0) []
End

(* A call whose compile-time keyword does not evaluate is rejected rather
   than translated with the keyword's default. *)
Definition kwargs_checked_def:
  kwargs_checked (kwargs : (identifier # expr) list) e =
    if EVERY (λ(k,v). MEM k ["max_outsize"; "is_delegate_call";
                             "is_static_call"; "revert_on_failure";
                             "raw_args"; "unwrap_tuple"; "ensure_tuple";
                             "method_id"; "skip_contract_check"] ⇒
                      IS_SOME (pin_fold_value v)) kwargs
    then e else rejected_expr
End


(* The value=, gas= and default_return_value= operands of extcall/staticcall,
   in source order, which is the order Vyper evaluates them in. *)
Definition ext_call_kwargs_def:
  ext_call_kwargs ([] : (identifier # expr) list) = [] /\
  ext_call_kwargs ((k,e)::kes) =
    (if k = "value" then [(EKValue,e)]
     else if k = "gas" then [(EKGas,e)]
     else if k = "default_return_value" then [(EKDefault,e)]
     else []) ++ ext_call_kwargs kes
End

Definition raw_call_flags_of_kwargs_def:
  raw_call_flags_of_kwargs kwargs =
    <| rcf_max_outsize := kwarg_num "max_outsize" kwargs 0;
       rcf_is_delegate := kwarg_bool "is_delegate_call" kwargs F;
       rcf_is_static := kwarg_bool "is_static_call" kwargs F;
       rcf_revert_on_failure := kwarg_bool "revert_on_failure" kwargs T;
       rcf_kws := MAP FST (ext_call_kwargs kwargs) |>
End

(* Runtime operands remain in code-generation order.  Only supplied runtime
   keywords contribute indices, visited in their JSON/source order. *)
Definition create_keyword_order_def:
  create_keyword_order kind has_salt nargs (kwargs : (identifier # expr) list) =
    FLAT (MAP (\(key,e).
      if key = "value" then [1n]
      else if key = "salt" /\ has_salt then
        [if kind = RawCreate then nargs + 1 else 2]
      else if key = "code_offset" then
        (case kind of CreateFromBlueprint _ =>
           [if has_salt then 3 else 2] | _ => [])
      else []) kwargs)
End

Theorem create_keyword_order_examples:
  create_keyword_order CreateMinimalProxy T 1
    [("salt",s); ("revert_on_failure",r); ("value",v)] = [2;1] /\
  create_keyword_order CreateCopyOf F 1 [] = [] /\
  create_keyword_order (CreateFromBlueprint F) T 3
    [("code_offset",off); ("salt",s); ("value",v)] = [3;2;1] /\
  create_keyword_order (CreateFromBlueprint T) F 2
    [("raw_args",r); ("code_offset",off)] = [2] /\
  create_keyword_order RawCreate T 3
    [("salt",s); ("value",v)] = [4;1]
Proof
  simp[create_keyword_order_def]
QED

(* Replace a compile-time expression by the literal of its value. *)
Definition fold_constant_def:
  fold_constant e =
    case OPTION_BIND (eval_constant e) constant_literal of
    | SOME l => Literal (expr_type e) l
    | NONE => e
End

Definition fold_pin_constant_def:
  fold_pin_constant e =
    case origin_fold_value e of
    | Literal ty l => Literal ty l
    | _ => e
End

Theorem fold_pin_constant_type[simp]:
  expr_type (fold_pin_constant e) = expr_type e
Proof
  Cases_on `origin_fold_value e` >> simp[fold_pin_constant_def] >>
  metis_tac[origin_fold_value_type]
QED

(* An exponent or a shift amount is a compile-time value where Vyper folds
   it; the checker needs a literal (or unsigned) one. *)
Definition exponent_operand_def:
  exponent_operand op e =
    if op = JBop_Pow \/ op = JBop_LShift \/ op = JBop_RShift
    then fold_pin_constant e else e
End

Definition word_literal_def:
  word_literal (Literal (BaseT (IntT n)) (IntL i)) =
    (if 0 <= i then Literal (BaseT (UintT 256)) (IntL i)
     else Literal (BaseT (IntT n)) (IntL i)) /\
  word_literal e = e
End

Definition make_builtin_call_def:
  make_builtin_call ty name args kwargs ret_ty =
    if name = "len" then fold_pin_constant (Builtin ty Len args)
    else if name = "concat" then
      (case ret_ty of JT_String n => Builtin ty (Concat n) args
                    | JT_Bytes n => Builtin ty (Concat n) args
                    | _ => Builtin ty (Concat 0) args)
    else if name = "slice" then
      (* The length is a compile-time value when it can be: the checker
         bounds the result by a literal length. *)
      (let slice_args = (case args of [src; start; len] => [src; start; fold_pin_constant len]
                                    | _ => args) in
       case ret_ty of JT_String n => Builtin ty (Slice n) slice_args
                    | JT_Bytes n => Builtin ty (Slice n) slice_args
                    | _ => Builtin ty (Slice 0) slice_args)
    else if name = "keccak256" then fold_pin_constant (Builtin ty Keccak256 args)
    else if name = "sha256" then
      (let original = Builtin ty Sha256 args in
       let args' = MAP origin_fold_value args in
       case pin_literal_values args' of
       | SOME vs =>
           (case pin_fold_result ty original
              (evaluate_builtin empty_evaluation_context empty_accounts
                ty Sha256 (MAP expr_type args') vs) of
            | Literal lty l => Literal lty l
            | _ => original)
       | NONE => original)
    else if name = "floor" then fold_pin_constant (Builtin ty Floor args)
    else if name = "ceil" then fold_pin_constant (Builtin ty Ceil args)
    else if name = "blockhash" then Builtin ty BlockHash args
    else if name = "blobhash" then Builtin ty BlobHash args
    else if name = "ecrecover" then
      (* Vyper annotates a small literal v, r or s as int8; its value is the
         word the precompile reads, so it is typed uint256. *)
      Builtin ty ECRecover (case args of
                            | h :: vrs => h :: MAP word_literal vrs
                            | [] => [])
    else if name = "ecadd" then Builtin ty ECAdd args
    else if name = "ecmul" then Builtin ty ECMul args
    else if name = "empty" then TypeBuiltin ty Empty ty []
    else if name = "max_value" then fold_pin_constant (TypeBuiltin ty MaxValue ty [])
    else if name = "min_value" then fold_pin_constant (TypeBuiltin ty MinValue ty [])
    else if name = "epsilon" then fold_pin_constant (TypeBuiltin ty Epsilon ty [])
    else if name = "convert" then
      (case args of (arg::_) => TypeBuiltin ty Convert ty [arg]
                  | _ => TypeBuiltin ty Convert ty [])
    else if name = "unsafe_add" then Builtin ty (Bop UnsafeAdd) args
    else if name = "unsafe_sub" then Builtin ty (Bop UnsafeSub) args
    else if name = "unsafe_mul" then Builtin ty (Bop UnsafeMul) args
    else if name = "unsafe_div" then Builtin ty (Bop UnsafeDiv) args
    else if name = "uint256_addmod" then fold_pin_constant (Builtin ty AddMod args)
    else if name = "uint256_mulmod" then fold_pin_constant (Builtin ty MulMod args)
    else if name = "pow_mod256" then fold_pin_constant (Builtin ty PowMod256 args)
    else if name = "min" then fold_pin_constant (Builtin ty (Bop Min) args)
    else if name = "max" then fold_pin_constant (Builtin ty (Bop Max) args)
    (* send(to, value, gas=0): the gas operand follows the positional ones. *)
    else if name = "send" then
      (case ALOOKUP kwargs "gas" of
       | SOME g => Call ty (Send T) (args ++ [g]) NONE
       | NONE => Call ty (Send F) args NONE)
    (* ===== Chain interaction builtins ===== *)
    (* raw_call(to, data, max_outsize=0, gas=gas, value=0,
                is_delegate_call=F, is_static_call=F, revert_on_failure=T)
       Convention: args in Call = [to_addr; data_bytes] ++ the value=/gas=
       operands in source order *)
    else if name = "raw_call" then kwargs_checked kwargs (
      Call ty (RawCallTarget (raw_call_flags_of_kwargs kwargs))
        (args ++ MAP SND (ext_call_kwargs kwargs)) NONE)
    else if name = "raw_log" then Call ty RawLog args NONE
    else if name = "raw_revert" then Call ty RawRevert args NONE
    else if name = "selfdestruct" then Call ty SelfDestructTarget args NONE
    else if name = "create_minimal_proxy_to" ∨ name = "create_forwarder_to" then
      kwargs_checked kwargs (
      let rof = kwarg_bool "revert_on_failure" kwargs T in
      let value_e = kwarg_expr "value" kwargs (Literal (BaseT (UintT 256)) (IntL 0)) in
      let salt_opt = ALOOKUP kwargs "salt" in
      let salt_es = case salt_opt of NONE => [] | SOME salt_e => [salt_e] in
      Call ty (CreateTarget CreateMinimalProxy (IS_SOME salt_opt) rof
        (create_keyword_order CreateMinimalProxy (IS_SOME salt_opt) (LENGTH args) kwargs))
        (TAKE 1 args ++ [value_e] ++ salt_es) NONE)
    else if name = "create_copy_of" then kwargs_checked kwargs (
      let rof = kwarg_bool "revert_on_failure" kwargs T in
      let value_e = kwarg_expr "value" kwargs (Literal (BaseT (UintT 256)) (IntL 0)) in
      let salt_opt = ALOOKUP kwargs "salt" in
      let salt_es = case salt_opt of NONE => [] | SOME salt_e => [salt_e] in
      Call ty (CreateTarget CreateCopyOf (IS_SOME salt_opt) rof
        (create_keyword_order CreateCopyOf (IS_SOME salt_opt) (LENGTH args) kwargs))
        (TAKE 1 args ++ [value_e] ++ salt_es) NONE)
    else if name = "create_from_blueprint" then kwargs_checked kwargs (
      let rof = kwarg_bool "revert_on_failure" kwargs T in
      let raw_args_flag = kwarg_bool "raw_args" kwargs F in
      let value_e = kwarg_expr "value" kwargs (Literal (BaseT (UintT 256)) (IntL 0)) in
      let salt_opt = ALOOKUP kwargs "salt" in
      let salt_es = case salt_opt of NONE => [] | SOME salt_e => [salt_e] in
      let code_offset_e = kwarg_expr "code_offset" kwargs
        (Literal (BaseT (UintT 256)) (IntL 3)) in
      Call ty (CreateTarget (CreateFromBlueprint raw_args_flag) (IS_SOME salt_opt) rof
        (create_keyword_order (CreateFromBlueprint raw_args_flag)
          (IS_SOME salt_opt) (LENGTH args) kwargs))
        (TAKE 1 args ++ [value_e] ++ salt_es ++ [code_offset_e] ++ DROP 1 args) NONE)
    else if name = "raw_create" then kwargs_checked kwargs (
      let rof = kwarg_bool "revert_on_failure" kwargs T in
      let value_e = kwarg_expr "value" kwargs (Literal (BaseT (UintT 256)) (IntL 0)) in
      let salt_opt = ALOOKUP kwargs "salt" in
      let salt_es = case salt_opt of NONE => [] | SOME salt_e => [salt_e] in
      Call ty (CreateTarget RawCreate (IS_SOME salt_opt) rof
        (create_keyword_order RawCreate (IS_SOME salt_opt) (LENGTH args) kwargs))
        (TAKE 1 args ++ [value_e] ++ DROP 1 args ++ salt_es) NONE)
    else if name = "shift" then
      (* Only a shift Vyper folds is supported: a runtime shift() is rejected,
         never read as a call to a function of that name. *)
      (case MAP origin_fold_value args of
       | [Literal _ (IntL i); Literal _ (IntL bits)] =>
           if -256 <= bits /\ bits <= 256 then
             if bits < 0 then
               Literal ty (IntL (int_shift_right (Num (-bits)) i))
             else
               (case pin_fold_result ty rejected_expr
                  (wrapped_int_op (if i < 0 then Signed 256 else Unsigned 256)
                    (int_shift_left (Num bits) i) : value + error) of
                | Literal lty l => Literal lty l
                | _ => rejected_expr)
           else rejected_expr
       | _ => rejected_expr)
    else if name = "abs" then fold_pin_constant (Builtin ty Abs args)
    else if name = "as_wei_value" then
      (* Vyper takes exactly two arguments, the second a string; one that
         doesn't reduce to a literal here is rejected, not read as wei. *)
      (case args of
         [v; d] =>
           (case denomination_of_expr d of
              SOME dn => fold_pin_constant (Builtin ty (AsWeiValue dn) [v])
            | NONE => rejected_expr)
       | _ => rejected_expr)
    else if name = "uint2str" then
      fold_pin_constant
        (case ret_ty of JT_String n => Builtin ty (Uint2Str n) args
                      | _ => Builtin ty (Uint2Str 0) args)
    else if name = "abi_decode" ∨ name = "_abi_decode" then
      kwargs_checked kwargs (
      let unwrap = kwarg_bool "unwrap_tuple" kwargs T in
      (case args of (arg::_) => TypeBuiltin ty (AbiDecode unwrap) ty [arg]
                  | _ => TypeBuiltin ty (AbiDecode unwrap) ty []))
    else if name = "abi_encode" ∨ name = "_abi_encode" then
      kwargs_checked kwargs (
      let ensure = kwarg_bool "ensure_tuple" kwargs T in
      let method_id = kwarg_method_id "method_id" kwargs in
      let arg_types = TupleT (MAP expr_type args) in
      TypeBuiltin ty (AbiEncode ensure method_id) arg_types args)
    else if name = "extract32" then
      TypeBuiltin ty Extract32 ty args
    else if name = "method_id" then
      fold_pin_constant (Builtin ty MethodId args)
    (* Struct constructor, cast, or regular call *)
    else (case ret_ty of
          | JT_Struct _ sname =>
              (case ty of
                 StructT nsid => StructLit ty nsid kwargs
               | _ => StructLit ty (NONE, sname) kwargs)
          | JT_Named _ _ =>
              if kwargs <> [] /\ ~is_builtin_cast_name name then
                (case ty of
                   StructT nsid => StructLit ty nsid kwargs
                 | _ => StructLit ty (NONE, name) kwargs)
              else
                if is_cast_name name then
                    if is_builtin_cast_name name then
                      (case ty of
                         BaseT _ =>
                           (case args of
                              (arg::_) => TypeBuiltin ty Convert ty [arg]
                            | _ => TypeBuiltin ty Convert ty [])
                       | _ =>
                           (case args of
                              (arg::_) => arg
                            | _ => rejected_expr))
                    else
                      (case args of
                         (arg::_) => arg
                       | _ => rejected_expr)
                else rejected_expr
          | _ =>
              if is_cast_name name then
                  if is_builtin_cast_name name then
                    (case ty of
                       BaseT _ =>
                         (case args of
                            (arg::_) => TypeBuiltin ty Convert ty [arg]
                          | _ => TypeBuiltin ty Convert ty [])
                     | _ =>
                         (case args of
                            (arg::_) => arg
                          | _ => rejected_expr))
                  else
                    (case args of
                       (arg::_) => arg
                     | _ => rejected_expr)
              else rejected_expr)
End


(* ===== Module Call Helpers ===== *)

(* Extract function name from a func expression *)
(* For JE_Attribute base fname, returns fname *)
Definition extract_func_name_def:
  (extract_func_name (JE_Attribute _ fname _ _ _ _ _) = fname) /\
  (extract_func_name (JE_Name name _ _ _) = name) /\
  (extract_func_name _ = "")
End


(* Check if a func expression has interface typeclass (for cross-module interface constructors) *)
Definition is_interface_constructor_def:
  (is_interface_constructor (JE_Attribute _ _ (SOME tc) _ _ _ _) = (tc = "interface")) /\
  (is_interface_constructor (JE_Name _ (SOME tc) _ _) = (tc = "interface")) /\
  (is_interface_constructor _ = F)
End


(* Extract the innermost module's source_id from a module chain *)
(* For lib1: returns SOME 0 (from JE_Name) *)
(* For lib1.lib2: returns SOME 1 (from the .lib2 Attribute) *)
Definition extract_innermost_module_src_def:
  (* Attribute with module/interface typeclass has source_id directly *)
  (extract_innermost_module_src (JE_Attribute _ _ (SOME tc) _ _ src_id_opt _) =
    if tc = "module" ∨ tc = "interface" then SOME src_id_opt else NONE) /\
  (* JE_Name with module/interface typeclass *)
  (extract_innermost_module_src (JE_Name _ (SOME tc) src_id_opt _) =
    if tc = "module" ∨ tc = "interface" then SOME src_id_opt else NONE) /\
  (* Other cases *)
  (extract_innermost_module_src _ = NONE)
End


(* Check if an expression is a module reference (not an interface-typed value).
   Used to detect nested module attribute access: mod3.mod2.mod1.X
   Interface-typed expressions like self.f should NOT match, because they are
   runtime values with attributes like .address and .balance. *)
Definition is_module_expr_def:
  (is_module_expr (JE_Attribute _ _ (SOME tc) _ _ _ _) = (tc = "module")) /\
  (is_module_expr (JE_Name _ (SOME tc) _ _) = (tc = "module")) /\
  (is_module_expr _ = F)
End


(* Resolve a module expression (possibly nested) to a source_id.
   e.g. lib1 -> SOME src_id_of_lib1
        lib2.lib1 -> SOME src_id_of_lib1 (via lib2's import_map)
   all_import_maps: source_id -> import_map for each module
   import_map: current module's alias -> source_id map *)
Definition resolve_module_expr_def:
  (resolve_module_expr all_import_maps import_map (JE_Name alias _ _ _) =
     ALOOKUP import_map alias) ∧
  (resolve_module_expr all_import_maps import_map (JE_Attribute inner alias _ _ _ _ _) =
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

(* ===== Expression translation context and name helpers ===== *)

(* Expression translation carries the root source ID, current module
   namespace, current module import map, constants/immutables, local and
   top-level types, the compile-time abstract override map, the literal
   values of the constants evaluated so far, and every module's import map. *)
Definition expr_main_src_id_def:
  expr_main_src_id ctx = FST ctx
End

Definition expr_current_nsid_def:
  expr_current_nsid ctx = FST (SND ctx)
End

Definition expr_import_map_def:
  expr_import_map ctx = FST (SND (SND ctx))
End

Definition expr_const_names_def:
  expr_const_names ctx = FST (SND (SND (SND ctx)))
End

Definition expr_local_types_def:
  expr_local_types ctx = FST (SND (SND (SND (SND ctx))))
End

Definition expr_toplevel_types_def:
  expr_toplevel_types ctx = FST (SND (SND (SND (SND (SND ctx)))))
End

Definition expr_override_map_def:
  expr_override_map ctx = FST (SND (SND (SND (SND (SND (SND ctx))))))
End

Definition expr_constants_def:
  expr_constants ctx = FST (SND (SND (SND (SND (SND (SND (SND ctx)))))))
End

Definition expr_all_import_maps_def:
  expr_all_import_maps ctx = FST (SND (SND (SND (SND (SND (SND (SND (SND ctx))))))))
End

Definition expr_origins_def:
  expr_origins ctx = SND (SND (SND (SND (SND (SND (SND (SND (SND ctx))))))))
End

Definition expr_with_local_types_def:
  expr_with_local_types ctx local_types =
    (expr_main_src_id ctx,
     expr_current_nsid ctx,
     expr_import_map ctx,
     expr_const_names ctx,
     local_types,
     expr_toplevel_types ctx,
     expr_override_map ctx,
     expr_constants ctx,
     expr_all_import_maps ctx,
     expr_origins ctx)
End

Definition expr_with_constants_def:
  expr_with_constants ctx constants =
    (expr_main_src_id ctx,
     expr_current_nsid ctx,
     expr_import_map ctx,
     expr_const_names ctx,
     expr_local_types ctx,
     expr_toplevel_types ctx,
     expr_override_map ctx,
     constants,
     expr_all_import_maps ctx,
     expr_origins ctx)
End

Definition expr_with_origins_def:
  expr_with_origins ctx origins =
    (expr_main_src_id ctx,
     expr_current_nsid ctx,
     expr_import_map ctx,
     expr_const_names ctx,
     expr_local_types ctx,
     expr_toplevel_types ctx,
     expr_override_map ctx,
     expr_constants ctx,
     expr_all_import_maps ctx,
     origins)
End

Definition lookup_local_type_def:
  lookup_local_type ctx name fallback =
    case ALOOKUP (expr_local_types ctx) name of
    | SOME ty => ty
    | NONE => fallback
End

Definition lookup_toplevel_type_def:
  lookup_toplevel_type ctx nsid fallback =
    case ALOOKUP (expr_toplevel_types ctx) nsid of
    | SOME ty => ty
    | NONE => fallback
End

Definition struct_field_key_def:
  struct_field_key sname fname = sname ++ "." ++ fname
End

(* A field read is typed at the field's declared type, not the wider type
   Vyper annotates in an argument, return or assignment position. *)
Definition member_type_def:
  member_type ctx (StructT (m, sname)) fname ann_ty =
    lookup_toplevel_type ctx (m, struct_field_key sname fname) ann_ty /\
  member_type ctx _ fname ann_ty = ann_ty
End

Definition expr_type_ctx_def:
  expr_type_ctx ctx =
    (expr_main_src_id ctx, expr_current_nsid ctx, expr_import_map ctx)
End

Definition resolve_source_ref_def:
  (resolve_source_ref ctx JMissingSource = expr_current_nsid ctx) /\
  (resolve_source_ref ctx (JExplicitSource src_id) =
    if src_id = -2 then expr_current_nsid ctx
    else source_id_to_nsid (expr_main_src_id ctx) src_id)
End

(* Module syntax carries the import alias that disambiguates Vyper's shared
   builtin source ID.  Prefer that canonical alias mapping to raw metadata. *)
Definition resolve_module_alias_def:
  resolve_module_alias ctx alias fallback =
    case ALOOKUP (expr_import_map ctx) alias of
    | SOME src_id => SOME src_id
    | NONE => resolve_source_ref ctx fallback
End

Definition resolve_func_module_ref_def:
  resolve_func_module_ref ctx
      (JE_Attribute (JE_Name alias tc src _)
        _ _ _ _ _ _) fallback =
    (if tc = SOME "module" then resolve_module_alias ctx alias src
     else resolve_source_ref ctx fallback) ∧
  (* A nested alias path (library.roots.isqrt) names the module through each
     module's import map; its call node carries the builtin modules' shared
     source ID, which would resolve to the current module. *)
  resolve_func_module_ref ctx (JE_Attribute obj _ _ _ _ _ _) fallback =
    (case resolve_module_expr (expr_all_import_maps ctx) (expr_import_map ctx)
            obj of
     | SOME src_id => SOME src_id
     | NONE => resolve_source_ref ctx fallback) ∧
  resolve_func_module_ref ctx _ fallback = resolve_source_ref ctx fallback
End

Definition resolve_override_aux_def:
  resolve_override_aux 0 override_map fn_key = fn_key ∧
  resolve_override_aux (SUC fuel) override_map fn_key =
    case ALOOKUP override_map fn_key of
    | NONE => fn_key
    | SOME next => resolve_override_aux fuel override_map next
End

Definition resolve_override_def:
  resolve_override ctx fn_key =
    resolve_override_aux (LENGTH (expr_override_map ctx))
      (expr_override_map ctx) fn_key
End

(* External signature metadata omits source IDs on nested nominal types.  Use
   the declaring function's module as the current type namespace. *)
Definition signature_type_ctx_def:
  signature_type_ctx ctx func_src =
    (expr_main_src_id ctx, resolve_source_ref ctx func_src, expr_import_map ctx)
End

(* A reference to an evaluated constant is its value at the reference's type,
   the type its position expects: with B: constant(Bytes[5]), the reference B
   in A: constant(Bytes[10]) = B is a Bytes[10]. Other top-level names stay
   references. *)
Definition top_level_ref_def:
  top_level_ref ctx ty nsid =
    case ALOOKUP (expr_constants ctx) nsid of
    | SOME l => Literal ty l
    | NONE => TopLevelName (lookup_toplevel_type ctx nsid ty) nsid
End

(* Bare references to constants and immutables are translated as
   module-qualified top-level names; ordinary names remain local/scoped. *)
Definition make_name_def:
  make_name ctx ty id =
    if MEM id (expr_const_names ctx)
    then top_level_ref ctx ty (expr_current_nsid ctx, id)
    else Name (lookup_local_type ctx id ty) id
End

Definition make_name_target_def:
  make_name_target ctx id =
    if MEM id (expr_const_names ctx)
    then TopLevelNameTarget (expr_current_nsid ctx, id)
    else NameTarget id
End

(* Python lowers I(addr) to a stack value (_lower_interface_constructor), so
   the address is loaded where the constructor appears. Vyper rejects a
   constructor without an address; its translation keeps the empty operand
   list, which fails Acc's arity check. *)
Definition interface_constructor_result_def:
  interface_constructor_result ty [Literal _ (BytesL bs)] =
    Literal ty (BytesL bs) /\
  interface_constructor_result _ [] =
    Builtin (BaseT AddressT) (Acc Address) [] /\
  interface_constructor_result _ (addr::_) =
    Builtin (BaseT AddressT) (Acc Address) [addr]
End

(* Cross-module flag result metadata may omit its declaration source. Recover
   that source from the module expression, then use it for both the result type
   and member lookup identity. *)
Definition extract_module_flag_def:
  (extract_module_flag ctx (JE_Attribute inner flag_name _ _ _ _ _) =
    case extract_innermost_module_src inner of
      SOME src => SOME (resolve_source_ref ctx src, flag_name)
    | NONE => NONE) /\
  (extract_module_flag ctx _ = NONE)
End

Definition make_flag_member_def:
  make_flag_member nsid attr = FlagMember (FlagT nsid) nsid attr
End

(* ===== Expression Translation ===== *)

(* Find a keyword by name in a keyword list, returns the json_expr if found *)
Definition find_keyword_def:
  find_keyword name [] = NONE ∧
  find_keyword name (JKeyword kw_name kw_val :: rest) =
    if kw_name = name then SOME kw_val
    else find_keyword name rest
End

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

Definition translate_attribute_def:
  translate_attribute ctx e translated_base attr result_tc base_type_name
      base_typeclass attr_src_id_opt ret_ty =
    case e of
    | JE_Name obj tc src_id_opt base_ret_ty =>
    let ty = translate_type (expr_type_ctx ctx) ret_ty in
    let base_ty = translate_type (expr_type_ctx ctx) base_ret_ty in
    (* Same-module flag member: Action.BUY where tc = SOME "flag" *)
    if tc = SOME "flag" /\ result_tc = SOME "flag" then
      make_flag_member (expr_current_nsid ctx, obj) attr
    else if obj = "msg" /\ attr = "sender" then Builtin (BaseT AddressT) (Env Sender) []
    else if obj = "msg" /\ attr = "value" then Builtin (BaseT (UintT 256)) (Env ValueSent) []
    else if obj = "msg" /\ (attr = "gas" \/ attr = "mana") then
      Builtin (BaseT (UintT 256)) (Env MsgGas) []
    else if obj = "block" /\ attr = "timestamp" then Builtin (BaseT (UintT 256)) (Env TimeStamp) []
    else if obj = "block" /\ attr = "number" then Builtin (BaseT (UintT 256)) (Env BlockNumber) []
    else if obj = "block" /\ attr = "prevhash" then Builtin (BaseT (BytesT (Fixed 32))) (Env PrevHash) []
    else if obj = "block" /\ attr = "blobbasefee" then Builtin (BaseT (UintT 256)) (Env BlobBaseFee) []
    else if obj = "block" /\ attr = "coinbase" then Builtin (BaseT AddressT) (Env Coinbase) []
    else if obj = "block" /\ attr = "gaslimit" then Builtin (BaseT (UintT 256)) (Env GasLimit) []
    else if obj = "block" /\ attr = "basefee" then Builtin (BaseT (UintT 256)) (Env BaseFee) []
    else if obj = "block" /\ attr = "difficulty" then Builtin (BaseT (UintT 256)) (Env PrevRandao) []
    else if obj = "tx" /\ attr = "gasprice" then Builtin (BaseT (UintT 256)) (Env GasPrice) []
    else if obj = "tx" /\ attr = "origin" then Builtin (BaseT AddressT) (Env TxOrigin) []
    else if obj = "chain" /\ attr = "id" then Builtin (BaseT (UintT 256)) (Env ChainId) []
    else if obj = "self" /\ attr = "balance" then
      Builtin (BaseT (UintT 256)) (Acc Balance) [Builtin (BaseT AddressT) (Env SelfAddr) []]
    else if obj = "self" /\ attr = "code" then
      Builtin (BaseT (BytesT (Dynamic 24576))) (Acc Code) [Builtin (BaseT AddressT) (Env SelfAddr) []]
    else if obj = "self" /\ attr = "is_contract" then
      Builtin (BaseT BoolT) (Acc IsContract) [Builtin (BaseT AddressT) (Env SelfAddr) []]
    else if obj = "self" /\ attr = "codehash" then
      Builtin (BaseT (BytesT (Fixed 32))) (Acc Codehash) [Builtin (BaseT AddressT) (Env SelfAddr) []]
    else if obj = "self" /\ attr = "codesize" then
      Builtin (BaseT (UintT 256)) (Acc Codesize) [Builtin (BaseT AddressT) (Env SelfAddr) []]
    (* self.x: declaration types override incomplete compiler expression metadata. *)
    else if obj = "self" then
      let nsid = (resolve_source_ref ctx attr_src_id_opt, attr) in
      TopLevelName (lookup_toplevel_type ctx nsid ty) nsid
    (* Module variable access (lib1.x): use its canonical declaration type.
       Annotation nodes carry no typeclass, so an imported alias also counts. *)
    else if tc = SOME "module" ∨
            (tc = NONE ∧ IS_SOME (ALOOKUP (expr_import_map ctx) obj)) then
      top_level_ref ctx ty (resolve_module_alias ctx obj src_id_opt, attr)
    else if attr = "balance" /\ base_type_name = SOME "address" then Builtin (BaseT (UintT 256)) (Acc Balance) [make_name ctx base_ty obj]
    else if attr = "address" /\ base_type_name = SOME "address" then Builtin (BaseT AddressT) (Acc Address) [make_name ctx base_ty obj]
    else if attr = "address" /\ base_typeclass = SOME "interface" then
      Builtin (BaseT AddressT) (Acc Address) [make_name ctx base_ty obj]
    else if attr = "is_contract" /\ base_type_name = SOME "address" then Builtin (BaseT BoolT) (Acc IsContract) [make_name ctx base_ty obj]
    else if attr = "codesize" /\ base_type_name = SOME "address" then Builtin (BaseT (UintT 256)) (Acc Codesize) [make_name ctx base_ty obj]
    else if attr = "codehash" /\ base_type_name = SOME "address" then Builtin (BaseT (BytesT (Fixed 32))) (Acc Codehash) [make_name ctx base_ty obj]
    else if attr = "code" /\ base_type_name = SOME "address" then Builtin (BaseT (BytesT (Dynamic 24576))) (Acc Code) [make_name ctx base_ty obj]
    else let base = make_name ctx base_ty obj in
      Attribute (member_type ctx (expr_type base) attr ty) base attr

  (* General attribute - handles nested and simple cases *)
  (* Check for cross-module flag access: lib1.Action.BUY *)
  (* base_type_name is the type name of the base expression (e.g., "address" for addr.code) *)
  (* base_typeclass is the typeclass of the base expression (e.g., "interface" for interface.address) *)
    | _ =>
    let ty = translate_type (expr_type_ctx ctx) ret_ty in
    if result_tc = SOME "flag" then
      case extract_module_flag ctx e of
        SOME nsid => make_flag_member nsid attr
      | NONE => Attribute ty translated_base attr
    (* Nested module access: mod3.mod2.mod1.X — use variable_reads source_id *)
    else if is_module_expr e then
      top_level_ref ctx ty (resolve_source_ref ctx attr_src_id_opt, attr)
    (* Annotation nodes carry no typeclass: resolve an alias path instead. *)
    else if base_typeclass = NONE ∧
            IS_SOME (resolve_module_expr (expr_all_import_maps ctx)
                       (expr_import_map ctx) e) then
      top_level_ref ctx ty
        (resolve_module_expr (expr_all_import_maps ctx) (expr_import_map ctx) e,
         attr)
    else if attr = "balance" /\ base_type_name = SOME "address" then Builtin (BaseT (UintT 256)) (Acc Balance) [translated_base]
    else if attr = "address" /\ base_type_name = SOME "address" then Builtin (BaseT AddressT) (Acc Address) [translated_base]
    else if attr = "address" /\ base_typeclass = SOME "interface" then Builtin (BaseT AddressT) (Acc Address) [translated_base]
    else if attr = "is_contract" /\ base_type_name = SOME "address" then Builtin (BaseT BoolT) (Acc IsContract) [translated_base]
    else if attr = "codesize" /\ base_type_name = SOME "address" then Builtin (BaseT (UintT 256)) (Acc Codesize) [translated_base]
    else if attr = "codehash" /\ base_type_name = SOME "address" then Builtin (BaseT (BytesT (Fixed 32))) (Acc Codehash) [translated_base]
    else if attr = "code" /\ base_type_name = SOME "address" then Builtin (BaseT (BytesT (Dynamic 24576))) (Acc Code) [translated_base]
    else Attribute (member_type ctx (expr_type translated_base) attr ty)
           translated_base attr
End


Definition translate_list_def:
  translate_list ctx ty es =
    let ty' = translate_type (expr_type_ctx ctx) ty in
    case ty of
    | JT_StaticArray vt len =>
        Builtin ty'
          (MakeArray (SOME (translate_type (expr_type_ctx ctx) vt)) (Fixed len)) es
    | JT_DynArray vt len =>
        Builtin ty'
          (MakeArray (SOME (translate_type (expr_type_ctx ctx) vt)) (Dynamic len)) es
    | _ => Builtin ty' (MakeArray NONE (Fixed (LENGTH es))) es
End


Definition pin_bool_values_def:
  pin_bool_values [] = SOME [] /\
  pin_bool_values (Literal ty (BoolL b) :: es) =
    OPTION_MAP (CONS b) (pin_bool_values es) /\
  pin_bool_values _ = NONE
End

(* A chain of 3 or more operands is marked BoolChain around the nested IfExp
   it desugars to, so the lowering can follow the pinned compiler's
   lower_BoolOp; `(b and c) if a else False` has the same IfExp and lowers as
   a ternary. *)
Definition bool_chain_def:
  bool_chain is_and es e =
    if 3 <= LENGTH es then Builtin (BaseT BoolT) (BoolChain is_and (LENGTH es)) [e]
    else e
End

Definition translate_boolop_def:
  translate_boolop JBoolop_And es =
    (case pin_bool_values (MAP origin_fold_value es) of
     | SOME bs => Literal (BaseT BoolT) (BoolL (EVERY I bs))
     | NONE => bool_chain T es (boolop_and es)) /\
  translate_boolop JBoolop_Or es =
    (case pin_bool_values (MAP origin_fold_value es) of
     | SOME bs => Literal (BaseT BoolT) (BoolL (EXISTS I bs))
     | NONE => bool_chain F es (boolop_or es))
End


Definition translate_unary_def:
  (translate_unary ctx JUop_USub e ret_ty =
    fold_pin_constant (Builtin (translate_type (expr_type_ctx ctx) ret_ty) Neg [e])) /\
  (translate_unary ctx JUop_Not e ret_ty =
    fold_pin_constant (Builtin (BaseT BoolT) Not [e])) /\
  (* `~x` has the type of `x`.  A flag annotation names only the flag, so it
     resolves to the current module's flag of that name; the translated
     operand carries the declaring module. *)
  (translate_unary ctx JUop_Invert e ret_ty =
    let ty = translate_type (expr_type_ctx ctx) ret_ty in
    fold_pin_constant
      (Builtin (case ty of FlagT _ => expr_type e | _ => ty) Not [e]))
End


(* Recover a writable path without restricting the depth of a pop receiver. *)
Definition expr_base_target_def:
  expr_base_target (Name _ id) = SOME (NameTarget id) /\
  expr_base_target (TopLevelName _ nsid) = SOME (TopLevelNameTarget nsid) /\
  expr_base_target (Subscript _ obj idx) =
    OPTION_MAP (\tgt. SubscriptTarget tgt idx) (expr_base_target obj) /\
  expr_base_target (Attribute _ obj attr) =
    OPTION_MAP (\tgt. AttributeTarget tgt attr) (expr_base_target obj) /\
  expr_base_target _ = NONE
End


(* Shared fallback after the name, interface shortcut, pop and self branches. *)
Definition translate_module_call_def:
  translate_module_call ctx func args' kwargs' ret_ty src_id_opt rty =
           if is_interface_constructor func then
             interface_constructor_result rty args'
           else let nsid = resolve_func_module_ref ctx func src_id_opt;
               fname = extract_func_name func in
           (case ret_ty of
              JT_Struct src_id_opt sname =>
                if fname = sname then
                  (* Struct constructor: library.SomeStruct(x=2) *)
                  let mod_nsid = case src_id_opt of
                      SOME sid => source_id_to_nsid (expr_main_src_id ctx) sid
                    | NONE =>
                      case func of
                        JE_Attribute obj _ _ _ _ _ _ =>
                          (case extract_innermost_module_src obj of
                             SOME src => resolve_source_ref ctx src
                           | NONE => nsid)
                      | _ => nsid in
                  StructLit (StructT (mod_nsid, fname)) (mod_nsid, fname) kwargs'
                else
                  (* Function call that returns a struct: library.foo() *)
                  Call rty (IntCall (resolve_override ctx (nsid, fname))) args' NONE
            | _ =>
              (* Module call: use source_id from type_decl_node *)
              Call rty (IntCall (resolve_override ctx (nsid, fname))) args' NONE)
End

Definition translate_call_def:
  translate_call ctx func args' kwargs' ret_ty src_id_opt translated_pop_target =
    let rty = translate_type (signature_type_ctx ctx src_id_opt) ret_ty in
    case func of
    | JE_Name name tc _ _ =>
        if tc = SOME "interface" then interface_constructor_result rty args'
        else make_builtin_call rty name args' kwargs' ret_ty
    | JE_Attribute obj fname _ _ _ _ _ =>
        (* Interface shortcuts take priority over pop and self calls. *)
        if fname = "__at__" \/ fname = "__interface__" then
          interface_constructor_result rty args'
        else if fname = "pop" then
          (* pop() yields an element, whatever wider type the context
             expects. *)
          (case translated_pop_target of
           | SOME (receiver, tgt) =>
               Pop (case expr_type receiver of
                    | ArrayT elem_ty _ => elem_ty
                    | _ => rty) tgt
           | NONE => Call rty (IntCall (NONE, "pop")) args' NONE)
        else
          (case obj of
           | JE_Name id _ _ _ =>
               if id = "self" then
                 Call rty
                   (IntCall (resolve_override ctx
                     (resolve_source_ref ctx src_id_opt, fname))) args' NONE
               else translate_module_call ctx func args' kwargs' ret_ty src_id_opt rty
           | _ => translate_module_call ctx func args' kwargs' ret_ty src_id_opt rty)
    | _ => translate_module_call ctx func args' kwargs' ret_ty src_id_opt rty
End

(* Recognize the source shape before translating msg.data: it is not an
   ordinary bounded bytes value in the internal AST. *)
Definition is_calldata_len_call_def:
  is_calldata_len_call (JE_Name name _ _ _)
    [JE_Attribute (JE_Name obj _ _ _) attr _ _ _ _ _] [] =
      (name = "len" /\ obj = "msg" /\ attr = "data") /\
  is_calldata_len_call _ _ _ = F
End

(* The length is a compile-time value, not a runtime operand. *)
Definition calldata_slice_length_def:
  calldata_slice_length e =
    case pin_fold_value e of
    | SOME (IntV i) =>
        if 0 < i /\ i < &(2 ** 256) then SOME (Num i) else NONE
    | _ => NONE
End

Definition is_calldata_slice_call_def:
  is_calldata_slice_call (JE_Name name _ _ _)
    (JE_Attribute (JE_Name obj _ _ _) attr _ _ _ _ _ :: _) =
      (name = "slice" /\ obj = "msg" /\ attr = "data") /\
  is_calldata_slice_call _ _ = F
End

Definition calldata_slice_bound_def:
  calldata_slice_bound [data; start; len] [] = calldata_slice_length len /\
  calldata_slice_bound _ _ = NONE
End

Theorem calldata_slice_bound_length:
  calldata_slice_bound args kwargs = SOME n ==> LENGTH args = 3
Proof
  strip_tac >> gvs[oneline calldata_slice_bound_def, AllCaseEqs()]
QED

(* Match only the dedicated source operand; compiler type/source metadata
   does not turn msg.data into an ordinary bounded bytes expression. *)
Definition is_raw_call_calldata_call_def:
  is_raw_call_calldata_call (JE_Name name _ _ _)
    [target; JE_Attribute (JE_Name obj _ _ _) attr _ _ _ _ _] =
      (name = "raw_call" /\ obj = "msg" /\ attr = "data") /\
  is_raw_call_calldata_call _ _ = F
End

Theorem is_raw_call_calldata_call_length:
  !func args. is_raw_call_calldata_call func args ==> LENGTH args = 2
Proof
  ho_match_mp_tac is_raw_call_calldata_call_ind >>
  simp[is_raw_call_calldata_call_def]
QED

Theorem is_raw_call_calldata_call_nonempty:
  is_raw_call_calldata_call func args ==> args <> []
Proof
  Cases_on `args` >> simp[] >> Cases_on `func` >>
  simp[is_raw_call_calldata_call_def]
QED

(* convert(x, T) and abi_decode(x, T) produce a T: Vyper annotates the call
   with the type its context expects, which may be wider, and annotates the
   type argument with T itself. *)
Definition json_expr_annotation_def:
  json_expr_annotation (JE_Name _ _ _ jt) = jt /\
  json_expr_annotation (JE_Attribute _ _ _ _ _ _ jt) = jt /\
  json_expr_annotation (JE_Subscript _ _ jt) = jt /\
  json_expr_annotation (JE_Tuple _ jt) = jt /\
  json_expr_annotation _ = JT_None
End

Definition type_argument_def:
  type_argument (JE_Name name tc _ _) [_; type_arg] =
    (if tc <> SOME "interface" /\
        MEM name ["convert"; "abi_decode"; "_abi_decode"]
     then SOME (json_expr_annotation type_arg) else NONE) /\
  type_argument _ _ = NONE
End

(* A JSON ABI import's declared Bytes/String bound is "..." rather than an
   ABI bound. The callsite operand is already translated using its canonical
   local declaration type; use that bound for the effective ABI signature. *)
Definition external_argument_type_def:
  external_argument_type sig_ctx JT_BytesUnbounded actual =
    (case expr_type actual of
     | BaseT (BytesT (Dynamic n)) => BaseT (BytesT (Dynamic n))
     | _ => NoneT) ∧
  external_argument_type sig_ctx JT_StringUnbounded actual =
    (case expr_type actual of
     | BaseT (StringT n) => BaseT (StringT n)
     | _ => NoneT) ∧
  external_argument_type sig_ctx ty actual = translate_type sig_ctx ty
End

Definition external_argument_types_def:
  external_argument_types sig_ctx [] _ = [] ∧
  external_argument_types sig_ctx _ [] = [] ∧
  external_argument_types sig_ctx (ty::tys) (actual::args) =
    external_argument_type sig_ctx ty actual ::
    external_argument_types sig_ctx tys args
End

Definition origin_hex_byte_def:
  origin_hex_byte (b : word8) =
    let n = w2n b in
    MAP (\d. CHR (if d < 10 then ORD #"0" + d else ORD #"a" + d - 10))
      [n DIV 16; n MOD 16]
End

Definition origin_hex_bytes_def:
  origin_hex_bytes bs = "0x" ++ FLAT (MAP origin_hex_byte bs)
End

Definition origin_int_string_def:
  origin_int_string (i : int) =
    (if i < 0 then "-" else "") ++ num_to_dec_string (Num (ABS i))
End

Definition canonical_literal_origin_def:
  canonical_literal_origin (Literal ty (IntL i)) = SOME (JE_Int i JT_None) /\
  canonical_literal_origin (Literal ty (DecimalL i)) =
    SOME (JE_Decimal (origin_int_string i ++ "e-10")) /\
  canonical_literal_origin (Literal ty (BoolL b)) = SOME (JE_Bool b) /\
  canonical_literal_origin (Literal ty (StringL s)) = SOME (JE_Str (LENGTH s) s) /\
  canonical_literal_origin (Literal (BaseT (BytesT (Dynamic n))) (BytesL bs)) =
    SOME (JE_Bytes n (origin_hex_bytes bs)) /\
  canonical_literal_origin (Literal ty (BytesL bs)) =
    SOME (JE_Hex (origin_hex_bytes bs) JT_None) /\
  canonical_literal_origin (Literal (BaseT (BytesT (Dynamic n))) (HexBytesL bs)) =
    SOME (JE_HexBytes n (origin_hex_bytes bs)) /\
  canonical_literal_origin _ = NONE
End

Definition origin_node_kind_def:
  origin_node_kind (JE_Int _ _) = SOME 0 /\
  origin_node_kind (JE_Decimal _) = SOME 1 /\
  origin_node_kind (JE_Str _ _) = SOME 2 /\
  origin_node_kind (JE_GenericStr _) = SOME 2 /\
  origin_node_kind (JE_Bytes _ _) = SOME 3 /\
  origin_node_kind (JE_HexBytes _ _) = SOME 8 /\
  origin_node_kind (JE_Hex _ _) = SOME 4 /\
  origin_node_kind (JE_Bool _) = SOME 5 /\
  origin_node_kind (JE_List _ _) = SOME 6 /\
  origin_node_kind (JE_Tuple _ _) = SOME 7 /\
  origin_node_kind _ = NONE
End

Definition origin_numeric_def:
  origin_numeric (JE_Int i _) = SOME (i * 10 ** 10) /\
  origin_numeric (JE_Decimal s) = SOME (decimal_string_to_int s) /\
  origin_numeric (JE_Bool b) = SOME (if b then 10 ** 10 else 0) /\
  origin_numeric _ = NONE
End

Definition origin_text_def:
  origin_text (JE_Hex s _) = SOME s /\
  origin_text (JE_Str _ s) = SOME s /\
  origin_text (JE_GenericStr s) = SOME s /\
  origin_text _ = NONE
End

Definition origin_bytes_def:
  origin_bytes (JE_Bytes _ s) =
    SOME (hex_string_to_bytes (FILTER isHexDigit (strip_0x s))) /\
  origin_bytes (JE_HexBytes _ s) =
    SOME (hex_string_to_bytes (FILTER isHexDigit (strip_0x s))) /\
  origin_bytes _ = NONE
End

Definition origin_same_value_def:
  origin_same_value l r =
    case (origin_numeric l, origin_numeric r) of
    | (SOME x,SOME y) => x = y
    | _ => case (origin_text l, origin_text r) of
           | (SOME x,SOME y) => x = y
           | _ => case (origin_bytes l, origin_bytes r) of
                  | (SOME x,SOME y) => x = y
                  | _ => F
End

Definition origin_homogeneous_def:
  origin_homogeneous [] = T /\
  origin_homogeneous (e::es) =
    (IS_SOME (origin_node_kind e) /\
     EVERY (\x. origin_node_kind x = origin_node_kind e) es)
End

Definition origin_membership_def:
  origin_membership op (SOME l) (SOME (JE_List es _)) =
    (if MEM op [JBop_In; JBop_NotIn] /\
        (case origin_node_kind l of SOME n => n < 6 \/ n = 8 | _ => F) /\
        EVERY (\x. case origin_node_kind x of SOME n => n < 6 \/ n = 8 | _ => F) es /\
        origin_homogeneous es
     then SOME (if op = JBop_In then EXISTS (origin_same_value l) es
                else ~EXISTS (origin_same_value l) es)
     else NONE) /\
  origin_membership _ _ _ = NONE
End

Definition origin_select_def:
  origin_select (SOME (JE_List es _)) (Literal _ (IntL i)) =
    (if origin_homogeneous es /\ 0 <= i /\ Num i < LENGTH es
     then SOME (EL (Num i) es) else NONE) /\
  origin_select _ _ = NONE
End

Definition origin_retype_def:
  origin_retype ty (Literal _ l) = Literal ty l /\
  origin_retype (ArrayT elem bd) (Builtin old (MakeArray (SOME _) _) es) =
    Builtin (ArrayT elem bd) (MakeArray (SOME elem) bd)
      (origin_retypes elem es) /\
  origin_retype ty e = e /\
  origin_retypes ty [] = [] /\
  origin_retypes ty (e::es) = origin_retype ty e :: origin_retypes ty es
End

Definition expr_origin_key_def:
  expr_origin_key ctx (JE_Name name tc src jt) =
    (if MEM name (expr_const_names ctx)
     then SOME (expr_current_nsid ctx,name) else NONE) /\
  expr_origin_key ctx
    (JE_Attribute obj attr result_tc btn btc src jt) =
    (case obj of
     | JE_Name alias tc sid _ =>
         if tc = SOME "module" \/
            (tc = NONE /\ IS_SOME (ALOOKUP (expr_import_map ctx) alias))
         then SOME (resolve_module_alias ctx alias sid,attr) else NONE
     | _ => OPTION_MAP (\m. (SOME m,attr))
              (resolve_module_expr (expr_all_import_maps ctx)
                 (expr_import_map ctx) obj)) /\
  expr_origin_key _ _ = NONE
End

(* The constant-origin table's entry for a constant reference.  Besides
   literal trees the table holds the empty(T) constants
   (module_origin_constants), which only assign_value reads. *)
Definition lookup_origin_entry_def:
  lookup_origin_entry ctx source =
    OPTION_BIND (expr_origin_key ctx source) (ALOOKUP (expr_origins ctx))
End

Definition lookup_origin_pair_def:
  lookup_origin_pair ctx source =
    case lookup_origin_entry ctx source of
    | SOME (v, origin) => if pin_literal_tree v then SOME (v, origin) else NONE
    | NONE => NONE
End

(* The right operand r' (translated from r) of an in / not in.  Where the
   source names a constant array, or r' is an array the frontend folded
   from something other than a list literal (a subscript of a constant,
   NESTED[0]), it is marked NamedConst: the pinned compiler unrolls a
   membership only over a list literal (lower_Compare) and loops over any
   other array.  A named constant is marked around its value, not its name:
   the checker types the body before constants are substituted, and
   NamedConst takes only a value (named_const_operand). *)
Definition membership_operand_def:
  membership_operand ctx r r' =
    case lookup_origin_pair ctx r of
    | SOME (Builtin a (MakeArray (SOME t) n) es, _) =>
        Builtin (expr_type r') NamedConst
          [origin_retype (expr_type r') (Builtin a (MakeArray (SOME t) n) es)]
    | _ =>
      case (r, r') of
      | (JE_List _ _, _) => r'
      | (_, Builtin _ (MakeArray (SOME _) _) _) =>
          Builtin (expr_type r') NamedConst [r']
      | _ => r'
End

(* A subscript or attribute is typed at the element's or field's own type:
   Vyper annotates it with the type its context expects, which may be wider.
   A HashMap value (no array base) keeps the annotation. *)
Definition element_type_def:
  element_type (ArrayT elem_ty _) idx ann_ty = elem_ty /\
  element_type (TupleT tys) (Literal _ (IntL n)) ann_ty =
    (if 0 <= n then (case oEL (Num n) tys of SOME ty => ty | NONE => ann_ty)
     else ann_ty) /\
  element_type _ _ ann_ty = ann_ty
End

Definition translate_expr_with_policy_def:
  (translate_expr_with_policy resolve ctx (JE_Int v ty) =
    Literal (translate_type (expr_type_ctx ctx) ty) (IntL v)) /\

  (translate_expr_with_policy resolve ctx (JE_Decimal s) =
    Literal (BaseT DecimalT) (DecimalL (decimal_string_to_int s))) /\

  (translate_expr_with_policy resolve ctx (JE_Str len s) =
    Literal (BaseT (StringT len)) (StringL s)) /\

  (translate_expr_with_policy resolve ctx (JE_GenericStr s) =
    Literal (BaseT (StringT (STRLEN s))) (StringL s)) /\

  (translate_expr_with_policy resolve ctx (JE_Bytes len hex) =
    Literal (BaseT (BytesT (Dynamic len))) (BytesL (hex_string_to_bytes (FILTER isHexDigit (strip_0x hex))))) /\

  (translate_expr_with_policy resolve ctx (JE_HexBytes len hex) =
    Literal (BaseT (BytesT (Dynamic len)))
      (HexBytesL (hex_string_to_bytes (FILTER isHexDigit (strip_0x hex))))) /\

  (translate_expr_with_policy resolve ctx (JE_Hex hex typ) =
    let bytes = hex_string_to_bytes (FILTER isHexDigit (strip_0x hex)) in
    let ty = case typ of
               JT_None => BaseT (BytesT (Fixed (LENGTH bytes)))
             | _ => translate_type (expr_type_ctx ctx) typ in
    Literal ty (BytesL bytes)) /\

  (translate_expr_with_policy resolve ctx (JE_Bool b) = Literal (BaseT BoolT) (BoolL b)) /\

  (translate_expr_with_policy resolve ctx JE_Ellipsis = Literal (BaseT BoolT) (BoolL T)) /\

  (translate_expr_with_policy resolve ctx
     (JE_Name id tc src_id_opt ret_ty) =
    let ty = translate_type (expr_type_ctx ctx) ret_ty in
    if id = "self" then Builtin (BaseT AddressT) (Env SelfAddr) [] else
    if resolve then
      case lookup_origin_pair ctx (JE_Name id tc src_id_opt ret_ty) of
      | SOME (value,origin) => origin_retype ty value
      | NONE => make_name ctx ty id
    else make_name ctx ty id) /\

  (* Special attributes: msg.*, block.*, tx.*, self.*, module.*, flag members *)
  (* attr_src_id_opt is from variable_reads on the outer Attribute (for self.x storage access) *)
  (* base_type_name is the type name of the base expression (e.g., "address" for addr.code) *)
  (* base_typeclass is the typeclass of the base expression (e.g., "interface" for interface.address) *)
  (translate_expr_with_policy resolve ctx
     (JE_Attribute e attr tc btn btc src jt) =
    let original = translate_attribute ctx e
      (translate_expr_with_policy resolve ctx e) attr tc btn btc src jt in
    if resolve then
      case lookup_origin_pair ctx (JE_Attribute e attr tc btn btc src jt) of
      | SOME (value,origin) => origin_retype (translate_type (expr_type_ctx ctx) jt) value
      | NONE => original
    else original) /\

  (* Subscript *)
  (* A tuple index is a compile-time value. *)
  (translate_expr_with_policy resolve ctx (JE_Subscript arr idx jt) =
    let arr' = translate_expr_with_policy resolve ctx arr in
    let idx' = translate_expr_with_policy resolve ctx idx in
    let idx'' = (case expr_type arr' of TupleT _ => fold_pin_constant idx' | _ => idx') in
    let ann_ty = translate_type (expr_type_ctx ctx) jt in
    let ty = element_type (expr_type arr') idx'' ann_ty in
    let original = Subscript ty arr' idx'' in
    let arr_value = origin_fold_value
      (translate_expr_with_policy T ctx arr) in
    let index_value = origin_fold_value
      (translate_expr_with_policy T ctx idx) in
    let arr_checked = origin_retype (expr_type arr_value) arr_value in
    if pin_literal_tree arr_checked /\ IS_SOME (origin_select
        (resolved_origin_expr T ctx arr arr_value) index_value) then
      let elem_ty = case expr_type arr_checked of ArrayT elem _ => elem | _ => ty in
      case pin_fold_subscript elem_ty arr_checked index_value of
      | Subscript _ _ _ => original
      | selected =>
          (* A folded element is a literal: it takes the type Vyper reads
             it at, as the compiler does. *)
          let retyped = origin_retype ann_ty selected in
          if pin_literal_tree retyped /\ expr_type retyped = ann_ty
          then retyped else original
    else original) /\

  (* NamedExpr - only appears in initializes:/uses: annotations, not in executable code *)
  (translate_expr_with_policy resolve ctx (JE_NamedExpr target value) =
    Literal (BaseT BoolT) (BoolL T)) /\

  (* BinOp *)
  (* The checker needs a literal exponent unless the base is one, so a
     compile-time exponent is folded. *)
  (* A flag annotation names only the flag, so it resolves to the current
     module's flag of that name; `|`, `&` and `^` have the type of their
     operands, and the translated left operand carries the declaring module. *)
  (translate_expr_with_policy resolve ctx (JE_BinOp l op r ret_ty) =
    let l' = translate_expr_with_policy resolve ctx l in
    let r' = translate_expr_with_policy resolve ctx r in
    let ty = translate_type (expr_type_ctx ctx) ret_ty in
    fold_pin_constant
      (Builtin (case ty of FlagT _ => expr_type l' | _ => ty)
        (Bop (translate_binop op)) [l'; exponent_operand op r'])) /\

  (translate_expr_with_policy resolve ctx (JE_Compare l op r) =
    let l' = translate_expr_with_policy resolve ctx l in
    let r' = translate_expr_with_policy resolve ctx r in
    let r'' = if MEM op [JBop_In; JBop_NotIn]
              then membership_operand ctx r r' else r' in
    let original = Builtin (BaseT BoolT) (Bop (translate_binop op)) [l';r''] in
    if ~MEM op [JBop_In; JBop_NotIn; JBop_Eq; JBop_NotEq]
    then fold_pin_constant original else
    let lv = origin_fold_value
      (translate_expr_with_policy T ctx l) in
    let rv = origin_fold_value
      (translate_expr_with_policy T ctx r) in
    let lo = resolved_origin_expr T ctx l lv in
    let ro = resolved_origin_expr T ctx r rv in
    if MEM op [JBop_In; JBop_NotIn] then
      case origin_membership op lo ro of
      | SOME b => Literal (BaseT BoolT) (BoolL b)
      | NONE => original
    else
      case (lo, ro) of
      | (SOME left, SOME right) =>
          (case origin_node_kind left of
           | SOME k =>
               if (k < 6 \/ k = 8) /\ origin_node_kind right = SOME k then
                 (case pin_fold_expr
                   (Builtin (BaseT BoolT) (Bop (translate_binop op)) [lv;rv]) of
                  | Literal ty value => Literal ty value
                  | _ => original)
               else original
           | NONE => original)
      | _ => original) /\


  (* BoolOp - convert to nested IfExp *)
  (translate_expr_with_policy resolve ctx (JE_BoolOp op es) =
    translate_boolop op
      (translate_expr_list_with_policy resolve ctx es)) /\

  (* UnaryOp *)
  (translate_expr_with_policy resolve ctx (JE_UnaryOp op e ret_ty) =
    translate_unary ctx op (translate_expr_with_policy resolve ctx e) ret_ty) /\

  (* IfExp (ternary) *)
  (* A flag-typed IfExp has the flag of its arms (see BinOp). *)
  (translate_expr_with_policy resolve ctx (JE_IfExp test body orelse ret_ty) =
    let test' = translate_expr_with_policy resolve ctx test in
    let body' = translate_expr_with_policy resolve ctx body in
    let orelse' = translate_expr_with_policy resolve ctx orelse in
    let ty = translate_type (expr_type_ctx ctx) ret_ty in
    IfExp (case ty of FlagT _ => expr_type body' | _ => ty) test' body' orelse') /\

  (* Tuple: Vyper types a tuple literal by its context (e.g. the parameter
     it is passed to), so members may be wider than the elements. *)
  (translate_expr_with_policy resolve ctx (JE_Tuple es ty) =
    let es' = translate_expr_list_with_policy resolve ctx es in
    let tys = (case translate_type (expr_type_ctx ctx) ty of
               | TupleT tys =>
                   if LENGTH tys = LENGTH es' /\ ~MEM NoneT tys then tys
                   else MAP expr_type es'
               | _ => MAP expr_type es') in
    Builtin (TupleT tys) (MakeArray NONE (Fixed (LENGTH es'))) es') /\

  (* List - array literal *)
  (translate_expr_with_policy resolve ctx (JE_List es ty) =
    translate_list ctx ty (translate_expr_list_with_policy resolve ctx es)) /\

  (* Call - single case with internal dispatch to avoid pattern completion issues *)
  (* JE_Call now includes source_id for module calls *)
  (translate_expr_with_policy resolve ctx (JE_Call func args kwargs ret_ty src_id_opt) =
    if is_calldata_len_call func args kwargs then
      Builtin (BaseT (UintT 256)) CalldataLen []
    else if is_calldata_slice_call func args then
      (let args' = translate_expr_list_with_policy resolve ctx args;
           target_ty = translate_type (expr_type_ctx ctx) ret_ty in
       case (calldata_slice_bound args' kwargs, target_ty) of
       | (SOME n, BaseT (BytesT (Dynamic m))) =>
           if n <= m then Builtin target_ty (CalldataSlice n) [EL 1 args']
           else rejected_expr
       | _ => rejected_expr)
    else if is_raw_call_calldata_call func args then
      let kwargs' = translate_kwargs_with_policy resolve ctx kwargs in
      kwargs_checked kwargs' (
      Call (translate_type (expr_type_ctx ctx) ret_ty)
        (RawCallCalldataTarget (raw_call_flags_of_kwargs kwargs'))
        (translate_expr_with_policy resolve ctx (HD args) :: MAP SND (ext_call_kwargs kwargs')) NONE)
    else let args' =
      case (func,args) of
      | (JE_Name name tc _ _, [topics;data]) =>
          if name = "raw_log" /\ tc <> SOME "interface" then
            let topics_value = translate_expr_with_policy T ctx topics in
            let topics_ty = expr_type topics_value in
            let candidate = origin_retype topics_ty (origin_fold_value topics_value) in
            [(if IS_SOME (resolved_origin_expr T ctx topics candidate) /\
                  pin_literal_tree candidate /\ expr_type candidate = topics_ty
              then candidate
              else translate_expr_with_policy resolve ctx topics);
             translate_expr_with_policy resolve ctx data]
          else translate_expr_list_with_policy resolve ctx args
      | _ => translate_expr_list_with_policy resolve ctx args in
    let kwargs' = translate_kwargs_with_policy resolve ctx kwargs in
    let translated_pop_target =
      case func of
      | JE_Attribute obj fname _ _ _ _ _ =>
          if fname = "pop" then
            let receiver = translate_expr_with_policy resolve ctx obj in
            OPTION_MAP (\tgt. (receiver, tgt)) (expr_base_target receiver)
          else NONE
      | _ => NONE in
    case type_argument func args of
    | SOME JT_None => rejected_expr
    | SOME result_ty =>
        translate_call ctx func args' kwargs' result_ty src_id_opt
          translated_pop_target
    | NONE =>
        translate_call ctx func args' kwargs' ret_ty src_id_opt
          translated_pop_target) /\

  (* ExtCall - mutating external call (is_static = F).
     Operands: target :: positional args ++ keyword args in source order. *)
  (translate_expr_with_policy resolve ctx
      (JE_ExtCall func_name func_src arg_types ret_ty target args keywords) =
    let kws = ext_call_kwargs (translate_kwargs_with_policy resolve ctx keywords) in
    let skip_check = kwarg_bool "skip_contract_check" (translate_kwargs_with_policy resolve ctx keywords) F in
    let sig_ctx = signature_type_ctx ctx func_src in
    let ret_ty' = translate_type sig_ctx ret_ty in
    let args' = translate_expr_list_with_policy resolve ctx args in
    (* Vyper records the full declared parameter list in argument_types, even
       when trailing defaulted parameters are omitted.  ExtCall carries the
       effective ABI signature selected at this call site. *)
    kwargs_checked (translate_kwargs_with_policy resolve ctx keywords) (
    Call ret_ty'
      (ExtCall F skip_check
        (func_name,
         external_argument_types sig_ctx arg_types args',
         ret_ty') (MAP FST kws))
      (translate_expr_with_policy resolve ctx target :: args' ++ MAP SND kws) NONE)) /\

  (* StaticCall - read-only external call (is_static = T); same operand
     layout as ExtCall, and Vyper rejects value= here. *)
  (translate_expr_with_policy resolve ctx
      (JE_StaticCall func_name func_src arg_types ret_ty target args keywords) =
    let kws = ext_call_kwargs (translate_kwargs_with_policy resolve ctx keywords) in
    let skip_check = kwarg_bool "skip_contract_check" (translate_kwargs_with_policy resolve ctx keywords) F in
    let sig_ctx = signature_type_ctx ctx func_src in
    let ret_ty' = translate_type sig_ctx ret_ty in
    let args' = translate_expr_list_with_policy resolve ctx args in
    (* See ExtCall above: retain only the effective ABI argument types. *)
    kwargs_checked (translate_kwargs_with_policy resolve ctx keywords) (
    Call ret_ty'
      (ExtCall T skip_check
        (func_name,
         external_argument_types sig_ctx arg_types args',
         ret_ty') (MAP FST kws))
      (translate_expr_with_policy resolve ctx target :: args' ++ MAP SND kws) NONE)) /\

  (* Helper for translating expression lists *)
  (translate_expr_list_with_policy resolve ctx [] = []) /\
  (translate_expr_list_with_policy resolve ctx (e::es) = translate_expr_with_policy resolve ctx e :: translate_expr_list_with_policy resolve ctx es) /\

  (* Helper for translating keywords *)
  (translate_kwargs_with_policy resolve ctx [] = []) /\
  (translate_kwargs_with_policy resolve ctx (JKeyword k v :: rest) = (k, translate_expr_with_policy resolve ctx v) :: translate_kwargs_with_policy resolve ctx rest) /\

  (resolved_origin_expr resolve ctx source value =
    case source of
    | JE_Name _ _ _ _ => OPTION_MAP SND (lookup_origin_pair ctx source)
    | JE_Attribute _ _ _ _ _ _ _ => OPTION_MAP SND (lookup_origin_pair ctx source)
    | JE_Hex raw jt => SOME (JE_Hex raw jt)
    | JE_HexBytes n raw => SOME (JE_HexBytes n raw)
    | JE_List es jt =>
        (case value of
         | Builtin _ (MakeArray _ _) values =>
             OPTION_MAP (\origins. JE_List origins jt)
               (resolved_origin_list resolve ctx es values)
         | _ => NONE)
    | JE_Tuple es jt =>
        (case value of
         | Builtin _ (MakeArray _ _) values =>
             OPTION_MAP (\origins. JE_Tuple origins jt)
               (resolved_origin_list resolve ctx es values)
         | _ => NONE)
    | JE_Subscript arr idx jt =>
        if ~pin_literal_tree value then NONE else
        let arr' = origin_fold_value
          (translate_expr_with_policy resolve ctx arr) in
        let idx' = origin_fold_value
          (translate_expr_with_policy resolve ctx idx) in
        origin_select (resolved_origin_expr resolve ctx arr arr') idx'
    | _ => canonical_literal_origin value) /\
  (resolved_origin_list resolve ctx [] [] = SOME []) /\
  (resolved_origin_list resolve ctx (e::es) (v::vs) =
    OPTION_BIND (resolved_origin_expr resolve ctx e
      (origin_fold_value v))
      (\origin. OPTION_MAP (CONS origin)
         (resolved_origin_list resolve ctx es vs))) /\
  (resolved_origin_list resolve ctx _ _ = NONE)
Termination
  WF_REL_TAC `measure (\x. case x of
    | INL (_, _, e) => json_expr_size e
    | INR (INL (_, _, es)) => list_size json_expr_size es
    | INR (INR (INL (_, _, kws))) => list_size json_keyword_size kws
    | INR (INR (INR (INL (_, _, e, value)))) => json_expr_size e
    | INR (INR (INR (INR (_, _, es, values)))) => list_size json_expr_size es)`
  >> rw[]
  >> imp_res_tac find_keyword_size
  >> gvs[]
  >> drule is_raw_call_calldata_call_nonempty
  >> Cases_on `args` >> gvs[]
End


Definition translate_expr_api_def:
  translate_expr ctx e = translate_expr_with_policy F ctx e
End

Definition translate_expr_list_api_def:
  translate_expr_list ctx es = translate_expr_list_with_policy F ctx es
End

Definition translate_kwargs_api_def:
  translate_kwargs ctx kws = translate_kwargs_with_policy F ctx kws
End

Definition translate_origin_expr_api_def:
  translate_origin_expr ctx e value = resolved_origin_expr F ctx e value
End

Definition translate_origin_list_api_def:
  translate_origin_list ctx es values = resolved_origin_list F ctx es values
End

Theorem translate_expr_def =
  PURE_REWRITE_RULE
    [boolTheory.COND_CLAUSES, GSYM translate_expr_api_def,
     GSYM translate_expr_list_api_def, GSYM translate_kwargs_api_def,
     GSYM translate_origin_expr_api_def, GSYM translate_origin_list_api_def]
    (LIST_CONJ (map (GEN_ALL o Q.INST [`resolve` |-> `F`] o SPEC_ALL)
      (CONJUNCTS translate_expr_with_policy_def)));


(* ===== Assignment Target Translation ===== *)
(* Defined after translate_expr since it uses it for subscript indices *)

Definition translate_base_target_def:
  (translate_base_target ctx (JBT_Name id) = make_name_target ctx id) /\
  (* Top-level targets retain whether their declaration is current or imported. *)
  (translate_base_target ctx (JBT_TopLevelName (src, name)) =
    TopLevelNameTarget (resolve_source_ref ctx src, name)) /\
  (translate_base_target ctx (JBT_Subscript tgt idx) =
    SubscriptTarget (translate_base_target ctx tgt) (translate_expr ctx idx)) /\
  (translate_base_target ctx (JBT_Attribute tgt attr) =
    AttributeTarget (translate_base_target ctx tgt) attr)
Termination
  (* Select the relation directly; avoid WF_REL_TAC's global size rewrites. *)
  qexists_tac `measure (json_base_target_size o SND)` >>
  conj_tac >- MATCH_ACCEPT_TAC prim_recTheory.WF_measure >>
  PURE_REWRITE_TAC [prim_recTheory.measure_thm, combinTheory.o_DEF,
                    pairTheory.SND] >>
  simp[json_base_target_size_def]
End


Definition translate_target_def:
  (translate_target ctx (JTgt_Base bt) = BaseTarget (translate_base_target ctx bt)) /\
  (translate_target ctx (JTgt_Tuple tgts) = TupleTarget (MAP (translate_target ctx) tgts))
Termination
  qexists_tac `measure (json_target_size o SND)` >>
  conj_tac >- MATCH_ACCEPT_TAC prim_recTheory.WF_measure >>
  PURE_REWRITE_TAC [prim_recTheory.measure_thm, combinTheory.o_DEF,
                    pairTheory.SND] >>
  simp[json_target_size_def] >>
  Induct_on `tgts` >> rw[json_target_size_def] >>
  res_tac >> simp[]
End


(* ===== Iterator Translation ===== *)

(* The bound comes from bound= when given, otherwise from compile-time range
   arguments; array iteration takes it from the array type. *)
Definition constant_count_def:
  constant_count e =
    case pin_fold_value e of
    | SOME (IntV i) => if 0 <= i then SOME (Num i) else NONE
    | _ => NONE
End

Definition range_count_def:
  range_count (s : expr) e =
    case (pin_fold_value s, pin_fold_value e) of
    | (SOME (IntV i), SOME (IntV j)) => if i <= j then Num (j - i) else 0
    | _ => 0
End

Definition get_iter_bound_def:
  (get_iter_bound ctx (JIter_Range args (SOME b)) =
     case constant_count (translate_expr ctx b) of SOME n => n | NONE => 0) /\
  (get_iter_bound ctx (JIter_Range [e] NONE) =
     range_count (Literal (BaseT (UintT 256)) (IntL 0)) (translate_expr ctx e)) /\
  (get_iter_bound ctx (JIter_Range (s::e::_) NONE) =
     range_count (translate_expr ctx s) (translate_expr ctx e)) /\
  (get_iter_bound ctx (JIter_Range [] NONE) = 0) /\
  (get_iter_bound ctx (JIter_Array _ (JT_StaticArray _ len)) = len) /\
  (get_iter_bound ctx (JIter_Array _ (JT_DynArray _ len)) = len) /\
  (get_iter_bound ctx (JIter_Array _ _) = 0)
End


(* Declaration validation rejects a range whose bound does not evaluate. *)
Definition iter_bound_resolved_def:
  (iter_bound_resolved ctx (JIter_Range args b) =
     EVERY (λe. IS_SOME (pin_fold_value (translate_expr ctx e)))
       (case b of SOME b => [b] | NONE => args)) /\
  (iter_bound_resolved ctx (JIter_Array _ _) = T)
End


Definition translate_iter_def:
  (translate_iter ctx var_ty (JIter_Range [] _) =
    Range (Literal var_ty (IntL (integer$int_of_num 0)))
          (Literal var_ty (IntL (integer$int_of_num 0)))) /\
  (* Without bound=, a range's endpoints are compile-time values, which the
     type checker requires to be literals. *)
  (translate_iter ctx var_ty (JIter_Range [e] bound) =
    Range (Literal var_ty (IntL (integer$int_of_num 0)))
          (case bound of
             NONE => fold_pin_constant (translate_expr ctx e)
           | SOME _ => translate_expr ctx e)) /\
  (translate_iter ctx var_ty (JIter_Range (s::e::_) bound) =
    case bound of
      NONE => Range (fold_pin_constant (translate_expr ctx s))
                    (fold_pin_constant (translate_expr ctx e))
    | SOME _ => Range (translate_expr ctx s) (translate_expr ctx e)) /\
  (translate_iter ctx var_ty (JIter_Array e _) =
    Array (translate_expr ctx e))
End


(* ===== Declaration Types ===== *)

(* Annotation bounds are compile-time values of their source expressions.
   annotation_resolved rejects a bound that does not evaluate. *)
Definition annotation_bound_def:
  annotation_bound ctx e =
    case constant_count (translate_expr ctx e) of SOME n => n | NONE => 0
End

Definition bound_resolved_def:
  bound_resolved ctx e = IS_SOME (constant_count (translate_expr ctx e))
End

Definition annotation_resolved_def:
  (annotation_resolved nominal_index all_import_maps ctx (JTA_Named name) =
    if name = "bool" ∨ name = "address" ∨ name = "self" ∨
       name = "decimal" ∨ name = "(void)"
    then T
    else IS_SOME (resolve_annotation_name nominal_index (expr_type_ctx ctx) name)) ∧
  (annotation_resolved nominal_index all_import_maps ctx (JTA_String n) =
    bound_resolved ctx n) ∧
  (annotation_resolved nominal_index all_import_maps ctx (JTA_Bytes n) =
    bound_resolved ctx n) ∧
  (annotation_resolved nominal_index all_import_maps ctx
      (JTA_StaticArray ty n) =
    (bound_resolved ctx n ∧
     annotation_resolved nominal_index all_import_maps ctx ty)) ∧
  (annotation_resolved nominal_index all_import_maps ctx
      (JTA_DynArray ty n) =
    (bound_resolved ctx n ∧
     annotation_resolved nominal_index all_import_maps ctx ty)) ∧
  (annotation_resolved nominal_index all_import_maps ctx
      (JTA_Tuple tys) =
    EVERY (annotation_resolved nominal_index all_import_maps ctx) tys) ∧
  (annotation_resolved nominal_index all_import_maps ctx
      (JTA_Qualified path name) =
    if name = "__interface__"
    then IS_SOME (resolve_qualified_type_path all_import_maps
                    (expr_type_ctx ctx) path)
    else IS_SOME (resolve_qualified_annotation nominal_index all_import_maps
                    (expr_type_ctx ctx) path name)) ∧
  (annotation_resolved nominal_index all_import_maps ctx _ = T)
Termination
  WF_REL_TAC `measure (λ(_,_,_,ann). json_type_annotation_size ann)` >> simp[]
End

(* Elaborate declaration annotations from syntax and the declaration index.
   This function is used only after annotation_resolved has succeeded. *)
Definition elaborate_annotation_def:
  (elaborate_annotation nominal_index all_import_maps ctx
      (JTA_Integer bits T) = BaseT (IntT bits)) ∧
  (elaborate_annotation nominal_index all_import_maps ctx
      (JTA_Integer bits F) = BaseT (UintT bits)) ∧
  (elaborate_annotation nominal_index all_import_maps ctx
      (JTA_BytesM m) = BaseT (BytesT (Fixed m))) ∧
  (elaborate_annotation nominal_index all_import_maps ctx
      (JTA_String n) = BaseT (StringT (annotation_bound ctx n))) ∧
  (elaborate_annotation nominal_index all_import_maps ctx
      (JTA_Bytes n) =
    BaseT (BytesT (Dynamic (annotation_bound ctx n)))) ∧
  (elaborate_annotation nominal_index all_import_maps ctx
      (JTA_StaticArray ty n) =
    ArrayT (elaborate_annotation nominal_index all_import_maps ctx ty)
      (Fixed (annotation_bound ctx n))) ∧
  (elaborate_annotation nominal_index all_import_maps ctx
      (JTA_DynArray ty n) =
    ArrayT (elaborate_annotation nominal_index all_import_maps ctx ty)
      (Dynamic (annotation_bound ctx n))) ∧
  (elaborate_annotation nominal_index all_import_maps ctx
      (JTA_Tuple tys) =
    TupleT (MAP (elaborate_annotation nominal_index all_import_maps ctx) tys)) ∧
  (elaborate_annotation nominal_index all_import_maps ctx
      (JTA_Named name) =
    if name = "bool" then BaseT BoolT
    else if name = "address" ∨ name = "self" then BaseT AddressT
    else if name = "decimal" then BaseT DecimalT
    else if name = "(void)" then NoneT
    else case resolve_annotation_name nominal_index (expr_type_ctx ctx) name of
         | SOME (kind, nsid) => nominal_type kind nsid
         | NONE => NoneT) ∧
  (elaborate_annotation nominal_index all_import_maps ctx
      (JTA_Qualified path name) =
    if name = "__interface__" then BaseT AddressT
    else case resolve_qualified_annotation nominal_index all_import_maps
                (expr_type_ctx ctx) path name of
         | SOME (kind, nsid) => nominal_type kind nsid
         | NONE => NoneT) ∧
  (elaborate_annotation nominal_index all_import_maps ctx JTA_None = NoneT)
Termination
  WF_REL_TAC `measure (λ(_,_,_,ann). json_type_annotation_size ann)` >> simp[]
End

Definition declaration_type_valid_def:
  declaration_type_valid nominal_index all_import_maps ctx inferred ann =
    (annotation_resolved nominal_index all_import_maps ctx ann ∧
     (ann = JTA_None ∨ inferred_type_consistent (expr_type_ctx ctx)
       (elaborate_annotation nominal_index all_import_maps ctx ann) inferred))
End

Definition canonical_decl_type_def:
  canonical_decl_type nominal_index all_import_maps ctx inferred ann =
    if ann = JTA_None then translate_type (expr_type_ctx ctx) inferred
    else elaborate_annotation nominal_index all_import_maps ctx ann
End


(* Error constructors are only meaningful as assert/raise reasons.  Preserve
   argument spelling here; declaration lookup validates and orders them later. *)
Definition custom_error_target_def:
  custom_error_target ctx (JE_Name name (SOME "error") src ty) =
    SOME (resolve_source_ref ctx src, name) ∧
  custom_error_target ctx
      (JE_Attribute obj name (SOME "error") base_name base_tc src ty) =
    SOME
      (resolve_func_module_ref ctx
        (JE_Attribute obj name (SOME "error") base_name base_tc src ty) src,
       name) /\
  custom_error_target ctx _ = NONE
End

Definition translate_custom_error_def:
  translate_custom_error ctx (JE_Call func args kwargs ty src) =
    (case custom_error_target ctx func of
     | NONE => NONE
     | SOME id =>
         SOME (CustomError id
           (MAP (translate_expr ctx) args)
           (translate_kwargs ctx kwargs))) ∧
  translate_custom_error ctx _ = NONE
End


(* ===== Statement Translation ===== *)

(* Vyper reads the name `UNREACHABLE` as an assert's message or a raise's
   exception as the unreachable marker, which fails with INVALID rather than
   reverting (vyper/semantics/analysis/local.py, vyper/codegen/stmt.py). *)
Definition is_unreachable_def:
  (is_unreachable (JE_Name name _ _ _) = (name = "UNREACHABLE")) /\
  (is_unreachable _ = F)
End

(* Local bindings enter the context after their initializer and stay within
   their block; loop binders are visible only in the loop body. *)
(* The values the pinned compiler's empty-value shortcut takes when they
   are written out (stmt.py _is_empty_value): [], b"" and empty(T); the
   shapes of the lowering's is_empty_value_expr. *)
Definition empty_value_tree_def:
  empty_value_tree (Builtin _ (MakeArray (SOME _) _) []) = T /\
  empty_value_tree (Literal _ (BytesL [])) = T /\
  empty_value_tree (TypeBuiltin _ Empty _ _) = T /\
  empty_value_tree _ = F
End

(* An assignment's value val' (translated from val).  Where the source names
   an empty constant, it is marked NamedConst: the pinned compiler's
   shortcut looks only at how the value is written, and copies a name's
   value in full.  As in membership_operand, the mark wraps the constant's
   value. *)
Definition assign_value_def:
  assign_value ctx val val' =
    case lookup_origin_entry ctx val of
    | SOME (v, _) =>
        if empty_value_tree v then
          Builtin (expr_type val') NamedConst [origin_retype (expr_type val') v]
        else val'
    | NONE => val'
End

Definition translate_stmt_def:
  (translate_stmt nominal_index all_import_maps ctx JS_Pass = Pass) /\
  (translate_stmt nominal_index all_import_maps ctx JS_Break = Break) /\
  (translate_stmt nominal_index all_import_maps ctx JS_Continue = Continue) /\
  (translate_stmt nominal_index all_import_maps ctx (JS_Expr e) = Expr (translate_expr ctx e)) /\
  (translate_stmt nominal_index all_import_maps ctx (JS_Return NONE) = Return NONE) /\
  (translate_stmt nominal_index all_import_maps ctx (JS_Return (SOME e)) = Return (SOME (translate_expr ctx e))) /\
  (translate_stmt nominal_index all_import_maps ctx (JS_Raise NONE) = Raise RaiseBare) /\
  (translate_stmt nominal_index all_import_maps ctx (JS_Raise (SOME e)) =
    if is_unreachable e then Raise RaiseUnreachable
    else
      case translate_custom_error ctx e of
      | SOME err => Raise (RaiseCustomError err)
      | NONE => Raise (RaiseReason (translate_expr ctx e))) /\
  (translate_stmt nominal_index all_import_maps ctx (JS_Assert test NONE) =
    Assert (translate_expr ctx test) AssertBare) /\
  (translate_stmt nominal_index all_import_maps ctx (JS_Assert test (SOME msg)) =
    Assert (translate_expr ctx test)
      (if is_unreachable msg then AssertUnreachable
       else
         case translate_custom_error ctx msg of
         | SOME err => AssertCustomError err
         | NONE => AssertReason (translate_expr ctx msg))) /\
  (translate_stmt nominal_index all_import_maps ctx (JS_Log (alias_opt, src, name) args) =
    let nsid =
      case alias_opt of
        NONE => resolve_source_ref ctx src
      | SOME alias => resolve_module_alias ctx alias src
    in
      Log (nsid, name) (MAP (translate_expr ctx) args)) /\
  (translate_stmt nominal_index all_import_maps ctx (JS_If test body orelse) =
    If (translate_expr ctx test)
       (translate_stmts nominal_index all_import_maps ctx body)
       (translate_stmts nominal_index all_import_maps ctx orelse)) /\
  (translate_stmt nominal_index all_import_maps ctx (JS_For var ty ann iter body) =
    let var_ty = canonical_decl_type nominal_index all_import_maps ctx ty ann in
    let body_ctx = expr_with_local_types ctx
      ((var, var_ty) :: expr_local_types ctx) in
    For var var_ty (translate_iter ctx var_ty iter)
        (get_iter_bound ctx iter)
        (translate_stmts nominal_index all_import_maps body_ctx body)) /\
  (translate_stmt nominal_index all_import_maps ctx (JS_Assign tgt val) =
    Assign (translate_target ctx tgt)
      (assign_value ctx val (translate_expr ctx val))) /\
  (translate_stmt nominal_index all_import_maps ctx (JS_AnnAssign var ty ann val) =
    AnnAssign var
      (canonical_decl_type nominal_index all_import_maps ctx ty ann)
      (assign_value ctx val (translate_expr ctx val))) /\
  (translate_stmt nominal_index all_import_maps ctx (JS_AugAssign tgt op val) =
    let val' = exponent_operand op (translate_expr ctx val) in
    AugAssign (expr_type val') (translate_base_target ctx tgt)
      (translate_binop op) val') /\
  (translate_stmt nominal_index all_import_maps ctx (JS_Append tgt val) =
    Append (translate_base_target ctx tgt) (translate_expr ctx val)) /\
  (translate_stmts nominal_index all_import_maps ctx [] = []) /\
  (translate_stmts nominal_index all_import_maps ctx (stmt :: rest) =
    let next_ctx =
      case stmt of
        JS_AnnAssign var ty ann _ =>
          expr_with_local_types ctx
            ((var, canonical_decl_type nominal_index all_import_maps ctx ty ann)
             :: expr_local_types ctx)
      | _ => ctx
    in
      translate_stmt nominal_index all_import_maps ctx stmt ::
      translate_stmts nominal_index all_import_maps next_ctx rest)
Termination
  WF_REL_TAC `measure (λitem. case item of
      INL (_,_,_,stmt) => json_stmt_size stmt
    | INR (_,_,_,stmts) => list_size json_stmt_size stmts)` >>
  simp[json_stmt_size_def]
End


(* ===== Top-level Translation ===== *)
