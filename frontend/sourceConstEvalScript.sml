Theory sourceConstEval
Ancestors
  sourceConstAST sourceConstBuiltin alist integer int_bitwise logroot
Libs
  ratLib

val () = ratLib.deprecate_rat ();

(* TOP-LEVEL: source_const_eval. Helpers implement mathematical operations and
   eager child-result collection. This is an opt-in, partial source evaluator,
   NOT a source type checker or a runtime-width/reification certificate.
   See sourceConstCore.md for the pinned semantic boundary. *)

(* ===== Eager result algebra ===== *)

(* Invalid children dominate unsupported and dynamic children, including those
   to their left. Within one class the first source-order failure wins.
   In particular a dynamic/False Boolean head cannot hide a zero divisor. *)
Definition source_const_combine_def:
  source_const_combine f left right =
    case (left,right) of
    | (SC_Invalid e,_) => SC_Invalid e
    | (_,SC_Invalid e) => SC_Invalid e
    | (SC_Unsupported u,_) => SC_Unsupported u
    | (_,SC_Unsupported u) => SC_Unsupported u
    | (SC_NotConstant,_) => SC_NotConstant
    | (_,SC_NotConstant) => SC_NotConstant
    | (SC_Value x,SC_Value y) => f x y
End

Definition source_const_collect_def:
  source_const_collect [] = SC_Value [] /\
  source_const_collect (r::rs) =
    source_const_combine (\v vs. SC_Value (v::vs)) r (source_const_collect rs)
End

Definition source_const_then_def:
  source_const_then result f =
    case result of
    | SC_Value v => f v
    | SC_NotConstant => SC_NotConstant
    | SC_Invalid e => SC_Invalid e
    | SC_Unsupported u => SC_Unsupported u
End

(* Incomplete parent rules never claim NotConstant: their acceptance/domain is
   unknown even with dynamic children (e.g. method_id with a runtime string).
   Still preserve every invalid child and the first unsupported child. *)
Definition source_const_unimplemented_def:
  source_const_unimplemented reason results =
    case source_const_collect results of
    | SC_Invalid e => SC_Invalid e
    | SC_Unsupported u => SC_Unsupported u
    | _ => SC_Unsupported reason
End

(* ===== Literal and environment validation ===== *)

Definition source_const_hex_ok_def:
  source_const_hex_ok s =
    (TAKE 2 s = "0x" /\ 2 < LENGTH s /\ EVEN (LENGTH s) /\
     EVERY (\c. MEM c "0123456789abcdefABCDEF") (DROP 2 s))
End

Definition source_const_value_ok_def:
  source_const_value_ok (SCV_Bytes bs) = EVERY (\b. b < 256) bs /\
  source_const_value_ok (SCV_Hex s) = source_const_hex_ok s /\
  source_const_value_ok (SCV_String s) = EVERY (\c. ORD c < 128) s /\
  source_const_value_ok (SCV_List vs) = EVERY source_const_value_ok vs /\
  source_const_value_ok (SCV_Tuple vs) =
    (vs <> [] /\ EVERY source_const_value_ok vs) /\
  source_const_value_ok (SCV_Struct path fields) =
    (path <> [] /\ ALL_DISTINCT (MAP FST fields) /\
     EVERY (\field. source_const_value_ok (SND field)) fields) /\
  source_const_value_ok _ = T
End

Definition source_const_literal_def:
  source_const_literal (SCL_Int i) = SC_Value (SCV_Int i) /\
  source_const_literal (SCL_Bool b) = SC_Value (SCV_Bool b) /\
  source_const_literal (SCL_Decimal coefficient places) =
    (if places <= 10 then
       SC_Value (SCV_Decimal (coefficient * &(10 ** (10 - places))))
     else SC_Invalid SCErr_DecimalPrecision) /\
  source_const_literal (SCL_String s) =
    (if EVERY (\c. ORD c < 128) s then SC_Value (SCV_String s)
     else SC_Invalid SCErr_StringCharacter) /\
  source_const_literal (SCL_Bytes bs) =
    (if EVERY (\b. b < 256) bs then SC_Value (SCV_Bytes bs)
     else SC_Invalid SCErr_Octet) /\
  source_const_literal (SCL_Hex s) =
    (if source_const_hex_ok s then SC_Value (SCV_Hex s)
     else SC_Invalid SCErr_HexToken)
End

Definition source_const_lookup_def:
  source_const_lookup env path =
    case ALOOKUP env path of
    | NONE => SC_Unsupported (SCS_UnresolvedName path)
    | SOME SC_DynamicBinding => SC_NotConstant
    | SOME (SC_Constant v) =>
        if source_const_value_ok v then SC_Value v else SC_Invalid SCErr_Domain
End

(* ===== Mathematical operator core ===== *)

(* HOL quot truncates toward zero, unlike HOL integer /. Remainder consequently
   has the dividend's sign. The caller rejects zero BEFORE these total helpers;
   the zero case below avoids HOL quot's unspecified zero-divisor value.
   No intermediate integer is clamped, wrapped or checked at a runtime width. *)
Definition source_const_quot_def:
  source_const_quot (a:int) (b:int) = if b = 0 then 0 else a quot b
End

Definition source_const_rem_def:
  source_const_rem a b = a - source_const_quot a b * b
End

(* The pinned Pow uses binary64 math.log as an anti-hang heuristic, NOT a
   uint256 result bound. Keep a deliberately wide uncertainty band rather
   than silently replace that host-float test by an exact 2^256 check.
   Outside the band we can compute/reject without huge exponentiation.
   The |a|<=1 fast path precedes the bound, exactly as in nodes.Pow. *)
Definition source_const_power_def:
  source_const_power (a:int) b =
    if b < 0 then SC_Invalid SCErr_NegativePower
    else if b = 0 then SC_Value (SCV_Int 1)
    else if ABS a <= 1 then
      SC_Value (SCV_Int (if a = 0 then 0 else if a = 1 \/ EVEN (Num b) then 1 else -1))
    else if 258 <= b \/ 2 ** 258 <= ABS a then SC_Invalid SCErr_PowerBound
    else let p = a ** Num b in
      if ABS p <= 2 ** 256 \/ ABS p = 2 ** 257 then SC_Value (SCV_Int p)
      else if 2 ** 258 <= ABS p then SC_Invalid SCErr_PowerBound
      else SC_Unsupported SCS_Power
End

Definition source_const_integer_binary_def:
  source_const_integer_binary bop a b =
    case bop of
    | SCB_Add => SC_Value (SCV_Int (a + b))
    | SCB_Sub => SC_Value (SCV_Int (a - b))
    | SCB_Mul => SC_Value (SCV_Int (a * b))
    | SCB_Div => if b = 0 then SC_Invalid SCErr_ZeroDivisor
                 else SC_Invalid SCErr_Domain
    | SCB_FloorDiv => if b = 0 then SC_Invalid SCErr_ZeroDivisor
                      else SC_Value (SCV_Int (source_const_quot a b))
    | SCB_Mod => if b = 0 then SC_Invalid SCErr_ZeroDivisor
                 else SC_Value (SCV_Int (source_const_rem a b))
    | SCB_Pow => source_const_power a b
    | SCB_LShift => if 0 <= b /\ b <= 256 then
                     SC_Value (SCV_Int (int_shift_left (Num b) a))
                   else SC_Invalid SCErr_ShiftCount
    | SCB_RShift => if 0 <= b /\ b <= 256 then
                     SC_Value (SCV_Int (int_shift_right (Num b) a))
                   else SC_Invalid SCErr_ShiftCount
    | SCB_BitAnd => SC_Value (SCV_Int (int_and a b))
    | SCB_BitOr => SC_Value (SCV_Int (int_or a b))
    | SCB_BitXor => SC_Value (SCV_Int (int_xor a b))
End

(* ===== Decimal context and per-operation quantization ===== *)

(* Python Decimal uses precision 78 / ROUND_HALF_EVEN. The integer coefficient
   keeps ten fractional places, but multiplication first has TWENTY; rounding
   that intermediate must precede ROUND_DOWN quantization back to ten. *)
Definition source_const_digits_def:
  source_const_digits n = if n = 0 then 1 else SUC (LOG 10 n)
End

Definition source_const_round_ratio_def:
  source_const_round_ratio n d =
    let q = n DIV d; r = n MOD d in
      if d < 2 * r \/ (d = 2 * r /\ ODD q) then q + 1 else q
End

Definition source_const_context_def:
  source_const_context (a:int) =
    let k = source_const_digits (Num (ABS a)) - 78; d = 10 ** k;
        c = &(source_const_round_ratio (Num (ABS a)) d) * &d in
      if a < 0 then -c else c
End

(* Round a nonnegative rational to 78 significant digits, then truncate to an
   integer. n/d here is the desired coefficient at scale 10^10. Digit lengths
   locate the exponent without a real/logarithmic approximation. *)
Definition source_const_decimal_ratio_def:
  source_const_decimal_ratio n d =
    let e = (&(source_const_digits n):int) - &(source_const_digits d);
        above = if 0 <= e then d * 10 ** Num e <= n
                else d <= n * 10 ** Num (-e);
        k = (if above then e else e - 1) - 77 in
      if 0 <= k then
        source_const_round_ratio n (d * 10 ** Num k) * 10 ** Num k
      else source_const_round_ratio (n * 10 ** Num (-k)) d DIV 10 ** Num (-k)
End

Definition source_const_decimal_quantize_def:
  source_const_decimal_quantize (c:int) =
    if ABS c < 10 ** 78 then SC_Value (SCV_Decimal c)
    else SC_Invalid SCErr_DecimalPrecision
End

(* The exponent-limit/underflow behavior of the host Decimal context is not
   modeled. An explicit conservative input envelope keeps supported operations
   far from Emax/Emin; outside it report Unsupported, not a mathematical value.
   This is NOT DecimalT's runtime bound. *)
Definition source_const_decimal_small_def:
  source_const_decimal_small (a:int) = (source_const_digits (Num (ABS a)) <= 1000)
End

Definition source_const_decimal_binary_def:
  source_const_decimal_binary bop (a:int) b =
    if (bop = SCB_Div \/ bop = SCB_FloorDiv \/ bop = SCB_Mod) /\ b = 0 then
      SC_Invalid SCErr_ZeroDivisor
    else if (bop = SCB_LShift \/ bop = SCB_RShift) /\
            (b < 0 \/ 256 * 10 ** 10 < b) then SC_Invalid SCErr_ShiftCount
    else if bop = SCB_Pow \/ bop = SCB_FloorDiv \/ bop = SCB_LShift \/
            bop = SCB_RShift \/ bop = SCB_BitAnd \/ bop = SCB_BitOr \/
            bop = SCB_BitXor then SC_Invalid SCErr_Domain
    else if ~source_const_decimal_small a \/ ~source_const_decimal_small b then
      SC_Unsupported SCS_DecimalOperation
    else case bop of
    | SCB_Add => SC_Value (SCV_Decimal (source_const_context (a + b)))
    | SCB_Sub => SC_Value (SCV_Decimal (source_const_context (a - b)))
    | SCB_Mul => source_const_decimal_quantize
        (source_const_quot (source_const_context (a * b)) (10 ** 10))
    (* Div._op recomputes a negative result as -(-left / right): the inner
       unary minus rounds LEFT to the Decimal context before dividing. *)
    | SCB_Div => let neg = ((a < 0) <> (b < 0));
                       aa = if neg then source_const_context a else a;
                       c = &(source_const_decimal_ratio
                              (Num (ABS aa) * 10 ** 10) (Num (ABS b))) in
        source_const_decimal_quantize (if neg then -c else c)
    | SCB_Mod => let aa = source_const_context (ABS a);
                     bb = source_const_context (ABS b) in
        if 10 ** 78 <= source_const_quot aa bb then
          SC_Invalid SCErr_DecimalPrecision
        else let c = source_const_context (source_const_rem aa bb) in
          SC_Value (SCV_Decimal (if a < 0 then -c else c))
    | _ => SC_Invalid SCErr_Domain
End

Definition source_const_unary_def:
  source_const_unary SCU_Neg (SCV_Int i) = SC_Value (SCV_Int (-i)) /\
  source_const_unary SCU_Neg (SCV_Decimal i) =
    (if source_const_decimal_small i then SC_Value (SCV_Decimal (source_const_context (-i)))
     else SC_Unsupported SCS_DecimalOperation) /\
  source_const_unary SCU_Not (SCV_Bool b) = SC_Value (SCV_Bool (~b)) /\
  source_const_unary SCU_Invert (SCV_Int i) =
    SC_Value (SCV_Int (int_xor (2 ** 256 - 1) i)) /\
  source_const_unary _ _ = SC_Invalid SCErr_Domain
End

Definition source_const_binary_def:
  source_const_binary bop (SCV_Int a) (SCV_Int b) =
    source_const_integer_binary bop a b /\
  source_const_binary bop (SCV_Decimal a) (SCV_Decimal b) =
    source_const_decimal_binary bop a b /\
  source_const_binary _ _ _ = SC_Invalid SCErr_Domain
End

Definition source_const_integer_compare_def:
  source_const_integer_compare cop (a:int) b =
    case cop of
    | SCC_Eq => SC_Value (SCV_Bool (a = b))
    | SCC_NotEq => SC_Value (SCV_Bool (a <> b))
    | SCC_Lt => SC_Value (SCV_Bool (a < b))
    | SCC_Le => SC_Value (SCV_Bool (a <= b))
    | SCC_Gt => SC_Value (SCV_Bool (a > b))
    | SCC_Ge => SC_Value (SCV_Bool (a >= b))
    | SCC_In => SC_Unsupported SCS_Membership
    | SCC_NotIn => SC_Unsupported SCS_Membership
End

(* Folded AST node kinds, not source types. List homogeneity is shallow:
   [[1],[True]] has two List nodes and is subscriptable by the pinned folder. *)
Definition source_const_kind_def:
  source_const_kind (SCV_Int _) = 0 /\
  source_const_kind (SCV_Bool _) = 1 /\
  source_const_kind (SCV_Decimal _) = 2 /\
  source_const_kind (SCV_String _) = 3 /\
  source_const_kind (SCV_Bytes _) = 4 /\
  source_const_kind (SCV_Hex _) = 5 /\
  source_const_kind (SCV_List _) = 6 /\
  source_const_kind (SCV_Tuple _) = 7 /\
  source_const_kind (SCV_Struct _ _) = 8 /\
  source_const_kind (SCV_BytesType _ _) = 9
End

Definition source_const_homogeneous_def:
  source_const_homogeneous [] = T /\
  source_const_homogeneous (v::vs) =
    EVERY (\w. source_const_kind w = source_const_kind v) vs
End

(* Membership intentionally uses Python value equality, NOT the normal
   same-kind Compare rule. Bool/Int/Decimal cross-compare numerically; Hex's
   raw spelling is a string here, without the normal Hex case normalization. *)
Definition source_const_numeric_def:
  source_const_numeric (SCV_Int i) = SOME (i * 10 ** 10) /\
  source_const_numeric (SCV_Bool b) = SOME (if b then 10 ** 10 else 0) /\
  source_const_numeric (SCV_Decimal i) = SOME i /\
  source_const_numeric _ = NONE
End

Definition source_const_python_equal_def:
  source_const_python_equal left right =
    case (source_const_numeric left, source_const_numeric right) of
    | (SOME a,SOME b) => a = b
    | _ => case (left,right) of
           | (SCV_String a,SCV_Hex b) => a = b
           | (SCV_Hex a,SCV_String b) => a = b
           | _ => left = right
End

Definition source_const_membership_def:
  source_const_membership cop left (SCV_List vs) =
    (if source_const_kind left < 6 /\
        EVERY (\v. source_const_kind v < 6) vs /\
        source_const_homogeneous vs then
       SC_Value (SCV_Bool
         (if cop = SCC_In then EXISTS (source_const_python_equal left) vs
          else ~EXISTS (source_const_python_equal left) vs))
     else SC_Invalid SCErr_Domain) /\
  source_const_membership _ _ _ = SC_Invalid SCErr_Domain
End

Definition source_const_hex_lower_def:
  source_const_hex_lower s =
    MAP (\c. if 65 <= ORD c /\ ORD c <= 70 then CHR (ORD c + 32) else c) s
End

Definition source_const_equal_def:
  source_const_equal (SCV_Hex a) (SCV_Hex b) =
    (source_const_hex_lower a = source_const_hex_lower b) /\
  source_const_equal a b = (a = b)
End

(* Equality domains are exact literal kinds outside membership; bool is not
   an integer and hex is not Bytes. Both numeric kinds support ordering. *)
Definition source_const_equality_domain_def:
  source_const_equality_domain (SCV_Bool _) (SCV_Bool _) = T /\
  source_const_equality_domain (SCV_String _) (SCV_String _) = T /\
  source_const_equality_domain (SCV_Bytes _) (SCV_Bytes _) = T /\
  source_const_equality_domain (SCV_Hex _) (SCV_Hex _) = T /\
  source_const_equality_domain _ _ = F
End

Definition source_const_compare_def:
  source_const_compare cop left right =
    if cop = SCC_In \/ cop = SCC_NotIn then source_const_membership cop left right
    else case (left,right) of
    | (SCV_Int a,SCV_Int b) => source_const_integer_compare cop a b
    | (SCV_Decimal a,SCV_Decimal b) => source_const_integer_compare cop a b
    | _ => if source_const_equality_domain left right /\
              (cop = SCC_Eq \/ cop = SCC_NotEq) then
             SC_Value (SCV_Bool (if cop = SCC_Eq then source_const_equal left right
                                else ~source_const_equal left right))
           else SC_Invalid SCErr_Domain
End

Definition source_const_is_bool_def:
  source_const_is_bool (SCV_Bool _) = T /\
  source_const_is_bool _ = F
End

Definition source_const_boolean_def:
  source_const_boolean bop vs =
    if LENGTH vs < 2 then SC_Invalid SCErr_BooleanArity
    else if ~EVERY source_const_is_bool vs then SC_Invalid SCErr_Domain
    else SC_Value (SCV_Bool
      (case bop of SCB_And => EVERY (\v. v = SCV_Bool T) vs
                 | SCB_Or => EXISTS (\v. v = SCV_Bool T) vs))
End

Definition source_const_tuple_def:
  source_const_tuple vs =
    if vs = [] then SC_Invalid SCErr_EmptyTuple else SC_Value (SCV_Tuple vs)
End

(* Only literal List nodes are subscripted by the pinned folder; tuple,
   string, bytes and Hex are NOT sequence-folding domains. Check shallow
   homogeneity before index type/bounds, even when the selected item is valid.
   No Python negative-index adjustment and no runtime-width index coercion. *)
Definition source_const_subscript_def:
  source_const_subscript (SCV_List vs) (SCV_Int i) =
    (if ~source_const_homogeneous vs then SC_Invalid SCErr_Domain
     else if EXISTS (\v. source_const_kind v = 8) vs then
       SC_Unsupported SCS_Subscript
     else if i < 0 \/ &(LENGTH vs) <= i then SC_Invalid SCErr_Index
     else SC_Value (EL (Num i) vs)) /\
  source_const_subscript _ _ = SC_Invalid SCErr_Domain
End

(* ===== Pure recursive evaluation ===== *)

(* Validate the result as well as original builtin domains. In particular this
   preserves the evaluator's structural invariant independently of hashing. *)
Definition source_const_checked_builtin_def:
  source_const_checked_builtin builtin args keywords =
    source_const_then (source_const_builtin builtin args keywords)
      (\v. if source_const_value_ok v then SC_Value v else SC_Invalid SCErr_Domain)
End

Definition source_const_builtin_result_def:
  source_const_builtin_result builtin result =
    if builtin = SCB_MethodId /\ result = SC_NotConstant then SC_Invalid SCErr_Domain
    else if source_const_builtin_arity builtin = NONE /\ result = SC_NotConstant then
      SC_Unsupported (SCS_Builtin builtin)
    else result
End

(* All child expressions are collected before applying a source rule, even for
   unsupported parents/calls. Unsupported forms cannot mask an invalid child.
   Calls preserve positional/keyword syntax; builtin identity resolution and
   signature/type validation remain prerequisites for future builtin rules. *)
Definition source_const_eval_def:
  source_const_eval env (SCE_Literal lit) = source_const_literal lit /\
  source_const_eval env (SCE_Name path) = source_const_lookup env path /\
  source_const_eval env SCE_Dynamic = SC_NotConstant /\
  source_const_eval env (SCE_BytesType fixed e) =
    source_const_then (source_const_eval env e) (source_const_bytes_type fixed) /\
  source_const_eval env (SCE_Unary uop e) =
    source_const_then (source_const_eval env e) (source_const_unary uop) /\
  source_const_eval env (SCE_Binary bop left right) =
    source_const_combine (source_const_binary bop)
      (source_const_eval env left) (source_const_eval env right) /\
  source_const_eval env (SCE_Boolean bop es) =
    source_const_then (source_const_collect (MAP (source_const_eval env) es))
      (source_const_boolean bop) /\
  source_const_eval env (SCE_Compare cop left right) =
    source_const_combine (source_const_compare cop)
      (source_const_eval env left) (source_const_eval env right) /\
  source_const_eval env (SCE_List es) =
    source_const_then (source_const_collect (MAP (source_const_eval env) es))
      (\vs. SC_Value (SCV_List vs)) /\
  source_const_eval env (SCE_Tuple es) =
    source_const_then (source_const_collect (MAP (source_const_eval env) es))
      source_const_tuple /\
  source_const_eval env (SCE_Subscript value index) =
    source_const_combine source_const_subscript
      (source_const_eval env value) (source_const_eval env index) /\
  source_const_eval env (SCE_Builtin builtin args keywords) =
    source_const_builtin_result builtin
      (source_const_combine
        (\vs ks. source_const_checked_builtin builtin vs (ZIP (MAP FST keywords,ks)))
        (source_const_collect (MAP (source_const_eval env) args))
        (source_const_collect (MAP (\kw. source_const_eval env (SND kw)) keywords))) /\
  source_const_eval env (SCE_Call callee args keywords) =
    source_const_unimplemented SCS_Call
      (source_const_eval env callee ::
       (MAP (source_const_eval env) args ++
        MAP (\kw. source_const_eval env (SND kw)) keywords)) /\
  source_const_eval env (SCE_Unsupported tag es) =
    source_const_unimplemented (SCS_Syntax tag) (MAP (source_const_eval env) es)
End
