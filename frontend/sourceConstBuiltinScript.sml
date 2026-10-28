Theory sourceConstBuiltin
Ancestors
  sourceConstAST integer arithmetic list string keccak

(* Resolved builtin identities only. This module does not recognize callees by
   spelling. BytesType's Boolean is T for bytesM, F for Bytes[N]; the resolver
   must establish the type-constructor identity before building that syntax. *)
Definition source_const_bytes_type_def:
  source_const_bytes_type fixed (SCV_Int n) =
    (if 0 < n /\ (~fixed \/ n <= 32) then
       SC_Value (SCV_BytesType fixed (Num n))
     else SC_Invalid SCErr_Type) /\
  source_const_bytes_type _ _ = SC_Invalid SCErr_Type
End

Definition source_const_uint256_def:
  source_const_uint256 (n:int) = (0 <= n /\ n < 2 ** 256)
End

Definition source_const_int256_def:
  source_const_int256 (n:int) = (-(2 ** 255) <= n /\ n < 2 ** 255)
End

Definition source_const_common_integer_def:
  source_const_common_integer a b =
    ((source_const_uint256 a /\ source_const_uint256 b) \/
     (source_const_int256 a /\ source_const_int256 b))
End

Definition source_const_decimal_domain_def:
  source_const_decimal_domain (n:int) = (-(2 ** 167) <= n /\ n < 2 ** 167)
End

(* Logarithmic recursion: never construct the (possibly 2^256-bit) power. *)
Definition source_const_modexp_def:
  source_const_modexp a n =
    if n = 0 then 1 else
    let p = source_const_modexp a (n DIV 2);
        q = (p * p) MOD (2 ** 256) in
      if EVEN n then q else (a * q) MOD (2 ** 256)
Termination
  WF_REL_TAC `measure SND` >> simp[]
End

Definition source_const_hex_digit_def:
  source_const_hex_digit c =
    if ORD c <= 57 then ORD c - 48
    else if ORD c <= 70 then ORD c - 55 else ORD c - 87
End

Definition source_const_hex_decode_def:
  source_const_hex_decode [] = [] /\
  source_const_hex_decode [c] = [] /\
  source_const_hex_decode (a::b::cs) =
    (16 * source_const_hex_digit a + source_const_hex_digit b) ::
      source_const_hex_decode cs
End

Definition source_const_hex_encode_def:
  source_const_hex_encode bs =
    "0x" ++ FLAT (MAP (\b.
      [EL ((b DIV 16) MOD 16) "0123456789abcdef";
       EL (b MOD 16) "0123456789abcdef"]) bs)
End

(* The dependency proves Keccak_256_w64_thm against bit-level Keccak, and
   supplies a cv translation with unconditional Keccak_256_w64_pre. *)
Definition source_const_keccak_def:
  source_const_keccak bs =
    MAP w2n (Keccak_256_w64 (MAP (n2w:num -> word8) bs))
End

Definition source_const_fixed_hex_def:
  source_const_fixed_hex s =
    (TAKE 2 s = "0x" /\ 2 < LENGTH s /\ LENGTH s <= 66 /\
     EVEN (LENGTH s) /\
     (EVERY (\c. MEM c "0123456789abcdef") (DROP 2 s) \/
      EVERY (\c. MEM c "0123456789ABCDEF") (DROP 2 s)))
End

(* EIP-55, derived from the original token and Keccak of its lowercase
   ASCII digits. No compiler type/checksum metadata is evidence. Digits are
   case-neutral; letters use the high bit of the corresponding hash nibble. *)
Definition source_const_address_hex_def:
  source_const_address_hex s =
    (TAKE 2 s = "0x" /\ LENGTH s = 42 /\
     EVERY (\c. MEM c "0123456789abcdefABCDEF") (DROP 2 s) /\
     let body = DROP 2 s;
         lower = MAP (\c. if MEM c "ABCDEF" then CHR (ORD c + 32) else c) body;
         hash = source_const_keccak (MAP ORD lower) in
       body = GENLIST (\i.
         let c = EL i lower;
             byte = EL (i DIV 2) hash;
             nibble = if EVEN i then byte DIV 16 else byte MOD 16 in
           if MEM c "abcdef" /\ 8 <= nibble then CHR (ORD c - 32) else c) 40)
End

Definition source_const_byte_input_def:
  source_const_byte_input (SCV_String s) =
    (if EVERY (\c. ORD c < 128) s then SOME (MAP ORD s) else NONE) /\
  source_const_byte_input (SCV_Bytes bs) =
    (if EVERY (\b. b < 256) bs then SOME bs else NONE) /\
  source_const_byte_input (SCV_Hex s) =
    (if source_const_fixed_hex s then SOME (source_const_hex_decode (DROP 2 s))
     else NONE) /\
  source_const_byte_input _ = NONE
End

Definition source_const_builtin_numeric_def:
  source_const_builtin_numeric SCB_Abs [SCV_Int a] =
    (if source_const_int256 a /\ source_const_int256 (ABS a) then
       SC_Value (SCV_Int (ABS a)) else SC_Invalid SCErr_Overflow) /\
  source_const_builtin_numeric SCB_PowMod256 [SCV_Int a; SCV_Int b] =
    (if source_const_uint256 a /\ source_const_uint256 b then
       SC_Value (SCV_Int (&(source_const_modexp (Num a) (Num b))))
     else SC_Invalid SCErr_Overflow) /\
  source_const_builtin_numeric SCB_Uint256AddMod [SCV_Int a; SCV_Int b; SCV_Int c] =
    (if c = 0 then SC_Invalid SCErr_ZeroDivisor
     else if source_const_uint256 a /\ source_const_uint256 b /\ source_const_uint256 c
     then SC_Value (SCV_Int ((a + b) % c)) else SC_Invalid SCErr_Overflow) /\
  source_const_builtin_numeric SCB_Uint256MulMod [SCV_Int a; SCV_Int b; SCV_Int c] =
    (if c = 0 then SC_Invalid SCErr_ZeroDivisor
     else if source_const_uint256 a /\ source_const_uint256 b /\ source_const_uint256 c
     then SC_Value (SCV_Int ((a * b) % c)) else SC_Invalid SCErr_Overflow) /\
  source_const_builtin_numeric SCB_Min [SCV_Int a; SCV_Int b] =
    (if source_const_common_integer a b then SC_Value (SCV_Int (if a <= b then a else b))
     else SC_Invalid SCErr_Domain) /\
  source_const_builtin_numeric SCB_Max [SCV_Int a; SCV_Int b] =
    (if source_const_common_integer a b then SC_Value (SCV_Int (if a <= b then b else a))
     else SC_Invalid SCErr_Domain) /\
  source_const_builtin_numeric SCB_Min [SCV_Decimal a; SCV_Decimal b] =
    (if source_const_decimal_domain a /\ source_const_decimal_domain b then
       SC_Value (SCV_Decimal (if a <= b then a else b)) else SC_Invalid SCErr_Domain) /\
  source_const_builtin_numeric SCB_Max [SCV_Decimal a; SCV_Decimal b] =
    (if source_const_decimal_domain a /\ source_const_decimal_domain b then
       SC_Value (SCV_Decimal (if a <= b then b else a)) else SC_Invalid SCErr_Domain) /\
  source_const_builtin_numeric _ _ = SC_Invalid SCErr_Domain
End

Definition source_const_method_id_def:
  source_const_method_id (SCV_String s) fixed =
    (if EVERY (\c. ORD c < 128) s /\ ~MEM #" " s then
       let selector = TAKE 4 (source_const_keccak (MAP ORD s)) in
         SC_Value (if fixed then SCV_Hex (source_const_hex_encode selector)
                   else SCV_Bytes selector)
     else SC_Invalid SCErr_Domain) /\
  source_const_method_id _ _ = SC_Invalid SCErr_Domain
End

Definition source_const_builtin_arity_def:
  source_const_builtin_arity SCB_Len = SOME (1:num) /\
  source_const_builtin_arity SCB_Keccak256 = SOME 1 /\
  source_const_builtin_arity SCB_MethodId = SOME 1 /\
  source_const_builtin_arity SCB_Abs = SOME 1 /\
  source_const_builtin_arity SCB_Min = SOME 2 /\
  source_const_builtin_arity SCB_Max = SOME 2 /\
  source_const_builtin_arity SCB_PowMod256 = SOME 2 /\
  source_const_builtin_arity SCB_Uint256AddMod = SOME 3 /\
  source_const_builtin_arity SCB_Uint256MulMod = SOME 3 /\
  source_const_builtin_arity _ = NONE
End

Definition source_const_builtin_apply_def:
  source_const_builtin_apply builtin args keywords =
    case builtin of
    | SCB_MethodId =>
        (case args of
         | [arg] => (case keywords of
             | [] => source_const_method_id arg F
             | [(key,SCV_BytesType fixed width)] =>
                 if key = "output_type" /\ width = 4 then source_const_method_id arg fixed
                 else SC_Invalid SCErr_Type
             | _ => SC_Invalid SCErr_Type)
         | _ => SC_Invalid SCErr_Type)
    | SCB_Len =>
        (case args of
         | [arg] =>
             if (case arg of SCV_Hex _ => F | _ => T) then
               (case source_const_byte_input arg of
                | SOME bs => SC_Value (SCV_Int (&(LENGTH bs)))
                | NONE => SC_Invalid SCErr_Domain)
             else SC_Invalid SCErr_Domain
         | _ => SC_Invalid SCErr_Domain)
    | SCB_Keccak256 =>
        (case args of
         | [arg] =>
             if (case arg of SCV_Hex s => LENGTH s = 66 | _ => T) then
               (case source_const_byte_input arg of
                | SOME bs => SC_Value (SCV_Hex (source_const_hex_encode (source_const_keccak bs)))
                | NONE => SC_Invalid SCErr_Domain)
             else SC_Invalid SCErr_Domain
         | _ => SC_Invalid SCErr_Domain)
    | _ => source_const_builtin_numeric builtin args
End

Definition source_const_builtin_def:
  source_const_builtin builtin args keywords =
    case source_const_builtin_arity builtin of
    | NONE => SC_Unsupported (SCS_Builtin builtin)
    | SOME arity =>
      if LENGTH args <> arity then SC_Invalid SCErr_Arity
      else if ~(keywords = [] \/
                (builtin = SCB_MethodId /\ MAP FST keywords = ["output_type"]))
      then SC_Invalid SCErr_Keyword
      else source_const_builtin_apply builtin args keywords
End
