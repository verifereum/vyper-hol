Theory sourceConstValue
Ancestors
  sourceConstEval vyperTypeSystem vyperValueOperation vyperTyping

(* Local, opt-in bridge from mathematical source values to runtime literals.
   No source-expression acceptance or compiler/lowering claim is made here.
   SCV_BytesType is a descriptor, never data. See sourceConstValue.md. *)

(* ===== Independent semantic representation ===== *)

(* This relation mentions runtime value constructors directly, not reification
   output. Octet validation prevents n2w from silently truncating source data.
   Decimal coefficients already have the source evaluator's 10^10 scaling. *)
Definition source_const_represents_def:
  source_const_represents (SCV_Int n) v = (v = IntV n) /\
  source_const_represents (SCV_Bool b) v = (v = BoolV b) /\
  source_const_represents (SCV_Decimal n) v = (v = DecimalV n) /\
  source_const_represents (SCV_String s) v =
    (EVERY (\c. ORD c < 128) s /\ v = StringV s) /\
  source_const_represents (SCV_Bytes bs) v =
    (EVERY (\b. b < 256) bs /\ v = BytesV (MAP n2w bs)) /\
  source_const_represents (SCV_Hex s) v =
    (source_const_hex_ok s /\
     v = BytesV (MAP n2w (source_const_hex_decode (DROP 2 s)))) /\
  source_const_represents (SCV_BytesType fixed n) v = F /\
  source_const_represents (SCV_List vs) v = F /\
  source_const_represents (SCV_Tuple vs) v = F /\
  source_const_represents (SCV_Struct path fields) v = F
End

(* ===== Executable literal reification ===== *)

Definition source_const_value_literal_def:
  source_const_value_literal (SCV_Int n) = SOME (IntL n) /\
  source_const_value_literal (SCV_Bool b) = SOME (BoolL b) /\
  source_const_value_literal (SCV_Decimal n) = SOME (DecimalL n) /\
  source_const_value_literal (SCV_String s) =
    (if EVERY (\c. ORD c < 128) s then SOME (StringL s) else NONE) /\
  source_const_value_literal (SCV_Bytes bs) =
    (if EVERY (\b. b < 256) bs then SOME (BytesL (MAP n2w bs)) else NONE) /\
  source_const_value_literal (SCV_Hex s) =
    (if source_const_hex_ok s then
       SOME (BytesL (MAP n2w (source_const_hex_decode (DROP 2 s))))
     else NONE) /\
  source_const_value_literal (SCV_BytesType fixed n) = NONE /\
  source_const_value_literal (SCV_List vs) = NONE /\
  source_const_value_literal (SCV_Tuple vs) = NONE /\
  source_const_value_literal (SCV_Struct path fields) = NONE
End

(* The caller supplies the expected resolved runtime type, not an inferred
   source annotation. Both literal range and type well-formedness are checked:
   e.g. 0 at uint0 satisfies the range check but is not a valid runtime type. *)
Definition source_const_reify_def:
  source_const_reify tenv ty sv =
    case source_const_value_literal sv of
    | NONE => NONE
    | SOME lit =>
        if well_formed_type tenv ty /\ well_typed_literal ty lit then
          SOME (Literal ty lit)
        else NONE
End
