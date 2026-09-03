(*
 * Concrete EVM event encoding for the Vyper semantics.
 *
 * TOP-LEVEL:
 *   event_info       -- checked metadata needed to encode declared events
 *   encode_vyper_event -- encode a declared Vyper event as an EVM event
 *   encode_raw_event -- construct an EVM event for raw_log
 *)

Theory vyperEvent
Ancestors
  cv cv_std vyperABI vyperValue contractABI vfmTypes
  byte keccak
Libs
  cv_transLib

Type event_info = “:string -> (num # type list # bool list) option”

Definition is_event_bytestring_type_def:
  is_event_bytestring_type (BaseT (BytesT (Dynamic _))) = T ∧
  is_event_bytestring_type (BaseT (StringT _)) = T ∧
  is_event_bytestring_type _ = F
End

(* Primitive word encoding used for indexed, statically-sized arguments. *)
Definition event_value_to_word_def:
  event_value_to_word (BoolV b) = (if b then 1w else 0w : bytes32) ∧
  event_value_to_word (IntV n) = (i2w n : bytes32) ∧
  event_value_to_word (FlagV k) = (n2w k : bytes32) ∧
  event_value_to_word (DecimalV n) = (i2w n : bytes32) ∧
  event_value_to_word (BytesV bs) =
    (if LENGTH bs = 20 then word_of_bytes_be (PAD_LEFT 0w 32 bs)
     else word_of_bytes_be (PAD_RIGHT 0w 32 bs)) ∧
  event_value_to_word _ = 0w
End

Definition encode_event_topic_def:
  encode_event_topic T (BytesV bs) =
    SOME (word_of_bytes_be (Keccak_256_w64 bs)) ∧
  encode_event_topic T (StringV s) =
    SOME (word_of_bytes_be (Keccak_256_w64 (MAP (n2w o ORD) s))) ∧
  encode_event_topic T _ = NONE ∧
  encode_event_topic F v = SOME (event_value_to_word v)
End

Definition encode_indexed_event_topics_def:
  encode_indexed_event_topics [] [] [] = SOME ([] : bytes32 list) ∧
  encode_indexed_event_topics (T::fs) (ty::tys) (v::vs) =
    (case encode_event_topic (is_event_bytestring_type ty) v of
     | NONE => NONE
     | SOME topic =>
         OPTION_MAP (CONS topic) (encode_indexed_event_topics fs tys vs)) ∧
  encode_indexed_event_topics (F::fs) (_::tys) (_::vs) =
    encode_indexed_event_topics fs tys vs ∧
  encode_indexed_event_topics _ _ _ = NONE
End

Definition non_indexed_event_args_def:
  non_indexed_event_args [] [] [] = SOME ([] : (type # value) list) ∧
  non_indexed_event_args (T::fs) (_::tys) (_::vs) =
    non_indexed_event_args fs tys vs ∧
  non_indexed_event_args (F::fs) (ty::tys) (v::vs) =
    OPTION_MAP (CONS (ty,v)) (non_indexed_event_args fs tys vs) ∧
  non_indexed_event_args _ _ _ = NONE
End

Definition encode_vyper_event_def:
  encode_vyper_event event_info tenv (logger : address) event_name vals =
    case event_info event_name of
    | NONE => NONE
    | SOME (event_hash, arg_types, indexed_flags) =>
        case encode_indexed_event_topics indexed_flags arg_types vals of
        | NONE => NONE
        | SOME indexed_topics =>
            case non_indexed_event_args indexed_flags arg_types vals of
            | NONE => NONE
            | SOME typed_vals =>
                case vyper_to_abi_list tenv (MAP FST typed_vals)
                                            (MAP SND typed_vals) of
                | NONE => NONE
                | SOME abi_vals =>
                    SOME <| logger := logger;
                            topics := n2w event_hash :: indexed_topics;
                            data := enc (Tuple (vyper_to_abi_types tenv
                                                (MAP FST typed_vals)))
                                        (ListV abi_vals) |>
End

Definition encode_raw_event_def:
  encode_raw_event (logger : address) topics data : event =
    <| logger := logger; topics := topics; data := data |>
End
