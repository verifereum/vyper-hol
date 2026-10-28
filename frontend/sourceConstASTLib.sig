signature sourceConstASTLib = sig
  include Abbrev

  (* Opt-in source syntax only: no inferred type, folded_value, declaration
     flags, source IDs or old/trusted decoder. Unknown/malformed syntax raises
     JSONDecode.JSONError. Decoding is not source typing or constant evaluation.
     Calls always remain SCE_Call; a later resolver owns builtin identity.
     Decimal exponent scaling is closed HOL arithmetic inside SCL_Decimal;
     consumers must evaluate it in HOL rather than destruct only ML numerals.
     Hex retains validated spelling; Bytes/HexBytes decode to octet lists. *)
  (* Shared strict operator decoding for the general source-syntax API. *)
  val unary_operator : term JSONDecode.decoder
  val binary_operator : term JSONDecode.decoder
  val boolean_operator : term JSONDecode.decoder
  val comparison_operator : term JSONDecode.decoder
  val expression : term JSONDecode.decoder
  val keyword : term JSONDecode.decoder
  val keywords : term JSONDecode.decoder
  val name_path : string list JSONDecode.decoder
  val annotation : term JSONDecode.decoder
  val annotation_bound : term JSONDecode.decoder

  (* Missing only => NONE. Present null/malformed is passed to d and fails
     unless d explicitly admits null. Duplicate keys fail, not first-wins. *)
  val optional_field : string -> 'a JSONDecode.decoder -> 'a option JSONDecode.decoder

  (* Optional source annotation: missing/null => NONE; malformed present
     annotations never become absence. Required annotations use annotation. *)
  val annotation_field : string -> term option JSONDecode.decoder
end
