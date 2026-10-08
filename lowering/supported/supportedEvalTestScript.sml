(* Generic closed selector regression, independent of the fixture inventory. *)
Theory supportedEvalTest
Ancestors contractABI selectorDispatch keccak
Libs supportedEvalLib cv_transLib

val () = supportedEvalLib.configure ();

Theorem closed_selector_length:
  LENGTH (function_selector "probe" [Uint 256; Bool]) = 4
Proof
  EVAL_TAC
QED

(* More than one rate block; the conversion uses the original total CV
   translation, not a short-signature-only implementation. *)
Theorem long_selector_length:
  LENGTH (function_selector (REPLICATE 140 #"x") [Uint 256]) = 4
Proof
  EVAL_TAC
QED

(* Independent upstream hash translation probe, without embedded hash bytes. *)
Theorem closed_hash_length:
  LENGTH (Keccak_256_w64 (MAP n2w [0;1;255])) = 32
Proof
  CONV_TAC cv_eval
QED

(* Exercise the converter's open-input branch without expanding a symbolic
   Keccak calculation. The fallback is the existing all-input compute fact. *)
Theorem symbolic_selector_fallback:
  function_selector name args = function_selector_eval name args
Proof
  CONV_TAC (LAND_CONV supportedEvalLib.function_selector_conv) >> REFL_TAC
QED
