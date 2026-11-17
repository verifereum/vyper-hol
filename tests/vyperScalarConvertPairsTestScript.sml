(* Scalar convert pairs where valid_conversion once disagreed with the pinned
   Vyper (_convert_rules.py): signed int -> address is rejected, and the
   decimal/address -> bool, bool -> decimal and bool/decimal -> bytesM pairs are
   accepted. Expected results are independent literals. *)
Theory vyperScalarConvertPairsTest
Ancestors
  list vyperAST vyperValue vyperValueOperation vyperContext vyperTypeSystem
Libs
  wordsLib

Theorem scalar_pairs_accepted:
  valid_conversion (BaseT DecimalT) (BaseT BoolT) /\
  valid_conversion (BaseT AddressT) (BaseT BoolT) /\
  valid_conversion (BaseT BoolT) (BaseT DecimalT) /\
  valid_conversion (BaseT BoolT) (BaseT (BytesT (Fixed 1))) /\
  valid_conversion (BaseT BoolT) (BaseT (BytesT (Fixed 32))) /\
  valid_conversion (BaseT DecimalT) (BaseT (BytesT (Fixed 21))) /\
  valid_conversion (BaseT DecimalT) (BaseT (BytesT (Fixed 32))) /\
  valid_conversion (BaseT (UintT 160)) (BaseT AddressT)
Proof
  EVAL_TAC
QED

Theorem scalar_pairs_rejected:
  ~valid_conversion (BaseT (IntT 8)) (BaseT AddressT) /\
  ~valid_conversion (BaseT (IntT 160)) (BaseT AddressT) /\
  ~valid_conversion (BaseT (IntT 256)) (BaseT AddressT) /\
  ~valid_conversion (BaseT BoolT) (BaseT (BytesT (Fixed 0))) /\
  ~valid_conversion (BaseT DecimalT) (BaseT (BytesT (Fixed 20)))
Proof
  EVAL_TAC
QED

(* The new evaluate_convert clauses. A decimal is a signed 168-bit integer
   scaled by 10^10; bytesM keeps the low M bytes of its sign-extended word. *)
Theorem scalar_pairs_values:
  evaluate_convert FEMPTY (BoolV T) (BaseT DecimalT) =
    INL (DecimalV 10000000000) /\
  evaluate_convert FEMPTY (BoolV F) (BaseT DecimalT) = INL (DecimalV 0) /\
  evaluate_convert FEMPTY (DecimalV 0) (BaseT BoolT) = INL (BoolV F) /\
  evaluate_convert FEMPTY (DecimalV 1) (BaseT BoolT) = INL (BoolV T) /\
  evaluate_convert FEMPTY (DecimalV (-1)) (BaseT BoolT) = INL (BoolV T) /\
  evaluate_convert_from FEMPTY (BaseT AddressT) (BytesV (REPLICATE 20 0w))
    (BaseT BoolT) = INL (BoolV F) /\
  evaluate_convert_from FEMPTY (BaseT AddressT) (BytesV (REPLICATE 19 0w ++ [1w]))
    (BaseT BoolT) = INL (BoolV T) /\
  evaluate_convert FEMPTY (BoolV T) (BaseT (BytesT (Fixed 4))) =
    INL (BytesV [0w; 0w; 0w; 1w]) /\
  evaluate_convert FEMPTY (BoolV F) (BaseT (BytesT (Fixed 1))) =
    INL (BytesV [0w]) /\
  evaluate_convert FEMPTY (DecimalV 258) (BaseT (BytesT (Fixed 21))) =
    INL (BytesV (REPLICATE 19 0w ++ [1w; 2w])) /\
  evaluate_convert FEMPTY (DecimalV (-1)) (BaseT (BytesT (Fixed 21))) =
    INL (BytesV (REPLICATE 21 255w))
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC
QED
