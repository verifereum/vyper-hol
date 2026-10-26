(* Concrete checks of the ECAdd/ECMul point validation in vyperContext. *)
Theory vyperECPrecompileTest
Ancestors
  vyperContext vyperValue
Libs
  wordsLib intLib

(* Off-curve inputs fail in either add position, and even for scalar zero. *)
Theorem evaluate_ec_invalid_point_regression:
  evaluate_ecadd [mk_ec_result (1, 1); mk_ec_result (0, 0)] =
    INR (RuntimeError "ECAdd invalid point") /\
  evaluate_ecadd [mk_ec_result (0, 0); mk_ec_result (1, 1)] =
    INR (RuntimeError "ECAdd invalid point") /\
  evaluate_ecmul [mk_ec_result (1, 1); IntV 0] =
    INR (RuntimeError "ECMul invalid point") /\
  evaluate_ecmul [mk_ec_result (1, 1); IntV 1] =
    INR (RuntimeError "ECMul invalid point")
Proof
  EVAL_TAC
QED

(* Coordinates at the field modulus are invalid, even for scalar zero. *)
Theorem evaluate_ec_field_bound_regression:
  evaluate_ecadd
    [mk_ec_result (bn254$bn254p, 2); mk_ec_result (0, 0)] =
    INR (RuntimeError "ECAdd invalid point") /\
  evaluate_ecadd
    [mk_ec_result (0, 0); mk_ec_result (1, bn254$bn254p)] =
    INR (RuntimeError "ECAdd invalid point") /\
  evaluate_ecmul [mk_ec_result (bn254$bn254p, 2); IntV 0] =
    INR (RuntimeError "ECMul invalid point") /\
  evaluate_ecmul [mk_ec_result (1, bn254$bn254p); IntV 1] =
    INR (RuntimeError "ECMul invalid point")
Proof
  EVAL_TAC
QED

(* Infinity is valid; a genuine zero result must not become a failure. *)
Theorem evaluate_ec_valid_point_regression:
  evaluate_ecadd [mk_ec_result (0, 0); mk_ec_result (0, 0)] =
    INL (mk_ec_result (0, 0)) /\
  evaluate_ecadd [mk_ec_result (0, 0); mk_ec_result (1, 2)] =
    INL (mk_ec_result (1, 2)) /\
  evaluate_ecmul [mk_ec_result (0, 0); IntV 1] =
    INL (mk_ec_result (0, 0)) /\
  evaluate_ecmul [mk_ec_result (1, 2); IntV 0] =
    INL (mk_ec_result (0, 0)) /\
  evaluate_ecmul [mk_ec_result (1, 2); IntV 1] =
    INL (mk_ec_result (1, 2))
Proof
  EVAL_TAC
QED
