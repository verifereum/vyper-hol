(*
 * Compiler Utility Functions
 *
 * Numeric helpers used by optimization passes.
 *)

Theory compilerUtils
Ancestors
  list words logroot
  vfmTypes

Definition pow2_def:
  pow2 n = (2:num) ** n
End

Definition wrap256_int_def:
  wrap256_int (val:int) =
    int_of_num (w2n (i2w val : bytes32))
End

Definition int_bounds_def:
  int_bounds signed bits =
    if signed then
      (-(int_of_num (pow2 (bits - 1))),
       int_of_num (pow2 (bits - 1)) - 1)
    else
      (0, int_of_num (pow2 bits) - 1)
End

Definition is_power_of_two_def:
  is_power_of_two (n:num) <=>
    n <> 0 /\ pow2 (LOG2 n) = n
End

Definition int_log2_def:
  int_log2 (n:num) = LOG2 n
End

Definition size_limits_max_uint256_def:
  size_limits_max_uint256 = int_of_num (pow2 256 - 1)
End

Definition size_limits_max_int256_def:
  size_limits_max_int256 = int_of_num (pow2 255 - 1)
End

Definition size_limits_min_int256_def:
  size_limits_min_int256 = - (int_of_num (pow2 255))
End

val _ = export_theory();
