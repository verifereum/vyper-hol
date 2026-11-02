(* Compatibility export: checked element strides and physical bounds are
   shared by fixed-array and dynamic-array loops. *)
Theory typedDynLoopSafety
Ancestors
  typedArrayLoopSafety

Theorem checked_dynarray_copy_element_safety = typedArrayLoopSafetyTheory.checked_array_copy_element_safety;
