(*
 * Base Pointer Types
 *
 * Shared pointer representation for memory analyses.
 *)

Theory basePtrTypes
Ancestors
  list
  memoryLocation

Datatype:
  ptr = <|
    ptr_alloca : allocation;
    ptr_offset : num option
  |>
End

Definition ptr_offset_by_def:
  ptr_offset_by p off =
    case (p.ptr_offset, off) of
      (SOME a, SOME b) => p with ptr_offset := SOME (a + b)
    | _ => p with ptr_offset := NONE
End

Definition ptr_from_alloca_def:
  ptr_from_alloca alloc = <| ptr_alloca := alloc; ptr_offset := SOME 0 |>
End

val _ = export_theory();
