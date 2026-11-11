(* Interface probes for the local branch of captured operand posts. *)
Theory exprExtRequestLocalProbe
Ancestors
  loweringPosts valueEncoding valueEncodingDefs

(* An empty outer array constrains its root length, not the length of
   the first capacity slot, even when that slot is itself a dynamic array. *)
Theorem extrequest_empty_nested_local_memory:
  val_in_memory
    (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)) (Dynamic 1))
    (ArrayV (DynArrayV [])) b mem <=>
  mem_word_at b mem = 0w
Proof
  simp[val_in_memory_def]
QED

(* In contrast, type paths still reach that unused capacity slot. *)
Theorem extrequest_nested_capacity_path:
  mem_path_offset
    (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)) (Dynamic 1))
    [ValueSubscript (IntV 0)] =
  SOME (32, ArrayTV (BaseTV (UintT 256)) (Dynamic 1))
Proof
  simp[mem_path_offset_def, mem_step_offset_def]
QED
