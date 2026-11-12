Theory frameRelocationObservations
Ancestors ptrDiscipline venomState venomExecSemantics

(* dead_result_rel at Halt reads accounts, transient storage, immutables,
   return data, halted, logs, pending deletions and requests, but not memory.
   write_memory_with_expansion and mstore change only vs_memory. In particular
   expansion does not charge GAS: exec_gas consumes vs_gas_readings, a separate
   field, only when executing GAS. Restoring memory is a projection retaining
   all control fields (prev/current bb, inst index, labels), gas readings and
   every observed field. Unlike exact state equality, the relational boundary
   below allows differences in dead storage, transient and immutable bytes.
   Existing mem2varBlockSimHelpers.mstore_preserves lists individual fields;
   the whole-record projection here covers also gas readings and requests. *)

Theorem dead_result_rel_memory_frame:
  dead_result_rel D (Halt (s with vs_memory := ms))
    (Halt (t with vs_memory := mt)) <=> dead_result_rel D (Halt s) (Halt t)
Proof
  simp[dead_result_rel_def]
QED

Theorem mstore_memory_frame:
  (mstore off value s with vs_memory := s.vs_memory) = s
Proof
  simp[mstore_def]
QED

Theorem dead_result_rel_mstore:
  dead_result_rel D (Halt (mstore off value s))
    (Halt (mstore offT valueT t)) <=> dead_result_rel D (Halt s) (Halt t)
Proof
  simp[mstore_def, dead_result_rel_memory_frame]
QED

val _ = if List.all (null o hyp)
  [dead_result_rel_memory_frame, mstore_memory_frame, dead_result_rel_mstore]
  then () else raise Fail "memory observations export has hypotheses";
