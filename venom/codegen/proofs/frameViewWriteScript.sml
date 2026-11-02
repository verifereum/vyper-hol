Theory frameViewWrite
Ancestors
  frameViewFacts frameViewMemory frameRel venomState venomMemProps
  venomExecSemantics contextCodegenRel codegenRel list

Theorem expanded_write_frame_view:
  write_memory_with_expansion off bytes (frame_view fn ra s with vs_memory := m) =
  frame_view fn ra (write_memory_with_expansion off bytes s) with
    vs_memory := (write_memory_with_expansion off bytes
                    (s with vs_memory := m)).vs_memory
Proof
  simp[write_memory_with_expansion_def, frame_view_def]
QED

Theorem mstore_frame_view:
  mstore off v (frame_view fn ra s with vs_memory := m) =
  frame_view fn ra (mstore off v s) with
    vs_memory := (mstore off v (s with vs_memory := m)).vs_memory
Proof
  simp[mstore_eq_write_mem, expanded_write_frame_view]
QED

Theorem mstore8_frame_view:
  mstore8 off v (frame_view fn ra s with vs_memory := m) =
  frame_view fn ra (mstore8 off v s) with
    vs_memory := (mstore8 off v (s with vs_memory := m)).vs_memory
Proof
  simp[mstore8_def, frame_view_def]
QED
