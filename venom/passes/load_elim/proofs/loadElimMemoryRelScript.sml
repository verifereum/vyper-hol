Theory loadElimMemoryRel
Ancestors
  venomState stateFrame pred_set list rich_list

Definition padded_exec_equiv_def:
  padded_exec_equiv vars s1 s2 <=>
    (!v. v NOTIN vars ==> lookup_var v s1 = lookup_var v s2) /\
    (!i. read_memory i 1 s1 = read_memory i 1 s2) /\
    execution_frame (s1 with vs_memory := []) =
    execution_frame (s2 with vs_memory := [])
End

Theorem padded_exec_equiv_refl:
  !vars s. padded_exec_equiv vars s s
Proof
  simp[padded_exec_equiv_def]
QED

Theorem padded_exec_equiv_trans:
  !vars s1 s2 s3.
    padded_exec_equiv vars s1 s2 /\ padded_exec_equiv vars s2 s3 ==>
    padded_exec_equiv vars s1 s3
Proof
  rw[padded_exec_equiv_def] >> metis_tac[]
QED

Theorem padded_exec_equiv_sym:
  !vars s1 s2. padded_exec_equiv vars s1 s2 ==>
    padded_exec_equiv vars s2 s1
Proof
  rw[padded_exec_equiv_def] >> metis_tac[]
QED

Theorem read_memory_length:
  !n i s. LENGTH (read_memory i n s) = n
Proof
  simp[read_memory_def, LENGTH_TAKE_EQ]
QED

Theorem read_memory_byte:
  !n i s j. j < n ==>
    EL j (read_memory i n s) =
    if i + j < LENGTH s.vs_memory then EL (i + j) s.vs_memory else 0w
Proof
  rpt strip_tac >> simp[read_memory_def, EL_TAKE, EL_APPEND_EQN,
    LENGTH_DROP, EL_DROP, EL_REPLICATE] >>
  Cases_on `i + j < LENGTH s.vs_memory` >> gvs[]
QED

Theorem read_memory_range_ext:
  !s1 s2. (!i. read_memory i 1 s1 = read_memory i 1 s2) ==>
    !i n. read_memory i n s1 = read_memory i n s2
Proof
  rpt strip_tac >> irule LIST_EQ >> simp[read_memory_length] >>
  qx_gen_tac `j` >> strip_tac >>
  first_x_assum (qspec_then `i + j` mp_tac) >>
  disch_then (mp_tac o Q.AP_TERM `EL 0`) >>
  simp[read_memory_byte]
QED

Theorem padded_exec_equiv_mload:
  !vars s1 s2 i. padded_exec_equiv vars s1 s2 ==>
    mload i s1 = mload i s2
Proof
  rpt strip_tac >>
  `read_memory i 32 s1 = read_memory i 32 s2` by
    (irule read_memory_range_ext >> gvs[padded_exec_equiv_def]) >>
  gvs[mload_def, read_memory_def]
QED

