(* Recursive memory-layout keys provide the punnability boundary. *)
Theory bodyMemTupleLayoutTransport
Ancestors
  context memoryLayoutSource memoryLayoutDefs exprSimLayoutTransport

Theorem layout_key_punnable[local]:
  (!ce src dst. memory_layout_key src = memory_layout_key dst ==>
     punnable ce src dst) /\
  (!ce ss ds. MAP memory_layout_key ss = MAP memory_layout_key ds ==>
     punnable_list ce ss ds)
Proof
  ho_match_mp_tac punnable_ind >>
  rpt conj_tac >> rpt gen_tac >>
  simp[punnable_def, memory_layout_key_array, memory_layout_key_tuple,
       memory_layout_key_array_cases, memory_layout_key_tuple_cases] >>
  rpt strip_tac >> metis_tac[memory_layout_key_bytes]
QED

Theorem tuple_layout_memory_transport:
  (!ty tv. evaluate_type tenv ty = SOME tv ==>
     type_memory_bytes ce ty = type_memory_size tv) /\
  tuple_memory_layout_eq dst src /\ arg_type_fits src dst /\
  evaluate_type tenv src = SOME sv /\ evaluate_type tenv dst = SOME dv ==>
  !v b mem. (val_in_memory sv v b mem <=> val_in_memory dv v b mem)
Proof
  strip_tac >>
  `memory_layout_key src = memory_layout_key dst` by
    (Cases_on `dst` >> Cases_on `src` >>
     gvs[tuple_memory_layout_eq_def, memory_layout_key_tuple]) >>
  drule (cj 1 layout_key_punnable) >> strip_tac >>
  drule (cj 1 compatible_layout_memory) >>
  metis_tac[]
QED
