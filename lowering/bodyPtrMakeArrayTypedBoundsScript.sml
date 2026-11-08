(* Typed-copy windows are selected in each layout independently.  In
   particular the source types below are the lowered call's types, not the
   widened destination types.  Empty children need no memory access: the
   non-strict endpoint bounds deliberately allow offset = total. *)
Theory bodyPtrMakeArrayTypedBounds
Ancestors
  typedCopyLayoutPtr structChildPtr tupleTypedLoad ptrCoverage
  compileEnv valueEncoding tupleMemoryLayout loweringPosts list rich_list arithmetic

Theorem typed_tuple_child_window:
  LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) tys tvs /\
  i < LENGTH tys ==>
  SUM (MAP (type_memory_bytes cenv) (TAKE i tys)) +
    type_memory_bytes cenv (EL i tys) <= SUM (MAP type_memory_size tvs)
Proof
  rpt strip_tac >>
  `LENGTH tys = LENGTH tvs` by metis_tac[LIST_REL_LENGTH] >>
  qpat_assum `LIST_REL _ tys tvs` mp_tac >>
  rewrite_tac[LIST_REL_EL_EQN] >> strip_tac >>
  drule tuple_prefix_sizes >> disch_then (qspec_then `i` assume_tac) >>
  gvs[] >> irule tuple_element_interval >> simp[]
QED

Theorem typed_tuple_source_read_window:
  LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) tys tvs /\
  values_have_types tvs vs /\ i < LENGTH tys ==>
  SUM (MAP (type_memory_bytes cenv) (TAKE i tys)) +
    val_footprint (EL i tvs) (EL i vs) <= SUM (MAP type_memory_size tvs)
Proof
  rpt strip_tac >>
  `LENGTH tys = LENGTH tvs` by metis_tac[LIST_REL_LENGTH] >>
  drule tuple_prefix_sizes >> disch_then (qspec_then `i` assume_tac) >>
  gvs[] >> irule tuple_child_footprint_contained >> simp[]
QED

Theorem typed_tuple_robust_source_child:
  LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) tys tvs /\
  LENGTH vs = LENGTH tvs /\ i < LENGTH tys /\
  (!m. mem_agree_outside tn.t_mem mem m ==> tuple_in_memory vs tvs addr m) ==>
  !m. mem_agree_outside tn.t_mem mem m ==>
    val_in_memory (EL i tvs) (EL i vs)
      (addr + SUM (MAP (type_memory_bytes cenv) (TAKE i tys))) m
Proof
  rpt strip_tac >>
  `LENGTH tys = LENGTH tvs` by metis_tac[LIST_REL_LENGTH] >>
  drule tuple_prefix_sizes >> disch_then (qspec_then `i` assume_tac) >>
  gvs[] >> irule tuple_in_memory_robust_element >> simp[] >> metis_tac[]
QED

(* prefix is zero for a fixed array and 32 for a dynamic array.  Apply
   this separately with the source stride and the destination stride;
   neither stride nor capacity is required to coincide. *)
Theorem typed_array_child_window:
  !i len n stride prefix:num.
  (i:num) < len /\ n <= stride ==>
  prefix + i * stride + n <= prefix + len * stride
Proof
  rpt strip_tac >>
  `SUC i * stride <= len * stride` by
    (irule LESS_MONO_MULT >> decide_tac) >>
  qpat_x_assum `SUC i * stride <= _` mp_tac >>
  simp_tac bool_ss [MULT_CLAUSES] >> decide_tac
QED

Theorem typed_array_child_access_window:
  !i len n stride prefix:num.
  (i:num) < len /\ 0 < n /\ n <= stride ==>
  prefix + i * stride < prefix + len * stride /\
  prefix + i * stride + n <= prefix + len * stride
Proof
  rpt gen_tac >> strip_tac >>
  `prefix + i * stride + n <= prefix + len * stride` suffices_by decide_tac >>
  irule typed_array_child_window >> simp[]
QED

Theorem typed_array_terminal_window:
  !i len stride prefix:num.
  (i:num) <= len ==>
  prefix + i * stride <= prefix + len * stride
Proof
  rpt strip_tac >> simp[] >> irule LESS_MONO_MULT >> simp[]
QED
