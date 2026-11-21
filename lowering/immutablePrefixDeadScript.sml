Theory immutablePrefixDead
Ancestors
  immutableRepSensitivity robustCopyTransportPtr exprSimProps
  valueEncodingProofs valueEncodingProps valueTypingMemoryProps
  bodyPtrDefs immSectionDead vyperValue list

Theorem immutable_section_byte_window:
  off + n <= lo ==>
  mem_bytes_at off n (mem_bytes_at 0 lo mem) = mem_bytes_at off n mem
Proof
  strip_tac >>
  qspecl_then [`0`,`off`,`n`,`lo`,`mem`] mp_tac
    abiCanonicalHeadSizeTheory.mem_bytes_at_window >>
  simp[GSYM valueEncodingDefsTheory.mem_bytes_at_bounded,
       valueEncodingProofsTheory.LENGTH_mem_bytes_at_proof]
QED

Theorem immutable_prefix_interior_dead:
  off + type_memory_size tv <= lo /\ well_formed_type_value tv /\
  value_has_type tv v /\
  (!m. mem_agree_outside dirty mem m ==> val_in_memory tv v off m) /\
  off <= i /\ i < off + type_memory_size tv /\ i IN dirty ==>
  mem_dead_bytes (mem_bytes_at 0 lo mem) off tv i
Proof
  strip_tac >>
  `mem_bytes_at off (type_memory_size tv) (mem_bytes_at 0 lo mem) =
   mem_bytes_at off (type_memory_size tv) mem` by
    (irule immutable_section_byte_window >> simp[]) >>
  `val_wf tv v` by metis_tac[value_has_type_memory_wf] >>
  `!m. mem_agree_outside dirty (mem_bytes_at 0 lo mem) m ==>
       val_in_memory tv v off m` by
    (rpt strip_tac >> irule robust_val_in_memory_copy_transport >>
     simp[] >> qexistsl_tac
       [`mem`,`mem_bytes_at 0 lo mem`,`type_memory_size tv`,`off`,`dirty`,`dirty`] >>
     simp[exprSimPropsTheory.val_footprint_le]) >>
  `!j. j < type_memory_size tv /\ off+j IN dirty ==>
       mem_dead_bytes (mem_bytes_at 0 lo mem) off tv (off+j)` by
    (mp_tac (Q.SPECL [`tv`,`v`,`off`,`mem_bytes_at 0 lo mem`,`dirty`]
       body_assign_immutable_rep_sensitivity) >> simp[]) >>
  `i - off < type_memory_size tv /\ off + (i - off) = i` by decide_tac >>
  first_x_assum (qspec_then `i - off` mp_tac) >> simp[]
QED
