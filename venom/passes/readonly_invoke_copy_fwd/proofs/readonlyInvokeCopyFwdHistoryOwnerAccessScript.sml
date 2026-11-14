(* Byte consequences for direct accesses of the original owner.  Calls and
   revert-forward execution have separate boundaries, not ordinary writes. *)
Theory readonlyInvokeCopyFwdHistoryOwnerAccess
Ancestors
  readonlyInvokeCopyFwdHistorySource readonlyInvokeCopyFwdHistoryAnalysis
  occurrenceAccess occurrenceGeometry o1LowerDloadOccurrence
  ptrDiscipline finite_map list

Theorem ricf_located_event_source_write_range_exclusion:
  ricf_located_event ctx0 fn log round b es prefix e current /\
  ssa_form fn /\ ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_src_alloca fn /\
  (ricf_event_copy e (EL b fn.fn_blocks)).inst_operands = [Var dst;Var sv;sz] /\
  dfg_get_def (dfg_build_function fn)
    (icf_assign_root (dfg_build_function fn) {} dst) = SOME di /\
  icf_is_alloca di /\
  MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\ ai.inst_outputs = [sv] /\
  fn_inst_ids_distinct fn /\ occurrence_syntax_origin fn a H /\
  occurrence_annotation_ok n a U B HP H stk PG G s /\
  occurrence_natural_geometry lo a U B stk s /\
  FLOOKUP B (a,ai.inst_id) = SOME (sb,z) /\ 0 < z /\
  e.rfe_index <= j /\ j < LENGTH (EL b fn.fn_blocks).bb_instructions /\
  access_ok lo G fn (EL j (EL b fn.fn_blocks).bb_instructions) s /\
  ~in_revert_forward fn s ==>
  !off len k.
    MEM (off,len) (source_memory_write_ranges
      (EL j (EL b fn.fn_blocks).bb_instructions) s) /\ k < z ==>
    ~(off <= sb+k /\ sb+k < off+len)
Proof
  strip_tac >>
  `occurrence_env_ok B (a::MAP (\u. u.of_owner) U) H G` by
    gvs[occurrence_annotation_ok_def] >>
  `!ops. mem_write_ops (EL j (EL b fn.fn_blocks).bb_instructions) = SOME ops ==>
     op_prov G ops.iao_ofst <> SOME (sb,z)` by
    metis_tac[ricf_located_event_source_write_exclusion] >>
  metis_tac[occurrence_access_write_exclusion]
QED

(* The stage discipline supplies access_ok at the actual source state.
   In revert-forward mode it supplies no ordinary byte bound. *)
Theorem ricf_located_event_reachable_source_write_exclusion:
  ricf_located_event ctx0 fn log round b es prefix e current /\
  ssa_form fn /\ ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_src_alloca fn /\
  (ricf_event_copy e (EL b fn.fn_blocks)).inst_operands = [Var dst;Var sv;sz] /\
  dfg_get_def (dfg_build_function fn)
    (icf_assign_root (dfg_build_function fn) {} dst) = SOME di /\
  icf_is_alloca di /\
  MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\ ai.inst_outputs = [sv] /\
  fn_inst_ids_distinct fn /\ occurrence_syntax_origin fn a H /\
  occurrence_annotation_ok n a U B HP H stk PG G s /\
  occurrence_natural_geometry lo a U B stk s /\
  FLOOKUP B (a,ai.inst_id) = SOME (sb,z) /\ 0 < z /\
  e.rfe_index <= j /\ j < LENGTH (EL b fn.fn_blocks).bb_instructions /\
  ptr_discipline lo C vs /\
  frame_reachable vs C stk PG G tn fn
    (EL j (EL b fn.fn_blocks).bb_instructions) s ==>
  in_revert_forward fn s \/
  (!off len k.
    MEM (off,len) (source_memory_write_ranges
      (EL j (EL b fn.fn_blocks).bb_instructions) s) /\ k < z ==>
    ~(off <= sb+k /\ sb+k < off+len))
Proof
  strip_tac >> Cases_on `in_revert_forward fn s` >> simp[] >>
  `access_ok lo G fn (EL j (EL b fn.fn_blocks).bb_instructions) s` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  metis_tac[ricf_located_event_source_write_range_exclusion, arithmeticTheory.ADD_SYM]
QED

(* The owner call boundary is the imported, exported theorem
   ricf_located_event_no_intervening_source_invoke.  Reuse it directly:
   its static ml_size <> SOME 0 premise is essential and is not replaced
   here by runtime positivity.  No duplicate interval theorem is needed. *)
