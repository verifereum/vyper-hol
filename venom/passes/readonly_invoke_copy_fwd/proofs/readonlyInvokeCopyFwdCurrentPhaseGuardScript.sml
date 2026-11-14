(* A current-owner phase protects both endpoints from the actual copy's
   write footprint, independently of the new event's transformation log. *)
Theory readonlyInvokeCopyFwdCurrentPhaseGuard
Ancestors
  readonlyInvokeCopyFwdHistoryPhase readonlyInvokeCopyFwdHistoryVisitAccess
  o1LowerDloadOccurrence occurrenceGeometry ptrDiscipline codegenRel
  venomInst venomState finite_map list words

Theorem ricf_phase_entry_current_copy_exclusion:
  ricf_phase_entry vs C ctxP logP stk PG G tn fn s a U B (p,[]) /\
  active_inst fn inst s /\
  inst.inst_opcode = MCOPY /\
  inst.inst_operands = [Var dst;Var sv;Lit z] /\
  eval_operands inst.inst_operands s = SOME [n2w db;n2w sb;z] /\
  db < dimword(:256) /\
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  occurrence_syntax_origin fn a H /\
  occurrence_natural_geometry lo a U B stk s /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ~ctx_has_dalloca C /\
  wf_function fn /\ ssa_form fn /\ fn_inst_wf fn /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn ==>
  !k. k < p.rpe_size ==>
    ~(db <= p.rpe_db+k /\ p.rpe_db+k < db+w2n z) /\
    ~(db <= p.rpe_sb+k /\ p.rpe_sb+k < db+w2n z)
Proof
  strip_tac >>
  fs[ricf_phase_entry_def] >>
  `fn = p.rpe_fn` by metis_tac[ricf_history_cursor_owner_function] >>
  `occurrence_annotation_ok n p.rpe_owner U B HP H stk PG G s` by
    metis_tac[occ_frame_reachable_annotation] >>
  `source_memory_write_ranges inst s = [(db,w2n z)]` by
    (gvs[source_memory_write_ranges_def, sized_source_write_range_def,
         eval_operands_def, AllCaseEqs(), w2n_n2w]) >>
  gvs[] >>
  metis_tac[ricf_history_cursor_owner_write_ranges, MEM, arithmeticTheory.ADD_SYM]
QED
