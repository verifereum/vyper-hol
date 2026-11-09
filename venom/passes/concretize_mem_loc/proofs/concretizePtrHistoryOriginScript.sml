Theory concretizePtrHistoryOrigin
Ancestors concretizePtrHistoryObservation concretizePtrWriteByteOrigin
  ptrDiscipline concretizeMemLocDefs pointerConfinedDefs venomWf venomInst
  frameExecutionHistory list pred_set finite_map words

Theorem ptr_history_write_origin:
  ptr_history_realized vs0 ctx fn PG h /\ MEM (j,t) h /\
  ptr_discipline lo ctx vs0 /\ MEM fn ctx.ctx_functions /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) ctx.ctx_functions /\
  wf_function fn /\ all_reachable fn /\ ssa_form fn /\
  EVERY inst_wf (fn_insts fn) /\ MEM j (fn_insts fn) /\
  ~in_revert_forward fn t /\ lo <= x /\
  x IN range_bytes (source_memory_write_ranges j t) ==>
  ?G v b sz. inst_write_op j = SOME (Var v) /\
    FLOOKUP G v = SOME (b,sz) /\ b <= x /\ x < b + sz /\
    ((?aid. FLOOKUP t.vs_allocas aid = SOME (b,sz) /\
       ml_used_gen (Allocation aid)
         (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn) mems j) \/
     (?i idx r. MEM i (fn_insts fn) /\ i.inst_opcode = PARAM /\
       i.inst_operands = [Lit idx] /\ MEM r i.inst_outputs /\
       w2n idx < LENGTH PG /\ EL (w2n idx) PG = SOME (b,sz) /\
       v IN pointer_derived_vars fn {r}))
Proof
  strip_tac >>
  `?stk0 G0 tn0. frame_reachable vs0 ctx stk0 PG G0 tn0 fn j t` by
    metis_tac[ptr_history_realized_def] >>
  qpat_x_assum `ptr_discipline _ _ _` mp_tac >>
  simp[ptr_discipline_def] >> strip_tac >>
  `fn_ptr_ok P fn` by fs[EVERY_MEM] >>
  `access_ok lo G0 fn j t` by metis_tac[] >>
  qexists `G0` >> irule ptr_frame_write_byte_origin >> simp[] >> metis_tac[]
QED

Theorem ptr_history_current_write_origin:
  frame_history vs0 ctx stk PG G tn fn inst s hs h /\ MEM (j,t) h /\
  ptr_discipline lo ctx vs0 /\ MEM fn ctx.ctx_functions /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) ctx.ctx_functions /\
  wf_function fn /\ all_reachable fn /\ ssa_form fn /\
  EVERY inst_wf (fn_insts fn) /\ MEM j (fn_insts fn) /\
  ~in_revert_forward fn t /\ lo <= x /\
  x IN range_bytes (source_memory_write_ranges j t) ==>
  ?G0 v b sz. inst_write_op j = SOME (Var v) /\
    FLOOKUP G0 v = SOME (b,sz) /\ b <= x /\ x < b + sz /\
    ((?aid. FLOOKUP t.vs_allocas aid = SOME (b,sz) /\
       ml_used_gen (Allocation aid)
         (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn) mems j) \/
     (?i idx r. MEM i (fn_insts fn) /\ i.inst_opcode = PARAM /\
       i.inst_operands = [Lit idx] /\ MEM r i.inst_outputs /\
       w2n idx < LENGTH PG /\ EL (w2n idx) PG = SOME (b,sz) /\
       v IN pointer_derived_vars fn {r}))
Proof
  strip_tac >> irule ptr_history_write_origin >> simp[] >>
  metis_tac[ptr_history_realized_invariant]
QED

Theorem ptr_history_saved_write_origin:
  frame_history vs0 ctx stk PG G tn fn inst s hs h /\ n < LENGTH stk /\
  MEM (j,t) (EL n hs) /\ ptr_discipline lo ctx vs0 /\
  MEM (EL n stk).cf_fn ctx.ctx_functions /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) ctx.ctx_functions /\
  wf_function (EL n stk).cf_fn /\ all_reachable (EL n stk).cf_fn /\
  ssa_form (EL n stk).cf_fn /\ EVERY inst_wf (fn_insts (EL n stk).cf_fn) /\
  MEM j (fn_insts (EL n stk).cf_fn) /\
  ~in_revert_forward (EL n stk).cf_fn t /\ lo <= x /\
  x IN range_bytes (source_memory_write_ranges j t) ==>
  ?G0 v b sz. inst_write_op j = SOME (Var v) /\
    FLOOKUP G0 v = SOME (b,sz) /\ b <= x /\ x < b + sz /\
    ((?aid. FLOOKUP t.vs_allocas aid = SOME (b,sz) /\
       ml_used_gen (Allocation aid)
         (bp_analyze_fuel (concretize_memloc_fuel (EL n stk).cf_fn)
           (cfg_analyze (EL n stk).cf_fn) (EL n stk).cf_fn) mems j) \/
     (?i idx r. MEM i (fn_insts (EL n stk).cf_fn) /\ i.inst_opcode = PARAM /\
       i.inst_operands = [Lit idx] /\ MEM r i.inst_outputs /\
       w2n idx < LENGTH (EL n stk).cf_params /\
       EL (w2n idx) (EL n stk).cf_params = SOME (b,sz) /\
       v IN pointer_derived_vars (EL n stk).cf_fn {r}))
Proof
  strip_tac >>
  `ptr_history_realized vs0 ctx (EL n stk).cf_fn (EL n stk).cf_params (EL n hs)` by
    (drule ptr_history_realized_invariant >> simp[LIST_REL_EL_EQN]) >>
  irule ptr_history_write_origin >> simp[] >> metis_tac[]
QED

Theorem ptr_history_observation_allocas_from:
  ptr_history_realized vs0 ctx fn PG h /\ MEM (j,t) h /\
  ptr_discipline lo ctx vs0 ==> allocas_from lo t
Proof
  simp[ptr_history_realized_def, ptr_discipline_def] >> metis_tac[]
QED

(* Classification is conditional on a non-revert observation, structural
   function facts, and an above-lo byte. Realization recovers PG exactly,
   but does not restore popped completed callee histories. This result does
   not identify a local allocation with a separately chosen fresh site by
   numeric overlap, nor link an imported PARAM to a caller argument. *)
