(*
 * S3: the pointer discipline and taint bound of the lowered runtime unit,
 * from a pointer-safe run of its entry.
 *
 * The run's pointer safety comes from the selected source run on finite
 * storage horizons: the exit arm of sourceUnitExecution's
 * source_unit_execution_correct_at gives it at every valid horizon H with
 * D = cx_dead H cx.  lower_vyper_runtime_unit_ptr_taint turns it into
 * o1PassContract's source invariant parts through ptrSafeRun's
 * ptr_safe_ptr_discipline; the unit's distinct labels and pointer
 * confinement are lowering_context_ok's.
 *
 * TOP-LEVEL:
 *   lower_vyper_runtime_unit_ptr_taint -- the pointer discipline and taint
 *     bound, at any dead set D the entry's run is pointer-safe for
 *)
Theory loweringPtrCorrect
Ancestors
  vyperCompiler vyperLoweringCorrect ptrSafeRun

Theorem lower_vyper_runtime_unit_ptr_taint:
  !tops rpolicy unit vs fn lbl D.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    ~ctx_has_dalloca unit.cu_context /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl /\
    (!fuel. ptr_safe_blocks D 0 fuel unit.cu_context fn [] FEMPTY entry_taint
       (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                   vs_inst_idx := 0 |>))
    ==> ptr_discipline 0 unit.cu_context vs /\
        taint_within D unit.cu_context vs
Proof
  rpt strip_tac >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
  drule lowering_context_ok_bridge >> strip_tac >>
  `EVERY (\f. ALL_DISTINCT (fn_labels f)) unit.cu_context.ctx_functions` by
    fs[listTheory.EVERY_MEM] >>
  drule_all lower_vyper_runtime_unit_fn_ptr_ok >> strip_tac >>
  `0 <= vs.vs_alloca_next` by simp[] >>
  drule_all ptr_safe_ptr_discipline >> simp[]
QED
