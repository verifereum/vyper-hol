Theory concretizePtrKillSoundness
Ancestors
  concretizePtrKillIdentity concretizePtrAllocationSize concretizePtrKillProbe
  concretizePtrProtectedPrefix concretizePtrRevertHistory
  concretizeMemLocDefs concretizePtrBPOrigins ptrDiscipline o1PassContract
  venomWf cfgWf cfgAnalysisProps venomInst venomState venomExecSemantics
  memLocDefs codegenRel finite_map list

Theorem ptr_reachable_protected_byte_no_kill:
  frame_reachable vs ctx stk PG G tn fn inst s /\ o1_run_state_ok vs /\
  EVERY (fn_ptr_ok P) ctx.ctx_functions /\ EVERY ssa_form ctx.ctx_functions /\
  EVERY fn_inst_wf ctx.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) ctx.ctx_functions /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) ctx.ctx_functions /\
  wf_function fn /\ all_reachable fn /\
  ptr_bp_origins fn (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn) /\
  MEM inst (fn_insts fn) /\ ptr_discipline lo ctx vs /\
  o1_ctx_shape ctx /\ ~ctx_has_dalloca ctx /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ b <= byte /\ byte < b + sz /\
  step_inst fuel ctx inst s = OK s' /\ ~in_revert_forward fn s /\
  ~MEM (Allocation aid) (MAP FST imports) /\
  (!off len. MEM (off,len) (source_memory_write_ranges inst s) ==>
    ~(off <= byte /\ byte < off + len)) ==>
  ~ptr_ml_can_kill (Allocation aid)
    (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn)
    (\a. if context_alloca_size fn imports a = 0 then NONE
         else SOME (context_alloca_size fn imports a)) inst
Proof
  strip_tac >> strip_tac >>
  drule_all ptr_reachable_successful_kill_identity >> strip_tac >>
  `site = (b,sz)` by metis_tac[optionTheory.SOME_11] >> gvs[] >>
  `context_alloca_size fn imports (Allocation aid) = sz` by
    metis_tac[ptr_frame_context_allocation_size] >>
  `sz <> 0` by decide_tac >>
  `?vals. eval_operands inst.inst_operands s = SOME vals` by
    metis_tac[ptr_successful_kill_operands_ready] >>
  `access_ok lo G fn inst s` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  `eval_operand ops.iao_ofst s = SOME w` by simp[eval_operand_def] >>
  `(\a. if context_alloca_size fn imports a = 0 then NONE
        else SOME (context_alloca_size fn imports a)) (Allocation aid) = SOME sz` by simp[] >>
  qpat_x_assum `ptr_ml_can_kill _ _ _ _` mp_tac >>
  pure_rewrite_tac[IMP_CLAUSES] >>
  irule ptr_protected_byte_no_kill >>
  qexistsl [`G`, `b`, `byte`, `w`, `fn`, `lo`, `ops`, `s`, `sz`, `v`, `vals`] >>
  simp[arithmeticTheory.ADD_COMM]
QED

(* For chronological ordinary observations, ptr_chrono_ordinary_non_revert
   supplies the guard from an endpoint outside revert-forward with opcode
   different from ASSIGN. Success alone does not supply this guard.
   Imports must still exclude the local key; projected owner-path coverage
   and descendant writes remain separate integration obligations. *)
