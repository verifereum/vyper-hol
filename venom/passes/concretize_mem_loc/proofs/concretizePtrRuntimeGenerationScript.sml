Theory concretizePtrRuntimeGeneration
Ancestors
  concretizePtrHistoryCfg concretizePtrHistoryUsed concretizePtrProductionCoverage
  concretizeAnalysisWriteSafety concretizeAnalysisScanCoverage
  concretizeAnalysisLivenessTransfer concretizeAnalysisBoundary
  concretizeMemLocDefs concretizePtrBPOrigins pointerConfinedDefs ptrDiscipline
  basePtrDefs memLocDefs venomWf venomInst list pred_set
  concretizePtrSingletonOriginProbe

Theorem ptr_write_op_operand:
  inst_write_op inst = SOME op ==> MEM op inst.inst_operands
Proof
  simp[inst_write_op_def, mem_write_ops_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[MEM_REVERSE, MEM]
QED

Theorem ptr_production_operand_gen:
  fn_ptr_ok P fn /\ ssa_form fn /\ EVERY inst_wf (fn_insts fn) /\
  (!i. MEM i (fn_insts fn) ==> MEM i (bp_scan_insts fn cfg.cfg_dfs_pre)) /\
  MEM inst (fn_insts fn) /\ MEM (Var v) inst.inst_operands /\
  v IN pointer_derived_vars fn (ptr_bp_alloc_roots fn aid) ==>
  ml_operand_gen (Allocation aid)
    (bp_analyze_fuel (concretize_memloc_fuel fn) cfg fn) inst
Proof
  strip_tac >> drule_all ptr_bp_production_coverage >> strip_tac >>
  `MEM (Allocation aid)
     (find_base_allocas (bp_analyze_fuel (concretize_memloc_fuel fn) cfg fn) (Var v))` by
    (simp[GSYM bp_bases_find_base_allocas, bp_bases_def, MEM_MAP] >>
     metis_tac[ptr_base_def]) >>
  simp[ml_operand_gen_def] >> metis_tac[]
QED

Theorem ptr_production_operand_used_seed:
  fn_ptr_ok P fn /\ ssa_form fn /\ EVERY inst_wf (fn_insts fn) /\
  (!i. MEM i (fn_insts fn) ==> MEM i (bp_scan_insts fn cfg.cfg_dfs_pre)) /\
  MEM inst (fn_insts fn) /\ MEM (Var v) inst.inst_operands /\
  v IN pointer_derived_vars fn (ptr_bp_alloc_roots fn aid) ==>
  ml_used_gen (Allocation aid)
    (bp_analyze_fuel (concretize_memloc_fuel fn) cfg fn) mems inst
Proof
  strip_tac >> drule_all ptr_production_operand_gen >> simp[ml_used_gen_def]
QED

Theorem ptr_history_write_used:
  frame_history vs0 ctx stk PG G tn fn current s hs h /\
  EVERY wf_function ctx.ctx_functions /\ wf_function fn /\ all_reachable fn /\
  fn_ptr_ok P fn /\ ssa_form fn /\ EVERY inst_wf (fn_insts fn) /\
  MEM (inst,ss) h /\ MEM inst (fn_insts fn) /\
  inst_write_op inst = SOME (Var v) /\
  v IN pointer_derived_vars fn (ptr_bp_alloc_roots fn aid) ==>
  MEM (Allocation aid) (ml_lookup
    (SND (ml_iterate_fuel (concretize_memloc_fuel fn)
      (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn)
      mems sizes pallocas (cfg_analyze fn) fn FEMPTY FEMPTY))
    (s.vs_current_bb,s.vs_inst_idx))
Proof
  strip_tac >> irule ptr_history_current_used >>
  drule_all ptr_history_cfg_analyze_ok >> strip_tac >>
  simp[] >> first_assum (irule_at (Pos last)) >> simp[] >>
  goal_assum (drule_at Any) >>
  irule ptr_production_operand_used_seed >> simp[] >>
  metis_tac[bp_scan_production_complete, ptr_write_op_operand]
QED

(* Reuse the checked two-call PARAM-store fixture, rather than duplicating it.
   Each INVOKE is a seed through its actual pointer operand, not its opcode. *)
Theorem ptr_runtime_invoke_used_probe:
  ml_used_gen (Allocation 1) (sop_bp sop_caller) (K [])
    (mk_inst 3 INVOKE [Label "leaf"; Var "a"] []) /\
  ~ml_used_gen (Allocation 1) (sop_bp sop_caller) (K [])
    (mk_inst 3 INVOKE [Label "leaf"] []) /\
  MEM (Allocation 1) (ml_lookup
    (SND (ml_iterate_fuel (concretize_memloc_fuel sop_caller)
      (sop_bp sop_caller) (K []) (K NONE) [] (cfg_analyze sop_caller)
      sop_caller FEMPTY FEMPTY)) ("entry",4))
Proof
  EVAL_TAC >> simp[] >> qexists_tac `Var "a"` >> EVAL_TAC
QED

(* Probe report: remaining semantic premises.

   The ordinary-write branch of ptr_history_fresh_untainted_witness gives
   only byte containment in source_memory_write_ranges. It does not select
   an address operand's provenance, or identify the allocation id owning x.
   ptr_production_operand_used_seed therefore still requires the derivation
   witness explicitly. Production BP coverage supplies its static base;
   bp_scan_production_complete supplies its scan premise under wf_function
   and all_reachable. Instruction membership and well-formedness must be
   recovered from the actual activation/context, not from byte containment.

   Local allocations: current/saved selected-site support is available in
   concretizePtrPresentSupport, but its root family includes both allocation
   table roots and imported PARAM roots. A byte-to-selected-site fact and
   an allocation-specific root witness are still needed. Numeric overlap
   alone must not choose an id (zero-sized/other activations are distinct).

   Imported PARAM sites: the callee's BP map does not contain the caller's
   allocation base for a PARAM. In the reused sop fixture, p has empty BP;
   the caller's actual Var a operand seeds Allocation 1 at the INVOKE.
   sop_at_imported_write / sop_at_local_write already check the callee store.
   The positive and negative tests above distinguish argument evidence from
   the bare existence of a call. No caller root is invented in the callee.

   Suspended callers: ptr_history_saved_used covers a known generating
   observation in that caller's own history. A callee write is not such an
   observation. One must connect its selected imported site to the actual
   caller argument (or connect a callee-local site to imported metadata),
   then identify the caller INVOKE observation. This is not supplied by
   the existential INVOKE barrier: it loses the completed callee history,
   the byte-writing event within that history, the argument/site linkage,
   and even evidence that the call touches x at all. The witness is useful
   for excluding traces with neither calls nor writes, not for treating
   every call as a seed for every allocation. Backward future-demand and
   lifetime protection remain separate obligations.
*)
