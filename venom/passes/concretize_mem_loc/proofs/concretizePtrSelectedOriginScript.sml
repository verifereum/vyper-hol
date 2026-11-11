Theory concretizePtrSelectedOrigin
Ancestors concretizePtrRuntimeGeneration concretizePtrActivationSupport
  concretizePtrClosure pointerClosure concretizePtrFrameOrigins concretizePtrBPOrigins
  concretizePtrRuntimeOrigins concretizeAnalysisScanCoverage
  ptrDiscipline pointerConfinedDefs venomWf venomInst list pred_set finite_map words

(* Well-formed outputs are needed: frame roots use MEM outputs, whereas BP
   allocation roots use inst_output (the singleton output selector). *)
Theorem ptr_selected_origin:
  EVERY inst_wf (fn_insts fn) /\
  ptr_site_supported (pointer_derived_vars fn (ptr_frame_site_roots fn A PG site)) G site /\
  FLOOKUP G v = SOME site ==>
  (?aid. FLOOKUP A aid = SOME site /\
    v IN pointer_derived_vars fn (ptr_bp_alloc_roots fn aid)) \/
  (?i idx r. MEM i (fn_insts fn) /\ i.inst_opcode = PARAM /\
    i.inst_operands = [Lit idx] /\ MEM r i.inst_outputs /\
    w2n idx < LENGTH PG /\ EL (w2n idx) PG = SOME site /\
    v IN pointer_derived_vars fn {r})
Proof
  strip_tac >>
  `v IN pointer_derived_vars fn (ptr_frame_site_roots fn A PG site)` by
    fs[ptr_site_supported_def] >>
  `?r. r IN ptr_frame_site_roots fn A PG site /\
       v IN pointer_derived_vars fn {r}` by
    metis_tac[ptr_derived_root_witness, ptr_frame_site_roots_finite] >>
  qpat_x_assum `r IN ptr_frame_site_roots _ _ _ _` mp_tac >>
  simp[ptr_frame_site_roots_def] >>
  disch_then (qx_choose_then `i` strip_assume_tac)
  >- (disj1_tac >> qexists `i.inst_id` >> simp[] >>
      `inst_wf i` by fs[EVERY_MEM] >>
      `inst_output i = SOME r` by
        (gvs[inst_wf_def] >> Cases_on `i.inst_outputs` >>
         gvs[inst_output_def] >> Cases_on `t` >> gvs[]) >>
      `pointer_derived_vars fn {r} SUBSET
        pointer_derived_vars fn (ptr_bp_alloc_roots fn i.inst_id)` by
        (irule ptr_derived_mono >> simp[ptr_bp_alloc_roots_finite] >>
         simp[SUBSET_DEF, ptr_bp_alloc_roots_def] >> metis_tac[]) >>
      fs[SUBSET_DEF]) >>
  disj2_tac >> metis_tac[]
QED

Theorem ptr_frame_write_selected_origin:
  frame_reachable vs0 ctx stk PG G tn fn inst s /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) ctx.ctx_functions /\
  fn_ptr_ok P fn /\ wf_function fn /\ all_reachable fn /\ ssa_form fn /\
  EVERY inst_wf (fn_insts fn) /\ MEM inst (fn_insts fn) /\
  inst_write_op inst = SOME (Var v) /\ FLOOKUP G v = SOME site ==>
  (?aid. FLOOKUP s.vs_allocas aid = SOME site /\
    ml_used_gen (Allocation aid)
      (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn) mems inst) \/
  (?i idx r. MEM i (fn_insts fn) /\ i.inst_opcode = PARAM /\
    i.inst_operands = [Lit idx] /\ MEM r i.inst_outputs /\
    w2n idx < LENGTH PG /\ EL (w2n idx) PG = SOME site /\
    v IN pointer_derived_vars fn {r})
Proof
  strip_tac >>
  `ptr_site_supported
    (pointer_derived_vars fn (ptr_frame_site_roots fn s.vs_allocas PG site)) G site` by
    metis_tac[ptr_frame_current_table_support] >>
  drule_all ptr_selected_origin >> strip_tac
  >- (disj1_tac >> qexists `aid` >> simp[] >>
      irule ptr_production_operand_used_seed >> simp[] >>
      metis_tac[bp_scan_production_complete, ptr_write_op_operand]) >>
  disj2_tac >> metis_tac[]
QED

(* This origin disjunction does not select provenance from a numeric byte
   range. It also does not retain completed callee writes or establish
   suspended-caller lifetime protection. Imported PARAMs retain their index
   precisely so later call linkage need not invent a callee-local BP root. *)
