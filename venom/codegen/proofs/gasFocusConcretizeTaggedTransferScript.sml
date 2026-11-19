Theory gasFocusConcretizeTaggedTransfer
Ancestors
  concretizePtrSourceOwnership concretizePtrParamSupport concretizePtrChronologicalHistory
  runtimeProvenanceSources pointerClosure concretizeAnalysisRoots pointerConfinedDefs
  ptrDiscipline contextCodegenRel venomWfProps venomInst allocaFrontierBound
  finite_map list pred_set

(* All direct ancestors checked against the M0002 NEW HELPER GUARD.
   Tagged support concerns domains only; no numerical erasure or safety. *)
Theorem ptr_focus_tagged_step_support:
  ptr_params_ok P fn PT /\ ptr_static_support P fn TG /\
  MEM inst (fn_insts fn) /\ fn_ptr_ok P fn /\ EVERY inst_wf (fn_insts fn) ==>
  ptr_static_support P fn (ptr_tagged_step token PT TG inst s)
Proof
  strip_tac >> simp[ptr_tagged_step_def] >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (simp[ptr_static_support_def] >> rpt strip_tac >>
      drule set_prov_source >> strip_tac
      >- metis_tac[ptr_static_support_def] >>
      `inst_output inst = SOME v` by simp[inst_output_def] >>
      `v IN ptr_roots P fn` by
        (simp[ptr_roots_def, alloca_roots_def] >> metis_tac[]) >>
      metis_tac[pointer_derived_vars_roots, ptr_roots_finite,
                fn_pv_def, SUBSET_DEF]) >>
  Cases_on `inst.inst_opcode = DALLOCA`
  >- (simp[ptr_static_support_def] >> rpt strip_tac >>
      drule set_prov_source >> simp[] >>
      metis_tac[ptr_static_support_def]) >>
  simp[] >> irule ptr_static_step >> simp[]
QED

Theorem ptr_focus_tagged_chrono_support:
  ptr_tagged_chrono_step C token a b PT TG saved PT' TG' saved' /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  MEM a.po_fn C.ctx_functions /\ ptr_params_ok P a.po_fn PT /\
  ptr_static_support P a.po_fn TG /\
  LIST_REL (\tags fr. MEM fr.cf_fn C.ctx_functions /\
    ptr_params_ok P fr.cf_fn (FST tags) /\
    ptr_static_support P fr.cf_fn (SND tags)) saved a.po_stack ==>
  MEM b.po_fn C.ctx_functions /\ ptr_params_ok P b.po_fn PT' /\
  ptr_static_support P b.po_fn TG' /\
  LIST_REL (\tags fr. MEM fr.cf_fn C.ctx_functions /\
    ptr_params_ok P fr.cf_fn (FST tags) /\
    ptr_static_support P fr.cf_fn (SND tags)) saved' b.po_stack
Proof
  strip_tac >>
  qpat_x_assum `ptr_tagged_chrono_step _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[Once ptr_tagged_chrono_step_cases, ptr_observe_def] >>
  strip_tac >> gvs[]
  >- (irule ptr_focus_tagged_step_support >>
      fs[EVERY_MEM] >> metis_tac[active_inst_mem_fn_insts])
  >- metis_tac[ptr_static_entry]
  >- (simp[] >> conj_tac
      >- metis_tac[lookup_function_MEM] >>
      irule ptr_static_invoke_params >> fs[EVERY_MEM] >>
      metis_tac[active_inst_mem_fn_insts]) >>
  gvs[] >> metis_tac[ptr_static_restrict]
QED
