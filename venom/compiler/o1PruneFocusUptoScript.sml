(* Fixed-filling bounded pointer safety and actual-entry events for pruning. *)
Theory o1PruneFocusUpto
Ancestors
  o1SafeUpto ptrDiscipline ptrDisciplineAgree ctxLookupAgree o1ComposeSupport
  o1PipelineCompose fcgPruning gasEvents list

Theorem prune_focus_ptr_upto:
  fcg = fcg_analyze unit.cu_context /\
  o1_ctx_shape unit.cu_context /\
  unit.cu_context.ctx_entry = SOME name /\
  o1_ptr_safe_upto D lo n unit.cu_context vs ==>
  o1_ptr_safe_upto D lo n
    (prune_unit_fcg_unreachable unit fcg).cu_context vs
Proof
  strip_tac >>
  drule o1_ctx_shape_wf >> strip_tac >>
  drule_all prune_unit_ctx_agree >> strip_tac >>
  `fcg_is_reachable fcg name` by
    metis_tac[fcg_analyze_entry_reachable] >>
  fs[o1_ptr_safe_upto_def] >>
  simp[o1_ptr_safe_upto_def, prune_unit_fcg_unreachable_fields] >>
  conj_tac
  >- (fs[EVERY_MEM] >> metis_tac[MEM_prune_unit_fcg_unreachable_functions]) >>
  conj_tac >- metis_tac[fmp_free_ctx_prune] >>
  conj_tac
  >- fs[fixed_region_reserved_def, prune_unit_fcg_unreachable_fields] >>
  conj_tac
  >- (irule ptr_discipline_upto_ctx_agree >>
      qexists_tac `fcg_is_reachable fcg` >>
      qexists_tac `unit.cu_context` >>
      simp[prune_unit_fcg_unreachable_fields,
           MEM_prune_unit_fcg_unreachable_functions] >> metis_tac[]) >>
  irule taint_within_upto_ctx_agree >>
  qexists_tac `fcg_is_reachable fcg` >>
  qexists_tac `unit.cu_context` >>
  simp[prune_unit_fcg_unreachable_fields] >> metis_tac[]
QED

Theorem prune_focus_entry_events:
  fcg = fcg_analyze unit.cu_context /\
  o1_ctx_shape unit.cu_context /\
  unit.cu_context.ctx_entry = SOME name /\
  lookup_function name unit.cu_context.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl ==>
  (prune_unit_fcg_unreachable unit fcg).cu_context.ctx_entry = SOME name /\
  lookup_function name
    (prune_unit_fcg_unreachable unit fcg).cu_context.ctx_functions = SOME fn /\
  gas_events_blocks fuel
    (prune_unit_fcg_unreachable unit fcg).cu_context fn
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) =
  gas_events_blocks fuel unit.cu_context fn
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)
Proof
  strip_tac >>
  drule o1_ctx_shape_wf >> strip_tac >>
  drule_all prune_unit_ctx_agree >> strip_tac >>
  `fcg_is_reachable fcg name` by
    metis_tac[fcg_analyze_entry_reachable] >>
  `lookup_function name
     (prune_unit_fcg_unreachable unit fcg).cu_context.ctx_functions = SOME fn /\
   fn_calls_within (fcg_is_reachable fcg) fn` by
    metis_tac[ctx_agree_def] >>
  simp[prune_unit_fcg_unreachable_fields] >>
  metis_tac[cj 3 gas_events_defs_ctx_agree]
QED
