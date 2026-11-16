(* Fixed-filling headroom and cut-guarded memory preservation by pruning. *)
Theory o1PruneFocusMemory
Ancestors
  o1SafeUpto o1ComposeSupport o1PipelineCompose ctxLookupAgree fcgPruning

Theorem prune_focus_headroom:
  fcg = fcg_analyze unit.cu_context /\
  o1_ctx_shape unit.cu_context /\
  unit.cu_context.ctx_entry = SOME name /\
  mem_inv dload_headroom_ok unit.cu_context vs ==>
  mem_inv dload_headroom_ok
    (prune_unit_fcg_unreachable unit fcg).cu_context vs
Proof
  strip_tac >>
  irule (cj 2 o1_prune_sim) >>
  simp[dload_headroom_ok_prune]
QED

Theorem prune_focus_cut_memory:
  fcg = fcg_analyze unit.cu_context /\
  o1_ctx_shape unit.cu_context /\
  unit.cu_context.ctx_entry = SOME name /\
  (!fn inst s. raw_reachable vs unit.cu_context fn inst s /\
     gas_cut n vs s ==>
     raw_mem_ok unit.cu_context fn inst s /\
     dload_offset_ok unit.cu_context fn inst s) ==>
  !fn inst s.
    raw_reachable vs (prune_unit_fcg_unreachable unit fcg).cu_context fn inst s /\
    gas_cut n vs s ==>
    raw_mem_ok (prune_unit_fcg_unreachable unit fcg).cu_context fn inst s /\
    dload_offset_ok (prune_unit_fcg_unreachable unit fcg).cu_context fn inst s
Proof
  strip_tac >>
  drule o1_ctx_shape_wf >> strip_tac >>
  drule_all prune_unit_ctx_agree >> strip_tac >>
  `fcg_is_reachable fcg name` by
    metis_tac[fcg_analyze_entry_reachable] >>
  `ctx_agree (fcg_is_reachable fcg)
     (prune_unit_fcg_unreachable unit fcg).cu_context unit.cu_context` by
    metis_tac[ctx_agree_sym] >>
  rpt gen_tac >> strip_tac >>
  `raw_reachable vs unit.cu_context fn inst s` by
    (drule raw_reachable_ctx_agree >>
     simp[prune_unit_fcg_unreachable_fields] >>
     metis_tac[]) >>
  first_x_assum drule_all >> strip_tac >>
  metis_tac[raw_mem_ok_ctx_free, dload_offset_ok_ctx_free]
QED
