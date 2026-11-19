(* Apply the fixed-reading code-end core at the packet's selected input. *)
Theory gasFocusStaticCodeEndSeam
Ancestors
  gasFocusStaticExitLift o1StaticPipelineCorrect o1PipelineCorrect
  o1PassContract venomPassSchedule codegenEntrySim codegenEntryRel
  asmOptimizer words list

Theorem focus_static_selected_code_end_exit:
  rds = raw ++ [0w] /\
  v7 = (vs0 with vs_gas_readings := rds) /\
  vi = (v7 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  run_pipeline_stages rpolicy o1_pipeline_spec.ps_pre_walk_stages unit
    (init_ir_supply unit) = SOME (pre,t) /\
  pre.cu_context.ctx_entry = SOME nm /\
  stage 0 = (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context /\
  stage 9 = out.po_unit.cu_context /\
  (!k. k < 9 ==> ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
    (stage k) (stage (SUC k))) /\
  (!k. k <= 9 ==> o1_ctx_shape (stage k) /\
    EVERY (o1_fn_row k) (stage k).ctx_functions) /\
  dead_wf D /\ o1_initial_state_ok vs0 /\
  vs0.vs_fmp = vs0.vs_initial_fmp /\ code_layout_valid vs0 /\
  o1_pre_walk_inv D unit.cu_context vi /\
  generate_context_plan out.po_unit.cu_context = SOME cpl /\
  codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0) /\
  w2n vs0.vs_initial_fmp <= w2n fmp /\
  (!fuel. gas_res_rel (run_context fuel (stage 7) v7)
    (ev_context orc fuel (stage 7) vs0)) /\
  (!fuel. gas_res_rel (run_context fuel (stage 8) vs0)
    (ev_context orc fuel (stage 8) vs0)) /\
  (!p d fn inst s. ev_reachable orc vs0 (stage 7) p d fn inst s ==>
    ?ws. raw_reachable v7 (stage 7) fn inst (s with vs_gas_readings := ws)) /\
  (!fn inst s. raw_reachable vs0 (stage 8) fn inst s ==>
    ?p d. ev_reachable orc vs0 (stage 8) p d fn inst
           (s with vs_gas_readings := vs0.vs_gas_readings)) /\
  (fin = asm_opt_finalizer ==>
    (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
      ~MEM (Label "code_end") inst.inst_operands) /\
    LENGTH vs0.vs_data_section < dimword (:256) DIV 2 /\
    mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
      s.vs_code = vs0.vs_code /\ s.vs_data_section = vs0.vs_data_section)
      unit.cu_context vi) /\
  (o1_lowered_inv out.po_unit.cu_context vs0 \/
   ((?eom. max_live_eom out.po_unit.cu_context = SOME eom /\
      mem_inv (\ctx fn inst s. in_static_abort_prefix fn s \/
        lowered_mem_ok eom (w2n s.vs_initial_fmp) ctx fn inst s)
        out.po_unit.cu_context vs0) /\
    !fuel. terminates (run_context fuel unit.cu_context vi) ==>
      ?u. run_context fuel unit.cu_context vi = Abort ExHalt_abort u)) ==>
  (fin = asm_opt_finalizer ==>
    code_end_offset_ok
      (\ctx fn inst s. raw_reachable vs0 ctx fn inst s /\ ~in_static_abort_prefix fn s)
      out.po_unit.cu_context) /\
  ((o1_lowered_inv out.po_unit.cu_context vs0 /\
    (fin = asm_opt_finalizer ==>
       code_end_offset_ok (raw_reachable vs0) out.po_unit.cu_context)) \/
   ((?eom. max_live_eom out.po_unit.cu_context = SOME eom /\
      mem_inv (\ctx fn inst s. in_static_abort_prefix fn s \/
        lowered_mem_ok eom (w2n s.vs_initial_fmp) ctx fn inst s)
        out.po_unit.cu_context vs0) /\
    !fuel. terminates (run_context fuel unit.cu_context vi) ==>
      ?u. run_context fuel unit.cu_context vi = Abort ExHalt_abort u))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  MATCH_MP_TAC (Q.INST [`opt` |-> `fin = asm_opt_finalizer`] focus_static_code_end_exit) >>
  (reverse conj_tac >- first_assum ACCEPT_TAC) >>
  disch_tac >>
  `fmp_variant_room (SOME fmp) out.po_unit.cu_context vs0` by
    (simp[fmp_variant_room_def] >>
     `vs0.vs_initial_fmp = n2w cpl.cp_initial_fmp` by
       fs[codegen_asm_entry_rel_def] >>
     qspecl_then [`out.po_unit.cu_context`, `cpl`, `vs0`] mp_tac
       generate_context_plan_eom_room >> simp[]) >>
  qpat_assum `fin = asm_opt_finalizer ==> _` (fn th => drule th >> strip_tac) >>
  `mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
      s.vs_code = vi.vs_code /\ s.vs_data_section = vi.vs_data_section)
    unit.cu_context vi` by
    (qpat_assum `mem_inv _ _ vi` mp_tac >>
     qpat_assum `vi = _` (fn th => PURE_REWRITE_TAC [th]) >>
     qpat_assum `v7 = _` (fn th => PURE_REWRITE_TAC [th]) >> simp[NoAsms]) >>
  `LENGTH o1_fn_passes = 9` by simp[o1_fn_passes_def] >>
  qpat_assum `!k. k <= 9 ==> _`
    (map_every assume_tac o CONJUNCTS o
      CONV_RULE (BINDER_CONV (REWR_CONV IMP_CONJ_THM) THENC FORALL_AND_CONV)) >>
  qpat_assum `LENGTH o1_fn_passes = 9` (fn len =>
    drule_all_then ACCEPT_TAC
      (PURE_REWRITE_RULE[len] o1_pipeline_code_end_offset_ok_static_abort_fixed))
QED
