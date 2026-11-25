(* A reachable oversized optimized CREATE requires a source exemption. *)
Theory linkedUnitCreateSize
Ancestors o1CreateSizeTransport[qualified] o1PipelineCorrect[qualified]
  unitMemInv unitShapeDefs venomRunBounded o1PassContract memSafeRun

Theorem o1_pipeline_create_size_from_raw_exemption:
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
  dead_wf D /\ o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\
  code_layout_valid vs /\ fmp_variant_room (SOME fmp) out.po_unit.cu_context vs /\
  (!vi. raw_variant fmp vi vs ==>
    o1_pre_walk_inv D unit.cu_context vi /\
    mem_inv (\ctx fn i s. inst_dload_in_section i s /\
      s.vs_code = vi.vs_code /\ s.vs_data_section = vi.vs_data_section)
      unit.cu_context vi) /\
  (!obs. ~(P : 'a -> bool) obs) /\
  (!vi fn i s. raw_variant fmp vi vs /\
    raw_reachable vi unit.cu_context fn i s /\ ~inst_create_size_ok i s ==>
    ?obs. P obs) ==>
  mem_inv (\ctx fn i s. inst_create_size_ok i s) out.po_unit.cu_context vs
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `unit_shape_ok out.po_unit` by
    (qspecl_then [`rpolicy`, `unit`, `out`] mp_tac
       o1PipelineCorrectTheory.run_venom_pipeline_output_shape >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  PURE_REWRITE_TAC [mem_inv_raw_reachable, inst_create_size_ok_def] >>
  BETA_TAC >>
  conj_tac
  >- (qpat_assum `unit_shape_ok out.po_unit`
        (strip_assume_tac o PURE_REWRITE_RULE [unit_shape_ok_def, entry_fn_first_def]) >>
      rename1 `out.po_unit.cu_context.ctx_functions = opt_fn::opt_rest` >>
      rename1 `out.po_unit.cu_context.ctx_entry = SOME opt_name` >>
      qexistsl_tac [`opt_name`, `opt_fn`, `opt_name`] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      `fn_shape_ok opt_fn` by
        (qpat_assum `out.po_unit.cu_context.ctx_functions = opt_fn::opt_rest`
          (fn funcs => qpat_assum `EVERY fn_shape_ok out.po_unit.cu_context.ctx_functions`
            (ACCEPT_TAC o CONJUNCT1 o PURE_REWRITE_RULE [funcs, listTheory.EVERY_DEF]))) >>
      conj_tac
      >- (qpat_assum `out.po_unit.cu_context.ctx_functions = opt_fn::opt_rest` SUBST1_TAC >>
          qpat_assum `opt_fn.fn_name = opt_name`
            (fn eq => simp[NoAsms, venomInstTheory.lookup_function_def, listTheory.FIND_thm, eq])) >>
      qpat_assum `fn_shape_ok opt_fn` (mp_tac o PURE_REWRITE_RULE [fn_shape_ok_def]) >>
      qpat_assum `opt_fn.fn_name = opt_name` (fn eq => simp[NoAsms, eq])) >>
  map_every qx_gen_tac [`visit_fn`, `visit_inst`, `visit_state`] >>
  disch_tac >>
  map_every qx_gen_tac [`value`, `off`, `sz`, `salt`, `sz_w`] >>
  disch_then (CONJUNCTS_THEN assume_tac) >>
  CCONTR_TAC >>
  mp_tac (Q.INST [`rp` |-> `rpolicy`, `unit` |-> `unit`,
    `out` |-> `out`, `v` |-> `vs`, `D` |-> `D`, `fmp` |-> `fmp`,
    `fn` |-> `visit_fn`, `j` |-> `visit_inst`, `t` |-> `visit_state`,
    `value` |-> `value`, `off` |-> `off`, `sz` |-> `sz`, `salt` |-> `salt`,
    `nbytes` |-> `sz_w`]
    (SPEC_ALL o1CreateSizeTransportTheory.o1_pipeline_reached_create_size)) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> asm_simp_tac bool_ss []) >>
  disch_then (qx_choosel_then [`vi`, `raw_fn`, `raw_inst`, `raw_state`, `a`, `p`, `z`, `sl`]
    (map_every assume_tac o CONJUNCTS)) >>
  `~inst_create_size_ok raw_inst raw_state` by
    (PURE_REWRITE_TAC [inst_create_size_ok_def] >>
     strip_tac >>
     pop_assum (qspecl_then [`a`, `p`, `z`, `sl`, `sz_w`] mp_tac) >>
     asm_simp_tac bool_ss []) >>
  qpat_assum `!vi fn i s. _ ==> ?obs. P obs`
    (qspecl_then [`vi`, `raw_fn`, `raw_inst`, `raw_state`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `obs` assume_tac) >>
  qpat_assum `!obs. ~P obs` (qspec_then `obs` mp_tac) >>
  asm_simp_tac bool_ss []
QED
