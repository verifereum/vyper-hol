(* Memory and pointer facts exported from safe linked-unit entry runs. *)
Theory linkedUnitMemory
Ancestors
  compileUnit vyperCompiler vyperLoweringCorrect deployUnitProducers
  ctorDeployMemoryFrontier sourceUnitExecutionMods bodyInvSplit
  acceptedContextPhi fragGasPathMem fragExecMem fragExec entryDispatchMem
  unitMemInv unitTransformDefs ptrDiscipline ptrSafeRun ptrOkCheck
  rawReachableFmp ctxLookupAgree o1SafeUpto
  lowerDloadDefs allocaFrontierBound memSafeRun contextCodegenRel
  venomInst venomState venomExecSemantics venomExecProofs
  finite_map list rich_list words

(* Both runtime runners install a checked context with raw function metadata. *)
Theorem linked_runtime_memory_context[local]:
  lower_vyper_runtime_unit_mods mods exps rp = SOME unit ==>
  lowering_context_ok unit.cu_context /\
  unit.cu_context.ctx_entry = SOME "__entry" /\
  (?func. lookup_function "__entry" unit.cu_context.ctx_functions = SOME func) /\
  EVERY (\func. func.fn_eom = NONE) unit.cu_context.ctx_functions
Proof
  simp[lower_vyper_runtime_unit_mods_def] >>
  pairarg_tac >> simp[bool_case_eq] >>
  strip_tac >> gvs[] >-
    (qpat_x_assum `run_grouped_lowering _ _ _ _ _ = _ ` mp_tac >>
     simp[run_grouped_lowering_def, extract_context_with_internals_def,
          mk_venom_context_def] >>
     pairarg_tac >> gvs[AllCaseEqs()] >>
     strip_tac >> gvs[] >>
     simp[lookup_function_def, listTheory.FIND_thm, mk_raw_function_def] >>
     drule package_internal_blocks_raw_defaults >>
     simp[EVERY_MEM, function_raw_metadata_defaults_def]) >>
  drule run_lowering_context_ok >>
  drule run_lowering_entry >>
  drule run_lowering_eom_none >>
  simp[]
QED

(* Without DALLOCA, the pointer check excludes all raw FMP operations. *)
Theorem checked_static_raw_fmp[local]:
  lowering_context_ok ctx /\ ~ctx_has_dalloca ctx /\
  w2n vs.vs_initial_fmp <= w2n vs.vs_fmp /\
  raw_reachable vs ctx func inst s ==>
  dalloca_no_wrap inst s /\ w2n s.vs_initial_fmp <= w2n s.vs_fmp
Proof
  strip_tac >>
  `ptr_ok_check ctx` by fs[lowering_context_ok_def] >>
  drule ptr_ok_check_sound >> strip_tac >>
  `EVERY no_raw_fmp_ops ctx.ctx_functions` by
    (rw[EVERY_MEM, no_raw_fmp_ops_def] >>
     rename1 `MEM f ctx.ctx_functions` >>
     rename1 `MEM i (fn_insts f)` >>
     `fn_ptr_ok (\nm. set (ctx_ptr_param_list ctx nm)) f` by fs[EVERY_MEM] >>
     `i.inst_opcode <> DALLOCA` by
       (fs[ctx_has_dalloca_def, EXISTS_MEM] >> metis_tac[]) >>
     `i.inst_opcode <> DRET /\ i.inst_opcode <> GETFMP /\
      i.inst_opcode <> SETFMP /\ i.inst_opcode <> RETFMP` by
       (fs[fn_ptr_ok_def] >> metis_tac[]) >>
     Cases_on `i.inst_opcode` >> gvs[is_raw_fmp_opcode_def]) >>
  drule raw_reachable_initial_fmp >> strip_tac >>
  drule_all raw_reachable_no_raw_fmp_fixed >> strip_tac >> simp[] >>
  drule active_inst_mem_fn_insts >> strip_tac >>
  fs[ctx_has_dalloca_def, EXISTS_MEM, dalloca_no_wrap_def] >>
  metis_tac[]
QED

Theorem lower_vyper_runtime_unit_ptr_taint_mods:
  !mods exps rpolicy unit vs fn lbl D.
    lower_vyper_runtime_unit_mods mods exps rpolicy = SOME unit /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl /\
    (!fuel. ptr_safe_blocks D 0 fuel unit.cu_context fn [] FEMPTY entry_taint
       (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                   vs_inst_idx := 0 |>))
    ==> ptr_discipline 0 unit.cu_context vs /\
        taint_within D unit.cu_context vs
Proof
  rpt gen_tac >> strip_tac >>
  drule linked_runtime_memory_context >> strip_tac >> gvs[] >>
  qspecl_then [`D`, `0`, `unit.cu_context`, `"__entry"`, `fn`, `lbl`, `vs`]
    mp_tac lowered_unit_ptr_taint >> simp[]
QED

Theorem lower_vyper_runtime_unit_memory_ok_from_no_wrap_mods:
  !mods exps rpolicy unit am tx vs fn lbl D.
    lower_vyper_runtime_unit_mods mods exps rpolicy = SOME unit /\
    initial_venom_state_rel_mods mods am tx vs /\
    (!f inst s. raw_reachable vs unit.cu_context f inst s ==>
       dalloca_no_wrap inst s /\ w2n s.vs_initial_fmp <= w2n s.vs_fmp) /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl /\
    (!fuel. mem_safe_blocks fuel unit.cu_context fn
       (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                   vs_inst_idx := 0 |>)) /\
    (!fuel. ptr_safe_blocks D 0 fuel unit.cu_context fn [] FEMPTY entry_taint
       (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                   vs_inst_idx := 0 |>))
    ==> raw_unit_memory_ok unit.cu_context vs /\
        EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
        fixed_region_reserved 0 unit.cu_context /\
        ptr_discipline 0 unit.cu_context vs /\
        taint_within D unit.cu_context vs
Proof
  rpt gen_tac >> strip_tac >>
  drule linked_runtime_memory_context >> strip_tac >> gvs[] >>
  `vs.vs_alloca_next = 0` by fs[initial_venom_state_rel_mods_def] >>
  `raw_unit_memory_ok unit.cu_context vs` by
    (qspecl_then [`0`, `unit.cu_context`, `"__entry"`, `fn`, `lbl`, `vs`]
      mp_tac lowered_unit_raw_memory_ok_from_no_wrap >>
     simp[lowering_context_ok_alloca_budget] >>
     impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  qspecl_then [`mods`, `exps`, `rpolicy`, `unit`, `vs`, `fn`, `lbl`, `D`]
    mp_tac lower_vyper_runtime_unit_ptr_taint_mods >>
  simp[fixed_region_reserved_def]
QED

Theorem lower_vyper_runtime_unit_memory_ok_mods:
  !mods exps rpolicy unit am tx vs fn lbl D.
    lower_vyper_runtime_unit_mods mods exps rpolicy = SOME unit /\
    initial_venom_state_rel_mods mods am tx vs /\
    ~ctx_has_dalloca unit.cu_context /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl /\
    (!fuel. mem_safe_blocks fuel unit.cu_context fn
       (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                   vs_inst_idx := 0 |>)) /\
    (!fuel. ptr_safe_blocks D 0 fuel unit.cu_context fn [] FEMPTY entry_taint
       (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                   vs_inst_idx := 0 |>))
    ==> raw_unit_memory_ok unit.cu_context vs /\
        EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
        fixed_region_reserved 0 unit.cu_context /\
        ptr_discipline 0 unit.cu_context vs /\
        taint_within D unit.cu_context vs
Proof
  rpt gen_tac >> strip_tac >>
  drule linked_runtime_memory_context >> strip_tac >> gvs[] >>
  `w2n vs.vs_initial_fmp <= w2n vs.vs_fmp` by
    fs[initial_venom_state_rel_mods_def] >>
  qspecl_then [`mods`, `exps`, `rpolicy`, `unit`, `am`, `tx`,
               `vs`, `fn`, `lbl`, `D`]
    mp_tac lower_vyper_runtime_unit_memory_ok_from_no_wrap_mods >>
  impl_tac >- (simp[] >> rpt strip_tac >> drule_all checked_static_raw_fmp >> simp[]) >>
  simp[]
QED

Theorem lower_vyper_runtime_unit_dload_in_section_mods:
  !mods exps rpolicy unit vs fn lbl.
    lower_vyper_runtime_unit_mods mods exps rpolicy = SOME unit /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl /\
    (!fuel. mem_safe_blocks fuel unit.cu_context fn
       (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                   vs_inst_idx := 0 |>))
    ==> mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                                 s.vs_code = vs.vs_code /\
                                 s.vs_data_section = vs.vs_data_section)
          unit.cu_context vs
Proof
  rpt gen_tac >> strip_tac >>
  drule linked_runtime_memory_context >> strip_tac >> gvs[] >>
  simp[mem_inv_raw_reachable] >>
  qspecl_then [`unit.cu_context`, `"__entry"`, `fn`, `lbl`, `vs`]
    mp_tac lowered_unit_dload_in_section >> simp[] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  drule raw_reachable_code_data >> strip_tac >>
  qpat_x_assum `!f i u. raw_reachable _ _ f i u ==> inst_dload_in_section i u`
    (drule_then assume_tac) >> simp[]
QED

Theorem lower_vyper_runtime_unit_dload_offset_ok_mods:
  !mods exps rpolicy unit vs fn lbl.
    lower_vyper_runtime_unit_mods mods exps rpolicy = SOME unit /\
    code_layout_valid vs /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl /\
    (!fuel. mem_safe_blocks fuel unit.cu_context fn
       (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                   vs_inst_idx := 0 |>))
    ==> mem_inv dload_offset_ok unit.cu_context vs
Proof
  rpt gen_tac >> strip_tac >>
  drule linked_runtime_memory_context >> strip_tac >> gvs[] >>
  qspecl_then [`unit.cu_context`, `"__entry"`, `fn`, `lbl`, `vs`]
    mp_tac lowered_unit_dload_offset_ok >> simp[]
QED

Theorem lower_vyper_runtime_unit_dload_headroom_ok_mods:
  !mods exps rpolicy unit am tx vs.
    lower_vyper_runtime_unit_mods mods exps rpolicy = SOME unit /\
    initial_venom_state_rel_mods mods am tx vs /\
    (ctx_has_dalloca unit.cu_context ==>
     unit_alloca_budget unit.cu_context +
       32 * ctx_dload_count unit.cu_context <= w2n vs.vs_initial_fmp)
    ==> mem_inv dload_headroom_ok unit.cu_context vs
Proof
  rpt gen_tac >> strip_tac >>
  drule linked_runtime_memory_context >> strip_tac >> gvs[] >>
  `vs.vs_alloca_next = 0` by fs[initial_venom_state_rel_mods_def] >>
  rename1 `lookup_function "__entry" _ = SOME entry_fn` >>
  qspecl_then [`0`, `unit.cu_context`, `"__entry"`, `entry_fn`, `vs`]
    mp_tac lowered_unit_dload_headroom_ok_from >> simp[] >>
  drule lowering_context_ok_dload_budget >>
  simp[ctx_dload_count_def, FILTER_FLAT, LENGTH_FLAT, MAP_MAP_o,
       combinTheory.o_DEF]
QED

Theorem lower_vyper_runtime_unit_exit_mem_safe_blocks_mods:
  !mods exps rpolicy unit func s n r.
    lower_vyper_runtime_unit_mods mods exps rpolicy = SOME unit /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
    s.vs_inst_idx = 0 /\
    gas_path_mem unit.cu_context func s n r /\ exit_result r ==>
    !fuel. mem_safe_blocks fuel unit.cu_context func s
Proof
  rpt gen_tac >> strip_tac >>
  drule linked_runtime_memory_context >> strip_tac >> gvs[] >>
  drule gas_path_mem_exec >> strip_tac >> gvs[exit_result_def] >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by
    (Cases_on `lookup_block s.vs_current_bb func.fn_blocks` >>
     gvs[run_from_def, exit_result_def]) >>
  `phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[lowering_context_ok_block_phi] >>
  `!m. mem_safe_run m unit.cu_context func s` by
    (irule mem_safe_run_all_fuel >> qexists_tac `fuel` >>
     simp[] >> metis_tac[exit_result_not_error]) >>
  `s with vs_inst_idx := 0 = s` by simp[venom_state_component_equality] >>
  irule mem_safe_blocks_no_phi >> asm_rewrite_tac[] >> qexists_tac `bb` >>
  asm_simp_tac std_ss [eval_phis_no_phi]
QED

(* The deployment allocation budget includes the entire immutable prefix. *)
Theorem linked_deploy_memory_context[local]:
  lower_vyper_deploy_unit_mods mods exps rp bc = SOME unit ==>
  lowering_context_ok unit.cu_context /\
  unit.cu_context.ctx_entry = SOME "__deploy" /\
  imm_len_mods mods + unit_alloca_budget unit.cu_context +
    32 * ctx_dload_count unit.cu_context < dimword (:256)
Proof
  simp[lower_vyper_deploy_unit_mods_def] >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> simp[bool_case_eq] >> strip_tac >>
  drule run_deploy_lowering_context_ok >> strip_tac >>
  drule run_deploy_lowering_static_headroom >>
  simp[ctx_dload_count_def, FILTER_FLAT, LENGTH_FLAT, MAP_MAP_o,
       combinTheory.o_DEF, dimword_def, venomLayoutTheory.dimindex_256] >>
  strip_tac >>
  conj_tac
  >- (qpat_x_assum `run_deploy_lowering _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ ` mp_tac >>
      simp[run_deploy_lowering_def, extract_context_with_internals_def,
           install_immutable_reservation_def, mk_venom_context_def] >>
      pairarg_tac >> gvs[AllCaseEqs()] >> strip_tac >> gvs[]) >>
  fs[imm_len_mods_def] >> decide_tac
QED

Theorem checked_deploy_memory_from_no_wrap[local]:
  !k ctx func vs.
  lowering_context_ok ctx /\ ctx.ctx_entry = SOME "__deploy" /\
  vs.vs_alloca_next = k /\
  k + unit_alloca_budget ctx + 32 * ctx_dload_count ctx < dimword (:256) /\
  (ctx_has_dalloca ctx ==>
     k + unit_alloca_budget ctx + 32 * ctx_dload_count ctx <= w2n vs.vs_initial_fmp) /\
  (!f inst s. raw_reachable vs ctx f inst s ==>
      dalloca_no_wrap inst s /\ w2n s.vs_initial_fmp <= w2n s.vs_fmp) /\
  code_layout_valid vs /\
  lookup_function "__deploy" ctx.ctx_functions = SOME func /\
  fn_entry_label func = SOME "__deploy" /\
  (!fuel. mem_safe_blocks fuel ctx func
     (vs with <|vs_prev_bb := NONE; vs_current_bb := "__deploy";
                vs_inst_idx := 0|>)) ==>
  raw_unit_memory_ok ctx vs /\ mem_inv dload_offset_ok ctx vs /\
  mem_inv dload_headroom_ok ctx vs
Proof
  rpt gen_tac >> strip_tac >> rpt conj_tac
  >- (qspecl_then [`k`, `ctx`, `"__deploy"`, `func`, `"__deploy"`, `vs`]
        mp_tac lowered_unit_raw_memory_ok_from_no_wrap >>
      impl_tac >- (simp[] >> first_assum ACCEPT_TAC) >>
      simp[])
  >- (qspecl_then [`ctx`, `"__deploy"`, `func`, `"__deploy"`, `vs`]
        mp_tac lowered_unit_dload_offset_ok >> simp[]) >>
  qspecl_then [`k`, `ctx`, `"__deploy"`, `func`, `vs`]
    mp_tac lowered_unit_dload_headroom_ok_from >> simp[]
QED

Theorem deploy_selected_memory_from_checked_mods:
  lower_vyper_deploy_unit_mods mods exps rpolicy runtime_bc = SOME dunit /\
  vs.vs_alloca_next = imm_len_mods mods /\
  ctx_has_dalloca dunit.cu_context /\
  imm_len_mods mods + unit_alloca_budget dunit.cu_context +
    32 * ctx_dload_count dunit.cu_context <= w2n vs.vs_initial_fmp /\
  code_layout_valid vs /\
  lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME func /\
  fn_entry_label func = SOME "__deploy" /\
  (!fuel. mem_safe_blocks fuel dunit.cu_context func
     (vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                 vs_inst_idx := 0 |>)) /\
  (!fuel. ptr_safe_blocks D (imm_len_mods mods) fuel dunit.cu_context func [] FEMPTY
     entry_taint
     (vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                 vs_inst_idx := 0 |>)) ==>
  raw_unit_memory_ok dunit.cu_context vs /\
  ptr_discipline (imm_len_mods mods) dunit.cu_context vs /\
  taint_within D dunit.cu_context vs /\
  mem_inv dload_offset_ok dunit.cu_context vs /\
  mem_inv dload_headroom_ok dunit.cu_context vs
Proof
  strip_tac >>
  drule linked_deploy_memory_context >> strip_tac >>
  qspecl_then [`D`, `imm_len_mods mods`, `dunit.cu_context`, `"__deploy"`,
               `func`, `"__deploy"`, `vs`]
    mp_tac lowered_unit_ptr_taint >> simp[] >> strip_tac >>
  qspecl_then [`imm_len_mods mods`, `dunit.cu_context`, `func`, `vs`]
    mp_tac checked_deploy_memory_from_no_wrap >>
  impl_tac >- (
    simp[] >>
  qspecl_then [`imm_len_mods mods`, `dunit.cu_context`, `"__deploy"`,
               `func`, `"__deploy"`, `vs`]
    mp_tac lowered_unit_checked_dalloca_facts >> simp[]) >>
  simp[]
QED

Theorem deploy_selected_memory_mods:
  lower_vyper_deploy_unit_mods mods exps rpolicy runtime_bc = SOME dunit /\
  ~ctx_has_dalloca dunit.cu_context /\
  vs.vs_alloca_next = imm_len_mods mods /\
  w2n vs.vs_initial_fmp <= w2n vs.vs_fmp /\
  code_layout_valid vs /\
  lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME func /\
  fn_entry_label func = SOME "__deploy" /\
  (!fuel. mem_safe_blocks fuel dunit.cu_context func
     (vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                 vs_inst_idx := 0 |>)) /\
  (!fuel. ptr_safe_blocks D (imm_len_mods mods) fuel dunit.cu_context func [] FEMPTY
     entry_taint
     (vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                 vs_inst_idx := 0 |>)) ==>
  raw_unit_memory_ok dunit.cu_context vs /\
  ptr_discipline (imm_len_mods mods) dunit.cu_context vs /\
  taint_within D dunit.cu_context vs /\
  mem_inv dload_offset_ok dunit.cu_context vs /\
  mem_inv dload_headroom_ok dunit.cu_context vs
Proof
  strip_tac >>
  drule linked_deploy_memory_context >> strip_tac >>
  qspecl_then [`D`, `imm_len_mods mods`, `dunit.cu_context`, `"__deploy"`,
               `func`, `"__deploy"`, `vs`]
    mp_tac lowered_unit_ptr_taint >> simp[] >> strip_tac >>
  qspecl_then [`imm_len_mods mods`, `dunit.cu_context`, `func`, `vs`]
    mp_tac checked_deploy_memory_from_no_wrap >>
  impl_tac >- (
    simp[] >>
  rpt strip_tac >> drule_all checked_static_raw_fmp >> simp[]) >>
  simp[]
QED
