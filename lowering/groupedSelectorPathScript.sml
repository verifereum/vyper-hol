(* Walk the actual comparisons to the first matching grouped entry. *)
Theory groupedSelectorPath
Ancestors
  groupedInternalLabels groupedSelectorStep entryDispatchPtr typedCopyArrayPtr
  actualEntryAllocationFrame moduleLoweringProps emitHelperProps
  fragGasOriginPtr fragGasOriginPtrExec fragGasPathPtr ptrDiscipline
  compileEnv moduleLowering fragExec venomState ptrSafeRun loweringStateRelDefs
  finite_map list

Theorem selector_entry_ghost[local]:
  (!bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) ==>
  entry_prov fn s G = G /\ entry_taint_vars fn s tn = tn
Proof
  strip_tac >> Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- simp[entry_prov_def, entry_taint_vars_def] >>
  irule entry_ghost_no_phi >> simp[]
QED

Theorem compile_group_entries_selected_origin:
  !entries mid common vars off sa sb fn m s ctx PG G tn lo.
    compile_group_entries mid entries common vars off sa = ((),sb) /\
    fn_has_code sa sb fn /\
    EVERY (\(_,name,_,_). ~internal_label_ok name) entries /\
    (!name bb. lookup_block name fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
    fresh_vars_wrt sa s /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    eval_operand mid s = SOME m /\ op_taint tn mid = {} /\
    allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
    !sel lbl mincd k.
      FIND (\(n,_,_,_). m = n2w n) entries = SOME (sel,lbl,mincd,k) ==>
      ?checks init done t G' tn'.
        checks.cs_current_bb = lbl /\ checks.cs_current_insts = [] /\
        sa.cs_next_id <= checks.cs_next_id /\
        sa.cs_next_var < checks.cs_next_var /\
        compile_entry_checks mincd common.ec_payable checks = ((),init) /\
        fn_has_code checks init fn /\
        compile_entry_point_kwargs common.ec_env vars off k common.ec_common_label init =
          ((),done) /\ fn_has_code init done fn /\
        (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
          (s,G,tn) [] (OK t,G',tn')) /\
        vars_pc_only s t /\ t.vs_current_bb = lbl /\ t.vs_inst_idx = 0 /\
        fresh_vars_wrt checks t /\
        tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
        tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
        (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
          FLOOKUP G' p = FLOOKUP G p /\ op_taint tn' (Var p) = op_taint tn (Var p)) /\
        (!D. (!fuel. ptr_safe_blocks D lo fuel ctx fn PG G' tn' t) ==>
          !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  Induct >> simp[FIND_thm] >>
  gen_tac >> PairCases_on `h` >> simp[EVERY_DEF, FIND_thm] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all compile_group_entries_cons_layout >>
  disch_then (qx_choosel_then [`next`,`next_state`,`checks`,`init`,`done`,`bb`]
    strip_assume_tac) >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  mp_tac (Q.INST [`func` |-> `fn`, `s` |-> `s`, `G` |-> `G`, `tn` |-> `tn`,
     `out` |-> `out`, `mid` |-> `mid`, `ctx` |-> `ctx`, `lo` |-> `lo`,
     `PG` |-> `PG`, `sel` |-> `h0`, `yes` |-> `h1`, `no` |-> `next`,
     `id` |-> `sa.cs_next_id`, `id'` |-> `sa.cs_next_id + 1`, `bb` |-> `bb`,
     `m` |-> `m`] grouped_comparison_origin_path) >>
  impl_tac >- fs[Abbr `out`] >>
  disch_then (qx_choosel_then [`u`, `Gu`, `tnu`] strip_assume_tac) >>
  `~u.vs_halted /\ allocas_from lo u /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp u)` by
    (fs[vars_pc_only_def, venom_state_component_equality, allocas_from_def,
        allocas_below_fmp_def] >> metis_tac[]) >>
  `!p. not_fresh_at sa p ==> p <> out` by
    simp[not_fresh_at_def, Abbr `out`] >>
  Cases_on `m = n2w h0`
  >- suspend "selected" >>
  suspend "next"
QED

Resume compile_group_entries_selected_origin[selected]:
  gvs[] >>
  qexistsl_tac [`checks`, `init`, `done`, `u`, `Gu`, `tnu`] >>
  simp[] >>
  rpt conj_tac
  >- (qpat_assum `!sa sb. _ ==> fresh_vars_wrt sb u`
        (qspecl_then [`sa`,`checks`] mp_tac) >> simp[Abbr `out`])
  >- (gen_tac >> strip_tac >>
      `p <> out` by (strip_tac >> gvs[]) >>
      qpat_assum `!p. p <> out ==> _` (qspec_then `p` mp_tac) >> simp[]) >>
  rpt strip_tac >>
  qpat_assum `!D fuel. _ ==> ptr_safe_run D lo fuel ctx fn PG G tn s`
    (qspecl_then [`D`, `fuel`] irule) >>
  `entry_prov fn u Gu = Gu /\ entry_taint_vars fn u tnu = tnu` by
    (irule selector_entry_ghost >>
     qpat_assum `!name bb. lookup_block name _ = _ ==> _`
       (qspec_then `u.vs_current_bb` ACCEPT_TAC)) >>
  simp[]
QED

Resume compile_group_entries_selected_origin[next]:
  fs[] >>
  `fresh_vars_wrt next_state u` by
    (qpat_assum `!sa sb. _ ==> fresh_vars_wrt sb u`
      (qspecl_then [`sa`,`next_state`] mp_tac) >> simp[Abbr `out`]) >>
  `eval_operand mid u = SOME m /\ op_taint tnu mid = {}` by
    (`s.vs_labels = u.vs_labels` by
       fs[vars_pc_only_def, venom_state_component_equality] >>
     Cases_on `mid` >> fs[eval_operand_def, op_taint_def] >>
     rename1 `lookup_var key s = SOME m` >>
     `key <> out` by
       (qspecl_then [`sa`,`s`,`Var key`,`m`,`key`,`sa.cs_next_var`]
          mp_tac fresh_vars_wrt_eval_operand >> simp[Abbr `out`, eval_operand_def]) >>
     qpat_assum `!p. p <> out ==> _` (qspec_then `key` mp_tac) >> simp[]) >>
  first_x_assum (qspecl_then [`mid`,`common`,`vars`,`off`,`next_state`,`sb`,`fn`,
    `m`,`u`,`ctx`,`PG`,`Gu`,`tnu`,`lo`] mp_tac) >>
  impl_tac >- (simp[] >> first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then [`sel`,`lbl`,`mincd`,`k`] mp_tac) >> simp[] >>
  disch_then (qx_choosel_then [`checks'`,`init'`,`done'`,`t`,`G'`,`tn'`]
    strip_assume_tac) >>
  `sa.cs_next_var < checks'.cs_next_var` by
    metis_tac[arithmeticTheory.LESS_TRANS] >>
  qexistsl_tac [`checks'`,`init'`,`done'`,`t`,`G'`,`tn'`] >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s,G,tn) [] (OK t,G',tn')` by metis_tac[gas_origin_ptr_path_append, APPEND] >>
  `vars_pc_only s t` by metis_tac[vars_pc_only_trans] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> `not_fresh_at next_state p` by
       fs[not_fresh_at_def] >> metis_tac[]) >>
  rpt strip_tac >> first_x_assum irule >>
  `entry_prov fn u Gu = Gu /\ entry_taint_vars fn u tnu = tnu` by
    (irule selector_entry_ghost >>
     qpat_assum `!name bb. lookup_block name _ = _ ==> _`
       (qspec_then `u.vs_current_bb` ACCEPT_TAC)) >>
  simp[] >>
  Cases_on `lookup_block u.vs_current_bb fn.fn_blocks`
  >- (Cases_on `fuel` >> simp[Once ptr_safe_blocks_def]) >>
  mp_tac (Q.INST [`s` |-> `u`, `G` |-> `Gu`, `tn` |-> `tnu`, `bb` |-> `x`]
    (SPEC_ALL ptr_safe_blocks_from_phi_free_run)) >>
  impl_tac >- (simp[] >>
    qpat_assum `!name bb. lookup_block name _ = _ ==> _`
      (qspecl_then [`u.vs_current_bb`,`x`] mp_tac) >> simp[]) >>
  disch_then (qspec_then `fuel` ACCEPT_TAC)
QED

Finalise compile_group_entries_selected_origin

Theorem compile_group_entries_missed_origin:
  !entries mid common vars off sa sb fn m s ctx PG G tn lo.
    compile_group_entries mid entries common vars off sa = ((),sb) /\
    fn_has_code sa sb fn /\
    EVERY (\(_,name,_,_). ~internal_label_ok name) entries /\
    (!name bb. lookup_block name fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
    FIND (\(n,_,_,_). m = n2w n) entries = NONE /\
    fresh_vars_wrt sa s /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    eval_operand mid s = SOME m /\ op_taint tn mid = {} /\
    allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
    ?t G' tn'.
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
        (s,G,tn) [] (OK t,G',tn')) /\
      vars_pc_only s t /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\ fresh_vars_wrt sb t /\
      eval_operand mid t = SOME m /\ op_taint tn' mid = {} /\
      tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
      tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
      (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
        FLOOKUP G' p = FLOOKUP G p /\ op_taint tn' (Var p) = op_taint tn (Var p)) /\
      (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' t) ==>
        !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  Induct
  >- (simp[compile_group_entries_def, comp_return_def, FIND_thm] >>
      rpt gen_tac >> strip_tac >> qexistsl_tac [`s`, `G`, `tn`] >>
      simp[gas_origin_ptr_path_rules, vars_pc_only_refl]) >>
  qx_gen_tac `group_entry` >> PairCases_on `group_entry` >>
  rpt gen_tac >> simp[EVERY_DEF, FIND_thm] >> strip_tac >>
  `m <> n2w group_entry0` by (strip_tac >> fs[]) >>
  drule_all compile_group_entries_cons_layout >>
  disch_then (qx_choosel_then [`next`,`next_state`,`checks`,`init`,`done`,`bb`]
    strip_assume_tac) >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  mp_tac (Q.INST [`func` |-> `fn`, `s` |-> `s`, `G` |-> `G`, `tn` |-> `tn`,
     `out` |-> `out`, `mid` |-> `mid`, `ctx` |-> `ctx`, `lo` |-> `lo`,
     `PG` |-> `PG`, `sel` |-> `group_entry0`, `yes` |-> `group_entry1`,
     `no` |-> `next`, `id` |-> `sa.cs_next_id`, `id'` |-> `sa.cs_next_id + 1`,
     `bb` |-> `bb`, `m` |-> `m`] grouped_comparison_origin_path) >>
  impl_tac >- fs[Abbr `out`] >>
  disch_then (qx_choosel_then [`u`, `Gu`, `tnu`] strip_assume_tac) >>
  fs[] >> suspend "walk_tail"
QED

Resume compile_group_entries_missed_origin[walk_tail]:
  `~u.vs_halted /\ allocas_from lo u /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp u)` by
    (fs[vars_pc_only_def, venom_state_component_equality, allocas_from_def,
        allocas_below_fmp_def] >> metis_tac[]) >>
  `!p. not_fresh_at sa p ==> p <> out` by
    simp[not_fresh_at_def, Abbr `out`] >>
  `fresh_vars_wrt next_state u` by
    (qpat_assum `!sa sb. _ ==> fresh_vars_wrt sb u`
      (qspecl_then [`sa`,`next_state`] mp_tac) >> simp[Abbr `out`]) >>
  `eval_operand mid u = SOME m /\ op_taint tnu mid = {}` by
    (`s.vs_labels = u.vs_labels` by
       fs[vars_pc_only_def, venom_state_component_equality] >>
     Cases_on `mid` >> fs[eval_operand_def, op_taint_def] >>
     rename1 `lookup_var key s = SOME m` >>
     `key <> out` by
       (qspecl_then [`sa`,`s`,`Var key`,`m`,`key`,`sa.cs_next_var`]
          mp_tac fresh_vars_wrt_eval_operand >> simp[Abbr `out`, eval_operand_def]) >>
     qpat_assum `!p. p <> out ==> _` (qspec_then `key` mp_tac) >> simp[]) >>
  first_x_assum (qspecl_then [`mid`,`common`,`vars`,`off`,`next_state`,`sb`,`fn`,
    `m`,`u`,`ctx`,`PG`,`Gu`,`tnu`,`lo`] mp_tac) >>
  impl_tac >- (simp[] >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`t`,`G'`,`tn'`] strip_assume_tac) >>
  qexistsl_tac [`t`,`G'`,`tn'`] >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s,G,tn) [] (OK t,G',tn')` by metis_tac[gas_origin_ptr_path_append, APPEND] >>
  `vars_pc_only s t` by metis_tac[vars_pc_only_trans] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> `not_fresh_at next_state p` by
       fs[not_fresh_at_def] >> metis_tac[]) >>
  rpt strip_tac >> first_x_assum irule >>
  `entry_prov fn u Gu = Gu /\ entry_taint_vars fn u tnu = tnu` by
    (irule selector_entry_ghost >>
     qpat_assum `!name bb. lookup_block name _ = _ ==> _`
       (qspec_then `u.vs_current_bb` ACCEPT_TAC)) >>
  simp[] >>
  Cases_on `lookup_block u.vs_current_bb fn.fn_blocks`
  >- (Cases_on `fuel` >> simp[Once ptr_safe_blocks_def]) >>
  mp_tac (Q.INST [`s` |-> `u`, `G` |-> `Gu`, `tn` |-> `tnu`, `bb` |-> `x`]
    (SPEC_ALL ptr_safe_blocks_from_phi_free_run)) >>
  impl_tac >- (simp[] >>
    qpat_assum `!name bb. lookup_block name _ = _ ==> _`
      (qspecl_then [`u.vs_current_bb`,`x`] mp_tac) >> simp[]) >>
  disch_then (qspec_then `fuel` ACCEPT_TAC)
QED

Finalise compile_group_entries_missed_origin
