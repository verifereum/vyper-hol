(* Allocation and selector execution through grouped dispatch. *)
Theory groupedDispatchPath
Ancestors
  groupedAllocatorStep groupedEntryResources groupedInternalLabels
  groupedSelectorPath groupedEntryCounters groupedKeywordAllocas groupedKeywordDecode
  exprLoweringProps ptrDiscipline fragGasOriginPtr moduleLoweringProps
  selectedAcceptedFold loweringShapeDefs venomState words list entryPrefixPtr
  entryDispatchPtr fragExec compileEnv moduleLowering bodyPtrDefs exprSimWordBuiltins
  defaultEntryPrefix fragGasOriginPtrLoop allocaFrontierBound allocaBudgetProps
  venomMemDefs loweringStateRelDefs venomInst venomExecSemantics
  gasShadowState gasShadow gasShadowRuntimeDispatch gasShadowModuleArgs gasShadowModuleDefs

Theorem grouped_registration_vars_pc[local]:
  vars_pc_only s t ==>
  t.vs_initial_fmp = s.vs_initial_fmp /\
  t.vs_alloca_next = s.vs_alloca_next /\
  pending_alloca_size fn t = pending_alloca_size fn s /\
  (allocas_below_fmp t <=> allocas_below_fmp s)
Proof
  simp[vars_pc_only_def, venom_state_component_equality,
       pending_alloca_size_def, allocas_below_fmp_def]
QED

Theorem grouped_default_group_missed_origin:
  compile_create_kwarg_allocas common.ec_env specs sa = (vars,sc) /\
  compile_group_entries (Var mid) entries common vars off sc = ((),sd) /\
  fn_has_code sa sc fn /\ fn_has_code sc sd fn /\
  EVERY (\(_,name,_,_). ~internal_label_ok name) entries /\
  (!name bb. lookup_block name fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  FIND (\(n,_,_,_). m = n2w n) entries = NONE /\
  selected_registration_resources ctx fn site lo sa s /\
  fn_inst_ids_distinct fn /\
  EVERY (\(_,ty,_). type_memory_bytes common.ec_env ty < dimword (:256)) specs /\
  unit_alloca_budget ctx < dimword (:256) /\
  not_fresh_at sa mid /\ eval_operand (Var mid) s = SOME m /\
  op_taint tn (Var mid) = {} /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp) ==>
  ?t G' tn'.
    selected_registration_resources ctx fn site lo sd t /\
    selected_registration_frame s tn t tn' /\ t.vs_memory = s.vs_memory /\
    not_fresh_at sd mid /\ eval_operand (Var mid) t = SOME m /\
    op_taint tn' (Var mid) = {} /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t /\
      t.vs_alloca_next + pending_alloca_size fn t <= w2n t.vs_initial_fmp) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  drule_all grouped_dispatch_allocas >>
  disch_then (qspecl_then [`PG`,`G`,`tn`]
    (qx_choosel_then [`u`,`Gu`,`tnu`] strip_assume_tac)) >>
  `ci_mono sa sc /\ ci_mono sc sd` by
    metis_tac[compile_create_kwarg_allocas_mono, compile_group_entries_ci_mono,
              pairTheory.SND] >>
  `eval_operand (Var mid) u = SOME m /\ op_taint tnu (Var mid) = {}` by
    (first_x_assum (qspec_then `mid` mp_tac) >> fs[eval_operand_def]) >>
  `fresh_vars_wrt sc u /\ ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
   u.vs_inst_idx = LENGTH sc.cs_current_insts /\ allocas_from lo u` by
    fs[selected_registration_resources_def] >>
  mp_tac (Q.SPECL [`entries`,`Var mid`,`common`,`vars`,`off`,`sc`,`sd`,
    `fn`,`m`,`u`,`ctx`,`PG`,`Gu`,`tnu`,`lo`]
      compile_group_entries_missed_origin) >>
  impl_tac >- (asm_rewrite_tac[] >> strip_tac >> res_tac) >>
  disch_then strip_assume_tac >>
  rename1 `vars_pc_only u miss` >>
  rename1 `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (u,Gu,tnu) [] (OK miss,Gmiss,tnmiss)` >>
  `selected_registration_resources ctx fn site lo sd miss` by
    (irule grouped_entry_resources_vars_pc >> asm_rewrite_tac[] >>
     qexistsl_tac [`u`,`sc`] >> fs[ci_mono_def]) >>
  `selected_registration_frame u tnu miss tnmiss /\ miss.vs_memory = u.vs_memory` by
    metis_tac[grouped_entry_frame_vars_pc] >>
  qexistsl_tac [`miss`,`Gmiss`,`tnmiss`] >> asm_rewrite_tac[] >>
  conj_tac >- fs[selected_registration_frame_def] >>
  conj_tac >-
    metis_tac[ci_mono_def, not_fresh_at_mono] >>
  conj_tac >-
    metis_tac[grouped_registration_vars_pc] >>
  conj_tac >-
    metis_tac[gas_origin_ptr_path_append, listTheory.APPEND_NIL] >>
  metis_tac[]
QED

Theorem grouped_single_group_missed_origin[local]:
  compile_selector_checks (Var mid) [(sel,lbl)] sa = ((),sb) /\
  fn_has_code sa sb fn /\
  (!name bb. lookup_block name fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  m <> n2w sel /\ selected_registration_resources ctx fn site lo sa s /\
  not_fresh_at sa mid /\ eval_operand (Var mid) s = SOME m /\
  op_taint tn (Var mid) = {} /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp) ==>
  ?t G' tn'.
    selected_registration_resources ctx fn site lo sb t /\
    selected_registration_frame s tn t tn' /\ t.vs_memory = s.vs_memory /\
    not_fresh_at sb mid /\ eval_operand (Var mid) t = SOME m /\
    op_taint tn' (Var mid) = {} /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t /\
      t.vs_alloca_next + pending_alloca_size fn t <= w2n t.vs_initial_fmp) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  `ci_mono sa sb` by metis_tac[compile_selector_checks_ci_mono, pairTheory.SND] >>
  `fresh_vars_wrt sa s /\ ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
   s.vs_inst_idx = LENGTH sa.cs_current_insts /\ allocas_from lo s` by
    fs[selected_registration_resources_def] >>
  `?bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
        phi_prefix_length bb.bb_instructions = 0` by
    (fs[fn_has_code_def] >> metis_tac[]) >>
  qpat_assum `compile_selector_checks _ _ _ = _`
    (mp_tac o MATCH_MP (Q.SPECL [`[(sel,lbl)]`,`Var mid`,`sa`,`sb`]
      compile_selector_checks_ptr_endpoint_frame)) >>
  disch_then (qspecl_then [`ctx`,`fn`,`s`,`m`,`lo`,`PG`,`G`,`tn`] mp_tac) >>
  impl_tac >- (asm_simp_tac (srw_ss()) [selector_hit_def] >> strip_tac >> res_tac) >>
  asm_simp_tac (srw_ss()) [selector_hit_def] >> disch_then strip_assume_tac >>
  rename1 `vars_pc_only s miss` >>
  rename1 `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s,G,tn) [] (OK miss,Gmiss,tnmiss)` >>
  `selected_registration_resources ctx fn site lo sb miss` by
    (irule grouped_entry_resources_vars_pc >> asm_rewrite_tac[] >>
     qexistsl_tac [`s`,`sa`] >> fs[ci_mono_def]) >>
  qexistsl_tac [`miss`,`Gmiss`,`tnmiss`] >> asm_rewrite_tac[] >>
  conj_tac >- metis_tac[grouped_entry_frame_vars_pc] >>
  conj_tac >- metis_tac[grouped_entry_frame_vars_pc] >>
  conj_tac >- metis_tac[ci_mono_def, not_fresh_at_mono] >>
  metis_tac[grouped_registration_vars_pc]
QED

Theorem compile_external_groups_missed_origin:
  !groups m mid sa sb jobs s G tn.
    compile_external_groups (Var mid) groups sa = (jobs,sb) /\
    fn_has_code sa sb fn /\
    EVERY group_entry_labels_ok groups /\
    EVERY (\group. case group of
      ExternalSingle (sel,lbl,tz) pkg => m <> n2w sel
    | ExternalDefaults common entries specs off =>
        FIND (\(sel,_,_,_). m = n2w sel) entries = NONE /\
        EVERY (\(_,ty,_). type_memory_bytes common.ec_env ty < dimword (:256))
          specs) groups /\
    (!name bb. lookup_block name fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
    selected_registration_resources ctx fn site lo sa s /\
    fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\
    not_fresh_at sa mid /\ eval_operand (Var mid) s = SOME m /\
    op_taint tn (Var mid) = {} /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
      s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp) ==>
    ?t G' tn'.
      selected_registration_resources ctx fn site lo sb t /\
      selected_registration_frame s tn t tn' /\ t.vs_memory = s.vs_memory /\
      not_fresh_at sb mid /\ eval_operand (Var mid) t = SOME m /\
      op_taint tn' (Var mid) = {} /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t /\
        t.vs_alloca_next + pending_alloca_size fn t <= w2n t.vs_initial_fmp) /\
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
        (s,G,tn) [] (OK t,G',tn')) /\
      (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' t) ==>
        !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  Induct
  >- (simp[compile_external_groups_def, comp_return_def] >>
      rpt strip_tac >> qexistsl_tac [`s`,`G`,`tn`] >>
      `~s.vs_halted` by fs[selected_registration_resources_def] >>
      asm_rewrite_tac[] >> simp[selected_registration_frame_def, gas_origin_ptr_path_rules]) >>
  (Cases >|
   [rename1 `ExternalSingle selector package` >> PairCases_on `selector` >>
      rpt gen_tac >> simp_tac (srw_ss()) [EVERY_DEF] >> strip_tac >>
      drule_all compile_external_single_cons_layout >> strip_tac >>
      drule_all grouped_single_group_missed_origin >>
      disch_then (qspecl_then [`PG`,`G`] strip_assume_tac),
    rpt gen_tac >> simp_tac (srw_ss()) [EVERY_DEF, group_entry_labels_ok_def] >>
      strip_tac >>
      rename1 `compile_external_groups (Var mid)
        (ExternalDefaults common entries specs off::groups) sa = _` >>
      `EVERY group_entry_labels_ok (ExternalDefaults common entries specs off::groups)` by
        asm_rewrite_tac[EVERY_DEF, group_entry_labels_ok_def] >>
      drule_all compile_external_defaults_cons_layout >> strip_tac >>
      drule_all grouped_default_group_missed_origin >>
      disch_then (qspecl_then [`PG`,`G`] strip_assume_tac)]) >>
  (rename1 `compile_external_groups (Var mid) groups ss = (rest,sb)` >>
  rename1 `selected_registration_resources ctx fn site lo ss u` >>
  rename1 `selected_registration_frame s tn u tnu` >>
  rename1 `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s,G,tn) [] (OK u,Gu,tnu)` >>
  qpat_assum `!m mid sa sb jobs s G tn. _`
    (qspecl_then [`m`,`mid`,`ss`,`sb`,`rest`,`u`,`Gu`,`tnu`] mp_tac) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then strip_assume_tac >>
  rename1 `selected_registration_frame u tnu v tnv` >>
  rename1 `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (u,Gu,tnu) [] (OK v,Gv,tnv)` >>
  qexistsl_tac [`v`,`Gv`,`tnv`] >> asm_rewrite_tac[] >>
  conj_tac >- fs[selected_registration_frame_def] >>
  conj_tac >- metis_tac[gas_origin_ptr_path_append, listTheory.APPEND_NIL] >>
  metis_tac[])
QED

Theorem grouped_default_group_selected_origin_with_frame:
  compile_create_kwarg_allocas common.ec_env specs sa = (vars,sc) /\
  compile_group_entries (Var mid) entries common vars off sc = ((),sd) /\
  fn_has_code sa sc fn /\ fn_has_code sc sd fn /\
  EVERY (\(_,name,_,_). ~internal_label_ok name) entries /\
  (!name bb. lookup_block name fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  FIND (\(n,_,_,_). m = n2w n) entries = SOME (sel,lbl,mincd,k) /\
  selected_registration_resources ctx fn site lo sa s /\
  fn_inst_ids_distinct fn /\
  EVERY (\(_,ty,_). type_memory_bytes common.ec_env ty < dimword (:256)) specs /\
  unit_alloca_budget ctx < dimword (:256) /\
  not_fresh_at sa mid /\ eval_operand (Var mid) s = SOME m /\
  op_taint tn (Var mid) = {} /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp) ==>
  ?checks init done t G' tn'.
    checks.cs_current_bb = lbl /\ checks.cs_current_insts = [] /\
    compile_entry_checks mincd common.ec_payable checks = ((),init) /\
    fn_has_code checks init fn /\
    compile_entry_point_kwargs common.ec_env vars off k common.ec_common_label init =
      ((),done) /\ fn_has_code init done fn /\
    cs_extends done sd /\ ci_mono done sd /\
    (!sha shb shfn. gas_shadow_state sc sha /\
      compile_group_entries (Var mid) entries
        (common with ec_body := MAP gas_shadow_stmt common.ec_body)
        (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) vars) off sha = ((),shb) /\
      fn_has_code sha shb shfn ==>
      ?shinit shdone.
        compile_entry_point_kwargs common.ec_env
          (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) vars) off k
          common.ec_common_label shinit = ((),shdone) /\
        fn_has_code shinit shdone shfn /\ gas_shadow_state init shinit) /\
    selected_registration_resources ctx fn site lo checks t /\
    selected_registration_frame s tn t tn' /\ t.vs_memory = s.vs_memory /\
    (!name op ty e. MEM (name,op,ty,e) vars ==>
      ?id q base.
        op = Var q /\ not_fresh_at checks q /\ lookup_var q t = SOME (n2w base) /\
        MEM (mk_inst id ALLOCA [Lit (n2w (type_memory_bytes common.ec_env ty))] [q])
          (fn_insts fn) /\
        FLOOKUP t.vs_allocas id = SOME (base,type_memory_bytes common.ec_env ty) /\
        id < checks.cs_next_id /\
        base + type_memory_bytes common.ec_env ty < dimword (:256) /\
        ptr_covers G' tn' q t (type_memory_bytes common.ec_env ty)) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t /\
      t.vs_alloca_next + pending_alloca_size fn t <= w2n t.vs_initial_fmp) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    (!D. (!fuel. ptr_safe_blocks D lo fuel ctx fn PG G' tn' t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  drule_all grouped_dispatch_allocas >>
  disch_then (qspecl_then [`PG`,`G`,`tn`]
    (qx_choosel_then [`u`,`Gu`,`tnu`] strip_assume_tac)) >>
  `eval_operand (Var mid) u = SOME m /\ op_taint tnu (Var mid) = {}` by
    (first_x_assum (qspec_then `mid` mp_tac) >> fs[eval_operand_def]) >>
  `fresh_vars_wrt sc u /\ ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
   u.vs_inst_idx = LENGTH sc.cs_current_insts /\ allocas_from lo u` by
    fs[selected_registration_resources_def] >>
  mp_tac (Q.SPECL [`entries`,`Var mid`,`common`,`vars`,`off`,`sc`,`sd`,
    `fn`,`m`,`u`,`ctx`,`PG`,`Gu`,`tnu`,`lo`]
      compile_group_entries_selected_origin_with_frame) >>
  impl_tac >- (asm_rewrite_tac[] >> strip_tac >> res_tac) >>
  disch_then (qspecl_then [`sel`,`lbl`,`mincd`,`k`] mp_tac) >>
  asm_rewrite_tac[] >> disch_then strip_assume_tac >>
  rename1 `compile_entry_checks mincd common.ec_payable checks = ((),init)` >>
  rename1 `compile_entry_point_kwargs _ _ _ _ _ init = ((),done)` >>
  rename1 `vars_pc_only u hit` >>
  rename1 `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (u,Gu,tnu) [] (OK hit,Ghit,tnhit)` >>
  `selected_registration_resources ctx fn site lo checks hit` by
    (irule grouped_entry_resources_vars_pc >> asm_simp_tac (srw_ss()) [] >>
     qexistsl_tac [`u`,`sc`] >> asm_rewrite_tac[]) >>
  `selected_registration_frame u tnu hit tnhit /\ hit.vs_memory = u.vs_memory` by
    metis_tac[grouped_entry_frame_vars_pc] >>
  `hit.vs_allocas = u.vs_allocas` by
    fs[vars_pc_only_def, venom_state_component_equality] >>
  qexistsl_tac [`checks`,`init`,`done`,`hit`,`Ghit`,`tnhit`] >>
  asm_rewrite_tac[] >>
  conj_tac >- fs[selected_registration_frame_def] >>
  conj_tac >- suspend "owners" >>
  conj_tac >- metis_tac[grouped_registration_vars_pc] >>
  conj_tac >- metis_tac[gas_origin_ptr_path_append, listTheory.APPEND_NIL] >>
  metis_tac[]
QED

Resume grouped_default_group_selected_origin_with_frame[owners]:
  qx_genl_tac [`name`,`op`,`ty`,`e`] >> strip_tac >>
  qpat_assum `!name op ty e. MEM _ vars ==> _`
    (drule_then strip_assume_tac) >>
  qmatch_asmsub_rename_tac `lookup_var qv u = SOME (n2w addr)` >>
  qmatch_asmsub_rename_tac `FLOOKUP u.vs_allocas alloc_id = SOME (addr,_)` >>
  qpat_assum `!p. not_fresh_at sc p ==> lookup_var p hit = _ /\ _`
    (drule_then strip_assume_tac) >>
  qexistsl_tac [`alloc_id`,`qv`,`addr`] >> asm_rewrite_tac[] >>
  rpt conj_tac
  >- metis_tac[not_fresh_at_mono, arithmeticTheory.LESS_IMP_LESS_OR_EQ]
  >- fs[selected_registration_resources_def] >>
  fs[ptr_covers_def]
QED

Finalise grouped_default_group_selected_origin_with_frame


val shadow_group = ``\group. case group of
  ExternalSingle selector package =>
    ExternalSingle selector (gas_shadow_external_package package)
| ExternalDefaults common entries specs off =>
    ExternalDefaults (common with ec_body := MAP gas_shadow_stmt common.ec_body)
      entries (MAP (\(n,ty,e). (n,ty,gas_shadow_expr e)) specs) off``;

Theorem compile_external_groups_selected_default_origin_with_frame:
  compile_external_groups (Var mid)
    (pref ++ ExternalDefaults common entries specs off::rest) sa = (jobs,sb) /\
  fn_has_code sa sb fn /\
  EVERY group_entry_labels_ok (pref ++ ExternalDefaults common entries specs off::rest) /\
  EVERY (\group. case group of
    ExternalSingle (sel,lbl,tz) pkg => m <> n2w sel
  | ExternalDefaults comp ens sp _ =>
      FIND (\(sel,_,_,_). m = n2w sel) ens = NONE /\
      EVERY (\(_,ty,_). type_memory_bytes comp.ec_env ty < dimword (:256)) sp) pref /\
  FIND (\(n,_,_,_). m = n2w n) entries = SOME (sel,lbl,mincd,k) /\
  EVERY (\(_,ty,_). type_memory_bytes common.ec_env ty < dimword (:256)) specs /\
  (!name bb. lookup_block name fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  selected_registration_resources ctx fn site lo sa s /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\
  not_fresh_at sa mid /\ eval_operand (Var mid) s = SOME m /\
  op_taint tn (Var mid) = {} /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp) ==>
  ?vars checks init done t G' tn'.
    MEM (ExternalCommonJob common vars) jobs /\
    (?alloc_start alloc_end.
      compile_create_kwarg_allocas common.ec_env specs alloc_start = (vars,alloc_end)) /\
    checks.cs_current_bb = lbl /\ checks.cs_current_insts = [] /\
    compile_entry_checks mincd common.ec_payable checks = ((),init) /\
    fn_has_code checks init fn /\
    compile_entry_point_kwargs common.ec_env vars off k common.ec_common_label init =
      ((),done) /\ fn_has_code init done fn /\
    cs_extends done sb /\ ci_mono done sb /\
    (!sha shb shfn shjobs. gas_shadow_state sa sha /\
      compile_external_groups (Var mid)
        (MAP ^shadow_group (pref ++ ExternalDefaults common entries specs off::rest))
        sha = (shjobs,shb) /\ fn_has_code sha shb shfn /\
      EVERY group_entry_labels_ok
        (MAP ^shadow_group (pref ++ ExternalDefaults common entries specs off::rest)) ==>
      ?shinit shdone.
        compile_entry_point_kwargs common.ec_env
          (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) vars) off k
          common.ec_common_label shinit = ((),shdone) /\
        fn_has_code shinit shdone shfn /\ gas_shadow_state init shinit) /\
    selected_registration_resources ctx fn site lo checks t /\
    selected_registration_frame s tn t tn' /\ t.vs_memory = s.vs_memory /\
    (!name op ty e. MEM (name,op,ty,e) vars ==>
      ?id q base.
        op = Var q /\ not_fresh_at checks q /\ lookup_var q t = SOME (n2w base) /\
        MEM (mk_inst id ALLOCA [Lit (n2w (type_memory_bytes common.ec_env ty))] [q])
          (fn_insts fn) /\
        FLOOKUP t.vs_allocas id = SOME (base,type_memory_bytes common.ec_env ty) /\
        id < checks.cs_next_id /\
        base + type_memory_bytes common.ec_env ty < dimword (:256) /\
        ptr_covers G' tn' q t (type_memory_bytes common.ec_env ty)) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t /\
      t.vs_alloca_next + pending_alloca_size fn t <= w2n t.vs_initial_fmp) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    (!D. (!fuel. ptr_safe_blocks D lo fuel ctx fn PG G' tn' t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> drule_all compile_external_groups_append_layout >> strip_tac >>
  fs[EVERY_APPEND] >>
  qmatch_asmsub_rename_tac `compile_external_groups (Var mid) pref sa = (prefix_jobs,sc)` >>
  mp_tac (Q.INST [`ctx` |-> `ctx`, `fn` |-> `fn`, `site` |-> `site`,
                 `lo` |-> `lo`, `PG` |-> `PG`]
    (Q.SPECL [`pref`,`m`,`mid`,`sa`,`sc`,`prefix_jobs`,`s`,`G`,`tn`]
      compile_external_groups_missed_origin)) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`u`,`Gu`,`tnu`] strip_assume_tac) >>
  `EVERY group_entry_labels_ok (ExternalDefaults common entries specs off::rest)` by
    asm_rewrite_tac[EVERY_DEF] >>
  drule_all compile_external_defaults_cons_layout >> strip_tac >>
  rename1 `compile_create_kwarg_allocas common.ec_env specs sc = (vars,alloc_end)` >>
  `EVERY (\(_,name,_,_). ~internal_label_ok name) entries` by
    fs[group_entry_labels_ok_def] >>
  drule_all grouped_default_group_selected_origin_with_frame >>
  disch_then (qspecl_then [`PG`,`Gu`] strip_assume_tac) >>
  rename1 `compile_entry_point_kwargs common.ec_env vars off k common.ec_common_label init = ((),done)` >>
  `cs_extends sd sb` by
    (irule compile_external_groups_extends >> goal_assum (drule_at Any) >>
     fs[group_entry_labels_ok_def]) >>
  `cs_extends done sb /\ ci_mono done sb` by
    metis_tac[cs_extends_trans, ci_mono_trans, compile_external_groups_ci_mono, pairTheory.SND] >>
  qexistsl_tac [`vars`,`checks`,`init`,`done`,`t`,`G'`,`tn'`] >>
  asm_rewrite_tac[MEM_APPEND, MEM] >>
  conj_tac >- (goal_assum drule >> first_assum ACCEPT_TAC) >>
  conj_tac >- suspend "shadow_entry" >>
  conj_tac >- fs[selected_registration_frame_def] >>
  conj_tac >- metis_tac[gas_origin_ptr_path_append, listTheory.APPEND_NIL] >>
  metis_tac[]
QED

Resume compile_external_groups_selected_default_origin_with_frame[shadow_entry]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_at (Pat `compile_external_groups _ _ sha = (shjobs,shb)`)
    compile_external_groups_append_layout >>
  disch_then (qspec_then `shfn` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (qx_choosel_then [`shpref`,`shtail`,`shsc`]
    (map_every assume_tac o CONJUNCTS)) >>
  `gas_shadow_state sc shsc` by
    metis_tac[pairTheory.SND,
      Q.SPECL [`pref`,`Var mid`,`sa`,`sha`] gas_shadow_compile_external_groups] >>
  drule_at (Pat `compile_external_groups _ _ shsc = (shtail,shb)`)
    compile_external_defaults_cons_layout >>
  disch_then (qspec_then `shfn` mp_tac) >>
  impl_tac >- asm_rewrite_tac[EVERY_DEF] >>
  disch_then (qx_choosel_then [`shvars`,`shalloc`,`shnext`,`shrest`]
    (map_every assume_tac o CONJUNCTS)) >>
  fs[external_common_accfupds, combinTheory.K_THM] >>
  `shvars = MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) vars /\
    gas_shadow_state alloc_end shalloc` by
    (qpat_assum `compile_create_kwarg_allocas common.ec_env specs sc = (vars,alloc_end)`
       (fn alloc =>
         let
           val (alloc_action, _) = dest_eq (concl alloc)
           val [env, specs, before_state] = #2 (strip_comb alloc_action)
         in
           mp_tac (ISPECL [specs,env,before_state,Term `shsc:compile_state`]
             gas_shadow_compile_create_kwarg_allocas)
         end) >>
     asm_rewrite_tac[pairTheory.FST, pairTheory.SND]) >>
  qpat_x_assum `shvars = _` SUBST_ALL_TAC >>
  qpat_assum `!sha shb shfn. gas_shadow_state alloc_end sha /\ _ ==> _`
    (qspecl_then [`shalloc`,`shnext`,`shfn`] mp_tac) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then ACCEPT_TAC
QED

Finalise compile_external_groups_selected_default_origin_with_frame

Theorem compile_external_groups_selected_default_origin:
  compile_external_groups (Var mid)
    (pref ++ ExternalDefaults common entries specs off::rest) sa = (jobs,sb) /\
  fn_has_code sa sb fn /\
  EVERY group_entry_labels_ok (pref ++ ExternalDefaults common entries specs off::rest) /\
  EVERY (\group. case group of
    ExternalSingle (sel,lbl,tz) pkg => m <> n2w sel
  | ExternalDefaults comp ens sp _ =>
      FIND (\(sel,_,_,_). m = n2w sel) ens = NONE /\
      EVERY (\(_,ty,_). type_memory_bytes comp.ec_env ty < dimword (:256)) sp) pref /\
  FIND (\(n,_,_,_). m = n2w n) entries = SOME (sel,lbl,mincd,k) /\
  EVERY (\(_,ty,_). type_memory_bytes common.ec_env ty < dimword (:256)) specs /\
  (!name bb. lookup_block name fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  selected_registration_resources ctx fn site lo sa s /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\
  not_fresh_at sa mid /\ eval_operand (Var mid) s = SOME m /\
  op_taint tn (Var mid) = {} /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp) ==>
  ?vars checks init done t G' tn'.
    MEM (ExternalCommonJob common vars) jobs /\
    MAP (\(n,_,ty,e). (n,ty,e)) vars = specs /\
    checks.cs_current_bb = lbl /\ checks.cs_current_insts = [] /\
    compile_entry_checks mincd common.ec_payable checks = ((),init) /\
    fn_has_code checks init fn /\
    compile_entry_point_kwargs common.ec_env vars off k common.ec_common_label init =
      ((),done) /\ fn_has_code init done fn /\
    selected_registration_resources ctx fn site lo checks t /\
    selected_registration_frame s tn t tn' /\ t.vs_memory = s.vs_memory /\
    (!name op ty e. MEM (name,op,ty,e) vars ==>
      ?id q base.
        op = Var q /\ not_fresh_at checks q /\ lookup_var q t = SOME (n2w base) /\
        MEM (mk_inst id ALLOCA [Lit (n2w (type_memory_bytes common.ec_env ty))] [q])
          (fn_insts fn) /\
        FLOOKUP t.vs_allocas id = SOME (base,type_memory_bytes common.ec_env ty) /\
        id < checks.cs_next_id /\
        base + type_memory_bytes common.ec_env ty < dimword (:256) /\
        ptr_covers G' tn' q t (type_memory_bytes common.ec_env ty)) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t /\
      t.vs_alloca_next + pending_alloca_size fn t <= w2n t.vs_initial_fmp) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    (!D. (!fuel. ptr_safe_blocks D lo fuel ctx fn PG G' tn' t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> drule_all compile_external_groups_selected_default_origin_with_frame >>
  disch_then (qspecl_then [`PG`,`G`]
    (qx_choosel_then [`vars`,`checks`,`init`,`done`,`t`,`G'`,`tn'`] strip_assume_tac)) >>
  qexistsl_tac [`vars`,`checks`,`init`,`done`,`t`,`G'`,`tn'`] >> asm_rewrite_tac[] >>
  drule compile_create_kwarg_allocas_preserves_specs >> simp[]
QED


Theorem grouped_dispatch_long_prelude_with_frame:
  compile_group_dispatch_linear groups fallback st = (jobs,st') /\
  fn_has_code st st' fn /\ EVERY group_entry_labels_ok groups /\
  4 <= LENGTH s.vs_call_ctx.cc_calldata /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  selected_registration_resources ctx fn site lo st s /\ s.vs_allocas = FEMPTY /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp) ==>
  ?mid q r br t G' tn'.
    compile_external_groups (Var mid) groups q = (jobs,r) /\ fn_has_code q r fn /\
    ci_mono r st' /\ cs_extends r st' /\ lookup_block r.cs_current_bb fn.fn_blocks = SOME br /\
    get_instruction br (LENGTH r.cs_current_insts) =
      SOME (mk_inst r.cs_next_id JMP [Label fallback] []) /\
    (!other other_jobs other_end other_fn.
      compile_group_dispatch_linear other fallback st = (other_jobs,other_end) /\
      fn_has_code st other_end other_fn /\ EVERY group_entry_labels_ok other ==>
      ?rr. compile_external_groups (Var mid) other q = (other_jobs,rr) /\
        fn_has_code q rr other_fn) /\
    selected_registration_resources ctx fn site lo q t /\
    selected_registration_frame s tn t tn' /\ t.vs_memory = s.vs_memory /\
    not_fresh_at q mid /\ eval_operand (Var mid) t =
      SOME (calldata_method_id s.vs_call_ctx.cc_calldata) /\
    op_taint tn' (Var mid) = {} /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t /\
      t.vs_alloca_next + pending_alloca_size fn t <= w2n t.vs_initial_fmp) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> drule_all compile_group_dispatch_linear_layout_with_frame >> strip_tac >>
  `fresh_vars_wrt st s /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
   s.vs_inst_idx = LENGTH st.cs_current_insts /\ allocas_from lo s` by
    fs[selected_registration_resources_def] >>
  `(LENGTH s.vs_call_ctx.cc_calldata < 4 ==>
     !bb. lookup_block fallback fn.fn_blocks = SOME bb ==>
       phi_prefix_length bb.bb_instructions = 0)` by fs[arithmeticTheory.NOT_LESS] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by metis_tac[] >>
  drule_all dispatch_prelude_ptr_endpoint >>
  asm_rewrite_tac[] >>
  disch_then (qspecl_then [`tn`,`PG`,`G`] strip_assume_tac) >>
  `selected_registration_resources ctx fn site lo q t` by
    (irule grouped_entry_resources_vars_pc >>
     asm_rewrite_tac[] >> qexistsl_tac [`s`,`st`] >> asm_rewrite_tac[]) >>
  qexistsl_tac [`STRING #"%" (toString (st.cs_next_var + 4))`,
    `q`,`r`,`br`,`t`,`G'`,`tn'`] >>
  asm_rewrite_tac[] >>
  conj_tac >- metis_tac[grouped_entry_frame_vars_pc] >>
  conj_tac >- metis_tac[grouped_entry_frame_vars_pc] >>
  conj_tac >- metis_tac[fresh_vars_wrt_not_fresh_at, operand_11] >>
  metis_tac[grouped_registration_vars_pc]
QED

Theorem grouped_dispatch_long_prelude:
  compile_group_dispatch_linear groups fallback st = (jobs,st') /\
  fn_has_code st st' fn /\ EVERY group_entry_labels_ok groups /\
  4 <= LENGTH s.vs_call_ctx.cc_calldata /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  selected_registration_resources ctx fn site lo st s /\ s.vs_allocas = FEMPTY /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp) ==>
  ?mid q r br t G' tn'.
    compile_external_groups (Var mid) groups q = (jobs,r) /\ fn_has_code q r fn /\
    lookup_block r.cs_current_bb fn.fn_blocks = SOME br /\
    get_instruction br (LENGTH r.cs_current_insts) =
      SOME (mk_inst r.cs_next_id JMP [Label fallback] []) /\
    selected_registration_resources ctx fn site lo q t /\
    selected_registration_frame s tn t tn' /\ t.vs_memory = s.vs_memory /\
    not_fresh_at q mid /\ eval_operand (Var mid) t =
      SOME (calldata_method_id s.vs_call_ctx.cc_calldata) /\
    op_taint tn' (Var mid) = {} /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t /\
      t.vs_alloca_next + pending_alloca_size fn t <= w2n t.vs_initial_fmp) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> drule_all grouped_dispatch_long_prelude_with_frame >>
  disch_then (qspecl_then [`tn`,`PG`,`G`]
    (qx_choosel_then [`mid`,`q`,`r`,`br`,`t`,`G'`,`tn'`] strip_assume_tac)) >>
  qexistsl_tac [`mid`,`q`,`r`,`br`,`t`,`G'`,`tn'`] >> asm_rewrite_tac[]
QED

Theorem grouped_dispatch_short_prelude:
  compile_group_dispatch_linear groups fallback st = (jobs,st') /\
  fn_has_code st st' fn /\ EVERY group_entry_labels_ok groups /\
  LENGTH s.vs_call_ctx.cc_calldata < 4 /\
  (!bb. lookup_block fallback fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  fresh_vars_wrt st s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?q r t G' tn'.
    compile_external_groups (Var (STRING #"%" (toString (st.cs_next_var + 4))))
      groups q = (jobs,r) /\ fn_has_code q r fn /\ ci_mono q st' /\
    vars_pc_only s t /\ fresh_vars_wrt q t /\ ~t.vs_halted /\
    t.vs_current_bb = fallback /\ t.vs_inst_idx = 0 /\
    selected_registration_frame s tn t tn' /\ t.vs_memory = s.vs_memory /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    (!D. (!fuel. ptr_safe_blocks D lo fuel ctx fn PG G' tn' t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> drule_all compile_group_dispatch_linear_layout_with_frame >> strip_tac >>
  `~(4 <= LENGTH s.vs_call_ctx.cc_calldata)` by
    simp[arithmeticTheory.NOT_LESS_EQUAL] >>
  `LENGTH s.vs_call_ctx.cc_calldata < dimword (:256)` by
    fs[wordsTheory.dimword_def] >>
  `(LENGTH s.vs_call_ctx.cc_calldata < 4 ==>
     !bb. lookup_block fallback fn.fn_blocks = SOME bb ==>
       phi_prefix_length bb.bb_instructions = 0)` by metis_tac[] >>
  drule_all dispatch_prelude_ptr_endpoint >>
  asm_rewrite_tac[] >>
  disch_then (qspecl_then [`tn`,`PG`,`G`] strip_assume_tac) >>
  `ci_mono q st'` by
    metis_tac[ci_mono_trans, compile_external_groups_ci_mono, pairTheory.SND] >>
  qexistsl_tac [`q`,`r`,`t`,`G'`,`tn'`] >>
  asm_rewrite_tac[] >> metis_tac[grouped_entry_frame_vars_pc]
QED

Theorem grouped_default_checks_pass_origin:
  compile_entry_checks m pay sa = ((),sb) /\ fn_has_code sa sb fn /\
  selected_registration_resources ctx fn site lo sa s /\
  (pay \/ s.vs_call_ctx.cc_callvalue = 0w) /\
  (m <= 4 \/ m <= LENGTH s.vs_call_ctx.cc_calldata) /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp) ==>
  ?t G' tn'.
    selected_registration_resources ctx fn site lo sb t /\
    selected_registration_frame s tn t tn' /\ t.vs_memory = s.vs_memory /\
    t.vs_allocas = s.vs_allocas /\ tn'.t_mem = tn.t_mem /\
    (!p. not_fresh_at sa p ==> not_fresh_at sb p /\
      lookup_var p t = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p)) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t /\
      t.vs_alloca_next + pending_alloca_size fn t <= w2n t.vs_initial_fmp) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ci_mono sa sb` by metis_tac[compile_entry_checks_ci_mono, pairTheory.SND] >>
  `fresh_vars_wrt sa s /\ ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
   s.vs_inst_idx = LENGTH sa.cs_current_insts /\ allocas_from lo s` by
    fs[selected_registration_resources_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by metis_tac[] >>
  drule_all default_entry_checks_ptr_endpoint_frame >>
  disch_then (qspecl_then [`tn`,`PG`,`G`] strip_assume_tac) >>
  `selected_registration_resources ctx fn site lo sb u` by
    (irule grouped_entry_resources_vars_pc >> asm_rewrite_tac[] >>
     qexistsl_tac [`s`,`sa`] >> fs[ci_mono_def]) >>
  qexistsl_tac [`u`,`G'`,`tn'`] >> asm_rewrite_tac[] >>
  rpt conj_tac
  >- metis_tac[grouped_entry_frame_vars_pc]
  >- metis_tac[grouped_entry_frame_vars_pc]
  >- fs[vars_pc_only_def, venom_state_component_equality]
  >- metis_tac[ci_mono_def, not_fresh_at_mono] >>
  metis_tac[grouped_registration_vars_pc]
QED

Theorem grouped_dispatch_missed_fallback_origin:
  compile_group_dispatch_linear groups fallback sa = (jobs,sb) /\
  fn_has_code sa sb fn /\ EVERY group_entry_labels_ok groups /\
  EVERY (\group. case group of
    ExternalSingle (sel,lbl,tz) pkg =>
      calldata_method_id s.vs_call_ctx.cc_calldata <> n2w sel
  | ExternalDefaults common entries specs _ =>
      FIND (\(sel,_,_,_). calldata_method_id s.vs_call_ctx.cc_calldata = n2w sel)
        entries = NONE /\
      EVERY (\(_,ty,_). type_memory_bytes common.ec_env ty < dimword (:256)) specs)
    groups /\
  (!name bb. lookup_block name fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  lookup_block fallback fn.fn_blocks = SOME target /\
  4 <= LENGTH s.vs_call_ctx.cc_calldata /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  selected_registration_resources ctx fn site lo sa s /\ s.vs_allocas = FEMPTY /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp) ==>
  ?mid q r t G' tn'.
    compile_external_groups (Var mid) groups q = (jobs,r) /\ ci_mono r sb /\
    fresh_vars_wrt r t /\ ~t.vs_halted /\
    t.vs_current_bb = fallback /\ t.vs_inst_idx = 0 /\
    selected_registration_frame s tn t tn' /\ t.vs_memory = s.vs_memory /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\ allocas_from lo t /\
    lo <= t.vs_alloca_next /\
    (!id entry. FLOOKUP t.vs_allocas id = SOME entry ==> id < r.cs_next_id) /\
    (!inst w b n. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_operands = [Lit w] /\
      FLOOKUP t.vs_allocas inst.inst_id = SOME (b,n) ==> n = w2n w) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t /\
      t.vs_alloca_next + pending_alloca_size fn t <= w2n t.vs_initial_fmp) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> drule_all grouped_dispatch_long_prelude_with_frame >>
  disch_then (qspecl_then [`tn`,`PG`,`G`]
    (qx_choosel_then [`mid`,`q`,`r`,`br`,`u`,`Gu`,`tnu`] strip_assume_tac)) >>
  mp_tac (Q.INST [`ctx` |-> `ctx`, `fn` |-> `fn`, `site` |-> `site`,
                 `lo` |-> `lo`, `PG` |-> `PG`]
    (Q.SPECL [`groups`,`calldata_method_id s.vs_call_ctx.cc_calldata`,
      `mid`,`q`,`r`,`jobs`,`u`,`Gu`,`tnu`]
      compile_external_groups_missed_origin)) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`v`,`Gv`,`tnv`] strip_assume_tac) >>
  `phi_prefix_length target.bb_instructions = 0` by metis_tac[] >>
  `lookup_block v.vs_current_bb fn.fn_blocks = SOME br /\
   get_instruction br v.vs_inst_idx = SOME (mk_inst r.cs_next_id JMP [Label fallback] []) /\
   ~v.vs_halted /\ allocas_from lo v` by fs[selected_registration_resources_def] >>
  `(!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
     (v,Gv,tnv) [] (OK (jump_to fallback v),Gv,tnv))` by
    (rpt gen_tac >> irule jmp_origin_ptr_path >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  `entry_prov fn (jump_to fallback v) Gv = Gv /\
   entry_taint_vars fn (jump_to fallback v) tnv = tnv` by
    (Cases_on `target.bb_instructions` >>
     gvs[entry_prov_def, entry_taint_vars_def, jump_to_def, phis_prov_def,
         phis_taint_def, phi_prefix_length_def, AllCaseEqs()]) >>
  `!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG Gv tnv (jump_to fallback v)) ==>
       !fuel. ptr_safe_run D lo fuel ctx fn PG Gv tnv v` by
    (rpt strip_tac >>
     `!fuel. ptr_safe_blocks D lo fuel ctx fn PG Gv tnv (jump_to fallback v)` by
       (irule ptr_safe_blocks_from_phi_free_run >>
        simp[jump_to_def] >> qexists_tac `target` >> simp[]) >>
     irule ptr_safe_jump_exact_continuation >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  `~(jump_to fallback v).vs_halted /\
   (jump_to fallback v).vs_current_bb = fallback /\
   (jump_to fallback v).vs_inst_idx = 0` by simp[jump_to_def] >>
  `vars_pc_only v (jump_to fallback v)` by
    simp[vars_pc_only_jump_to, vars_pc_only_refl] >>
  `selected_registration_frame s tn (jump_to fallback v) tnv /\
   (jump_to fallback v).vs_memory = s.vs_memory` by
    fs[selected_registration_frame_def, jump_to_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp (jump_to fallback v) /\
    (jump_to fallback v).vs_alloca_next + pending_alloca_size fn (jump_to fallback v) <=
      w2n (jump_to fallback v).vs_initial_fmp` by metis_tac[grouped_registration_vars_pc] >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
     (s,G,tn) [] (OK (jump_to fallback v),Gv,tnv)` by
    metis_tac[gas_origin_ptr_path_append, listTheory.APPEND_NIL] >>
  qexistsl_tac [`mid`,`q`,`r`,`jump_to fallback v`,`Gv`,`tnv`] >>
  asm_rewrite_tac[] >>
  fs[selected_registration_resources_def, jump_to_def, fresh_vars_wrt_def,
     alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
     allocas_from_def, alloca_frontier_inv_def, remaining_alloca_budget_def] >>
  metis_tac[]
QED

Theorem compile_external_groups_selected_single_origin:
  compile_external_groups (Var mid)
    (pref ++ ExternalSingle (sel,lbl,mincd) pkg::rest) sa = (jobs,sb) /\
  fn_has_code sa sb fn /\
  EVERY group_entry_labels_ok (pref ++ ExternalSingle (sel,lbl,mincd) pkg::rest) /\
  EVERY (\group. case group of
    ExternalSingle (n,_,_) pack => m <> n2w n
  | ExternalDefaults common entries specs _ =>
      FIND (\(n,_,_,_). m = n2w n) entries = NONE /\
      EVERY (\(_,ty,_). type_memory_bytes common.ec_env ty < dimword (:256)) specs) pref /\
  m = n2w sel /\
  (!name bb. lookup_block name fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  selected_registration_resources ctx fn site lo sa s /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\
  not_fresh_at sa mid /\ eval_operand (Var mid) s = SOME m /\
  op_taint tn (Var mid) = {} /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp) ==>
  ?prefix_jobs sc sd t G' tn'.
    MEM (ExternalLegacyJob pkg) jobs /\
    compile_external_groups (Var mid) pref sa = (prefix_jobs,sc) /\
    compile_selector_checks (Var mid) [(sel,lbl)] sc = ((),sd) /\
    t.vs_current_bb = lbl /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    (!id entry. FLOOKUP t.vs_allocas id = SOME entry ==> id < sc.cs_next_id) /\
    (!inst w b n. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_operands = [Lit w] /\
      FLOOKUP t.vs_allocas inst.inst_id = SOME (b,n) ==> n = w2n w) /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\ fresh_vars_wrt sd t /\
    selected_registration_frame s tn t tn' /\ t.vs_memory = s.vs_memory /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t /\
      t.vs_alloca_next + pending_alloca_size fn t <= w2n t.vs_initial_fmp) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    (!D. (!fuel. ptr_safe_blocks D lo fuel ctx fn PG G' tn' t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> drule_all compile_external_groups_append_layout >> strip_tac >>
  full_simp_tac bool_ss [EVERY_APPEND, EVERY_DEF] >>
  qmatch_asmsub_rename_tac `compile_external_groups (Var mid) pref sa = (prefix_jobs,sc)` >>
  mp_tac (Q.INST [`ctx` |-> `ctx`, `fn` |-> `fn`, `site` |-> `site`,
                 `lo` |-> `lo`, `PG` |-> `PG`]
    (Q.SPECL [`pref`,`m`,`mid`,`sa`,`sc`,`prefix_jobs`,`s`,`G`,`tn`]
      compile_external_groups_missed_origin)) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`u`,`Gu`,`tnu`] strip_assume_tac) >>
  drule_all compile_external_single_cons_layout >> strip_tac >>
  rename1 `compile_selector_checks (Var mid) [(sel,lbl)] sc = ((),sd)` >>
  `fresh_vars_wrt sc u /\ ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
   u.vs_inst_idx = LENGTH sc.cs_current_insts /\ allocas_from lo u` by
    fs[selected_registration_resources_def] >>
  `?bb. lookup_block sd.cs_current_bb fn.fn_blocks = SOME bb /\
        phi_prefix_length bb.bb_instructions = 0` by
    (fs[fn_has_code_def] >> metis_tac[]) >>
  qpat_assum `compile_selector_checks (Var mid) [(sel,lbl)] sc = ((),sd)`
    (mp_tac o MATCH_MP (Q.SPECL [`[(sel,lbl)]`,`Var mid`,`sc`,`sd`]
      compile_selector_checks_ptr_endpoint_frame)) >>
  disch_then (qspecl_then [`ctx`,`fn`,`u`,`m`,`lo`,`PG`,`Gu`,`tnu`] mp_tac) >>
  impl_tac >- (asm_simp_tac (srw_ss()) [selector_hit_def] >> metis_tac[]) >>
  asm_simp_tac (srw_ss()) [selector_hit_def] >> disch_then strip_assume_tac >>
  rename1 `vars_pc_only u t` >>
  rename1 `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (u,Gu,tnu) [] (OK t,G',tn')` >>
  `selected_registration_frame u tnu t tn' /\ t.vs_memory = u.vs_memory` by
    metis_tac[grouped_entry_frame_vars_pc] >>
  `selected_registration_frame s tn t tn'` by
    (qpat_assum `selected_registration_frame s tn u tnu`
       (strip_assume_tac o REWRITE_RULE [selected_registration_frame_def]) >>
     qpat_assum `selected_registration_frame u tnu t tn'`
       (strip_assume_tac o REWRITE_RULE [selected_registration_frame_def]) >>
     asm_simp_tac (srw_ss()) [selected_registration_frame_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t /\
      t.vs_alloca_next + pending_alloca_size fn t <= w2n t.vs_initial_fmp` by
    metis_tac[grouped_registration_vars_pc] >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,G',tn')` by
    metis_tac[gas_origin_ptr_path_append, listTheory.APPEND_NIL] >>
  `!D. (!fuel. ptr_safe_blocks D lo fuel ctx fn PG G' tn' t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s` by metis_tac[] >>
  qexistsl_tac [`t`,`G'`,`tn'`] >>
  asm_rewrite_tac[MEM_APPEND, MEM] >>
  `t.vs_allocas = u.vs_allocas /\ t.vs_alloca_next = u.vs_alloca_next` by
    fs[vars_pc_only_def, venom_state_component_equality] >>
  fs[selected_registration_resources_def, alloca_inv_def,
     allocas_non_overlapping_def, alloca_next_valid_def, allocas_from_def,
     alloca_frontier_inv_def, remaining_alloca_budget_def] >>
  rpt strip_tac >> res_tac >> asm_rewrite_tac[]
QED

(* An unmatched grouped selector can allocate keyword buffers on its way
   past the other groups. Carry that allocation history into the fallback
   guard, whose execution changes neither the buffers nor their owners. *)
Theorem grouped_fallback_checks_pass:
  compile_group_dispatch_linear groups fallback start = (jobs,dispatch_end) /\
  fn_has_code start dispatch_end fn /\ EVERY group_entry_labels_ok groups /\
  ci_mono dispatch_end checks /\ checks.cs_current_bb = fallback /\
  checks.cs_current_insts = [] /\ lookup_block fallback fn.fn_blocks = SOME target /\
  compile_entry_checks 4 pay checks = ((),body_start) /\
  fn_has_code checks body_start fn /\
  (pay \/ s.vs_call_ctx.cc_callvalue = 0w) /\
  (4 <= LENGTH s.vs_call_ctx.cc_calldata ==>
    EVERY (\group. case group of
      ExternalSingle (sel,lbl,tz) pkg =>
        calldata_method_id s.vs_call_ctx.cc_calldata <> n2w sel
    | ExternalDefaults common entries specs _ =>
        FIND (\(sel,_,_,_). calldata_method_id s.vs_call_ctx.cc_calldata = n2w sel)
          entries = NONE /\
        EVERY (\(_,ty,_). type_memory_bytes common.ec_env ty < dimword (:256)) specs)
      groups) /\
  (!name bb. lookup_block name fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  selected_registration_resources ctx fn site lo start s /\ s.vs_allocas = FEMPTY /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp) ==>
  ?u Gu tnu.
    selected_registration_resources ctx fn site lo body_start u /\
    selected_registration_frame s tn u tnu /\ u.vs_memory = s.vs_memory /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u /\
      u.vs_alloca_next + pending_alloca_size fn u <= w2n u.vs_initial_fmp) /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK u,Gu,tnu)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?t Gt tnt.
    selected_registration_resources ctx fn site lo checks t /\
    selected_registration_frame s tn t tnt /\ t.vs_memory = s.vs_memory /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t /\
      t.vs_alloca_next + pending_alloca_size fn t <= w2n t.vs_initial_fmp) /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,Gt,tnt)` by
    (Cases_on `4 <= LENGTH s.vs_call_ctx.cc_calldata`
     >- (`EVERY (\group. case group of
            ExternalSingle (sel,lbl,tz) pkg =>
              calldata_method_id s.vs_call_ctx.cc_calldata <> n2w sel
          | ExternalDefaults common entries specs _ =>
              FIND (\(sel,_,_,_). calldata_method_id s.vs_call_ctx.cc_calldata = n2w sel)
                entries = NONE /\
              EVERY (\(_,ty,_). type_memory_bytes common.ec_env ty < dimword (:256)) specs)
            groups` by fs[] >>
         drule_all grouped_dispatch_missed_fallback_origin >>
         disch_then (strip_assume_tac o SPEC_ALL) >>
         rename1 `ci_mono r dispatch_end` >>
         rename1 `fresh_vars_wrt r t` >>
         rename1 `selected_registration_frame s tn t tnt` >>
         `r.cs_next_id <= checks.cs_next_id /\ r.cs_next_var <= checks.cs_next_var` by
           (fs[ci_mono_def] >> decide_tac) >>
         `!id entry. FLOOKUP t.vs_allocas id = SOME entry ==> id < checks.cs_next_id` by
           (rpt strip_tac >>
            qpat_assum `!id entry. FLOOKUP t.vs_allocas id = SOME entry ==>
               id < r.cs_next_id` (drule_then assume_tac) >> decide_tac) >>
         `fresh_vars_wrt checks t` by
           (irule emitHelperPropsTheory.fresh_vars_wrt_mono >>
            qexists_tac `r` >> simp[arithmeticTheory.GREATER_EQ]) >>
         qexistsl_tac [`t`,`G'`,`tnt`] >>
         asm_rewrite_tac[selected_registration_resources_def, LENGTH]) >>
     `LENGTH s.vs_call_ctx.cc_calldata < 4` by decide_tac >>
     `fresh_vars_wrt start s /\ ~s.vs_halted /\
       s.vs_current_bb = start.cs_current_bb /\
       s.vs_inst_idx = LENGTH start.cs_current_insts /\ allocas_from lo s` by
       fs[selected_registration_resources_def] >>
     `ctx_has_dalloca ctx ==> allocas_below_fmp s` by metis_tac[] >>
     `!bb. lookup_block fallback fn.fn_blocks = SOME bb ==>
       phi_prefix_length bb.bb_instructions = 0` by metis_tac[] >>
     drule_all grouped_dispatch_short_prelude >>
     disch_then (strip_assume_tac o SPEC_ALL) >>
     rename1 `ci_mono q dispatch_end` >>
     rename1 `fresh_vars_wrt q t` >>
     rename1 `selected_registration_frame s tn t tnt` >>
     `fresh_vars_wrt checks t` by
       (imp_res_tac ci_mono_trans >> fs[ci_mono_def] >>
        metis_tac[emitHelperPropsTheory.fresh_vars_wrt_mono, arithmeticTheory.GREATER_EQ]) >>
     qexistsl_tac [`t`,`G'`,`tnt`] >> asm_rewrite_tac[] >>
     conj_tac
     >- (irule grouped_entry_resources_vars_pc >>
         asm_rewrite_tac[LENGTH] >> qexistsl_tac [`s`,`start`] >> simp[]) >>
     metis_tac[grouped_registration_vars_pc]) >>
  rename1 `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,Gt0,tnt)` >>
  `t.vs_call_ctx = s.vs_call_ctx` by fs[selected_registration_frame_def] >>
  `(pay \/ t.vs_call_ctx.cc_callvalue = 0w) /\
    LENGTH t.vs_call_ctx.cc_calldata < dimword (:256)` by simp[] >>
  mp_tac (Q.INST [`m` |-> `4`, `s` |-> `t`, `sa` |-> `checks`,
    `sb` |-> `body_start`, `tn` |-> `tnt`, `G` |-> `Gt0`]
    (SPEC_ALL grouped_default_checks_pass_origin)) >>
  asm_rewrite_tac[arithmeticTheory.LESS_EQ_REFL] >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  rename1 `selected_registration_frame t tnt v tnv` >>
  `selected_registration_frame s tn v tnv` by
    (qpat_assum `selected_registration_frame s tn t tnt` mp_tac >>
     qpat_assum `selected_registration_frame t tnt v tnv` mp_tac >>
     PURE_REWRITE_TAC [selected_registration_frame_def] >> rpt strip_tac >>
     asm_rewrite_tac[]) >>
  qexistsl_tac [`v`,`G'`,`tnv`] >> asm_rewrite_tac[] >>
  rpt gen_tac >>
  qpat_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) _ _`
    (qspecl_then [`D`,`explicit`] assume_tac) >>
  qpat_assum `!D explicit. gas_origin_ptr_path _ (t,Gt0,tnt) _ _`
    (qspecl_then [`D`,`explicit`] assume_tac) >>
  qpat_assum `gas_origin_ptr_path _ (s,G,tn) _ _`
    (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
  disch_then (qspecl_then [`t`,`Gt0`,`tnt`,`[]`,`OK v`,`G'`,`tnv`] mp_tac) >>
  simp[]
QED
