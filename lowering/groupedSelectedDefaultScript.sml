(* Run the selector and the selected entry checks before initialization. *)
Theory groupedSelectedDefault
Ancestors
  groupedDispatchPath groupedInternalLabels groupedEntryResources groupedEntryCounters
  fragGasOriginPtr exprLoweringProps selectedAcceptedFold ptrDiscipline
  moduleLowering compileEnv emitHelperProps gasShadowState gasShadow gasShadowModuleDefs
  venomInst venomState fragExec fragGasOriginPtrLoop bodyPtrDefs words list pair

val shadow_group = ``\group. case group of
  ExternalSingle selector package =>
    ExternalSingle selector (gas_shadow_external_package package)
| ExternalDefaults common entries specs off =>
    ExternalDefaults (common with <| ec_env := gas_shadow_env T common.ec_env;
      ec_body := MAP gas_shadow_stmt common.ec_body |>)
      entries (MAP (\(n,ty,e). (n,ty,gas_shadow_expr e)) specs) off``;

Theorem grouped_selected_default_initializer_start:
  groups = pre ++ ExternalDefaults common entries specs off::post /\
  compile_group_dispatch_linear groups fallback sf = (jobs,sd) /\
  compile_group_dispatch_linear (MAP ^shadow_group groups) fallback sf =
    (shadow_jobs,shadow_sd) /\
  fn_has_code sf sd fn /\ fn_has_code sf shadow_sd shadow_fn /\
  EVERY group_entry_labels_ok groups /\
  EVERY group_entry_labels_ok (MAP ^shadow_group groups) /\
  EVERY (\group. case group of
    ExternalSingle (sel,_,_) _ => calldata_method_id s.vs_call_ctx.cc_calldata <> n2w sel
  | ExternalDefaults comp ens sp _ =>
      FIND (\(sel,_,_,_). calldata_method_id s.vs_call_ctx.cc_calldata = n2w sel) ens = NONE /\
      EVERY (\(_,ty,_). type_memory_bytes comp.ec_env ty < dimword (:256)) sp) pre /\
  FIND (\(sel,_,_,_). calldata_method_id s.vs_call_ctx.cc_calldata = n2w sel) entries =
    SOME (sel,lbl,mincd,k) /\
  EVERY (\(_,ty,_). type_memory_bytes common.ec_env ty < dimword (:256)) specs /\
  4 <= LENGTH s.vs_call_ctx.cc_calldata /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  (mincd <= 4 \/ mincd <= LENGTH s.vs_call_ctx.cc_calldata) /\
  (common.ec_payable \/ s.vs_call_ctx.cc_callvalue = 0w) /\
  selected_registration_resources ctx fn site lo sf s /\ s.vs_allocas = FEMPTY /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\
  (!name bb. lookup_block name fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp) ==>
  ?vars alloc_start alloc_end checks si si' last dispatch_end shadow_si shadow_si'
    v Gv tnv t J tz.
    MEM (ExternalCommonJob common vars) jobs /\
    compile_create_kwarg_allocas common.ec_env specs alloc_start = (vars,alloc_end) /\
    checks.cs_current_bb = lbl /\ checks.cs_current_insts = [] /\
    compile_entry_checks mincd common.ec_payable checks = ((),si) /\
    fn_has_code checks si fn /\
    compile_init_kwargs common.ec_env vars off k (Lit 0w) si = ((),si') /\
    fn_has_code si si' fn /\ fn_has_code si' last fn /\
    emit_inst JMP [Label common.ec_common_label] [] si' = ((),last) /\
    cs_extends last dispatch_end /\ ci_mono last dispatch_end /\
    cs_extends dispatch_end sd /\ ci_mono dispatch_end sd /\
    compile_init_kwargs (gas_shadow_env T common.ec_env)
      (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) vars)
      off k (Lit 0w) shadow_si = ((),shadow_si') /\
    fn_has_code shadow_si shadow_si' shadow_fn /\ gas_shadow_state si shadow_si /\
    selected_registration_resources ctx fn site lo checks v /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (v,Gv,tnv) [] (OK t,J,tz)) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK v,Gv,tnv)) /\
    selected_registration_resources ctx fn site lo si t /\
    selected_registration_frame s tn t tz /\ t.vs_memory = s.vs_memory /\
    (!name op ty e. MEM (name,op,ty,e) vars ==>
      ?id q base.
        op = Var q /\ not_fresh_at si q /\ lookup_var q t = SOME (n2w base) /\
        MEM (mk_inst id ALLOCA [Lit (n2w (type_memory_bytes common.ec_env ty))] [q])
          (fn_insts fn) /\
        FLOOKUP t.vs_allocas id = SOME (base,type_memory_bytes common.ec_env ty) /\
        id < si.cs_next_id /\
        base + type_memory_bytes common.ec_env ty < dimword (:256) /\
        ptr_covers J tz q t (type_memory_bytes common.ec_env ty)) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t /\
      t.vs_alloca_next + pending_alloca_size fn t <= w2n t.vs_initial_fmp) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,J,tz))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all grouped_dispatch_long_prelude_with_frame >>
  disch_then (qspecl_then [`tn`,`PG`,`G`] (qx_choosel_then
    [`mid`,`prelude`,`dispatch_end`,`br`,`u`,`Gu`,`tnu`]
    (map_every assume_tac o CONJUNCTS))) >>
  qpat_assum `!other other_jobs other_end other_fn. _`
    (qspecl_then [`MAP ^shadow_group groups`,`shadow_jobs`,`shadow_sd`,`shadow_fn`] mp_tac) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choose_then `shadow_dispatch_end`
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `groups = _` SUBST_ALL_TAC >>
  mp_tac (Q.INST [`pref` |-> `pre`,`rest` |-> `post`,`m` |->
      `calldata_method_id s.vs_call_ctx.cc_calldata`,`sa` |-> `prelude`,
      `sb` |-> `dispatch_end`,`s` |-> `u`,`G` |-> `Gu`,`tn` |-> `tnu`]
      (SPEC_ALL compile_external_groups_selected_default_origin_with_frame)) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`vars`,`checks`,`si`,`last`,`v`,`Gv`,`tnv`]
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `!sha shb shfn shjobs. _`
    (qspecl_then [`prelude`,`shadow_dispatch_end`,`shadow_fn`,`shadow_jobs`] mp_tac) >>
  impl_tac >- fs[gas_shadow_state_refl] >>
  disch_then (qx_choosel_then [`shadow_si`,`shadow_last`]
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `compile_entry_point_kwargs common.ec_env vars _ _ _ _ = _` (fn code =>
    qpat_assum `fn_has_code si last fn` (fn installed =>
      qx_choose_then `si'` (map_every assume_tac o CONJUNCTS)
        (MATCH_MP compile_entry_point_kwargs_layout (CONJ code installed)))) >>
  qpat_assum `compile_entry_point_kwargs _ (MAP _ vars) _ _ _ _ = _` (fn code =>
    qpat_assum `fn_has_code shadow_si shadow_last shadow_fn` (fn installed =>
      qx_choose_then `shadow_si'` (map_every assume_tac o CONJUNCTS)
        (MATCH_MP compile_entry_point_kwargs_layout (CONJ code installed)))) >>
  `v.vs_call_ctx = s.vs_call_ctx` by metis_tac[selected_registration_frame_def] >>
  mp_tac (Q.INST [`m` |-> `mincd`,`pay` |-> `common.ec_payable`,
    `sa` |-> `checks`,`sb` |-> `si`,`s` |-> `v`,`G` |-> `Gv`,`tn` |-> `tnv`]
    (SPEC_ALL grouped_default_checks_pass_origin)) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`t`,`J`,`tz`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `?alloc_start alloc_end. _`
    (qx_choosel_then [`alloc_start`,`alloc_end`] assume_tac) >>
  qexistsl_tac [`vars`,`alloc_start`,`alloc_end`,`checks`,`si`,`si'`,`last`,
    `dispatch_end`,`shadow_si`,`shadow_si'`,`v`,`Gv`,`tnv`,`t`,`J`,`tz`] >>
  asm_rewrite_tac[] >>
  rpt conj_tac
  >~ [`gas_origin_ptr_path _ (s,G,tn) [] (OK v,Gv,tnv)`]
  >- (rpt gen_tac >>
      irule gas_origin_ptr_path_trans >> asm_rewrite_tac[listTheory.APPEND_NIL] >>
      qexistsl_tac [`Gu`,`u`,`tnu`] >> asm_rewrite_tac[])
  >- (fs[selected_registration_frame_def] >> metis_tac[])
  >- suspend "owners" >>
  suspend "path"
QED

Resume grouped_selected_default_initializer_start[owners]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `!name op ty e. MEM _ vars ==> _`
    (drule_then (qx_choosel_then [`id`,`q`,`addr`] strip_assume_tac)) >>
  qexistsl_tac [`id`,`q`,`addr`] >>
  `ci_mono checks si` by metis_tac[compile_entry_checks_ci_mono, pairTheory.SND] >>
  qpat_assum `!p. not_fresh_at checks p ==> _` (drule_then strip_assume_tac) >>
  asm_rewrite_tac[] >>
  conj_tac >- fs[ci_mono_def] >>
  fs[ptr_covers_def] >> metis_tac[]
QED

Resume grouped_selected_default_initializer_start[path]:
  rpt gen_tac >>
  irule gas_origin_ptr_path_trans >> asm_rewrite_tac[listTheory.APPEND_NIL] >>
  qexistsl_tac [`Gv`,`v`,`tnv`] >> asm_rewrite_tac[] >>
  irule gas_origin_ptr_path_trans >> asm_rewrite_tac[listTheory.APPEND_NIL] >>
  qexistsl_tac [`Gu`,`u`,`tnu`] >> asm_rewrite_tac[]
QED

Finalise grouped_selected_default_initializer_start
