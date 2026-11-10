(* Compiler-only suffix preservation for selected argument registration. *)
Theory actualRegistrationCode
Ancestors
  actualDecoderPackaging abiDecoderAppend moduleLowering fragExec compileEnv arithmetic list
  loweringShapeProps loweringShapeDefs loweringShapeRules vyperCompiler venomInst

Theorem cs_appends_abi_arg_ptr_guard:
  !opc actual parent. cs_appends (compile_abi_arg_ptr_guard opc actual parent)
Proof
  rw[compile_abi_arg_ptr_guard_def, cs_appends_return] >>
  ho_match_mp_tac cs_appends_bind >> simp[cs_appends_emit_helpers] >> gen_tac >>
  ho_match_mp_tac cs_appends_bind >> simp[cs_appends_emit_helpers]
QED

Theorem cs_appends_decode_args:
  !args cenv off opc hi base.
    cs_appends (compile_decode_args cenv args off opc hi base)
Proof
  Induct >- simp[compile_decode_args_def, cs_appends_return] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[Once compile_decode_args_def, LET_THM] >>
  Cases_on `h1` >> simp[]
  >- (ntac 2 (ho_match_mp_tac cs_appends_bind >> conj_tac
        >- simp[cs_appends_emit_helpers] >> gen_tac) >>
      irule cs_appends_ignore_bind >> conj_tac
      >- simp[cs_appends_abi_clamp] >>
      irule cs_appends_ignore_bind >> conj_tac
      >- (Cases_on `FLOOKUP cenv.ce_vars h0` >> simp[cs_appends_return] >>
          Cases_on `var_location_decode_operand x` >>
          simp[cs_appends_return, cs_appends_emit_helpers]) >> simp[]) >>
  Cases_on `FLOOKUP cenv.ce_vars h0` >> simp[] >>
  Cases_on `var_location_decode_operand x` >> simp[] >>
  Cases_on `h2` >> simp[] >>
  rpt (ho_match_mp_tac cs_appends_bind >> conj_tac
    >- simp[cs_appends_emit_helpers] >> gen_tac) >>
  irule cs_appends_ignore_bind >>
  simp[cs_appends_ignore_bind, cs_appends_abi_arg_ptr_guard,
       cs_appends_abi_decode_mutual]
QED

Theorem cs_appends_register_positional_args:
  !args cenv off. cs_appends (compile_register_positional_args cenv args off)
Proof
  Induct >- simp[compile_register_positional_args_def, cs_appends_return] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[Once compile_register_positional_args_def] >>
  Cases_on `FLOOKUP cenv.ce_vars h0` >> simp[] >>
  Cases_on `var_location_memory_size x` >> simp[] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_abi_alloc_buffer] >> gen_tac >>
  simp[cs_appends_bind, cs_appends_return] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_return] >> gen_tac >>
  irule cs_appends_ignore_bind >> simp[cs_appends_decode_args]
QED

Theorem register_positional_args_append:
  !xs ys cenv off st cenvf stf.
    compile_register_positional_args cenv (xs ++ ys) off st = (cenvf,stf) <=>
    ?cenvm stm.
      compile_register_positional_args cenv xs off st = (cenvm,stm) /\
      compile_register_positional_args cenvm ys
        (off + SUM (MAP (\(name,prim,dyn,sz,info). sz) xs)) stm = (cenvf,stf)
Proof
  Induct >- simp[compile_register_positional_args_def, comp_return_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp_tac (srw_ss()) [APPEND, MAP, SUM, pairTheory.pair_case_thm] >>
  Cases_on `FLOOKUP cenv.ce_vars h0`
  >- (asm_simp_tac (srw_ss()) [compile_register_positional_args_def] >>
      qpat_x_assum `!ys cenv off st cenvf stf. _` (fn th => rewrite_tac[th]) >> simp_tac std_ss [ADD_ASSOC]) >>
  Cases_on `var_location_memory_size x`
  >- (asm_simp_tac (srw_ss()) [compile_register_positional_args_def] >>
      qpat_x_assum `!ys cenv off st cenvf stf. _` (fn th => rewrite_tac[th]) >> simp_tac std_ss [ADD_ASSOC]) >>
  asm_simp_tac (srw_ss()) [compile_register_positional_args_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_alloc_buffer x' st` >>
  simp_tac (srw_ss()) [LET_THM] >>
  pairarg_tac >>
  qpat_x_assum `compile_decode_args _ _ _ _ _ _ _ = _`
    (fn th => rewrite_tac[th]) >>
  simp_tac std_ss [] >>
  qpat_x_assum `!ys cenv off st cenvf stf. _` (fn th => rewrite_tac[th]) >>
  simp_tac std_ss [ADD_ASSOC]
QED

Theorem register_positional_args_suffix_extends:
  compile_register_positional_args cenv args off st = (cenvf,stf) ==>
  cs_extends st stf
Proof
  metis_tac[cs_appends_def, cs_appends_register_positional_args]
QED

Theorem decode_args_suffix_extends:
  compile_decode_args cenv args off opc hi base_adj st = ((),stf) ==>
  cs_extends st stf
Proof
  metis_tac[cs_appends_def, cs_appends_decode_args]
QED

Theorem register_selected_arg_boundaries:
  compile_register_positional_args cenv (prefix ++ arg :: suffix) off st =
    (cenvf,stf) ==>
  ?ce_before before ce_after after.
    compile_register_positional_args cenv prefix off st = (ce_before,before) /\
    compile_register_positional_args ce_before [arg]
      (off + SUM (MAP (\(name,prim,dyn,sz,info). sz) prefix)) before =
      (ce_after,after) /\
    compile_register_positional_args ce_after suffix
      (off + SUM (MAP (\(name,prim,dyn,sz,info). sz) prefix) +
       (\(name,prim,dyn,sz,info). sz) arg) after = (cenvf,stf) /\
    cs_extends st before /\ cs_extends before after /\ cs_extends after stf
Proof
  rewrite_tac[register_positional_args_append] >> strip_tac >>
  qpat_x_assum `compile_register_positional_args _ (_::_) _ _ = _` mp_tac >>
  `arg :: suffix = [arg] ++ suffix` by simp[] >>
  pop_assum (fn th => once_rewrite_tac[th]) >>
  rewrite_tac[register_positional_args_append] >> strip_tac >>
  goal_assum $ drule_at Any >> goal_assum $ drule_at Any >>
  full_simp_tac std_ss [MAP, SUM, ADD_ASSOC] >>
  metis_tac[register_positional_args_suffix_extends]
QED

Theorem registration_emit_op_extends[local]:
  emit_op opc ops st = (v,st') ==> cs_extends st st'
Proof
  metis_tac[cs_appends_def, cj 2 cs_appends_emit_helpers]
QED

Theorem registration_guard_extends[local]:
  compile_abi_arg_ptr_guard opc actual parent st = (v,st') ==> cs_extends st st'
Proof
  metis_tac[cs_appends_def, cs_appends_abi_arg_ptr_guard]
QED

Theorem decode_singleton_aggregate_boundary:
  compile_decode_args cenv [(name,F,dyn,sz,info)] off CALLDATALOAD (Lit 0w) base_adj st =
    ((),stf) /\
  FLOOKUP cenv.ce_vars name = SOME loc /\
  var_location_decode_operand loc = SOME dst ==>
  ?src first.
    compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) info first = ((),stf) /\
    cs_extends st first
Proof
  strip_tac >>
  qpat_x_assum `compile_decode_args _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_decode_args_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  Cases_on `dyn` >> simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> fs[]) >> strip_tac >> gvs[] >>
  goal_assum $ drule_at Any >>
  imp_res_tac registration_emit_op_extends >>
  imp_res_tac registration_guard_extends >>
  metis_tac[cs_extends_trans]
QED

Theorem register_singleton_aggregate_boundary:
  compile_register_positional_args cenv [(name,F,dyn,sz,info)] off st =
    (cenvf,stf) /\
  FLOOKUP cenv.ce_vars name = SOME loc /\
  var_location_memory_size loc = SOME mem_size ==>
  ?buf allocated src first.
    compile_alloc_buffer mem_size st = (buf,allocated) /\
    compile_abi_decode_to_buf buf.buf_operand src CALLDATALOAD (Lit 0w)
      info first = ((),stf) /\
    cs_extends st first
Proof
  strip_tac >>
  qpat_x_assum `compile_register_positional_args _ _ _ _ = _` mp_tac >>
  simp[compile_register_positional_args_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule decode_singleton_aggregate_boundary >>
  simp[finite_mapTheory.FLOOKUP_UPDATE, var_location_decode_operand_def] >>
  strip_tac >>
  imp_res_tac (REWRITE_RULE [cs_appends_def] cs_appends_abi_alloc_buffer) >>
  metis_tac[cs_extends_trans]
QED

Theorem register_selected_aggregate_decoder:
  compile_register_positional_args cenv
    (prefix ++ (name,F,dyn,sz,info) :: suffix) off st = (cenvf,stf) /\
  (!ce before. compile_register_positional_args cenv prefix off st = (ce,before) ==>
    ?loc mem_size. FLOOKUP ce.ce_vars name = SOME loc /\
      var_location_memory_size loc = SOME mem_size) ==>
  ?dst src first last.
    compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) info first = ((),last) /\
    cs_extends st first /\ cs_extends last stf
Proof
  strip_tac >> drule register_selected_arg_boundaries >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule_all register_singleton_aggregate_boundary >> strip_tac >>
  goal_assum $ drule_at Any >> metis_tac[cs_extends_trans]
QED

Theorem external_function_registration_boundary:
  compile_external_function_body cenv args nr nkey transient view ss ret_type st =
    ((),stf) /\
  shape_state st /\ cenv_static_ok cenv /\ cenv.ce_return_pc = NONE /\
  ~supported_stmts_expr_exists expr_shape_root ss ==>
  ?ce registered.
    compile_register_positional_args cenv args 4 st = (ce,registered) /\
    compile_guarded_body ce nr nkey transient view ss ret_type registered = ((),stf) /\
    shape_state registered /\ cs_extends registered stf
Proof
  strip_tac >>
  qpat_x_assum `compile_external_function_body _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_external_function_body_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  `cenv_shape_ok st cenv` by metis_tac[cenv_static_ok_shape_ok] >>
  mp_tac compile_register_positional_args_shape >>
  simp[shape_step_def] >> disch_then drule >> simp[] >> strip_tac >>
  drule compile_guarded_body_env_shape >> simp[] >>
  simp[shape_step_def, shape_extends_def] >>
  disch_then drule >> simp[] >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem external_bodies_run_shape:
  EVERY external_fn_shape_ok fns /\ shape_state st /\
  compile_external_fn_bodies fns st = ((),stf) ==>
  shape_state stf /\ cs_extends st stf
Proof
  strip_tac >> drule compile_external_fn_bodies_shape >>
  simp[shape_step_def, shape_extends_def] >> disch_then drule >> simp[]
QED

Theorem external_bodies_append:
  !xs ys st stf.
    compile_external_fn_bodies (xs ++ ys) st = ((),stf) <=>
    ?mid. compile_external_fn_bodies xs st = ((),mid) /\
      compile_external_fn_bodies ys mid = ((),stf)
Proof
  Induct >- simp[compile_external_fn_bodies_def, comp_return_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_external_fn_bodies_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >>
  first_x_assum (fn th => rewrite_tac[th]) >>
  simp[]
QED

Theorem external_singleton_body_boundary:
  compile_external_fn_bodies
    [(lbl,cenv,args,min_cds,pay,nr,nkey,transient,view,ss,ret_type)] st = ((),stf) /\
  shape_state st /\
  external_fn_shape_ok (lbl,cenv,args,min_cds,pay,nr,nkey,transient,view,ss,ret_type) ==>
  ?first.
    compile_external_function_body cenv args nr nkey transient view ss ret_type first =
      ((),stf) /\ shape_state first /\ cs_extends st first
Proof
  strip_tac >>
  qpat_x_assum `compile_external_fn_bodies _ _ = _` mp_tac >>
  simp[compile_external_fn_bodies_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  goal_assum $ drule_at Any >>
  `shape_step F (K T) (\st. T) (new_block lbl) (\x st. T)` by
    (ho_match_mp_tac shape_step_new_block >> simp[shape_stable_def]) >>
  pop_assum mp_tac >> simp[shape_step_def] >> disch_then drule >>
  simp[] >> strip_tac >>
  mp_tac compile_entry_checks_shape >> simp[shape_step_def] >>
  disch_then drule >> simp[] >> strip_tac >>
  gvs[shape_extends_def] >> metis_tac[cs_extends_trans]
QED

Theorem external_bodies_cons_split:
  compile_external_fn_bodies (fn_desc::rest) st = ((),stf) <=>
  ?mid. compile_external_fn_bodies [fn_desc] st = ((),mid) /\
    compile_external_fn_bodies rest mid = ((),stf)
Proof
  MATCH_ACCEPT_TAC (SIMP_RULE std_ss [APPEND]
    (Q.SPEC `[fn_desc]` external_bodies_append))
QED

Theorem external_selected_registration_boundary:
  compile_external_fn_bodies
    (prefix ++ (lbl,cenv,args,min_cds,pay,nr,nkey,transient,view,ss,ret_type) :: suffix)
    st = ((),stf) /\ shape_state st /\
  EVERY external_fn_shape_ok
    (prefix ++ (lbl,cenv,args,min_cds,pay,nr,nkey,transient,view,ss,ret_type) :: suffix) ==>
  ?first ce registered.
    compile_register_positional_args cenv args 4 first = (ce,registered) /\
    cs_extends st first /\ cs_extends registered stf
Proof
  strip_tac >>
  qpat_x_assum `compile_external_fn_bodies _ _ = _` mp_tac >>
  rewrite_tac[external_bodies_append] >> strip_tac >>
  qpat_x_assum `compile_external_fn_bodies (_::_) _ = _` mp_tac >>
  pure_once_rewrite_tac[external_bodies_cons_split] >> strip_tac >>
  fs[EVERY_APPEND] >>
  drule_all external_bodies_run_shape >> strip_tac >>
  drule_all external_singleton_body_boundary >> strip_tac >>
  qpat_x_assum `compile_external_fn_bodies prefix _ = _` kall_tac >>
  `EVERY external_fn_shape_ok
    [(lbl,cenv,args,min_cds,pay,nr,nkey,transient,view,ss,ret_type)]` by simp[] >>
  drule_all external_bodies_run_shape >> strip_tac >>
  qpat_x_assum `compile_external_fn_bodies [_] _ = _` kall_tac >>
  drule_all external_bodies_run_shape >> strip_tac >>
  fs[external_fn_shape_ok_def] >>
  drule_all external_function_registration_boundary >> strip_tac >>
  goal_assum $ drule_at Any >> metis_tac[cs_extends_trans]
QED

Theorem external_fallback_suffix_extends:
  shape_state st /\ fallback_shape_ok fallback_fn /\
  new_block fallback_lbl st = (old,fallback_st) /\
  (case fallback_fn of
     NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
   | SOME (ce,pay,nr,key,trans,view,ss,ret) =>
       compile_fallback_body ce pay nr key trans view ss ret)
    fallback_st = ((),entry_end) ==>
  cs_extends st entry_end
Proof
  strip_tac >>
  `shape_step F (K T) (\st. T) (new_block fallback_lbl) (\x st. T)` by
    (ho_match_mp_tac shape_step_new_block >> simp[shape_stable_def]) >>
  pop_assum mp_tac >> simp[shape_step_def] >> disch_then drule >>
  simp[] >> strip_tac >>
  drule runtime_fallback_shape >> simp[shape_step_def] >>
  disch_then drule >> simp[] >> strip_tac >>
  gvs[shape_extends_def] >> metis_tac[cs_extends_trans]
QED

Theorem runtime_dispatch_shape_boundary:
  EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) selectors /\ shape_state st /\
  fresh_label "fallback" st = (fallback_lbl,label_st) /\
  compile_selector_dispatch_linear (MAP (\(sel,lbl,z). (sel,lbl)) selectors)
    fallback_lbl label_st = ((),dispatch_st) ==>
  shape_state dispatch_st /\ cs_extends st dispatch_st
Proof
  strip_tac >>
  `shape_step F jump_label_ok (\st. T) (fresh_label "fallback")
     (\l st. T /\ compiler_label l /\ label_sfx "fallback" l)` by
    (ho_match_mp_tac shape_step_fresh_label_sfx >> simp[shape_stable_def]) >>
  pop_assum mp_tac >> simp[shape_step_def] >> disch_then drule >>
  simp[] >> strip_tac >>
  `EVERY (\(sel,lbl). jump_label_ok lbl)
     (MAP (\(sel,lbl,z). (sel,lbl)) selectors)` by
    (fs[EVERY_MAP, EVERY_MEM, pairTheory.FORALL_PROD, jump_label_ok_def] >> metis_tac[]) >>
  `jump_label_ok fallback_lbl` by simp[jump_label_ok_def] >>
  `~label_sfx "dispatch" fallback_lbl` by
    (`"fallback" <> "dispatch"` by simp[] >> metis_tac[label_sfx_distinct]) >>
  drule_all compile_selector_dispatch_linear_shape >>
  simp[shape_step_def] >> disch_then drule >> simp[] >> strip_tac >>
  gvs[shape_extends_def] >> metis_tac[cs_extends_trans]
QED

Theorem external_selected_aggregate_boundary:
  compile_external_fn_bodies
    (prefix ++ (lbl,cenv,ap ++ (name,F,dyn,sz,info)::az,
      min_cds,pay,nr,nkey,transient,view,ss,ret_type) :: suffix)
    st = ((),stf) /\ shape_state st /\
  EVERY external_fn_shape_ok
    (prefix ++ (lbl,cenv,ap ++ (name,F,dyn,sz,info)::az,
      min_cds,pay,nr,nkey,transient,view,ss,ret_type) :: suffix) /\
  (!start ce before.
    compile_register_positional_args cenv ap 4 start = (ce,before) ==>
    ?loc mem_size. FLOOKUP ce.ce_vars name = SOME loc /\
      var_location_memory_size loc = SOME mem_size) ==>
  ?dst src first last.
    compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) info first = ((),last) /\
    cs_extends st first /\ cs_extends last stf
Proof
  strip_tac >> drule_all external_selected_registration_boundary >> strip_tac >>
  drule register_selected_aggregate_decoder >>
  impl_tac >- metis_tac[] >> strip_tac >>
  goal_assum $ drule_at Any >> metis_tac[cs_extends_trans]
QED

Theorem run_lowering_packaged_entry_member:
  run_lowering selectors external_fns internal_fns fallback_fn rpolicy
    bucket_count fn_metadata_bytes dense_buckets entry_info "__entry" = SOME unit /\
  compile_generate_runtime selectors external_fns internal_fns fallback_fn
    rpolicy.rpol_frontend_dispatch bucket_count fn_metadata_bytes dense_buckets
    entry_info (initial_compile_state "__entry") = ((),final) /\
  compile_internal_fn_bodies internal_fns entry_end = (r,final) /\
  shape_state entry_end /\
  shape_extends F jump_label_ok (initial_compile_state "__entry") entry_end /\
  EVERY internal_fn_shape_ok internal_fns /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors internal_fns) /\
  ALL_DISTINCT (MAP FST (internal_fn_descriptors internal_fns)) ==>
  MEM (mk_raw_function "__entry" (all_blocks entry_end)) unit.cu_context.ctx_functions
Proof
  strip_tac >> drule runtime_entry_blocks_shape >> strip_tac >>
  `EVERY (\d. ~compiler_label (FST d) /\
    ~MEM (FST d) (MAP (\bb. bb.bb_label) (all_blocks entry_end)))
      (internal_fn_descriptors internal_fns)` by
    (rewrite_tac[EVERY_MEM] >> rpt strip_tac >> BETA_TAC >>
     irule internal_name_not_entry_label >> simp[] >> fs[EVERY_MEM]) >>
  drule_all external_phase_packaged_entry >> strip_tac >>
  qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[run_lowering_def] >>
  Cases_on `lowering_policy_ok rpolicy` >> simp[] >>
  Cases_on `lowering_context_ok
    (mk_venom_context (mk_raw_function "__entry" (all_blocks entry_end)::functions)
      (SOME "__entry"))` >> simp[] >> strip_tac >>
  gvs[mk_venom_context_def]
QED

Theorem runtime_selected_aggregate_packaged:
  run_lowering selectors external_fns internal_fns fallback_fn rpolicy
    bucket_count fn_metadata_bytes dense_buckets entry_info "__entry" = SOME unit /\
  rpolicy.rpol_frontend_dispatch = Linear /\
  compile_generate_runtime selectors external_fns internal_fns fallback_fn
    Linear bucket_count fn_metadata_bytes dense_buckets entry_info
    (initial_compile_state "__entry") = ((),final) /\
  run_venom_pipeline mem_ok calling_ok post_ok rpolicy spec unit = SOME out /\
  EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) selectors /\
  EVERY external_fn_shape_ok external_fns /\ fallback_shape_ok fallback_fn /\
  EVERY internal_fn_shape_ok internal_fns /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors internal_fns) /\
  ALL_DISTINCT (MAP FST (internal_fn_descriptors internal_fns)) /\
  external_fns = prefix ++
    (lbl,cenv,ap ++ (name,F,dyn,sz,info)::az,
      min_cds,pay,nr,nkey,transient,view,ss,ret_type) :: suffix /\
  (!start ce before.
    compile_register_positional_args cenv ap 4 start = (ce,before) ==>
    ?loc mem_size. FLOOKUP ce.ce_vars name = SOME loc /\
      var_location_memory_size loc = SOME mem_size) ==>
  ?dst src first last fn.
    compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) info first = ((),last) /\
    MEM fn unit.cu_context.ctx_functions /\ fn_has_code first last fn /\
    !inst. abi_decoder_code_member inst last ==> MEM inst (fn_insts fn)
Proof
  strip_tac >>
  `shape_state (initial_compile_state "__entry")` by
    simp[shape_state_initial_compile_state] >>
  drule_all runtime_external_boundary >> strip_tac >>
  drule_all runtime_dispatch_shape_boundary >> strip_tac >>
  drule_all external_bodies_run_shape >> strip_tac >>
  drule_all external_fallback_suffix_extends >> strip_tac >>
  qpat_x_assum `external_fns = _` SUBST_ALL_TAC >>
  Cases_on `r` >> fs[] >>
  drule run_lowering_packaged_entry_member >> simp[] >>
  disch_then drule >> simp[] >> strip_tac >>
  drule_all checked_pipeline_entry_labels >> strip_tac >>
  drule external_selected_aggregate_boundary >> simp[] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule cs_extends_abi_decode >> strip_tac >>
  `cs_extends last entry_end` by metis_tac[cs_extends_trans] >>
  goal_assum $ drule_at Any >> goal_assum $ drule_at Any >>
  conj_tac
  >- (irule external_decoder_fn_has_code >>
      goal_assum $ drule_at Any >> simp[] >>
      metis_tac[cs_extends_trans]) >>
  metis_tac[external_phase_decoder_owned]
QED
