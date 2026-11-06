(* Preserve the entry-check states at the compiler boundary. *)
Theory entryCheckIntervals
Ancestors actualRegistrationCode actualDecoderPackaging loweringShapeProps
  loweringShapeDefs loweringShapeRules moduleLowering compileEnv fragExec list rich_list

Theorem external_singleton_check_interval:
  compile_external_fn_bodies
    [(lbl,cenv,args,min_cds,pay,nr,nkey,transient,view,ss,ret_type)] st = ((),stf) /\
  shape_state st /\
  external_fn_shape_ok (lbl,cenv,args,min_cds,pay,nr,nkey,transient,view,ss,ret_type) ==>
  ?opened checked.
    new_block lbl st = (st.cs_current_bb,opened) /\
    compile_entry_checks min_cds pay opened = ((),checked) /\
    compile_external_function_body cenv args nr nkey transient view ss ret_type checked = ((),stf) /\
    shape_state opened /\ shape_state checked /\
    cs_extends st opened /\ cs_extends opened checked /\ cs_extends checked stf
Proof
  strip_tac >>
  qpat_x_assum `compile_external_fn_bodies _ _ = _` mp_tac >>
  simp[compile_external_fn_bodies_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  `shape_step F (K T) (\st. T) (new_block lbl) (\x st. T)` by
    (ho_match_mp_tac shape_step_new_block >> simp[shape_stable_def] >>
     irule jump_label_ok_not_internal >>
     gvs[external_fn_shape_ok_def, jump_label_ok_def]) >>
  pop_assum mp_tac >> simp[shape_step_def] >> disch_then drule >>
  simp[] >> strip_tac >>
  mp_tac compile_entry_checks_shape >> simp[shape_step_def] >>
  disch_then drule >> simp[] >> strip_tac >>
  drule cs_extends_new_block >> strip_tac >>
  fs[external_fn_shape_ok_def] >>
  drule_all external_function_registration_boundary >> strip_tac >>
  drule register_positional_args_suffix_extends >> strip_tac >>
  gvs[shape_extends_def] >> conj_tac
  >- (qpat_x_assum `new_block _ _ = _` mp_tac >> simp[new_block_def]) >>
  metis_tac[cs_extends_trans]
QED

Theorem external_selected_check_interval:
  compile_external_fn_bodies
    (prefix ++ (lbl,cenv,args,min_cds,pay,nr,nkey,transient,view,ss,ret_type)::suffix)
    st = ((),stf) /\ shape_state st /\
  EVERY external_fn_shape_ok
    (prefix ++ (lbl,cenv,args,min_cds,pay,nr,nkey,transient,view,ss,ret_type)::suffix) ==>
  ?before opened checked after.
    compile_external_fn_bodies prefix st = ((),before) /\
    new_block lbl before = (before.cs_current_bb,opened) /\
    compile_entry_checks min_cds pay opened = ((),checked) /\
    compile_external_function_body cenv args nr nkey transient view ss ret_type checked = ((),after) /\
    compile_external_fn_bodies suffix after = ((),stf) /\
    shape_state opened /\ shape_state checked /\
    cs_extends st opened /\ cs_extends opened checked /\ cs_extends checked stf
Proof
  strip_tac >>
  qpat_x_assum `compile_external_fn_bodies _ _ = _` mp_tac >>
  rewrite_tac[external_bodies_append] >> strip_tac >>
  qpat_x_assum `compile_external_fn_bodies (_::_) _ = _` mp_tac >>
  pure_once_rewrite_tac[external_bodies_cons_split] >> strip_tac >>
  fs[EVERY_APPEND] >>
  drule_all external_bodies_run_shape >> strip_tac >>
  drule_all external_singleton_check_interval >> strip_tac >>
  `EVERY external_fn_shape_ok
    [(lbl,cenv,args,min_cds,pay,nr,nkey,transient,view,ss,ret_type)]` by simp[] >>
  drule_all external_bodies_run_shape >> strip_tac >>
  qpat_x_assum `compile_external_fn_bodies [_] _ = _` kall_tac >>
  qpat_x_assum `compile_external_fn_bodies prefix _ = _` mp_tac >> strip_tac >>
  drule_all external_bodies_run_shape >> strip_tac >>
  qexistsl_tac [`opened`, `checked`, `mid'`] >>
  simp[] >> metis_tac[cs_extends_trans]
QED

Theorem installed_selected_check_code:
  compile_external_fn_bodies pkgs start = ((),(stop_st : compile_state)) /\
  shape_state start /\ EVERY external_fn_shape_ok pkgs /\
  MEM (lbl,cenv,args,min_cds,pay,nr,nkey,transient,view,ss,ret_type) pkgs /\
  fn_has_code start stop_st fn ==>
  ?opened checked.
    compile_entry_checks min_cds pay opened = ((),checked) /\
    fn_has_code opened checked fn /\
    opened.cs_current_bb = lbl /\ opened.cs_current_insts = [] /\
    ~block_is_terminated opened
Proof
  strip_tac >>
  qpat_x_assum `MEM _ pkgs` mp_tac >> rewrite_tac[MEM_SPLIT] >> strip_tac >>
  gvs[] >> drule external_selected_check_interval >>
  impl_tac >- simp[] >> strip_tac >>
  qexistsl_tac [`opened`, `checked`] >> simp[] >> conj_tac
  >- metis_tac[fn_has_code_mid] >>
  qpat_x_assum `new_block _ _ = _` mp_tac >>
  simp[new_block_def, comp_bind_def, comp_return_def] >>
  strip_tac >> gvs[block_is_terminated_def]
QED
