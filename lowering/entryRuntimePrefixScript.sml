(* Concrete compiler states at the entry/internal segmentation boundary. *)
Theory entryRuntimePrefix
Ancestors
  moduleLowering compileEnv entryRuntimeSlice loweringShapeProps
  loweringShapeDefs loweringShapeRules list venomInst unitShapeDefs

Theorem compile_generate_runtime_linear_split:
  compile_generate_runtime selectors external_fns internal_fns fallback_fn
    Linear bucket_count fn_metadata_bytes dense_buckets entry_info st0 =
      ((), st_final) ==>
  ?fallback_lbl s1 s2 s3 old s4 entry_st ir.
    fresh_label "fallback" st0 = (fallback_lbl, s1) /\
    compile_selector_dispatch_linear
      (MAP (\(sel,lbl,z). (sel,lbl)) selectors) fallback_lbl s1 = ((), s2) /\
    compile_external_fn_bodies external_fns s2 = ((), s3) /\
    new_block fallback_lbl s3 = (old, s4) /\
    (case fallback_fn of
       NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
     | SOME (ce,pay,nr,key,trans,view,ss,ty) =>
         compile_fallback_body ce pay nr key trans view ss ty) s4 = ((), entry_st) /\
    compile_internal_fn_bodies internal_fns entry_st = (ir, st_final)
Proof
  simp[compile_generate_runtime_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED

Theorem external_body_interval_extends[local]:
  cenv_static_ok ce /\ ce.ce_return_pc = NONE /\
  ~supported_stmts_expr_exists expr_shape_root fbody /\
  shape_state sd /\
  compile_register_positional_args ce args 4 sd = (ce', sa) /\
  compile_guarded_body ce' nr key trans view fbody rt sa = ((), se) ==>
  cs_extends sd sa /\ cs_extends sa se /\ shape_state se
Proof
  strip_tac >>
  `cenv_shape_ok sd ce` by (irule cenv_static_ok_shape_ok >> simp[]) >>
  qspecl_then [`args`, `ce`, `4`] mp_tac compile_register_positional_args_shape >>
  rewrite_tac[shape_step_def] >> disch_then drule >> simp[] >> strip_tac >>
  drule compile_guarded_body_env_shape >> simp[] >>
  rewrite_tac[shape_step_def] >> disch_then drule >> simp[] >> strip_tac >>
  gvs[shape_extends_def] >> first_x_assum drule >> simp[]
QED

Theorem compile_external_member_interval:
  MEM (lbl, ce, args, cds, pay, nr, key, trans, view, fbody, rt) packages /\
  EVERY external_fn_shape_ok packages /\ shape_state start /\
  compile_external_fn_bodies packages start = ((), st_final) ==>
  ?pre post sb old sc sd ce' sa se.
    packages = pre ++ (lbl, ce, args, cds, pay, nr, key, trans, view, fbody, rt) :: post /\
    compile_external_fn_bodies pre start = ((), sb) /\
    new_block lbl sb = (old, sc) /\
    compile_entry_checks cds pay sc = ((), sd) /\
    compile_register_positional_args ce args 4 sd = (ce', sa) /\
    compile_guarded_body ce' nr key trans view fbody rt sa = ((), se) /\
    compile_external_fn_bodies post se = ((), st_final) /\
    cs_extends start sa /\ cs_extends sa se /\ cs_extends se st_final /\
    shape_state st_final
Proof
  strip_tac >> drule_all compile_external_fn_bodies_member >> strip_tac >>
  gvs[EVERY_APPEND, external_fn_shape_ok_def] >>
  qspec_then `pre` mp_tac compile_external_fn_bodies_shape >>
  simp[shape_step_def] >> disch_then drule >> simp[] >> strip_tac >>
  `shape_state sc` by (irule shape_state_new_block >> metis_tac[]) >>
  `cs_extends sb sc` by metis_tac[cs_extends_new_block] >>
  qspecl_then [`cds`, `pay`] mp_tac compile_entry_checks_shape >>
  rewrite_tac[shape_step_def] >> disch_then drule >> simp[] >> strip_tac >>
  drule_all external_body_interval_extends >> strip_tac >>
  qspec_then `post` mp_tac compile_external_fn_bodies_shape >>
  simp[shape_step_def] >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `compile_register_positional_args ce args 4 sd = (selected_ce, sa)` >>
  qexistsl [`pre`, `post`, `sb`, `old`, `sc`, `sd`, `selected_ce`, `sa`, `se`] >>
  gvs[shape_extends_def] >>
  irule cs_extends_trans >> qexists `sb` >> simp[] >>
  irule cs_extends_trans >> qexists `sc` >> simp[] >>
  irule cs_extends_trans >> qexists `sd` >> simp[]
QED

Theorem runtime_dispatch_prefix_shape[local]:
  shape_state st0 /\
  EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) selectors /\
  fresh_label "fallback" st0 = (fallback_lbl, s1) /\
  compile_selector_dispatch_linear
    (MAP (\(sel,lbl,z). (sel,lbl)) selectors) fallback_lbl s1 = ((), s2) ==>
  shape_extends F jump_label_ok st0 s2 /\ shape_state s2 /\
  jump_label_ok fallback_lbl
Proof
  strip_tac >>
  qspecl_then [`F`, `jump_label_ok`, `\st. T`, `"fallback"`]
    mp_tac shape_step_fresh_label_sfx >>
  simp[shape_stable_def, shape_step_def] >> disch_then drule >> simp[] >> strip_tac >>
  `~label_sfx "dispatch" fallback_lbl` by
    (`"fallback" <> "dispatch"` by EVAL_TAC >> metis_tac[label_sfx_distinct]) >>
  `jump_label_ok fallback_lbl` by simp[jump_label_ok_def] >>
  `EVERY (\(sel,lbl). jump_label_ok lbl)
     (MAP (\(sel,lbl,z). (sel,lbl)) selectors)` by
    (gvs[EVERY_MAP, EVERY_MEM, pairTheory.FORALL_PROD, jump_label_ok_def] >>
     metis_tac[]) >>
  drule_all compile_selector_dispatch_linear_shape >>
  rewrite_tac[shape_step_def] >> disch_then drule >> simp[] >> strip_tac >>
  metis_tac[shape_extends_trans]
QED

Theorem runtime_fallback_interval_shape[local]:
  fallback_shape_ok fallback_fn /\ shape_state s4 /\
  (case fallback_fn of
     NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
   | SOME (ce,pay,nr,key,trans,view,ss,ty) =>
       compile_fallback_body ce pay nr key trans view ss ty) s4 = ((), entry_st) ==>
  shape_extends F jump_label_ok s4 entry_st /\ shape_state entry_st
Proof
  Cases_on `fallback_fn`
  >- (simp[] >> strip_tac >>
      `shape_step F jump_label_ok
         (\st. T /\ EVERY (label_or_plain st) [Lit 0w; Lit 0w] /\
                EVERY (plain_operand st) (MAP Var []))
         (emit_inst REVERT [Lit 0w; Lit 0w] []) (\x st. T)` by
        (ho_match_mp_tac shape_step_emit_inst >>
         simp[shape_stable_def, lowered_inst_ok_def, mk_inst_def,
              raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
              is_param_opcode_def, is_read0_opcode_def, label_positions_ok_def,
              operand_case_not_label, is_terminator_def,
              stackPlanTypesTheory.is_label_operand_def]) >>
      gvs[shape_step_def] >> first_x_assum drule >>
      simp[label_or_plain_def, plain_operand_def,
           stackPlanTypesTheory.is_label_operand_def]) >>
  PairCases_on `x` >> simp[fallback_shape_ok_def] >> strip_tac >>
  drule_all (SRULE [fallback_shape_ok_def] compile_fallback_body_shape) >>
  rewrite_tac[shape_step_def] >> disch_then drule >> simp[] >> strip_tac >>
  gvs[shape_extends_def, jump_label_ok_def, EVERY_MEM] >> metis_tac[]
QED

Theorem runtime_entry_prefix_states:
  compile_generate_runtime selectors external_fns internal_fns fallback_fn
    Linear bucket_count fn_metadata_bytes dense_buckets entry_info st0 =
      ((), st_final) /\ shape_state st0 /\
  EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) selectors /\
  EVERY external_fn_shape_ok external_fns /\ fallback_shape_ok fallback_fn /\
  EVERY internal_fn_shape_ok internal_fns /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors internal_fns) ==>
  ?fallback_lbl s1 s2 s3 old s4 entry_st ir segs.
    fresh_label "fallback" st0 = (fallback_lbl, s1) /\
    compile_selector_dispatch_linear
      (MAP (\(sel,lbl,z). (sel,lbl)) selectors) fallback_lbl s1 = ((), s2) /\
    compile_external_fn_bodies external_fns s2 = ((), s3) /\
    new_block fallback_lbl s3 = (old, s4) /\
    (case fallback_fn of
       NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
     | SOME (ce,pay,nr,key,trans,view,ss,ty) =>
         compile_fallback_body ce pay nr key trans view ss ty) s4 = ((), entry_st) /\
    compile_internal_fn_bodies internal_fns entry_st = (ir, st_final) /\
    shape_state s2 /\ cs_extends st0 s2 /\ cs_extends s3 entry_st /\
    shape_state entry_st /\ shape_extends F jump_label_ok st0 entry_st /\
    all_blocks st_final = all_blocks entry_st ++ FLAT segs /\
    LIST_REL internal_segment_ok (internal_fn_descriptors internal_fns) segs
Proof
  strip_tac >> drule compile_generate_runtime_linear_split >> strip_tac >>
  drule_all runtime_dispatch_prefix_shape >> strip_tac >>
  qspec_then `external_fns` mp_tac compile_external_fn_bodies_shape >>
  simp[shape_step_def] >> disch_then drule >> simp[] >> strip_tac >>
  qspecl_then [`F`, `jump_label_ok`, `\st. T`, `fallback_lbl`]
    mp_tac shape_step_new_block >>
  simp[shape_stable_def, shape_step_def] >> disch_then drule >> simp[] >> strip_tac >>
  drule_all runtime_fallback_interval_shape >> strip_tac >>
  drule_all compile_internal_fn_bodies_shape >> strip_tac >>
  qexists `segs` >>
  simp[] >>
  `shape_extends F jump_label_ok s3 entry_st` by
    (irule shape_extends_trans >> qexists `s4` >> simp[]) >>
  `shape_extends F jump_label_ok st0 s3` by
    (irule shape_extends_trans >> qexists `s2` >> simp[]) >>
  `shape_extends F jump_label_ok st0 entry_st` by
    (irule shape_extends_trans >> qexists `s3` >> simp[]) >>
  `cs_extends st0 s2` by
    (qpat_x_assum `shape_extends _ _ st0 s2` mp_tac >> simp[shape_extends_def]) >>
  `cs_extends s3 entry_st` by
    (qpat_x_assum `shape_extends _ _ s3 entry_st` mp_tac >> simp[shape_extends_def]) >>
  simp[]
QED

Theorem runtime_selected_body_states:
  compile_generate_runtime selectors external_fns internal_fns fallback_fn
    Linear bucket_count fn_metadata_bytes dense_buckets entry_info st0 =
      ((), st_final) /\ shape_state st0 /\
  EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) selectors /\
  EVERY external_fn_shape_ok external_fns /\ fallback_shape_ok fallback_fn /\
  EVERY internal_fn_shape_ok internal_fns /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors internal_fns) /\
  MEM (lbl, ce, args, cds, pay, nr, key, trans, view, fbody, rt) external_fns ==>
  ?entry_st sd selected_ce sa se ir segs.
    compile_register_positional_args ce args 4 sd = (selected_ce, sa) /\
    compile_guarded_body selected_ce nr key trans view fbody rt sa = ((), se) /\
    cs_extends st0 sa /\ cs_extends sa se /\ cs_extends se entry_st /\
    shape_state entry_st /\ shape_extends F jump_label_ok st0 entry_st /\
    compile_internal_fn_bodies internal_fns entry_st = (ir, st_final) /\
    all_blocks st_final = all_blocks entry_st ++ FLAT segs /\
    LIST_REL internal_segment_ok (internal_fn_descriptors internal_fns) segs
Proof
  strip_tac >> drule_all runtime_entry_prefix_states >> strip_tac >>
  drule_all compile_external_member_interval >> strip_tac >>
  rename1 `compile_register_positional_args ce args 4 sd = (selected_ce, sa)` >>
  rename1 `compile_guarded_body selected_ce nr key trans view fbody rt sa = ((), se)` >>
  `cs_extends st0 sa` by
    (irule cs_extends_trans >> qexists `s2` >> simp[]) >>
  `cs_extends se entry_st` by
    (irule cs_extends_trans >> qexists `s3` >> simp[]) >>
  qexistsl [`entry_st`, `sd`, `selected_ce`, `sa`, `se`, `ir`, `segs`] >> simp[]
QED
