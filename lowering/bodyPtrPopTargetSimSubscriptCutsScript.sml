Theory bodyPtrPopTargetSimSubscriptCuts
Ancestors
  bodyPtrPopTargetFactor exprLowering exprLoweringProps emitHelperProps
  stmtLoweringMono compileEnv targetPlaceSimDefs exprSimDefs exprSimHypsDefs
  vyperInterpreter vyperState gasContext pair

Theorem target_array_compile_parts_ptr:
  compile_get_target_ptr cfn ce bt sa = ((bop,loc,SOME (ValPT (ArrayT et bd))),sm) /\
  compile_get_target_ptr cfn ce (SubscriptTarget bt e) sa = (r,sb) ==>
  ?idx sn dst.
    lower_value cfn ce (expr_type e) e sm = (idx,sn) /\
    compile_array_subscript bop idx
      (case bd of Fixed _ => F | Dynamic _ => T)
      (case bd of Fixed n => n | Dynamic _ => 0)
      (word_scale (case loc of SOME l => l | NONE => LocMemory))
      (elem_size_in_location ce (case loc of SOME l => l | NONE => LocMemory) et)
      (is_signed_type (expr_type e))
      (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca
        (case loc of SOME l => l | NONE => LocMemory)) sn = (dst,sb) /\
    r = (dst,loc,SOME (ValPT et))
Proof
  strip_tac >> Cases_on `lower_value cfn ce (expr_type e) e sm` >>
  drule_all pop_compile_target_array_cut >>
  Cases_on `bd` >> simp[comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >> metis_tac[]
QED

Theorem target_subscript_base_admissible_ptr:
  gas_admissible (eval_base_place cx (SubscriptTarget bt e)) target_res_ok es ==>
  gas_admissible (eval_base_place cx bt) target_res_ok es
Proof
  simp[gas_admissible_def, Once evaluate_def, bind_def] >> rpt strip_tac >>
  Cases_on `res` >> simp[target_res_ok_def] >>
  first_x_assum (qspec_then `gs` mp_tac) >> simp[target_res_ok_def]
QED

(* General in the expression compiler: only its code-growth interface matters. *)
Theorem target_subscript_base_code_ptr:
  (!ce ty e st. ci_mono st (SND (cfn ce ty e st))) /\
  compile_get_target_ptr cfn ce bt sa = (rb,sm) /\
  compile_get_target_ptr cfn ce (SubscriptTarget bt e) sa = (r,sb) /\
  fn_has_code sa sb func ==>
  fn_has_code sa sm func /\ cs_extends sm sb
Proof
  strip_tac >>
  `!ce ty e st. ci_mono st (SND (lower_value cfn ce ty e st))` by
    metis_tac[ci_mono_lower_value_cfn] >>
  qpat_x_assum `compile_get_target_ptr _ _ (SubscriptTarget _ _) _ = _`
    (mp_tac o PURE_ONCE_REWRITE_RULE [compile_get_target_ptr_def]) >>
  qmatch_goalsub_abbrev_tac `comp_bind _ rest` >>
  `!result st. ci_mono st (SND (rest result st))` by
    (rpt gen_tac >> Cases_on `SND (SND result)`
     >- (simp[Abbr `rest`, LET_THM] >>
         irule ci_mono_bind >> simp[] >> rpt gen_tac >> BETA_TAC >>
         irule ci_mono_bind >>
         simp[ci_mono_compile_array_subscript, ci_mono_compile_ptr_load,
              ci_mono_comp_return]) >>
     rename1 `SND (SND result) = SOME pt` >> Cases_on `pt`
     >- (simp[Abbr `rest`, LET_THM] >>
         irule ci_mono_bind >> simp[] >> rpt gen_tac >> BETA_TAC >>
         irule ci_mono_bind >> reverse conj_tac
         >- (rpt gen_tac >> IF_CASES_TAC >>
             simp[ci_mono_compile_keccak256_key, ci_mono_comp_return]) >>
         rpt gen_tac >> BETA_TAC >> irule ci_mono_bind >>
         simp[ci_mono_compile_mapping_subscript, ci_mono_comp_return]) >>
     simp[Abbr `rest`, LET_THM] >>
     irule ci_mono_bind >> simp[] >> rpt gen_tac >> BETA_TAC >>
     irule ci_mono_bind >>
     simp[ci_mono_compile_array_subscript, ci_mono_compile_ptr_load,
          ci_mono_comp_return]) >>
  simp[comp_bind_def] >> strip_tac >>
  `ci_mono sm sb` by metis_tac[pairTheory.SND] >>
  `ci_mono sa sm` by metis_tac[ci_mono_compile_get_target_ptr_cfn, pairTheory.SND] >>
  gvs[ci_mono_def] >> metis_tac[fragExecTheory.fn_has_code_split]
QED
