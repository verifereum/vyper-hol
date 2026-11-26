(* Compiler cuts shared by the linked Append and AugAssign rules. *)
Theory bodyPlacePairedStagesMods
Ancestors
  augAssignFullCodeStages stmtSimAppendResolved stmtSimAugAssignPlace
  gasShadowCompileStmtHelpers gasShadowCompilePure gasShadowCompileBase
  gasShadowCompileContext gasShadowCompileCallSupport gasShadowState gasShadow
  gasShadowStmtEnv gasShadowCompileStmtBase
  fragExec stmtLoweringMono exprLoweringProps compileEnv loweringPosts stmtLowering
  vyperInterpreter vyperState

(* These cuts do not inspect the active module or the simulation invariant. *)
Theorem augassign_paired_stages_mods =
  augAssignFullCodeStagesTheory.augassign_full_code_stages

Theorem augassign_source_stages_mods =
  stmtSimAugAssignPlaceTheory.aug_place_eval_cases

(* The RHS is entered only on the INL branch of the target evaluation. *)
Theorem append_source_stages_mods:
  eval_stmt cx (Append t e) =
    bind (eval_target_place cx t) (\p.
      bind (bind (eval_expr cx e) (read_result cx)) (append_place cx p))
Proof
  simp[Once evaluate_def, bind_assoc, SF ETA_ss]
QED

Theorem append_code_tail[local]:
  stmt_env cenv lc rt (Append t e) sa = (c,sf) /\
  compile_get_target_ptr compile_expr cenv t sa = (r,sp) /\
  loc = (case FST (SND r) of NONE => LocMemory | SOME l => l) /\
  elem = (case SND (SND r) of SOME (ValPT (ArrayT ty _)) => ty
                           | _ => BaseT (UintT 256)) /\
  cap = (case SND (SND r) of SOME (ValPT (ArrayT _ (Dynamic n))) => n
                          | _ => 0) ==>
  ?op sm. lower_value compile_expr cenv elem e sp = (op,sm) /\
    (if is_word_type elem then
       compile_dynarray_append cenv (FST r) op (word_scale loc)
         (elem_size_in_location cenv loc elem) elem (lowered_value_type cenv e)
         cap T loc sm = ((),sf)
     else
       ?tmp sc sd. compile_alloc_buffer (type_memory_bytes cenv elem) sm = (tmp,sc) /\
         compile_store_memory cenv op tmp.buf_operand elem (lowered_value_type cenv e)
           sc = ((),sd) /\
         compile_dynarray_append cenv (FST r) tmp.buf_operand (word_scale loc)
           (elem_size_in_location cenv loc elem) elem elem cap F loc sd = ((),sf))
Proof
  strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, Once compile_stmt_def] >>
  qpat_x_assum `loc = _` (SUBST1_TAC o SYM) >>
  qpat_x_assum `elem = _` (SUBST1_TAC o SYM) >>
  qpat_x_assum `cap = _` (SUBST1_TAC o SYM) >>
  Cases_on `lower_value compile_expr cenv elem e sp` >>
  rename1 `lower_value _ _ _ _ _ = (op,sm)` >> simp[] >>
  Cases_on `is_word_type elem` >> simp[comp_return_def]
  >- (pairarg_tac >> simp[] >> strip_tac >> gvs[]) >>
  Cases_on `compile_alloc_buffer (type_memory_bytes cenv elem) sm` >>
  rename1 `compile_alloc_buffer _ _ = (tmp,sc)` >> simp[] >>
  Cases_on `compile_store_memory cenv op tmp.buf_operand elem (lowered_value_type cenv e) sc` >>
  rename1 `compile_store_memory _ _ _ _ _ _ = (u,sd)` >>
  Cases_on `u` >> simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[]
QED

Theorem paired_result[local]:
  gas_shadow_compiles f g /\ gas_shadow_state a b /\
  f a = (x,c) /\ g b = (y,d) ==> x = y /\ gas_shadow_state c d
Proof
  strip_tac >>
  qpat_x_assum `gas_shadow_compiles _ _` (mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  disch_then drule >> simp[]
QED

Theorem cut_interval[local]:
  fn_has_code sa sf func /\ ci_mono sa sm /\ ci_mono sm sf ==>
  fn_has_code sa sm func /\ fn_has_code sm sf func
Proof
  strip_tac >> irule fn_has_code_split >> fs[ci_mono_def]
QED

Theorem append_copy_intervals[local]:
  fn_has_code sp sf func /\ ci_mono sp sm /\
  compile_alloc_buffer bytes sm = (tmp,sc) /\
  compile_store_memory cenv op tmp.buf_operand elem src_ty sc = ((),sd) /\
  compile_dynarray_append cenv dst tmp.buf_operand ws esz elem elem cap F loc sd = ((),sf) ==>
  fn_has_code sp sm func /\ fn_has_code sm sc func /\
  fn_has_code sc sd func /\ fn_has_code sd sf func
Proof
  strip_tac >>
  `ci_mono sm sc` by metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND] >>
  `ci_mono sc sd` by metis_tac[ci_mono_compile_store_memory, pairTheory.SND] >>
  `ci_mono sd sf` by metis_tac[ci_mono_compile_dynarray_append, pairTheory.SND] >>
  `ci_mono sc sf` by metis_tac[ci_mono_trans] >>
  `ci_mono sm sf` by metis_tac[ci_mono_trans] >>
  `fn_has_code sp sm func /\ fn_has_code sm sf func` by (irule cut_interval >> simp[]) >>
  `fn_has_code sm sc func /\ fn_has_code sc sf func` by (irule cut_interval >> simp[]) >>
  `fn_has_code sc sd func /\ fn_has_code sd sf func` by (irule cut_interval >> simp[]) >>
  simp[]
QED

(* The selectors also describe exactly what the compiler emits when the
   pointer result is not a typed dynamic array; that case is not assumed
   admissible by this compiler-only rule. *)
Theorem append_paired_stages_mods:
  stmt_env cenv lc rt (Append t e) sa = (c,sf) /\
  stmt_env (gas_shadow_env T cenv) lc rt (gas_shadow_stmt (Append t e))
    shadow_sa = (gas_shadow_env T c,shadow_sf) /\
  gas_shadow_state sa shadow_sa /\
  fn_has_code sa sf func /\ fn_has_code shadow_sa shadow_sf shadow_func ==>
  c = cenv /\ gas_shadow_state sf shadow_sf /\
  ?r sp shadow_sp loc elem cap op sm shadow_sm.
    compile_get_target_ptr compile_expr cenv t sa = (r,sp) /\
    compile_get_target_ptr compile_expr (gas_shadow_env T cenv) (gas_shadow_target t)
      shadow_sa = (r,shadow_sp) /\
    gas_shadow_state sp shadow_sp /\ ci_mono sa sp /\ ci_mono shadow_sa shadow_sp /\
    fn_has_code sa sp func /\ fn_has_code shadow_sa shadow_sp shadow_func /\
    loc = (case FST (SND r) of NONE => LocMemory | SOME l => l) /\
    elem = (case SND (SND r) of SOME (ValPT (ArrayT ty _)) => ty
                             | _ => BaseT (UintT 256)) /\
    cap = (case SND (SND r) of SOME (ValPT (ArrayT _ (Dynamic n))) => n
                            | _ => 0) /\
    lower_value compile_expr cenv elem e sp = (op,sm) /\
    lower_value compile_expr (gas_shadow_env T cenv) elem (gas_shadow_expr e)
      shadow_sp = (op,shadow_sm) /\
    gas_shadow_state sm shadow_sm /\ ci_mono sp sm /\ ci_mono shadow_sp shadow_sm /\
    fn_has_code sp sm func /\ fn_has_code shadow_sp shadow_sm shadow_func /\
    (if is_word_type elem then
       compile_dynarray_append cenv (FST r) op (word_scale loc)
         (elem_size_in_location cenv loc elem) elem (lowered_value_type cenv e)
         cap T loc sm = ((),sf) /\
       compile_dynarray_append cenv (FST r) op (word_scale loc)
         (elem_size_in_location cenv loc elem) elem (lowered_value_type cenv e)
         cap T loc shadow_sm = ((),shadow_sf) /\
       fn_has_code sm sf func /\ fn_has_code shadow_sm shadow_sf shadow_func
     else ?tmp sc sd shadow_sc shadow_sd.
       compile_alloc_buffer (type_memory_bytes cenv elem) sm = (tmp,sc) /\
       compile_alloc_buffer (type_memory_bytes cenv elem) shadow_sm = (tmp,shadow_sc) /\
       gas_shadow_state sc shadow_sc /\ gas_shadow_state sd shadow_sd /\
       compile_store_memory cenv op tmp.buf_operand elem (lowered_value_type cenv e)
         sc = ((),sd) /\
       compile_store_memory cenv op tmp.buf_operand elem (lowered_value_type cenv e)
         shadow_sc = ((),shadow_sd) /\
       compile_dynarray_append cenv (FST r) tmp.buf_operand (word_scale loc)
         (elem_size_in_location cenv loc elem) elem elem cap F loc sd = ((),sf) /\
       compile_dynarray_append cenv (FST r) tmp.buf_operand (word_scale loc)
         (elem_size_in_location cenv loc elem) elem elem cap F loc shadow_sd = ((),shadow_sf) /\
       fn_has_code sm sc func /\ fn_has_code shadow_sm shadow_sc shadow_func /\
       fn_has_code sc sd func /\ fn_has_code shadow_sc shadow_sd shadow_func /\
       fn_has_code sd sf func /\ fn_has_code shadow_sd shadow_sf shadow_func)
Proof
  strip_tac >>
  `gas_shadow_state sf shadow_sf` by
    (qspec_then `Append t e` mp_tac (Q.INST [`sd` |-> `T`] gas_shadow_stmt_env_env) >>
     disch_then (qspecl_then [`cenv`,`lc`,`rt`] mp_tac) >>
     simp[gas_shadow_compiles_env_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >>
     simp[]) >>
  drule_all_then strip_assume_tac append_resolved_target_prefix >>
  qpat_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _`
    (mp_then (Pat `stmt_env _ _ _ _ _ = _`) mp_tac append_resolved_target_prefix o
     SIMP_RULE bool_ss [gas_shadow_stmt_def]) >>
  disch_then (drule_then strip_assume_tac) >> gvs[] >>
  rename1 `stmt_env cenv lc rt (Append t e) sa = (_,sf)` >>
  rename1 `compile_get_target_ptr compile_expr cenv t sa = (r,sp)` >>
  rename1 `compile_get_target_ptr _ _ (gas_shadow_target t) shadow_sa = (sr,shadow_sp)` >>
  `r = sr /\ gas_shadow_state sp shadow_sp` by
    (irule paired_result >> rpt (first_assum (irule_at Any)) >>
     simp[gas_shadow_stmt_get_target_ptr_env]) >>
  gvs[] >>
  rename1 `compile_get_target_ptr compile_expr cenv t sa = (r,sp)` >>
  qabbrev_tac `loc = case FST (SND r) of NONE => LocMemory | SOME l => l` >>
  qabbrev_tac `elem = case SND (SND r) of SOME (ValPT (ArrayT ty _)) => ty
                                        | _ => BaseT (UintT 256)` >>
  qabbrev_tac `cap = case SND (SND r) of SOME (ValPT (ArrayT _ (Dynamic n))) => n
                                       | _ => 0` >>
  qpat_assum `stmt_env _ _ _ (Append t e) _ = _`
    (mp_then (Pat `stmt_env _ _ _ _ _ = _`) mp_tac
      append_code_tail) >>
  disch_then (drule_then (qspecl_then [`loc`,`elem`,`cap`] mp_tac)) >>
  (impl_tac >- simp[Abbr `loc`, Abbr `elem`, Abbr `cap`]) >> strip_tac >>
  qpat_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _`
    (mp_then (Pat `stmt_env _ _ _ _ _ = _`) mp_tac append_code_tail o
     SIMP_RULE bool_ss [gas_shadow_stmt_def]) >>
  disch_then (drule_then (qspecl_then [`loc`,`elem`,`cap`] mp_tac)) >>
  (impl_tac >- simp[Abbr `loc`, Abbr `elem`, Abbr `cap`]) >> simp[] >> strip_tac >>
  rename1 `lower_value compile_expr cenv elem e sp = (op,sm)` >>
  rename1 `lower_value _ _ _ (gas_shadow_expr e) shadow_sp = (shadow_op,shadow_sm)` >>
  `op = shadow_op /\ gas_shadow_state sm shadow_sm` by
    (irule paired_result >> rpt (first_assum (irule_at Any)) >>
     simp[gas_shadow_stmt_lower_value_env]) >>
  qexists_tac `shadow_sm` >> simp[] >>
  `ci_mono sp sm /\ ci_mono shadow_sp shadow_sm` by
    metis_tac[ci_mono_lower_value_compile_expr, pairTheory.SND] >>
  simp[] >> Cases_on `is_word_type elem` >> fs[]
  >- (`ci_mono sm sf /\ ci_mono shadow_sm shadow_sf` by
        metis_tac[ci_mono_compile_dynarray_append, pairTheory.SND] >>
      `fn_has_code sp sm func /\ fn_has_code sm sf func` by
        (irule cut_interval >> simp[]) >>
      `fn_has_code shadow_sp shadow_sm shadow_func /\ fn_has_code shadow_sm shadow_sf shadow_func` by
        (irule cut_interval >> simp[]) >> simp[]) >>
  rename1 `compile_alloc_buffer _ sm = (tmp,sc)` >>
  rename1 `compile_alloc_buffer _ shadow_sm = (shadow_tmp,shadow_sc)` >>
  `tmp = shadow_tmp /\ gas_shadow_state sc shadow_sc` by
    (irule paired_result >> rpt (first_assum (irule_at Any)) >>
     simp[gas_shadow_compiles_alloc_buffer]) >>
  gvs[] >>
  rename1 `compile_store_memory _ _ _ _ _ sc = ((),sd)` >>
  rename1 `compile_store_memory _ _ _ _ _ shadow_sc = ((),shadow_sd)` >>
  `gas_shadow_state sd shadow_sd` by
    (`() = () /\ gas_shadow_state sd shadow_sd` suffices_by simp[] >>
     irule paired_result >> rpt (first_assum (irule_at Any)) >>
     simp[gas_shadow_compiles_store_memory]) >>
  `fn_has_code sp sm func /\ fn_has_code sm sc func /\
   fn_has_code sc sd func /\ fn_has_code sd sf func` by
    (irule append_copy_intervals >> rpt (first_assum (irule_at Any))) >>
  `fn_has_code shadow_sp shadow_sm shadow_func /\ fn_has_code shadow_sm shadow_sc shadow_func /\
   fn_has_code shadow_sc shadow_sd shadow_func /\ fn_has_code shadow_sd shadow_sf shadow_func` by
    (irule append_copy_intervals >> rpt (first_assum (irule_at Any))) >>
  simp[]
QED
