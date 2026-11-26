(* Select the return fragment using the entered callee's frame metadata. *)
Theory bodySelectedReturnConventionMods
Ancestors
  bodySelectedVoidReturnMods bodySelectedWordReturnMods bodySelectedStackReturnMods
  bodySelectedBufferReturnMods bodySelectedUnlockTaintMods
  bodyInvariantFrameProps gasOutcomeFullPostMods stmtSimReturn typedCopyPtr
  bodyFullPostsMods bodyPtrDefs bodySim compileEnv loweringStateRelDefs
  vyperTypeSystem vyperState venomState pair words bodyInvSplit exprLoweringProps

Theorem selected_return_retq_weaken[local]:
  stmt_frag_full_mods (DF,lo,d,ctx,shctx,PG,func,shfunc)
    cx lctx Q ce m shm src es /\
  (!H v ee gt r. ee.scopes = [] /\ Q H v ee gt r ==> R H v ee gt r) ==>
  stmt_frag_full_mods (DF,lo,d,ctx,shctx,PG,func,shfunc)
    cx lctx R ce m shm src es
Proof
  pure_rewrite_tac[stmt_frag_full_mods_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  first_x_assum (drule_all_then assume_tac) >>
  irule gas_outcome_full_mods_post_source >> goal_assum (drule_at Any) >>
  simp[] >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  gen_tac >>
  qpat_assum `!tail. stmt_exit_ptr _ _ _ _ _` (qspec_then `tail` mp_tac) >>
  rewrite_tac[stmt_exit_ptr_def] >>
  disch_then (DISJ_CASES_THEN2 assume_tac strip_assume_tac)
  >- (disj1_tac >> first_assum ACCEPT_TAC) >>
  disj2_tac >> qexists `v` >> simp[] >>
  qpat_assum `!H v ee gt r. _ ==> R H v ee gt r` irule >> simp[]
QED

Theorem selected_return_frame_metadata[local]:
  same_frame ce site ==>
  site.ce_return_pc = ce.ce_return_pc /\
  site.ce_return_buf = ce.ce_return_buf /\
  site.ce_returns_count = ce.ce_returns_count /\
  site.ce_nonreentrant = ce.ce_nonreentrant /\
  site.ce_modules = ce.ce_modules /\
  site.ce_module_vars = ce.ce_module_vars /\
  site.ce_module_var_type = ce.ce_module_var_type /\
  site.ce_is_ctor = ce.ce_is_ctor
Proof
  simp[same_frame_def, compile_env_component_equality]
QED

Theorem selected_return_word_count[local]:
  is_word_type ty ==> returns_stack_count sft ty = 1
Proof
  Cases_on `ty` >> simp[returns_stack_count_def,is_word_type_def]
QED

Theorem selected_return_word_rebase[local]:
  same_frame ce site /\ ee.scopes = [] /\ intret_q H func site cx tv v ee r /\
  (!ir u. r = IntRet ir u ==>
    immutable_frame_mods func site cx (ee with scopes := []) u /\
    stor_taint_ok_at D (SND gt) u /\
    !i. i < lo /\ i IN (SND gt).t_mem ==>
      imm_section_dead_mods site (mem_bytes_at 0 lo u.vs_memory) i) ==>
  intret_q H func ce cx tv v ee r /\
  (!ir u. r = IntRet ir u ==>
    immutable_frame_mods func ce cx (ee with scopes := []) u /\
    stor_taint_ok_at D (SND gt) u /\
    !i. i < lo /\ i IN (SND gt).t_mem ==>
      imm_section_dead_mods ce (mem_bytes_at 0 lo u.vs_memory) i)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then strip_assume_tac selected_return_frame_metadata >>
  qpat_x_assum `intret_q _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [intret_q_def, result_rel_def]) >>
  `return_unlock_state site s = return_unlock_state ce s` by
    simp[return_unlock_state_def] >>
  conj_tac
  >- (simp[intret_q_def, result_rel_def] >>
      qexistsl [`s`,`i`] >> simp[] >>
      `state_rel H func ce cx (ee with scopes := []) s` by
        (irule constructor_exit_state_rel >> metis_tac[]) >>
      `ee with scopes := [] = ee` by simp[vyperStateTheory.evaluation_state_component_equality] >>
      fs[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!ir u. r = IntRet ir u ==> _` (drule_then strip_assume_tac) >>
  simp[] >> conj_tac
  >- (qpat_assum `immutable_frame_mods _ site _ _ u` mp_tac >>
      map_every (fn p => qpat_assum p mp_tac)
        [`site.ce_is_ctor = _`, `site.ce_module_var_type = _`,
         `site.ce_module_vars = _`, `site.ce_modules = _`] >>
      POP_ASSUM_LIST (K ALL_TAC) >> ntac 4 disch_tac >>
      simp_tac (srw_ss())
        [immutable_frame_mods_def, immutables_rel_mods_def, immutable_alloca_sep_mods_def,
         immutables_rel_def, immutable_alloca_sep_def, immutable_decl_sep_def,
         local_region_def, lookup_scopes_def] >>
      asm_rewrite_tac []) >>
  qpat_assum `!i. i < lo /\ _ ==> imm_section_dead_mods _ _ _` mp_tac >>
  pure_rewrite_tac[imm_section_dead_mods_def] >>
  qpat_assum `site.ce_modules = _` (pure_once_rewrite_tac o single) >>
  qpat_assum `site.ce_module_vars = _` (pure_once_rewrite_tac o single) >> simp[]
QED

fun selected_plain_retq c =
  ``\(H:(bool # bytes32 # type_value) list # num list) v ee
     (gt:(string |-> num # num) # taint) r. intret_q H func ^c cx tv v ee r /\
      !ir u. r = IntRet ir u ==>
        immutable_frame_mods func ^c cx (ee with scopes := []) u /\
        stor_taint_ok_at (DF H) (SND gt) u /\
        !i. i < lo /\ i IN (SND gt).t_mem ==>
          imm_section_dead_mods ^c (mem_bytes_at 0 lo u.vs_memory) i``;

val frame_plain_retq = selected_plain_retq ``ce:compile_env``;
val site_plain_retq = selected_plain_retq ``site:compile_env``;
val frame_buffer_retq =
  ``\(H:(bool # bytes32 # type_value) list # num list) v ee
     (gt:(string |-> num # num) # taint) r. intret_q H func ce cx tv v ee r /\
      !ir u. r = IntRet ir u ==>
        (!mem. mem_agree_outside (SND gt).t_mem u.vs_memory mem ==>
          val_in_memory tv v (w2n (bw:bytes32)) mem) /\
        immutable_frame_mods func ce cx (ee with scopes := []) u /\
        stor_taint_ok_at (DF H) (SND gt) u /\
        !i. i < lo /\ i IN (SND gt).t_mem ==>
          imm_section_dead_mods ce (mem_bytes_at 0 lo u.vs_memory) i``;

Theorem selected_frame_ret_ok_mods:
  contract_inv mods exps ctx ce cx /\
  ce.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  ce.ce_returns_count = returns_stack_count
    (\k. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields k)) ty /\
  (has_rb <=> ce.ce_returns_count = 0 /\ ty <> NoneT) /\
  (~has_rb ==> ce.ce_return_buf = NONE) /\
  (ty <> NoneT ==> evaluate_type (get_tenv cx) ty = SOME tv) /\
  (has_rb ==> lo <= w2n bw /\ 0 < type_memory_size tv /\
              type_memory_size tv + 64 < dimword (:256)) /\
  ((FST ce.ce_nonreentrant /\ ~SND (SND (SND ce.ce_nonreentrant))) ==>
    ~cx.txn.is_static /\ FST (SND (SND ce.ce_nonreentrant))) /\
  (!H v ee gt r. intret_q H func ce cx tv v ee r /\
    (!ir u. r = IntRet ir u ==>
      immutable_frame_mods func ce cx (ee with scopes := []) u /\
      stor_taint_ok_at (DF H) (SND gt) u /\
      (!i. i < lo /\ i IN (SND gt).t_mem ==>
        imm_section_dead_mods ce (mem_bytes_at 0 lo u.vs_memory) i) /\
      (has_rb ==> !mem. mem_agree_outside (SND gt).t_mem u.vs_memory mem ==>
        val_in_memory tv v (w2n bw) mem)) ==> RetQ H v ee gt r) ==>
  frame_ret_ok_full_mods mods
    (DF,lo,(if has_rb then SOME (bw,type_memory_size tv) else NONE),
     ctx,shctx,PG,func,shfunc) cx RetQ ce ty
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `is_word_type ty ==> ce.ce_returns_count = 1` by
    simp[selected_return_word_count] >>
  pure_rewrite_tac[frame_ret_ok_full_mods_def] >>
  rpt gen_tac >> rename1 `same_frame ce site` >> strip_tac >>
  drule_then strip_assume_tac selected_return_frame_metadata >>
  Cases_on `eo`
  >- suspend "void" >>
  rename1 `Return (SOME e)` >>
  `ty <> NoneT` by fs[type_stmt_return_some_iff] >>
  `evaluate_type (get_tenv cx) ty = SOME tv` by simp[] >>
  Cases_on `has_rb`
  >- suspend "buffer" >>
  Cases_on `is_word_type ty`
  >- suspend "word" >>
  suspend "stack"
QED

Resume selected_frame_ret_ok_mods[void]:
  `ty = NoneT` by fs[type_stmt_def, AllCaseEqs()] >>
  `~has_rb /\ ce.ce_returns_count = 0` by fs[returns_stack_count_def] >>
  gvs[] >>
  irule selected_return_retq_weaken >> qexists `^frame_plain_retq` >>
  conj_tac
  >- (rpt gen_tac >> BETA_TAC >> strip_tac >> first_x_assum irule >> simp[]) >>
  irule selected_void_return_frag_mods >> simp[] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `FST site.ce_nonreentrant /\ ~SND (SND (SND site.ce_nonreentrant)) ==>
     FST (SND (SND site.ce_nonreentrant))` by simp[] >>
  drule_all selected_unlock_exit_taint_mods >> simp[]
QED

Resume selected_frame_ret_ok_mods[buffer]:
  `ce.ce_returns_count = 0` by fs[] >>
  `~is_word_type ty` by fs[] >>
  fs[] >>
  `contract_inv mods exps ctx site cx` by
    (drule_then strip_assume_tac body_invariants_same_frame >> simp[]) >>
  irule selected_return_retq_weaken >> qexists `^frame_buffer_retq` >>
  conj_tac
  >- (rpt gen_tac >> BETA_TAC >> strip_tac >> first_x_assum irule >>
      simp[] >> rpt gen_tac >> disch_tac >> first_x_assum drule >> simp[]) >>
  irule selected_buffer_return_frag_mods >>
  simp[] >> qexistsl [`env`,`exps`,`mods`] >> simp[]
QED

Resume selected_frame_ret_ok_mods[word]:
  `ce.ce_returns_count = 1 /\ ce.ce_return_buf = NONE` by simp[] >>
  gvs[] >>
  irule selected_return_retq_weaken >> qexists `^site_plain_retq` >>
  conj_tac
  >- (rpt gen_tac >> BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
      qpat_assum `!H v ee gt r. _ ==> RetQ H v ee gt r` irule >>
      drule_all_then strip_assume_tac selected_return_word_rebase >> simp[]) >>
  irule selected_word_return_frag_mods >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      drule_all selected_unlock_exit_taint_mods >> simp[]) >>
  qexists `env` >> simp[]
QED

Resume selected_frame_ret_ok_mods[stack]:
  `0 < ce.ce_returns_count /\ ce.ce_return_buf = NONE` by
    (conj_tac >- (CCONTR_TAC >> gvs[]) >> simp[]) >>
  gvs[] >>
  irule selected_return_retq_weaken >> qexists `^frame_plain_retq` >>
  conj_tac
  >- (rpt gen_tac >> BETA_TAC >> strip_tac >> first_x_assum irule >> simp[]) >>
  irule selected_stack_return_frag_mods >>
  simp[] >> qexistsl [`env`,`mods`] >> simp[]
QED

Finalise selected_frame_ret_ok_mods
