Theory linkedExternalFrameRet
Ancestors
  bodyFullPostsMods bodySim compileEnv compileVyper exprLowering e2eDefs e2eModsDefs
  externalReturnPackage linkedReturnAbiLayout gasOutcomeFullPostMods linkedExternalReturnNone
  linkedExternalReturnValued sourceUnitExecutionMods vyperInterpreter
  vyperTypeSystem vyperTypeCallGraph vyperValueOperation vyperValue context words list pair finite_map

Theorem linked_external_frame_ret_ok_full:
  ce.ce_modules = mods /\
  ce.ce_is_external /\ ~ce.ce_is_ctor /\
  ce.ce_return_pc = NONE /\ ce.ce_ctor_exit_label = NONE /\
  ce.ce_nonreentrant = (nr,global_nonreentrant_slot,T,mut = View) /\
  ce.ce_type_env = get_tenv cx /\ type_env_all_modules mods = get_tenv cx /\
  (ret <> NoneT ==>
    ce.ce_ret_enc_info = (update_cenv_ret_abi ce ret).ce_ret_enc_info /\
    ce.ce_max_return_size = (update_cenv_ret_abi ce ret).ce_max_return_size /\
    assignable_type (get_tenv cx) ret /\
    (ce.ce_raw_return ==> ?n. ret = BaseT (BytesT (Dynamic n))) /\
    type_memory_bytes ce ret < 2 ** 64) /\
  (nr ==> is_view_mut mut = (mut = View)) /\
  (nr /\ mut <> View ==> ~cx.txn.is_static /\
    cx.nonreentrant_slot = SOME global_nonreentrant_slot) /\
  ALOOKUP mods (ALOOKUP exps cx.txn.function_name) = SOME tops /\
  ce.ce_raw_return =
    lookup_raw_return_or_F (ALOOKUP exps cx.txn.function_name)
      cx.txn.function_name External tops /\
  external_return_type_mods mods exps cx.txn.function_name = ret /\
  (ret = NoneT ==> tx_return_bytes_mods mods exps cx.txn NoneV []) ==>
  frame_ret_ok_full_mods mods (DF,0,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx (\H v ee gt r. ?tv v' us.
      evaluate_type (get_tenv cx) ret = SOME tv /\ safe_cast tv v = SOME v' /\
      unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),us) /\
      external_call_result_rel_mods H mods exps ret cx.txn
        (INL v', finalize_pending_deletions
          (abstract_machine_from_state cx.sources caller_exports cx.layouts us),
         us.requests) r) ce ret
Proof
  rewrite_tac[frame_ret_ok_full_mods_def] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule_then (map_every assume_tac o CONJUNCTS) return_same_frame_metadata >>
  `cenv'.ce_modules = mods /\ cenv'.ce_ctor_exit_label = NONE` by
    (qpat_assum `same_frame ce cenv'`
       (strip_assume_tac o SIMP_RULE (srw_ss())
          [same_frame_def, compile_env_component_equality]) >>
     asm_rewrite_tac[]) >>
  Cases_on `eo`
  >- (`ret = NoneT` by
        (qpat_assum `IS_SOME (type_stmt env ret (Return NONE))` mp_tac >>
         Cases_on `ret = NoneT` >> simp[NoAsms, type_stmt_def]) >>
      qpat_assum `ret = NoneT` SUBST_ALL_TAC >>
      simp_tac bool_ss [evaluate_type_def, optionTheory.SOME_11] >>
      qmatch_goalsub_abbrev_tac `stmt_frag_full_mods _ _ _ RetQ _ _ _ _ _` >>
      `RetQ = (\H v ee gt r. ?us.
           safe_cast NoneTV v = SOME NoneV /\
           unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),us) /\
           external_call_result_rel_mods H mods exps NoneT cx.txn
             (INL NoneV, finalize_pending_deletions
               (abstract_machine_from_state cx.sources caller_exports cx.layouts us),
              us.requests) r)` by
        (simp[NoAsms, Abbr `RetQ`, FUN_EQ_THM, safe_cast_def] >>
         qx_genl_tac [`H`,`value`,`ee`,`out`] >>
         Cases_on `value` >> simp[NoAsms]) >>
      pop_assum SUBST1_TAC >>
      simp_tac bool_ss [optionTheory.OPTION_MAP_DEF] >>
      irule linked_external_return_none_frag >>
      rpt conj_tac
      >- (qpat_assum `cenv'.ce_is_ctor = ce.ce_is_ctor` SUBST1_TAC >>
          first_assum ACCEPT_TAC)
      >- first_assum ACCEPT_TAC
      >- (qpat_assum `cenv'.ce_return_pc = ce.ce_return_pc` SUBST1_TAC >>
          first_assum ACCEPT_TAC)
      >- (qpat_assum `cenv'.ce_nonreentrant = ce.ce_nonreentrant` SUBST1_TAC >>
          first_assum ACCEPT_TAC)
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC >>
      qpat_assum `NoneT = NoneT ==> tx_return_bytes_mods _ _ _ _ _` (ACCEPT_TAC o SIMP_RULE bool_ss [])) >>
  rename1 `stmt_exprs_ok cenv' (Return (SOME e))` >>
  `ret <> NoneT` by
    (qpat_assum `IS_SOME (type_stmt env ret (Return (SOME e)))` mp_tac >>
     Cases_on `ret = NoneT` >> simp[NoAsms, type_stmt_def]) >>
  qpat_assum `ret <> NoneT ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `type_memory_bytes cenv' = type_memory_bytes ce` by
    (irule type_memory_bytes_frame >> first_assum ACCEPT_TAC) >>
  `type_to_abi_enc_info ce.ce_struct_fields cenv' ret =
    type_to_abi_enc_info ce.ce_struct_fields ce ret` by
    (irule type_to_abi_enc_info_struct_fields >> first_assum ACCEPT_TAC) >>
  `type_memory_bytes cenv' ret = type_memory_bytes ce ret` by
    first_assum (fn size => ACCEPT_TAC (Q.AP_THM size `ret`)) >>
  `cenv'.ce_ret_enc_info = (update_cenv_ret_abi cenv' ret).ce_ret_enc_info /\
    cenv'.ce_max_return_size = (update_cenv_ret_abi cenv' ret).ce_max_return_size` by
    (qpat_assum `cenv'.ce_ret_enc_info = ce.ce_ret_enc_info` SUBST1_TAC >>
     qpat_assum `cenv'.ce_max_return_size = ce.ce_max_return_size` SUBST1_TAC >>
     qpat_assum `ce.ce_ret_enc_info = (update_cenv_ret_abi ce ret).ce_ret_enc_info` SUBST1_TAC >>
     qpat_assum `ce.ce_max_return_size = (update_cenv_ret_abi ce ret).ce_max_return_size` SUBST1_TAC >>
     qpat_assum `cenv'.ce_struct_fields = ce.ce_struct_fields`
       (fn fields => simp[NoAsms, update_cenv_ret_abi_def, LET_THM, fields]) >>
     qpat_assum `type_to_abi_enc_info ce.ce_struct_fields cenv' ret = _`
       (fn plan => PURE_REWRITE_TAC [plan]) >>
     qpat_assum `type_memory_bytes cenv' ret = type_memory_bytes ce ret`
       (fn size => simp[NoAsms, size])) >>
  qabbrev_tac `return_at = \(H:(bool # 256 word # type_value) list # num list) v us (ss:venom_state).
    external_call_result_rel_mods H mods exps ret cx.txn
      (INL v, finalize_pending_deletions
        (abstract_machine_from_state cx.sources caller_exports cx.layouts us),
       us.requests) (Halt ss)` >>
  qmatch_goalsub_abbrev_tac `stmt_frag_full_mods _ _ _ RetQ _ _ _ _ _` >>
  `RetQ = (\H v ee gt (r:exec_result). ?tv v' us (ss:venom_state).
       evaluate_type (get_tenv cx) ret = SOME tv /\ safe_cast tv v = SOME v' /\
       unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),us) /\
       r = Halt ss /\ return_at H v' us ss)` by
    (simp[NoAsms, Abbr `RetQ`, FUN_EQ_THM, Abbr `return_at`] >>
     qx_genl_tac [`H`,`value`,`ee`,`out`] >>
     Cases_on `out` >> simp[NoAsms, external_call_result_rel_mods_def, LET_THM]) >>
  pop_assum SUBST1_TAC >>
  simp_tac bool_ss [optionTheory.OPTION_MAP_DEF] >>
  irule return_valued_frag_full_mods >>
  asm_simp_tac (srw_ss()) [global_nonreentrant_slot_def, dimword_def, int_calls_stmt_def] >>
  conj_tac
  >- (qexists_tac `caller_exports` >>
      rpt gen_tac >> strip_tac >>
      qpat_assum `ALOOKUP mods (ALOOKUP exps cx.txn.function_name) = SOME tops`
        (fn tops_eq => simp[NoAsms, Abbr `return_at`, external_call_result_rel_mods_def,
          LET_THM, tops_eq]) >>
      `log_entry_corresponds (build_event_info_mods (type_env_all_modules mods) mods (K NONE))
           (type_env_all_modules mods) cx.txn.target = $=` by
        simp[NoAsms, FUN_EQ_THM, log_entry_corresponds_def] >>
      rpt conj_tac >>
      FIRST [first_assum ACCEPT_TAC,
        simp[NoAsms, finalize_pending_deletions_metadata, abstract_machine_from_state_def] >>
        first_assum ACCEPT_TAC,
        qpat_assum `log_entry_corresponds _ _ _ = $=` (fn logs =>
          simp[NoAsms, logs_correspond_def, logs, LIST_REL_eq,
            finalize_pending_deletions_metadata, abstract_machine_from_state_def]) >>
        first_assum ACCEPT_TAC]) >>
  conj_tac
  >- (strip_tac >>
      qpat_assum `type_memory_bytes ce ret < 2 ** 64`
        (ACCEPT_TAC o SIMP_RULE (srw_ss()) [])) >>
  conj_tac
  >- (qpat_assum `call_evaluation_safe cx (int_calls_stmt (Return (SOME e)))`
        (ACCEPT_TAC o PURE_REWRITE_RULE [int_calls_stmt_def, int_calls_expr_def])) >>
  qexists_tac `env` >> asm_rewrite_tac[]
QED
