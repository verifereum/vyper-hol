(* Finish Pop at the very place reached by the counted target evaluation. *)
Theory bodyPopSuffixMods
Ancestors
  bodyPopReachedMemoryArmMods bodyPopReachedSlotArmMods
  bodyPopReachedMemoryDynarrayMods bodyPopExitPathsMods bodyPopInputsMods
  bodyWriteTargetStageMods exprSimHypsDefs popTargetPre allocLimits
  vyperStorageFootprint

Theorem pop_reached_not_immutable[local]:
  expr_body_pre_mods mods cenv cx env (Pop ann bt) es /\
  write_target_post_mods H D lo d ctx func cenv cx bt es sa sm s0 ee
    (PlaceR (ImmutablePlace owner id path)) (Type aty) dst G0 tn0 G tn t ==>
  F
Proof
  strip_tac >> drule_then strip_assume_tac write_target_immutable_view_mods >>
  `target_in_immutables cenv.ce_module_vars bt` by
    (simp[target_in_immutables_root] >> qexists `off` >> simp[]) >>
  fs[expr_body_pre_mods_def,alloc_limits_expr_def]
QED

Theorem pop_place_suffix_mods:
  contract_inv mods exps ctx cenv cx /\
  expr_body_pre_mods mods cenv cx env (Pop ann bt) es /\
  compile_expr cenv ty (Pop ann bt) sa = (vv,sb) /\
  ci_mono sa sm /\ ci_mono sm sb /\ fn_has_code sm sb func /\
  gas_admissible (eval_expr cx (Pop ann bt)) expr_vv_res_ok es /\
  write_target_entry_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx bt es st0 sa sm shadow_sa shadow_sm dst s0 G0 tn0 /\
  (!tail. eval_target_place cx bt
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL p,ee with gas_obs := tail)) /\
  storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\
  (!id path. p = MemoryPlace id path ==>
     ?entry v. lookup_scopes id ee.scopes = SOME entry /\
               evaluate_subscripts entry.type entry.value path = INL v) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     write_target_post_mods H (DF H) lo d ctx func cenv cx bt es sa sm s0
       ee (PlaceR p) (Type (ArrayT ann (Dynamic cap))) dst G0 tn0 G tn t) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (pop_place cx p) (ee,t,G,tn)
    (\H res ef G' tn' u. ?tv. res = INL tv /\
      vv_post_mods H ctx func cenv cx (Pop ann bt) es sa sb s0 ef tv vv u /\
      vv_store_bound cx (post_value_type cenv (Pop ann bt))
        (lowered_value_type cenv (Pop ann bt)) ef tv vv u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ef G' tn' u /\
      ptr_vv_ok cx (post_value_type cenv (Pop ann bt)) tv vv ef G' tn' u /\
      (!v. tv = Value v /\ ~is_word_type (post_value_type cenv (Pop ann bt)) /\
           ~is_bytestring_type (post_value_type cenv (Pop ann bt)) ==>
           vv_own cenv cx (post_value_type cenv (Pop ann bt)) sa sb ef tv vv u /\
           (!t' ptr. vv = LocatedValue t' ptr ==> ptr.ptr_location = LocMemory)) /\
      (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
       ?v. read_result cx tv ef = (INL v,ef) /\
           !rt w. evaluate_type (get_tenv cx) (post_value_type cenv (Pop ann bt)) = SOME rt /\
                  eval_operand (vv_operand vv) u = SOME w ==>
                  w2n w + type_memory_size rt <= lo /\
                  (!mem. mem_agree_outside tn'.t_mem u.vs_memory mem ==>
                         val_in_memory rt v (w2n w) mem)) /\
      (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type cenv (Pop ann bt)) ==>
                ptr_buf_ok cenv (Pop ann bt) op G' u) /\
      (!t' ptr. vv = LocatedValue t' ptr /\ ptr.ptr_location = LocMemory ==>
                ptr_buf_ok cenv (Pop ann bt) ptr.ptr_operand G' u) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn')
    (\H res ef gt r. expr_exit res r /\ halt_exit H cx ef res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `p`
  >~ [`pop_place cx (ImmutablePlace _ _ _)`]
  >- (`valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
        fs[storage_trace_domain_def] >>
      qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
        (drule_then assume_tac) >>
      drule_all_then CONTR_TAC pop_reached_not_immutable)
  >~ [`pop_place cx (StoragePlace _ _ _)`]
  >- (irule pop_reached_slot_arm_mods >>
      conj_tac >- (qexists `marks` >> first_assum ACCEPT_TAC) >>
      conj_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC pop_slot_static_exit_cc_static_mods) >>
      asm_simp_tac bool_ss [] >>
      conj_tac >- (qexists `ty` >> first_assum ACCEPT_TAC) >>
      conj_tac >- (qexistsl_tac [`env`,`exps`,`mods`] >> asm_simp_tac bool_ss []) >>
      qexistsl_tac [`cap`,`dst`,`shadow_func`,`shadow_sa`,`shadow_sm`,`sm`] >>
      asm_simp_tac bool_ss []) >>
  rename1 `pop_place cx (MemoryPlace id path)` >>
  irule pop_reached_memory_arm_mods >>
  conj_tac >- (qexists `marks` >> first_assum ACCEPT_TAC) >>
  conj_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC pop_reached_memory_dynarray_len_mods) >>
  conj_tac >-
    (qpat_assum `!i p. MemoryPlace id path = MemoryPlace i p ==> _`
       (qspecl_then [`id`,`path`] mp_tac) >> simp_tac bool_ss []) >>
  asm_simp_tac bool_ss [] >>
  conj_tac >- (qexists `ty` >> first_assum ACCEPT_TAC) >>
  conj_tac >- (qexistsl_tac [`env`,`exps`,`mods`] >> asm_simp_tac bool_ss []) >>
  qexistsl_tac [`cap`,`dst`,`shadow_func`,`shadow_sa`,`shadow_sm`,`sm`] >>
  asm_simp_tac bool_ss []
QED
