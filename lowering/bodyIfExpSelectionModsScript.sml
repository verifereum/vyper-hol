(* Join the linked branch stages at the two source success equations. *)
Theory bodyIfExpSelectionMods
Ancestors
  bodyIfExpControlMods bodyIfExpConditionalMods bodyIfExpValueMods
  bodyIfExpWordReadMods bodyIfExpEqualLayoutMods bodyIfExpBytesArmMods
  bodyIfExpTypedArmMods exprBodyPreProps
Libs
  monadsyntax

Theorem ifexp_selection_full_mods:
  expr_type c = BaseT BoolT /\ expr_type a = t /\ expr_type b = t /\
  evaluate_type (get_tenv cx) t = SOME rty /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv.
       evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields) /\
  (!ty' tvt. evaluate_type (get_tenv cx) ty' = SOME tvt ==>
     type_memory_bytes cenv ty' = type_memory_size tvt) /\
  (~is_word_type t ==> type_memory_size rty < 2 ** 64) /\
  (!e. e = a \/ e = b ==>
    (is_word_type (post_value_type cenv e) ==> is_word_type t) /\
    (is_word_type t \/
     post_value_type cenv e = t /\
       (same_memory_layout cenv (lowered_value_type cenv e) t \/
        is_bytestring_type t /\ is_bytestring_type (lowered_value_type cenv e) /\
        arg_type_fits (lowered_value_type cenv e) t) \/
     post_value_type cenv e = lowered_value_type cenv e /\
       type_widens_to (get_tenv cx) (lowered_value_type cenv e) t /\
       (?stv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv))) /\
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (BaseT BoolT) c es /\
  (!gs v mid. bind (eval_expr cx c) (read_result cx) (es with gas_obs := gs) = (INL v,mid) ==>
    expr_body_pre_mods mods cenv cx env a mid /\ expr_body_pre_mods mods cenv cx env b mid /\
    expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty a mid /\
    expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty b mid /\
    (!e gs' raw ee. (e = a \/ e = b) /\
      eval_expr cx e (mid with gas_obs := gs') = (INL raw,ee) ==>
      eval_result_typed (env,cx,ee) raw (Type (expr_type e))) /\
    !e gs' v' ee. (e = a \/ e = b) /\
      bind (eval_expr cx e) (read_result cx) (mid with gas_obs := gs') = (INL v',ee) ==>
      value_has_type rty v' /\
      !ptv. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv ==>
        value_has_type ptv v') ==>
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty (IfExp t c a b) es /\
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty (IfExp t c a b) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> conj_asm1_tac
  >- (irule ifexp_vv_from_stages_mods >> reverse conj_tac
      >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      qexistsl [`env`,`rty`] >> pure_rewrite_tac[LET_THM] >>
      CONV_TAC (DEPTH_CONV BETA_CONV) >> reverse conj_tac
      >- (reverse conj_tac >- first_assum ACCEPT_TAC >>
          rpt gen_tac >> disch_tac >>
          qpat_assum `!gs v mid. bind _ _ _ = _ ==> _` (drule_then strip_assume_tac) >>
          rpt conj_tac >> first_assum ACCEPT_TAC) >>
      suspend "arm") >>
  irule ifexp_value_from_vv_mods >> first_assum ACCEPT_TAC
QED

Resume ifexp_selection_full_mods[arm]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!gs v mid. bind _ _ _ = _ ==> _` (drule_then strip_assume_tac) >>
  qmatch_goalsub_abbrev_tac `eval_expr cx arm` >>
  `expr_body_pre_mods mods cenv cx env arm mid` by
    (Cases_on `sel` >> simp[Abbr `arm`]) >>
  SUBGOAL_THEN ``arm:expr = a \/ arm = b`` ASSUME_TAC
  >- (Cases_on `sel` >> simp[Abbr `arm`]) >>
  pure_once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule (Q.INST [`rty` |-> `rty`, `env` |-> `env`] ifexp_arm_conditional_from_step_mods) >>
  qpat_assum `compile_expr cenv ty arm se = _` (irule_at Any) >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr _) shadow_se = _` (irule_at Any) >>
  qexistsl [`shadow_func`,`rty`,`env`] >>
  `~(jump_to lbl z).vs_halted /\ (jump_to lbl z).vs_current_bb = se.cs_current_bb /\
    (jump_to lbl z).vs_inst_idx = LENGTH se.cs_current_insts` by
    simp[venomStateTheory.jump_to_def] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    immutable_frame_mods func cenv cx mid (jump_to lbl z)` by
    (rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `!fn inst s. frag_reachable ctx func (jump_to lbl z) fn inst s ==>
     dalloca_fmp_headroom inst s` by first_assum ACCEPT_TAC >>
  simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      qpat_assum `!gs raw ee. eval_expr cx arm _ = _ ==> _`
        (drule_then mp_tac) >> simp[]) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  suspend "convert"
QED

Resume ifexp_selection_full_mods[convert]:
  qx_genl_tac [`gs_arm`,`ee`,`tv`,`u`,`G`,`tn`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!v. read_result cx tv ee = _ ==> _`
    (assume_tac o cj 1 o REWRITE_RULE [IMP_CONJ_THM, FORALL_AND_THM]) >>
  `cenv.ce_is_ctor /\ vv_location av = SOME LocCode ==>
    ?val. read_result cx tv ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type cenv arm) = SOME rt /\
        eval_operand (vv_operand av) u = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem u.vs_memory mem ==>
          val_in_memory rt val (w2n w) mem)` by
    (pure_once_rewrite_tac[arithmeticTheory.ADD_COMM] >> first_assum ACCEPT_TAC) >>
  Cases_on `is_word_type t`
  >- (qpat_assum `compile_expr cenv ty arm se = _`
        (mp_then Any mp_tac ifexp_arm_word_read_mods) >>
      disch_then (drule_at (Pat `compile_ifexp_arm _ _ _ _ _ = _`)) >>
      disch_then (drule_all_then mp_tac) >>
      disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`c`,`PG`]
        (qx_choosel_then [`v`,`fin`,`Gf`,`tf`] strip_assume_tac)) >>
      qexistsl [`v`,`fin`,`Gf`,`tf`] >> simp[] >> first_assum ACCEPT_TAC) >>
  `~is_word_type (post_value_type cenv arm)` by
    (qpat_assum `!e. e = a \/ e = b ==> _` (qspec_then `arm` mp_tac) >> simp[]) >>
  `type_memory_bytes cenv t = type_memory_size rty` by simp[] >>
  `type_memory_size rty < 2 ** 64` by simp[] >>
  qpat_assum `!e. e = a \/ e = b ==> _` (qspec_then `arm` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> simp[] >>
  Cases_on `same_memory_layout cenv (lowered_value_type cenv arm) t` >> simp[]
  >- (disch_tac >> suspend "same_layout") >>
  disch_then (DISJ_CASES_THEN strip_assume_tac)
  >- suspend "bytes" >> suspend "typed"
QED

Resume ifexp_selection_full_mods[same_layout]:
  `env.type_defs = get_tenv cx` by
    (drule_then assume_tac expr_body_pre_mods_inv >>
     drule_then assume_tac expr_sim_inv_mods_env >>
     drule_then ACCEPT_TAC vyperTypeEvalCaseProofsTheory.env_consistent_type_defs_get_tenv) >>
  `!tag x. av = StackValue tag x ==> ptr_buf_ok cenv arm x G u` by simp[] >>
  `!v. tv = Value v /\ ~is_word_type (post_value_type cenv arm) /\
       ~is_bytestring_type (post_value_type cenv arm) ==>
       vv_own cenv cx (post_value_type cenv arm) se sea ee tv av u` by
    (qx_gen_tac `v` >>
     qpat_assum `!w. tv = Value w /\ _ ==> vv_own _ _ _ _ _ _ (Value w) _ _`
       (qspec_then `v` mp_tac) >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  SUBGOAL_THEN ``post_value_type cenv arm = t \/
    post_value_type cenv arm = lowered_value_type cenv arm /\
    type_widens_to (get_tenv cx) (lowered_value_type cenv arm) t`` ASSUME_TAC
  >- (qpat_assum `post_value_type cenv arm = t \/ _` mp_tac >> metis_tac[]) >>
  `~expr_has_effect (IfExp t c a b) ==> ~expr_has_effect arm` by
    (qpat_assum `arm = a \/ arm = b` (DISJ_CASES_THEN SUBST1_TAC) >> simp[]) >>
  qpat_assum `compile_expr cenv ty arm se = _`
    (mp_then Any mp_tac ifexp_arm_equal_layout_from_unwrap_mods) >>
  disch_then (drule_at (Pat `compile_ifexp_arm _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_expr _ _ _ = (INL _,_)`)) >>
  disch_then (drule_all_then mp_tac) >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choosel_then [`v`,`fin`,`Gf`,`tf`] (map_every assume_tac o CONJUNCTS))) >>
  qexistsl [`v`,`fin`,`Gf`,`tf`] >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> pure_once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  qpat_assum `!rt w. evaluate_type _ _ = _ /\ eval_operand _ fin = _ ==> _`
    (qspecl_then [`rty`,`w`] mp_tac) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC
QED

Resume ifexp_selection_full_mods[typed]:
  `(is_word_type (post_value_type cenv arm) ==> is_word_type (expr_type arm))` by simp[] >>
  qpat_assum `compile_expr cenv ty arm se = _`
    (mp_then Any mp_tac ifexp_typed_arm_from_read_mods) >>
  disch_then (drule_at (Pat `compile_ifexp_arm _ _ _ _ _ = _`)) >>
  disch_then (drule_all_then mp_tac) >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`c`,`PG`]
    (qx_choosel_then [`v`,`fin`,`Gf`,`tf`] (map_every assume_tac o CONJUNCTS))) >>
  qexistsl [`v`,`fin`,`Gf`,`tf`] >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> pure_once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  qpat_assum `!rt w. evaluate_type _ _ = _ /\ eval_operand _ fin = _ ==> _`
    (qspecl_then [`rty`,`w`] mp_tac) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC
QED

Resume ifexp_selection_full_mods[bytes]:
  qpat_assum `compile_expr cenv ty arm se = _`
    (mp_then Any mp_tac ifexp_bytes_arm_from_read_mods) >>
  disch_then (drule_at (Pat `compile_ifexp_arm _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_expr _ _ _ = (INL _,_)`)) >>
  disch_then (drule_all_then mp_tac) >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`c`,`PG`]
    (qx_choosel_then [`v`,`fin`,`Gf`,`tf`] (map_every assume_tac o CONJUNCTS))) >>
  qexistsl [`v`,`fin`,`Gf`,`tf`] >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> disj2_tac >> pure_once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  qpat_assum `!rt w. evaluate_type _ _ = _ /\ eval_operand _ fin = _ ==> _`
    (qspecl_then [`rty`,`w`] mp_tac) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC
QED

Finalise ifexp_selection_full_mods
