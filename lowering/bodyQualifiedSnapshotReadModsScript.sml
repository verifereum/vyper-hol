(* Add the snapshot suffix to the counted open RHS, after its source read. *)
Theory bodyQualifiedSnapshotReadMods
Ancestors
  bodyFullPostsMods reasonSourceProps exprSimAttribute exprSimMemorySource
  gasOutcomeFullMods gasStorage gasExemptCertMods fragGasOriginPtr
  vyperState vyperStorageTrace vyperStorageFootprint stmtSimProps haltExitProj
Libs
  monadsyntax

Theorem snapshot_vv_read[local]:
  vv_holds_mods cenv cx ty pv vv mid t ==>
  ?v. read_result cx pv mid = (INL v,mid)
Proof
  Cases_on `vv` >> simp[vv_holds_mods_def]
  >- (strip_tac >> drule reason_vv_read_success >> simp[]) >>
  rename1 `p.ptr_location = LocCode` >> Cases_on `p.ptr_location = LocCode`
  >- (simp[immutable_holds_mods_def] >>
      rpt strip_tac >> drule immutable_holds_read >> simp[]) >>
  simp[] >> strip_tac >> drule reason_vv_read_success >> simp[]
QED

val snapshot_open_fields =
  ``\(H : (bool # 256 word # type_value) list # num list) pv mid G tn t.
    vv_post_mods H ctx func cenv cx e es sa sb s0 mid pv vv t /\
    vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e)
      mid pv vv t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid G tn t /\
    ptr_vv_ok cx (post_value_type cenv e) pv vv mid G tn t /\
    (!v. pv = Value v /\ ~is_word_type (post_value_type cenv e) /\
         ~is_bytestring_type (post_value_type cenv e) ==>
         vv_own cenv cx (post_value_type cenv e) sa sb mid pv vv t /\
         (!t' p. vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
    (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     ?val. read_result cx pv mid = (INL val,mid) /\
           !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                  eval_operand (vv_operand vv) t = SOME w ==>
                  w2n w + type_memory_size rt <= lo /\
                  (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                         val_in_memory rt val (w2n w) mem)) /\
    (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type cenv e) ==>
             ptr_buf_ok cenv e op G t) /\
    (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
            ptr_buf_ok cenv e p.ptr_operand G t) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;

val snapshot_expr_exit =
  ``\(H : (bool # 256 word # type_value) list # num list)
      (res : 'a + exception) ee (gt : (string |-> (num # num)) # taint) r.
      expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)``;

val snapshot_open_exit = inst [alpha |-> ``:eval_result``] snapshot_expr_exit;
val snapshot_read_exit = inst [alpha |-> ``:value``] snapshot_expr_exit;

Theorem qualified_snapshot_read_lift_mods:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (eval_expr cx e) (es,s0,G0,tn0)
    (\H res mid G tn t. ?pv. res = INL pv /\
      ^snapshot_open_fields H pv mid G tn t) ^snapshot_open_exit /\
  (!marks pv v mid G tn t.
     storage_trace_domain cx st0 mid.storage_trace /\
     mid.gas_obs = [] /\
     (!tail. eval_expr cx e
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
       (INL pv,mid with gas_obs := tail)) /\
     read_result cx pv mid = (INL v,mid) /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
          gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
            (s0,G0,tn0) marks (OK t,G,tn) /\
          ^snapshot_open_fields H pv mid G tn t) ==>
     ?u Gu tu. !H. valid_horizon cx st0 H mid.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
         (t,G,tn) [] (OK u,Gu,tu) /\ Q H (INL v) mid Gu tu u) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0) Q ^snapshot_read_exit
Proof
  BETA_TAC >> strip_tac >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _`
    (strip_assume_tac o BETA_RULE o ONCE_REWRITE_RULE [gas_outcome_full_mods_def]) >>
  rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks`
  >- (disj1_tac >> conj_tac
      >- (irule gas_bad_storage_at_bind_left >> simp[storage_trace_frame_read_result]) >>
      qexistsl_tac [`H`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >> asm_rewrite_tac[])
  >- suspend "counted" >>
  disj2_tac >> disj2_tac >> simp[force_ignore_bind_action] >>
  qexistsl_tac [`err`,`ee`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
  reverse conj_tac >- (qexists_tac `H` >> asm_rewrite_tac[]) >>
  irule gas_exempt_cert_mods_error_result >> first_assum ACCEPT_TAC
QED

Resume qualified_snapshot_read_lift_mods[counted]:
  Cases_on `res`
  >- suspend "normal" >>
  rename1 `INR exc` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`INR exc`,`ee`,`r`,`G'`,`tn'`] >>
  simp[Once bind_def] >> gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  metis_tac[expr_exit_INR_type,halt_exit_INR_type]
QED

Resume qualified_snapshot_read_lift_mods[normal]:
  rename1 `INL pv` >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> simp[NoAsms] >>
  disch_then (CONJUNCTS_THEN2 kall_tac
    (qx_choose_then `t` (CONJUNCTS_THEN2 SUBST_ALL_TAC strip_assume_tac))) >>
  qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  drule_then (qx_choose_then `v` assume_tac) snapshot_vv_read >>
  suspend "suffix"
QED

Resume qualified_snapshot_read_lift_mods[suffix]:
  qpat_assum `!marks pv v mid G tn t. _ ==> ?u Gu tu. _`
    (qspecl_then [`marks`, `pv`, `v`, `ee with gas_obs := []`, `G'`, `tn'`, `t`] mp_tac) >>
  impl_tac
  >- (simp[NoAsms] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      gen_tac >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _`
        (qspec_then `H` (drule_then mp_tac)) >>
      simp[NoAsms,fragExecTheory.exit_result_def]) >>
  disch_then (qx_choosel_then [`u`, `Gu`, `tu`] (mk_asm "suffix")) >>
  drule_then (assume_tac o SIMP_RULE (srw_ss()) []) read_result_gas_obs >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`INL v`, `ee`, `OK u`, `Gu`, `tu`] >>
  conj_tac >- simp[Once bind_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  gen_tac >> strip_tac >> simp[NoAsms] >>
  asm "suffix" (qspec_then `H` (drule_then strip_assume_tac) o
    SIMP_RULE (srw_ss()) []) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `H` (drule_then (assume_tac o cj 1))) >>
  drule_then (qspecl_then [`t`, `G'`, `tn'`, `[]`, `OK u`, `Gu`, `tu`] mp_tac)
    gas_origin_ptr_path_append >> simp[]
QED

Finalise qualified_snapshot_read_lift_mods
