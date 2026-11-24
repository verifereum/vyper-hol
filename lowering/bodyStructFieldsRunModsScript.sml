(* Linked execution of a suffix of a struct literal's ordered field stores. *)
Theory bodyStructFieldsRunMods
Ancestors
  bodyStructFieldStepMods bodyStructFieldConsOutcomeMods bodyStructFieldsSourceMods
  bodyStructFieldsCompileMods bodyFullPredsMods bodyInvCodeProps
  gasOutcomeFullPostMods bodyFullPostsMods exprSimFullBundleProps
  bodyFullHashKeccakFixed bodyAssignNameLinkedSetup
  exprSimHypsDefs valueEncodingDefs typeLayoutProps vyperTypeABI
  stmtSimProps vyperStorageFootprint gasOutcomeFull fragGasOriginPtr
  bodyPtrDefs loweringPosts exprLowering exprLoweringProps exprBodyPreProps emitHelperProps
  bodyStructFieldCutsMods bodyInvSplit bodyFullShadowBodyInv
  vyperInterpreter vyperState vyperAST compileEnv context list pair words
Libs monadsyntax

val list_post = ``\(fs : (string # expr) list) tvs cells off (H : (bool # 256 word # type_value) list # num list)
    (res : value list + exception) ee g ts z.
  ?vs added. res = INL vs /\ expr_sim_inv_mods mods ce cx env ee /\
    LIST_REL value_has_type tvs vs /\
    struct_prefix_mods (ctx,func,ce,cx,lo,d,pure) (ees,fr,sf,Gf,tnf)
      (root,addr,capacity,aid) (H,DF H,ee,sb,g,ts,z)
      (cells ++ added) (off + type_memory_size_list tvs) /\
    (!m. mem_agree_outside ts.t_mem z.vs_memory m ==>
      fields_in_memory (ZIP (MAP FST fs,vs)) (ZIP (MAP FST fs,tvs)) (addr+off) m)``;

val list_exit = ``\(H : (bool # 256 word # type_value) list # num list) res ee
    (gt : (string |-> num # num) # taint) r.
  ?exc. (res : value list + exception) = INR exc /\
    expr_exit (INR exc : eval_result + exception) r /\
    halt_exit H cx ee (INR exc : eval_result + exception) r /\
    (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)``;

(* The ordinary linked VV success post, at the head's own compiler slice. *)
val head_post = ``\(H : (bool # 256 word # type_value) list # num list) tv ee g ts t.
  vv_post_mods H ctx func ce cx e es si sm s ee tv vv t /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv t /\
  t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at_mods (DF H) lo d ce cx ee g ts t /\
  ptr_vv_ok cx (post_value_type ce e) tv vv ee g ts t /\
  (!v. tv = Value v /\ ~is_word_type (post_value_type ce e) /\
       ~is_bytestring_type (post_value_type ce e) ==>
    vv_own ce cx (post_value_type ce e) si sm ee tv vv t /\
    (!tag p. vv = LocatedValue tag p ==> p.ptr_location = LocMemory)) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?v. read_result cx tv ee = (INL v,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
             eval_operand (vv_operand vv) t = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside ts.t_mem t.vs_memory mem ==> val_in_memory rt v (w2n w) mem)) /\
  (!tag x. vv = StackValue tag x /\ ~is_word_type (post_value_type ce e) ==> ptr_buf_ok ce e x g t) /\
  (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==> ptr_buf_ok ce e p.ptr_operand g t) /\
  ghost_kept_at lo ce es si G tn s g ts``;

Triviality prefix_gas_obs:
  struct_prefix_mods (ctx,func,ce,cx,lo,d,pure) (ees,fr,sf,Gf,tnf)
    (root,addr,capacity,aid) (H,D,es with gas_obs := obs,si,G,tn,s) cells off <=>
  struct_prefix_mods (ctx,func,ce,cx,lo,d,pure) (ees,fr,sf,Gf,tnf)
    (root,addr,capacity,aid) (H,D,es,si,G,tn,s) cells off
Proof
  `!b. get_storage cx (es with gas_obs := obs) b = get_storage cx es b` by
    (Cases >> simp[vyperStorageBackendTheory.get_storage_def]) >>
  simp[struct_prefix_mods_def, immutable_frame_mods_def, immutables_rel_mods_def,
       immutable_alloca_sep_mods_def, loweringStateRelDefsTheory.immutables_rel_def,
       immutable_alloca_sep_def,
       storage_well_formed_on_def, vyperStorageBackendTheory.get_storage_def,
       ghost_inv_at_mods_def, wb_frame_def, locals_kept_def, popped_kept_def,
       pure_frame_def, stmt_state_rel_start_gas_obs]
QED

Triviality emit_op_var:
  emit_op opc ops si = (dst_op,sn) ==> ?dst. dst_op = Var dst
Proof
  disch_then (strip_assume_tac o MATCH_MP (cj 2 emitted_insts_emit_op)) >>
  metis_tac[]
QED

Theorem struct_fields_run_mods:
  !fs tys tvs es si sb shadow_si shadow_sb s G tn cells off out.
    compile_struct_lit compile_expr ce (StructT nsid) fs (Var root) off si = (out,sb) /\
    compile_struct_lit compile_expr (gas_shadow_env T ce) (StructT nsid)
      (MAP (I ## gas_shadow_expr) fs) (Var root) off shadow_si = (out,shadow_sb) /\
    expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (si,sb,shadow_si,shadow_sb) /\
    contract_inv mods exps ctx ce cx /\ module_body_inv mods src tops ce cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    body_const_cells_agree_mods mods cx env es /\
    body_exprs_full_ok_mods mods exps cx (MAP SND fs) /\
    (?(H0 : (bool # 256 word # type_value) list # num list).
        stmt_state_rel H0 ctx func ce cx ees sf) /\
    LIST_REL (\t (name,e). ALOOKUP
      (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)) name =
      SOME (t,type_memory_bytes ce t)) tys fs /\
    LIST_REL (\t e. arg_type_fits (expr_type e) t) tys (MAP SND fs) /\
    OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
    local_ptrs_reserved ce si /\ local_ptrs_reserved ce fr /\
    (!fn inst t. frag_reachable ctx func s fn inst t ==> dalloca_fmp_headroom inst t) /\
    (!H. dead_lo_ok_mods H (DF H) lo ce cx) /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
    return_buf_frame d ce si s /\
    (!e ee. MEM e (MAP SND fs) /\ expr_sim_inv_mods mods ce cx env ee ==>
      expr_body_pre_mods mods ce cx env e ee) /\
    (pure ==> ~EXISTS expr_has_effect (MAP SND fs)) /\ expr_sim_inv_mods mods ce cx env es /\
    storage_trace_domain cx st0 es.storage_trace /\ off + type_memory_size_list tvs <= capacity /\
    gas_admissible (eval_exprs cx (MAP SND fs))
      (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)) es /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
       struct_prefix_mods (ctx,func,ce,cx,lo,d,pure) (ees,fr,sf,Gf,tnf)
         (root,addr,capacity,aid) (H,DF H,es,si,G,tn,s) cells off) ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      ce.ce_modules cx st0 (eval_exprs cx (MAP SND fs)) (es,s,G,tn)
      (^list_post fs tvs cells off) ^list_exit
Proof
  BETA_TAC >> Induct
  >- (simp_tac bool_ss [MAP, LIST_REL_NIL, OPT_MMAP_def, Once compile_struct_lit_def,
                        comp_return_def, PAIR_EQ] >> rpt strip_tac >> gvs[] >>
      `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
        fs[storage_trace_domain_def] >>
      `~s.vs_halted` by
        (qpat_assum `!H. valid_horizon _ _ H _ ==> struct_prefix_mods _ _ _ _ _ _`
           (drule_then (strip_assume_tac o REWRITE_RULE [struct_prefix_mods_def])) >>
         first_assum ACCEPT_TAC) >>
      irule gas_outcome_full_mods_pure >> simp[] >>
      qexistsl [`G`,`es`,`INL []`,`s`,`tn`] >>
      conj_tac >- simp[Once evaluate_def, return_def] >>
      gen_tac >> disch_tac >> conj_tac >- simp[Once gas_origin_ptr_path_cases] >>
      qexists_tac `[]` >> simp[type_memory_size_list_sum, valueEncodingDefsTheory.val_in_memory_def,
                              prefix_gas_obs]) >>
  qx_gen_tac `field_pair` >> PairCases_on `field_pair` >> rpt gen_tac >> strip_tac >>
  Cases_on `tys` >> gvs[LIST_REL_CONS1, OPT_MMAP_def, AllCaseEqs()] >>
  rename1 `OPT_MMAP (evaluate_type _) rest_tys = SOME rest_tvs` >>
  rename1 `arg_type_fits (expr_type e) fty` >>
  rename1 `evaluate_type (get_tenv cx) fty = SOME ftv` >>
  rename1 `ALOOKUP _ fname = SOME (fty,_)` >>
  `type_memory_bytes ce fty = type_memory_size ftv` by
    drule_all_then ACCEPT_TAC assign_name_memory_bytes_mods >>
  qpat_assum `ALOOKUP _ fname = SOME (fty,_)`
    (mp_then (Pos hd) mp_tac (SIMP_RULE (srw_ss()) [] struct_field_cons_paired_compile)) >>
  disch_then (drule_at (Pat `compile_struct_lit _ (gas_shadow_env T _) _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_struct_lit _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `expr_sim_full_code _ _`)) >>
  simp[] >>
  disch_then (qx_choosel_then [`vv`,`sm`,`dst_op`,`sn`,`op`,`su`,`ss`,
    `sm_shadow`,`sn_shadow`,`su_shadow`,`ss_shadow`] strip_assume_tac) >>
  drule_then (qx_choose_then `dst` SUBST_ALL_TAC) emit_op_var >> gvs[] >>
  `expr_body_pre_mods mods ce cx env e es` by
    (qpat_assum `!e' ee. (_ \/ _) /\ _ ==> _`
       (qspecl_then [`e`,`es`] mp_tac) >> simp[]) >>
  drule_all_then assume_tac struct_fields_head_admissible_mods >>
  suspend "head"
QED

Resume struct_fields_run_mods[head]:
  `expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     ce cx (expr_type e) e es` by
    (qpat_assum `body_exprs_full_ok_mods _ _ _ (_::_)` mp_tac >>
     simp_tac bool_ss [Once body_exprs_full_ok_mods_def] >> strip_tac >>
     qpat_assum `body_expr_full_ok_mods _ _ _ e`
       (strip_assume_tac o REWRITE_RULE [Once body_expr_full_ok_mods_def]) >>
     qpat_assum `!DF lo d PG src tops ctx sh f sf ce env ty es.
        _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ expr_vv_sim_full_mods _ _ _ _ _ _`
       (strip_assume_tac o SIMP_RULE bool_ss [IMP_CONJ_THM, FORALL_AND_THM]) >>
     qpat_assum `!DF lo d PG src tops ctx sh f sf ce env ty es.
        _ ==> expr_vv_sim_full_mods _ _ _ _ _ _` irule >>
     asm_simp_tac bool_ss [] >> conj_tac
     >- (qexistsl [`src`,`tops`] >> first_assum ACCEPT_TAC) >>
     qexists_tac `env` >> asm_simp_tac bool_ss []) >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[storage_trace_domain_def] >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func ce cx es s /\ immutable_frame_mods func ce cx es s /\
     storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx es G tn s` by
    (rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H _ ==> struct_prefix_mods _ _ _ _ _ _`
       (drule_then (strip_assume_tac o REWRITE_RULE [struct_prefix_mods_def])) >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> struct_prefix_mods _ _ _ _ _ _`
    (drule_then (strip_assume_tac o REWRITE_RULE [struct_prefix_mods_def])) >>
  drule_then strip_assume_tac expr_sim_full_endpoint_fields >>
  drule_then assume_tac stmt_state_rel_allocas_below_fmp >>
  fs[expr_sim_full_code_def] >>
  qpat_x_assum `expr_vv_sim_full_mods _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`si`,`sm`,`shadow_si`,`sm_shadow`,`vv`,`s`,`G`,`tn`] mp_tac) >>
  (impl_tac >- (asm_simp_tac bool_ss [] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_tac >>
  irule (SIMP_RULE (srw_ss()) [] struct_field_cons_outcome_mods) >>
  BETA_TAC >> qexists_tac `^head_post` >> BETA_TAC >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  suspend "store"
QED

Resume struct_fields_run_mods[store]:
  qx_genl_tac [`marks`,`tv`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  qpat_assum `mid with gas_obs := [] = mid` (fn eq =>
    qpat_assum `!tail. eval_expr _ _ _ = (INL _,_ with gas_obs := tail)`
      (qspec_then `[]` (assume_tac o REWRITE_RULE [APPEND_NIL,eq]))) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
      vv_post_mods H ctx func ce cx e es si sm s mid tv vv t /\
      ghost_inv_at_mods (DF H) lo d ce cx mid G1 tn1 t` by
    (rpt strip_tac >> qpat_assum `!H. _ ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  qpat_assum `!H. _ ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ vv_store_bound _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `expr_sim_full_endpoint func sm s t` by simp[expr_sim_full_endpoint_def] >>
  `off + type_memory_size ftv + type_memory_size_list rest_tvs <= capacity` by
    (qpat_assum `off + type_memory_size_list (ftv::rest_tvs) <= capacity` mp_tac >>
     simp_tac (srw_ss()) [type_memory_size_list_sum] >> decide_tac) >>
  `off + type_memory_size ftv <= capacity` by decide_tac >>
  qpat_assum `∀H. _ ==> struct_prefix_mods _ _ _ _ _ _`
    (drule_then assume_tac) >>
  rename1 `stmt_state_rel anchor_h ctx func ce cx ees sf` >>
  drule (Q.ISPEC `anchor_h : (bool # 256 word # type_value) list # num list`
    (Q.GEN `H0` struct_field_success_step_mods)) >>
  disch_then (drule_at (Pat `eval_expr _ _ (_ with gas_obs := _) = (INL _,_)`)) >>
  disch_then (drule_at (Pat `expr_body_pre_mods _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `contract_inv _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_op ADD _ _ = (Var _,_)`)) >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `expr_sim_full_endpoint _ _ _ _`)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `storage_trace_domain _ _ _`)) >>
  disch_then (qspecl_then [`marks`,`ftv`,`gas_explicit_sites ctx shadow_ctx`,`PG`,`DF`] mp_tac) >>
  (impl_tac >- (asm_simp_tac bool_ss [IMP_CONJ_THM, FORALL_AND_THM] >>
    rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
      (qpat_assum `!v. tv = Value v /\ _ ==> vv_own _ _ _ _ _ _ _ _ _ /\ _`
         mp_tac >> simp_tac bool_ss [IMP_CONJ_THM, FORALL_AND_THM])))) >>
  disch_then (qx_choosel_then [`v`,`u`,`G2`,`tn2`]
    (strip_assume_tac o REWRITE_RULE [IMP_CONJ_THM, FORALL_AND_THM])) >>
  suspend "tail"
QED

Resume struct_fields_run_mods[tail]:
  drule_all_then strip_assume_tac struct_fields_source_cuts_mods >>
  qexistsl [`v`,`u`,`G2`,`tn2`] >> asm_simp_tac bool_ss [] >>
  pure_once_rewrite_tac [APPEND_ASSOC] >>
  qpat_assum `!tys tvs es si sb ssi ssb s G tn cells off out. _ ==> gas_outcome_full_mods _ _ _ _ _ _ _ _`
    irule >>
  asm_simp_tac bool_ss [] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qexists_tac `anchor_h` >> first_assum ACCEPT_TAC)
  >- (qexists_tac `rest_tys` >> asm_simp_tac bool_ss []) >>
  qexistsl [`out`,`shadow_sb`,`ss_shadow`,`ss`] >>
  asm_simp_tac bool_ss [] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
Finalise struct_fields_run_mods
