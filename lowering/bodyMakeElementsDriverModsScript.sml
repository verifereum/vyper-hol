(* Composition of the linked MakeArray traversal from its one-slot rule. *)
Theory bodyMakeElementsDriverMods
Ancestors
  bodyMakeElementsContractMods gasOutcomeFullBindMods gasOutcomeFullPostMods
  exprSimAggregateLoops exprSimWordArgs exprSimUnwrap exprLoweringProps
  externalEntryShape gasShadowCompileStmtHelpers gasShadowCompileBase
  gasShadowCompileConvert gasShadowCompileContext gasShadowCompilePure
  gasExemptCertMods vyperStorageTrace vyperTypeInvariants stateRelProj
  forPtrAllocationFrame bodyFullPostsMods bodyInvSplit bodyFullShadowBodyInv
  vyperStorageFootprint exprSimHypsDefs exprSimProps bodyFullPredsMods
  compileEnv exprLowering gasShadowState gasShadow vyperState vyperInterpreter
  valueEncoding typeLayoutProps fragExec gasOutcomeFull loweringPosts list pair

val _ = Parse.hide "base";

Theorem make_elements_storage_obs[local]:
  storage_well_formed_on cx (ee with gas_obs := gs) A <=>
  storage_well_formed_on cx ee A
Proof
  irule storage_well_formed_on_backends >> simp[]
QED

Theorem make_elements_cut_gas_obs[local,simp]:
  make_elements_cut_mods DF lo d ctx func cenv cx st0 root window cs
    (ee with gas_obs := gs) s G tn <=>
  make_elements_cut_mods DF lo d ctx func cenv cx st0 root window cs ee s G tn
Proof
  PairCases_on `root` >> PairCases_on `window` >>
  simp[make_elements_cut_mods_def, wb_frame_gas_obs,
       immutable_frame_mods_def, immutables_rel_mods_def,
       immutable_alloca_sep_mods_def, immutable_alloca_sep_def,
       loweringStateRelDefsTheory.immutables_rel_def, ghost_inv_at_mods_def,
       make_elements_storage_obs]
QED

Theorem make_elements_inv_gas_obs[local,simp]:
  expr_sim_inv_mods mods cenv cx env (ee with gas_obs := gs) <=>
  expr_sim_inv_mods mods cenv cx env ee
Proof
  simp[expr_sim_inv_mods_def]
QED

Theorem make_elements_nil[local]:
  make_elements_entry_mods mods exps src tops cenv cx env
    (DF,lo,d,ctx,shadow_ctx,func,shadow_func) st0
    (csbase,ebase,sbase,Gbase,tnbase) (aid,base,cap,q) [] ps off sa (es,s,G,tn) ==>
  make_elements_run_mods (DF,lo,ctx,shadow_ctx,PG,func) cenv cx st0
    (eval_exprs cx []) (es,s,G,tn)
    (make_elements_post_mods mods cenv cx env DF lo d ctx func st0
      (csbase,ebase,sbase,Gbase,tnbase) (aid,base,cap,q) [] [] ps off sa sa es s)
Proof
  strip_tac >>
  qhdtm_x_assum `make_elements_entry_mods`
    (strip_assume_tac o REWRITE_RULE[make_elements_entry_mods_def]) >>
  `~s.vs_halted` by fs[make_elements_cut_mods_def] >>
  rewrite_tac[make_elements_run_mods_def] >> irule gas_outcome_full_mods_pure >>
  simp[] >> qexistsl_tac [`G`,`es`,`INL []`,`s`,`tn`] >>
  simp[eval_exprs_nil, fragGasOriginPtrTheory.gas_origin_ptr_path_rules,
       make_elements_post_mods_def, valueEncodingDefsTheory.val_in_memory_def,
       make_elements_save_mods_def, make_elements_window_mods_def,
       make_elements_frame_mods_def]
QED

Theorem make_elements_once_shadow[local]:
  gas_shadow_compiles (make_elements_once_mods ce e q off dty)
    (make_elements_once_mods (gas_shadow_env T ce) (gas_shadow_expr e) q off dty)
Proof
  simp[make_elements_once_mods_def] >>
  irule gas_shadow_compiles_bind >>
  simp[gas_shadow_stmt_compile_expr_env] >>
  gen_tac >> irule gas_shadow_compiles_bind >>
  simp[gas_shadow_compiles_emit_op_same] >>
  gen_tac >> irule gas_shadow_compiles_bind >>
  simp[gas_shadow_compiles_unwrap_value, gas_shadow_compiles_store_memory]
QED

Theorem make_elements_once_split[local]:
  compile_make_tuple compile_expr ce (e::es) (ty::tys) (Var q) off sa = (Var q,sb) ==>
  ?sc. make_elements_once_mods ce e q off ty sa = ((),sc) /\
       compile_make_tuple compile_expr ce es tys (Var q)
         (off + type_memory_bytes ce ty) sc = (Var q,sb) /\
       cs_extends sa sc /\ sa.cs_next_var <= sc.cs_next_var /\
       sa.cs_next_id <= sc.cs_next_id
Proof
  disch_then (strip_assume_tac o MATCH_MP compile_make_tuple_cons) >>
  qexists_tac `st` >> simp[make_elements_once_mods_def, comp_bind_def] >>
  drule compile_expr_extends >> strip_tac >>
  drule unwrap_value_extends >> strip_tac >>
  rename1 `emit_op ADD [Var q; Lit (n2w off)] sm = (dst,sn)` >>
  rename1 `unwrap_value ce vv sn = (op,su)` >>
  `cs_extends sm sn` by
    (mp_tac (Q.SPECL [`ADD`,`[Var q; Lit (n2w off)]`,`sm`]
       externalEntryShapeTheory.emit_op_labels) >> simp[]) >>
  `cs_extends su st` by
    (mp_tac (Q.SPECL [`ce`,`op`,`dst`,`ty`,`lowered_value_type ce e`,`su`]
       externalEntryShapeTheory.compile_store_memory_labels) >> simp[]) >>
  conj_tac >- metis_tac[cs_extends_trans] >>
  mp_tac (Q.SPECL [`ADD`,`[Var q; Lit (n2w off)]`,`sm`] ci_mono_emit_op) >>
  mp_tac (Q.SPECL [`ce`,`vv`,`sn`] ci_mono_unwrap_value) >>
  mp_tac (Q.SPECL [`ce`,`op`,`dst`,`ty`,`lowered_value_type ce e`,`su`]
    ci_mono_compile_store_memory) >>
  simp[ci_mono_def] >> decide_tac
QED

Theorem make_elements_tail_extends[local]:
  compile_make_tuple compile_expr ce es tys buf off sa = (buf,sb) ==>
  cs_extends sa sb
Proof
  strip_tac >>
  qspecl_then [`compile_expr`,`ce`,`es`,`tys`,`buf`,`off`,`sa`] mp_tac
    externalEntryShapeTheory.compile_make_tuple_labels >>
  simp[externalEntryShapeTheory.compile_expr_labels]
QED

Theorem make_elements_split_code[local]:
  compile_make_tuple compile_expr cenv (h::xs) (ty::tys) (Var q) off sa = (Var q,sb) /\
  compile_make_tuple compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr (h::xs))
    (ty::tys) (Var q) off sha = (Var q,shb) /\
  make_elements_code_mods func shadow_func sa sb sha shb ==>
  ?sc shc. make_elements_once_mods cenv h q off ty sa = ((),sc) /\
     make_elements_once_mods (gas_shadow_env T cenv) (gas_shadow_expr h) q off ty sha = ((),shc) /\
     compile_make_tuple compile_expr cenv xs tys (Var q)
       (off + type_memory_bytes cenv ty) sc = (Var q,sb) /\
     compile_make_tuple compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr xs) tys (Var q)
       (off + type_memory_bytes cenv ty) shc = (Var q,shb) /\
     make_elements_code_mods func shadow_func sa sc sha shc /\
     make_elements_code_mods func shadow_func sc sb shc shb /\
     sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id
Proof
  simp[] >> strip_tac >>
  qpat_assum `compile_make_tuple _ _ (h::xs) _ _ _ sa = _`
    (strip_assume_tac o MATCH_MP make_elements_once_split) >>
  qpat_assum `compile_make_tuple _ _ (gas_shadow_expr h::_) _ _ _ sha = _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [] o MATCH_MP make_elements_once_split) >>
  fs[make_elements_code_mods_def] >>
  rename1 `make_elements_once_mods cenv h q off ty sa = ((),sc)` >>
  rename1 `make_elements_once_mods _ (gas_shadow_expr h) q off ty sha = ((),shc)` >>
  `gas_shadow_state sc shc` by
    (mp_tac (Q.INST [`ce` |-> `cenv`, `e` |-> `h`, `dty` |-> `ty`]
       make_elements_once_shadow) >> simp[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`sha`] mp_tac) >> simp[]) >>
  qpat_assum `compile_make_tuple _ _ xs _ _ _ sc = _`
    (assume_tac o MATCH_MP make_elements_tail_extends) >>
  qpat_assum `compile_make_tuple _ _ (MAP gas_shadow_expr xs) _ _ _ shc = _`
    (assume_tac o MATCH_MP make_elements_tail_extends) >>
  `fn_has_code sa sc func /\ fn_has_code sc sb func` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code sha shc shadow_func /\ fn_has_code shc shb shadow_func` by
    metis_tac[fn_has_code_split] >>
  simp[]
QED

Theorem make_elements_local_region_cut[local]:
  make_elements_static_mods mods exps src tops cenv cx env
    (DF,lo,ctx,shadow_ctx,func,shadow_func) st0 csbase ebase sbase aid sa /\
  make_elements_cut_mods DF lo d ctx func cenv cx st0
    (csbase,ebase,sbase,Gbase,tnbase) (aid,base,cap,q) sa es s G tn /\
  make_elements_cut_mods DF lo d ctx func cenv cx st0
    (csbase,ebase,sbase,Gbase,tnbase) (aid,base,cap,q) sc mid t G1 tn1 /\
  valid_horizon cx st0 H mid.storage_trace /\
  local_region cenv es.scopes s name b n ==>
  local_region cenv mid.scopes t name b n
Proof
  simp[make_elements_static_mods_def, make_elements_cut_mods_def] >>
  strip_tac >>
  `valid_horizon cx st0 H ebase.storage_trace` by
    (qpat_x_assum `mid.storage_trace = _` SUBST_ALL_TAC >>
     metis_tac[valid_horizon_append]) >>
  `stmt_state_rel H ctx func cenv cx ebase sbase` by simp[] >>
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  `local_region cenv ebase.scopes sbase name b n` by
    (irule local_region_frame >> conj_tac >- (qexists_tac `func` >> simp[]) >>
     qexistsl_tac [`csbase`,`es.scopes`,`s`] >>
     qpat_assum `wb_frame _ _ es _ _ _`
       (strip_assume_tac o REWRITE_RULE[wb_frame_def]) >> simp[] >>
     qpat_assum `MAP FDOM ebase.scopes = MAP FDOM mid.scopes`
       (fn th => pure_once_rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC) >>
  irule local_region_frame_fwd >>
  qexistsl_tac [`sbase`,`csbase`,`ebase.scopes`] >>
  qpat_assum `wb_frame _ _ mid _ _ _`
    (strip_assume_tac o REWRITE_RULE[wb_frame_def]) >> simp[]
QED

Theorem make_elements_frame_trans[local]:
  make_elements_frame_mods cenv func base cap sa es s t /\
  make_elements_frame_mods cenv func base cap sc mid t u /\
  (!name b n. local_region cenv es.scopes s name b n ==>
              local_region cenv mid.scopes t name b n) /\
  make_elements_save_mods t u /\ sa.cs_next_id <= sc.cs_next_id ==>
  make_elements_frame_mods cenv func base cap sa es s u
Proof
  simp[make_elements_frame_mods_def, make_elements_save_mods_def] >> strip_tac >>
  conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  `mem_bytes_at p n u.vs_memory = mem_bytes_at p n t.vs_memory` by
    (qpat_assum `!p n. _ ==> mem_bytes_at p n u.vs_memory = _`
       (qspecl_then [`p`,`n`] irule) >> simp[] >>
     rpt strip_tac >> first_x_assum irule >> qexists_tac `i` >> simp[] >> decide_tac) >>
  `mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory` by
    (qpat_assum `!p n. _ ==> mem_bytes_at p n t.vs_memory = _`
       (qspecl_then [`p`,`n`] irule) >> simp[] >>
     rpt strip_tac >> first_x_assum irule >> qexists_tac `i` >> simp[]) >>
  simp[]
QED

Theorem make_elements_size_cons[local]:
  type_memory_size_list (dtv::dtvs) = type_memory_size dtv + type_memory_size_list dtvs
Proof
  simp_tac bool_ss [type_memory_size_list_sum,listTheory.MAP,listTheory.SUM]
QED

Theorem make_elements_window_trans[local]:
  make_elements_window_mods base cap off k s t /\
  make_elements_window_mods base cap (off+k) w t u ==>
  make_elements_window_mods base cap off (k+w) s u
Proof
  simp[make_elements_window_mods_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  `base + off + k <= p` by decide_tac >>
  `base + (off + k) + w <= p` by decide_tac >>
  metis_tac[]
QED

Theorem make_elements_prefix_retained[local]:
  make_elements_prefix_mods base ps off s tn /\
  make_elements_prefix_mods base ((dtv,v,base+off,type_memory_size dtv)::ps) wide u tu ==>
  make_elements_prefix_mods base ps off u tu /\
  (!m. mem_agree_outside tu.t_mem u.vs_memory m ==> val_in_memory dtv v (base+off) m)
Proof
  simp[make_elements_prefix_mods_def, EVERY_MEM, FORALL_PROD] >> metis_tac[]
QED

Theorem make_elements_from_slot_mods:
  make_slot_contract_mods ==> make_elements_contract_mods
Proof
  rewrite_tac[make_elements_contract_mods_def] >> strip_tac >>
  Induct_on `args`
  >- (rpt gen_tac >> strip_tac >> Cases_on `tys` >>
      gvs[compile_make_tuple_def, comp_return_def] >> irule make_elements_nil >>
      goal_assum (drule_at Any))
  >> rpt gen_tac >> strip_tac >>
  Cases_on `tys` >- gvs[] >>
  gvs[AllCaseEqs()] >>
  rename1 `evaluate_type (get_tenv cx) ty = SOME dtv` >>
  rename1 `OPT_MMAP _ tys = SOME dtvs` >>
  drule_all (SIMP_RULE (srw_ss()) [] make_elements_split_code) >> strip_tac >>
  rename1 `make_elements_once_mods cenv h q off ty sa = ((),sc)` >>
  rename1 `make_elements_once_mods _ (gas_shadow_expr h) q off ty sha = ((),shc)` >>
  `off + type_memory_size dtv + type_memory_size_list dtvs <= cap` by
    (qpat_assum `off + type_memory_size_list _ <= cap` mp_tac >>
     simp_tac bool_ss [type_memory_size_list_sum, listTheory.MAP, listTheory.SUM,
                       arithmeticTheory.ADD_ASSOC]) >>
  qabbrev_tac `Slot = (make_slot_post_mods mods exps cenv cx env DF lo d ctx func st0
      (csbase,ebase,sbase,Gbase,tnbase) (aid,base,cap,q) h args dtv ps off sa sc es s :
      (bool # 256 word # type_value) list # num list -> value + exception ->
      evaluation_state -> (string |-> num # num) -> taint -> venom_state -> bool)` >>
  `make_elements_run_mods (DF,lo,ctx,shadow_ctx,PG,func) cenv cx st0
       (bind (eval_expr cx h) (read_result cx)) (es,s,G,tn) Slot` by
    (simp[Abbr `Slot`] >> qpat_assum `make_slot_contract_mods`
       (irule o REWRITE_RULE[make_slot_contract_mods_def]) >>
     rewrite_tac[make_slot_entry_mods_def] >>
     qexistsl_tac [`ty`,`sha`,`shadow_func`,`shc`,`src`,`tops`] >>
     simp[] >> decide_tac) >>
  qhdtm_x_assum `make_slot_contract_mods` kall_tac >>
  rewrite_tac[eval_exprs_cons_action, make_elements_run_mods_def] >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >>
  conj_tac
  >- (gen_tac >> irule storage_trace_frame_bind_all >>
      simp[cj 6 evaluate_storage_trace_frame, storage_trace_frame_return]) >>
  conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[]) >>
  conj_tac
  >- (irule storage_trace_frame_bind_all >>
      simp[cj 5 evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  qexists_tac `Slot` >> reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      qhdtm_assum `make_elements_run_mods`
        (irule_at Any o REWRITE_RULE[make_elements_run_mods_def]) >> simp[] >>
      POP_ASSUM_LIST (K all_tac) >>
      rpt gen_tac >> Cases_on `res` >>
      simp[exprSimDefsTheory.expr_exit_INL, exprSimDefsTheory.halt_exit_def] >>
      metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
  suspend "head_next"
QED

Resume make_elements_from_slot_mods[head_next]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> Slot H _ _ _ _ _`
    (drule_then mp_tac) >> simp[Abbr `Slot`,make_slot_post_mods_def] >>
  strip_tac >> disj1_tac >> goal_assum (drule_at Any) >>
  `make_elements_prefix_mods base ((dtv,v,base+off,type_memory_size dtv)::ps)
       (off+type_memory_size dtv) t tn1` by
    (irule make_elements_prefix_cons_mods >> simp[val_footprint_le]) >>
  `make_elements_entry_mods mods exps src tops cenv cx env
     (DF,lo,d,ctx,shadow_ctx,func,shadow_func) st0 (csbase,ebase,sbase,Gbase,tnbase)
     (aid,base,cap,q) args ((dtv,v,base+off,type_memory_size dtv)::ps)
     (off+type_memory_size dtv) sc (mid,t,G1,tn1)` by
    (qhdtm_assum `make_elements_entry_mods`
       (strip_assume_tac o REWRITE_RULE[make_elements_entry_mods_def]) >>
     simp[make_elements_entry_mods_def] >>
     qhdtm_x_assum `make_elements_static_mods` mp_tac >>
     simp[make_elements_static_mods_def] >> rpt strip_tac >>
     irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  qabbrev_tac `Tail = (make_elements_post_mods mods cenv cx env DF lo d ctx func st0
     (csbase,ebase,sbase,Gbase,tnbase) (aid,base,cap,q) args dtvs
     ((dtv,v,base+off,type_memory_size dtv)::ps) (off+type_memory_size dtv) sc sb mid t :
     (bool # 256 word # type_value) list # num list -> value list + exception ->
     evaluation_state -> (string |-> num # num) -> taint -> venom_state -> bool)` >>
  `make_elements_run_mods (DF,lo,ctx,shadow_ctx,PG,func) cenv cx st0
     (eval_exprs cx args) (mid,t,G1,tn1) Tail` by
    (simp[Abbr `Tail`] >> first_x_assum irule >>
     qpat_assum `make_elements_entry_mods _ _ _ _ _ _ _ _ _ _ _ args _ _ sc _`
       (irule_at Any) >> simp[] >>
     qexistsl_tac [`tys`,`shb`,`shc`] >>
     qpat_assum `type_memory_bytes cenv ty = type_memory_size dtv`
       (fn th => qpat_assum `compile_make_tuple _ _ args _ _ _ sc = _`
           (assume_tac o REWRITE_RULE[th]) >>
         qpat_assum `compile_make_tuple _ _ (MAP gas_shadow_expr args) _ _ _ shc = _`
           (assume_tac o REWRITE_RULE[th])) >> simp[]) >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >>
  conj_tac >- simp[storage_trace_frame_return] >>
  conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_values >>
      goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_values >> simp[]) >>
  conj_tac >- simp[cj 6 evaluate_storage_trace_frame] >>
  qexists_tac `Tail` >> reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      qpat_assum `make_elements_run_mods _ _ _ _ (eval_exprs cx args) _ Tail`
        (irule_at Any o REWRITE_RULE[make_elements_run_mods_def]) >> simp[] >>
      rpt gen_tac >> Cases_on `res'` >> simp[exprSimDefsTheory.expr_exit_INL]) >>
  suspend "tail_next"
QED

Resume make_elements_from_slot_mods[tail_next]:
  qx_genl_tac [`tailmarks`,`tailres`,`ee`,`G2`,`tn2`,`u`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> Tail H _ _ _ _ _`
    (drule_then mp_tac) >> simp[Abbr `Tail`,make_elements_post_mods_def] >>
  strip_tac >> disj1_tac >> goal_assum (drule_at Any) >>
  `~u.vs_halted` by
    (qpat_assum `make_elements_cut_mods _ _ _ _ _ _ _ _ _ _ sb ee u _ _`
       (strip_assume_tac o REWRITE_RULE[make_elements_cut_mods_def]) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `make_elements_entry_mods _ _ _ _ _ _ _ _ _ _ _ (h::args) _ _ sa _`
    (strip_assume_tac o REWRITE_RULE[make_elements_entry_mods_def]) >>
  `make_elements_prefix_mods base ps off u tn2 /\
   (!m. mem_agree_outside tn2.t_mem u.vs_memory m ==> val_in_memory dtv v (base+off) m)` by
    (irule make_elements_prefix_retained >>
     qpat_assum `make_elements_prefix_mods base ps off s tn` (irule_at Any) >>
     qpat_assum `make_elements_prefix_mods base (_::ps) _ u tn2` (irule_at Any) >> simp[]) >>
  irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl_tac [`G2`,`ee`,`INL (v::vs)`,`u`,`tn2`] >>
  simp[return_def,fragGasOriginPtrTheory.gas_origin_ptr_path_rules,
       make_elements_post_mods_def] >> rpt strip_tac
  >- (fs[make_elements_save_mods_def] >> metis_tac[])
  >- (simp[Once valueEncodingDefsTheory.val_in_memory_def] >>
      qpat_assum `!m. mem_agree_outside tn2.t_mem u.vs_memory m ==> tuple_in_memory _ _ _ m`
        drule >> simp[arithmeticTheory.ADD_ASSOC])
  >- (rewrite_tac[make_elements_size_cons] >> irule make_elements_window_trans >>
      qexists_tac `t` >> simp[]) >>
  irule make_elements_frame_trans >>
  qexistsl_tac [`mid`,`sc`,`t`] >> simp[] >>
  rpt gen_tac >> strip_tac >> irule make_elements_local_region_cut >>
  qpat_assum `local_region cenv es.scopes s _ _ _` (irule_at Any) >>
  qpat_assum `make_elements_cut_mods _ _ _ _ _ _ _ _ _ _ sc mid t _ _` (irule_at Any) >>
  qpat_assum `make_elements_cut_mods _ _ _ _ _ _ _ _ _ _ sa es s _ _` (irule_at Any) >>
  qhdtm_assum `make_elements_static_mods` (irule_at Any) >>
  qpat_assum `valid_horizon cx st0 _ mid.storage_trace` (irule_at Any)
QED

Finalise make_elements_from_slot_mods
