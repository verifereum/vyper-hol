(* Execute the slot suffix from the reached VV without replaying its child. *)
Theory bodyMakeSlotWordSuffixMods
Ancestors
  bodyMakeElementsContractMods bodyStructFieldAddMods bodyStructFieldSmallStoreMods
  bodyIfExpWordReadMods bodyAttributeWordUnwrapMods bodyFullUnwrapRun
  bodyFullPathHistory bodyPtrMakeArrayEmission exprSimAggregateChildren
  gasShadowCompileHelpers exprOperandVar loweringShapeRules stateRelProj
  exprBodyPreProps exprBodyPreTypingProps exprSimIfExpWidenedPhysicalType
  aggregateEvaluatedLayout bodyWriteSubscriptSourceMods vyperEvalExprPreservesScopesDom
  vyperTypeEvalCaseProofs fragGasOriginPtrDead fragGasOriginPtrLoop
  bodySimStmtFacts exprSimUnwrap vyperStorageTrace vyperTypeExprSoundness
  exprLowering compileEnv bodyFullPostsMods loweringPosts bodyPtrDefs fragGasOriginPtr context
  vyperStorageFootprint fragExec exprLoweringProps exprSimWordArgs freshWrites
  exprPtrUnwrapFrames typedMemoryCopy typedCopyOriginPtrBase logStoreDataOriginPtr
  bodyFullAttributeAdd bodyPtrMakeArrayAddFrame bodyForRangeScalarFrameMods
  bodyFullHashKeccakFixed assignBasePtrOffset bodyStructFieldCutsMods
  exprSimVVFrame exprSimProps loweringStateRelDefs finite_map bodyFullShadowBodyInv venomState
  exprSimMemDefs exprSimCopy

val _ = Parse.hide "base";

Theorem slot_word_read_type[local]:
  expr_body_pre_mods mods ce cx env e es /\
  eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME rt /\
  read_result cx tv ee = (INL v,ee) ==> value_has_type rt v
Proof
  strip_tac >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee)` by
    simp[vyperStateTheory.bind_def] >>
  `expr_body_pre_mods mods ce cx env e (es with gas_obs := gs)` by simp[] >>
  drule_at (Pat `bind _ _ _ = _`) (REWRITE_RULE [ETA_THM] expr_body_pre_eval_mods) >>
  disch_then (drule_at (Pat `expr_body_pre_mods _ _ _ _ _ (es with gas_obs := gs)`)) >>
  strip_tac >>
  drule expr_sim_inv_mods_env >>
  disch_then (strip_assume_tac o MATCH_MP
    (SPEC_ALL env_consistent_type_defs_get_tenv)) >>
  fs[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >> gvs[]
QED

val no_dead = ``<|d_stor := K (K {}); d_trans := K (K {});
                  d_imm := K {}; d_ret := K {}|>``;

Theorem slot_word_unwrap[local]:
  unwrap_value ce vv sn = (op,su) /\ fn_has_code sn su func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sn /\
  copy_old_operand sn (vv_operand vv) /\
  is_word_type (expr_type e) /\ evaluate_type (get_tenv cx) (expr_type e) = SOME rt /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rt v) /\
  vv_post_mods H ctx func ce cx e es si sn s0 ee tv vv s /\
  ghost_inv_at_mods Dh lo d ce cx ee G tn s /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv s /\
  ptr_vv_ok cx (post_value_type ce e) tv vv ee G tn s /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?v. read_result cx tv ee = (INL v,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
             eval_operand (vv_operand vv) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rt v (w2n w) mem)) /\
  ~s.vs_halted /\ s.vs_current_bb = sn.cs_current_bb /\
  s.vs_inst_idx = LENGTH sn.cs_current_insts /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?v u Gf tf.
    read_result cx tv ee = (INL v,ee) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gf,tf)) /\
    eval_operand op u = SOME (typed_val_to_w256 rt v) /\
    op_taint tf op = {} /\
    u.vs_current_bb = su.cs_current_bb /\ u.vs_inst_idx = LENGTH su.cs_current_insts /\
    alloca_history func u /\
    u = s with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|> /\
    (!x. not_fresh_at sn x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm
Proof
  strip_tac >> Cases_on `vv`
  >- (qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
      simp[unwrap_value_def, comp_return_def] >> strip_tac >> gvs[] >>
      qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
      qpat_x_assum `vv_holds_mods _ _ _ _ _ _ _` mp_tac >>
      simp[vv_holds_mods_def,vv_holds_def,expr_val_rel_def] >> strip_tac >>
      qexistsl [`v`,`s`,`G`,`tn`] >>
      fs[ptr_vv_ok_def, ptr_val_ok_def, cj 1 gas_origin_ptr_path_rules]) >>
  rename1 `LocatedValue tag p` >>
  drule word_arm_location >> simp[] >> strip_tac >>
  qpat_x_assum `tag = expr_type e` SUBST_ALL_TAC >>
  qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[unwrap_value_def] >> disch_tac >>
  qpat_assum `ghost_inv_at_mods Dh _ _ _ _ _ _ _ _`
    (mp_then (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)
      (drule_at (Pat `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`))
      (Q.INST [`D` |-> `^no_dead`] word_arm_located_packet)) >>
  disch_then (qspecl_then [`su`,`rt`,`op`,`PG`] mp_tac) >>
  impl_tac >- gvs[vv_location_def, vv_operand_def, arithmeticTheory.ADD_COMM] >>
  strip_tac >>
  `alloca_inv s` by
    (qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
     drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `!x. not_fresh_at sn x ==> lookup_var x q = lookup_var x s` by
    (gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at sn x ==> _ /\ _ /\ _` drule >> simp[]) >>
  drule_all_then (qspec_then `explicit` strip_assume_tac) word_arm_loaded_path >>
  rename1 `gas_origin_ptr_path _ _ [] (OK u,Gf,tf)` >>
  qexistsl [`v`,`u`,`Gf`,`tf`] >> simp[] >>
  gen_tac >> irule gas_origin_ptr_path_from_no_dead >> simp[]
QED

(* Rebase only the word VV across a read-only prefix. *)
Theorem slot_rebase_holds[local]:
  vv_holds_mods ce cx ty tv vv ee s /\ t.vs_memory = s.vs_memory /\
  contract_storage t = contract_storage s /\
  contract_transient t = contract_transient s /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s ==>
  vv_holds_mods ce cx ty tv vv ee t
Proof
  Cases_on `vv` >> simp[vv_holds_mods_def,vv_operand_def]
  >- metis_tac[vv_holds_vars_frame,vv_operand_def] >>
  rename1 `LocatedValue ann p` >> Cases_on `p.ptr_location = LocCode` >>
  simp[vv_holds_mods_def,immutable_holds_mods_def] >>
  metis_tac[vv_holds_vars_frame,vv_operand_def,immutable_holds_memory_cong]
QED

Theorem slot_rebase_place[local]:
  vv_place_ptr_mods ce cx ee s tv vv /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
  (!id q sz. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var q) sz) ==>
     lookup_var q t = lookup_var q s) ==>
  vv_place_ptr_mods ce cx ee t tv vv
Proof
  Cases_on `vv` >- simp[vv_place_ptr_mods_def] >>
  Cases_on `tv`
  >~ [`vv_place_ptr_mods _ _ _ _ (PlaceR _) _`]
  >- (rename1 `PlaceR place` >> Cases_on `place` >>
      simp[vv_place_ptr_mods_def] >> rpt strip_tac >>
      irule vv_place_ptr_vars_frame >> qexists_tac `s` >> simp[] >>
      rpt strip_tac >> res_tac >> simp[]) >>
  simp[vv_place_ptr_mods_def] >> rpt strip_tac >>
  irule vv_place_ptr_vars_frame >> qexists_tac `s` >> simp[] >>
  rpt strip_tac >> res_tac >> simp[]
QED

Theorem slot_rebase_word_post[local]:
  vv_post_mods H ctx func ce cx e es si sm s0 ee tv vv s /\
  is_word_type (expr_type e) /\
  stmt_state_rel H ctx func ce cx ee t /\ immutable_frame_mods func ce cx ee t /\
  t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
  contract_storage t = contract_storage s /\ contract_transient t = contract_transient s /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
  (!x. not_fresh_at si x ==> lookup_var x t = lookup_var x s) /\
  local_ptrs_reserved ce si /\ sm.cs_next_id <= sn.cs_next_id ==>
  vv_post_mods H ctx func ce cx e es si sn s0 ee tv vv t
Proof
  strip_tac >>
  `!id q sz. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var q) sz) ==>
     lookup_var q t = lookup_var q s` by metis_tac[local_ptrs_reserved_def] >>
  `!n b sz. local_region ce ee.scopes t n b sz <=>
            local_region ce ee.scopes s n b sz` by
    (rpt gen_tac >> irule local_region_lookup_cong >> rpt strip_tac >>
     first_x_assum irule >> goal_assum (drule_at Any)) >>
  qhdtm_x_assum `vv_post_mods`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  `vv_holds_mods ce cx (post_value_type ce e) tv vv ee t` by
    (irule slot_rebase_holds >> qexists_tac `s` >> simp[]) >>
  `vv_place_ptr_mods ce cx ee t tv vv` by
    (irule slot_rebase_place >> qexists_tac `s` >> simp[] >> first_assum ACCEPT_TAC) >>
  `vv_at ce cx (post_value_type ce e) si sn ee tv vv t` by
    (irule vv_at_vars_frame >> qexistsl [`s`,`sm`] >> simp[]) >>
  `locals_kept ce es ee s0 t` by
    (irule locals_kept_mem_tail >> qexists_tac `s` >> simp[]) >>
  `pure_frame ce func es si s0 t <=> pure_frame ce func es si s0 s` by
    simp[pure_frame_state_cong] >>
  `vv_storage_live H cx vv ee t <=> vv_storage_live H cx vv ee s` by
    (Cases_on `vv` >> gvs[vv_operand_def]) >>
  simp[vv_post_mods_def,post_value_type_word] >> metis_tac[]
QED

Theorem make_slot_word_suffix_mods:
  is_word_type dty /\
  make_slot_entry_mods mods exps src tops cenv cx env
    (DF,lo,d,ctx,shadow_ctx,func,shadow_func) st0
    (csbase,ebase,sbase,Gbase,tnbase) (aid,base,cap,q)
    h xs dty dtv ps off sa sb sha shb (es,s,G,tn) /\
  compile_expr cenv (expr_type h) h sa = (vv,sm) /\
  compile_expr (gas_shadow_env T cenv) (expr_type (gas_shadow_expr h))
    (gas_shadow_expr h) sha = (vv,shm) /\
  gas_shadow_state sm shm /\
  (!tail. eval_expr cx h
      (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL raw,mid with gas_obs := tail)) /\
  mid.gas_obs = [] /\ storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s,G,tn) marks (OK u,g1,tt1) /\
    make_slot_child_post_mods DF lo d ctx func cenv cx h es sa sm s G tn vv
      H (INL raw) mid g1 tt1 u) ==>
  ?v t gf tf. read_result cx raw mid = (INL v,mid) /\ value_has_type dtv v /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (u,g1,tt1) [] (OK t,gf,tf)) /\
    struct_store_effects func (sm,g1,tt1,u) (sb,gf,tf,t) (base+off,dtv,v) /\
    sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id
Proof
  strip_tac >>
  qhdtm_assum `make_slot_entry_mods`
    (strip_assume_tac o REWRITE_RULE [make_slot_entry_mods_def]) >>
  qhdtm_assum `make_elements_entry_mods`
    (strip_assume_tac o REWRITE_RULE [make_elements_entry_mods_def]) >>
  qhdtm_assum `make_elements_static_mods`
    (strip_assume_tac o REWRITE_RULE [make_elements_static_mods_def]) >>
  qhdtm_assum `make_elements_cut_mods`
    (strip_assume_tac o REWRITE_RULE [make_elements_cut_mods_def]) >>
  `expr_body_pre_mods mods cenv cx env h es` by simp[] >>
  `type_widens_to (get_tenv cx) (expr_type h) dty` by
    simp[vyperTypeSystemTheory.type_widens_to_def,vyperTypeSystemTheory.well_formed_type_def] >>
  `expr_type h = dty` by metis_tac[type_widens_to_word] >>
  `is_word_type (expr_type h)` by simp[] >>
  `post_value_type cenv h = expr_type h` by (irule post_value_type_word >> simp[]) >>
  `type_memory_size dtv = 32` by metis_tac[exprSimPropsTheory.word_tv_memory_size] >>
  qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` (mp_tac o SRULE [])) >>
  `mid with gas_obs := [] = mid` by simp[vyperStateTheory.evaluation_state_component_equality] >>
  simp[] >> disch_tac >>
  `!v. read_result cx raw mid = (INL v,mid) ==> value_has_type dtv v` by
    (gen_tac >> strip_tac >> irule slot_word_read_type >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `expr_body_pre_mods _ _ _ _ _ _`)) >> simp[]) >>
  qabbrev_tac `H0 = storage_trace_horizon mid.storage_trace` >>
  `valid_horizon cx st0 H0 mid.storage_trace` by fs[Abbr `H0`, storage_trace_domain_def] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (s,G,tn) marks (OK u,g1,tt1) /\
     vv_post_mods H ctx func cenv cx h es sa sm s mid raw vv u /\
     ghost_inv_at_mods (DF H) lo d cenv cx mid g1 tt1 u` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ make_slot_child_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H _ _ _ _ _`
       (drule_then (strip_assume_tac o REWRITE_RULE [make_slot_child_post_mods_def])) >> fs[]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ make_slot_child_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H _ _ _ _ _`
    (drule_then (strip_assume_tac o REWRITE_RULE [make_slot_child_post_mods_def])) >>
  qpat_x_assum `INL raw = INL tv` (SUBST_ALL_TAC o SYM o REWRITE_RULE [sumTheory.INL_11]) >>
  qpat_x_assum `expr_type h = dty` (SUBST_ALL_TAC o SYM) >>
  fs[] >>
  `~u.vs_halted` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     drule_then strip_assume_tac gas_origin_ptr_path_projections >>
     drule fragGasSeqPtrTheory.gas_path_ptr_ok_not_halted >> simp[]) >>
  qpat_assum `compile_expr cenv _ _ sa = _` (strip_assume_tac o MATCH_MP (SPEC_ALL compile_expr_extends)) >>
  qabbrev_tac `out = STRING #"%" (toString sm.cs_next_var)` >>
  Cases_on `emit_op ADD [Var q; Lit (n2w off)] sm` >>
  rename1 `emit_op ADD [Var q; Lit (n2w off)] sm = (dst,sn)` >>
  `dst = Var out /\ sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id` by
    (qpat_assum `emit_op _ _ _ = _`
       (mp_tac o PURE_REWRITE_RULE [emit_op_eq]) >>
     simp[Abbr `out`] >> strip_tac >> gvs[]) >>
  qpat_x_assum `dst = Var out` SUBST_ALL_TAC >>
  Cases_on `unwrap_value cenv vv sn` >>
  rename1 `unwrap_value cenv vv sn = (op,su)` >>
  `compile_store_memory cenv op (Var out) (expr_type h) (lowered_value_type cenv h) su = ((),sb)` by
    (qpat_assum `make_elements_once_mods cenv _ _ _ _ _ = _`
       (mp_tac o PURE_REWRITE_RULE [make_elements_once_mods_def]) >> simp[comp_bind_def]) >>
  `cs_extends sm sn /\ cs_extends sn su /\ cs_extends su sb` by
    (conj_tac >- (irule (cj 2 cs_appends_emit_helpers |> REWRITE_RULE [cs_appends_def]) >>
                   goal_assum (drule_at Any)) >>
     conj_tac >- metis_tac[unwrap_value_extends] >>
     qspecl_then [`cenv`,`op`,`Var out`,`expr_type h`,`lowered_value_type cenv h`,`su`]
       (mp_tac o cj 1) externalEntryShapeTheory.compile_store_memory_labels >> simp[]) >>
  `fn_has_code sm sn func /\ fn_has_code sn su func /\ fn_has_code su sb func` by
    (qhdtm_assum `make_elements_code_mods`
       (strip_assume_tac o REWRITE_RULE [make_elements_code_mods_def]) >>
     `cs_extends sn sb` by metis_tac[cs_extends_trans] >>
     `cs_extends sm sb` by metis_tac[cs_extends_trans] >>
     metis_tac[fn_has_code_split]) >>
  `wb_frame cenv es mid sa s u /\ stmt_state_rel H0 ctx func cenv cx mid u` by
    (qhdtm_assum `vv_post_mods` (mp_tac o PURE_REWRITE_RULE [vv_post_mods_def]) >>
     simp[wb_frame_def] >> strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  `lookup_var q u = SOME (n2w base)` by metis_tac[wb_frame_vars] >>
  `ptr_covers g1 tt1 q u cap` by
    (qpat_assum `ptr_covers G tn q s cap` (mp_tac o REWRITE_RULE [ptr_covers_def]) >>
     qpat_assum `ghost_kept_at lo cenv es sa G tn s g1 tt1`
       (mp_tac o REWRITE_RULE [ghost_kept_at_def]) >>
     simp[ptr_covers_def] >> metis_tac[]) >>
  `not_fresh_at sm q` by (irule not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `!p. vv_operand vv = Var p ==> not_fresh_at sm p` by
    metis_tac[exprOperandVarTheory.compiler_compile_var] >>
  `!p n. cenv.ce_return_buf = SOME (PtrVar (Var p) n) ==> not_fresh_at sa p` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `csbase` >> simp[]) >>
  `!p n. cenv.ce_return_pc = SOME (PtrVar (Var p) n) ==> not_fresh_at sa p` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `csbase` >> simp[]) >>
  `base+off+32 < dimword (:256) /\ base+off+32 <= u.vs_alloca_next` by decide_tac >>
  `eval_operand (Var q) u = SOME (n2w base)` by simp[venomStateTheory.eval_operand_def] >>
  `op_taint tt1 (Var q) = {}` by fs[ptr_covers_def] >>
  qabbrev_tac `i = mk_inst sm.cs_next_id ADD [Var q; Lit (n2w off)] [out]` >>
  qabbrev_tac `au = update_var out (n2w base + n2w off) u` >>
  qabbrev_tac `a = au with vs_inst_idx := SUC u.vs_inst_idx` >>
  qabbrev_tac `ga = step_prov PG g1 i au` >>
  qabbrev_tac `ta = step_taint i u au tt1` >>
  `(!D lo' explicit. allocas_from lo' u ==>
     gas_origin_ptr_path (D,lo',explicit,ctx,func,PG) (u,g1,tt1) [] (OK a,ga,ta)) /\
   FLOOKUP ga out = op_prov g1 (Var q) /\ op_taint ta (Var out) = {} /\
   ta.t_mem = tt1.t_mem /\ ta.t_stor = tt1.t_stor /\ ta.t_trans = tt1.t_trans /\ ta.t_imm = tt1.t_imm /\
   (!p. p <> out ==> FLOOKUP ga p = FLOOKUP g1 p /\ op_taint ta (Var p) = op_taint tt1 (Var p))` by
    (rule_assum_tac (REWRITE_RULE [markerTheory.Abbrev_def]) >>
     drule_all attribute_add_full_frame >> simp[]) >>
  `!x. not_fresh_at sm x ==> x <> out` by
    (simp[not_fresh_at_def,Abbr `out`] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `!x. not_fresh_at sm x ==> lookup_var x a = lookup_var x u /\
     FLOOKUP ga x = FLOOKUP g1 x /\ op_taint ta (Var x) = op_taint tt1 (Var x)` by
    (rpt strip_tac >> `x <> out` by (first_x_assum irule >> simp[]) >>
     simp[Abbr `a`,Abbr `au`,venomStateTheory.update_var_def,
          venomStateTheory.lookup_var_def,FLOOKUP_UPDATE]) >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by
    (qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ g1 tt1 u`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >> simp[]) >>
  `a.vs_memory = u.vs_memory /\ a.vs_allocas = u.vs_allocas /\
   a.vs_alloca_next = u.vs_alloca_next /\ a.vs_data_section = u.vs_data_section /\
   a.vs_call_ctx = u.vs_call_ctx /\ a.vs_accounts = u.vs_accounts /\
   a.vs_transient = u.vs_transient /\ a.vs_immutables = u.vs_immutables /\
   contract_storage a = contract_storage u /\ contract_transient a = contract_transient u /\
   ~a.vs_halted /\ (ctx_has_dalloca ctx ==> allocas_below_fmp a)` by
    simp[Abbr `a`,Abbr `au`,venomStateTheory.update_var_def,contract_storage_def,
         contract_transient_def,ptrDisciplineTheory.allocas_below_fmp_def] >>
  drule_all_then strip_assume_tac emit_op_fetch_boundary >>
  `tmp = out` by
    (qpat_assum `Var out = Var tmp` mp_tac >>
     pure_rewrite_tac [venomStateTheory.operand_11] >> disch_then (ACCEPT_TAC o SYM)) >>
  qpat_x_assum `tmp = out` SUBST_ALL_TAC >>
  qpat_x_assum `out = STRING _ _` kall_tac >>
  qpat_x_assum `Var out = Var out` kall_tac >>
  `a.vs_current_bb = sn.cs_current_bb /\ a.vs_inst_idx = LENGTH sn.cs_current_insts` by
    simp[Abbr `a`,Abbr `au`,update_var_def] >>
  `alloca_history func a` by
    (`step_inst_base i u = OK au` by
       (qpat_assum `eval_operand (Var q) u = SOME _` mp_tac >>
        qpat_assum `Abbrev (i = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
        qpat_assum `Abbrev (au = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
        qpat_assum `i = _` (fn th => qpat_assum `au = _` (fn th' =>
          SIMP_TAC (srw_ss()) [th,th',venomExecSemanticsTheory.step_inst_base_opcode_eqs,
            venomInstTheory.mk_inst_def,venomExecSemanticsTheory.exec_pure2_def,eval_operand_def]))) >>
     `get_instruction bb u.vs_inst_idx = SOME i` by
       (qpat_assum `Abbrev (i = _)`
          (PURE_REWRITE_TAC o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
        first_assum ACCEPT_TAC) >>
     drule_all allocaHistoryTheory.alloca_history_base_step >>
     qpat_assum `Abbrev (a = _)` (fn th => qpat_assum `Abbrev (i = _)` (fn th' =>
       SIMP_TAC (srw_ss()) [REWRITE_RULE [markerTheory.Abbrev_def] th,
         REWRITE_RULE [markerTheory.Abbrev_def] th',venomInstTheory.mk_inst_def,
         venomInstTheory.is_terminator_def]))) >>
  `!x. not_fresh_at sa x ==> lookup_var x a = lookup_var x u /\
       FLOOKUP ga x = FLOOKUP g1 x /\ op_taint ta (Var x) = op_taint tt1 (Var x)` by
    (rpt strip_tac >> `not_fresh_at sm x` by (irule not_fresh_at_mono >> qexists `sa` >> simp[]) >>
     qpat_assum `!x. not_fresh_at sm x ==> lookup_var x a = _ /\ _` (drule_then strip_assume_tac) >> simp[]) >>
  `not_local_ptr cenv mid.scopes out` by
    (qpat_assum `Abbrev (out = _)`
       (PURE_REWRITE_TAC o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     irule local_ptrs_reserved_fresh >> qexists `sa` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `stmt_state_rel H0 ctx func cenv cx mid a` by
    (simp[Abbr `a`,Abbr `au`,stmt_state_rel_inst_idx] >>
     irule stmt_state_rel_update_var >> simp[]) >>
  `immutable_frame_mods func cenv cx mid a` by
    (irule immutable_frame_mods_exterior_frame >> qexistsl [`mid`,`u`,`sa`] >>
     qpat_assum `vv_post_mods H0 ctx func cenv cx h es sa sm s mid raw vv u`
       (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
     simp[] >> rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x a = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `eval_operand (vv_operand vv) a = eval_operand (vv_operand vv) u` by
    (Cases_on `vv_operand vv`
     >- simp[eval_operand_def]
     >- (simp[eval_operand_def] >>
         qpat_assum `!p. vv_operand vv = Var p ==> _` (drule_then assume_tac) >>
         qpat_assum `!x. not_fresh_at sm x ==> lookup_var x a = _ /\ _`
           (drule_then strip_assume_tac) >> simp[]) >>
     simp[eval_operand_def,Abbr `a`,Abbr `au`,update_var_def]) >>
  `vv_post_mods H0 ctx func cenv cx h es sa sn s mid raw vv a` by
    (irule slot_rebase_word_post >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl [`u`,`sm`] >> rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac
      >- (rpt strip_tac >> qpat_assum `!x. not_fresh_at sa x ==> lookup_var x a = _ /\ _`
            (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_inv_at_mods (DF H0) lo d cenv cx mid ga ta a` by
    (irule ghost_inv_at_mods_exterior_frame >> qexistsl [`g1`,`mid`,`u`,`sa`,`tt1`] >>
     simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ptr_vv_ok cx (post_value_type cenv h) raw vv mid ga ta a` by
    (map_every (fn pat => qpat_assum pat
       (PURE_REWRITE_TAC o single o REWRITE_RULE [markerTheory.Abbrev_def]))
       [`Abbrev (ga = _)`,`Abbrev (ta = _)`,`Abbrev (a = _)`,`Abbrev (au = _)`,`Abbrev (i = _)`] >>
     irule binop_source_ptr_vv_ok >> simp[] >> strip_tac >>
     qpat_assum `!p. vv_operand vv = Var p ==> _` (drule_then assume_tac) >>
     qpat_assum `!x. not_fresh_at sm x ==> x <> out` (drule_then mp_tac) >>
     pure_rewrite_tac [REFL_CLAUSE, NOT_CLAUSES, IMP_CLAUSES]) >>
  `vv_store_bound cx (post_value_type cenv h) (lowered_value_type cenv h) mid raw vv a` by
    (irule vv_store_bound_frame_mem_src >> qexists `u` >> simp[]) >>
  `(cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?v. read_result cx raw mid = (INL v,mid) /\
        !rt w. evaluate_type (get_tenv cx) (post_value_type cenv h) = SOME rt /\
          eval_operand (vv_operand vv) a = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside ta.t_mem a.vs_memory mem ==>
            val_in_memory rt v (w2n w) mem))` by
    (strip_tac >>
     qpat_assum `cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==> _` mp_tac >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (qx_choose_then `v` strip_assume_tac) >>
     qexists `v` >> simp[] >> rpt strip_tac >>
     qpat_assum `!rt w. evaluate_type _ _ = SOME rt /\ _ ==> _` (qspecl_then [`dtv`,`w`] mp_tac) >>
     simp[] >> decide_tac) >>
  `copy_old_operand sn (vv_operand vv)` by
    (pure_rewrite_tac [copy_old_operand_def] >> rpt strip_tac >>
     irule not_fresh_at_mono >> qexists `sm` >> simp[]) >>
  `local_ptrs_reserved cenv sn` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[] >> decide_tac) >>
  drule_at (Pat `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`) slot_word_unwrap >>
  disch_then (qspecl_then [`ta`,`su`,`dtv`,`op`,`lo`,
    `gas_explicit_sites ctx shadow_ctx`,`d`,`PG`,`ga`,`DF H0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (Q.X_CHOOSE_THEN `v` (Q.X_CHOOSE_THEN `b`
    (Q.X_CHOOSE_THEN `gb` (Q.X_CHOOSE_THEN `tb` strip_assume_tac)))) >>
  `value_has_type dtv v` by (first_x_assum irule >> first_assum ACCEPT_TAC) >>
  `not_fresh_at sn out` by
    (qpat_assum `emit_op ADD _ sm = _`
       (mp_tac o MATCH_MP emitHelperPropsTheory.emitted_insts_emit_op) >>
     simp[not_fresh_at_def,Abbr `out`] >> decide_tac) >>
  `lookup_var out a = SOME (n2w (base+off))` by
    simp[Abbr `a`,Abbr `au`,update_var_def,lookup_var_def,FLOOKUP_UPDATE,wordsTheory.word_add_n2w] >>
  `ptr_covers ga ta out a 32` by
    (qpat_assum `ptr_covers g1 tt1 q u cap` (mp_tac o REWRITE_RULE [ptr_covers_def]) >>
     `base < dimword (:256) /\ base+off < dimword (:256)` by decide_tac >>
     simp[ptr_covers_def,ptrDisciplineTheory.op_prov_def] >>
     disch_then (qx_choosel_then [`pbase`,`psz`] strip_assume_tac) >>
     qexistsl [`pbase`,`psz`] >> simp[] >> decide_tac) >>
  `lookup_var out b = SOME (n2w (base+off)) /\ ptr_covers gb tb out b 32` by
    (qpat_assum `!x. not_fresh_at sn x ==> lookup_var x b = _ /\ _` (drule_then strip_assume_tac) >>
     drule_all copy_ptr_covers_transport >> simp[]) >>
  `b.vs_allocas = u.vs_allocas /\ b.vs_alloca_next = u.vs_alloca_next /\
   b.vs_memory = u.vs_memory /\ ~b.vs_halted /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp b)` by
    (`allocas_below_fmp b <=> allocas_below_fmp a` by
       (qpat_assum `b = a with <|vs_vars := _; vs_inst_idx := _|>` (PURE_ONCE_REWRITE_TAC o single) >>
        SIMP_TAC (srw_ss()) [ptrDisciplineTheory.allocas_below_fmp_def]) >>
     rpt (conj_tac >-
       (qpat_assum `b = a with <|vs_vars := _; vs_inst_idx := _|>` (PURE_ONCE_REWRITE_TAC o single) >> simp[])) >>
     simp[]) >>
  `allocas_from lo b` by
    (qpat_assum `allocas_from lo u` mp_tac >>
     SIMP_TAC (srw_ss()) [ptrDisciplineTheory.allocas_from_def] >>
     qpat_assum `b.vs_allocas = u.vs_allocas` (PURE_REWRITE_TAC o single) >>
     disch_then ACCEPT_TAC) >>
  `lo <= b.vs_alloca_next /\ base+off+32 <= b.vs_alloca_next` by simp[] >>
  `w2n (n2w (base+off):bytes32) = base+off` by
    (`base+off < dimword (:256)` by decide_tac >> simp[wordsTheory.w2n_n2w,arithmeticTheory.LESS_MOD]) >>
  qpat_assum `compile_store_memory _ _ _ _ _ _ = _`
    (mp_then (Pat `compile_store_memory _ _ _ _ _ _ = _`) mp_tac
        compile_store_memory_word_origin_ptr_path) >>
  disch_then (qspecl_then [`v`,`tb`,`get_tenv cx`,`b`,`lo`,`func`,
    `gas_explicit_sites ctx shadow_ctx`,`n2w (base+off)`,`dtv`,`ctx`,`PG`,`gb`] mp_tac) >>
  qpat_assum `w2n (n2w (base+off):bytes32) = base+off` (PURE_REWRITE_TAC o single) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`t`,`gf`,`tf`] strip_assume_tac) >>
  `ci_mono sm sn` by simp[ci_mono_def] >>
  `ci_mono sn su` by
    (qspec_then `cenv` (qspecl_then [`vv`,`sn`] mp_tac) ci_mono_unwrap_value >> simp[]) >>
  `ci_mono sm su` by (irule ci_mono_trans >> qexists `sn` >> simp[]) >>
  `ci_mono su sb` by
    (`ci_mono su (SND (compile_store_memory cenv op (Var out) (expr_type h)
          (lowered_value_type cenv h) su))` by REWRITE_TAC [ci_mono_compile_store_memory] >>
     qpat_x_assum `ci_mono su (SND _)` mp_tac >> simp[]) >>
  `ci_mono sm sb` by (irule ci_mono_trans >> qexists `su` >> simp[]) >>
  `!x. not_fresh_at sm x ==> lookup_var x b = lookup_var x u /\
       FLOOKUP gb x = FLOOKUP g1 x /\ op_taint tb (Var x) = op_taint tt1 (Var x)` by
    (rpt strip_tac >>
     `not_fresh_at sn x` by (irule not_fresh_at_mono >> qexists `sm` >> simp[]) >>
     qpat_assum `!x. not_fresh_at sn x ==> lookup_var x b = _ /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at sm x ==> lookup_var x a = _ /\ _` (drule_then strip_assume_tac) >>
     simp[]) >>
  `typed_copy_state_frame sm (base+off) 32 u b` by
    (pure_rewrite_tac [typed_copy_state_frame_def] >>
     (conj_tac >-
       (qpat_assum `b = a with <|vs_vars := _; vs_inst_idx := _|>` (PURE_ONCE_REWRITE_TAC o single) >>
        simp[Once venom_state_component_equality,Abbr `a`,Abbr `au`,update_var_def])) >>
     simp[typed_copy_frame_def] >> rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sm x ==> lookup_var x b = _ /\ _` (drule_then strip_assume_tac) >>
     first_assum ACCEPT_TAC) >>
  `typed_copy_state_frame sm (base+off) 32 b t` by
    (irule typed_copy_state_frame_mono >> qexists `su` >> simp[]) >>
  `typed_copy_state_frame sm (base+off) 32 u t` by
    (irule typed_copy_state_frame_trans >> qexists `b` >> simp[]) >>
  `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (u,g1,tt1) [] (OK t,gf,tf)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >>
     qexistsl [`gb`,`b`,`tb`] >> reverse conj_tac
     >- qpat_assum `!D. gas_origin_ptr_path _ (b,gb,tb) [] _` (qspec_then `D` ACCEPT_TAC) >>
     irule gas_origin_ptr_path_trans >> qexistsl [`ga`,`a`,`ta`] >>
     reverse conj_tac
     >- qpat_assum `!D. gas_origin_ptr_path _ (a,ga,ta) [] _` (qspec_then `D` ACCEPT_TAC) >>
     qpat_assum `!D lo' explicit. allocas_from lo' u ==> _` irule >> first_assum ACCEPT_TAC) >>
  `alloca_history func t` by
    (qpat_assum `!D. gas_origin_ptr_path _ (u,g1,tt1) [] (OK t,gf,tf)` (qspec_then `DF H0` assume_tac) >>
     drule_all body_full_path_alloca_history >> simp[]) >>
  `t.vs_alloca_next = u.vs_alloca_next` by
    (qpat_assum `typed_copy_state_frame sm _ _ u t`
       (mp_tac o cj 1 o PURE_REWRITE_RULE [typed_copy_state_frame_def]) >>
     simp[Once venom_state_component_equality]) >>
  `val_wf dtv v` by
    (irule (cj 1 valueEncodingTypingTheory.value_has_type_val_wf) >> first_assum ACCEPT_TAC) >>
  qexistsl [`v`,`t`,`gf`,`tf`] >>
  simp[struct_store_effects_def,exprSimFullBundlePropsTheory.expr_sim_full_endpoint_def] >>
  qpat_assum `ci_mono sm sb` (strip_assume_tac o PURE_REWRITE_RULE [ci_mono_def]) >>
  conj_tac >> first_assum ACCEPT_TAC
QED
