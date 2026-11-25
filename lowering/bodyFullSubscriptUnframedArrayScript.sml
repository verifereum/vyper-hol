(* Join the copied and uncopied array continuations at the index cut. *)
Theory bodyFullSubscriptUnframedArray
Ancestors vyperState[qualified,ignore_grammar] exprSimIfExpWidenedOwnedProvenance[qualified,ignore_grammar]
  bodyFullShadowBodyInv bodyFullHashKeccakFixed[qualified,ignore_grammar]
  bodyFullSubscriptCopiedBind bodyFullSubscriptNoCopyBind
  bodyFullSubscriptNoCopyMemorySelect[qualified,ignore_grammar]
  bodyFullSubscriptCopySnapshot bodyFullSubscriptLiveSlotSelect
  bodyFullSubscriptLiveImmSelect bodyFullSubscriptFixedSelect
  bodyFullSubscriptDynamicSelect bodyFullSubscriptDynamicChildRow
  bodyFullSubscriptCapturedEndpoint bodyFullSubscriptLiveLocalView
  bodyFullSubscriptOwnedIndexView bodySim bodyFullPreds bodySimFull
  exprSimSubscriptArraySource exprSimHypsDefs
  vyperStorageFootprint exprSimSubscriptArray loweringPosts context compileEnv
  exprSimSubscriptArrayOrigin exprReasonOperand exprOperandVar exprSimCopy
  bodyFullSubscriptCapturedDynamicRun bodyFullSubscriptLiveLanding

Theorem subscript_ghost_kept_initial_gas[local]:
  ghost_kept_at lo ce (es with gas_obs := gs) sa G0 tn0 s0 G tn =
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn
Proof
  simp[bodyPtrDefsTheory.ghost_kept_at_def]
QED

Theorem subscript_value_own_located[local]:
  vv_own ce cx ty sa sm ee (Value v) vv u /\
  (!t p. vv = LocatedValue t p ==> p.ptr_location = LocMemory) /\
  ~is_word_type ty /\ sm.cs_next_id <= sn.cs_next_id ==>
  vv_own ce cx ty sa sn ee (Value v)
    (LocatedValue ann (mk_ptr (vv_operand vv) LocMemory)) u
Proof
  Cases_on `vv` >>
  simp[vv_own_def, expr_val_own_def, vv_operand_def, mk_ptr_def,
       vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  strip_tac >> gen_tac >> strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >> disj1_tac >>
  rename1 `FLOOKUP u.vs_allocas aid = SOME (b,sz)` >>
  qexistsl [`aid`,`b`,`sz`] >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem subscript_unframed_array_vv_full:
  !cx v8 e1 e2 DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es et bd.
    (!s'' res t s3 res' t'.
       eval_expr cx e1 s'' = (INL res,t) /\
       (if subscript_reads_base cx e1 e2 then
          bind (read_result cx res) (\v. return (Value v))
        else return res) s3 = (INL res',t') ==>
       body_expr_full_ok cx e2) /\
    body_expr_full_ok cx e1 /\ body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre cenv cx env (Subscript v8 e1 e2) es /\
    expr_type e1 = ArrayT et bd /\
    place_type cenv e1 = ValPT (ArrayT et bd) /\
    post_value_type cenv e1 = expr_type e1 /\
    ~((!t r t'. eval_expr cx e2 t = (INL r,t') ==>
                t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
      ~subscript_reads_base cx e1 e2 /\ ~copies_subscript_base cenv e1 e2 /\
      (!s tr slot vt t.
         eval_expr cx e1 s <> (INL (PlaceR (StoragePlace tr slot vt)),t)) /\
      ((~cenv.ce_is_ctor /\
        !ty st. vv_location (FST (compile_expr cenv ty e1 st)) = SOME LocCode) \/
       ((?n. bd = Fixed n) /\
        (!tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv) /\
        !ty st. vv_location (FST (compile_expr cenv ty e1 st)) = SOME LocMemory))) ==>
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Subscript v8 e1 e2) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then (qspecl_then [`e1`, `e2`] assume_tac) body_inv_copies_subscript_base >>
  Cases_on `subscript_reads_base cx e1 e2` >- suspend "copied" >>
  `~copies_subscript_base cenv e1 e2` by fs[] >>
  `!s raw t. eval_expr cx e1 s = (INL raw,t) ==> body_expr_full_ok cx e2` by
    (rpt strip_tac >> first_x_assum irule >> simp[vyperStateTheory.return_def] >>
     metis_tac[]) >>
  irule subscript_nocopy_bind_full >>
  qpat_assum `expr_type e1 = ArrayT et bd` (irule_at Any) >>
  qpat_assum `expr_body_pre _ _ _ _ _` (irule_at Any) >>
  qpat_assum `body_inv _ _ _ _` (irule_at Any) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[LET_THM] >> BETA_TAC >>
  namedCases_on `raw` ["v", "p", "tr slot kt vt"]
  >- suspend "value"
  >- (namedCases_on `p` ["tr slot vt", "id path", "m off vt"]
      >- (irule (BETA_RULE (PURE_REWRITE_RULE [LET_THM] subscript_live_slot_select_full)) >>
          rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
          TRY (qexists `env` >> first_assum ACCEPT_TAC >> NO_TAC) >>
          qexistsl [`G1`,`bvv`,`gs1`,`gs2`,`iop`,`mid`,`s`,`sm`,`st2`,`tn1`,`ty`] >>
          rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
          qx_gen_tac `H` >> strip_tac >>
          qpat_assum `!H. valid_horizon _ _ H _ ==> _`
            (drule_then (map_every assume_tac o CONJUNCTS)) >> simp[])
      >- (irule (BETA_RULE (PURE_REWRITE_RULE [LET_THM]
                 bodyFullSubscriptNoCopyMemorySelectTheory.subscript_nocopy_memory_place_select_full)) >>
          rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
          TRY (qexists `tops` >> first_assum ACCEPT_TAC >> NO_TAC) >>
          TRY (qexists `env` >> first_assum ACCEPT_TAC >> NO_TAC) >>
          qexistsl [`G1`,`bvv`,`gs1`,`gs2`,`iop`,`mid`,`s`,`sm`,`st2`,`tn1`,`ty`] >>
          rpt conj_tac >> first_assum ACCEPT_TAC)
      >- suspend "immutable") >>
  `expr_body_pre cenv cx env e1 es` by
    (qpat_assum `expr_body_pre _ _ _ (Subscript _ _ _) _`
       (mp_then Any irule exprSimSubscriptArraySourceTheory.expr_body_pre_array_subscript_base_eval) >>
     qpat_assum `eval_expr cx e1 _ = (INL _,_)` (irule_at Any) >> simp[]) >>
  `expr_body_pre cenv cx env e1 (es with gas_obs := gs1)` by simp[] >>
  drule_all_then strip_assume_tac exprSimSourceTheory.expr_body_pre_runtime_typed >>
  gvs[vyperTypeInvariantsTheory.eval_result_typed_def]
QED

Resume subscript_unframed_array_vv_full[immutable]:
  `expr_body_pre cenv cx env e1 es` by
    (qpat_assum `expr_body_pre _ _ _ (Subscript _ _ _) _`
       (mp_then Any irule exprSimSubscriptArraySourceTheory.expr_body_pre_array_subscript_base_eval) >>
     qpat_assum `eval_expr cx e1 _ = (INL _,_)` (irule_at Any) >> simp[]) >>
  `expr_body_pre cenv cx env (Subscript v8 e1 e2) (es with gas_obs := gs1)` by simp[] >>
  drule_all_then assume_tac expr_body_pre_array_subscript_index_after_base >>
  `well_typed_expr env (Subscript v8 e1 e2) /\
   well_typed_expr env e1 /\ well_typed_expr env e2` by fs[expr_body_pre_def] >>
  `v8 = et` by
    (drule_all vyperTypeConstantFoldTheory.constant_subscript_type_ok >>
     simp[vyperTypeSystemTheory.subscript_type_ok_def]) >>
  qpat_x_assum `v8 = et` SUBST_ALL_TAC >>
  `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  drule_all_then assume_tac compile_array_vv_type >>
  `?p. bvv = LocatedValue (ArrayT et bd) p /\ p.ptr_location = LocCode` by
    (qpat_assum `vv_post _ _ _ _ _ e1 _ _ _ _ _ _ bvv s`
       (mp_tac o PURE_REWRITE_RULE [vv_post_def]) >>
     Cases_on `bvv` >> fs[vv_type_def, vv_at_def, vv_place_ptr_def, is_word_type_def]) >>
  qpat_x_assum `bvv = LocatedValue _ _` SUBST_ALL_TAC >>
  `loc = LocCode` by fs[vv_location_def] >>
  qpat_x_assum `loc = LocCode` SUBST_ALL_TAC >>
  `!id t. FLOOKUP env.var_types id = SOME t ==>
          ?q sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var q) sz)` by
    (gvs[expr_body_pre_def, expr_sim_inv_def]) >>
  `!l. p.ptr_operand <> Label l` by
    (qpat_assum `compile_expr cenv ty e1 sa = _`
       (mp_then Any mp_tac compile_array_pointer_not_label) >>
     disch_then (qspecl_then [`et`, `env`, `bd`] mp_tac) >> simp[]) >>
  drule_all_then assume_tac lower_compile_expr_not_label >>
  `copy_old_operand sm p.ptr_operand` by
    (qpat_assum `compile_expr cenv ty e1 sa = _`
       (mp_then Any mp_tac (CONJUNCT1 compiler_compile_var)) >>
     simp[vv_operand_def, copy_old_operand_def]) >>
  `copy_old_operand st2 iop` by
    (qpat_assum `lower_value compile_expr cenv ty e2 sm = _`
       (mp_then Any mp_tac compile_lower_value_var) >> simp[copy_old_operand_def]) >>
  irule subscript_live_immutable_select_full >>
  qpat_assum `eval_expr cx e1 _ = _` (irule_at Any) >>
  qpat_assum `bind (eval_expr cx e2) _ _ = _` (irule_at Any) >>
  simp[copy_old_operand_def, vv_operand_def, word_scale_def,
       elem_size_in_location_def, is_slot_addressed_def,
       exprSimSubscriptArrayComposeTheory.expr_post_initial_gas] >>
  qexistsl [`s`,`tops`,`tn1`,`st2`,`sm`,`p`,`iop`,`env`,`G1`] >>
  qpat_x_assum `LocCode = (case _ of NONE => _ | SOME l => l)` kall_tac >>
  qpat_x_assum `~((!t r t'. eval_expr _ _ _ = _ ==> _) /\ _)` kall_tac >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (gvs[copy_old_operand_def, vv_operand_def, word_scale_def,
           elem_size_in_location_def, is_slot_addressed_def] >> NO_TAC) >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >> simp[]
QED

(* The owned Value survives the index evaluation. Observe the selector at st2,
   retaining its exact result and endpoint ghosts at every valid horizon. *)
Theorem nocopy_value_select_observed:
  fixed_select_scalar_intro lo (gas_explicit_sites ctx shadow_ctx) ctx func PG FO /\
  captured_dynamic_scalar_rule DO /\
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env (Subscript v8 e1 e2) es /\
  expr_type e1 = ArrayT et bd /\ post_value_type cenv e1 = expr_type e1 /\
  compile_expr cenv ty e1 sa = (bvv,sm) /\
  lower_value compile_expr cenv ty e2 sm = (iop,st2) /\
  loc = (case vv_location bvv of NONE => LocMemory | SOME l => l) /\
  compile_array_subscript (vv_operand bvv) iop
    (case bd of Fixed _ => F | Dynamic _ => T)
    (case bd of Fixed n => n | Dynamic _ => 0)
    (word_scale loc) (elem_size_in_location cenv loc et)
    (is_signed_type (expr_type e2))
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc) st2 = (dst,sb) /\
  fn_has_code st2 sb func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  local_ptrs_reserved cenv st2 /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_var <= st2.cs_next_var /\ sm.cs_next_id <= st2.cs_next_id /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  eval_expr cx e1 (es with gas_obs := gs1) = (INL (Value v),mid) /\
  bind (eval_expr cx e2) (read_result cx) (mid with gas_obs := gs2) = (INL key,fin) /\
  storage_trace_domain cx st0 fin.storage_trace /\ fin.gas_obs = [] /\
  ~it.vs_halted /\ it.vs_current_bb = st2.cs_current_bb /\
  it.vs_inst_idx = LENGTH st2.cs_current_insts /\ alloca_history func it /\
  s0.vs_alloca_next <= s.vs_alloca_next /\ s.vs_alloca_next <= it.vs_alloca_next /\
  vv_store_bound cx (post_value_type cenv e1) (lowered_value_type cenv e1) mid (Value v) bvv s /\
  ptr_vv_ok cx (post_value_type cenv e1) (Value v) bvv mid G1 tn1 s /\
  (!y. Value v = Value y /\ ~is_word_type (post_value_type cenv e1) /\
       ~is_bytestring_type (post_value_type cenv e1) ==>
       vv_own cenv cx (post_value_type cenv e1) sa sm mid (Value v) bvv s /\
       (!t p. bvv = LocatedValue t p ==> p.ptr_location = LocMemory)) /\
  (!t op. bvv = StackValue t op /\ ~is_word_type (post_value_type cenv e1) ==>
          ptr_buf_ok cenv e1 op G1 s) /\
  (!t p. bvv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
         ptr_buf_ok cenv e1 p.ptr_operand G1 s) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  ptr_val_ok cx (post_value_type cenv e2) key iop Gi tni it /\
  ghost_kept_at lo cenv mid sm G1 tn1 s Gi tni /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0 /\
    vv_post H ctx func cenv cx e1 es sa sm s0 mid (Value v) bvv s /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 s /\
    expr_post H ctx func cenv cx e2 mid sm st2 s fin key iop it /\
    ghost_inv_at (DF H) lo d cenv cx fin Gi tni it) ==>
  v8 = et /\ loc = LocMemory /\
  ?res r Gz tnz.
    (case bd of
       Fixed n => ?sc. fixed_select_cuts func st2 sc sb /\ FO st2 sc sb it r
     | Dynamic cap => ?sz iw nw q.
         r = (if idx_in_range (is_signed_type (expr_type e2)) iw nw
              then OK q else Abort Revert_abort q) /\
         captured_dynamic_itinerary DO func (vv_operand bvv) iop dst sz
           (is_signed_type (expr_type e2)) iw nw st2 sb (it,Gi,tni) (q,Gz,tnz)) /\
    (!tail. select_result cx (ArrayT et bd) (Value v) (ValueSubscript key)
      (fin with gas_obs := tail) = (res,fin with gas_obs := tail)) /\
    (!H. valid_horizon cx st0 H fin.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (it,Gi,tni) [] (r,Gz,tnz) /\
      ((?z. r = OK z /\
        subscript_dynamic_select_post DF lo d ctx func cenv cx et e1 e2 es sa sb s0 G0 tn0 dst
          H res (fin with gas_obs := []) Gz tnz z) \/
       (exit_result r /\ expr_exit res r /\
        halt_exit H cx (fin with gas_obs := []) res r /\
        (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre cenv cx env e1 es` by
    (qpat_assum `expr_body_pre _ _ _ (Subscript _ _ _) _`
       (mp_then Any irule exprSimSubscriptArraySourceTheory.expr_body_pre_array_subscript_base_eval) >>
     qpat_assum `eval_expr cx e1 _ = (INL _,_)` (irule_at Any) >> simp[]) >>
  `expr_body_pre cenv cx env e1 (es with gas_obs := gs1)` by simp[] >>
  drule_all_then strip_assume_tac exprSimSourceTheory.expr_body_pre_runtime_typed >>
  qpat_assum `expr_type e1 = _` (fn eq =>
    qpat_assum `evaluate_type (get_tenv cx) (expr_type e1) = SOME _`
      (assume_tac o REWRITE_RULE [eq])) >>
  drule_then strip_assume_tac vyperTypeValuesTheory.evaluate_type_ArrayT_cases >>
  `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `~is_word_type (post_value_type cenv e1) /\
   ~is_bytestring_type (post_value_type cenv e1)` by
    simp[is_word_type_def, is_bytestring_type_def] >>
  qpat_x_assum `!v. Value _ = Value v /\ _ ==> _`
    (qspec_then `v` (mp_tac o SIMP_RULE (srw_ss()) [])) >>
  impl_tac >- simp[] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `ptr_buf_ok cenv e1 (vv_operand bvv) G1 s` by
    (Cases_on `bvv` >> fs[vv_operand_def]) >>
  qpat_assum `compile_expr cenv ty e1 sa = _`
    (mp_then Any mp_tac (CONJUNCT1 compiler_compile_var)) >> simp[] >> disch_tac >>
  `vv_post (storage_trace_horizon fin.storage_trace) ctx func cenv cx e1
      (es with gas_obs := gs1) sa sm s0 mid (Value v) bvv s /\
   expr_post (storage_trace_horizon fin.storage_trace) ctx func cenv cx e2
      (mid with gas_obs := gs2) sm st2 s fin key iop it /\
   ghost_kept_at lo cenv (mid with gas_obs := gs2) sm G1 tn1 s Gi tni` by
    simp[exprSimPropsTheory.vv_post_initial_gas,
         exprSimSubscriptArrayComposeTheory.expr_post_initial_gas,
         subscript_ghost_kept_initial_gas] >>
  drule_all_then assume_tac compile_array_vv_type >>
  `lower_value compile_expr cenv ty e1 sa = (vv_operand bvv,sm)` by
    (Cases_on `bvv` >> fs[vv_type_def, vv_operand_def, exprLoweringTheory.lower_value_def,
      exprLoweringTheory.unwrap_value_def, is_word_type_def, comp_return_def, comp_bind_def]) >>
  `well_typed_expr env e1 /\
   (!id t. FLOOKUP env.var_types id = SOME t ==>
          ?q sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var q) sz))` by
    qpat_assum `expr_body_pre cenv cx env e1 es` (fn pre =>
      let
        val facts = MATCH_MP exprBodyPrePropsTheory.expr_body_pre_static_facts pre
        val inv = REWRITE_RULE [expr_sim_inv_def] (cj 1 facts)
      in
        ACCEPT_TAC (CONJ (cj 2 facts) (cj 6 inv))
      end) >>
  `!l. vv_operand bvv <> Label l` by (irule lower_compile_expr_not_label >> metis_tac[]) >>
  `expr_body_pre cenv cx env (Subscript v8 e1 e2) (es with gas_obs := gs1)` by simp[] >>
  qpat_x_assum `tvt = ArrayTV _ _` SUBST_ALL_TAC >>
  qpat_x_assum `vv_post _ _ _ _ _ e1 es _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `expr_post _ _ _ _ _ e2 mid _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `ghost_kept_at _ _ mid _ _ _ _ _ _` kall_tac >>
  drule_all_then strip_assume_tac subscript_owned_array_index_view >>
  `loc = LocMemory` by metis_tac[] >>
  qpat_x_assum `loc = LocMemory` SUBST_ALL_TAC >>
  drule_all_then assume_tac expr_body_pre_array_subscript_index_after_base >>
  `expr_body_pre cenv cx env e2 (mid with gas_obs := gs2)` by simp[] >>
  drule_all_then strip_assume_tac exprSimConcatArgsTheory.concat_head_typed >>
  drule_all_then strip_assume_tac exprSimSubscriptArraySuffixTheory.framed_array_index_post_view >>
  `well_typed_expr env (Subscript v8 e1 e2) /\ well_typed_expr env e2` by fs[expr_body_pre_def] >>
  `v8 = et` by
    (drule_all vyperTypeConstantFoldTheory.constant_subscript_type_ok >>
     simp[vyperTypeSystemTheory.subscript_type_ok_def]) >>
  qpat_x_assum `v8 = et` SUBST_ALL_TAC >>
  qpat_x_assum `key = IntV i` SUBST_ALL_TAC >>
  qpat_x_assum `(case vv_location bvv of NONE => _ | SOME l => l) = LocMemory` SUBST_ALL_TAC >>
  `is_word_type (expr_type e2)` by
    (qpat_assum `evaluate_type _ (expr_type e2) = _` mp_tac >>
     qpat_assum `value_has_type tv (IntV i)` mp_tac >> rpt (pop_assum kall_tac) >>
     Cases_on `expr_type e2` >>
     simp[vyperValueTheory.evaluate_type_def, AllCaseEqs(),
          vyperTypingTheory.value_has_type_def, is_word_type_def] >>
     rpt strip_tac >> gvs[vyperTypingTheory.value_has_type_def, is_word_type_def]) >>
  `op_taint tni (vv_operand bvv) = {}` by
    (qpat_assum `ptr_vv_ok _ _ _ bvv fin Gi tni it` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `bvv` >>
     rw[vv_operand_def, bodyPtrDefsTheory.ptr_vv_ok_def,
        bodyPtrDefsTheory.ptr_val_ok_def]) >>
  `op_taint tni iop = {} /\ op_prov Gi iop = NONE` by
    (qpat_assum `ptr_val_ok _ _ _ iop Gi tni it`
       (strip_assume_tac o REWRITE_RULE [bodyPtrDefsTheory.ptr_val_ok_def]) >> fs[]) >>
  `allocas_from lo it` by
    (qpat_assum `ghost_inv_at _ lo d cenv cx fin Gi tni it`
      (strip_assume_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def])) >>
  `!x. vv_operand bvv = Var x ==> not_fresh_at st2 x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x. iop = Var x ==> not_fresh_at st2 x` by
    (qpat_assum `lower_value compile_expr cenv ty e2 sm = _`
       (mp_then Any mp_tac compile_lower_value_var) >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (qpat_assum `eval_expr cx e1 _ = _`
       (mp_then Any mp_tac vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom) >> simp[]) >>
  qpat_assum `expr_post _ _ _ _ _ e2 (mid with gas_obs := gs2) _ _ _ _ _ _ _`
    (mp_then Any assume_tac exprSimWordArgsTheory.expr_post_frame o
     REWRITE_RULE [exprSimSubscriptArrayComposeTheory.expr_post_initial_gas]) >>
  qpat_assum `vv_post _ _ _ _ _ e1 (es with gas_obs := gs1) _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o
     REWRITE_RULE [exprSimPropsTheory.vv_post_initial_gas, vv_post_def]) >>
  `wb_frame cenv es mid sa s0 s` by (simp[wb_frame_def] >> metis_tac[]) >>
  `wb_frame cenv es fin sa s0 it` by
    (irule (INST_TYPE [alpha |-> ``:256``] exprSimWordArgsTheory.wb_frame_trans) >>
     simp[] >> conj_tac
     >- (qexistsl [`mid`,`sm`,`s`] >> simp[]) >>
     goal_assum (drule_at Any)) >>
  `MAP FDOM mid.scopes = MAP FDOM fin.scopes` by
    (qpat_assum `MAP FDOM (mid with gas_obs := gs2).scopes = _`
       (ACCEPT_TAC o SIMP_RULE (srw_ss()) [])) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gi tni` by
    (irule (INST_TYPE [``:'b`` |-> ``:256``] wordArgsPtrTheory.ghost_kept_at_wb_trans) >>
     simp[] >> conj_tac
     >- (qexistsl [`storage_trace_horizon fin.storage_trace`,`ctx`,`cx`,`func`] >> simp[]) >>
     qexistsl [`G1`,`mid`,`mid with gas_obs := gs2`,`s`,`sm`,`tn1`] >> simp[]) >>
  qpat_assum `expr_post _ _ _ _ _ e2 (mid with gas_obs := gs2) _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o
     REWRITE_RULE [exprSimSubscriptArrayComposeTheory.expr_post_initial_gas, expr_post_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp it` by
    (qpat_assum `stmt_state_rel _ ctx func cenv cx fin it`
       (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  `~expr_has_effect (Subscript et e1 e2) ==> pure_frame cenv func es sa s0 it` by
    (simp[] >> strip_tac >> irule exprSimPropsTheory.pure_frame_trans >> simp[] >>
     qexistsl [`mid`,`sm`,`s`] >> fs[wb_frame_def]) >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==>
     stmt_state_rel H ctx func cenv cx fin it /\
     storage_well_formed_on cx fin (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx fin Gi tni it` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >>
     fs[expr_post_def]) >>
  `type_memory_bytes cenv et = type_memory_size elem_tv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  Cases_on `bd`
  >- (`?kvs. v = ArrayV (SArrayV kvs)` by
        (qpat_assum `value_has_type (ArrayTV _ (Fixed _)) v` mp_tac >>
         rpt (pop_assum kall_tac) >> Cases_on `v` >> simp[vyperTypingTheory.value_has_type_inv] >>
         qmatch_goalsub_rename_tac `ArrayV av` >> Cases_on `av` >>
         simp[vyperTypingTheory.value_has_type_inv]) >>
      qpat_x_assum `v = ArrayV _` SUBST_ALL_TAC >>
      simp[mk_ptr_def, vv_location_def, vv_operand_def, post_value_type_def] >>
      `?sc res q Gq tq.
        let sgn = is_signed_type (expr_type e2) in
        let rr = if idx_in_range sgn iw (n2w n) then OK q else Abort Revert_abort q in
        array_bounds_check iop (Lit (n2w n)) sgn st2 = ((),sc) /\
        array_elem_ptr (vv_operand bvv) iop F (word_scale LocMemory)
          (type_memory_bytes cenv et) sc = (dst,sb) /\
        fixed_select_cuts func st2 sc sb /\ FO st2 sc sb it rr /\
        (!tail. select_result cx (ArrayT et (Fixed n)) (Value (ArrayV (SArrayV kvs)))
          (ValueSubscript (IntV i)) (fin with gas_obs := tail) = (res,fin with gas_obs := tail)) /\
        storage_trace_domain cx st0 fin.storage_trace /\
        (!H. valid_horizon cx st0 H fin.storage_trace ==>
          gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
            (it,Gi,tni) [] (rr,Gq,tq) /\
          ((?z. rr = OK z /\
            subscript_dynamic_select_post DF lo d ctx func cenv cx et e1 e2 es sa sb s0 G0 tn0 dst
              H res fin Gq tq z) \/
            (exit_result rr /\ expr_exit res rr /\ halt_exit H cx fin res rr /\
             (ctx_has_dalloca ctx ==> !z. rr = Halt z ==> allocas_below_fmp z))))`
      suffices_by
        (simp_tac bool_ss [LET_THM] >> strip_tac >>
         qexistsl [`res`,`if idx_in_range (is_signed_type (expr_type e2)) iw (n2w n)
                         then OK q else Abort Revert_abort q`,`Gq`,`tq`] >>
         `fin with gas_obs := [] = fin` by simp[vyperStateTheory.evaluation_state_component_equality] >>
         simp[] >> metis_tac[]) >>
      rewrite_tac[subscript_dynamic_select_post_def] >>
      irule (BETA_RULE subscript_fixed_memory_select_observed) >>
      `n < dimword (:256)` by metis_tac[placeStoreSlotsTheory.store_slots_fixed_count_bound] >>
      `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st2 x` by
        metis_tac[freshWritesTheory.not_fresh_at_mono] >>
      `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st2 x` by
        metis_tac[freshWritesTheory.not_fresh_at_mono] >>
      `compile_array_subscript (vv_operand bvv) iop F n (word_scale LocMemory)
         (type_memory_size elem_tv) (is_signed_type (expr_type e2))
         (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory) st2 = (dst,sb)` by
        (qpat_assum `type_memory_bytes cenv et = _` (fn sz =>
           qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _`
             (ACCEPT_TAC o SIMP_RULE (srw_ss()) [elem_size_in_location_def,is_slot_addressed_def,sz]))) >>
      `st2.cs_next_id <= sb.cs_next_id` by
        (qpat_assum `compile_array_subscript _ _ F _ _ (type_memory_size _) _ _ _ = _`
           (SUBST1_TAC o SYM o SIMP_RULE (srw_ss()) [] o AP_TERM ``SND : operand # compile_state -> compile_state``) >>
         irule (cj 3 (iffLR exprLoweringPropsTheory.ci_mono_def)) >>
         irule exprLoweringPropsTheory.ci_mono_compile_array_subscript >>
         simp[exprLoweringPropsTheory.ci_mono_compile_ptr_load]) >>
      `vv_own cenv cx (ArrayT et (Fixed n)) sa st2 fin (Value (ArrayV (SArrayV kvs)))
         (LocatedValue (ArrayT et (Fixed n)) (mk_ptr (vv_operand bvv) LocMemory)) it` by
        (irule subscript_value_own_located >> simp[is_word_type_def] >>
         qexists `sm` >> metis_tac[]) >>
      `vv_at cenv cx (ArrayT et (Fixed n)) sa st2 fin (Value (ArrayV (SArrayV kvs)))
         (LocatedValue (ArrayT et (Fixed n)) (mk_ptr (vv_operand bvv) LocMemory)) it` by
        (irule exprSimIfExpWidenedOwnedProvenanceTheory.vv_own_memory_transport >>
         simp[vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
         qexistsl [`ArrayTV elem_tv (Fixed n)`,`ArrayT et (Fixed n)`,`ArrayT et (Fixed n)`] >> simp[]) >>
      `n <> 0` by
        (Cases_on `n` >> simp[] >>
         qpat_x_assum `evaluate_type _ (ArrayT et (Fixed 0)) = SOME _` mp_tac >>
         simp[Once vyperValueTheory.evaluate_type_def]) >>
      simp[GSYM mk_ptr_def, vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
      rpt conj_tac
      >- (qexists `compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory` >> simp[])
      >- (qpat_assum `w2n addr + type_memory_size (ArrayTV _ (Fixed _)) < _`
            (ACCEPT_TAC o REWRITE_RULE [valueEncodingTheory.type_memory_size_def]))
      >- (strip_tac >>
          `ptr_mem_ok cx (ArrayT et (Fixed n)) (ArrayV (SArrayV kvs))
             (vv_operand bvv) Gi tni it` by
            (qpat_assum `expr_type e1 = ArrayT et (Fixed n)` (fn ety =>
               qpat_assum `ptr_vv_ok _ _ _ bvv fin Gi tni it`
                 (mp_tac o REWRITE_RULE [ety])) >>
             qpat_assum `!t p. bvv = LocatedValue t p ==> _` mp_tac >>
             rpt (pop_assum kall_tac) >> Cases_on `bvv` >>
             simp[vv_operand_def, bodyPtrDefsTheory.ptr_vv_ok_def,
                  bodyPtrDefsTheory.ptr_val_ok_def, is_word_type_def,
                  vyperStateTheory.read_result_def, vyperStateTheory.return_def]) >>
          qpat_assum `ptr_mem_ok _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.ptr_mem_ok_def]) >>
          disch_then (qspecl_then [`ArrayTV elem_tv (Fixed n)`,`addr`] mp_tac) >>
          simp[val_footprint_def, exprSimPropsTheory.val_store_size_def,
               valueEncodingTheory.type_memory_size_def] >>
          strip_tac >> rename1 `FLOOKUP Gi x = SOME (b,len)` >>
          qexistsl [`b`,`len`] >> gvs[ptrDisciplineTheory.op_prov_def])
      >- (strip_tac >>
          `alloca_next_valid it` by
            metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca,
                      venomMemDefsTheory.alloca_inv_def] >>
          qpat_assum `vv_own _ _ _ _ st2 _ _ (LocatedValue _ _) _`
            (mp_tac o SIMP_RULE (srw_ss()) [vv_own_def, mk_ptr_def,
                    vyperStateTheory.read_result_def, vyperStateTheory.return_def]) >>
          disch_then (qspec_then `ArrayTV elem_tv (Fixed n)` mp_tac) >>
          simp[val_footprint_def,valueEncodingTheory.type_memory_size_def] >>
          strip_tac >> irule instMemFrontierTheory.alloca_region_below_frontier >>
          simp[] >> qexistsl [`aid`,`b`,`sz`] >> simp[])
      >- (qexists `ArrayT et (Fixed n)` >> simp[])) >>
  qpat_x_assum `!cap. Dynamic n = Dynamic cap ==> _`
    (qspec_then `n` (strip_assume_tac o SIMP_RULE (srw_ss()) [])) >>
  qpat_x_assum `v = ArrayV (DynArrayV _)` SUBST_ALL_TAC >>
  simp[IgnAsm `i = _`] >>
  `?res r q Gq tq.
    r = (if idx_in_range (is_signed_type (expr_type e2)) iw (n2w (LENGTH vs))
         then OK q else Abort Revert_abort q) /\
    captured_dynamic_itinerary DO func (Var x) iop dst (type_memory_size elem_tv)
      (is_signed_type (expr_type e2)) iw (n2w (LENGTH vs)) st2 sb (it,Gi,tni) (q,Gq,tq) /\
    (!tail. select_result cx (ArrayT et (Dynamic n)) (Value (ArrayV (DynArrayV vs)))
      (ValueSubscript (IntV i)) (fin with gas_obs := tail) = (res,fin with gas_obs := tail)) /\
    storage_trace_domain cx st0 fin.storage_trace /\
    (!H. valid_horizon cx st0 H fin.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (it,Gi,tni) [] (r,Gq,tq) /\
      ((?z. r = OK z /\
       subscript_dynamic_select_post DF lo d ctx func cenv cx et e1 e2 es sa sb s0 G0 tn0 dst
         H res (fin with gas_obs := []) Gq tq z) \/
       (exit_result r /\ expr_exit res r /\ halt_exit H cx (fin with gas_obs := []) res r /\
         (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))))`
  suffices_by
    (strip_tac >> qexistsl [`res`,`r`,`Gq`,`tq`] >> asm_rewrite_tac[] >>
     qexistsl [`type_memory_size elem_tv`,`iw`,`n2w (LENGTH vs)`,`q`] >> asm_rewrite_tac[]) >>
  irule subscript_dynamic_value_select_observed >>
  `LENGTH vs < dimword (:256)` by
    (qpat_assum `LENGTH vs <= n` mp_tac >>
     `n < dimword (:256)` by
       metis_tac[typedArrayLoopValuesTheory.evaluate_type_dynarray_count_bound] >>
     decide_tac) >>
  `compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory =
     (\op. emit_op MLOAD [op])` by simp[FUN_EQ_THM,compile_ptr_load_def] >>
  `compile_array_subscript (vv_operand bvv) iop T 0 32 (type_memory_size elem_tv)
     (is_signed_type (expr_type e2)) (\op. emit_op MLOAD [op]) st2 = (dst,sb)` by
    ((qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[elem_size_in_location_def,is_slot_addressed_def,word_scale_def] >> (gvs[elem_size_in_location_def, is_slot_addressed_def, word_scale_def]))) >>
  `st2.cs_next_id <= sb.cs_next_id` by
    (qpat_assum `compile_array_subscript _ _ T _ _ (type_memory_size _) _ _ _ = _`
       (SUBST1_TAC o SYM o SIMP_RULE (srw_ss()) [] o AP_TERM ``SND : operand # compile_state -> compile_state``) >>
     irule (cj 3 (iffLR exprLoweringPropsTheory.ci_mono_def)) >>
     irule exprLoweringPropsTheory.ci_mono_compile_array_subscript >>
     simp[exprLoweringPropsTheory.ci_mono_emit_op]) >>
  `vv_own cenv cx (ArrayT et (Dynamic n)) sa st2 fin (Value (ArrayV (DynArrayV vs)))
     (LocatedValue (ArrayT et (Dynamic n)) (mk_ptr (vv_operand bvv) LocMemory)) it` by
    (irule subscript_value_own_located >> simp[is_word_type_def] >>
     qexists `sm` >> metis_tac[]) >>
  qpat_assum `vv_operand bvv = Var x` (fn eq =>
    map_every (fn pat => qpat_assum pat (assume_tac o REWRITE_RULE [eq]))
      [`op_taint tni (vv_operand bvv) = _`,
       `eval_operand (vv_operand bvv) it = SOME addr`,
       `compile_array_subscript (vv_operand bvv) iop T 0 32 _ _ _ _ = _`,
       `vv_own _ _ _ _ st2 _ _ (LocatedValue _ (mk_ptr (vv_operand bvv) _)) _`]) >>
  `w2n addr + (n * type_memory_size elem_tv + 32) < dimword (:256)` by
    (qpat_assum `w2n addr + type_memory_size (ArrayTV _ (Dynamic _)) < _` mp_tac >>
     rewrite_tac[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
  `w2n addr + (n * type_memory_size elem_tv + 32) <= it.vs_alloca_next` by
    (`alloca_next_valid it` by
        metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca,
                  venomMemDefsTheory.alloca_inv_def] >>
      qpat_assum `vv_own _ _ _ _ st2 _ _ (LocatedValue _ _) _`
        (mp_tac o SIMP_RULE (srw_ss()) [vv_own_def, mk_ptr_def,
                vyperStateTheory.read_result_def, vyperStateTheory.return_def]) >>
      disch_then (qspec_then `ArrayTV elem_tv (Dynamic n)` mp_tac) >>
      simp[val_footprint_def,valueEncodingTheory.type_memory_size_def] >>
      strip_tac >> irule instMemFrontierTheory.alloca_region_below_frontier >>
      simp[] >> qexistsl [`aid`,`b'`,`sz'`] >> simp[] >> decide_tac) >>
  simp[GSYM mk_ptr_def, ptrDisciplineTheory.op_prov_def] >>
  rpt conj_tac
  >- (qexists `0` >> simp[])
  >- (qexistsl [`ArrayT et (Dynamic n)`,`st2`] >> simp[]) >>
  qexists `addr` >> fs[arithmeticTheory.ADD_COMM]
QED

Resume subscript_unframed_array_vv_full[value]:
  `fixed_select_scalar_intro lo (gas_explicit_sites ctx shadow_ctx) ctx func PG
      (\sa sc sb s r. T)` by
    (simp[fixed_select_scalar_intro_def, fixed_select_cuts_def] >>
     rpt gen_tac >> strip_tac >>
     drule_all bodyFullTargetArraySuffixTheory.array_tail_scalar_uniform >>
     disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] mp_tac) >> simp[]) >>
  assume_tac captured_dynamic_scalar_rule_trivial >>
  drule_all_then strip_assume_tac nocopy_value_select_observed >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_intro >>
  qexistsl [`Gz`,`fin`,`[]`,`r`,`res`,`tnz`] >>
  simp[gasSummaryTheory.gas_explicit_def] >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  fs[subscript_dynamic_select_post_def, post_value_type_def, mk_ptr_def, vv_location_def]
QED

Resume subscript_unframed_array_vv_full[copied]:
  `copies_subscript_base cenv e1 e2` by fs[] >>
  `!s raw mid saved. eval_expr cx e1 s = (INL raw,mid) /\
     read_result cx raw mid = (INL saved,mid) ==> body_expr_full_ok cx e2` by
    (rpt strip_tac >> first_x_assum irule >>
     qexistsl [`raw`,`Value saved`,`s`,`mid`,`mid`,`mid`] >>
     simp[vyperStateTheory.bind_def,vyperStateTheory.return_def]) >>
  irule (Q.SPEC `T` subscript_copied_bind_caller_frames) >>
  qpat_assum `expr_type e1 = ArrayT et bd` (irule_at Any) >>
  qpat_assum `expr_body_pre _ _ _ _ _` (irule_at Any) >>
  qpat_assum `body_inv _ _ _ _` (irule_at Any) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS)
  >- suspend "copied_select" >>
  drule_then assume_tac
    exprSimSubscriptArraySourceTheory.copies_subscript_base_not_array_slot_base >>
  drule_all subscript_array_copy_snapshot_caller_frame >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] strip_assume_tac) >>
  qexistsl [`u`,`Gc`,`tnc`,`q`,`w`,`atv`] >> simp[]
QED

Resume subscript_unframed_array_vv_full[copied_select]:
  qpat_x_assum `T ==> _` (strip_assume_tac o REWRITE_RULE []) >>
  `expr_body_pre cenv cx env e2 (mid with gas_obs := ic)` by
    (`expr_body_pre cenv cx env (Subscript v8 e1 e2) (es with gas_obs := gs)` by simp[] >>
     drule_all_then assume_tac expr_body_pre_array_subscript_index_after_base >> simp[]) >>
  drule_all_then strip_assume_tac exprSimConcatArgsTheory.concat_head_typed >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==>
     stmt_state_rel H ctx func cenv cx fin z /\ storage_well_formed_on cx fin (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx fin Gi tni z` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >>
     fs[expr_post_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  drule_all_then strip_assume_tac exprSimSubscriptArraySuffixTheory.framed_array_index_post_view >>
  qpat_assum `copies_subscript_base _ _ _`
    (assume_tac o MATCH_MP exprSimSubscriptArraySourceTheory.copies_subscript_base_not_array_slot_base) >>
  `expr_body_pre cenv cx env e1 es` by
    (irule expr_body_pre_array_subscript_base >>
     qpat_assum `expr_body_pre _ _ _ (Subscript _ _ _) _` (irule_at Any) >> simp[]) >>
  `well_typed_expr env (Subscript v8 e1 e2) /\ well_typed_expr env e1` by fs[expr_body_pre_def] >>
  `v8 = et` by
    (drule_all vyperTypeConstantFoldTheory.constant_subscript_type_ok >>
     simp[vyperTypeSystemTheory.subscript_type_ok_def]) >>
  qpat_x_assum `v8 = et` SUBST_ALL_TAC >>
  qpat_x_assum `key = IntV i` SUBST_ALL_TAC >>
  `is_word_type (expr_type e2)` by
    (qpat_assum `evaluate_type _ (expr_type e2) = _` mp_tac >>
     qpat_assum `value_has_type tv (IntV i)` mp_tac >> rpt (pop_assum kall_tac) >>
     Cases_on `expr_type e2` >>
     simp[vyperValueTheory.evaluate_type_def, AllCaseEqs(),
          vyperTypingTheory.value_has_type_def, is_word_type_def] >>
     rpt strip_tac >> gvs[vyperTypingTheory.value_has_type_def, is_word_type_def]) >>
  `op_taint tni iop = {} /\ op_prov Gi iop = NONE` by
    fs[bodyPtrDefsTheory.ptr_val_ok_def] >>
  `allocas_from lo z` by fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp z` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ fin z /\ _`
       (qspec_then `storage_trace_horizon fin.storage_trace`
         (drule_then (ACCEPT_TAC o
            MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp o CONJUNCT1)))) >>
  `exprLoweringProps$ci_mono sa sm /\ exprLoweringProps$ci_mono sm sc /\
   exprLoweringProps$ci_mono sc si` by
    (conj_tac
     >- (qspecl_then [`cenv`,`ty`,`e1`,`sa`] mp_tac
           (CONJUNCT1 exprLoweringPropsTheory.compile_expr_ci_mono) >> simp[]) >>
     conj_tac
     >- (qspecl_then [`cenv`,`T`,`bvv`,`sm`] mp_tac
           exprLoweringPropsTheory.ci_mono_compile_snapshot_vv >> simp[]) >>
     qspecl_then [`cenv`,`ty`,`e2`,`sc`] mp_tac
       exprLoweringPropsTheory.ci_mono_lower_value_compile_expr >> simp[]) >>
  `sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_var <= si.cs_next_var /\
   sa.cs_next_id <= sm.cs_next_id /\ sc.cs_next_id <= si.cs_next_id` by
    fs[exprLoweringPropsTheory.ci_mono_def] >>
  `local_ptrs_reserved cenv sc` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `!x. iop = Var x ==> not_fresh_at si x` by
    (qpat_assum `lower_value compile_expr cenv ty e2 sc = _`
      (mp_then Any mp_tac compile_lower_value_var) >> simp[]) >>
  `vv_own cenv cx (ArrayT et bd) sa si fin (Value saved) cvv z` by
    (irule exprSimCalldataSliceTheory.vv_own_start_mono >>
     qexists `sm` >> simp[] >>
     irule exprSimIfExpWidenedAdapterTheory.vv_own_alloc_mono_frame >>
     metis_tac[]) >>
  drule_then strip_assume_tac vyperTypeValuesTheory.evaluate_type_ArrayT_cases >>
  qpat_x_assum `atv = ArrayTV _ _` SUBST_ALL_TAC >>
  `type_memory_bytes cenv et = type_memory_size elem_tv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `eval_operand (Var q) z = SOME w` by simp[venomStateTheory.eval_operand_def] >>
  `op_taint tni (Var q) = {} /\
   ?b psz. op_prov Gi (Var q) = SOME (b,psz) /\ b <= w2n w /\
           w2n w + type_memory_size (ArrayTV elem_tv bd) <= b + psz` by
    (qpat_x_assum `ptr_covers Gi tni q z _`
       (strip_assume_tac o REWRITE_RULE [bodyPtrDefsTheory.ptr_covers_def]) >>
     gvs[ptrDisciplineTheory.op_prov_def]) >>
  `vv_at cenv cx (ArrayT et bd) sa si fin (Value saved) cvv z` by
    (simp[] >> irule exprSimIfExpWidenedOwnedProvenanceTheory.vv_own_memory_transport >>
     simp[vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
     qexistsl [`ArrayTV elem_tv bd`,`ArrayT et bd`,`ArrayT et bd`] >> gvs[]) >>
  `val_footprint (ArrayTV elem_tv bd) saved = type_memory_size (ArrayTV elem_tv bd)` by
    (irule annassignRelayoutSourceTheory.nonbytes_evaluated_val_footprint >>
     qexistsl [`get_tenv cx`,`ArrayT et bd`] >> simp[is_bytestring_type_def]) >>
  `stmt_state_rel (storage_trace_horizon fin.storage_trace) ctx func cenv cx fin z` by simp[] >>
  `alloca_next_valid z` by
    metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca,
              venomMemDefsTheory.alloca_inv_def] >>
  qpat_x_assum `cvv = LocatedValue _ _` SUBST_ALL_TAC >>
  `type_memory_size (ArrayTV elem_tv bd) <> 0 ==>
   w2n w + type_memory_size (ArrayTV elem_tv bd) <= z.vs_alloca_next /\
   w2n w + type_memory_size (ArrayTV elem_tv bd) < dimword (:256)` by
    (strip_tac >>
     qpat_x_assum `vv_own _ _ _ sm sc _ _ _ _` mp_tac >>
     simp[vv_own_def, mk_ptr_def, vyperStateTheory.read_result_def,
          vyperStateTheory.return_def] >> disch_then strip_assume_tac >> gvs[] >>
     conj_tac
     >- (irule instMemFrontierTheory.alloca_region_below_frontier >>
         simp[] >> qexistsl [`aid`,`b'`,`sz`] >> simp[]) >>
     `stmt_state_rel (storage_trace_horizon fin.storage_trace) ctx func cenv cx fin z` by simp[] >>
     qpat_assum `stmt_state_rel _ _ _ _ _ fin z`
       (mp_then Any (assume_tac o CONJUNCT1) exprSimPropsTheory.stmt_state_rel_region_lt) >>
     qpat_assum `!aid b sz. FLOOKUP z.vs_allocas aid = _ ==> _`
       (drule_then mp_tac) >> decide_tac) >>
  `w2n w + type_memory_size (ArrayTV elem_tv bd) < dimword (:256)` by
    (Cases_on `type_memory_size (ArrayTV elem_tv bd) = 0` >> simp[wordsTheory.w2n_lt]) >>
  `si.cs_next_id <= sb.cs_next_id` by
    (qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _`
       (SUBST1_TAC o SYM o SIMP_RULE (srw_ss()) [] o AP_TERM ``SND : operand # compile_state -> compile_state``) >>
     irule (cj 3 (iffLR exprLoweringPropsTheory.ci_mono_def)) >>
     irule exprLoweringPropsTheory.ci_mono_compile_array_subscript >>
     simp[exprLoweringPropsTheory.ci_mono_compile_ptr_load]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  Cases_on `bd`
  >- suspend "copied_fixed" >>
  suspend "copied_dynamic"
QED

Resume subscript_unframed_array_vv_full[copied_fixed]:
  `?kvs. saved = ArrayV (SArrayV kvs)` by
    (qpat_assum `value_has_type (ArrayTV _ (Fixed _)) saved` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `saved` >> simp[vyperTypingTheory.value_has_type_inv] >>
     qmatch_goalsub_rename_tac `ArrayV av` >> Cases_on `av` >>
     simp[vyperTypingTheory.value_has_type_inv]) >>
  qpat_x_assum `saved = ArrayV _` SUBST_ALL_TAC >>
  qpat_x_assum `vv = LocatedValue _ _` SUBST_ALL_TAC >>
  `n < dimword (:256)` by metis_tac[typedCopyCompleteArrayTheory.evaluate_type_fixed_count_bound] >>
  `n <> 0` by
    (Cases_on `n` >> simp[] >>
     qpat_x_assum `evaluate_type _ (ArrayT et (Fixed 0)) = SOME _` mp_tac >>
     simp[Once vyperValueTheory.evaluate_type_def]) >>
  simp[mk_ptr_def, vv_location_def, vv_operand_def, post_value_type_def] >>
  irule (SIMP_RULE (srw_ss()) [mk_ptr_def, vv_location_def, vv_operand_def,
                               post_value_type_def] subscript_fixed_memory_select_full) >>
  simp[] >>
  qexistsl [`Var q`,`iop`,
    `compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory`,`si`,
    `ArrayT et (Fixed n)`,`w`,`word_scale LocMemory`] >>
  fs[GSYM mk_ptr_def, elem_size_in_location_def, is_slot_addressed_def,
     vyperStateTheory.read_result_def, vyperStateTheory.return_def,
     valueEncodingTheory.type_memory_size_def]
QED

Resume subscript_unframed_array_vv_full[copied_dynamic]:
  `?vs. saved = ArrayV (DynArrayV vs) /\ LENGTH vs <= n` by
    (qpat_assum `value_has_type (ArrayTV _ (Dynamic _)) saved` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `saved` >> simp[vyperTypingTheory.value_has_type_inv] >>
     qmatch_goalsub_rename_tac `ArrayV av` >> Cases_on `av` >>
     simp[vyperTypingTheory.value_has_type_inv]) >>
  qpat_x_assum `saved = ArrayV _` SUBST_ALL_TAC >>
  qpat_x_assum `vv = LocatedValue _ _` SUBST_ALL_TAC >>
  `LENGTH vs < dimword (:256)` by
    (`n < dimword (:256)` by
       metis_tac[typedArrayLoopValuesTheory.evaluate_type_dynarray_count_bound] >> decide_tac) >>
  `mem_word_taint tni.t_mem (w2n w) = {}` by
    metis_tac[bodyPtrBopInMemoryContentsTheory.dynarray_memory_header_clean] >>
  `compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory =
     (\op. emit_op MLOAD [op])` by simp[FUN_EQ_THM,compile_ptr_load_def] >>
  simp[mk_ptr_def, vv_location_def, vv_operand_def, post_value_type_def] >>
  irule (SIMP_RULE (srw_ss()) [mk_ptr_def, vv_location_def, vv_operand_def,
                               post_value_type_def] subscript_dynamic_value_select_full) >>
  simp[] >>
  qexistsl [`w`,`b`,`Var q`,`ArrayT et (Dynamic n)`,`0`,`iop`,`si`,`si`,`psz`] >>
  fs[GSYM mk_ptr_def, elem_size_in_location_def, is_slot_addressed_def, word_scale_def,
     valueEncodingTheory.type_memory_size_def]
QED

Finalise subscript_unframed_array_vv_full
