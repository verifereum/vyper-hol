(* Selection from the represented memory place after the no-copy index cut. *)
Theory bodyFullSubscriptNoCopyMemorySelect
Ancestors bodyFullSubscriptLocalCutOrigin[qualified,ignore_grammar] abiEncodeArgsSim[qualified,ignore_grammar] vyperPlaceResultTyping[qualified,ignore_grammar]
  option[qualified,ignore_grammar] vyperTypeValues[qualified,ignore_grammar]
  vyperTyping[qualified,ignore_grammar] vyperValueOperation[qualified,ignore_grammar]
  bodyFullSubscriptLiveLocalView bodyFullSubscriptCapturedEndpoint
  bodyFullSubscriptDynamicChildRow bodyFullSubscriptFixedSelect bodyFullSubscriptDynamicSelect
  bodyFullPreds bodySimFull exprSimSubscriptArraySuffix exprSimExtract32Post
  exprSimSubscriptArraySource exprSimProps exprSimSource exprSimHypsDefs
  exprOperandVar exprLoweringProps exprSimUnwrap exprSimVVFrame
  gasShadowCompile gasShadowState gasShadow gasExemptCert stateRelProj
  vyperStorageTrace vyperStorageFootprint bodyPtrDefs loweringPosts compileEnv
  vyperInterpreter vyperState vyperAST context exprSimWordArgs wordArgsPtr
  exprReasonOperand exprSimHyps bodyFullHashKeccakFixed[qualified,ignore_grammar]

Theorem subscript_nocopy_memory_place_select_full:
  body_inv tops ctx cenv cx /\
  ~subscript_reads_base cx e1 e2 /\ ~copies_subscript_base cenv e1 e2 /\
  expr_body_pre cenv cx env (Subscript ann e1 e2) es /\
  expr_type e1 = ArrayT et bd /\ place_type cenv e1 = ValPT (ArrayT et bd) /\
  post_value_type cenv e1 = expr_type e1 /\
  ~(?n i p. bd = Fixed n /\ PlaceR (MemoryPlace id path) = PlaceR (MemoryPlace i p) /\ base_from_pop e1) /\
  compile_expr cenv ty e1 sa = (bvv,sm) /\
  lower_value compile_expr cenv ty e2 sm = (iop,st2) /\
  loc = (case vv_location bvv of SOME l => l | NONE => LocMemory) /\
  compile_array_subscript (vv_operand bvv) iop
    (case bd of Fixed _ => F | Dynamic _ => T)
    (case bd of Fixed n => n | Dynamic _ => 0)
    (word_scale loc) (elem_size_in_location cenv loc et)
    (is_signed_type (expr_type e2))
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc) st2 = (dst,sb) /\
  fn_has_code sa sb func /\ fn_has_code st2 sb func /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  local_ptrs_reserved cenv st2 /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_var <= st2.cs_next_var /\ sm.cs_next_id <= st2.cs_next_id /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  eval_expr cx e1 (es with gas_obs := gs1) = (INL (PlaceR (MemoryPlace id path)),mid) /\
  bind (eval_expr cx e2) (read_result cx) (mid with gas_obs := gs2) = (INL key,fin) /\
  storage_trace_domain cx st0 fin.storage_trace /\ mid.gas_obs = [] /\ fin.gas_obs = [] /\
  ~s.vs_halted /\ ~it.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  it.vs_current_bb = st2.cs_current_bb /\ it.vs_inst_idx = LENGTH st2.cs_current_insts /\
  alloca_history func s /\ alloca_history func it /\
  s0.vs_alloca_next <= s.vs_alloca_next /\ s.vs_alloca_next <= it.vs_alloca_next /\
  vv_store_bound cx (post_value_type cenv e1) (lowered_value_type cenv e1)
    mid (PlaceR (MemoryPlace id path)) bvv s /\
  ptr_vv_ok cx (post_value_type cenv e1) (PlaceR (MemoryPlace id path)) bvv mid G1 tn1 s /\
  (!v. PlaceR (MemoryPlace id path) = Value v /\ ~is_word_type (post_value_type cenv e1) /\
       ~is_bytestring_type (post_value_type cenv e1) ==>
       vv_own cenv cx (post_value_type cenv e1) sa sm mid (PlaceR (MemoryPlace id path)) bvv s /\
       (!t p. bvv = LocatedValue t p ==> p.ptr_location = LocMemory)) /\
  (cenv.ce_is_ctor /\ vv_location bvv = SOME LocCode ==>
   ?v. read_result cx (PlaceR (MemoryPlace id path)) mid = (INL v,mid) /\
       !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e1) = SOME rt /\
              eval_operand (vv_operand bvv) s = SOME w ==>
              w2n w + type_memory_size rt <= lo /\
              (!mem. mem_agree_outside tn1.t_mem s.vs_memory mem ==>
                     val_in_memory rt v (w2n w) mem)) /\
  (!t op. bvv = StackValue t op /\ ~is_word_type (post_value_type cenv e1) ==>
          ptr_buf_ok cenv e1 op G1 s) /\
  (!t p. bvv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
         ptr_buf_ok cenv e1 p.ptr_operand G1 s) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  expr_store_bound cx (post_value_type cenv e2) key iop it /\
  ptr_val_ok cx (post_value_type cenv e2) key iop Gi tni it /\
  (~is_word_type (post_value_type cenv e2) ==> ptr_buf_ok cenv e2 iop Gi it) /\
  ghost_kept_at lo cenv mid sm G1 tn1 s Gi tni /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0 /\
    vv_post H ctx func cenv cx e1 es sa sm s0 mid (PlaceR (MemoryPlace id path)) bvv s /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 s /\
    expr_post H ctx func cenv cx e2 mid sm st2 s fin key iop it /\
    ghost_inv_at (DF H) lo d cenv cx fin Gi tni it) ==>
  gas_outcome_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (cx_tops cx) cx st0
    (select_result cx (ArrayT et bd) (PlaceR (MemoryPlace id path)) (ValueSubscript key)) (fin,it,Gi,tni)
    (\H res ee G tn t. ?tv. res = INL tv /\
      vv_post H ctx func cenv cx (Subscript ann e1 e2) es sa sb s0 ee tv (LocatedValue ann (mk_ptr dst loc)) t /\
      vv_store_bound cx (post_value_type cenv (Subscript ann e1 e2))
        (lowered_value_type cenv (Subscript ann e1 e2)) ee tv (LocatedValue ann (mk_ptr dst loc)) t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ptr_vv_ok cx (post_value_type cenv (Subscript ann e1 e2)) tv (LocatedValue ann (mk_ptr dst loc)) ee G tn t /\
      (!v. tv = Value v /\ ~is_word_type (post_value_type cenv (Subscript ann e1 e2)) /\
           ~is_bytestring_type (post_value_type cenv (Subscript ann e1 e2)) ==>
           vv_own cenv cx (post_value_type cenv (Subscript ann e1 e2)) sa sb ee tv (LocatedValue ann (mk_ptr dst loc)) t /\
           (!t' p. (LocatedValue ann (mk_ptr dst loc)) = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
      (cenv.ce_is_ctor /\ vv_location (LocatedValue ann (mk_ptr dst loc)) = SOME LocCode ==>
       ?val. read_result cx tv ee = (INL val,ee) /\
             !rt w. evaluate_type (get_tenv cx) (post_value_type cenv (Subscript ann e1 e2)) =
                    SOME rt /\ eval_operand (vv_operand (LocatedValue ann (mk_ptr dst loc))) t = SOME w ==>
                    w2n w + type_memory_size rt <= lo /\
                    (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                           val_in_memory rt val (w2n w) mem)) /\
      (!t' op. (LocatedValue ann (mk_ptr dst loc)) = StackValue t' op /\
               ~is_word_type (post_value_type cenv (Subscript ann e1 e2)) ==>
               ptr_buf_ok cenv (Subscript ann e1 e2) op G t) /\
      (!t' p. (LocatedValue ann (mk_ptr dst loc)) = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
              ptr_buf_ok cenv (Subscript ann e1 e2) p.ptr_operand G t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `H0 = storage_trace_horizon fin.storage_trace` >>
  `valid_horizon cx st0 H0 fin.storage_trace` by
    fs[Abbr `H0`, storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `expr_body_pre cenv cx env e1 es` by
    (qpat_assum `expr_body_pre _ _ _ (Subscript _ _ _) _`
       (mp_then Any irule exprSimSubscriptArraySourceTheory.expr_body_pre_array_subscript_base_eval) >>
     qpat_assum `eval_expr cx e1 _ = (INL _,_)` (irule_at Any) >> simp[]) >>
  `expr_body_pre cenv cx env e1 (es with gas_obs := gs1)` by simp[] >>
  drule_all_then strip_assume_tac expr_body_pre_runtime_typed >>
  `?etv. evaluate_type (get_tenv cx) et = SOME etv /\
     evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd)` by
    (qpat_assum `evaluate_type (get_tenv cx) (expr_type e1) = _` mp_tac >>
     qpat_assum `expr_type e1 = ArrayT et bd` (fn th => rewrite_tac[th]) >>
     metis_tac[vyperTypeValuesTheory.evaluate_type_ArrayT_cases]) >>
  `post_value_type cenv e1 = ArrayT et bd` by simp[] >>
  `?bt p. bvv = LocatedValue bt p /\ p.ptr_location = LocMemory` by
    (Cases_on `bvv` >>
     qpat_assum `vv_post H0 _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o PURE_REWRITE_RULE [vv_post_def, vv_at_def]) >>
     simp[is_word_type_def] >> metis_tac[]) >>
  `ann = et` by
    (`well_typed_expr env (Subscript ann e1 e2)` by fs[expr_body_pre_def] >>
     `well_typed_expr env e1` by fs[expr_body_pre_def] >>
     drule_all vyperTypeConstantFoldTheory.constant_subscript_type_ok >>
     simp[vyperTypeSystemTheory.subscript_type_ok_def]) >>
  `?tvi. evaluate_type (get_tenv cx) (expr_type e2) = SOME tvi /\
         value_has_type tvi key` by
    (`expr_body_pre cenv cx env (Subscript ann e1 e2) (es with gas_obs := gs1)` by simp[] >>
     drule_all_then assume_tac expr_body_pre_array_subscript_index_after_base >>
     `?ir. eval_expr cx e2 (mid with gas_obs := gs2) = (INL ir,fin) /\
           read_result cx ir fin = (INL key,fin)` by
       (drule_then strip_assume_tac vyperStatePreservationTheory.bind_split
        >- (rename1 `read_result cx ir _ = (INL key,fin)` >>
            qpat_assum `read_result cx ir _ = _`
              (SUBST_ALL_TAC o MATCH_MP vyperStateTheory.read_result_state) >>
            qexists `ir` >> simp[])
        >> gvs[]) >>
     `expr_body_pre cenv cx env e2 (mid with gas_obs := gs2)` by simp[] >>
     drule_all_then strip_assume_tac expr_body_pre_runtime_typed >>
     metis_tac[]) >>
  drule_all_then strip_assume_tac framed_array_index_post_view >>
  `loc = LocMemory /\ vv_operand bvv = p.ptr_operand` by simp[vv_operand_def, vv_location_def] >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sm x` by metis_tac[cj 1 compiler_compile_var] >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at st2 x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x. iop = Var x ==> not_fresh_at st2 x` by metis_tac[compile_lower_value_var] >>
  `!l. p.ptr_operand <> Label l` by
    (`!id t. FLOOKUP env.var_types id = SOME t ==>
        ?x sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var x) sz)` by
       (qpat_assum `expr_body_pre cenv cx env e1 es` mp_tac >>
        rewrite_tac[expr_body_pre_def, expr_sim_inv_def] >>
        rpt strip_tac >> first_x_assum drule >> simp[]) >>
     `reason_uniform_shape compile_expr cenv ty e1` by
       (irule compile_expr_reason_uniform >> qexists `env` >> fs[expr_body_pre_def]) >>
     qpat_x_assum `reason_uniform_shape _ _ _ _` mp_tac >>
     simp[reason_uniform_shape_def] >> strip_tac >>
     first_x_assum drule >> simp[reason_result_shape_def]) >>
  `type_memory_bytes cenv et = type_memory_size etv` by
    (irule expr_sim_inv_memory_size >> simp[] >>
     qexistsl [`cx`,`env`,`es`] >> fs[expr_body_pre_def]) >>
  `is_int_type (expr_type e2)` by
    (`well_typed_expr env (Subscript ann e1 e2)` by fs[expr_body_pre_def] >>
     pop_assum mp_tac >>
     simp[Once (cj 7 vyperTypeSystemTheory.well_typed_expr_def)] >>
     strip_tac >> gvs[vyperTypeSystemTheory.subscript_type_ok_def] >>
     drule vyperTypeSystemTheory.type_place_expr_vtype_annotation >>
     rename1 `type_place_expr env e1 = SOME pty` >>
     strip_tac >> Cases_on `pty` >>
     gvs[vyperTypeSystemTheory.vtype_annotation_ok_def,
         vyperTypeSystemTheory.subscript_vtype_def, AllCaseEqs()]) >>
  `is_word_type (expr_type e2)` by
    (Cases_on `expr_type e2` >> gvs[vyperTypeSystemTheory.is_int_type_def] >>
     rename1 `is_word_type (BaseT ibt)` >> Cases_on `ibt` >>
     gvs[vyperTypeSystemTheory.is_int_type_def, is_word_type_def]) >>
  `op_taint tni iop = {} /\ op_prov Gi iop = NONE` by
    fs[ptr_val_ok_def, post_value_type_word] >>
  `allocas_from lo it` by fs[ghost_inv_at_def] >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (qpat_assum `eval_expr cx e1 _ = _`
       (mp_then Any mp_tac vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom) >>
     simp[]) >>
  `wb_frame cenv es mid sa s0 s` by
    (fs[vv_post_def, wb_frame_def] >> first_assum ACCEPT_TAC) >>
  `wb_frame cenv mid fin sm s it` by metis_tac[expr_post_frame] >>
  `wb_frame cenv es fin sa s0 it` by (drule_all wb_frame_trans >> simp[]) >>
  `~expr_has_effect (Subscript et e1 e2) ==> pure_frame cenv func es sa s0 it` by
    (simp[expr_has_effect_thm] >> strip_tac >>
     `pure_frame cenv func es sa s0 s` by fs[vv_post_def] >>
     `pure_frame cenv func mid sm s it` by (drule_all expr_post_pure_frame >> simp[]) >>
     irule pure_frame_trans >> simp[] >> qexistsl [`mid`,`sm`,`s`] >>
     fs[wb_frame_def] >> metis_tac[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gi tni` by
    (irule (INST_TYPE [``:'b`` |-> ``:256``] ghost_kept_at_wb_trans) >>
     simp[] >> conj_tac >- (qexistsl [`H0`,`ctx`,`cx`,`func`] >> simp[]) >>
     qexistsl [`G1`,`mid`,`mid`,`s`,`sm`,`tn1`] >> simp[]) >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==>
     stmt_state_rel H ctx func cenv cx fin it /\
     storage_well_formed_on cx fin (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx fin Gi tni it` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (qspec_then `H` (drule_then (map_every assume_tac o CONJUNCTS))) >>
     fs[expr_post_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp it` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ fin it /\ _`
       (qspec_then `H0` (drule_then (ACCEPT_TAC o
          MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp o CONJUNCT1)))) >>
  `ci_mono st2 sb` by
    (qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ st2 = _`
       (mp_tac o Q.AP_TERM `SND : (operand # compile_state) -> compile_state`) >>
     simp[NoAsms] >> disch_then (SUBST1_TAC o SYM) >>
     irule ci_mono_compile_array_subscript >> simp[ci_mono_compile_ptr_load]) >>
  `sa.cs_next_var <= st2.cs_next_var /\ st2.cs_next_id <= sb.cs_next_id` by
    fs[ci_mono_def] >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st2 x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st2 x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `s0.vs_alloca_next <= it.vs_alloca_next` by decide_tac >>
  qpat_x_assum `ann = et` SUBST_ALL_TAC >>
  qpat_x_assum `key = IntV i` SUBST_ALL_TAC >>
  qpat_x_assum `bvv = LocatedValue bt p` SUBST_ALL_TAC >>
  qpat_x_assum `loc = LocMemory` SUBST_ALL_TAC >>
  PURE_REWRITE_TAC [LET_THM] >>
  Cases_on `bd` >-
    (`~base_from_pop e1` by fs[] >>
     drule_all_then (map_every strip_assume_tac o CONJUNCTS) subscript_live_local_index_view >>
     `etv' = etv` by fs[] >> qpat_x_assum `etv' = etv` SUBST_ALL_TAC >>
     `?kvs. v = ArrayV (SArrayV kvs)` by
       (irule typedArrayLoopValuesTheory.value_has_type_sarray_cases >>
        goal_assum (drule_at Any)) >>
     qpat_x_assum `v = ArrayV (SArrayV kvs)` SUBST_ALL_TAC >>
     `n < dimword (:256)` by
       (drule targetSubscriptStorageTheory.target_storage_array_type_bound >>
        simp[vyperASTTheory.bound_length_def]) >>
     `type_memory_size (ArrayTV etv (Fixed n)) = n * type_memory_size etv` by
       simp[valueEncodingTheory.type_memory_size_def] >>
     `local_region cenv fin.scopes it id (w2n B) sz` by
       fs[loweringStateRelDefsTheory.local_region_def,
          vyperPlaceTypingTheory.runtime_place_typed_memory] >>
     `stmt_state_rel H0 ctx func cenv cx fin it` by metis_tac[expr_post_state] >>
     `w2n B + sz <= it.vs_alloca_next` by
       (drule_all bodyMemoryDefsTheory.body_local_region_frontier >> simp[]) >>
     `w2n a + n * type_memory_size etv <= it.vs_alloca_next` by decide_tac >>
     `place_ptr_rel cenv cx it (PlaceR (MemoryPlace id path)) a (SOME LocMemory)
          (Type (ArrayT et (Fixed n)))` by metis_tac[] >>
     `vv_at cenv cx (ArrayT et (Fixed n)) sa st2 fin (PlaceR (MemoryPlace id path))
        (LocatedValue bt (mk_ptr p.ptr_operand LocMemory)) it` by
       (simp[vv_at_def, mk_ptr_def, val_footprint_def] >>
        disj2_tac >> disj1_tac >> qexistsl [`id`,`w2n B`,`sz`] >>
        simp[local_val_at_def, local_place_at_def, local_path_at_def] >>
        `w2n B + k - w2n B = k` by decide_tac >> simp[] >>
        drule_all_then strip_assume_tac
          bodyFullSubscriptLocalCutOriginTheory.subscript_local_cut_returned_paths >>
        `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
        drule_all_then strip_assume_tac abiEncodeArgsSimTheory.abi_args_local_type_coherent >>
        `local_ptrs_rel func cenv es.scopes s0` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
        drule_all_then strip_assume_tac nameLoweringPropsTheory.local_ptrs_rel_value >>
        `w2n B + sz < dimword (:256)` by
          metis_tac[stmt_state_rel_region_lt] >>
        qpat_assum `place_ptr_rel _ _ _ _ _ _ (Type (ArrayT et (Fixed n)))`
          (mp_tac o REWRITE_RULE [place_ptr_rel_def]) >>
        simp[] >> strip_tac >> rename1 `mem_path_offset _ path = SOME (j,_)` >>
        `j + type_memory_size (ArrayTV etv (Fixed n)) <= sz` by
          (drule mem_path_offset_sound >> strip_tac >> decide_tac) >>
        `j < dimword (:256) /\ w2n B + j < dimword (:256)` by decide_tac >>
        `w2n (B + n2w j) = w2n B + j` by simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w] >>
        `j = k` by
          (qpat_assum `a = B + n2w j` (fn th =>
             qpat_assum `w2n a = w2n B + k` (mp_tac o REWRITE_RULE [th])) >> simp[]) >>
        simp[] >> qexists `path` >> simp[]) >>
     `type_memory_size etv <> 0 ==>
        ?b sz. op_prov Gi p.ptr_operand = SOME (b,sz) /\ b <= w2n a /\
               w2n a + n * type_memory_size etv <= b + sz` by
       (strip_tac >>
        `n <> 0` by
          (Cases_on `n` >> simp[] >>
           qpat_x_assum `evaluate_type _ (ArrayT et (Fixed 0)) = SOME _` mp_tac >>
           simp[Once vyperValueTheory.evaluate_type_def]) >>
        `ptr_mem_ok cx (ArrayT et (Fixed n)) (ArrayV (SArrayV kvs)) p.ptr_operand Gi tni it` by
          fs[ptr_vv_ok_def] >>
        `val_footprint (ArrayTV etv (Fixed n)) (ArrayV (SArrayV kvs)) <> 0` by
          simp[val_footprint_def] >>
        drule_all_then strip_assume_tac bodyPtrBopHashFootprintTheory.ptr_mem_ok_bounds >>
        qpat_x_assum `op_prov Gi _ = op_prov G1 _` kall_tac >>
        simp[ptrDisciplineTheory.op_prov_def] >>
        fs[val_store_size_def] >> decide_tac) >>
     qpat_assum `type_memory_bytes cenv et = _` (fn sz_th =>
       qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ st2 = _`
         (assume_tac o SRULE [vv_operand_def, word_scale_def, elem_size_in_location_def,
                              is_slot_addressed_def, sz_th])) >>
     BETA_TAC >> irule subscript_fixed_memory_select_full >>
     simp[IgnAsm `i = _`] >>
     goal_assum (drule_at (Pat `compile_array_subscript _ _ _ _ _ _ _ _ _ = _`)) >>
     qexistsl [`iw`,`bt`] >> simp[IgnAsm `op_prov Gi _ = op_prov G1 _`]) >>
  `?a vs x b sz.
     read_result cx (PlaceR (MemoryPlace id path)) fin = (INL (ArrayV (DynArrayV vs)),fin) /\
     runtime_place_typed cx fin (MemoryPlace id path) (ArrayTV etv (Dynamic n)) /\
     place_ptr_rel cenv cx it (PlaceR (MemoryPlace id path)) a (SOME LocMemory)
       (Type (ArrayT et (Dynamic n))) /\
     value_has_type (ArrayTV etv (Dynamic n)) (ArrayV (DynArrayV vs)) /\
     eval_operand p.ptr_operand it = SOME a /\
     (!mem. mem_agree_outside tni.t_mem it.vs_memory mem ==>
       val_in_memory (ArrayTV etv (Dynamic n)) (ArrayV (DynArrayV vs)) (w2n a) mem) /\
     LENGTH vs <= n /\ p.ptr_operand = Var x /\ FLOOKUP Gi x = SOME (b,sz) /\
     b <= w2n a /\ w2n a + 32 + n * type_memory_size etv <= b + sz /\
     w2n a + 32 + n * type_memory_size etv < dimword (:256) /\
     op_taint tni p.ptr_operand = {} /\ mem_word_taint tni.t_mem (w2n a) = {}` by
    (Cases_on `base_from_pop e1` >-
       (`expr_body_pre cenv cx env (Subscript et e1 e2) (es with gas_obs := gs1)` by simp[] >>
        `vv_post H0 ctx func cenv cx e1 (es with gas_obs := gs1) sa sm s0 mid
           (PlaceR (MemoryPlace id path)) (LocatedValue bt p) s` by
          (qpat_assum `vv_post H0 _ _ _ _ _ es _ _ _ _ _ _ _` mp_tac >>
           pure_rewrite_tac[vv_post_def, locals_kept_def, popped_kept_def,
                            vyperStateTheory.evaluation_state_accfupds, pure_frame_gas_obs] >> simp[]) >>
        `expr_post H0 ctx func cenv cx e2 (mid with gas_obs := gs2) sm st2 s fin (IntV i) iop it` by
          simp[extract32_expr_post_start_gas_obs] >>
        `ghost_kept_at lo cenv (mid with gas_obs := gs2) sm G1 tn1 s Gi tni` by
          (qpat_assum `ghost_kept_at lo cenv mid _ _ _ _ _ _` mp_tac >>
           pure_rewrite_tac[ghost_kept_at_def, vyperStateTheory.evaluation_state_accfupds] >> simp[]) >>
        `evaluate_type (get_tenv cx) (expr_type e1) = SOME (ArrayTV etv (Dynamic n))` by
          (qpat_assum `expr_type e1 = ArrayT _ _` (fn th => rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
        drule_all (SRULE [] (Q.INST [`raw` |-> `PlaceR (MemoryPlace id path)`]
          subscript_dynamic_header_at_index)) >> simp[] >>
        strip_tac >> fs[ptr_vv_ok_def] >> gvs[]) >>
     drule_all_then (map_every strip_assume_tac o CONJUNCTS) subscript_live_local_index_view >>
     `etv' = etv` by fs[] >> qpat_x_assum `etv' = etv` SUBST_ALL_TAC >>
     qpat_x_assum `!cap. Dynamic n = Dynamic cap ==> _` (qspec_then `n` mp_tac) >>
     simp[] >> strip_tac >> qexistsl [`vs`,`x`,`b`,`n'`] >>
     gvs[valueEncodingTheory.type_memory_size_def, IgnAsm `op_prov Gi _ = op_prov G1 _`]) >>
  qpat_assum `runtime_place_typed _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vyperPlaceTypingTheory.runtime_place_typed_memory]) >>
  `read_memory_path entry path = INL (ArrayV (DynArrayV vs))` by
    (qpat_x_assum `read_result cx (PlaceR (MemoryPlace id path)) fin = _` mp_tac >>
     simp[read_result_def, read_place_def, get_scopes_def, bind_def,
          lift_option_type_def, lift_sum_def] >>
     Cases_on `read_memory_path entry path` >> simp[return_def, raise_def]) >>
  `LENGTH vs < dimword (:256)` by
    (drule targetSubscriptStorageTheory.target_storage_array_type_bound >>
     simp[vyperASTTheory.bound_length_def] >> decide_tac) >>
  `w2n a + (32 + n * type_memory_size etv) <= it.vs_alloca_next` by
    (`stmt_state_rel H0 ctx func cenv cx fin it` by metis_tac[expr_post_state] >>
     qpat_assum `place_ptr_rel _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [place_ptr_rel_def]) >>
     rename [`FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var root) rs)`,
             `lookup_var root it = SOME B`, `a = B + n2w k`,
             `mem_path_offset rt path = SOME (k,_)`] >>
     `local_region cenv fin.scopes it id (w2n B) rs` by
       (simp[loweringStateRelDefsTheory.local_region_def] >> metis_tac[]) >>
     `w2n B + rs <= it.vs_alloca_next` by
       (drule_all bodyMemoryDefsTheory.body_local_region_frontier >> simp[]) >>
     `w2n B + rs < dimword (:256)` by metis_tac[stmt_state_rel_region_lt] >>
     `local_ptrs_rel func cenv fin.scopes it` by
       metis_tac[stmt_state_rel_local_ptrs_alloca] >>
     `type_memory_size entry.type <= rs` by
       (drule_all_then strip_assume_tac nameLoweringPropsTheory.local_ptrs_rel_value >> simp[]) >>
     `rt = entry.type` by
       ((drule_all_then (map_every strip_assume_tac o CONJUNCTS)
          bodyFullSubscriptLocalCutOriginTheory.subscript_local_cut_returned_paths >>
        `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
        drule_all_then strip_assume_tac abiEncodeArgsSimTheory.abi_args_local_type_coherent >>
        qpat_assum `typed_scope_transition es fin`
          (strip_assume_tac o REWRITE_RULE [vyperTypeEvalProofsTheory.typed_scope_transition_def]) >>
        drule_all_then strip_assume_tac vyperPlaceResultTypingTheory.scope_pop_trace_lookup >>
        drule_then strip_assume_tac vyperPlaceResultTypingTheory.entry_pop_trace_metadata >> fs[] >> (gvs[expr_body_pre_def, bodyFullSubscriptLocalCutOriginTheory.subscript_local_cut_returned_paths, abiEncodeArgsSimTheory.abi_args_local_type_coherent, vyperPlaceResultTypingTheory.scope_pop_trace_lookup, vyperPlaceResultTypingTheory.entry_pop_trace_metadata]))) >>
     `k + type_memory_size (ArrayTV etv (Dynamic n)) <= rs` by
       (drule mem_path_offset_sound >> strip_tac >>
        `tv = ArrayTV etv (Dynamic n)` by
          metis_tac[optionTheory.SOME_11] >>
        qpat_x_assum `tv = ArrayTV etv (Dynamic n)` SUBST_ALL_TAC >>
        qpat_x_assum `rt = entry.type` SUBST_ALL_TAC >>
        decide_tac) >>
     `k < dimword (:256) /\ w2n B + k < dimword (:256)` by decide_tac >>
     `w2n a = w2n B + k` by simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w] >>
     fs[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
  `compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory =
     (\op. emit_op MLOAD [op])` by simp[FUN_EQ_THM, compile_ptr_load_def] >>
  qpat_assum `compile_ptr_load _ _ LocMemory = _` (fn load_th =>
    qpat_assum `type_memory_bytes cenv et = _` (fn sz_th =>
      qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ st2 = _`
        (assume_tac o SRULE [vv_operand_def, word_scale_def, load_th,
                             elem_size_in_location_def, is_slot_addressed_def, sz_th]))) >>
  BETA_TAC >> irule subscript_dynamic_memory_select_full >>
  simp[IgnAsm `i = _`] >>
  qexistsl [`a`,`b`,`p.ptr_operand`,`0`,`iop`,`iw`,`st2`,`sz`] >>
  simp[ptrDisciplineTheory.op_prov_def, IgnAsm `i = _`,
       AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM,
       IgnAsm `op_prov Gi _ = op_prov G1 _`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  strip_tac >>
  irule (SRULE [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
    subscript_dynamic_child_input) >>
  simp[IgnAsm `i = _`] >>
  goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `bind _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `place_ptr_rel _ _ _ _ _ _ _`)) >>
  simp[IgnAsm `i = _`] >>
  goal_assum (drule_at (Pat `expr_body_pre _ _ _ (Subscript _ _ _) _`)) >>
  qpat_x_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 Gi tni` kall_tac >>
  goal_assum (drule_at (Pat `ghost_kept_at _ _ es _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `ghost_kept_at _ _ mid _ _ _ _ _ _`)) >>
  simp[IgnAsm `i = _`] >>
  goal_assum (drule_at (Pat `storage_trace_domain _ _ _`)) >>
  qexistsl [`DF`,`LocatedValue bt p`,`ctx`,`d`,`func`,`iop`,`st2`] >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ es s0 /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ fin it /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  simp[IgnAsm `i = _`]
QED
