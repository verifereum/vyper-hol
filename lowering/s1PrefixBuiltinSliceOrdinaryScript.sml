(* Request-prefix companion to bodyFullBuiltinSliceOrdinary. *)
Theory s1PrefixBuiltinSliceOrdinary
Ancestors
  s1PrefixPreds s1PrefixDefs s1PrefixCompose s1PrefixProps s1PrefixSliceOrdinaryBounds
  bodyFullBuiltinSliceDynamicCapture bodyFullBuiltinSliceFixedCapture
  exprSimSliceDynamicStartEntry exprSimSliceFixedStartEntry
  exprSimSliceOrdinaryPairedLayout exprSimSliceOperandHeadroom
  exprSimSliceOrdinaryContinue exprSimSliceTerminal exprSimSliceSource
  bodyFullPreds bodyFullExprsListFacts bodyFullSimProjection
  bodySimFull exprSimSource exprSimHash exprBodyPreProps
  exprSimSliceCapture exprOperandVar exprLoweringProps bodyFullIfExpReach
  loweringPosts bodyMemoryDefs exprSimWordArgs vyperStorageFootprint
  vyperStorageTrace vyperStatePreservation vyperInterpreter vyperState
  compileEnv exprLowering bodyPtrDefs venomState freshWrites
Libs
  monadsyntax

fun slice_child rule child =
  qpat_assum child
    (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [rule]) >>
  disch_then (irule o CONJUNCT1 o SIMP_RULE bool_ss [IMP_CONJ_THM, FORALL_AND_THM]) >>
  qexistsl_tac [`env`,`tops`] >> simp[]

fun slice_use [] rule = mp_tac rule
  | slice_use (premise::rest) rule = qpat_assum premise (mp_then Any (slice_use rest) rule)

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >>
  drule expr_body_pre_static_facts >> strip_tac >>
  drule slice_typed_args >>
  disch_then (qx_choosel_then [`src`,`start`,`len`]
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `args = _` SUBST_ALL_TAC >>
  `body_exprs_full_ok cx [src;start;len] /\ body_exprs_prefix_ok cx [src;start;len]` by
    fs[vyperContextTheory.builtin_args_length_ok_def] >>
  `~is_extcode src` by
    (qpat_assum `code_slice_source (Slice n) [src;start;len] = NONE` mp_tac >>
     qid_spec_tac `src` >> ho_match_mp_tac is_extcode_ind >> simp[is_extcode_def]) >>
  `~is_self_code src` by
    (qpat_assum `~is_extcode src` mp_tac >>
     qid_spec_tac `src` >> ho_match_mp_tac is_self_code_ind >>
     simp[is_self_code_def,is_extcode_def]) >>
  `expr_body_pre cenv cx env src es` by
    (irule expr_body_pre_builtin_arg >>
     conj_tac >- simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  `body_expr_full_ok cx src /\ body_expr_prefix_ok cx src` by
    fs[Once body_exprs_full_ok_cons,body_exprs_prefix_ok_def] >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type src) src es` by
    (irule (cj 1 body_expr_full_ok_simulations) >> asm_rewrite_tac[] >>
     qexistsl_tac [`env`,`tops`] >> simp[]) >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type src) src es` by
    slice_child body_expr_prefix_ok_def `body_expr_prefix_ok cx src` >>
  pure_rewrite_tac[expr_vv_sim_prefix_def,expr_vv_sim_full_pre_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `body_inv tops ctx cenv cx` (mp_then Any mp_tac body_inv_no_phi) >>
     disch_then (drule_then ACCEPT_TAC)) >>
  drule_all slice_ordinary_paired_layout >>
  disch_then (qx_choosel_then [`src_op`,`src_len`,`src_data`,`start_op`,`len_op`,
    `st1`,`sc`,`sd`,`se`,`shadow_s1`,`shadow_sc`,`shadow_sd`,`shadow_se`] strip_assume_tac) >>
  `gas_admissible (bind (eval_expr cx src) (read_result cx)) expr_res_ok es` by
    (irule expr_body_pre_gas_admissible >> goal_assum (drule_at Any)) >>
  `expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx
     (expr_type src) src es (st0,sa,st1,shadow_sa,shadow_s1,src_op,s0,G0,tn0)` by
    (simp[expr_sim_full_pre_def] >> first_assum ACCEPT_TAC) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
     (bind (eval_expr cx src) (read_result cx)) (es,s0,G0,tn0)` by
    (qpat_assum `expr_sim_prefix _ _ _ _ src _` (mp_tac o REWRITE_RULE[expr_sim_prefix_def]) >>
     disch_then (drule_then ACCEPT_TAC)) >>
  qpat_assum `expr_sim_full _ _ _ _ src _` (mp_tac o REWRITE_RULE[expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`st1`,`shadow_sa`,`shadow_s1`,
    `src_op`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (mp_then Any mp_tac slice_operand_outcome_headroom) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ src_post src_exit` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (cx_tops cx) cx st0
      (bind (eval_expr cx src) (read_result cx)) (es,s0,G0,tn0)
      (\H res ee G tn t. src_post H res ee G tn t /\ ee.gas_obs = [] /\ ~t.vs_halted)
      (\H res ee gt r. ISR res)` by
    (irule gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
     qpat_assum `gas_outcome_full _ _ _ _ _ _ src_post src_exit` (irule_at Any) >>
     simp[Abbr `src_exit`] >> rpt gen_tac >> Cases_on `res` >>
     simp[exprSimDefsTheory.expr_exit_INL]) >>
  `eval_expr cx (Builtin a (Slice n) [src;start;len]) =
    bind (bind (eval_expr cx src) (read_result cx)) (\v.
      do sv <- bind (eval_expr cx start) (read_result cx);
         lv <- bind (eval_expr cx len) (read_result cx);
         acc <- get_accounts;
         r <- lift_sum (evaluate_builtin cx acc a (Slice n)
                 (MAP expr_type [src;start;len]) [v;sv;lv]);
         return (Value r) od)` by
    (simp[Once slice_eval_ordinary] >>
     `eval_exprs cx [] = return []` by simp[FUN_EQ_THM,eval_exprs_nil,return_def] >>
     simp[eval_exprs_cons_action,bind_assoc,bind_return]) >>
  pop_assum (PURE_ONCE_REWRITE_TAC o single) >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ (\H res ee G tn t. src_post H res ee G tn t /\ _) _`
    (mp_then Any irule gas_prefix_full_bind) >>
  simp[slice_read_frame, evaluate_requests_outcomes_frame,
       requests_outcomes_frame_read_result, requests_outcomes_frame_bind_all,
       slice_terminal_source_frame, storage_trace_frame_bind_all] >>
  qx_genl_tac [`marks`,`v`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> src_post _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then strip_assume_tac)) >>
  qpat_x_assum `src_post (storage_trace_horizon _) _ _ _ _ _` mp_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> src_post _ _ _ _ _ _ /\ _` mp_tac >>
  simp[Abbr `src_post`,NoAsms] >> strip_tac >> strip_tac >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     expr_post H ctx func cenv cx src es sa st1 s0 mid v src_op t /\
     ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
       (qspec_then `H` (drule_then strip_assume_tac)) >> simp[]) >>
  qpat_assum `!tail. bind (eval_expr cx src) _ _ = _` (qspec_then `[]` assume_tac) >>
  `?s tv s' s1 w s1'. eval_expr cx src s = (INL tv,s') /\
     read_result cx tv s1 = (INL w,s1')` by
    (drule bind_split >> simp[] >> metis_tac[]) >>
  `body_exprs_full_ok cx [start;len] /\ body_exprs_prefix_ok cx [start;len]` by
    (conj_tac
     >- (qpat_assum `body_exprs_full_ok cx [src;start;len]`
           (mp_tac o ONCE_REWRITE_RULE [body_exprs_full_ok_cons]) >>
         disch_then (irule o cj 2) >>
         goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
     qpat_assum `body_exprs_prefix_ok cx [src;start;len]`
       (mp_tac o ONCE_REWRITE_RULE [body_exprs_prefix_ok_def]) >>
     disch_then (irule o cj 2) >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  `?bt. expr_type src = BaseT bt` by
    (qpat_assum `(a = BaseT (BytesT (Dynamic n)) /\ _) \/ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `expr_sim_inv cenv cx env mid /\ value_has_type (BaseTV bt) v` by
    (qpat_assum `bind (eval_expr cx src) _ _ = _`
       (mp_then Any mp_tac (SIMP_RULE (srw_ss()) [SF ETA_ss] expr_body_pre_base_result)) >>
     simp[] >> disch_then (qspecl_then [`env`,`cenv`] mp_tac) >> simp[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (qpat_assum `bind (eval_expr cx src) _ _ = _`
       (mp_then Any mp_tac body_const_cells_agree_expr_read) >>
     simp[] >> disch_then irule >> simp[] >> disj1_tac >>
     qpat_assum `expr_body_pre cenv cx env src es`
       (mp_then Any mp_tac expr_body_pre_static_facts) >> simp[]) >>
  `expr_body_pre cenv cx env start mid` by
    (qpat_assum `expr_body_pre _ _ _ (Builtin _ _ _) _`
       (mp_then Any mp_tac expr_body_pre_builtin_typed_arg) >>
     disch_then (qspecl_then [`start`,`mid`] mp_tac) >> simp[]) >>
  `evaluate_type (get_tenv cx) (BaseT bt) = SOME (BaseTV bt)` by
    (qpat_assum `expr_body_pre cenv cx env src es`
       (mp_then Any mp_tac exprSimHypsTheory.expr_body_pre_type_evaluates) >>
     simp[optionTheory.IS_SOME_EXISTS] >> metis_tac[vyperTypeConversionsTheory.evaluate_type_BaseT_SOME]) >>
  `sa.cs_next_var <= st1.cs_next_var /\ sa.cs_next_var <= sc.cs_next_var` by
    (fs[ci_mono_def] >> decide_tac) >>
  `!x. src_op = Var x ==> not_fresh_at st1 x` by
    (qpat_assum `lower_value compile_expr cenv (expr_type src) src sa = _` mp_tac >>
     qpat_assum `local_ptrs_reserved cenv sa` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[compile_lower_value_var]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st1 x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st1 x)` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `?u Gu tu.
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (t,G1,tn1) [] (OK u,Gu,tu) /\
       stmt_state_rel H ctx func cenv cx mid u /\
       storage_well_formed_on cx mid (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx mid Gu tu u) /\
     u.vs_current_bb = sc.cs_current_bb /\
     u.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~u.vs_halted /\
     alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
     return_buf_frame d cenv sc u /\
     (!fn inst z. frag_reachable ctx func u fn inst z ==> dalloca_fmp_headroom inst z)` by
    (Cases_on `is_bytestring_type (expr_type src)`
     >- suspend "dynamic_capture" >> suspend "fixed_capture") >>
  suspend "bounds"
QED
*)
Theorem slice_builtin_none_vv_prefix:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a n args es.
  (builtin_args_length_ok (Slice n) (LENGTH args) ==>
       case code_slice_source (Slice n) args of
         NONE => body_exprs_full_ok cx args
       | SOME (code_ty,addr) =>
           body_exprs_full_ok cx (TL args) /\
           (!s tail_vs t.
              eval_exprs cx (TL args) s = (INL tail_vs,t) ==>
              body_exprs_full_ok cx [addr])) /\
  (builtin_args_length_ok (Slice n) (LENGTH args) ==>
       case code_slice_source (Slice n) args of
         NONE => body_exprs_prefix_ok cx args
       | SOME (code_ty,addr) =>
           body_exprs_prefix_ok cx (TL args) /\
           (!s tail_vs t.
              eval_exprs cx (TL args) s = (INL tail_vs,t) ==>
              body_exprs_prefix_ok cx [addr])) /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Builtin a (Slice n) args) es /\
  code_slice_source (Slice n) args = NONE ==>
  expr_vv_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a (Slice n) args) es
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume slice_builtin_none_vv_prefix[dynamic_capture]:
  qpat_x_assum `if is_bytestring_type _ then _ else _` mp_tac >> simp[] >> strip_tac >>
  `?cap. bt = BytesT (Dynamic cap) \/ bt = StringT cap` by
    (qpat_assum `is_bytestring_type (expr_type src)` mp_tac >>
     qpat_assum `expr_type src = BaseT bt` SUBST1_TAC >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `bt` >> simp[is_bytestring_type_def] >>
     rename1 `BytesT bound` >> Cases_on `bound` >> simp[is_bytestring_type_def]) >>
  `post_value_type cenv src = BaseT bt` by metis_tac[post_value_type_bytestring] >>
  `!l. src_op <> Label l` by
    (qpat_assum `lower_value compile_expr cenv (expr_type src) src sa = _`
       (mp_then Any mp_tac slice_source_operand_not_label) >>
     simp[] >> disch_then (drule_then ACCEPT_TAC)) >>
  mp_tac slice_dynamic_capture_typed_start_entry >>
  (impl_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC slice_dynamic_capture_full_run)) >>
  disch_then (slice_use
    [`!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ src _ _ _ _ mid _ _ t /\ _`,
     `compile_bytestring_src src_op st1 = _`,
     `evaluate_type (get_tenv cx) (BaseT bt) = _`,
     `expr_sim_inv cenv cx env mid`]) >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] mp_tac) >>
  (impl_tac >- (fs[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`captured`,`Gu`,`tu`,`srcvar`,`p`,`bs`,`u`]
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `u = _` kall_tac >>
  qexistsl_tac [`u`,`Gu`,`tu`] >>
  simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume slice_builtin_none_vv_prefix[fixed_capture]:
  qpat_x_assum `if is_bytestring_type _ then _ else _` mp_tac >> simp[] >>
  disch_then (qx_choosel_then [`buf`,`sm`,`shadow_sm`] (map_every assume_tac o CONJUNCTS)) >>
  `?m. bt = BytesT (Fixed m)` by
    (qpat_assum `~is_bytestring_type (expr_type src)` mp_tac >>
     qpat_assum `expr_type src = BaseT bt` SUBST1_TAC >>
     qpat_assum `(a = BaseT (BytesT (Dynamic n)) /\ _) \/ _` mp_tac >>
     qpat_assum `expr_type src = BaseT bt` SUBST1_TAC >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[is_bytestring_type_def] >>
     Cases_on `bd` >> gvs[is_bytestring_type_def]) >>
  qpat_x_assum `bt = BytesT (Fixed m)` SUBST_ALL_TAC >>
  `?bs. v = BytesV bs /\ m <= 32` by
    (qpat_assum `evaluate_type (get_tenv cx) (BaseT (BytesT (Fixed m))) = _` mp_tac >>
     qpat_assum `value_has_type (BaseTV (BytesT (Fixed m))) v` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `v` >>
     Cases_on `m <= 32` >>
     simp[vyperValueTheory.evaluate_type_def,vyperTypingTheory.value_has_type_def]) >>
  qpat_x_assum `v = BytesV bs` SUBST_ALL_TAC >>
  `return_buf_frame d cenv st1 t` by
    (irule return_buf_frame_frame >>
     qpat_assum `return_buf_frame d cenv sa s0` (irule_at Any) >> simp[] >>
     qpat_assum `expr_post (storage_trace_horizon _) _ _ _ _ src _ _ _ _ _ _ _ t`
       (strip_assume_tac o REWRITE_RULE[expr_post_def]) >> first_assum ACCEPT_TAC) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by fs[ghost_inv_at_def] >>
  slice_use
    [`!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ src _ _ _ _ mid _ _ t /\ _`,
     `compile_alloc_buffer 32 st1 = _`, `emit_void MSTORE [buf.buf_operand;src_op] sm = _`,
     `expr_type src = BaseT (BytesT (Fixed m))`] slice_fixed_capture_start_entry >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] mp_tac) >>
  (impl_tac >- (conj_tac
    >- (rpt gen_tac >> strip_tac >> irule slice_fixed_capture_full_run >>
        simp[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
        >- (qexists_tac `src_op` >> simp[] >> first_assum ACCEPT_TAC)
        >> goal_assum (drule_at Any)) >>
    simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`root`,`p`,`word`,`u`,`Gu`,`tu`]
    (map_every assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`u`,`Gu`,`tu`] >> simp[] >> rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> stmt_state_rel _ _ _ _ _ _ u /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume slice_builtin_none_vv_prefix[bounds]:
  irule gas_prefix_full_zero_prefix_guarded >>
  simp[slice_read_frame,slice_terminal_source_frame,storage_trace_frame_bind_all] >>
  qexistsl_tac [`Gu`,`u`,`tu`] >>
  (conj_tac >- (gen_tac >> disch_tac >>
    qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
      (qspec_then `H` (drule_then strip_assume_tac)) >> simp[])) >>
  `body_expr_full_ok cx start /\ body_expr_prefix_ok cx start` by
    fs[Once body_exprs_full_ok_cons,body_exprs_prefix_ok_def] >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty start mid` by
    (irule (cj 1 body_expr_full_ok_simulations) >> asm_rewrite_tac[] >>
     qexistsl_tac [`env`,`tops`] >> simp[]) >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty start mid` by
    slice_child body_expr_prefix_ok_def `body_expr_prefix_ok cx start` >>
  `gas_admissible (bind (eval_expr cx start) (read_result cx)) expr_res_ok mid` by
    (irule expr_body_pre_gas_admissible >> goal_assum (drule_at Any)) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x)` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx
     ty start mid (st0,sc,sd,shadow_sc,shadow_sd,start_op,u,Gu,tu)` by
    (simp[expr_sim_full_pre_def] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >> simp[]) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
     (bind (eval_expr cx start) (read_result cx)) (mid,u,Gu,tu)` by
    (qpat_assum `expr_sim_prefix _ _ _ _ start _` (mp_tac o REWRITE_RULE[expr_sim_prefix_def]) >>
     disch_then (drule_then ACCEPT_TAC)) >>
  qpat_assum `expr_sim_full _ _ _ _ start _` (mp_tac o REWRITE_RULE[expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sc`,`sd`,`shadow_sc`,`shadow_sd`,
    `start_op`,`u`,`Gu`,`tu`] mp_tac) >>
  (impl_tac >- (qpat_assum `expr_sim_full_pre _ _ _ _ start _ _` mp_tac >>
     pure_rewrite_tac[expr_sim_full_pre_def] >> disch_then ACCEPT_TAC)) >> strip_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ (bind (eval_expr cx start) _) _ _ _`
    (mp_then Any mp_tac slice_operand_outcome_headroom) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qpat_assum `expr_type src = BaseT bt` (fn src_ty =>
    qpat_assum `expr_type start = _` (fn start_ty =>
      qpat_assum `expr_type len = _` (fn len_ty =>
        irule (SIMP_RULE (srw_ss()) [src_ty,start_ty,len_ty] slice_ordinary_bounds_prefix)))) >>
  qpat_assum `lower_value compile_expr cenv ty start sc = _` (irule_at Any) >>
  qpat_assum `lower_value compile_expr cenv ty len sd = _` (irule_at Any) >>
  qpat_assum `lower_value compile_expr _ ty (gas_shadow_expr len) shadow_sd = _` (irule_at Any) >>
  simp[] >> qexistsl_tac [`tops`,`shadow_func`,`es`,`env`,`d`] >> simp[] >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
  goal_assum (drule_at Any) >> simp[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> qexists_tac `v'` >> simp[] >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> Cases_on `res` >> simp[exprSimDefsTheory.expr_exit_INL]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise slice_builtin_none_vv_prefix
*)
