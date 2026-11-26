(* Force the reached value of a qualified internal call at the unwrap cut. *)
Theory bodySelectedReturnUnwrapMods
Ancestors
  bodyFullIntCallReturnTyping bodyIfExpWordReadMods bodyForRangeScalarFrameMods
  bodyFullPostsMods bodyFullShadowBodyInv bodyLocalCopyPhysicalRhsMods
  gasOutcomeFullPostMods gasOutcomeFullBindMods gasExemptCertMods
  exprLowering exprLoweringProps exprSimUnwrap exprSimUnwrapProps exprOperandVar
  loweringPosts bodyPtrDefs exprSimMemDefs compileEnv context
  fragGasOriginPtr fragGasOriginPtrDead bodyFullUnwrapRun freshWrites exprSimCopy
  vyperStorageTrace vyperStorageFootprint vyperState vyperInterpreter
Libs monadsyntax

Theorem selected_call_vv_shape[local]:
  compile_expr ce ty (Call ann (IntCall key) args dflt) sa = (vv,sm) ==>
  ((?tag a. vv = StackValue tag a) \/
   (?tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory))
Proof
  simp[Once compile_expr_def,Once compile_call_def] >>
  rpt (pairarg_tac >> fs[]) >>
  gvs[AllCaseEqs()] >> rpt (pairarg_tac >> fs[]) >>
  strip_tac >> gvs[base_ptr_def]
QED

Theorem selected_return_value_post[local]:
  vv_post_mods H ctx func ce cx e es sa sm s0 ee (Value v) vv s /\
  vv_location vv <> SOME LocCode ==>
  vv_post H ctx func ce cx e es sa sm s0 ee (Value v) vv s /\
  immutable_frame_mods func ce cx ee s
Proof
  Cases_on `vv` >>
  simp[vv_post_mods_def,vv_post_def,vv_location_def,vv_place_ptr_mods_def,
       vv_holds_mods_def] >>
  strip_tac >> gvs[] >> first_assum ACCEPT_TAC
QED

Theorem selected_return_identity[local]:
  ((?tag a. vv = StackValue tag a) \/
   (?tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory /\
            ~is_word_type tag /\ ~is_word_type (post_value_type ce e))) /\
  unwrap_value ce vv sm = (op,sb) /\
  vv_post_mods H ctx func ce cx e es sa sm s0 ee (Value v) vv s /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee (Value v) vv s /\
  ptr_vv_ok cx (post_value_type ce e) (Value v) vv ee G tn s /\
  (!tag a. vv = StackValue tag a /\ ~is_word_type (post_value_type ce e) ==>
     ptr_buf_ok ce e a G s) /\
  (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
     ptr_buf_ok ce e p.ptr_operand G s) ==>
  sb = sm /\ expr_post_mods H ctx func ce cx e es sa sb s0 ee v op s /\
  expr_store_bound cx (post_value_type ce e) v op s /\
  ptr_val_ok cx (post_value_type ce e) v op G tn s /\
  (~is_word_type (post_value_type ce e) ==> ptr_buf_ok ce e op G s)
Proof
  strip_tac >> `vv_location vv <> SOME LocCode` by gvs[vv_location_def] >>
  drule_all selected_return_value_post >> strip_tac >>
  gvs[unwrap_value_def,comp_return_def,ptr_vv_ok_def,ptr_val_ok_def,
      expr_post_mods_def,read_result_def,return_def] >>
  (conj_tac >- metis_tac[expr_post_of_vv_post_stack,expr_post_of_vv_post_memory]) >>
  qpat_x_assum `vv_store_bound _ _ _ _ _ _ _` mp_tac >>
  simp[expr_store_bound_def,vv_store_bound_def,read_result_def,return_def] >>
  metis_tac[]
QED

val selected_load_frame = ``
  u = s with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|> /\
  (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP (Gf : string |-> num # num) x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x)) /\
  tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
  tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm``;

val no_dead = ``<|d_stor := K (K {}); d_trans := K (K {});
                   d_imm := K {}; d_ret := K {}|>``;

Theorem selected_return_word_load[local]:
  unwrap_value ce (LocatedValue tag p) sm = (op,sb) /\
  p.ptr_location = LocMemory /\ is_word_type tag /\
  post_value_type ce e = tag /\ evaluate_type (get_tenv cx) tag = SOME rt /\
  value_has_type rt v /\
  vv_post_mods H ctx func ce cx e es sa sm s0 ee (Value v) (LocatedValue tag p) s /\
  ghost_inv_at_mods Dh lo d ce cx ee G tn s /\
  vv_store_bound cx tag (lowered_value_type ce e) ee (Value v) (LocatedValue tag p) s /\
  ptr_vv_ok cx tag (Value v) (LocatedValue tag p) ee G tn s /\
  copy_old_operand sm p.ptr_operand /\ local_ptrs_reserved ce sm /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?u Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gf,tf)) /\
    eval_operand op u = SOME (typed_val_to_w256 rt v) /\
    op_taint tf op = {} /\ op_prov Gf op = NONE /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ ^selected_load_frame
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca p.ptr_location p.ptr_operand sm = (op,sb)` by
    fs[unwrap_value_def] >>
  drule_at (Pat `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    (Q.INST [`D` |-> `^no_dead`] word_arm_located_packet) >>
  disch_then (drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_ptr_load _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`rt`,`PG`] mp_tac) >>
  (impl_tac >- simp[read_result_def,return_def,arithmeticTheory.ADD_COMM]) >>
  disch_then (qx_choosel_then [`rv`,`w`,`q`,`Gf`,`tf`] strip_assume_tac) >>
  gvs[read_result_def,return_def] >>
  `alloca_inv s` by
    (qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
     drule stateRelProjTheory.stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `!x. not_fresh_at sm x ==> lookup_var x q = lookup_var x s` by
    (gen_tac >> disch_tac >> qpat_assum `!x. not_fresh_at sm x ==> _ /\ _ /\ _` drule >> simp[]) >>
  drule_at (Pat `compile_ptr_load _ _ _ _ _ = _`) word_arm_loaded_path >>
  disch_then (drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`w`,`typed_val_to_w256 rt rv`,`q`,`explicit`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `gas_origin_ptr_path _ _ [] (OK u,Gf,tf)` >>
  qexistsl [`u`,`Gf`,`tf`] >> simp[] >>
  gen_tac >> irule gas_origin_ptr_path_from_no_dead >> simp[]
QED

Theorem selected_return_word_frame[local]:
  vv_post_mods H ctx func ce cx e es sa sm s0 ee (Value v) (LocatedValue tag p) s /\
  ghost_inv_at_mods D lo d ce cx ee G tn s /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  p.ptr_location = LocMemory /\ is_word_type (post_value_type ce e) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
  eval_operand op u = SOME (typed_val_to_w256 rt v) /\
  local_ptrs_reserved ce sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  ^selected_load_frame ==>
  expr_post_mods H ctx func ce cx e es sa sb s0 ee v op u /\
  ghost_inv_at_mods D lo d ce cx ee Gf tf u /\
  ghost_kept_at lo ce es sa G0 tn0 s0 Gf tf
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule selected_return_value_post >> simp[vv_location_def] >> strip_tac >>
  `!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s` by
    (rpt strip_tac >> qpat_assum `!x. not_fresh_at sm x ==> _ /\ _ /\ _` drule >> simp[]) >>
  `stmt_state_rel H ctx func ce cx ee u` by
    (irule bodyPtrSignedConvertSourceFrameTheory.stmt_state_rel_readonly_vars_pc >>
     qexistsl [`s`,`sm`] >> fs[vv_post_def]) >>
  conj_tac
  >- (simp[expr_post_mods_def] >> conj_tac
      >- (irule expr_post_of_vv_post_load_physical >> simp[] >>
          goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
          conj_tac
          >- (rpt strip_tac >> qpat_assum `!x. not_fresh_at sm x ==> lookup_var x u = _`
                drule >> simp[]) >>
          rpt conj_tac >> simp[] >>
          qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
            (fn th => simp[Once th])) >>
      irule immutable_frame_mods_exterior_frame >> qexistsl [`ee`,`s`,`sm`] >>
      simp[] >> rpt conj_tac >> qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
        (fn th => simp[Once th])) >>
  conj_tac
  >- (irule ghost_inv_at_mods_exterior_frame >> qexistsl [`G`,`ee`,`s`,`sm`,`tn`] >> simp[] >>
      rpt conj_tac >> qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
        (fn th => simp[Once th])) >>
  irule ghost_kept_at_clean_suffix >> qexistsl [`G`,`tn`] >> simp[] >>
  rpt strip_tac >> `not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >> simp[]
QED

val owned_post = ``
  \(H : (bool # 256 word # type_value) list # num list) (res : eval_result + exception) ee G1 tn1 s. ?tv. res = INL tv /\
    vv_post_mods H ctx func ce cx e es0 sa sm s0 ee tv vv s /\
    vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv s /\
    s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G1 tn1 s /\
    ptr_vv_ok cx (post_value_type ce e) tv vv ee G1 tn1 s /\
    (!v. tv = Value v /\ ~is_word_type (post_value_type ce e) /\
         ~is_bytestring_type (post_value_type ce e) ==>
      vv_own ce cx (post_value_type ce e) sa sm ee tv vv s /\
      (!tag p. vv = LocatedValue tag p ==> p.ptr_location = LocMemory)) /\
    (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
      ?v. read_result cx tv ee = (INL v,ee) /\
        !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
               eval_operand (vv_operand vv) s = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn1.t_mem s.vs_memory mem ==>
                 val_in_memory rt v (w2n w) mem)) /\
    (!tag a. vv = StackValue tag a /\ ~is_word_type (post_value_type ce e) ==>
      ptr_buf_ok ce e a G1 s) /\
    (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok ce e p.ptr_operand G1 s) /\
    ghost_kept_at lo ce es0 sa G0 tn0 s0 G1 tn1``;

val read_post = ``
  \(H : (bool # 256 word # type_value) list # num list) (res : value + exception) ee G1 tn1 s.
    ?v. res = INL v /\
    expr_post_mods H ctx func ce cx e es0 sa sb s0 ee v op s /\
    expr_store_bound cx (post_value_type ce e) v op s /\
    s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G1 tn1 s /\
    ptr_val_ok cx (post_value_type ce e) v op G1 tn1 s /\
    (~is_word_type (post_value_type ce e) ==> ptr_buf_ok ce e op G1 s) /\
    ghost_kept_at lo ce es0 sa G0 tn0 s0 G1 tn1``;

val exit_post = ``\(H : (bool # 256 word # type_value) list # num list) res ee
  (gt : (string |-> num # num) # taint) r. expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)``;

Theorem selected_return_read_suffix[local]:
  ((?tag a. vv = StackValue tag a) \/
   (?tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory)) /\
  unwrap_value ce vv sm = (op,sb) /\ fn_has_code sm sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sm /\
  sa.cs_next_var <= sm.cs_next_var /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (is_word_type (post_value_type ce e) ==>
    ?rt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\ value_has_type rt v) /\
  ~s.vs_halted /\ ee.gas_obs = [] /\ storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    (^owned_post) H (INL (Value v)) ee G tn s) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (read_result cx (Value v)) (ee,s,G,tn) (^read_post) (^(Term.inst [alpha |-> ``:value``] exit_post))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [] o BETA_RULE)) >>
  Cases_on `(?tag a. vv = StackValue tag a) \/
   (?tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory /\
            ~is_word_type tag /\ ~is_word_type (post_value_type ce e))`
  >- suspend "identity" >>
  suspend "load"
QED

Resume selected_return_read_suffix[identity]:
  `sb = sm` by
    (qpat_assum `unwrap_value _ _ _ = _` mp_tac >>
     qpat_assum `(?tag a. vv = StackValue tag a) \/ _` strip_assume_tac >>
     gvs[unwrap_value_def,comp_return_def]) >>
  irule gas_outcome_full_mods_pure >> simp[read_result_def,return_def] >>
  qexistsl [`G`,`ee`,`INL v`,`s`,`tn`] >>
  `ee with gas_obs := [] = ee` by simp[vyperStateTheory.evaluation_state_component_equality] >>
  simp[cj 1 gas_origin_ptr_path_rules] >> gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [] o BETA_RULE)) >>
  drule_at (Pat `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`) selected_return_identity >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Resume selected_return_read_suffix[load]:
  `?tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory /\
    (~is_word_type tag ==> is_word_type (post_value_type ce e))` by metis_tac[] >>
  qpat_x_assum `vv = LocatedValue _ _` SUBST_ALL_TAC >>
  rename1 `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ (Value v) (LocatedValue tag p) s` >>
  `tag = post_value_type ce e \/
   is_bytestring_type tag /\ is_bytestring_type (post_value_type ce e)` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
     fs[vv_post_mods_def,vv_holds_mods_def,vv_holds_def] >> metis_tac[]) >>
  `tag = post_value_type ce e /\ is_word_type tag` by
    metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
  `copy_old_operand sm p.ptr_operand` by fs[copy_old_operand_def,vv_operand_def] >>
  qpat_x_assum `tag = post_value_type ce e` SUBST_ALL_TAC >>
  `?rt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\ value_has_type rt v` by
    metis_tac[] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  drule_at (Pat `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`) selected_return_word_load >>
  disch_then (drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (qspecl_then [`rt`,`explicit`,`PG`] mp_tac) >> (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`u`,`Gf`,`tf`] strip_assume_tac) >>
  irule gas_outcome_full_mods_pure >> simp[read_result_def,return_def] >>
  qexistsl [`Gf`,`ee`,`INL v`,`u`,`tf`] >>
  `ee with gas_obs := [] = ee` by simp[vyperStateTheory.evaluation_state_component_equality] >>
  simp[expr_store_bound_word,ptr_val_ok_word] >> qx_gen_tac `h` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `h` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) [] o BETA_RULE) >>
  `expr_post_mods h ctx func ce cx e es0 sa sb s0 ee v op u /\
   ghost_inv_at_mods (DF h) lo d ce cx ee Gf tf u /\
   ghost_kept_at lo ce es0 sa G0 tn0 s0 Gf tf` by
    (qpat_assum `vv_post_mods h _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_then (Pat `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`) mp_tac
         (Q.INST [`sb` |-> `sb`] selected_return_word_frame)) >>
     disch_then (drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)) >>
     disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
     disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
     disch_then (qspecl_then [`tf`,`sb`,`Gf`] mp_tac) >> simp[]) >>
  `allocas_below_fmp u = allocas_below_fmp s` by
    (qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
     simp[ptrDisciplineTheory.allocas_below_fmp_def]) >>
  simp[] >>
  qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>` (fn th => simp[Once th])
QED

Finalise selected_return_read_suffix[local]

val selected_rest = ``
  do lock_if_nr cx nr (is_view_mut mut);
     rv <- finally_unless_halt
       (finally
         (try (do eval_stmts (cx with stk updated_by CONS (src,name)) ss;
                  return NoneV od) handle_function)
         (pop_function prev))
       (unlock_if_nr cx nr (is_view_mut mut));
     crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
     return (Value crv)
  od``;

Theorem selected_return_source_frame[local]:
  storage_trace_frame (^selected_rest)
Proof
  irule storage_trace_frame_ignore_bind >>
  simp_tac pure_ss [storage_trace_frame_optional_locks, AND_CLAUSES] >>
  irule storage_trace_frame_bind_all >> reverse conj_tac
  >- (irule storage_trace_frame_finally_unless_halt >>
      simp_tac pure_ss [storage_trace_frame_optional_locks, AND_CLAUSES] >>
      irule storage_trace_frame_finally >> simp[storage_trace_frame_function_stack] >>
      irule storage_trace_frame_try >> simp[storage_trace_frame_function_handler] >>
      irule storage_trace_frame_ignore_bind >>
      simp[evaluate_storage_trace_frame,storage_trace_frame_return]) >>
  gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
  simp[storage_trace_frame_lifts,storage_trace_frame_return]
QED

Theorem selected_return_source_type[local]:
  (^selected_rest) start = (INL tv,ee) ==>
  ?v. tv = Value v /\ value_has_type rtv v
Proof
  pure_rewrite_tac[ignore_bind_def] >>
  simp_tac pure_ss [bind_def, AllCaseEqs(), lift_option_type_def, return_def,
                    pairTheory.pair_case_thm, sumTheory.sum_case_def] >>
  strip_tac >> Cases_on `safe_cast rtv rv` >> gvs[raise_def,return_def] >>
  metis_tac[vyperTypingTheory.safe_cast_result_well_typed]
QED

Theorem selected_return_post_type[local]:
  ce.ce_func_return_type (nsid_to_string (src,name)) = ret /\
  type_widens_to (get_tenv cx) ret ann /\ evaluate_type (get_tenv cx) ret = SOME rtv /\
  value_has_type rtv v ==>
  ?rt. evaluate_type (get_tenv cx)
    (post_value_type ce (Call ann (IntCall (src,name)) es dflt)) = SOME rt /\ value_has_type rt v
Proof
  strip_tac >> Cases_on `is_word_type ann \/ is_bytestring_type ann`
  >- (simp[post_value_type_def] >> irule vyperTypeArgFitsTheory.type_widens_to_value_has_type >>
      qexistsl [`ret`,`rtv`] >> simp[]) >>
  gvs[post_value_type_def,lowered_value_type_def]
QED

val call_expr = ``Call ann (IntCall (src,name)) es dflt``;
val call_owned = subst [``e:expr`` |-> call_expr] owned_post;
val call_read = subst [``e:expr`` |-> call_expr] read_post;
val owned_exit = Term.inst [alpha |-> ``:eval_result``] exit_post;
val read_exit = Term.inst [alpha |-> ``:value``] exit_post;

(* The raw result is already on the counted execution.  Bind its source
   answer to the forcing continuation at the same machine endpoint. *)
Theorem selected_return_unwrap_mods:
  contract_inv mods exps ctx ce cx /\ ALOOKUP mods src = SOME tops /\
  expr_body_pre_mods mods ce cx env (^call_expr) es0 /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
  evaluate_type (get_tenv cx) ret = SOME rtv /\
  compile_expr ce ty (^call_expr) sa = (vv,sm) /\
  compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr (^call_expr)) shadow_sa = (vv,shadow_sm) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sm shadow_sm /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func ==>
   gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) mods cx st0
     (^selected_rest) (es1,t,G,tn) (^call_owned) (^owned_exit)) ==>
  !op sb shadow_sb.
    unwrap_value ce vv sm = (op,sb) /\ unwrap_value ce vv shadow_sm = (op,shadow_sb) /\
    gas_shadow_state sb shadow_sb /\ fn_has_code sa sb func /\
    fn_has_code shadow_sa shadow_sb shadow_func /\
    gas_admissible (bind (^selected_rest) (read_result cx)) expr_res_ok es1 ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) mods cx st0
      (bind (^selected_rest) (read_result cx)) (es1,t,G,tn) (^call_read) (^read_exit)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `compile_expr ce ty (Call _ _ _ _) sa = _`
    (strip_assume_tac o MATCH_MP compile_expr_extends) >>
  qpat_assum `unwrap_value ce vv sm = _`
    (strip_assume_tac o MATCH_MP unwrap_value_extends) >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
    (strip_assume_tac o MATCH_MP compile_expr_extends) >>
  qpat_assum `unwrap_value _ _ shadow_sm = _`
    (strip_assume_tac o MATCH_MP unwrap_value_extends) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (qspecl_then [`sa`,`sm`,`sb`,`func`] mp_tac fragExecTheory.fn_has_code_split >> simp[]) >>
  `fn_has_code shadow_sa shadow_sm shadow_func` by
    (qspecl_then [`shadow_sa`,`shadow_sm`,`shadow_sb`,`shadow_func`] mp_tac
       fragExecTheory.fn_has_code_split >> simp[]) >>
  qpat_x_assum `fn_has_code sa sm func /\ _ ==> _` mp_tac >>
  (impl_tac >- simp[]) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` >>
  irule gas_outcome_full_mods_bind_all >> rpt conj_tac
  >~ [`storage_trace_frame (ignore_bind _ _)`]
  >- irule selected_return_source_frame
  >~ [`!v. storage_trace_frame (read_result cx v)`]
  >- simp[storage_trace_frame_read_result]
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> drule gas_exempt_cert_mods_bind_result >> simp[] >>
      disch_then irule >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_result >> first_assum ACCEPT_TAC) >>
  qexists `\H res ee G tn t. childQ H res ee G tn t /\ ee.gas_obs = [] /\ ~t.vs_halted` >>
  reverse conj_tac
  >- suspend "prefix" >>
  suspend "read"
QED

Resume selected_return_unwrap_mods[prefix]:
  irule gas_outcome_full_mods_post_source >> first_assum (irule_at Any) >>
  simp[Abbr `childR`] >> rpt strip_tac >> Cases_on `res`
  >- (Cases_on `r` >> fs[exprSimDefsTheory.expr_exit_def]) >>
  Cases_on `r` >> Cases_on `y` >>
  gvs[exprSimDefsTheory.expr_exit_def,exprSimDefsTheory.halt_exit_def] >>
  rename1 `expr_exit (INR (Error err)) _` >>
  Cases_on `err` >> fs[exprSimDefsTheory.expr_exit_def]
QED

Resume selected_return_unwrap_mods[read]:
  qx_genl_tac [`marks`,`res`,`ee`,`G1`,`tn1`,`s`] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qunabbrev_tac `childQ` >> disch_then (strip_assume_tac o BETA_RULE) >> gvs[] >>
  qpat_assum `!tail. ignore_bind _ _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [listTheory.APPEND_NIL])) >>
  `ee with gas_obs := [] = ee` by simp[vyperStateTheory.evaluation_state_component_equality] >>
  drule (SIMP_RULE (srw_ss()) [] selected_return_source_type) >> strip_tac >>
  gvs[] >>
  drule_all intcall_declared_return_type_mods >> strip_tac >>
  drule_all (SIMP_RULE (srw_ss()) [] selected_return_post_type) >> strip_tac >>
  drule selected_call_vv_shape >> disch_tac >>
  irule (SIMP_RULE (srw_ss()) [] (Q.INST [`e` |-> `Call ann (IntCall (src,name)) es dflt`]
    selected_return_read_suffix)) >> simp[] >>
  qexistsl [`sm`,`vv`] >> simp[] >>
  rpt conj_tac
  >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[])
  >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[])
  >- (qpat_assum `compile_expr ce ty (Call _ _ _ _) sa = _`
        (mp_then Any mp_tac (cj 1 compiler_compile_var)) >> simp[])
  >> irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]
QED

Finalise selected_return_unwrap_mods
