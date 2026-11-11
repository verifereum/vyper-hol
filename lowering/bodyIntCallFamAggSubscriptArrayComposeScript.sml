(* Prepare the exact counted suffix from resource-preserving child endpoints. *)
Theory bodyIntCallFamAggSubscriptArrayCompose
Ancestors
  bodyIntCallFamAggSubscriptArrayPrepare bodyIntCallFamAggSubscriptArrayIndex
  bodyIntCallFamAggSubscriptArraySuffix exprSimSubscriptArraySuffix
  exprSimSubscriptArrayEndpoint exprSimSubscriptArraySource exprSimSource
  bodyIntCallJointContract exprLoweringProps exprSimHypsDefs loweringPosts

Theorem intcall_framed_array_child_suffix:
  ((?ty. vv_location (FST (compile_expr ce ty obj sa)) = SOME LocCode) \/
   (?n. bd = Fixed n)) /\
  expr_body_pre ce fp.jc_cx env (Subscript et obj idx) es /\
  expr_type obj = ArrayT et bd /\ post_value_type ce obj = expr_type obj /\
  eval_expr fp.jc_cx obj es = (INL r,t) /\
  eval_expr fp.jc_cx idx t = (INL ir,ee) /\
  read_result fp.jc_cx ir ee = (INL iv,ee) /\
  ee.scopes = t.scopes /\ ee.immutables = t.immutables /\ ee.gas_obs = [] /\
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx obj es sa sb s0 t r
    (LocatedValue (ArrayT et bd) p) u /\
  expr_post fp.jc_ctx fp.jc_func ce fp.jc_cx idx t sb sc u ee iv iop s /\
  ((~ce.ce_is_ctor /\ p.ptr_location = LocCode) \/
   ((?n. bd = Fixed n) /\
    (!tv. evaluate_type (get_tenv fp.jc_cx) et = SOME tv ==> dynarray_free tv) /\
    p.ptr_location = LocMemory)) /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sb x) /\
  (!l. p.ptr_operand <> Label l) /\
  (!x. iop = Var x ==> not_fresh_at sc x) /\ (!l. iop <> Label l) /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sb /\ local_ptrs_reserved ce sc /\
  MAP FDOM es.scopes = MAP FDOM t.scopes /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  sb.cs_next_var <= sc.cs_next_var /\ sb.cs_next_id <= sc.cs_next_id /\
  compile_array_subscript p.ptr_operand iop
    (case bd of Fixed _ => F | Dynamic _ => T)
    (case bd of Fixed n => n | Dynamic _ => 0)
    (word_scale p.ptr_location) (elem_size_in_location ce p.ptr_location et)
    (is_signed_type (expr_type idx))
    (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca p.ptr_location) sc = (dst,sd) /\
  fn_has_code sc sd fp.jc_func /\
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s0 /\
  intcall_expr_cont fp ce env es sa s0 t sb u /\
  intcall_expr_cont fp ce env t sb u ee sc s /\
  (p.ptr_location = LocMemory ==>
    !tv. evaluate_type (get_tenv fp.jc_cx) (ArrayT et bd) = SOME tv ==>
      ?w a k. eval_operand p.ptr_operand u = SOME w /\
        a <= w2n w /\ w2n w + type_memory_size tv <= a + k /\
        a + k < dimword (:256) /\
        (fp.jc_lo <= a \/
         ?b z. fp.jc_staged b z /\ b <= a /\ a + k <= b + z)) ==>
  gas_summary_at F (fp.jc_ctx,fp.jc_func) []
    (select_result fp.jc_cx (ArrayT et bd) r (ValueSubscript iv)) (ee,s)
    (\res ee' q. ?tv. res = INL tv /\
      vv_holds ce fp.jc_cx (post_value_type ce (Subscript et obj idx)) tv
        (LocatedValue et (mk_ptr dst p.ptr_location)) ee' q /\
      vv_at ce fp.jc_cx (post_value_type ce (Subscript et obj idx)) sa sd ee' tv
        (LocatedValue et (mk_ptr dst p.ptr_location)) q /\
      (post_value_type ce (Subscript et obj idx) <> expr_type (Subscript et obj idx) ==>
        vv_own ce fp.jc_cx (post_value_type ce (Subscript et obj idx)) sa sd ee' tv
          (LocatedValue et (mk_ptr dst p.ptr_location)) q) /\
      (~expr_has_effect (Subscript et obj idx) ==>
        vv_storage_live fp.jc_cx (LocatedValue et (mk_ptr dst p.ptr_location)) ee' q) /\
      (!x. vv_operand (LocatedValue et (mk_ptr dst p.ptr_location)) = Var x ==>
        not_fresh_at sd x) /\
      (post_value_type ce (Subscript et obj idx) <> NoneT /\
       ~is_word_type (post_value_type ce (Subscript et obj idx)) /\
       ~is_bytestring_type (post_value_type ce (Subscript et obj idx)) /\
       (case LocatedValue et (mk_ptr dst p.ptr_location) of StackValue _ _ => T
         | LocatedValue _ p => p.ptr_location = LocMemory) ==>
       !tv'. evaluate_type (get_tenv fp.jc_cx)
         (post_value_type ce (Subscript et obj idx)) = SOME tv' ==>
         ?w a k. eval_operand (vv_operand (LocatedValue et (mk_ptr dst p.ptr_location))) q = SOME w /\
           a <= w2n w /\ w2n w + type_memory_size tv' <= a + k /\
           a + k < dimword (:256) /\
           (fp.jc_lo <= a \/
            ?b z. fp.jc_staged b z /\ b <= a /\ a + k <= b + z)) /\
      intcall_expr_cont fp ce env es sa s0 ee' sd q)
    (\res ee' outcome. expr_exit res outcome)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then assume_tac expr_body_pre_array_subscript_base >>
  drule_all_then assume_tac expr_body_pre_array_subscript_index_after_base >>
  drule_all_then strip_assume_tac expr_body_pre_runtime_typed >>
  `value_has_type tvt iv` by metis_tac[] >>
  drule_all framed_array_index_post_view >> strip_tac >>
  `is_word_type (expr_type idx)` by
    (qpat_x_assum `value_has_type tvt iv` mp_tac >>
     qpat_x_assum `evaluate_type _ (expr_type idx) = _` mp_tac >>
     qpat_x_assum `iv = IntV i` SUBST1_TAC >> rpt (pop_assum kall_tac) >>
     Cases_on `expr_type idx` >>
     simp[vyperValueTheory.evaluate_type_def, AllCaseEqs(),
          vyperTypingTheory.value_has_type_def, compileEnvTheory.is_word_type_def] >>
     rpt strip_tac >> gvs[vyperTypingTheory.value_has_type_def,
                          compileEnvTheory.is_word_type_def]) >>
  drule_all intcall_framed_array_index_endpoint >> strip_tac >>
  drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`) framed_array_post_view >>
  disch_then (qspecl_then [`t`,`env`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  `expr_sim_inv ce fp.jc_cx env t /\
   stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s0 /\
   stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx ee s /\
   ~s.vs_halted /\ s.vs_current_bb = sc.cs_current_bb /\
   s.vs_inst_idx = LENGTH sc.cs_current_insts` by
    fs[intcall_expr_cont_def, intcall_expr_res_def] >>
  `cs_extends sc sd /\ sc.cs_next_var <= sd.cs_next_var /\
   sc.cs_next_id <= sd.cs_next_id` by
    (irule array_subscript_grows >>
     goal_assum (drule_at Any) >> simp[ci_mono_compile_ptr_load]) >>
  `!q. (!x z. not_fresh_at sc x /\ lookup_var x s = SOME z ==> lookup_var x q = SOME z) /\
       (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
       q.vs_memory = s.vs_memory /\ stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx ee q ==>
       vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx obj es sa sd s0 ee r
         (LocatedValue (ArrayT et bd) p) q` by
    (rpt strip_tac >>
     qpat_x_assum `vv_post _ _ _ _ _ _ sa sc _ _ _ _ _` kall_tac >>
     irule framed_array_base_endpoint >> simp[] >>
     goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     simp[] >> qexists_tac `env` >> simp[]) >>
  `p.ptr_location = LocMemory ==>
     ?n a k. bd = Fixed n /\ a <= w2n w /\
       w2n w + type_memory_size (ArrayTV etv bd) <= a + k /\
       a + k < dimword (:256) /\
       (fp.jc_lo <= a \/ ?b z. fp.jc_staged b z /\ b <= a /\ a + k <= b + z)` by
    (strip_tac >>
     qpat_x_assum `p.ptr_location = LocMemory ==> _` drule >>
     disch_then (qspec_then `ArrayTV etv bd` mp_tac) >> simp[] >>
     strip_tac >> rename1 `eval_operand p.ptr_operand u = SOME bw` >>
     `bw = w` by metis_tac[optionTheory.SOME_11] >>
     gvs[] >> metis_tac[]) >>
  qpat_x_assum `iv = IntV i` SUBST1_TAC >>
  irule intcall_framed_array_suffix_summary >>
  simp[SF SFY_ss] >>
  (conj_tac >- metis_tac[arithmeticTheory.ADD_COMM]) >>
  qexistsl_tac [`iop`,`iw`,`sc`] >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!x. p.ptr_operand = Var x ==> _` drule >>
  simp[compileEnvTheory.not_fresh_at_def]
QED
