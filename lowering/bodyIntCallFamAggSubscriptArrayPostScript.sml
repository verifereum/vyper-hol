(* Complete selected-value posts: representation and window authorization. *)
Theory bodyIntCallFamAggSubscriptArrayPost
Ancestors
  bodyIntCallJointContract bodyIntCallFamAggSubscriptArrayWindow
  exprSimSubscriptArraySuffix loweringPosts context compileEnv vyperAST
  vyperArray vyperTyping vyperValueOperation valueEncoding integer words
  exprSimSubscriptArrayFramed exprSimDefs gasSummary

Theorem intcall_array_selected_post:
  vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx (Subscript et obj idx)
    es sa sd s0 ee child (LocatedValue et (mk_ptr dst loc)) q /\
  intcall_expr_cont fp ce env es sa s0 ee sd q /\
  (!x. dst = Var x ==> not_fresh_at sd x) /\
  (loc = LocMemory \/ loc = LocCode) /\
  evaluate_type (get_tenv fp.jc_cx) et = SOME etv /\
  value_has_type (ArrayTV etv bd) (ArrayV av) /\
  valid_index (ArrayTV etv bd) av i /\
  eval_operand dst q = SOME
    (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) +
               Num i * type_memory_size etv)) /\
  (loc = LocMemory ==>
    ?n a k. bd = Fixed n /\ a <= w2n w /\
      w2n w + type_memory_size (ArrayTV etv bd) <= a + k /\
      a + k < dimword (:256) /\
      (fp.jc_lo <= a \/
       ?b z. fp.jc_staged b z /\ b <= a /\ a + k <= b + z)) ==>
  ?tv. INL child = INL tv /\
    vv_holds ce fp.jc_cx (post_value_type ce (Subscript et obj idx)) tv
      (LocatedValue et (mk_ptr dst loc)) ee q /\
    vv_at ce fp.jc_cx (post_value_type ce (Subscript et obj idx)) sa sd ee tv
      (LocatedValue et (mk_ptr dst loc)) q /\
    (post_value_type ce (Subscript et obj idx) <> expr_type (Subscript et obj idx) ==>
      vv_own ce fp.jc_cx (post_value_type ce (Subscript et obj idx)) sa sd ee tv
        (LocatedValue et (mk_ptr dst loc)) q) /\
    (~expr_has_effect (Subscript et obj idx) ==>
      vv_storage_live fp.jc_cx (LocatedValue et (mk_ptr dst loc)) ee q) /\
    (!x. vv_operand (LocatedValue et (mk_ptr dst loc)) = Var x ==> not_fresh_at sd x) /\
    (post_value_type ce (Subscript et obj idx) <> NoneT /\
     ~is_word_type (post_value_type ce (Subscript et obj idx)) /\
     ~is_bytestring_type (post_value_type ce (Subscript et obj idx)) /\
     (case LocatedValue et (mk_ptr dst loc) of StackValue _ _ => T
       | LocatedValue _ p => p.ptr_location = LocMemory) ==>
     !tv'. evaluate_type (get_tenv fp.jc_cx)
       (post_value_type ce (Subscript et obj idx)) = SOME tv' ==>
       ?w a k. eval_operand (vv_operand (LocatedValue et (mk_ptr dst loc))) q = SOME w /\
         a <= w2n w /\ w2n w + type_memory_size tv' <= a + k /\
         a + k < dimword (:256) /\
         (fp.jc_lo <= a \/
          ?b z. fp.jc_staged b z /\ b <= a /\ a + k <= b + z)) /\
    intcall_expr_cont fp ce env es sa s0 ee sd q
Proof
  strip_tac >>
  fs[vv_post_def, expr_type_def, vv_operand_def, mk_ptr_def] >>
  rpt strip_tac >> gvs[] >>
  `array_length (ArrayTV etv (Fixed n)) av = n` by
    (Cases_on `av` >> gvs[value_has_type_def, array_length_def]) >>
  `Num i < n` by
    (qspecl_then [`&n`,`i`] mp_tac (GEN_ALL integerTheory.NUM_LT) >> gvs[]) >>
  fs[type_memory_size_def] >>
  drule_all intcall_array_element_window >> strip_tac >>
  qexistsl_tac [`a`,`k`] >> simp[] >> metis_tac[]
QED

(* The representation is supplied at the very same endpoint as the counted
   resource-preserving run; no determinism or witness alignment is assumed. *)
Theorem intcall_array_element_summary:
  expr_body_pre ce fp.jc_cx env obj es /\
  eval_expr fp.jc_cx obj es = (INL r,t) /\
  expr_type obj = ArrayT et bd /\ post_value_type ce obj = expr_type obj /\
  evaluate_type (get_tenv fp.jc_cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  evaluate_type (get_tenv fp.jc_cx) et = SOME etv /\
  ee.scopes = t.scopes /\ ee.immutables = t.immutables /\ ee.gas_obs = [] /\
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  (vv_location (FST (compile_expr ce ty obj sa)) = SOME LocCode \/
   (?n. bd = Fixed n)) /\
  read_result fp.jc_cx r ee = (INL (ArrayV av),ee) /\
  array_index (ArrayTV etv bd) av i = SOME v /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\ val_wf etv v /\ value_has_type etv v /\
  vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx obj es sa sd s0 ee r
    (LocatedValue ann p) q /\
  (p.ptr_location = LocMemory \/ p.ptr_location = LocCode) /\
  (p.ptr_location = LocMemory ==> ?n. bd = Fixed n) /\
  eval_operand p.ptr_operand q = SOME w /\
  eval_operand dst q = SOME
    (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) +
               Num i * type_memory_size etv)) /\
  (p.ptr_location = LocMemory ==>
    w2n (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) +
                   Num i * type_memory_size etv)) =
      w2n w + ((case bd of Fixed _ => 0 | Dynamic _ => 32) +
                Num i * type_memory_size etv)) /\
  (!x. dst = Var x ==> not_fresh_at sd x) /\
  value_has_type (ArrayTV etv bd) (ArrayV av) /\
  valid_index (ArrayTV etv bd) av i /\
  (p.ptr_location = LocMemory ==>
    ?n a k. bd = Fixed n /\ a <= w2n w /\
      w2n w + type_memory_size (ArrayTV etv bd) <= a + k /\
      a + k < dimword (:256) /\
      (fp.jc_lo <= a \/
       ?b z. fp.jc_staged b z /\ b <= a /\ a + k <= b + z)) /\
  intcall_expr_cont fp ce env es sa s0 ee sd q /\
  gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK q) ==>
  gas_summary_at F (fp.jc_ctx,fp.jc_func) []
    (select_result fp.jc_cx (ArrayT et bd) r (ValueSubscript (IntV i))) (ee,s)
    (\res ee' u. ?child. res = INL child /\
      vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx (Subscript et obj idx)
        es sa sd s0 ee' child (LocatedValue et (mk_ptr dst p.ptr_location)) u /\
      (!x. dst = Var x ==> not_fresh_at sd x) /\
      eval_operand dst u = SOME
        (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) +
                   Num i * type_memory_size etv)) /\
      intcall_expr_cont fp ce env es sa s0 ee' sd u)
    (\res ee' outcome. expr_exit res outcome)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all framed_array_select_read >> strip_tac >>
  `vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx (Subscript et obj idx)
     es sa sd s0 ee child (LocatedValue et (mk_ptr dst p.ptr_location)) q` by
    (irule vv_post_array_element >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  irule select_result_counted_summary >> simp[] >>
  qexists_tac `OK q` >> simp[] >>
  `ee with gas_obs := [] = ee` by
    (Cases_on `ee` >> gvs[vyperStateTheory.evaluation_state_component_equality]) >>
  simp[] >> goal_assum (drule_at Any) >> simp[]
QED
