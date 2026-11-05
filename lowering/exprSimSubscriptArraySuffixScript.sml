(* Source selection and counted suffix summaries for framed arrays. *)
Theory exprSimSubscriptArraySuffix
Ancestors
  exprSimSubscriptArrayEndpoint exprSimSubscriptArrayFramed
  exprSimSubscriptArraySource gasSummary exprSimDefs vyperState
  vyperPlaceTyping vyperValueOperation vyperArray integer_word words integer
  exprSimSource exprSimCopy exprSimLen valueEncodingProps valueEncoding

Theorem framed_array_select_error:
  expr_body_pre cenv cx env obj es /\
  eval_expr cx obj es = (INL r,t) /\
  expr_type obj = ArrayT et bd /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  t'.scopes = t.scopes /\ t'.immutables = t.immutables /\
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  read_result cx r t' = (INL (ArrayV av),t') /\
  (!al. av = SArrayV al ==> ?n. bd = Fixed n) /\
  ~valid_index (ArrayTV etv bd) av i ==>
  select_result cx (ArrayT et bd) r (ValueSubscript (IntV i)) t' =
    (INR (Error (RuntimeError "evaluate_subscripts array_index")),t')
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then assume_tac evaluate_array_subscript_oob >>
  Cases_on `r`
  >~ [`read_result cx (HashMapRef tr slot tv key) _ = _`] >-
    gvs[read_result_def, raise_def]
  >~ [`Value value`] >-
    (gvs[read_result_def, return_def] >>
     drule_all select_value_result >> simp[bind_def, lift_sum_def, raise_def]) >>
  drule_all expr_body_pre_place_metadata >> strip_tac >> gnvs[] >>
  `runtime_place_typed cx t' p (ArrayTV etv bd)` by
    (Cases_on `p`
     >~ [`StoragePlace tr slot vt`] >- metis_tac[]
     >~ [`MemoryPlace id path`] >-
       gvs[runtime_place_typed_memory] >>
     qpat_x_assum `runtime_place_typed _ _ _ _` mp_tac >>
     Cases_on `ALOOKUP t.immutables cx.txn.target` >>
     simp[runtime_place_typed_immutable, get_immutables_def,
          get_address_immutables_def, bind_def, ignore_bind_def, return_def, raise_def]) >>
  drule_all select_nonstorage_place_error >> simp[]
QED

Theorem select_result_nonstorage_gas_obs:
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) ==>
  select_result cx ty r sb (s with gas_obs := gs) =
    (FST (select_result cx ty r sb s), s with gas_obs := gs)
Proof
  strip_tac >> Cases_on `r`
  >~ [`Value v`] >-
    (simp[select_result_def, lift_option_type_def, lift_sum_def,
          bind_def, ignore_bind_def, return_def, raise_def] >>
     rpt (CASE_TAC >> simp[return_def, raise_def]))
  >~ [`HashMapRef tr slot kt vt`] >-
    (Cases_on `sb` >>
     simp[select_result_def, extend_place_def, lift_option_type_def,
          bind_def, ignore_bind_def, return_def, raise_def] >>
     rpt (CASE_TAC >> simp[bind_def, ignore_bind_def, return_def, raise_def])) >>
  Cases_on `p`
  >~ [`StoragePlace tr slot vt`] >- metis_tac[]
  >~ [`MemoryPlace id path`] >-
    (simp[select_result_def, extend_place_def, place_type_value_def,
          read_place_def, get_scopes_def, lift_option_type_def,
          lift_sum_def, bind_def, ignore_bind_def, return_def, raise_def] >>
     rpt (CASE_TAC >> simp[bind_def, ignore_bind_def, return_def, raise_def])) >>
  simp[select_result_def, extend_place_def, place_type_value_def,
       read_place_def, get_immutables_def, get_address_immutables_def,
       lift_option_type_def, lift_sum_def, bind_def, ignore_bind_def, return_def, raise_def] >>
  rpt (CASE_TAC >> simp[bind_def, ignore_bind_def, return_def, raise_def])
QED

Theorem select_result_counted_summary:
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  select_result cx ty r sb es = (res,es) /\
  gas_marked_path F ctx func s 0 outcome /\
  ((?t. outcome = OK t /\ Q res (es with gas_obs := []) t) \/
   (exit_result outcome /\ expr_exit res outcome)) ==>
  gas_summary_at F (ctx,func) [] (select_result cx ty r sb) (es,s)
    Q (\res ee outcome. expr_exit res outcome)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`res`,`es`,`outcome`] >> simp[] >>
  simp[gas_marked_exec_def] >>
  drule select_result_nonstorage_gas_obs >> simp[]
QED

Theorem idx_in_range_integer:
  n < dimword (:256) ==>
  (idx_in_range sgn w (n2w n) <=>
   0 <= (if sgn then w2i w else &(w2n w)) /\
   (if sgn then w2i w else &(w2n w)) < &n)
Proof
  strip_tac >> Cases_on `sgn` >>
  simp[exprSimArrayIndexTheory.idx_in_range_def, WORD_LTi, word_0_w2i, w2n_n2w] >>
  Cases_on `word_msb w` >>
  simp[w2i_def] >>
  Cases_on `w = 0w` >> gvs[]
QED

Theorem array_index_word_bounds:
  array_length (ArrayTV et bd) av < dimword (:256) /\
  i = (if sgn then w2i w else &(w2n w)) ==>
  (valid_index (ArrayTV et bd) av i <=>
   idx_in_range sgn w (n2w (array_length (ArrayTV et bd) av)))
Proof
  strip_tac >> drule idx_in_range_integer >> simp[]
QED

Theorem framed_array_element_summary:
  expr_body_pre cenv cx env obj es /\
  eval_expr cx obj es = (INL r,t) /\
  expr_type obj = ArrayT et bd /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  ee.scopes = t.scopes /\ ee.immutables = t.immutables /\ ee.gas_obs = [] /\
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  (vv_location (FST (compile_expr cenv ty obj sa)) = SOME LocCode \/
   (?n. bd = Fixed n)) /\
  read_result cx r ee = (INL (ArrayV av),ee) /\
  array_index (ArrayTV etv bd) av i = SOME v /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\ val_wf etv v /\ value_has_type etv v /\
  vv_post ctx func cenv cx obj es sa sd s0 ee r (LocatedValue ann p) q /\
  (p.ptr_location = LocMemory \/ p.ptr_location = LocCode) /\
  (p.ptr_location = LocMemory ==> ?n. bd = Fixed n) /\
  eval_operand p.ptr_operand q = SOME w /\
  j = (case bd of Fixed _ => 0 | Dynamic _ => 32) + Num i * type_memory_size etv /\
  eval_operand dst q = SOME (w + n2w j) /\
  (p.ptr_location = LocMemory ==> w2n (w + n2w j) = w2n w + j) /\
  gas_marked_path F ctx func s 0 (OK q) /\
  q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts ==>
  gas_summary_at F (ctx,func) []
    (select_result cx (ArrayT et bd) r (ValueSubscript (IntV i))) (ee,s)
    (\res ee' q. ?child. res = INL child /\
      vv_post ctx func cenv cx (Subscript et obj idx) es sa sd s0 ee' child
        (LocatedValue et (mk_ptr dst p.ptr_location)) q /\
      q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts)
    (\res ee' outcome. expr_exit res outcome)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all framed_array_select_read >> strip_tac >>
  drule_all vv_post_array_element >> strip_tac >>
  irule select_result_counted_summary >> simp[] >>
  qexists_tac `OK q` >> simp[] >>
  `ee with gas_obs := [] = ee` by
    (Cases_on `ee` >> gvs[vyperStateTheory.evaluation_state_component_equality]) >>
  simp[] >> metis_tac[]
QED

Theorem framed_array_post_view:
  expr_body_pre cenv cx env obj es /\
  eval_expr cx obj es = (INL r,t) /\ expr_type obj = ArrayT et bd /\
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  ee.scopes = t.scopes /\ ee.immutables = t.immutables /\
  vv_post ctx func cenv cx obj es sa sc s0 ee r (LocatedValue (ArrayT et bd) p) q /\
  (p.ptr_location = LocMemory \/ (~cenv.ce_is_ctor /\ p.ptr_location = LocCode)) ==>
  ?etv av w.
    evaluate_type (get_tenv cx) et = SOME etv /\
    evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
    read_result cx r ee = (INL (ArrayV av),ee) /\
    val_wf (ArrayTV etv bd) (ArrayV av) /\
    value_has_type (ArrayTV etv bd) (ArrayV av) /\
    eval_operand p.ptr_operand q = SOME w /\
    array_length (ArrayTV etv bd) av < dimword (:256) /\
    (!al. av = SArrayV al ==> ?n. bd = Fixed n)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  `?v w. read_result cx r ee = (INL v,ee) /\
           eval_operand p.ptr_operand q = SOME w` by
    (fs[loweringPostsTheory.vv_post_def, loweringPostsTheory.vv_holds_def,
        loweringPostsTheory.immutable_holds_def] >> metis_tac[]) >>
  `FST (read_result cx r ee) = FST (read_result cx r t)` by
    (irule read_result_nonstorage_frame >> simp[]) >>
  `read_result cx r t = (INL v,t)` by
    (Cases_on `read_result cx r t` >> imp_res_tac read_result_state >> gvs[]) >>
  `value_has_type (ArrayTV tv bd) v` by metis_tac[] >>
  `val_wf (ArrayTV tv bd) v` by
    metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
  rename1 `read_result cx r ee = (INL (ArrayV av),ee)` >>
  Cases_on `bd` >> Cases_on `av` >>
  gvs[vyperTypingTheory.value_has_type_def,
      vyperValueTheory.type_slot_size_def, vyperValueOperationTheory.array_length_def] >>
  `n * 1 <= n * type_slot_size tv` by simp[arithmeticTheory.LE_MULT_LCANCEL] >>
  decide_tac
QED
