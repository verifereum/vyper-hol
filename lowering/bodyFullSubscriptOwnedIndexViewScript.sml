(* The no-copy subscript takes vv_operand directly. A non-word stack
   result is a memory address here, just like a located memory result. *)
Theory bodyFullSubscriptOwnedIndexView
Ancestors
  bodyFullSubscriptCapturedEndpoint loweringPosts exprSimMemDefs exprSimProps
  bodyPtrDefs bodyPtrBopHashFootprint logValueFramePtr
  context exprLoweringProps compileEnv vyperState vyperValue words

Theorem owned_stack_memory_post[local]:
  vv_post H ctx fn ce cx obj es sa sm s0 mid (Value av) (StackValue t op) s /\
  vv_own ce cx (post_value_type ce obj) sa sm mid (Value av) (StackValue t op) s /\
  ~is_word_type (post_value_type ce obj) ==>
  vv_post H ctx fn ce cx obj es sa sm s0 mid (Value av)
    (LocatedValue (post_value_type ce obj) (mk_ptr op LocMemory)) s
Proof
  simp[vv_post_def, vv_holds_def, expr_val_rel_def, vv_at_def, vv_own_def,
       expr_val_at_def, expr_val_own_def, mk_ptr_def, read_result_def, return_def] >>
  metis_tac[]
QED

Theorem owned_value_memory_post[local]:
  vv_post H ctx fn ce cx obj es sa sm s0 mid (Value av) vv s /\
  vv_own ce cx (post_value_type ce obj) sa sm mid (Value av) vv s /\
  ~is_word_type (post_value_type ce obj) /\
  (case vv_location vv of NONE => LocMemory | SOME l => l) = LocMemory ==>
  vv_post H ctx fn ce cx obj es sa sm s0 mid (Value av)
    (LocatedValue (post_value_type ce obj) (mk_ptr (vv_operand vv) LocMemory)) s
Proof
  Cases_on `vv` >> simp[vv_operand_def, vv_location_def]
  >- metis_tac[owned_stack_memory_post] >>
  strip_tac >>
  gvs[vv_post_def, vv_holds_def, vv_at_def, vv_own_def, vv_storage_live_def, mk_ptr_def,
      read_result_def, return_def] >> metis_tac[]
QED

Theorem owned_value_memory_guarantees[local]:
  ~is_word_type ty /\
  (case vv_location vv of NONE => LocMemory | SOME l => l) = LocMemory ==>
  (vv_own ce cx ty sa sm ee (Value av) vv s <=>
   vv_own ce cx ty sa sm ee (Value av)
     (LocatedValue ty (mk_ptr (vv_operand vv) LocMemory)) s) /\
  (ptr_vv_ok cx ty (Value av) vv ee G tn s <=>
   ptr_vv_ok cx ty (Value av)
     (LocatedValue ty (mk_ptr (vv_operand vv) LocMemory)) ee G tn s)
Proof
  Cases_on `vv` >>
  simp[vv_own_def, ptr_vv_ok_def, ptr_val_ok_def, expr_val_own_def,
       vv_operand_def, vv_location_def, mk_ptr_def, read_result_def, return_def]
QED

Theorem subscript_owned_array_index_view:
  expr_body_pre ce cx env (Subscript ann obj idx) es /\
  eval_expr cx obj es = (INL (Value av),mid) /\
  expr_type obj = ArrayT et bd /\
  post_value_type ce obj = expr_type obj /\
  evaluate_type (get_tenv cx) (expr_type obj) = SOME (ArrayTV etv bd) /\
  vv_post H ctx fn ce cx obj es sa sm s0 mid (Value av) vv s /\
  vv_own ce cx (post_value_type ce obj) sa sm mid (Value av) vv s /\
  ptr_vv_ok cx (post_value_type ce obj) (Value av) vv mid G tn s /\
  (!t' p. vv = LocatedValue t' p ==> p.ptr_location = LocMemory) /\
  ptr_buf_ok ce obj (vv_operand vv) G s /\
  bind (eval_expr cx idx) (read_result cx) (mid with gas_obs := gs) = (INL key,fin) /\
  expr_post H ctx fn ce cx idx (mid with gas_obs := gs) sm sn s fin key op u /\
  ghost_kept_at lo ce (mid with gas_obs := gs) sm G tn s G' tn' /\
  local_ptrs_reserved ce sm /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!l. vv_operand vv <> Label l) ==>
  (case vv_location vv of NONE => LocMemory | SOME l => l) = LocMemory /\
  vv_own ce cx (expr_type obj) sa sm fin (Value av) vv u /\
  ptr_vv_ok cx (expr_type obj) (Value av) vv fin G' tn' u /\
  ptr_buf_ok ce obj (vv_operand vv) G' u /\
  value_has_type (ArrayTV etv bd) av /\
  val_wf (ArrayTV etv bd) av /\
  ?addr. eval_operand (vv_operand vv) s = SOME addr /\
         eval_operand (vv_operand vv) u = SOME addr /\
         w2n addr + type_memory_size (ArrayTV etv bd) < dimword (:256) /\
         (!mem. mem_agree_outside tn'.t_mem u.vs_memory mem ==>
                val_in_memory (ArrayTV etv bd) av (w2n addr) mem) /\
         (!cap. bd = Dynamic cap ==>
          ?vs x b sz. av = ArrayV (DynArrayV vs) /\
                      LENGTH vs <= cap /\
                      mload (w2n addr) u = n2w (LENGTH vs) /\
                      mem_word_taint tn'.t_mem (w2n addr) = {} /\
                      vv_operand vv = Var x /\
                      FLOOKUP G' x = SOME (b,sz) /\
                      b <= w2n addr /\
                      w2n addr + 32 + cap * type_memory_size etv <= b + sz /\
                      ptr_covers G' tn' x u 32)
Proof
  DISCH_THEN (MAP_EVERY assume_tac o CONJUNCTS) >>
  `(case vv_location vv of NONE => LocMemory | SOME l => l) = LocMemory` by
    (Cases_on `vv` >> fs[vv_location_def]) >>
  `~is_word_type (post_value_type ce obj)` by simp[is_word_type_def] >>
  drule_all_then assume_tac owned_value_memory_post >>
  drule_all_then strip_assume_tac owned_value_memory_guarantees >>
  `evaluate_type (get_tenv cx) (post_value_type ce obj) = SOME (ArrayTV etv bd)` by gvs[] >>
  `expr_body_pre ce cx env obj es` by
    (qpat_assum `expr_body_pre _ _ _ (Subscript _ _ _) _`
       (mp_then Any irule exprSimSubscriptArraySourceTheory.expr_body_pre_array_subscript_base_eval) >>
     qpat_assum `eval_expr cx obj _ = (INL _,_)` (irule_at Any) >> simp[]) >>
  `value_has_type (ArrayTV etv bd) av` by
    (drule_all_then strip_assume_tac exprSimSourceTheory.expr_body_pre_runtime_typed >>
     gvs[read_result_def, return_def]) >>
  qabbrev_tac `p = mk_ptr (vv_operand vv) LocMemory` >>
  `p.ptr_location = LocMemory /\ p.ptr_operand = vv_operand vv` by
    simp[Abbr `p`, mk_ptr_def] >>
  `vv_own ce cx (post_value_type ce obj) sa sm mid (Value av)
     (LocatedValue (post_value_type ce obj) p) s /\
   ptr_vv_ok cx (post_value_type ce obj) (Value av)
     (LocatedValue (post_value_type ce obj) p) mid G tn s` by metis_tac[] >>
  `(!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
   (!l. p.ptr_operand <> Label l)` by simp[] >>
  drule_all_then strip_assume_tac bodyFullSubscriptCapturedPlaceTheory.subscript_owned_value_transport >>
  `!x. vv_operand vv = Var x ==> FLOOKUP G' x = FLOOKUP G x` by
    (fs[ghost_kept_at_def] >> metis_tac[]) >>
  `ptr_buf_ok ce obj (vv_operand vv) G' u` by
    (irule ptr_buf_ok_frame >> qexistsl [`G`,`s`] >> gvs[]) >>
  `vv_own ce cx (expr_type obj) sa sm fin (Value av) vv u /\
   ptr_vv_ok cx (expr_type obj) (Value av) vv fin G' tn' u` by metis_tac[] >>
  `read_result cx (Value av) mid = (INL av,mid)` by simp[read_result_def,return_def] >>
  drule_all_then assume_tac exprSimSubscriptArraySuffixTheory.vv_post_memory_footprint_bound >>
  `val_footprint (ArrayTV etv bd) av = type_memory_size (ArrayTV etv bd)` by
    (Cases_on `av` >> simp[val_footprint_def]) >>
  `ptr_mem_ok cx (expr_type obj) av (vv_operand vv) G' tn' u` by
    gvs[ptr_vv_ok_def, read_result_def, return_def] >>
  `eval_operand (vv_operand vv) s = SOME w /\ eval_operand (vv_operand vv) u = SOME w` by gvs[] >>
  simp[] >> conj_tac >- metis_tac[ptr_mem_ok_robust] >>
  rpt strip_tac >> qpat_x_assum `bd = Dynamic cap` SUBST_ALL_TAC >>
  (* Keep the supplier's disjunctive premise intact for matching. *)
  Q.SUBGOAL_THEN
    `(?id path. Value av = PlaceR (MemoryPlace id path) /\ base_from_pop obj) \/
     (?v. Value av = Value v /\ p.ptr_location = LocMemory /\
          vv_own ce cx (post_value_type ce obj) sa sm mid (Value av)
            (LocatedValue (post_value_type ce obj) p) s)` assume_tac >- simp[] >>
  drule_all_then strip_assume_tac subscript_dynamic_header_at_index >>
  gvs[read_result_def, return_def] >> metis_tac[]
QED
