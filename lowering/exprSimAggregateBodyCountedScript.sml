(* Replay boundary for body-aware counted aggregate children. *)
Theory exprSimAggregateBodyCounted
Ancestors
  exprSimAggregateChildren exprSimAggregateLoops exprSimSource
  gasSummary fragGasMode fragGasPath vyperInterpreter vyperState exprSimHypsDefs
  exprSimHyps exprSimUnwrap exprSimUnwrapProps exprSimMemoryRead
  exprLoweringProps loweringPosts compileEnv placeTypedCopyRecursivePath
  placeMemoryPrimitiveForward localMemoryStorePath freshWrites exprSimProps
  vyperAST vyperTypeCallGraph aggregateStoreSizePath
Libs
  monadsyntax

Theorem aggregate_body_marked_replay:
  gas_marked_exec memory (ctx,func) source (es,s0) marks res mid r ==>
  source (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (res,mid with gas_obs := [])
Proof
  simp[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` mp_tac) >> simp[]
QED

Theorem aggregate_body_marked_read_replay:
  expr_body_pre ce cx env e es /\
  gas_marked_exec memory (ctx,func) (eval_expr cx e) (es,s0)
    marks (INL tv) mid r /\
  read_result cx tv (mid with gas_obs := []) =
    (INL v,mid with gas_obs := []) ==>
  expr_body_pre ce cx env e
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) /\
  (do res <- eval_expr cx e; read_result cx res od)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
      (INL v,mid with gas_obs := [])
Proof
  strip_tac >> drule aggregate_body_marked_replay >> strip_tac >>
  simp[bind_def]
QED

(* Metadata required by the recursive counted typed-copy interface. *)
Theorem aggregate_body_copy_metadata:
  expr_body_pre ce cx env e es ==>
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv.
      evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields)
Proof
  strip_tac >> gvs[expr_body_pre_def, expr_sim_inv_def] >>
  first_assum ACCEPT_TAC
QED

Theorem unwrap_value_body_rebased_path:
  compile_expr ce ty e si = (vv,sj) /\
  expr_body_pre ce cx env e es /\
  unwrap_value ce vv sm = (op,su) /\ local_ptrs_reserved ce sm /\
  sa.cs_next_id <= sm.cs_next_id /\
  read_result cx tv es' = (INL v,es') /\
  vv_post ctx func ce cx e es sa sm s0 es' tv vv r /\
  fn_has_code sm su func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_marked_path F ctx func r 0 (OK u) /\
    expr_post ctx func ce cx e es'
      (sa with cs_next_var := sm.cs_next_var) su r es' v op u /\
    ~u.vs_halted /\ u.vs_current_bb = su.cs_current_bb /\
    u.vs_inst_idx = LENGTH su.cs_current_insts
Proof
  strip_tac >>
  drule vv_post_rebase >>
  disch_then assume_tac >>
  `vv_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
    sm r es' (Value v) vv r` by metis_tac[vv_post_read_result] >>
  Cases_on `post_value_type ce e = expr_type e`
  >- (mp_tac unwrap_value_path >>
      disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      disch_then (qspecl_then [`su`, `op`] mp_tac) >>
      impl_tac
      >- (simp[] >> conj_tac
          >- (gvs[local_ptrs_reserved_def, not_fresh_at_def] >> metis_tac[]) >>
          rpt strip_tac >> drule_all expr_body_pre_copy_ok >> simp[]) >>
      strip_tac >> qexists_tac `u` >>
      gvs[gas_marked_path_def] >> metis_tac[gas_path_normal]) >>
  `!t p. vv = LocatedValue t p ==> p.ptr_location = LocMemory` by
    metis_tac[aggregate_unequal_post_result_location] >>
  Cases_on `vv`
  >- (gvs[exprLoweringTheory.unwrap_value_def, compileEnvTheory.comp_return_def] >>
      qexists_tac `r` >> simp[gas_marked_path_def, gas_path_rules] >>
      drule expr_post_of_vv_post_stack >> simp[]) >>
  `p.ptr_location = LocMemory` by metis_tac[] >>
  Cases_on `is_word_type t`
  >- (mp_tac (GEN_ALL unwrap_memory_marked_read) >>
      disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      disch_then (qspecl_then [`su`, `op`] mp_tac) >>
      impl_tac
      >- (simp[] >> gvs[local_ptrs_reserved_def, not_fresh_at_def] >>
          metis_tac[]) >>
      strip_tac >>
      gvs[gas_marked_exec_def, read_result_def, return_def] >>
      qexists_tac `u` >> simp[] >>
      metis_tac[gas_marked_path_def, gas_path_normal]) >>
  gvs[exprLoweringTheory.unwrap_value_def, compileEnvTheory.comp_return_def] >>
  qexists_tac `r` >> simp[gas_marked_path_def, gas_path_rules] >>
  irule expr_post_of_vv_post_memory >> simp[] >> qexists_tac `t` >> simp[]
QED

Theorem aggregate_store_body_rebased_slice_path:
  compile_store_memory ce op (Var x) (expr_type e) (lowered_value_type ce e)
    su = ((),sb) /\
  expr_body_pre ce cx env e es /\
  (do res <- eval_expr cx e; read_result cx res od) es = (INL v,es') /\
  (int_calls_expr e <> [] /\ lowered_value_type ce e <> expr_type e ==>
    acyclic_struct_metadata ce.ce_struct_fields) /\
  not_fresh_at sm x /\ lookup_var x r = SOME w /\
  sm.cs_next_var <= su.cs_next_var /\
  (!z. op = Var z ==> not_fresh_at su z) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  stmt_state_rel ctx func ce cx es' r /\
  FLOOKUP r.vs_allocas did = SOME (b,k) /\ did < sa.cs_next_id /\
  b <= w2n w /\ w2n w + type_memory_size tv <= b+k /\
  w2n w + type_memory_size tv < dimword (:256) /\
  (!name a len. local_region ce es'.scopes r name a len ==>
    a+len <= w2n w \/ w2n w + type_memory_size tv <= a) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n w) (type_memory_size tv)) /\
  expr_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
    su r es' v op s /\
  fn_has_code su sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = su.cs_current_bb /\
  s.vs_inst_idx = LENGTH su.cs_current_insts ==>
  ?q. gas_marked_path F ctx func s 0 (OK q) /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory tv v (w2n w) q.vs_memory /\
    stmt_state_rel ctx func ce cx es' q /\
    (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==> lookup_var z q = SOME a) /\
    (!aid a. FLOOKUP r.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
    (!aid off sz a len.
      FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!name b k. local_region ce es'.scopes r name b k ==>
        off+sz <= b \/ b+k <= off) /\
      off <= a /\ a+len <= off+sz /\
      (a+len <= w2n w \/ w2n w+type_memory_size tv <= a) ==>
      mem_bytes_at a len q.vs_memory = mem_bytes_at a len r.vs_memory) /\
    locals_kept ce es' r q
Proof
  strip_tac >>
  `well_typed_expr env e` by fs[expr_body_pre_def] >>
  drule compile_store_memory_post_type >>
  disch_then (qspecl_then [`ce`, `op`, `Var x`] assume_tac) >>
  gvs[] >>
  `lookup_var x s = SOME w` by metis_tac[expr_post_rebased_lookup] >>
  `not_fresh_at su x` by metis_tac[not_fresh_at_mono] >>
  `stmt_state_rel ctx func ce cx es' s /\
   FLOOKUP s.vs_allocas did = SOME (b,k)` by fs[expr_post_def] >>
  `!name a len. local_region ce es'.scopes s name a len ==>
    a+len <= w2n w \/ w2n w + type_memory_size tv <= a` by
    (rpt strip_tac >>
     `local_region ce es'.scopes r name a len` by
       (irule local_region_frame >> conj_tac
        >- (qexists_tac `func` >> fs[stmt_state_rel_def, state_rel_def]) >>
        qexistsl_tac [`sm`, `es'.scopes`, `s`] >> simp[] >>
        metis_tac[expr_post_rebased_lookup]) >>
     first_x_assum drule >> simp[arithmeticTheory.ADD_COMM]) >>
  Cases_on `post_value_type ce e = expr_type e`
  >- suspend "same_layout" >>
  `~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e)` by
    metis_tac[post_value_type_word, post_value_type_bytestring] >>
  `acyclic_struct_metadata ce.ce_struct_fields` by
    (qpat_x_assum `_ ==> acyclic_struct_metadata _` irule >>
     conj_tac
     >- (Cases_on `e` >>
         fs[post_value_type_def, expr_type_def] >>
         rename1 `Call _ tgt _ _` >> Cases_on `tgt` >>
         fs[post_value_type_def, expr_type_def] >>
         simp[Once int_calls_expr_def]) >>
     metis_tac[post_value_type_lowered]) >>
  `type_widens_to (get_tenv cx) (post_value_type ce e) (expr_type e)` by
    (`expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
     drule_all post_value_type_widens >>
     fs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def]) >>
  `~is_word_type (post_value_type ce e) /\
   ~is_bytestring_type (post_value_type ce e)` by
    metis_tac[typedMemoryCopyTheory.return_source_word_widens_eq,
              typedMemoryCopyTheory.type_widens_from_bytestring] >>
  drule_all aggregate_child_physical_encoding >> strip_tac >>
  `w2n sw + type_memory_size stv < dimword (:256) /\
   (w2n sw + type_memory_size stv <= w2n w \/
    w2n w + type_memory_size tv <= w2n sw)` by
    (`expr_val_at ce cx (post_value_type ce e)
       (sa with cs_next_var := sm.cs_next_var) su es' v op s` by
       fs[expr_post_def] >>
     irule aggregate_physical_source_slot_bounds >>
     goal_assum (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `type_widens_to _ _ _`)) >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ s`)) >>
     goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME (b,k)`)) >>
     simp[arithmeticTheory.ADD_COMM] >>
     first_assum (ACCEPT_TAC o SRULE [arithmeticTheory.ADD_COMM])) >>
  `compile_store_memory_typed ce (Var x) (expr_type e) op
     (post_value_type ce e) su = ((),sb)` by
    fs[contextTheory.compile_store_memory_def] >>
  drule aggregate_body_copy_metadata >> strip_tac >>
  drule compile_store_memory_typed_forward_run >>
  disch_then (drule_at (Pat `type_widens_to _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ (expr_type e) = _`)) >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ s.vs_memory`)) >>
  disch_then (qspecl_then [`ctx`, `func`, `w`] mp_tac) >>
  (impl_tac
   >- (simp[venomStateTheory.eval_operand_def, arithmeticTheory.ADD_COMM] >>
       first_assum ACCEPT_TAC)) >>
  strip_tac >> qexists_tac `t` >> simp[] >>
  drule aggregate_store_rebased_control_frame >>
  disch_then (qspecl_then [`t`, `type_memory_size tv`, `w2n w`] mp_tac) >>
  (impl_tac
   >- (gvs[typedMemoryCopyTheory.typed_copy_state_frame_def,
           typedMemoryCopyTheory.typed_copy_frame_def] >>
       rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >> gvs[] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume aggregate_store_body_rebased_slice_path[same_layout]:
  `type_memory_size tv + 64 < dimword (:256)` by
    (Cases_on `is_word_type (expr_type e)`
     >- (drule_all word_tv_memory_size >> simp[wordsTheory.dimword_def]) >>
     drule_all expr_body_pre_copy_ok >> simp[wordsTheory.dimword_def]) >>
  `?sw. eval_operand op s = SOME sw /\
    (if is_word_type (expr_type e) then sw = typed_val_to_w256 tv v
     else val_in_memory tv v (w2n sw) s.vs_memory)` by
    (fs[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  `compile_store_memory ce op (Var x) (expr_type e) (expr_type e) su = ((),sb)` by
    metis_tac[] >>
  drule compile_store_memory_same_type_size_forward >>
  disch_then (drule_at (Pat `evaluate_type _ _ = SOME tv`)) >>
  disch_then (drule_at (Pat `eval_operand op s = SOME sw`)) >>
  disch_then (qspecl_then [`v`, `func`, `w`, `ctx`] mp_tac) >>
  (impl_tac >- simp[venomStateTheory.eval_operand_def]) >>
  strip_tac >> qexists_tac `t` >> simp[] >>
  drule aggregate_store_rebased_control_frame >>
  disch_then (qspecl_then [`t`, `type_memory_size tv`, `w2n w`] mp_tac) >>
  (impl_tac >- (simp[] >> conj_tac
    >- (qpat_x_assum `t with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|> = s`
          (mp_tac o Q.AP_TERM `\z. z with <|vs_prev_bb := s.vs_prev_bb;
            vs_current_bb := s.vs_current_bb|>`) >> simp[]) >>
    rpt conj_tac >> first_assum (ACCEPT_TAC o SRULE [arithmeticTheory.ADD_COMM]))) >>
  strip_tac >> gvs[] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise aggregate_store_body_rebased_slice_path

Theorem aggregate_body_child_store_slice_path:
  compile_expr ce ty e si = (vv,sj) /\
  unwrap_value ce vv sm = (op,su) /\
  compile_store_memory ce op (Var x) (expr_type e) (lowered_value_type ce e)
    su = ((),sb) /\
  expr_body_pre ce cx env e es /\
  (do res <- eval_expr cx e; read_result cx res od) es = (INL v,es') /\
  (int_calls_expr e <> [] /\ lowered_value_type ce e <> expr_type e ==>
    acyclic_struct_metadata ce.ce_struct_fields) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_var <= su.cs_next_var /\
  (!z. op = Var z ==> not_fresh_at su z) /\
  cs_extends sm su /\ cs_extends su sb /\
  read_result cx tvv es' = (INL v,es') /\
  vv_post ctx func ce cx e es sa sm s0 es' tvv vv r /\
  not_fresh_at sm x /\ lookup_var x r = SOME w /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  stmt_state_rel ctx func ce cx es' r /\
  FLOOKUP r.vs_allocas did = SOME (b,k) /\ did < sa.cs_next_id /\
  b <= w2n w /\ w2n w + type_memory_size tv <= b+k /\
  w2n w + type_memory_size tv < dimword (:256) /\
  (!n b k. local_region ce es'.scopes r n b k ==>
    b+k <= w2n w \/ w2n w + type_memory_size tv <= b) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n w) (type_memory_size tv)) /\
  (!q. val_in_memory tv v (w2n w) q.vs_memory /\
      stmt_state_rel ctx func ce cx es' q /\
      (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==> lookup_var z q = SOME a) /\
      (!aid b. FLOOKUP r.vs_allocas aid = SOME b ==> FLOOKUP q.vs_allocas aid = SOME b) /\
      (!aid off sz a k.
        FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
        (!n b len. local_region ce es'.scopes r n b len ==> off+sz <= b \/ b+len <= off) /\
        off <= a /\ a+k <= off+sz /\
        (a+k <= w2n w \/ w2n w+type_memory_size tv <= a) ==>
        mem_bytes_at a k q.vs_memory = mem_bytes_at a k r.vs_memory) /\
      locals_kept ce es' r q ==> Q q) /\
  ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?q. gas_marked_path F ctx func r 0 (OK q) /\ Q q /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `fn_has_code sm su func /\ fn_has_code su sb func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  drule_all unwrap_value_body_rebased_path >> strip_tac >>
  drule_all aggregate_store_body_rebased_slice_path >> strip_tac >>
  qexists_tac `q` >> simp[] >> conj_tac
  >- metis_tac[gas_marked_path_then, arithmeticTheory.ADD_CLAUSES] >>
  first_x_assum irule >> simp[] >> rpt conj_tac >>
  first_assum (ACCEPT_TAC o SRULE [arithmeticTheory.ADD_COMM])
QED
