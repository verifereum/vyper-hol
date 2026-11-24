(* The result ALLOCA precedes source materialization in a widening arm. *)
Theory bodyIfExpAllocMods
Ancestors
  bodyFullAllocaFresh bodyFullPostsMods bodyFullShadowBodyInv bodyFullHashKeccakFixed
  exprOperandVar
  exprSimIfExpWidenedAdapter exprSimVVFrame exprSimProps exprSimMemDefs
  bodyPtrDefs bodyInvSplit loweringPosts loweringStateRelDefs exprLoweringProps
  abiBuiltinAllocation stmtReasonMemory loweringHalt ptrDiscipline venomMemDefs
  emitHelperProps fragExec venomExecSemantics context robustCopyTransportPtr
  vyperStorageFootprint vyperState venomState finite_map

Theorem ifexp_alloc_new_sites[local]:
  compile_alloc_buffer n sm = (buf,k) /\ buf.buf_operand = Var p /\
  run_inst_seq (emitted_insts sm k) s = OK raw /\
  q = raw with vs_inst_idx := j /\ n < dimword (:256) /\
  FLOOKUP q.vs_allocas aid = SOME (b,m) ==>
  FLOOKUP s.vs_allocas aid = SOME (b,m) \/ s.vs_alloca_next <= b
Proof
  strip_tac >> drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[run_inst_seq_def, AllCaseEqs()] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_alloca_eq] >> Cases_on `FLOOKUP s.vs_allocas sm.cs_next_id` >>
  gvs[AllCaseEqs(), update_var_def, FLOOKUP_UPDATE, wordsTheory.w2n_n2w] >>
  rpt strip_tac >> Cases_on `aid = sm.cs_next_id` >> gvs[FLOOKUP_UPDATE]
QED

Theorem ifexp_alloc_immutable[local]:
  immutable_frame_mods func ce cx ee s /\
  q.vs_memory = s.vs_memory /\ q.vs_data_section = s.vs_data_section /\
  s.vs_alloca_next <= q.vs_alloca_next /\
  (!aid b n. FLOOKUP q.vs_allocas aid = SOME (b,n) ==>
             FLOOKUP s.vs_allocas aid = SOME (b,n) \/ s.vs_alloca_next <= b) /\
  (!id b n. local_region ce ee.scopes q id b n <=> local_region ce ee.scopes s id b n) ==>
  immutable_frame_mods func ce cx ee q
Proof
  strip_tac >> fs[immutable_frame_mods_def] >> conj_tac
  >- (fs[immutables_rel_mods_def, immutables_rel_def] >> first_assum ACCEPT_TAC) >>
  fs[immutable_alloca_sep_mods_def] >> rpt gen_tac >> strip_tac >>
  irule immutable_alloca_sep_frame >> qexistsl [`s`,`ee`] >> simp[] >>
  rpt gen_tac >> disch_tac >> disj1_tac >> qexists `id` >>
  `!u. local_region (ce with ce_module := src) ee.scopes u id b sz =
       local_region ce ee.scopes u id b sz` by simp[local_region_def] >>
  metis_tac[]
QED

Theorem ifexp_alloc_ghost[local]:
  ghost_inv_at_mods D lo d ce cx ee G tn s /\
  stmt_state_rel H ctx func ce cx ee s /\ local_ptrs_reserved ce sm /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x. not_fresh_at sm x ==>
    lookup_var x q = lookup_var x s /\ FLOOKUP Ga x = FLOOKUP G x /\
    op_taint ta (Var x) = op_taint tn (Var x)) /\
  q with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
           vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|> = s /\
  allocas_from lo q /\ s.vs_alloca_next <= q.vs_alloca_next /\
  ta.t_stor = tn.t_stor /\ ta.t_trans = tn.t_trans /\ ta.t_imm = tn.t_imm /\
  (!i. i IN ta.t_mem <=> i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < stop)) ==>
  ghost_inv_at_mods D lo d ce cx ee Ga ta q
Proof
  strip_tac >>
  `ghost_inv_at D 0 d ce cx ee G tn s /\ lo <= s.vs_alloca_next` by
    (fs[ghost_inv_at_mods_def, ghost_inv_at_def, allocas_from_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_inv_at D 0 d ce cx ee Ga ta q` by
    (irule alloc_buffer_ghost_inv_at >> conj_tac >- simp[allocas_from_def] >>
     qexistsl [`G`,`H`,`ctx`,`stop`,`func`,`s`,`sm`,`tn`] >> simp[]) >>
  `q.vs_memory = s.vs_memory` by
    (qpat_assum `q with <|vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _|> = s` (SUBST1_TAC o SYM) >> simp[]) >>
  `!i. i < lo /\ i IN ta.t_mem ==> i IN tn.t_mem` by (simp[] >> decide_tac) >>
  fs[ghost_inv_at_mods_def, ghost_inv_at_def] >> rpt conj_tac
  >- metis_tac[]
  >- (rpt strip_tac >> `not_fresh_at sm x` by fs[local_ptrs_reserved_def] >>
      metis_tac[]) >>
  decide_tac
QED

Theorem ifexp_alloc_holds[local]:
  vv_holds_mods ce cx ty tv vv ee s /\ q.vs_memory = s.vs_memory /\
  contract_storage q = contract_storage s /\ contract_transient q = contract_transient s /\
  eval_operand (vv_operand vv) q = eval_operand (vv_operand vv) s ==>
  vv_holds_mods ce cx ty tv vv ee q
Proof
  Cases_on `vv`
  >- (simp[vv_holds_mods_def] >> metis_tac[vv_holds_vars_frame]) >>
  rename1 `LocatedValue ty' p` >> Cases_on `p.ptr_location = LocCode`
  >- (simp[vv_operand_def, vv_holds_mods_def, immutable_holds_mods_def] >>
      metis_tac[immutable_holds_memory_cong]) >>
  simp[vv_holds_mods_def] >> metis_tac[vv_holds_vars_frame]
QED

Theorem ifexp_alloc_place[local]:
  vv_place_ptr_mods ce cx ee s tv vv /\
  eval_operand (vv_operand vv) q = eval_operand (vv_operand vv) s /\
  (!id x n w. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var x) n) /\
              lookup_var x s = SOME w ==> lookup_var x q = SOME w) ==>
  vv_place_ptr_mods ce cx ee q tv vv
Proof
  strip_tac >>
  `!ce'. ce'.ce_vars = ce.ce_vars /\ vv_place_ptr ce' cx ee s tv vv ==>
         vv_place_ptr ce' cx ee q tv vv` by
    (rpt strip_tac >> irule vv_place_ptr_vars_frame >> qexists `s` >>
     simp[] >> first_assum ACCEPT_TAC) >>
  Cases_on `tv`
  >- (Cases_on `vv` >> fs[vv_place_ptr_mods_def] >> metis_tac[])
  >- (rename1 `PlaceR pl` >> Cases_on `pl` >> Cases_on `vv` >>
      fs[vv_place_ptr_mods_def] >> metis_tac[]) >>
  Cases_on `vv` >> fs[vv_place_ptr_mods_def] >> metis_tac[]
QED

Theorem ifexp_alloc_post[local]:
  vv_post_mods H ctx func ce cx e es sa sm s0 ee tv vv s /\
  stmt_state_rel H ctx func ce cx ee q /\ immutable_frame_mods func ce cx ee q /\
  q.vs_memory = s.vs_memory /\ contract_storage q = contract_storage s /\
  contract_transient q = contract_transient s /\
  eval_operand (vv_operand vv) q = eval_operand (vv_operand vv) s /\
  (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
  (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP q.vs_allocas aid = SOME b) /\
  (!id b n. local_region ce ee.scopes q id b n <=> local_region ce ee.scopes s id b n) /\
  sm.cs_next_id <= k.cs_next_id /\
  (!id x n w. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var x) n) /\
    lookup_var x s = SOME w ==> lookup_var x q = SOME w) ==>
  vv_post_mods H ctx func ce cx e es sa k s0 ee tv vv q
Proof
  strip_tac >> fs[vv_post_mods_def] >> rpt conj_tac
  >- (irule ifexp_alloc_holds >> qexists `s` >> simp[])
  >- (irule vv_at_alloc_mono_frame >> qexistsl [`s`,`sm`] >> simp[])
  >- (irule ifexp_alloc_place >> qexists `s` >> simp[] >> first_assum ACCEPT_TAC)
  >- (strip_tac >> irule vv_own_alloc_mono_frame >> qexistsl [`s`,`sm`] >> simp[])
  >- (Cases_on `vv` >> fs[vv_operand_def])
  >- metis_tac[]
  >- (irule locals_kept_mem_tail >> goal_assum (drule_at Any) >> simp[]) >>
  strip_tac >> irule pure_frame_mem_tail >> qexists `s` >> simp[]
QED

Theorem ifexp_alloc_robust[local]:
  q.vs_memory = s.vs_memory /\
  (!i. i < s.vs_alloca_next ==> (i IN ta.t_mem <=> i IN tn.t_mem)) /\
  val_wf rt v /\
  (val_footprint rt v = 0 \/ b + val_footprint rt v <= s.vs_alloca_next) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory rt v b mem) ==>
  !mem. mem_agree_outside ta.t_mem q.vs_memory mem ==> val_in_memory rt v b mem
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  gen_tac >> disch_tac >> irule robust_val_in_memory_exterior_frame >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`s.vs_memory`,`q.vs_memory`,`tn.t_mem`,`ta.t_mem`,
             `{i | s.vs_alloca_next <= i}`] >>
  simp[] >> rpt strip_tac >> decide_tac
QED

Theorem ifexp_alloc_memory_pointer[local]:
  ptr_mem_ok cx ty v op G tn s /\
  (!w rt. eval_operand op s = SOME w /\ evaluate_type (get_tenv cx) ty = SOME rt ==>
     val_wf rt v /\ (val_store_size rt v = 0 \/ w2n w + val_store_size rt v <= s.vs_alloca_next)) /\
  eval_operand op q = eval_operand op s /\ q.vs_memory = s.vs_memory /\
  (!x. op = Var x ==> FLOOKUP Ga x = FLOOKUP G x) /\
  (!i. i < s.vs_alloca_next ==> (i IN ta.t_mem <=> i IN tn.t_mem)) ==>
  ptr_mem_ok cx ty v op Ga ta q
Proof
  simp[ptr_mem_ok_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_assum `!w rt. _` (drule_all_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `!tv w. _ ==> (!mem. _) /\ _` (drule_all_then strip_assume_tac) >>
  conj_tac
  >- (qpat_assum `q.vs_memory = _` (SUBST1_TAC o SYM) >>
      match_mp_tac (Q.INST [`q` |-> `q`, `ta` |-> `ta`, `s` |-> `s`, `tn` |-> `tn`]
        ifexp_alloc_robust) >>
      simp[] >> mp_tac (Q.SPECL [`tv`,`v`] val_footprint_le_store_size) >> decide_tac) >>
  disch_tac >> qpat_x_assum `val_footprint tv v <> 0 ==> _`
    (fn th => first_assum (strip_assume_tac o MATCH_MP th)) >>
  qexistsl [`x`,`b`,`sz`] >> simp[] >> metis_tac[]
QED

Theorem ifexp_alloc_ptr[local]:
  ptr_vv_ok cx ty tv vv ee G tn s /\ vv_store_bound cx ty lt ee tv vv s /\
  (!v rt. read_result cx tv ee = (INL v,ee) /\
           evaluate_type (get_tenv cx) ty = SOME rt ==> value_has_type rt v) /\
  eval_operand (vv_operand vv) q = eval_operand (vv_operand vv) s /\
  op_taint ta (vv_operand vv) = op_taint tn (vv_operand vv) /\
  op_prov Ga (vv_operand vv) = op_prov G (vv_operand vv) /\
  (!x. vv_operand vv = Var x ==> FLOOKUP Ga x = FLOOKUP G x) /\
  q.vs_memory = s.vs_memory /\ q.vs_accounts = s.vs_accounts /\
  q.vs_call_ctx = s.vs_call_ctx /\ q.vs_transient = s.vs_transient /\
  ta.t_stor = tn.t_stor /\ ta.t_trans = tn.t_trans /\
  (!i. i < s.vs_alloca_next ==> (i IN ta.t_mem <=> i IN tn.t_mem)) ==>
  ptr_vv_ok cx ty tv vv ee Ga ta q
Proof
  strip_tac >>
  `!v. (((?ty'. vv = StackValue ty' (vv_operand vv)) /\ ~is_word_type ty) \/
        (?ty' p. vv = LocatedValue ty' p /\ p.ptr_location = LocMemory)) /\
       read_result cx tv ee = (INL v,ee) /\ ptr_mem_ok cx ty v (vv_operand vv) G tn s ==>
       ptr_mem_ok cx ty v (vv_operand vv) Ga ta q` by
    (rpt gen_tac >> strip_tac >> irule ifexp_alloc_memory_pointer >>
     qexistsl [`G`,`s`,`tn`] >> simp[] >> rpt gen_tac >> strip_tac >>
     (conj_tac >- metis_tac[valueEncodingTypingTheory.value_has_type_val_wf]) >>
     qpat_assum `vv_store_bound _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [vv_store_bound_def]) >>
     metis_tac[vv_operand_def]) >>
  Cases_on `vv` >> gvs[ptr_vv_ok_def, vv_operand_def, ptr_val_ok_def] >>
  metis_tac[]
QED

Theorem ifexp_alloc_ctor_code[local]:
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?v. read_result cx tv ee = (INL v,ee) /\
      !rt w. evaluate_type (get_tenv cx) ty = SOME rt /\
             eval_operand (vv_operand vv) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
               val_in_memory rt v (w2n w) mem)) /\
  (!v rt. read_result cx tv ee = (INL v,ee) /\
           evaluate_type (get_tenv cx) ty = SOME rt ==> value_has_type rt v) /\
  eval_operand (vv_operand vv) q = eval_operand (vv_operand vv) s /\
  q.vs_memory = s.vs_memory /\ lo <= s.vs_alloca_next /\
  (!i. i < s.vs_alloca_next ==> (i IN ta.t_mem <=> i IN tn.t_mem)) ==>
  ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?v. read_result cx tv ee = (INL v,ee) /\
      !rt w. evaluate_type (get_tenv cx) ty = SOME rt /\
             eval_operand (vv_operand vv) q = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside ta.t_mem q.vs_memory mem ==>
               val_in_memory rt v (w2n w) mem)
Proof
  strip_tac >> strip_tac >> fs[] >> rpt gen_tac >> strip_tac >>
  qpat_assum `!rt w. _ ==> _ /\ (!mem. _)`
    (qspecl_then [`rt`,`w`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_assum `q.vs_memory = _` (SUBST1_TAC o SYM) >>
  match_mp_tac (Q.INST [`q` |-> `q`, `ta` |-> `ta`, `s` |-> `s`, `tn` |-> `tn`]
    ifexp_alloc_robust) >>
  `val_wf rt v` by metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  simp[] >> drule val_footprint_le >> decide_tac
QED

(* The literal site can be reused by a loop. Its result is still disjoint
   from the locals and every live allocation preceding the arm's end. *)
Theorem ifexp_arm_result_alloc_mods:
  compile_expr ce ty e sa = (vv,sm) /\ local_ptrs_reserved ce sa /\
  compile_alloc_buffer n sm = (buf,k) /\ fn_has_code sm k func /\
  fn_inst_ids_distinct func /\ n < dimword (:256) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  storage_trace_domain cx st0 ee.storage_trace /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es sa sm s0 ee tv vv s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  ptr_vv_ok cx (post_value_type ce e) tv vv ee G tn s /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv s /\
  (!ty' op. vv = StackValue ty' op /\ ~is_word_type (post_value_type ce e) ==>
    ptr_buf_ok ce e op G s) /\
  (!ty' p. vv = LocatedValue ty' p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?v. read_result cx tv ee = (INL v,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
             eval_operand (vv_operand vv) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rt v (w2n w) mem)) /\
  (!v rt. read_result cx tv ee = (INL v,ee) /\
    evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt ==>
    value_has_type rt v) ==>
  ?p w q Ga ta raw.
    buf.buf_operand = Var p /\ buf.buf_size = n /\
    sm.cs_next_id + 1 = k.cs_next_id /\ sm.cs_next_var + 1 = k.cs_next_var /\
    ~not_fresh_at sm p /\ not_fresh_at k p /\ local_ptrs_reserved ce k /\
    cs_extends sm k /\
    run_inst_seq (emitted_insts sm k) s = OK raw /\
    q = raw with vs_inst_idx := LENGTH k.cs_current_insts /\
    Ga = step_prov PG G (mk_inst sm.cs_next_id ALLOCA [Lit (n2w n)] [p]) raw /\
    ta = step_taint (mk_inst sm.cs_next_id ALLOCA [Lit (n2w n)] [p]) s raw tn /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK q,Ga,ta)) /\
    ~q.vs_halted /\ q.vs_current_bb = k.cs_current_bb /\
    q.vs_inst_idx = LENGTH k.cs_current_insts /\ alloca_history func q /\
    allocas_from lo q /\ (ctx_has_dalloca ctx ==> allocas_below_fmp q) /\
    s.vs_alloca_next <= q.vs_alloca_next /\ lo <= w2n w /\
    w2n w + n < dimword (:256) /\ w2n w + n <= q.vs_alloca_next /\
    lookup_var p q = SOME w /\ ptr_covers Ga ta p q n /\
    FLOOKUP q.vs_allocas sm.cs_next_id = SOME (w2n w,n) /\
    FLOOKUP Ga p = SOME (w2n w,n) /\
    (!aid b len. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n w) n b len) /\
    (!id b len. local_region ce ee.scopes q id b len ==>
      regions_disjoint (w2n w) n b len) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP q.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sm x ==>
       lookup_var x q = lookup_var x s /\ FLOOKUP Ga x = FLOOKUP G x /\
       op_taint ta (Var x) = op_taint tn (Var x)) /\
    q.vs_memory = s.vs_memory /\ q.vs_data_section = s.vs_data_section /\
    q.vs_gas_readings = s.vs_gas_readings /\ q.vs_labels = s.vs_labels /\
    ta.t_stor = tn.t_stor /\ ta.t_trans = tn.t_trans /\ ta.t_imm = tn.t_imm /\
    (!i. i IN ta.t_mem <=> i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < w2n w + n)) /\
    (!id b len. local_region ce ee.scopes q id b len <=> local_region ce ee.scopes s id b len) /\
    eval_operand (vv_operand vv) q = eval_operand (vv_operand vv) s /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      vv_post_mods H ctx func ce cx e es sa k s0 ee tv vv q /\
      ghost_inv_at_mods (DF H) lo d ce cx ee Ga ta q) /\
    (vv_own ce cx (post_value_type ce e) sa sm ee tv vv s ==>
      vv_own ce cx (post_value_type ce e) sa k ee tv vv q) /\
    ptr_vv_ok cx (post_value_type ce e) tv vv ee Ga ta q /\
    vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv q /\
    (!ty' op. vv = StackValue ty' op /\ ~is_word_type (post_value_type ce e) ==>
      ptr_buf_ok ce e op Ga q) /\
    (!ty' p. vv = LocatedValue ty' p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok ce e p.ptr_operand Ga q) /\
    (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
      ?v. read_result cx tv ee = (INL v,ee) /\
        !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
               eval_operand (vv_operand vv) q = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside ta.t_mem q.vs_memory mem ==>
            val_in_memory rt v (w2n w) mem))
Proof
  strip_tac >> drule_then strip_assume_tac (cj 1 compile_expr_grows) >>
  `local_ptrs_reserved ce sm` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
        stmt_state_rel H ctx func ce cx ee s /\ immutable_frame_mods func ce cx ee s /\
        ghost_inv_at_mods (DF H) lo d ce cx ee G tn s` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ ghost_inv_at_mods _ _ _ _ _ _ _ _ s`
       (drule_then strip_assume_tac) >> fs[vv_post_mods_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  first_x_assum (drule_then strip_assume_tac) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
  drule_all (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
             alloc_buffer_origin_ptr_path_with_raw_endpoint) >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`]
            (qx_choosel_then [`p`,`w`,`q`,`Ga`,`ta`,`raw`] strip_assume_tac)) >>
  suspend "boundary"
QED

Resume ifexp_arm_result_alloc_mods[boundary]:
  drule compile_alloc_buffer_parts >> strip_tac >>
  drule_then assume_tac compile_alloc_buffer_extends >>
  `p = STRING #"%" (toString sm.cs_next_var)` by metis_tac[operand_11] >>
  `local_ptrs_reserved ce k` by
    (irule local_ptrs_reserved_next_var >> qexists `sm` >> simp[]) >>
  `lo <= w2n w` by
    (qpat_assum `allocas_from lo q` (mp_tac o REWRITE_RULE [allocas_from_def]) >>
     disch_then (qspecl_then [`sm.cs_next_id`,`w2n w`,`n`] mp_tac) >> simp[]) >>
  `q.vs_memory = s.vs_memory /\ q.vs_data_section = s.vs_data_section /\
   q.vs_gas_readings = s.vs_gas_readings /\ q.vs_halted = s.vs_halted /\
   q.vs_labels = s.vs_labels /\ q.vs_accounts = s.vs_accounts /\
   q.vs_call_ctx = s.vs_call_ctx /\ q.vs_transient = s.vs_transient` by
    (qpat_assum `q with <|vs_vars := _; vs_allocas := _;
      vs_alloca_next := _; vs_inst_idx := _|> = s` (SUBST1_TAC o SYM) >> simp[]) >>
  `contract_storage q = contract_storage s /\ contract_transient q = contract_transient s` by
    simp[contract_storage_def, contract_transient_def] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    (drule_at (Pat `compile_expr _ _ _ _ = _`) (cj 1 compiler_compile_var) >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!id x sz. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var x) sz) ==>
             lookup_var x q = lookup_var x s` by
    (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `!id b sz. local_region ce ee.scopes q id b sz <=> local_region ce ee.scopes s id b sz` by
    (rpt gen_tac >> irule local_region_lookup_cong >> metis_tac[]) >>
  `eval_operand (vv_operand vv) q = eval_operand (vv_operand vv) s /\
   op_taint ta (vv_operand vv) = op_taint tn (vv_operand vv) /\
   op_prov Ga (vv_operand vv) = op_prov G (vv_operand vv)` by
    (Cases_on `vv_operand vv` >> fs[eval_operand_def, op_taint_def, op_prov_def] >> metis_tac[]) >>
  `!i. i < s.vs_alloca_next ==> (i IN ta.t_mem <=> i IN tn.t_mem)` by simp[] >>
  `immutable_frame_mods func ce cx ee q` by
    (irule ifexp_alloc_immutable >> qexists `s` >> simp[] >>
     rpt gen_tac >> disch_tac >> irule ifexp_alloc_new_sites >>
     qexistsl [`buf`,`LENGTH k.cs_current_insts`,`k`,`n`,`p`,`q`,`raw`,`sm`] >> simp[]) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee q` by
    (qpat_assum `!H. stmt_state_rel H _ _ _ _ _ s ==> _` (drule_then ACCEPT_TAC)) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp q` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _ q`
       (mp_then Any ACCEPT_TAC stmt_state_rel_allocas_below_fmp)) >>
  suspend "transport"
QED

Resume ifexp_arm_result_alloc_mods[transport]:
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by metis_tac[] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es sa k s0 ee tv vv q /\
    ghost_inv_at_mods (DF H) lo d ce cx ee Ga ta q` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods H _ _ _ _ _ _ _ sm _ _ _ _ s /\ _`
       (drule_then strip_assume_tac) >>
     `stmt_state_rel H ctx func ce cx ee s` by fs[vv_post_mods_def] >>
     conj_tac
     >- (`!id x sz w. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var x) sz) /\
                       lookup_var x s = SOME w ==> lookup_var x q = SOME w` by
           (rpt gen_tac >> strip_tac >>
            qpat_assum `!id x sz. FLOOKUP ce.ce_vars id = _ ==> _`
              (drule_then (fn th => rewrite_tac[th])) >> first_assum ACCEPT_TAC) >>
         `!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s` by
           (gen_tac >> disch_tac >>
            qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sm x` (drule_then assume_tac) >>
            qpat_assum `!x. not_fresh_at sm x ==> _ /\ _` (drule_then strip_assume_tac) >>
            first_assum ACCEPT_TAC) >>
         qpat_x_assum `q = raw with vs_inst_idx := _` kall_tac >>
         irule ifexp_alloc_post >> simp[] >> qexistsl [`s`,`sm`] >> simp[] >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
     irule (INST_TYPE [alpha |-> ``:256``] ifexp_alloc_ghost) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`G`,`H`,`ctx`,`func`,`s`,`sm`,`w2n w + n`,`tn`] >> asm_rewrite_tac[] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!x. vv_operand vv = Var x ==> FLOOKUP Ga x = FLOOKUP G x` by metis_tac[] >>
  `ptr_vv_ok cx (post_value_type ce e) tv vv ee Ga ta q` by
    (irule ifexp_alloc_ptr >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`G`,`lowered_value_type ce e`,`s`,`tn`] >> asm_rewrite_tac[] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv q` by
    (irule vv_store_bound_frame_mem_src >> qexists `s` >> asm_rewrite_tac[]) >>
  `vv_own ce cx (post_value_type ce e) sa sm ee tv vv s ==>
   vv_own ce cx (post_value_type ce e) sa k ee tv vv q` by
    (strip_tac >> irule vv_own_alloc_mono_frame >> qexistsl [`s`,`sm`] >>
     asm_rewrite_tac[] >> simp[]) >>
  suspend "resources"
QED

Resume ifexp_arm_result_alloc_mods[resources]:
  `ptr_buf_ok ce e (vv_operand vv) G s ==> ptr_buf_ok ce e (vv_operand vv) Ga q` by
    (qpat_x_assum `Ga = step_prov _ _ _ _` kall_tac >>
     rewrite_tac[ptr_buf_ok_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
     qpat_assum `!w. eval_operand (vv_operand vv) s = SOME w /\ _ ==> ?x b sz. _`
       (qspec_then `w'` mp_tac) >>
     (impl_tac >-
       (qpat_assum `eval_operand _ q = eval_operand _ s` (SUBST1_TAC o SYM) >>
        conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (qx_choosel_then [`x`,`b`,`sz`] strip_assume_tac) >>
     qexistsl [`x`,`b`,`sz`] >> asm_rewrite_tac[] >>
     qpat_assum `!x. vv_operand vv = Var x ==> _`
       (drule_then (fn th => rewrite_tac[th])) >> first_assum ACCEPT_TAC) >>
  `!ty' op. vv = StackValue ty' op /\ ~is_word_type (post_value_type ce e) ==>
      ptr_buf_ok ce e op Ga q` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `ptr_buf_ok _ _ _ G s ==> _` mp_tac >>
     qpat_assum `vv = _` (fn th => rewrite_tac[th,vv_operand_def]) >>
     disch_then irule >>
     qpat_assum `!ty' op. _ /\ ~is_word_type _ ==> ptr_buf_ok _ _ _ G s`
       (drule_all_then ACCEPT_TAC)) >>
  `!ty' pp. vv = LocatedValue ty' pp /\ pp.ptr_location = LocMemory ==>
      ptr_buf_ok ce e pp.ptr_operand Ga q` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `ptr_buf_ok _ _ _ G s ==> _` mp_tac >>
     qpat_assum `vv = _` (fn th => rewrite_tac[th,vv_operand_def]) >>
     disch_then irule >>
     qpat_assum `!ty' pp. _ /\ pp.ptr_location = LocMemory ==> ptr_buf_ok _ _ _ G s`
       (drule_all_then ACCEPT_TAC)) >>
  `ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?v. read_result cx tv ee = (INL v,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
             eval_operand (vv_operand vv) q = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside ta.t_mem q.vs_memory mem ==>
               val_in_memory rt v (w2n w) mem)` by
    (match_mp_tac (Q.INST [`s` |-> `s`,`tn` |-> `tn`] ifexp_alloc_ctor_code) >>
     asm_rewrite_tac[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl [`p`,`w`,`q`,`Ga`,`ta`,`raw`] >> asm_rewrite_tac[]
QED

Finalise ifexp_arm_result_alloc_mods
