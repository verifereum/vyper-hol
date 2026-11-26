(* The formal-sized destination is allocated after the reached child vv.
   The silent allocation interval carries the same source endpoint forward. *)
Theory bodyIntCallBufferAllocVVMods
Ancestors
  bodyExtKeywordDefaultAllocMods bodyExtKeywordDefaultAllocResourcesMods
  bodyExtKeywordDefaultAllocCtorMods bodyExtKeywordDefaultUnwrapMods
  valueTypingMemoryProps exprSimMemDefs
  bodyPtrIfExpAllocCompiler abiBufferAllocationCode exprSimAlloc
  bodyFullPostsMods exprSimIfExpWidenedAdapter bodyPtrIfExpAllocSource
  bodyPtrBopRepresentationFrame revertReasonPrefixPtr logValueFramePtr
  exprSimWordArgs bodyMemoryDefs exprSimCopy bodyPtrDefs
  vyperStorageFootprint venomState venomInst finite_map words context ptrDiscipline freshWrites

Theorem intcall_alloc_word_ptr[local]:
  ptr_vv_ok cx ty raw vv ee G tn s /\ is_word_type ty /\
  stmt_state_rel H ctx func ce cx ee s /\ vv_at ce cx ty sa ci ee raw vv s /\
  read_result cx raw ee = (INL v,ee) /\ evaluate_type (get_tenv cx) ty = SOME pt /\
  val_wf pt v /\
  eval_operand (vv_operand vv) a = eval_operand (vv_operand vv) s /\
  op_prov Ga (vv_operand vv) = op_prov G (vv_operand vv) /\
  op_taint ta (vv_operand vv) = op_taint tn (vv_operand vv) /\
  a.vs_memory = s.vs_memory /\ a.vs_accounts = s.vs_accounts /\
  a.vs_transient = s.vs_transient /\ a.vs_call_ctx = s.vs_call_ctx /\
  ta.t_stor = tn.t_stor /\ ta.t_trans = tn.t_trans /\
  (!i. i < s.vs_alloca_next ==> (i IN ta.t_mem <=> i IN tn.t_mem)) ==>
  ptr_vv_ok cx ty raw vv ee Ga ta a
Proof
  Cases_on `vv` >- (simp[ptr_vv_ok_def,ptr_val_ok_def,vv_operand_def] >> metis_tac[]) >>
  rename1 `LocatedValue tag p` >> simp[vv_operand_def] >> strip_tac >>
  Cases_on `p.ptr_location <> LocMemory`
  >- (irule ptr_vv_ok_nonmemory_frame >> conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl [`G`,`s`,`tn`] >> simp[]) >>
  fs[] >>
  `!w. eval_operand p.ptr_operand s = SOME w ==>
      val_wf pt v /\ (!i. w2n w <= i /\ i < w2n w + val_footprint pt v ==>
                            i < s.vs_alloca_next)` by
    (rpt strip_tac >> drule_all located_vv_at_memory_footprint >> simp[]) >>
  fs[ptr_vv_ok_def] >>
  irule bop_ptr_mem_ok_frame >> qexistsl [`G`,`s`,`tn`,`pt`] >>
  simp[] >> conj_tac >- (Cases_on `p.ptr_operand` >> fs[op_prov_def]) >>
  metis_tac[]
QED

fun accept_alloc_payload th =
  qpat_assum `read_result cx raw ee = _` (fn read_eq =>
    qpat_assum `evaluate_type (get_tenv cx) (post_value_type ce e) = _`
      (fn type_eq => ACCEPT_TAC (PURE_REWRITE_RULE [read_eq,type_eq] th)))

Theorem intcall_buffer_alloc_vv_mods:
  let cap = MAX 32 (type_memory_bytes ce dty) in
  compile_alloc_buffer cap ci = (buf,ca) /\ fn_has_code ci ca func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce ci /\ cap < dimword (:256) /\
  sa.cs_next_var <= ci.cs_next_var /\
  (!x. vv_operand vv = Var x ==> not_fresh_at ci x) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post_mods H ctx func ce cx e es sa ci s0 ee raw vv s /\
     ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  stmt_state_rel (H0:(bool # bytes32 # type_value) list # num list) ctx func ce cx es s0 /\
  ghost_kept_at lo ce es sa Gi ti s0 G tn /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d ce ci s /\ alloca_history func s /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = ci.cs_current_bb /\
  s.vs_inst_idx = LENGTH ci.cs_current_insts /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME pt /\ value_has_type pt v /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee raw vv s /\
  ptr_vv_ok cx (post_value_type ce e) raw vv ee G tn s /\
  (!tag x. vv = StackValue tag x ==> ptr_buf_ok ce e x G s) /\
  (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
     ptr_buf_ok ce e p.ptr_operand G s) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?a. read_result cx raw ee = (INL a,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
             eval_operand (vv_operand vv) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rt a (w2n w) mem)) ==>
  ?dst base a Ga ta.
    buf.buf_operand = Var dst /\ not_fresh_at ca dst /\
    not_local_ptr ce ee.scopes dst /\
    MEM (mk_inst ci.cs_next_id ALLOCA [Lit (n2w cap)] [dst]) (fn_insts func) /\
    ci.cs_next_id < ca.cs_next_id /\ ci.cs_next_var <= ca.cs_next_var /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
           (s,G,tn) [] (OK a,Ga,ta)) /\
    ~a.vs_halted /\ a.vs_current_bb = ca.cs_current_bb /\
    a.vs_inst_idx = LENGTH ca.cs_current_insts /\
    alloca_history func a /\ allocas_from lo a /\
    s.vs_alloca_next <= a.vs_alloca_next /\ s0.vs_alloca_next <= a.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp a) /\
    lookup_var dst a = SOME (n2w base) /\ op_taint ta (Var dst) = {} /\
    ptr_covers Ga ta dst a cap /\ FLOOKUP Ga dst = SOME (base,cap) /\
    FLOOKUP a.vs_allocas ci.cs_next_id = SOME (base,cap) /\
    lo <= base /\ base + cap < dimword (:256) /\ base + cap <= a.vs_alloca_next /\
    (!aid b len. aid < ci.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint base cap b len) /\
    (!name b len. local_region ce ee.scopes a name b len ==> regions_disjoint base cap b len) /\
    (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==> FLOOKUP a.vs_allocas aid = SOME row) /\
    (!x. not_fresh_at ci x ==> lookup_var x a = lookup_var x s /\
      FLOOKUP Ga x = FLOOKUP G x /\ op_taint ta (Var x) = op_taint tn (Var x)) /\
    (!id b len. local_region ce ee.scopes a id b len <=> local_region ce ee.scopes s id b len) /\
    a.vs_memory = s.vs_memory /\ a.vs_labels = s.vs_labels /\
    ta.t_stor = tn.t_stor /\ ta.t_trans = tn.t_trans /\ ta.t_imm = tn.t_imm /\
    (!i. i < s.vs_alloca_next ==> (i IN ta.t_mem <=> i IN tn.t_mem)) /\
    eval_operand (vv_operand vv) a = eval_operand (vv_operand vv) s /\
    op_prov Ga (vv_operand vv) = op_prov G (vv_operand vv) /\
    op_taint ta (vv_operand vv) = op_taint tn (vv_operand vv) /\
    return_buf_frame d ce ca a /\ wb_frame ce ee ee ci s a /\
    ghost_kept_at lo ce es sa Gi ti s0 Ga ta /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       vv_post_mods H ctx func ce cx e es sa ca s0 ee raw vv a /\
       ghost_inv_at_mods (DF H) lo d ce cx ee Ga ta a) /\
    vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee raw vv a /\
    ptr_vv_ok cx (post_value_type ce e) raw vv ee Ga ta a /\
    (!tag x. vv = StackValue tag x ==> ptr_buf_ok ce e x Ga a) /\
    (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
       ptr_buf_ok ce e p.ptr_operand Ga a) /\
    (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
      ?a'. read_result cx raw ee = (INL a',ee) /\
        !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
               eval_operand (vv_operand vv) a = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside ta.t_mem a.vs_memory mem ==>
            val_in_memory rt a' (w2n w) mem))
Proof
  simp_tac bool_ss [LET_THM] >>
  qabbrev_tac `cap = MAX 32 (type_memory_bytes ce dty)` >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ext_kw_default_alloc_mods >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`dst`,`w`,`a`,`Ga`,`ta`] (map_every assume_tac o CONJUNCTS))) >>
  `not_local_ptr ce ee.scopes dst` by
    (drule_at (Pat `compile_alloc_buffer _ _ = _`) (cj 1 compile_alloc_buffer_frame_separation) >>
     disch_then irule >> conj_tac >- first_assum ACCEPT_TAC >>
     qexists `ci` >> simp[] >> metis_tac[not_fresh_at_mono]) >>
  `ci.cs_next_id < ca.cs_next_id /\ ci.cs_next_var <= ca.cs_next_var /\
   MEM (mk_inst ci.cs_next_id ALLOCA [Lit (n2w cap)] [dst]) (fn_insts func)` by
    (drule_then strip_assume_tac compile_alloc_buffer_code >>
     drule_all_then assume_tac buffer_alloc_code >>
     `dst = STRING #"%" (toString ci.cs_next_var)` by metis_tac[operand_11] >> simp[]) >>
  `a.vs_labels = s.vs_labels /\ a.vs_accounts = s.vs_accounts /\
   a.vs_transient = s.vs_transient /\ a.vs_call_ctx = s.vs_call_ctx` by
    (qpat_assum `a with <|vs_vars := _; vs_allocas := _;
        vs_alloca_next := _; vs_inst_idx := _|> = s` (SUBST1_TAC o SYM) >> simp[]) >>
  `!id b len. local_region ce ee.scopes a id b len <=> local_region ce ee.scopes s id b len` by
    (rpt gen_tac >> irule copy_buffer_local_region_frame >> qexists `ci` >> simp[]) >>
  `lo <= w2n w` by (qpat_assum `allocas_from lo a` (mp_tac o REWRITE_RULE [allocas_from_def]) >>
    disch_then drule >> simp[]) >>
  `op_taint ta (Var dst) = {}` by fs[ptr_covers_def] >>
  `return_buf_frame d ce ca a` by
    (drule return_buf_frame_frame >> disch_then irule >> simp[]) >>
  `wb_frame ce ee ee ci s a` by
    (irule wb_frame_readonly_tail >> qexistsl [`ci`,`s`] >> simp[wb_frame_refl]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       vv_post_mods H ctx func ce cx e es sa ca s0 ee raw vv a /\
       ghost_inv_at_mods (DF H) lo d ce cx ee Ga ta a` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ a /\ _`
       (drule_then strip_assume_tac) >>
     conj_tac >- (irule default_unwrap_vv_cursor >> qexists `ci` >> simp[] >> decide_tac) >>
     first_assum ACCEPT_TAC) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ s /\ _`
    (drule_then strip_assume_tac) >>
  qexistsl [`dst`,`w2n w`,`a`,`Ga`,`ta`] >>
  pure_rewrite_tac[n2w_w2n] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >> suspend "resources"
QED

Resume intcall_buffer_alloc_vv_mods[resources]:
  ASM_CASES_TAC ``is_word_type (post_value_type ce e)``
  >- suspend "word" >>
  drule_all_then strip_assume_tac
    (Q.INST [`u` |-> `a`] ext_kw_default_alloc_unwrap_resources_mods) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `_ ==> ?payload. _ /\ !rt w. _ /\ eval_operand _ a = _ ==> _`
    accept_alloc_payload
QED

Resume intcall_buffer_alloc_vv_mods[word]:
  qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ s`
    (strip_assume_tac o REWRITE_RULE[vv_post_mods_def]) >>
  drule_then assume_tac value_has_type_memory_wf >>
  conj_tac >- drule_all_then ACCEPT_TAC vv_store_bound_frame_mem_src >>
  conj_tac >- drule_all_then ACCEPT_TAC intcall_alloc_word_ptr >>
  `(ptr_buf_ok ce e (vv_operand vv) G s ==>
    ptr_buf_ok ce e (vv_operand vv) Ga a)` by
    (strip_tac >> irule ptr_buf_ok_frame >> qexistsl [`G`,`s`] >> simp[] >>
     Cases_on `vv_operand vv` >> fs[op_prov_def]) >>
  conj_tac >- (rpt gen_tac >> strip_tac >> fs[vv_operand_def]) >>
  conj_tac >- (rpt gen_tac >> strip_tac >> fs[vv_operand_def]) >>
  mp_tac (Q.INST [`ce` |-> `ce`, `vv` |-> `vv`, `cx` |-> `cx`,
                  `tv` |-> `raw`, `ee` |-> `ee`, `e` |-> `e`,
                  `s` |-> `s`, `tn` |-> `tn`, `u` |-> `a`, `ta` |-> `ta`,
                  `lo` |-> `lo`, `v` |-> `v`, `pt` |-> `pt`]
    ext_kw_default_alloc_ctor_payload_mods) >>
  impl_tac
  >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then accept_alloc_payload
QED

Finalise intcall_buffer_alloc_vv_mods
