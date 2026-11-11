(* Allocation frames for deferred and already staged arguments. *)
Theory bodyIntCallFamCallIntStageAllocation
Ancestors
  bodyIntCallFamCallIntCompletedEffect bodyIntCallFamCallIntStageEffect
  bodyIntCallWindowLanding exprSimCopy

val deferred = ``\fp ce e vv r b es s.
  ?a. vv_holds ce fp.jc_cx (post_value_type ce e) r vv es s /\
    vv_at ce fp.jc_cx (post_value_type ce e) a b es r vv s /\
    (post_value_type ce e <> expr_type e ==>
      vv_own ce fp.jc_cx (post_value_type ce e) a b es r vv s) /\
    vv_storage_live fp.jc_cx vv es s /\
    (!x. vv_operand vv = Var x ==> not_fresh_at b x) /\
    (post_value_type ce e <> NoneT /\
     ~is_word_type (post_value_type ce e) /\
     ~is_bytestring_type (post_value_type ce e) /\
     (case vv of StackValue _ _ => T
               | LocatedValue _ p => p.ptr_location = LocMemory) ==>
     !tv. evaluate_type (get_tenv fp.jc_cx) (post_value_type ce e) = SOME tv ==>
       ?w off len. eval_operand (vv_operand vv) s = SOME w /\
         off <= w2n w /\ w2n w + type_memory_size tv <= off + len /\
         off + len < dimword (:256) /\
         (fp.jc_lo <= off \/
          ?lb size. fp.jc_staged lb size /\ lb <= off /\
                      off + len <= lb + size))``;
val deferred_list = ``\fp ce ds vs rs b es s.
  LENGTH ds = LENGTH vs /\ LENGTH ds = LENGTH rs /\
  !i. i < LENGTH ds ==>
    ^deferred fp ce (EL i ds) (EL i vs) (EL i rs) b es s``;

val completed = ``\cx start current ty flag v op s.
  ?tv w. evaluate_type (get_tenv cx) ty = SOME tv /\
    eval_operand op s = SOME w /\
    (!x. op = Var x ==> not_fresh_at current x) /\
    (if flag then is_word_type ty /\ w = typed_val_to_w256 tv v
     else val_in_memory tv v (w2n w) s.vs_memory /\
       ?aid len. FLOOKUP s.vs_allocas aid = SOME (w2n w,len) /\
         start.cs_next_id <= aid /\ aid < current.cs_next_id /\
         type_memory_size tv <= len /\
         w2n w + len <= s.vs_alloca_next /\
         w2n w + len < dimword (:256))``;
val completed_prefix = ``\cx start current tys flags values ops s.
  LENGTH flags = LENGTH tys /\ LENGTH values = LENGTH tys /\
  LENGTH ops = LENGTH tys /\
  !i. i < LENGTH tys ==>
    ^completed cx start current (EL i tys) (EL i flags)
      (EL i values) (EL i ops) s``;

(* Memory identity, unlike a store frame, needs no value well-formedness. *)
Theorem intcall_completed_memory_identity:
  ^completed_prefix cx start sa tys flags values ops s /\
  sa.cs_next_id <= sb.cs_next_id /\ sa.cs_next_var <= sb.cs_next_var /\
  (!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
    eval_operand op u = eval_operand op s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP u.vs_allocas aid = SOME entry) /\
  s.vs_alloca_next <= u.vs_alloca_next /\ u.vs_memory = s.vs_memory ==>
  ^completed_prefix cx start sb tys flags values ops u
Proof
  BETA_TAC >> strip_tac >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  `eval_operand (EL i ops) u = eval_operand (EL i ops) s` by
    metis_tac[] >>
  qexistsl_tac [`tv`, `w`] >> simp[] >>
  conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  Cases_on `EL i flags` >> gvs[] >>
  qexistsl_tac [`aid`, `len`] >> simp[]
QED

Theorem intcall_deferred_memory_identity:
  ^deferred_list fp ce ds vs rs sa es s /\
  sa.cs_next_id <= sb.cs_next_id /\ sa.cs_next_var <= sb.cs_next_var /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es u /\
  local_ptrs_reserved ce sa /\
  (!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
    eval_operand op u = eval_operand op s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP u.vs_allocas aid = SOME entry) /\ u.vs_memory = s.vs_memory ==>
  ^deferred_list fp ce ds vs rs sb es u
Proof
  BETA_TAC >> strip_tac >>
  irule (BETA_RULE bodyIntCallFamCallIntTransportTheory.intcall_deferred_list_endpoint) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  reverse conj_tac >- (first_assum ACCEPT_TAC) >>
  qexistsl_tac [`sa`, `s`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> irule copy_buffer_local_region_frame >>
      qexists_tac `sa` >> simp[] >>
      rpt strip_tac >>
      qpat_x_assum `!op. _ ==> eval_operand op u = _`
        (qspec_then `Var x` mp_tac) >>
      simp[venomStateTheory.eval_operand_def]) >>
  conj_tac
  >- metis_tac[] >>
  rpt strip_tac >> Cases_on `EL i vs` >> simp[]
QED

Theorem intcall_stage_allocation_landing:
  compile_alloc_buffer sz sa = (buf,sb) /\
  fn_has_code sa sb func /\ stmt_state_rel ctx func ce cx es s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  sz < dimword (:256) /\ allocas_above lo s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u w. gas_marked_path F ctx func s 0 (OK u) /\
    stmt_state_rel ctx func ce cx es u /\
    eval_operand buf.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    lo <= w2n w /\ w2n w + sz < dimword (:256) /\
    allocas_above lo u /\ u.vs_memory = s.vs_memory /\
    s.vs_alloca_next <= u.vs_alloca_next /\
    sa.cs_next_id < sb.cs_next_id /\ sa.cs_next_var <= sb.cs_next_var /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
      eval_operand op u = eval_operand op s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!name b len. local_region ce es.scopes u name b len <=>
                  local_region ce es.scopes s name b len) /\
    (!name b len. local_region ce es.scopes s name b len ==>
       regions_disjoint (w2n w) sz b len) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sb p) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  mp_tac (Q.INST [`reserved` |-> `\q. !x. q = Var x ==> not_fresh_at sa x`, `sm` |-> `sb`]
    (SPEC_ALL bodyIntCallWindowLandingTheory.materialization_alloc_landing)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `!name b len. local_region ce es.scopes u name b len <=>
                local_region ce es.scopes s name b len` by
    (rpt strip_tac >> irule copy_buffer_local_region_frame >> metis_tac[]) >>
  `sa.cs_next_id < sb.cs_next_id /\ sa.cs_next_var <= sb.cs_next_var` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
       compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.comp_return_def,
       compileEnvTheory.fresh_id_def, compileEnvTheory.fresh_var_def,
       compileEnvTheory.emit_def] >> strip_tac >> gvs[]) >>
  qexistsl_tac [`u`, `w`] >> simp[] >> metis_tac[]
QED

(* Allocation-id separation also covers reuse of the new staging site. *)
Theorem intcall_stage_allocation_old_window:
  stmt_state_rel ctx func ce cx es u /\
  FLOOKUP u.vs_allocas site = SOME (dst,sz) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP u.vs_allocas aid = SOME entry) /\
  FLOOKUP s.vs_allocas aid = SOME (lb,len) /\ aid < site /\
  lb <= p /\ p+k <= lb+len ==>
  regions_disjoint p k dst sz
Proof
  strip_tac >>
  `FLOOKUP u.vs_allocas aid = SOME (lb,len)` by metis_tac[] >>
  `aid <> site` by decide_tac >>
  `regions_disjoint lb len dst sz` by
    (irule exprSimPrecompilesTheory.state_allocations_disjoint >> metis_tac[]) >>
  fs[compileEnvTheory.regions_disjoint_def] >> decide_tac
QED

Theorem intcall_stage_allocation_protected_window:
  allocas_above lo u /\ FLOOKUP u.vs_allocas site = SOME (dst,sz) /\
  p+k <= lo ==> regions_disjoint p k dst sz
Proof
  simp[intCallFrameTheory.allocas_above_def,
       compileEnvTheory.regions_disjoint_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem intcall_stage_allocation_immutable_window:
  compile_alloc_buffer sz sa = (buf,sb) /\ fn_has_code sa sb func /\
  stmt_state_rel ctx func ce cx es u /\
  FLOOKUP u.vs_allocas sa.cs_next_id = SOME (dst,sz) /\ ce.ce_is_ctor /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
  FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
  regions_disjoint off (type_memory_size tv) dst sz
Proof
  strip_tac >> drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  drule exprSimPrecompilesTheory.precompile_alloca_immutable_disjoint >>
  disch_then drule >> simp[venomInstTheory.mk_inst_def] >>
  disch_then drule >> simp[] >>
  metis_tac[compileEnvTheory.regions_disjoint_def]
QED
