(* Pending and completed certificates at the very same counted allocation endpoint. *)
Theory bodyIntCallFamCallIntAllocationCertificates
Ancestors
  bodyIntCallFamCallIntAllocationGeometry bodyIntCallFamCallIntStageAllocation

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

Theorem intcall_stage_allocation_certificates:
  compile_alloc_buffer sz sa = (buf,sb) /\
  fn_has_code sa sb fp.jc_func /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s /\
  fn_inst_ids_distinct fp.jc_func /\ local_ptrs_reserved ce sa /\
  sz < dimword (:256) /\ allocas_above fp.jc_lo s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ^deferred_list fp ce ds vs rs sa es s /\
  ^completed_prefix fp.jc_cx start sa tys flags values ops s ==>
  ?u w. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
    stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es u /\
    ^deferred_list fp ce ds vs rs sb es u /\
    ^completed_prefix fp.jc_cx start sb tys flags values ops u /\
    eval_operand buf.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    fp.jc_lo <= w2n w /\ w2n w + sz < dimword (:256) /\
    allocas_above fp.jc_lo u /\ u.vs_memory = s.vs_memory /\
    s.vs_alloca_next <= u.vs_alloca_next /\
    sa.cs_next_id < sb.cs_next_id /\ sa.cs_next_var <= sb.cs_next_var /\
    (!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
      eval_operand op u = eval_operand op s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!name lb len. local_region ce es.scopes u name lb len <=>
                  local_region ce es.scopes s name lb len) /\
    (!name lb len. local_region ce es.scopes s name lb len ==>
       regions_disjoint (w2n w) sz lb len) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sb p) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  BETA_TAC >> strip_tac >> drule_all intcall_stage_allocation_landing >> strip_tac >>
  `^deferred_list fp ce ds vs rs sb es u` by
    (BETA_TAC >> irule (BETA_RULE intcall_deferred_memory_identity) >>
     simp[] >> qexistsl_tac [`s`, `sa`] >> gvs[]) >>
  `^completed_prefix fp.jc_cx start sb tys flags values ops u` by
    (BETA_TAC >> irule (BETA_RULE intcall_completed_memory_identity) >>
     simp[] >> qexistsl_tac [`s`, `sa`] >> gvs[]) >>
  qexistsl_tac [`u`, `w`] >> gvs[] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
