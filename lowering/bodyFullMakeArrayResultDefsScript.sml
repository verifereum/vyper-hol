(* A pointwise interface between MakeArray execution and its full vv post.
   No execution is postulated here: the certificate records the allocation and
   loop endpoint, and packaging_ok is an obligation for a separate proof. *)
Theory bodyFullMakeArrayResultDefs
Ancestors
  bodySimFull exprSimHypsDefs exprSimDefs loweringPosts bodyPtrDefs
  compileEnv context valueEncoding vyperInterpreter vyperState venomState
  venomInst fragExec exprLowering

val _ = Parse.hide "base";

Definition make_array_completed_def:
  make_array_completed (H : (bool # 256 word # type_value) list # num list)
    D lo d ctx func ce cx env e es sa sm sb s0 si
    G0 tn0 ee v tv base cap q G tn t gs <=>
    (?ann elem bnd args. e = Builtin ann (MakeArray elem bnd) args) /\
    expr_body_pre ce cx env e es /\
    eval_expr cx e (es with gas_obs := gs) = (INL (Value v),ee) /\
    lowered_value_type ce e = expr_type e /\
    ~is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    cap = type_memory_bytes ce (expr_type e) /\
    cap = type_memory_size tv /\
    (!m. mem_agree_outside tn.t_mem t.vs_memory m ==>
         val_in_memory tv v base m) /\
    ci_mono sa sm /\ ci_mono sm sb /\
    sa.cs_next_id < sm.cs_next_id /\ local_ptrs_reserved ce sm /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w cap)] [q]) (fn_insts func) /\
    si.vs_memory = s0.vs_memory /\
    (!name b n. local_region ce es.scopes si name b n <=>
                local_region ce es.scopes s0 name b n) /\
    FLOOKUP si.vs_allocas sa.cs_next_id = SOME (base,cap) /\
    base + cap < dimword (:256) /\
    (?events. ee.storage_trace = es.storage_trace ++ events) /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (base,cap) /\
    lookup_var q t = SOME (n2w base) /\
    ptr_covers G tn q t cap /\ not_fresh_at sb q /\
    base + cap <= t.vs_alloca_next /\
    (!name b n. local_region ce ee.scopes t name b n ==>
      loweringStateRelDefs$regions_disjoint base cap b n) /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    wb_frame ce es ee sa s0 t /\
    ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
    return_buf_frame d ce sb t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    stmt_state_rel H ctx func ce cx ee t /\
    storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at D lo d ce cx ee G tn t /\
    (~expr_has_effect e ==>
      (!name b n. local_region ce es.scopes si name b n ==>
        mem_bytes_at b n t.vs_memory = mem_bytes_at b n si.vs_memory) /\
      (!p n. (p+n <= base \/ base+cap <= p) /\
        (!inst b sz. MEM inst (fn_insts func) /\
          inst.inst_opcode = ALLOCA /\ sm.cs_next_id <= inst.inst_id /\
          FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==>
          loweringStateRelDefs$regions_disjoint p n b sz) ==>
        mem_bytes_at p n t.vs_memory = mem_bytes_at p n si.vs_memory))
End

(* Closed and deliberately unproved here. The result proof discharges this
   universal implication; the two runtime branches may consume it meanwhile. *)
Definition make_array_packaging_ok_def:
  make_array_packaging_ok <=>
  !H D lo d ctx func ce cx env e es sa sm sb s0 si G0 tn0 ee v tv base cap q G tn t gs.
    make_array_completed H D lo d ctx func ce cx env e es sa sm sb s0 si
      G0 tn0 ee v tv base cap q G tn t gs ==>
    (?raw. raw = Value v /\
      vv_post H ctx func ce cx e es sa sb s0 ee raw
        (LocatedValue (expr_type e) (mk_ptr (Var q) LocMemory)) t /\
      vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e)
        ee raw (LocatedValue (expr_type e) (mk_ptr (Var q) LocMemory)) t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at D lo d ce cx ee G tn t /\
      ptr_vv_ok cx (post_value_type ce e) raw
        (LocatedValue (expr_type e) (mk_ptr (Var q) LocMemory)) ee G tn t /\
      (ce.ce_is_ctor /\
        vv_location (LocatedValue (expr_type e) (mk_ptr (Var q) LocMemory)) = SOME LocCode ==>
        ?val. read_result cx raw ee = (INL val,ee) /\
          !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
            eval_operand (vv_operand (LocatedValue (expr_type e) (mk_ptr (Var q) LocMemory))) t = SOME w ==>
            w2n w + type_memory_size rt <= lo /\
            (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
              val_in_memory rt val (w2n w) mem)) /\
      (!t' op. LocatedValue (expr_type e) (mk_ptr (Var q) LocMemory) = StackValue t' op /\
        ~is_word_type (post_value_type ce e) ==> ptr_buf_ok ce e op G t) /\
      (!t' p. LocatedValue (expr_type e) (mk_ptr (Var q) LocMemory) = LocatedValue t' p /\
        p.ptr_location = LocMemory ==> ptr_buf_ok ce e p.ptr_operand G t) /\
      ghost_kept_at lo ce es sa G0 tn0 s0 G tn)
End

Theorem make_array_completed_endpoint:
  make_array_completed H D lo d ctx func ce cx env e es sa sm sb s0 si
    G0 tn0 ee v tv base cap q G tn t gs ==>
  stmt_state_rel H ctx func ce cx ee t /\
  ghost_inv_at D lo d ce cx ee G tn t /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ptr_covers G tn q t cap
Proof
  simp[make_array_completed_def]
QED

(* Interface probes: the same endpoint packet covers both zero-offset layouts
   and the dynamic-array length word followed by its 32-byte-offset payload. *)
Theorem make_array_completed_tuple_probe[local]:
  make_array_completed H D lo d ctx func ce cx env
    (Builtin ann (MakeArray NONE bnd) args) es sa sm sb s0 si
    G0 tn0 ee (ArrayV (TupleV vs)) (TupleTV tvs) base cap q G tn t gs ==>
  (!m. mem_agree_outside tn.t_mem t.vs_memory m ==>
       tuple_in_memory vs tvs (base + 0) m) /\
  ptr_covers G tn q t cap
Proof
  simp[make_array_completed_def,valueEncodingDefsTheory.val_in_memory_def]
QED

Theorem make_array_completed_static_probe[local]:
  make_array_completed H D lo d ctx func ce cx env
    (Builtin ann (MakeArray (SOME et) (Fixed n)) args) es sa sm sb s0 si
    G0 tn0 ee (ArrayV (SArrayV kvs)) (ArrayTV tv (Fixed n))
    base cap q G tn t gs ==>
  (!m. mem_agree_outside tn.t_mem t.vs_memory m ==>
       kvs_in_memory kvs (base + 0) tv m) /\
  ptr_covers G tn q t cap
Proof
  simp[make_array_completed_def,valueEncodingDefsTheory.val_in_memory_def]
QED

Theorem make_array_completed_dynamic_probe[local]:
  make_array_completed H D lo d ctx func ce cx env
    (Builtin ann (MakeArray (SOME et) (Dynamic n)) args) es sa sm sb s0 si
    G0 tn0 ee (ArrayV (DynArrayV vs)) (ArrayTV tv (Dynamic n))
    base cap q G tn t gs ==>
  (!m. mem_agree_outside tn.t_mem t.vs_memory m ==>
       mem_word_at base m = n2w (LENGTH vs) /\
       elems_in_memory vs (base + 32) tv m) /\
  ptr_covers G tn q t cap
Proof
  simp[make_array_completed_def,valueEncodingDefsTheory.val_in_memory_def]
QED
