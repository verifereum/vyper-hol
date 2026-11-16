(* A fixed successful Args endpoint is allocated and staged once. *)
Theory bodyFullAbiEncodeTuplePrepared
Ancestors
  bodyFullAbiEncodeTupleAlloc bodyFullAbiEncodeTupleZero bodyFullAbiEncodeArgs
  bodyFullPathHistory exprSimAbiEncodeArgsSeparation abiEncodeEndpointMetadata
  valueEncodingTyping abiBuiltinAllocation abiTupleEncodePrepare
  emitHelperProps loweringShapeDefs abiArgsLabelBoundary
  finite_map words list arithmetic

Theorem abi_encode_args_tuple_prepared:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es /\
  ~(LENGTH args = 1 /\ ~ensure) /\
  abi_args_post H0 ctx func ce cx es origin st s0 ee args ops vs initial /\
  LENGTH tvs = LENGTH args /\
  (!i. i < LENGTH args ==>
    evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME (EL i tvs) /\
    value_has_type (EL i tvs) (EL i vs) /\
    type_memory_bytes ce (lowered_value_type ce (EL i args)) = type_memory_size (EL i tvs) /\
    type_memory_size (EL i tvs) < 2**64 /\
    (is_word_type (lowered_value_type ce (EL i args)) ==>
      abi_tuple_input ce (lowered_value_type ce (EL i args)) (EL i tvs) (EL i vs) (EL i ops) initial /\
      op_taint tn (EL i ops) = {}) /\
    (~is_word_type (lowered_value_type ce (EL i args)) /\ 0 < type_memory_size (EL i tvs) ==>
      abi_tuple_input ce (lowered_value_type ce (EL i args)) (EL i tvs) (EL i vs) (EL i ops) initial /\
      ?x w. EL i ops = Var x /\ lookup_var x initial = SOME w /\
        ptr_covers G tn x initial (type_memory_size (EL i tvs)) /\
        w2n w + type_memory_size (EL i tvs) < dimword(:256) /\
        w2n w + type_memory_size (EL i tvs) <= initial.vs_alloca_next /\
        (!mem. mem_agree_outside tn.t_mem initial.vs_memory mem ==>
          val_in_memory (EL i tvs) (EL i vs) (w2n w) mem))) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  EVERY (\op. !x. op = Var x ==> not_fresh_at st x) ops /\
  alloca_history func initial /\ allocas_from lo initial /\ lo <= initial.vs_alloca_next /\
  local_ptrs_reserved ce origin /\ local_ptrs_reserved ce st /\
  origin.cs_next_var <= st.cs_next_var /\ origin.cs_next_id <= st.cs_next_id /\
  ~ctx_has_dalloca ctx /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  n = abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args)) /\
  compile_alloc_buffer n st = (buf,allocated) /\
  compile_store_abi_tuple ce buf.buf_operand 0
    (ZIP (ops,MAP (lowered_value_type ce) args)) allocated = ((),staged) /\
  fn_has_code st allocated func /\ fn_has_code allocated staged func /\
  fn_inst_ids_distinct func ==>
  ?root bw prepared Gp tnp.
    buf.buf_operand = Var root /\ not_fresh_at staged root /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (initial,G,tn) [] (OK prepared,Gp,tnp)) /\
    (!mem. mem_agree_outside tnp.t_mem prepared.vs_memory mem ==>
      val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) (w2n bw) mem) /\
    lookup_var root prepared = SOME bw /\ ptr_covers Gp tnp root prepared n /\
    w2n bw + n < dimword(:256) /\ lo <= w2n bw /\
    w2n bw + n <= prepared.vs_alloca_next /\
    ~prepared.vs_halted /\ prepared.vs_current_bb = staged.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH staged.cs_current_insts /\
    prepared.vs_allocas = (abi_builtin_allocate_state st.cs_next_id n initial).vs_allocas /\
    prepared.vs_alloca_next = (abi_builtin_allocate_state st.cs_next_id n initial).vs_alloca_next /\
    alloca_history func prepared /\ allocas_from lo prepared /\
    lo <= prepared.vs_alloca_next /\ initial.vs_alloca_next <= prepared.vs_alloca_next /\
    local_ptrs_rel func ce ee.scopes prepared /\
    (!name z k. local_region ce es.scopes s0 name z k ==>
      regions_disjoint (w2n bw) n z k) /\
    (!name z k. local_region ce ee.scopes initial name z k ==>
      regions_disjoint (w2n bw) n z k) /\
    (!aid z k. FLOOKUP s0.vs_allocas aid = SOME (z,k) /\ aid < origin.cs_next_id ==>
      regions_disjoint (w2n bw) n z k) /\
    (!D. ghost_inv_at D lo d ce cx ee G tn initial ==>
      ghost_inv_at D lo d ce cx ee Gp tnp prepared) /\
    (ghost_kept_at lo ce es origin G0 tn0 s0 G tn ==>
      ghost_kept_at lo ce es origin G0 tn0 s0 Gp tnp) /\
    tnp.t_stor = tn.t_stor /\ tnp.t_trans = tn.t_trans /\ tnp.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==> lookup_var x prepared = lookup_var x initial /\
      FLOOKUP Gp x = FLOOKUP G x /\ op_taint tnp (Var x) = op_taint tn (Var x)) /\
    (!oldop. (!x. oldop = Var x ==> not_fresh_at st x) ==>
      eval_operand oldop prepared = eval_operand oldop initial /\
      op_taint tnp oldop = op_taint tn oldop /\ op_prov Gp oldop = op_prov G oldop)
Proof
  strip_tac >> drule abi_args_post_lengths >> strip_tac >>
  `n < dimword(:256)` by
    (drule_all abi_encode_endpoint_staging_size >>
     simp[abi_tuple_bytes_def, type_memory_bytes_def, MAP_MAP_o,
       combinTheory.o_DEF, MAP_ZIP, dimword_def]) >>
  `stmt_state_rel H0 ctx func ce cx ee initial` by fs[abi_args_post_def] >>
  `!i. i < LENGTH (MAP (lowered_value_type ce) args) ==>
    val_wf (EL i tvs) (EL i vs) /\
    type_memory_size (EL i tvs) = type_memory_bytes ce (EL i (MAP (lowered_value_type ce) args)) /\
    type_memory_bytes ce (EL i (MAP (lowered_value_type ce) args)) < dimword(:256) /\
    (if ~is_word_type (EL i (MAP (lowered_value_type ce) args)) /\
      type_memory_bytes ce (EL i (MAP (lowered_value_type ce) args)) = 0 then T else
      abi_tuple_input ce (EL i (MAP (lowered_value_type ce) args)) (EL i tvs) (EL i vs) (EL i ops) initial /\
      (!x. EL i ops = Var x ==> not_fresh_at st x) /\
      (if is_word_type (EL i (MAP (lowered_value_type ce) args)) then op_taint tn (EL i ops) = {} else
        evaluate_type (get_tenv cx) (EL i (MAP (lowered_value_type ce) args)) = SOME (EL i tvs) /\
        expr_val_at ce cx (EL i (MAP (lowered_value_type ce) args)) origin st ee (EL i vs) (EL i ops) initial /\
        ?x w. EL i ops = Var x /\ lookup_var x initial = SOME w /\
          ptr_covers G tn x initial (type_memory_bytes ce (EL i (MAP (lowered_value_type ce) args))) /\
          w2n w + type_memory_bytes ce (EL i (MAP (lowered_value_type ce) args)) < dimword(:256) /\
          w2n w + type_memory_bytes ce (EL i (MAP (lowered_value_type ce) args)) <= initial.vs_alloca_next /\
          (!mem. mem_agree_outside tn.t_mem initial.vs_memory mem ==>
            val_in_memory (EL i tvs) (EL i vs) (w2n w) mem)))` by suspend "inputs" >>
  drule_all (INST_TYPE [``:'b`` |-> ``:'a``] abi_encode_tuple_allocate_origin) >>
  disch_then (qspecl_then [`tn`, `explicit`, `PG`, `G`, `d`] strip_assume_tac) >>
  FAIL_TAC "allocated tuple"
QED

Resume abi_encode_args_tuple_prepared[inputs]:
  simp[LENGTH_MAP, EL_MAP] >> rpt strip_tac >>
  qpat_assum `!i. i < LENGTH args ==> evaluate_type _ _ = _ /\ _`
    (drule_then strip_assume_tac) >>
  `val_wf (EL i tvs) (EL i vs)` by metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  `type_memory_size (EL i tvs) < dimword(:256)` by
    (fs[dimword_def] >> decide_tac) >>
  `!x. EL i ops = Var x ==> not_fresh_at st x` by
    (fs[EVERY_EL] >> metis_tac[]) >>
  `expr_val_at ce cx (lowered_value_type ce (EL i args)) origin st ee
      (EL i vs) (EL i ops) initial` by
    (irule abi_encode_args_value_at >> goal_assum (drule_at Any) >> simp[]) >>
  Cases_on `is_word_type (lowered_value_type ce (EL i args))` >> gvs[] >>
  Cases_on `type_memory_size (EL i tvs) = 0` >> gvs[]
QED
Finalise abi_encode_args_tuple_prepared
