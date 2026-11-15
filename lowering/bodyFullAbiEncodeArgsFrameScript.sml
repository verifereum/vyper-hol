(* Whole-list frames for retained ABI argument resources. *)
Theory bodyFullAbiEncodeArgsFrame
Ancestors
  bodyFullAbiEncodeRetention bodyFullAbiEncodeBorrowed abiEncodeArgsSim
  representationCleanPtr loweringPosts bodyPtrDefs arithmetic words
  assignTuplePtrCopyLen logValueFramePtr abiDecodeStaticProps allocaHistory
  ptrDiscipline venomExecSemantics venomState abiTupleProps

Theorem abi_encode_owned_args_frame:
  wb_frame ce es ee st s t /\
  ghost_kept_at lo ce es st G tn s G' tn' /\
  ghost_inv_at D lo d ce cx ee G' tn' t /\
  alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
  not_fresh_at st x /\ lookup_var x s = SOME w /\
  ptr_covers G tn x s capacity /\ val_wf tv value /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv value (w2n w) mem) /\
  FLOOKUP s.vs_allocas aid = SOME (rowbase,sz) /\ aid < st.cs_next_id /\
  rowbase <= w2n w /\ w2n w + val_footprint tv value <= rowbase + sz /\
  (!n b k. local_region ce es.scopes s n b k ==>
    rowbase + sz <= b \/ b + k <= rowbase) ==>
  lookup_var x t = SOME w /\
  ptr_covers G' tn' x t capacity /\
  (!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
    val_in_memory tv value (w2n w) mem) /\
  FLOOKUP t.vs_allocas aid = SOME (rowbase,sz) /\
  mem_bytes_at rowbase sz t.vs_memory = mem_bytes_at rowbase sz s.vs_memory /\
  allocas_from lo t /\ lo <= t.vs_alloca_next /\
  alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
  (w2n w + capacity <= s.vs_alloca_next ==> w2n w + capacity <= t.vs_alloca_next)
Proof
  strip_tac >>
  `lookup_var x t = SOME w /\
   FLOOKUP t.vs_allocas aid = SOME (rowbase,sz) /\
   mem_bytes_at rowbase sz t.vs_memory = mem_bytes_at rowbase sz s.vs_memory` by
    (fs[wb_frame_def] >> metis_tac[]) >>
  `FLOOKUP G' x = FLOOKUP G x /\
   op_taint tn' (Var x) = op_taint tn (Var x)` by
    (fs[ghost_kept_at_def] >> metis_tac[]) >>
  `ptr_covers G' tn' x t capacity` by
    (irule ptr_covers_lookup_frame >> qexistsl_tac [`G`, `s`, `tn`] >> simp[]) >>
  `mem_bytes_at (w2n w) (val_footprint tv value) t.vs_memory =
   mem_bytes_at (w2n w) (val_footprint tv value) s.vs_memory` by
    (irule mem_bytes_at_bytewise >> rpt strip_tac >>
     irule mem_bytes_at_eq_byte >> qexistsl_tac [`rowbase`, `sz`] >> simp[] >> decide_tac) >>
  `!i. w2n w <= i /\ i < w2n w + val_footprint tv value /\
       i IN tn'.t_mem ==> i IN tn.t_mem` by
    (fs[ghost_kept_at_def] >> rpt strip_tac >>
     qpat_x_assum `!a off k i. FLOOKUP s.vs_allocas a = SOME (off,k) /\ _ ==> _`
       (qspecl_then [`aid`, `rowbase`, `sz`, `i`] mp_tac) >>
     impl_tac >- (simp[] >> rpt strip_tac >> metis_tac[]) >> simp[]) >>
  `!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
     val_in_memory tv value (w2n w) mem` by
    (rpt strip_tac >> irule robust_val_in_memory_footprint_frame >>
     conj_tac >- simp[] >>
     qexistsl_tac [`s.vs_memory`, `t.vs_memory`, `tn.t_mem`, `tn'.t_mem`] >> simp[]) >>
  fs[ghost_inv_at_def] >> decide_tac
QED

Theorem abi_encode_borrowed_args_frame:
  expr_sim_inv ce cx env es /\
  stmt_state_rel (H0:(bool # bytes32 # type_value) list # num list) ctx func ce cx es s /\
  stmt_state_rel (H1:(bool # bytes32 # type_value) list # num list) ctx func ce cx ee t /\
  ee.scopes = es.scopes /\ local_ptrs_reserved ce st /\ wb_frame ce es ee st s t /\
  ghost_kept_at lo ce es st G tn s G' tn' /\ sb.cs_next_id <= st.cs_next_id /\
  (!x. op = Var x ==> not_fresh_at st x) /\ (!l. op <> Label l) /\
  expr_val_rel cx (lowered_value_type ce e) v op s /\
  expr_val_at ce cx (lowered_value_type ce e) sa sb es v op s /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  value_has_type tv v /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
  type_memory_size tv < 2**64 /\
  (is_word_type (lowered_value_type ce e) ==>
    abi_tuple_input ce (lowered_value_type ce e) tv v op s /\ op_taint tn op = {}) /\
  (~is_word_type (lowered_value_type ce e) /\ 0 < type_memory_size tv ==>
    abi_tuple_input ce (lowered_value_type ce e) tv v op s /\
    ?x w. op = Var x /\ lookup_var x s = SOME w /\
      ptr_covers G tn x s (type_memory_size tv) /\
      w2n w + type_memory_size tv < dimword(:256) /\
      w2n w + type_memory_size tv <= s.vs_alloca_next /\
      (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        val_in_memory tv v (w2n w) mem)) ==>
  expr_val_rel cx (lowered_value_type ce e) v op t /\
  expr_val_at ce cx (lowered_value_type ce e) sa sb ee v op t /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  value_has_type tv v /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
  type_memory_size tv < 2**64 /\
  (is_word_type (lowered_value_type ce e) ==>
    abi_tuple_input ce (lowered_value_type ce e) tv v op t /\ op_taint tn' op = {}) /\
  (~is_word_type (lowered_value_type ce e) /\ 0 < type_memory_size tv ==>
    abi_tuple_input ce (lowered_value_type ce e) tv v op t /\
    ?x w. op = Var x /\ lookup_var x t = SOME w /\
      ptr_covers G' tn' x t (type_memory_size tv) /\
      w2n w + type_memory_size tv < dimword(:256) /\
      w2n w + type_memory_size tv <= t.vs_alloca_next /\
      (!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
        val_in_memory tv v (w2n w) mem))
Proof
  strip_tac >>
  `eval_operand op s = eval_operand op t` by
    (Cases_on `eval_operand op s` >> gvs[expr_val_rel_def] >>
     metis_tac[abi_args_operand_kept]) >>
  `expr_val_rel cx (lowered_value_type ce e) v op t` by
    (irule abi_args_value_kept_eq >> metis_tac[]) >>
  `expr_val_at ce cx (lowered_value_type ce e) sa sb ee v op t` by
    (irule abi_args_location_kept_eq >> simp[] >> metis_tac[]) >>
  simp[] >> conj_tac
  >- (strip_tac >>
      `op_taint tn' op = op_taint tn op` by
        (Cases_on `op` >> gvs[ghost_kept_at_def, op_taint_def]) >>
      gvs[abiTuplePropsTheory.abi_tuple_input_def]) >>
  strip_tac >>
  `ptr_val_ok cx (lowered_value_type ce e) v op G tn s` by
    (`val_wf tv v` by gvs[abi_tuple_input_def] >>
     `val_store_size tv v <= type_memory_size tv` by
       metis_tac[exprSimPropsTheory.val_store_size_le] >>
     gvs[ptr_val_ok_def, ptr_mem_ok_def, ptr_covers_def, eval_operand_def] >>
     decide_tac) >>
  drule_all abi_encode_borrowed_operand_retained >> strip_tac >>
  gvs[] >>
  `lookup_var x t = SOME w` by gvs[eval_operand_def] >>
  `FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)` by
    (fs[ghost_kept_at_def] >> metis_tac[]) >>
  `ptr_covers G' tn' x t (type_memory_size tv)` by
    (irule ptr_covers_lookup_frame >> qexistsl_tac [`G`, `s`, `tn`] >> simp[]) >>
  `!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
    val_in_memory tv v (w2n w) mem` by
    (gvs[ptr_val_ok_def, ptr_mem_ok_def, eval_operand_def] >> metis_tac[]) >>
  `abi_tuple_input ce (lowered_value_type ce e) tv v (Var x) t` by
    (gvs[abi_tuple_input_def, eval_operand_def] >> metis_tac[mem_agree_outside_def]) >>
  simp[] >> qexists `w` >> simp[] >> decide_tac
QED
