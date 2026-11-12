(* Counted typed snapshot stores at the lowered annotation. *)
Theory bodyMemSnapshotStore
Ancestors
  bodyCopyMemory bodyMemAggregateStore exprSimBufferStore exprSimMemUnwrap
  valueCopyBytes exprSimProps exprSimMemDefs loweringPosts exprLoweringProps
  exprLowering context compileEnv valueEncodingProps fragGasPathMem
  venomState venomInst venomExecSemantics

Theorem snapshot_nonword_store_mem_ok[local]:
  compile_store_memory ce src dst ty ty sa = ((),sb) /\
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  val_in_memory tv v (w2n w) s.vs_memory /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  eval_operand src s = SOME w /\ eval_operand dst s = SOME d /\
  w2n w + type_memory_size tv <= s.vs_alloca_next /\
  w2n d + type_memory_size tv <= s.vs_alloca_next /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> Cases_on `is_bytestring_type ty`
  >- (drule_all buffer_typed_bytestring_header >> strip_tac >>
      `val_store_size tv v <= type_memory_size tv` by
        metis_tac[val_store_size_le] >>
      gvs[compile_store_memory_def] >>
      irule compile_store_bytestring_body_mem_ok >>
      qexistsl_tac [`d`, `dst`, `len`, `src`, `w`] >> simp[] >>
      metis_tac[]) >>
  gvs[compile_store_memory_def] >>
  irule compile_copy_memory_body_mem_ok >>
  qexistsl_tac [`d`, `dst`, `type_memory_size tv`, `src`, `w`] >> simp[]
QED

Theorem snapshot_nonword_store_path_mem[local]:
  compile_store_memory ce src dst ty ty sa = ((),sb) /\
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  val_in_memory tv v (w2n w) s.vs_memory /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  eval_operand src s = SOME w /\ eval_operand dst s = SOME d /\
  w2n w + type_memory_size tv <= s.vs_alloca_next /\
  w2n d + type_memory_size tv <= s.vs_alloca_next /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?z. gas_path_mem ctx func s 0 (OK z) /\
    val_in_memory tv v (w2n d) z.vs_memory /\
    (z with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s) /\
    (!a k. a + k <= w2n d \/ w2n d + type_memory_size tv <= a ==>
       mem_bytes_at a k z.vs_memory = mem_bytes_at a k s.vs_memory) /\
    alloca_history func z /\ ~z.vs_halted /\
    z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `expr_val_rel cx ty v src s` by simp[expr_val_rel_def] >>
  drule_all snapshot_nonword_store_mem_ok >> strip_tac >>
  drule_all buffer_store_memory_encoding >> strip_tac >>
  drule buffer_store_memory_shape >> strip_tac >>
  drule aggregate_store_memory_no_gas >> strip_tac >>
  drule_all straight_path_mem >> strip_tac >>
  qexists_tac `q with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[lookup_var_def] >>
  qpat_x_assum `_ with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
  simp[venom_state_component_equality] >>
  metis_tac[lookup_var_def, arithmeticTheory.ADD_COMM]
QED
