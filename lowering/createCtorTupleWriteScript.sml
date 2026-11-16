Theory createCtorTupleWrite
Ancestors
  placeMemoryPrimitiveForward valueCopy exprLowering context exprLoweringProps
  loweringPosts valueEncodingProps
  fragGasMode venomState venomMemDefs venomExecSemantics exprSimProps
  emitHelperProps immutableMemoryFrame arithmetic

Theorem ctor_physical_write_run[local]:
  (if is_word_type ty then emit_void MSTORE [dst; op]
   else if is_bytestring_type ty then compile_store_bytestring op dst
   else emit_void MCOPY [dst; op; Lit (n2w (type_memory_bytes ce ty))]) ca = ((),cb) /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv + 64 < dimword (:256) /\
  eval_operand op s = SOME sw /\ eval_operand dst s = SOME dw /\
  (if is_word_type ty then sw = typed_val_to_w256 tv v
   else val_in_memory tv v (w2n sw) s.vs_memory) /\
  (!x. op = Var x \/ dst = Var x ==> not_fresh_at ca x) ==>
  cb.cs_current_insts = ca.cs_current_insts ++ emitted_insts ca cb /\
  same_blocks ca cb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts ca cb) /\
  EVERY (\i. i.inst_opcode <> GAS) (emitted_insts ca cb) /\
  ?t. run_inst_seq (emitted_insts ca cb) s = OK t /\
      val_in_memory tv v (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at ca x ==> lookup_var x t = lookup_var x s) /\
      (!a n. a+n <= w2n dw \/ w2n dw + type_memory_size tv <= a ==>
        mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  strip_tac >>
  Cases_on `~is_word_type ty /\ ~is_bytestring_type ty /\ type_memory_bytes ce ty = 0`
  >- (gvs[] >>
      drule_all (emit_mcopy_run |> SPEC_ALL |> Q.INST [`n` |-> `0`]
        |> SIMP_RULE (srw_ss()) []) >> strip_tac >> simp[] >>
      conj_tac
      >- (drule emitted_insts_emit_void >> simp[venomInstTheory.mk_inst_def]) >>
      rpt conj_tac
      >~ [`val_in_memory`]
      >- (irule mcopy_val_in_memory >> simp[] >>
          drule val_footprint_le >> simp[])
      >~ [`lookup_var`]
      >- simp[mcopy_def, write_memory_with_expansion_def, LET_THM, lookup_var_def]
      >~ [`mem_bytes_at`]
      >- (rpt strip_tac >> irule mem_bytes_at_mcopy_disjoint >> simp[])
      >~ [`LENGTH _ <= LENGTH _`]
      >- simp[mcopy_def, immutable_write_memory_capacity, MAX_DEF] >>
      simp[mcopy_def, write_memory_with_expansion_def, LET_THM,
           venom_state_component_equality]) >>
  `compile_store_memory ce op dst ty ty ca = ((),cb)` by
    (simp[compile_store_memory_def] >>
     Cases_on `is_word_type ty` >> gvs[] >>
     Cases_on `is_bytestring_type ty` >> gvs[] >>
     Cases_on `type_memory_size tv` >> gvs[compile_copy_memory_def]) >>
  `!x. op = Var x ==> not_fresh_at ca x` by metis_tac[] >>
  `!x. dst = Var x ==> not_fresh_at ca x` by metis_tac[] >>
  drule_all compile_store_memory_run_size_bound_with_capacity >> strip_tac >>
  simp[] >> conj_tac
  >- (irule compile_store_memory_same_type_no_gas >> goal_assum drule) >>
  gvs[venom_state_component_equality, ADD_COMM] >> metis_tac[]
QED

Theorem ctor_physical_write_path:
  (if is_word_type ty then emit_void MSTORE [dst; op]
   else if is_bytestring_type ty then compile_store_bytestring op dst
   else emit_void MCOPY [dst; op; Lit (n2w (type_memory_bytes ce ty))]) ca = ((),cb) /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv + 64 < dimword (:256) /\
  eval_operand op s = SOME sw /\ eval_operand dst s = SOME dw /\
  (if is_word_type ty then sw = typed_val_to_w256 tv v
   else val_in_memory tv v (w2n sw) s.vs_memory) /\
  (!x. op = Var x \/ dst = Var x ==> not_fresh_at ca x) /\
  fn_has_code ca cb func /\ ~s.vs_halted /\
  s.vs_current_bb = ca.cs_current_bb /\
  s.vs_inst_idx = LENGTH ca.cs_current_insts ==>
  ?q. gas_marked_path F ctx func s 0 (OK q) /\
      val_in_memory tv v (w2n dw) q.vs_memory /\
      ~q.vs_halted /\ q.vs_current_bb = cb.cs_current_bb /\
      q.vs_inst_idx = LENGTH cb.cs_current_insts /\
      (!x. not_fresh_at ca x ==> lookup_var x q = lookup_var x s) /\
      (!a n. a+n <= w2n dw \/ w2n dw + type_memory_size tv <= a ==>
        mem_bytes_at a n q.vs_memory = mem_bytes_at a n s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH q.vs_memory /\
      (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
        vs_current_bb := s.vs_current_bb; vs_prev_bb := s.vs_prev_bb;
        vs_inst_idx := s.vs_inst_idx|>) = s
Proof
  strip_tac >> drule_all ctor_physical_write_run >> strip_tac >>
  rename1 `run_inst_seq _ s = OK u` >>
  `cb.cs_current_bb = ca.cs_current_bb` by gvs[same_blocks_def] >>
  `gas_marked_path F ctx func s 0
     (OK (u with vs_inst_idx := LENGTH cb.cs_current_insts))` by
    (irule straight_line_zero_gas_path >> simp[] >>
     qexistsl_tac [`emitted_insts ca cb`, `ca`] >> simp[]) >>
  qexists_tac `u with vs_inst_idx := LENGTH cb.cs_current_insts` >>
  gvs[venom_state_component_equality, lookup_var_def] >> metis_tac[]
QED
