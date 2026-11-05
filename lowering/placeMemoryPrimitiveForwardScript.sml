Theory placeMemoryPrimitiveForward
Ancestors
  placeMemoryForwardPath fragGasSeq fragGasMode fragExec valueCopy
  context exprLoweringProps compileEnv venomState venomInst
  list rich_list exprSimAlloc typedCopyDomain emitHelper

(* Lift a primitive sequence witness, changing only its final instruction
   index. Callers retain their semantic postconditions for this same state. *)
Theorem straight_line_zero_gas_path:
  fn_has_code sa sb func /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ code /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
  EVERY (\i. i.inst_opcode <> GAS) code /\
  run_inst_seq code s = OK u /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_marked_path F ctx func s 0
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  rw[fn_has_code_def] >>
  `isPREFIX code (DROP (LENGTH sa.cs_current_insts) bb.bb_instructions)` by
    (gvs[IS_PREFIX_APPEND] >> simp[DROP_APPEND]) >>
  `FILTER (\i. i.inst_opcode = GAS) code = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[EVERY_MEM]) >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by metis_tac[] >>
  `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  drule_all tuple_run_inst_seq_gas_path >>
  simp[gas_marked_path_def, arithmeticTheory.ADD_COMM]
QED

(* Accessible dependency inventory (C1.4.9.1.1).
   These imports are build-checked without typedMemoryCopy.

   role                 usable interface
   -------------------  --------------------------------------------------
   primitive sequence   valueCopy.compile_store_memory_run_capacity:
                        same-type word/bytestring/raw copy; one witness has
                        representation, old-variable preservation, outside
                        bytes, record equality and memory length growth.
   individual stores    valueCopy.emit_mcopy_run, store_bytestring_run_exact;
                        mcopy_val_in_memory, mem_bytes_at_mcopy_disjoint,
                        mem_bytes_at_write_disjoint, val_in_memory_relocate.
   staging allocation   exprSimAlloc.literal_alloc_buffer_run: sequence,
                        old allocas/vars, local disjointness, pointer bounds.
   compiler recursion   context.compile_store_memory_typed_def and mutual
                        equations; typedCopyDomain.type_copy_child_rank,
                        member_rank_lt_tuple, member_rank_lt_struct.
   straight-line path   straight_line_zero_gas_path (above): actual zero-GAS
                        path for sequence witness with final index update.
   loop composition     placeMemoryForwardPath zero-iteration and jump facts.
   code lookup          fragExec.fn_has_code_same_block, fn_has_code_mid,
                        fn_has_code_new_block, fn_has_code_start.
   source state         compileEnv.local_ptrs_rel, stmtSimDefs.stmt_state_rel
                        (the target already imports these).

   Missing outputs, NOT certified by this inventory:
   - dynamic/fixed array setup/round/exit emitted-code layout boundaries;
   - separated recursive typed-copy forward runner returning a single t with
     gas_marked_path F, val_in_memory at the destination, non-memory record
     frame, old vars/allocas, outside byte equality, and memory growth;
   - source-preservation/destination-prefix facts for arrays and sequential
     tuple/struct copies, without importing typedMemoryCopy invariants;
   - arbitrary MemoryPlace path replacement and stmt_state_rel reconstruction
     after write_place (C1.2/C1.3), including staging outside live regions.

   Explicit replacement execution interface for review (not a theorem):
   in addition to the final value and control endpoint, return
     (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
               vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
               vs_inst_idx := s.vs_inst_idx|>) = s,
     old-variable lookup equality, outside-destination mem_bytes_at equality,
     LENGTH s.vs_memory <= LENGTH t.vs_memory.
   These are conclusions, not a newly defined duplicate frame predicate.
   For fresh staging the record frame must permit the fresh alloca update
   while preserving existing allocation entries and allocation validity.

   Only stmtSimReturnWiden imports typedMemoryCopy in the existing lowering
   sources; do not use it as a convenience ancestor for eventual assembly.
   The target's direct ancestors and the helpers above build independently.
   The previous typedMemoryCopy guard failure is therefore not a blocker to
   *all* permitted work, but its recursive lemmas cannot be used as-is.
*)

Theorem compile_store_memory_same_type_no_gas:
  compile_store_memory cenv src dst ty ty sa = ((),sb) ==>
  EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  simp[compile_store_memory_def] >>
  Cases_on `is_word_type ty`
  >- (simp[emit_void_def, comp_bind_def, comp_return_def, fresh_id_def,
           emit_def] >> strip_tac >> gvs[emitted_insts_def, DROP_APPEND,
                                      mk_inst_def]) >>
  Cases_on `is_bytestring_type ty`
  >- (simp[compile_store_bytestring_def, compile_bytestring_copy_len_def,
           emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
           fresh_id_def, fresh_var_def, emit_def] >>
      strip_tac >> gvs[emitted_insts_def] >>
      pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_APPEND, mk_inst_def]) >>
  Cases_on `type_memory_bytes cenv ty` >>
  simp[compile_copy_memory_def, emit_void_def, comp_bind_def, comp_return_def,
       fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def, DROP_APPEND, mk_inst_def]
QED

Theorem compile_store_memory_same_type_forward:
  compile_store_memory cenv src dst ty ty sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  (if is_word_type ty then sw = typed_val_to_w256 tv v
   else val_in_memory tv v (w2n sw) s.vs_memory) /\
  w2n dw + type_memory_size tv + 64 < dimword (:256) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      val_in_memory tv v (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
                   FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size tv <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  drule_all compile_store_memory_run_capacity >> strip_tac >>
  rename1 `run_inst_seq _ s = OK u` >>
  `EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    (irule compile_store_memory_same_type_no_gas >> goal_assum drule) >>
  `sb.cs_current_bb = sa.cs_current_bb` by gvs[same_blocks_def] >>
  `gas_marked_path F ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule straight_line_zero_gas_path >> simp[] >>
     qexistsl_tac [`emitted_insts sa sb`, `sa`] >> simp[]) >>
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb /\
   u.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `(u with <|vs_vars := _; vs_memory := _|>) = s`
       (mp_tac o Q.AP_TERM `\z. (z.vs_halted,z.vs_current_bb,z.vs_allocas)`) >>
     simp[]) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[lookup_var_def] >>
  qpat_x_assum `(u with <|vs_vars := _; vs_memory := _|>) = s`
    (mp_tac o Q.AP_TERM `\z. z with vs_inst_idx := s.vs_inst_idx`) >>
  simp[] >> metis_tac[lookup_var_def, arithmeticTheory.ADD_COMM]
QED
