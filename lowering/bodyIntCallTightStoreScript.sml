(* Primitive same-type stores with explicit physical write capacity. *)
Theory bodyIntCallTightStore
Ancestors
  bodyIntCallSmallStore placeMemoryTypedPrimitive placeMemoryPrimitiveForward
  exprSimBufferStore exprSimProps valueCopy context compileEnv venomState
  venomExecSemantics valueEncoding valueEncodingProps venomMemProps
  stmtSimDeclStore valueCopyBytes fragExec exprLoweringProps

Theorem intcall_bytes_store_sequence:
  compile_store_bytestring src dst sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  val_in_memory tv v (w2n sw) s.vs_memory /\
  val_store_size tv v < dimword (:256) /\ val_store_size tv v <= bound ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  ?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
    val_in_memory tv v (w2n dw) u.vs_memory /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (!a k. a + k <= w2n dw \/ w2n dw + bound <= a ==>
      mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH u.vs_memory
Proof
  strip_tac >> drule_all buffer_typed_bytestring_header >> strip_tac >>
  `mem_word_at (w2n sw) s.vs_memory = n2w len` by simp[mem_word_at_eq_mload] >>
  `32 + 32 * word_size len < dimword (:256)` by metis_tac[] >>
  drule_all store_bytestring_run_exact >> strip_tac >>
  simp[] >> conj_tac
  >- (irule mcopy_val_in_memory >> simp[] >>
      qspec_then `tv` (qspec_then `v` mp_tac) val_footprint_le_store_size >>
      simp[]) >>
  conj_tac >- gvs[] >>
  conj_tac
  >- (rpt strip_tac >> irule mem_bytes_at_mcopy_disjoint >> decide_tac) >>
  simp[mcopy_memory_length]
QED

Theorem intcall_raw_store_sequence:
  compile_copy_memory dst src n sa = ((),sb) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  n < dimword (:256) /\ n <= bound /\
  val_in_memory tv v (w2n sw) s.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= n ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  ?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
    val_in_memory tv v (w2n dw) u.vs_memory /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (!a k. a + k <= w2n dw \/ w2n dw + bound <= a ==>
      mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH u.vs_memory
Proof
  strip_tac >> drule_all compile_copy_memory_sequence >> strip_tac >>
  Cases_on `n = 0`
  >- (gvs[] >> irule valueCopyTheory.val_in_memory_relocate >> simp[] >>
      qexistsl_tac [`w2n sw`, `0`, `s.vs_memory`] >>
      simp[mem_bytes_at_def]) >>
  simp[] >> conj_tac
  >- (irule mcopy_val_in_memory >> simp[]) >>
  conj_tac
  >- simp[mcopy_def, write_memory_with_expansion_def,
          venom_state_component_equality] >>
  conj_tac
  >- simp[mcopy_def, write_memory_with_expansion_def, lookup_var_def] >>
  conj_tac
  >- (rpt strip_tac >> irule mem_bytes_at_mcopy_disjoint >> decide_tac) >>
  simp[mcopy_memory_length]
QED

Theorem intcall_same_type_store_sequence:
  compile_store_memory cenv src dst ty ty sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  (if is_word_type ty then sw = typed_val_to_w256 tv v
   else val_in_memory tv v (w2n sw) s.vs_memory) /\
  (if is_word_type ty then 32
   else if is_bytestring_type ty then val_store_size tv v
   else type_memory_bytes cenv ty) < dimword (:256) /\
  (if is_word_type ty then 32
   else if is_bytestring_type ty then val_store_size tv v
   else type_memory_bytes cenv ty) <= bound ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  ?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
    val_in_memory tv v (w2n dw) u.vs_memory /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (!a k. a + k <= w2n dw \/ w2n dw + bound <= a ==>
      mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH u.vs_memory
Proof
  strip_tac >> Cases_on `is_word_type ty`
  >- (gvs[] >>
      `type_memory_size tv = 32` by metis_tac[typed_word_store] >>
      `~is_bytestring_type ty` by metis_tac[is_bytestring_word_type] >>
      `type_memory_size tv + 64 < dimword (:256)` by simp[wordsTheory.dimword_def] >>
      `type_memory_size tv <= bound` by simp[] >>
      drule compile_store_memory_run_frame_with_capacity >>
      simp[] >> disch_then drule_all >> strip_tac >>
      gvs[] >> metis_tac[]) >>
  Cases_on `is_bytestring_type ty`
  >- (gvs[compile_store_memory_def] >>
      drule_all intcall_bytes_store_sequence >> strip_tac >>
      gvs[] >> metis_tac[]) >>
  gvs[compile_store_memory_def] >>
  `val_footprint tv v <= type_memory_size tv` by metis_tac[val_footprint_le] >>
  drule_all intcall_raw_store_sequence >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem intcall_same_type_store_forward:
  compile_store_memory cenv src dst ty ty sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  (if is_word_type ty then sw = typed_val_to_w256 tv v
   else val_in_memory tv v (w2n sw) s.vs_memory) /\
  (if is_word_type ty then 32
   else if is_bytestring_type ty then val_store_size tv v
   else type_memory_bytes cenv ty) < dimword (:256) /\
  (if is_word_type ty then 32
   else if is_bytestring_type ty then val_store_size tv v
   else type_memory_bytes cenv ty) <= bound /\
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
    (!a k. a + k <= w2n dw \/ w2n dw + bound <= a ==>
      mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all intcall_same_type_store_sequence >> strip_tac >>
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
