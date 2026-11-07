(* Location boundary for the immutable For element preparation.  The boolean
   constructor flag remains explicit: runtime uses DLOAD; constructors ILOAD. *)
Theory whitelistForIterImmCopy
Ancestors
  stmtLowering context compileEnv exprSimTopLevelImmutable exprSimCopy
  immutableCopyExecution vyperValue valueEncodingProps emitHelper venomInst venomExecSemantics
Libs
  monadsyntax

Theorem immutable_iter_small_copy:
  elem_size <= 32 ==>
  compile_iter_elem_copy cenv src dst elem_size LocCode F target_ty elem_ty =
    do v <- compile_imm_load_word cenv.ce_is_ctor cenv.ce_imm_alloca src;
       emit_void MSTORE [dst; v]
    od
Proof
  simp[compile_iter_elem_copy_def, compile_ptr_load_def]
QED

Theorem immutable_iter_large_copy:
  32 < elem_size ==>
  compile_iter_elem_copy cenv src dst elem_size LocCode F target_ty elem_ty =
    compile_imm_copy_to_memory cenv.ce_is_ctor cenv.ce_imm_alloca
      src dst ((elem_size + 31) DIV 32) 0
Proof
  simp[compile_iter_elem_copy_def]
QED

(* Execution, not merely compiler shape: the frame records all old registers
   and static state, while the memory equation retains the constructor read. *)
Theorem immutable_iter_large_run:
  32 < bytes /\
  compile_iter_elem_copy cenv src dst bytes LocCode F ty ty sa = ((),sb) /\
  copy_old_operand sa src /\ copy_old_operand sa dst /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  (!region. cenv.ce_is_ctor /\ cenv.ce_imm_alloca = SOME region ==>
     eval_operand region s = SOME 0w /\ copy_old_operand sa region) ==>
  ?z. copy_runtime_frame sa s sb z /\
      z.vs_memory =
        (immutable_transfers F cenv.ce_is_ctor a b ((bytes + 31) DIV 32) 0 s).vs_memory
Proof
  strip_tac >> gvs[immutable_iter_large_copy] >>
  Cases_on `cenv.ce_is_ctor` >> gvs[]
  >- (drule_all copy_ctor_run >> simp[]) >>
  drule_all copy_runtime_run >> simp[]
QED

Theorem immutable_iter_load_run[local]:
  compile_imm_load_word ctor imm src sa = (value,mid) /\
  copy_old_operand sa src /\ eval_operand src s = SOME a /\
  (!region. ctor /\ imm = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sa region) ==>
  ?u. copy_runtime_frame sa s mid u /\ copy_old_operand mid value /\
      eval_operand value u = SOME (immutable_copy_read ctor a s) /\
      u.vs_memory = s.vs_memory
Proof
  Cases_on `ctor` >> simp[] >> strip_tac
  >- (drule_all copy_ctor_load >> simp[]) >>
  drule_all copy_runtime_load >> simp[]
QED

Theorem immutable_iter_small_run:
  bytes <= 32 /\
  compile_iter_elem_copy cenv src dst bytes LocCode F ty ty sa = ((),sb) /\
  copy_old_operand sa src /\ copy_old_operand sa dst /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  (!region. cenv.ce_is_ctor /\ cenv.ce_imm_alloca = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sa region) ==>
  ?z. copy_runtime_frame sa s sb z /\
      z.vs_memory = (mstore (w2n b) (immutable_copy_read cenv.ce_is_ctor a s) s).vs_memory
Proof
  strip_tac >> gvs[immutable_iter_small_copy, comp_bind_def] >>
  pairarg_tac >> gvs[] >>
  rename1 `compile_imm_load_word _ _ _ sa = (value,mid)` >>
  drule_all immutable_iter_load_run >> strip_tac >>
  `copy_old_operand mid dst` by
    (fs[copy_runtime_frame_def] >> metis_tac[copy_old_operand_mono]) >>
  `eval_operand dst u = SOME b` by metis_tac[copy_runtime_frame_operand] >>
  drule_all copy_runtime_store >> strip_tac >>
  qexists_tac `mstore (w2n b) (immutable_copy_read cenv.ce_is_ctor a s) u` >>
  conj_tac >- metis_tac[copy_runtime_frame_trans] >>
  simp[venomStateTheory.mstore_def]
QED

Theorem immutable_iter_copy_run:
  compile_iter_elem_copy cenv src dst bytes LocCode F ty ty sa = ((),sb) /\
  copy_old_operand sa src /\ copy_old_operand sa dst /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  (!region. cenv.ce_is_ctor /\ cenv.ce_imm_alloca = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sa region) ==>
  ?z. copy_runtime_frame sa s sb z /\
      z.vs_memory =
        (if bytes <= 32 then
           mstore (w2n b) (immutable_copy_read cenv.ce_is_ctor a s) s
         else immutable_transfers F cenv.ce_is_ctor a b ((bytes + 31) DIV 32) 0 s).vs_memory
Proof
  strip_tac >> Cases_on `bytes <= 32` >> simp[]
  >- (drule_all immutable_iter_small_run >> simp[]) >>
  `32 < bytes` by decide_tac >>
  drule_all immutable_iter_large_run >> simp[]
QED

(* A well-evaluated array rules out the zero-sized element case, even though
   assignable_type by itself is not a positive-size predicate. *)
Theorem immutable_array_element_size_positive:
  evaluate_type tenv (ArrayT ty bd) = SOME (ArrayTV tv bd) ==>
  0 < type_memory_size tv
Proof
  simp[Once evaluate_type_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  simp[valueEncodingPropsTheory.type_memory_size_slots]
QED

Theorem immutable_iter_transfer_size[local]:
  0 < type_memory_size tv ==>
  (if type_memory_size tv <= 32 then
     mstore (w2n b) (immutable_copy_read ctor a s) s
   else immutable_transfers F ctor a b ((type_memory_size tv + 31) DIV 32) 0 s) =
  immutable_transfers F ctor a b (type_slot_size tv) 0 s
Proof
  simp[type_memory_size_slots] >> strip_tac >>
  Cases_on `type_slot_size tv <= 1`
  >- (`type_slot_size tv = 1` by decide_tac >>
      simp[] >>
      pure_once_rewrite_tac[numLib.num_CONV ``1:num``] >>
      pure_rewrite_tac[immutable_transfers_def, immutable_word_transfer_def] >>
      simp[wordsTheory.WORD_ADD_0]) >>
  simp[arithmeticTheory.ADD_DIV_ADD_DIV]
QED

Theorem immutable_iter_copy_typed_run:
  compile_iter_elem_copy cenv src dst bytes LocCode F ty ty sa = ((),sb) /\
  bytes = type_memory_size tv /\ 0 < bytes /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  stmt_state_rel ctx func cenv cx es s /\
  immutable_holds cenv cx ty (Value v) a es s /\
  copy_old_operand sa src /\ copy_old_operand sa dst /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  w2n b + bytes < dimword (:256) /\
  (cenv.ce_is_ctor ==> regions_disjoint (w2n a) bytes (w2n b) bytes) /\
  (!region. cenv.ce_is_ctor /\ cenv.ce_imm_alloca = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sa region) ==>
  ?z. copy_runtime_frame sa s sb z /\
      val_wf tv v /\ val_in_memory tv v (w2n b) z.vs_memory /\
      val_footprint tv v <= bytes /\
      LENGTH s.vs_memory <= LENGTH z.vs_memory /\
      (!off len. off + len <= w2n b \/ w2n b + bytes <= off ==>
        mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory)
Proof
  strip_tac >> gvs[] >>
  drule_all immutable_iter_copy_run >> strip_tac >>
  drule immutable_iter_transfer_size >> strip_tac >> gvs[] >>
  drule_all immutable_holds_bounds >> strip_tac >>
  qexists_tac `z` >> simp[] >>
  Cases_on `cenv.ce_is_ctor` >> gvs[]
  >- (drule copy_ctor_contents >> simp[] >> metis_tac[]) >>
  conj_tac >- (drule copy_runtime_contents >> simp[] >> metis_tac[]) >>
  conj_tac >- (drule copy_runtime_contents >> simp[] >> metis_tac[]) >>
  drule_at (Pos (el 3)) runtime_code_copy_memory_frame >> simp[] >> metis_tac[]
QED

Theorem immutable_iter_copy_static_frame:
  copy_runtime_frame sa s sb z ==> copy_static z = copy_static s
Proof
  simp[copy_runtime_frame_def]
QED

Theorem immutable_offset_opcodes[local]:
  compile_lit_byte_offset op off sa = (r,sb) ==>
  ?code. sb.cs_current_insts = sa.cs_current_insts ++ code /\
    EVERY (\i. MEM i.inst_opcode [ADD; ILOAD; DLOAD; MSTORE]) code
Proof
  Cases_on `off = 0` >> Cases_on `op` >>
  simp[compile_lit_byte_offset_def, comp_return_def, emit_op_def,
       comp_bind_def, comp_ignore_bind_def, fresh_id_def, fresh_var_def,
       emit_def] >> rpt strip_tac >> gvs[] >>
  simp[mk_inst_def] >> metis_tac[listTheory.EVERY_DEF, listTheory.APPEND_NIL]
QED

Theorem immutable_load_opcodes[local]:
  compile_imm_load_word ctor imm op sa = (r,sb) ==>
  ?code. sb.cs_current_insts = sa.cs_current_insts ++ code /\
    EVERY (\i. MEM i.inst_opcode [ADD; ILOAD; DLOAD; MSTORE]) code
Proof
  Cases_on `ctor` >> Cases_on `imm` >>
  simp[compile_imm_load_word_def, comp_return_def, emit_op_def,
       comp_bind_def, comp_ignore_bind_def, fresh_id_def, fresh_var_def,
       emit_def] >> rpt strip_tac >> gvs[] >>
  simp[mk_inst_def] >>
  metis_tac[listTheory.EVERY_DEF, listTheory.APPEND_ASSOC]
QED

Theorem immutable_store_opcodes[local]:
  emit_void MSTORE ops sa = ((),sb) ==>
  ?code. sb.cs_current_insts = sa.cs_current_insts ++ code /\
    EVERY (\i. MEM i.inst_opcode [ADD; ILOAD; DLOAD; MSTORE]) code
Proof
  simp[emit_void_def, emit_def, comp_bind_def, fresh_id_def,
       comp_return_def] >> rpt strip_tac >> gvs[] >> simp[mk_inst_def] >>
  metis_tac[listTheory.EVERY_DEF]
QED

Theorem immutable_transfers_opcodes[local]:
  !n off sa sb. compile_imm_copy_to_memory ctor imm src dst n off sa = ((),sb) ==>
  ?code. sb.cs_current_insts = sa.cs_current_insts ++ code /\
    EVERY (\i. MEM i.inst_opcode [ADD; ILOAD; DLOAD; MSTORE]) code
Proof
  Induct >> simp[Once compile_imm_copy_to_memory_def, comp_return_def] >>
  rpt gen_tac >> simp[comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  drule immutable_offset_opcodes >> strip_tac >>
  drule immutable_load_opcodes >> strip_tac >>
  drule immutable_store_opcodes >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  qpat_x_assum `compile_lit_byte_offset src off sa = _`
    (mp_then Any strip_assume_tac immutable_offset_opcodes) >>
  gvs[] >> metis_tac[listTheory.EVERY_APPEND, listTheory.APPEND_ASSOC]
QED

Theorem immutable_iter_copy_opcodes[local]:
  compile_iter_elem_copy cenv src dst bytes LocCode F ty ty sa = ((),sb) ==>
  ?code. sb.cs_current_insts = sa.cs_current_insts ++ code /\
    EVERY (\i. MEM i.inst_opcode [ADD; ILOAD; DLOAD; MSTORE]) code
Proof
  Cases_on `bytes <= 32` >> strip_tac
  >- (gvs[immutable_iter_small_copy, comp_bind_def] >>
      pairarg_tac >> gvs[] >>
      drule immutable_load_opcodes >> strip_tac >>
      drule immutable_store_opcodes >> strip_tac >>
      gvs[] >> metis_tac[listTheory.EVERY_APPEND, listTheory.APPEND_ASSOC]) >>
  `32 < bytes` by decide_tac >> gvs[immutable_iter_large_copy] >>
  drule immutable_transfers_opcodes >> simp[]
QED

Theorem immutable_copy_opcode_control[local]:
  MEM inst.inst_opcode [ADD; ILOAD; DLOAD; MSTORE] /\
  step_inst_base inst s = OK z ==>
  z.vs_prev_bb = s.vs_prev_bb /\ z.vs_current_bb = s.vs_current_bb /\
  z.vs_inst_idx = s.vs_inst_idx
Proof
  simp[] >> strip_tac >>
  gvs[step_inst_base_opcode_eqs, exec_pure2_def, exec_read1_def,
      exec_write2_def, AllCaseEqs(), venomStateTheory.update_var_def,
      venomStateTheory.mstore_def]
QED

Theorem immutable_copy_sequence_control[local]:
  !code s z.
  EVERY (\i. MEM i.inst_opcode [ADD; ILOAD; DLOAD; MSTORE]) code /\
  run_inst_seq code s = OK z ==>
  z.vs_prev_bb = s.vs_prev_bb /\ z.vs_current_bb = s.vs_current_bb /\
  z.vs_inst_idx = s.vs_inst_idx
Proof
  Induct >> simp[exprLoweringPropsTheory.run_inst_seq_def] >> rpt gen_tac >>
  strip_tac >> gvs[AllCaseEqs()] >>
  drule_at (Pos (el 2)) immutable_copy_opcode_control >> simp[] >>
  strip_tac >> first_x_assum drule >> simp[]
QED

Theorem immutable_iter_copy_state_frame:
  compile_iter_elem_copy cenv src dst bytes LocCode F ty ty sa = ((),sb) /\
  copy_runtime_frame sa s sb z ==>
  (z with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s
Proof
  strip_tac >> drule immutable_iter_copy_opcodes >> strip_tac >>
  gvs[copy_runtime_frame_def, exprLoweringPropsTheory.emitted_insts_def,
      listTheory.DROP_APPEND] >>
  drule_at (Pos (el 2)) immutable_copy_sequence_control >> strip_tac >>
  gvs[exprSimStorageCopyTheory.copy_static_def,
      venomStateTheory.venom_state_component_equality]
QED

Theorem immutable_iter_copy_typed_run_full:
  compile_iter_elem_copy cenv src dst bytes LocCode F ty ty sa = ((),sb) /\
  bytes = type_memory_size tv /\ 0 < bytes /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  stmt_state_rel ctx func cenv cx es s /\
  immutable_holds cenv cx ty (Value v) a es s /\
  copy_old_operand sa src /\ copy_old_operand sa dst /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  w2n b + bytes < dimword (:256) /\
  (cenv.ce_is_ctor ==> regions_disjoint (w2n a) bytes (w2n b) bytes) /\
  (!region. cenv.ce_is_ctor /\ cenv.ce_imm_alloca = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sa region) ==>
  ?z. copy_runtime_frame sa s sb z /\
      val_wf tv v /\ val_in_memory tv v (w2n b) z.vs_memory /\
      val_footprint tv v <= bytes /\
      LENGTH s.vs_memory <= LENGTH z.vs_memory /\
      (!off len. off + len <= w2n b \/ w2n b + bytes <= off ==>
        mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
      (z with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s
Proof
  strip_tac >> drule_all immutable_iter_copy_typed_run >> strip_tac >>
  drule_all immutable_iter_copy_state_frame >> strip_tac >>
  qexists_tac `z` >> gvs[] >> metis_tac[]
QED
