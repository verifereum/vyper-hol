(* Location boundary for the immutable For element preparation.  The boolean
   constructor flag remains explicit: runtime uses DLOAD; constructors ILOAD. *)
Theory whitelistForIterImmCopy
Ancestors
  stmtLowering context compileEnv exprSimTopLevelImmutable exprSimCopy stmtSimForArray
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

Theorem immutable_iter_copy_opcodes:
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

Theorem immutable_array_elements_length[local]:
  value_has_type (ArrayTV tv bd) (ArrayV av) ==>
  LENGTH (array_elements (ArrayTV tv bd) av) = array_length (ArrayTV tv bd) av
Proof
  Cases_on `bd` >> Cases_on `av` >>
  simp[vyperTypingTheory.value_has_type_def,
       vyperValueOperationTheory.array_elements_def,
       vyperValueOperationTheory.array_length_def]
QED

Theorem immutable_array_elements_index[local]:
  value_has_type (ArrayTV tv bd) (ArrayV av) /\
  i < LENGTH (array_elements (ArrayTV tv bd) av) ==>
  array_index (ArrayTV tv bd) av (&i) =
    SOME (EL i (array_elements (ArrayTV tv bd) av))
Proof
  strip_tac >> drule immutable_array_elements_length >> strip_tac >>
  irule (iffLR (SPEC_ALL vyperArrayTheory.array_elements_index)) >>
  simp[vyperArrayTheory.valid_index_def] >> gvs[]
QED

Theorem immutable_iter_element_ready:
  immutable_holds cenv cx (ArrayT et bd) r w es s /\
  read_result cx r es = (INL (ArrayV av),es) /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\
  value_has_type (ArrayTV etv bd) (ArrayV av) /\
  well_formed_type_value (ArrayTV etv bd) /\
  vs = array_elements (ArrayTV etv bd) av /\ i < LENGTH vs ==>
  immutable_holds cenv cx et (Value (EL i vs))
    (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) +
              i * type_memory_size etv)) es s /\
  value_has_type etv (EL i vs) /\ 0 < type_memory_size etv
Proof
  strip_tac >> gvs[] >>
  `well_formed_type_value etv` by
    (Cases_on `bd` >> gvs[vyperTypingTheory.well_formed_type_value_def]) >>
  drule_all immutable_array_elements_index >> strip_tac >>
  `value_has_type etv (EL i (array_elements (ArrayTV etv bd) av))` by
    (drule vyperAssignPreservesTypeTheory.array_index_has_type >> simp[]) >>
  reverse conj_tac >- (simp[] >> metis_tac[immutable_array_element_size_positive]) >>
  drule_at (Pos (el 6)) exprSimSubscriptArrayFramedTheory.immutable_holds_array_element >>
  simp[vyperStateTheory.read_result_def] >>
  disch_then irule >> simp[vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  metis_tac[]
QED

Theorem immutable_iter_copy_declare_rel:
  compile_iter_elem_copy cenv src (Var p) bytes LocCode F ty ty sa = ((),sb) /\
  bytes = type_memory_size tv /\ 0 < bytes /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr cenv es.scopes p /\ lookup_var p s = SOME w /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [p] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
  bytes <= sz /\ w2n w + bytes < dimword (:256) /\
  immutable_holds cenv cx ty (Value v) a es s /\
  copy_old_operand sa src /\ eval_operand src s = SOME a /\
  local_ptrs_reserved cenv sa /\
  (!q. q = p \/ ~not_local_ptr cenv es.scopes q ==> not_fresh_at sa q) ==>
  ?z. copy_runtime_frame sa s sb z /\
    stmt_state_rel ctx func cenv cx
      (es with scopes :=
        (sc |+ (id, <|assignable := assign; type := tv; value := v; popped := []|>)) :: rest) z /\
    immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es z /\
    LENGTH s.vs_memory <= LENGTH z.vs_memory /\
    (!off len. off + len <= w2n w \/ w2n w + bytes <= off ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory)
Proof
  strip_tac >>
  `copy_old_operand sa (Var p)` by simp[copy_old_operand_def] >>
  `eval_operand (Var p) s = SOME w` by simp[venomStateTheory.eval_operand_def] >>
  `(cenv.ce_is_ctor ==> regions_disjoint (w2n a) bytes (w2n w) bytes)` by
    (strip_tac >> drule_all immutable_holds_alloca_disjoint >>
     gvs[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  `(!region. cenv.ce_is_ctor /\ cenv.ce_imm_alloca = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sa region)` by
    (rpt strip_tac
     >- (gvs[exprLoweringPropsTheory.stmt_state_rel_def,
             compileEnvTheory.immutable_base_zero_def]) >>
     Cases_on `region` >> simp[copy_old_operand_def] >>
     metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_imm_base]) >>
  drule_all immutable_iter_copy_typed_run_full >> strip_tac >>
  `(!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s)` by
    gvs[copy_runtime_frame_def] >>
  `z.vs_data_section = s.vs_data_section` by
    gvs[copy_runtime_frame_def, exprSimStorageCopyTheory.copy_static_def,
        venomStateTheory.venom_state_component_equality] >>
  gvs[] >>
  qexists_tac `z` >> simp[] >> conj_tac
  >- (irule array_iter_copy_declare_rel >>
      goal_assum (drule_at Any) >> simp[] >>
      qexistsl_tac [`inst`, `s`, `sa`, `w`] >> simp[] >>
      metis_tac[arithmeticTheory.ADD_COMM]) >>
  reverse conj_tac >- metis_tac[] >>
  irule array_iter_copy_immutables >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`w2n w`, `type_memory_size tv`] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`ctx`, `func`, `inst`] >> simp[] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

(* Straight-line compiler facts do not require semantic operand witnesses. *)
Theorem immutable_iter_load_static:
  compile_imm_load_word ctor imm src sa = (v,sb) ==>
  same_blocks sa sb /\ cs_extends sa sb /\
  sa.cs_next_var <= sb.cs_next_var /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  ~block_is_terminated sb
Proof
  Cases_on `ctor` >> Cases_on `imm` >>
  simp[compile_imm_load_word_def, emit_op_def, fresh_var_def,
       fresh_id_def, emit_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, LET_THM] >>
  strip_tac >> gvs[] >>
  simp[exprLoweringPropsTheory.same_blocks_def, cs_extends_def,
       exprLoweringPropsTheory.emitted_insts_def,
       block_is_terminated_def, mk_inst_def, is_terminator_def,
       rich_listTheory.DROP_LENGTH_APPEND] >>
  Cases_on `sa.cs_current_insts` >>
  simp[listTheory.LAST_CONS_cond, is_terminator_def] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  simp[rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem immutable_byte_offset_static[local]:
  ~block_is_terminated sa /\
  compile_lit_byte_offset src off sa = (v,sb) ==>
  same_blocks sa sb /\ cs_extends sa sb /\
  sa.cs_next_var <= sb.cs_next_var /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  ~block_is_terminated sb
Proof
  Cases_on `off = 0` >> Cases_on `src` >>
  simp[compile_lit_byte_offset_def, emit_op_def, fresh_var_def,
       fresh_id_def, emit_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, LET_THM] >>
  strip_tac >> gvs[] >>
  simp[exprLoweringPropsTheory.same_blocks_def, cs_extends_def,
       exprLoweringPropsTheory.emitted_insts_def,
       block_is_terminated_def, mk_inst_def, is_terminator_def,
       rich_listTheory.DROP_LENGTH_APPEND] >>
  Cases_on `sa.cs_current_insts` >>
  simp[listTheory.LAST_CONS_cond, is_terminator_def]
QED

Theorem immutable_store_static[local]:
  emit_void MSTORE ops sa = ((),sb) ==>
  same_blocks sa sb /\ cs_extends sa sb /\
  sa.cs_next_var <= sb.cs_next_var /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  ~block_is_terminated sb
Proof
  simp[emit_void_def, fresh_id_def, emit_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, LET_THM] >>
  strip_tac >> gvs[] >>
  simp[exprLoweringPropsTheory.same_blocks_def, cs_extends_def,
       exprLoweringPropsTheory.emitted_insts_def,
       block_is_terminated_def, mk_inst_def, is_terminator_def,
       rich_listTheory.DROP_LENGTH_APPEND] >>
  Cases_on `sa.cs_current_insts` >>
  simp[listTheory.LAST_CONS_cond, is_terminator_def]
QED

Theorem immutable_static_trans[local]:
  !sa sm sb.
  (same_blocks sa sm /\ cs_extends sa sm /\
   sa.cs_next_var <= sm.cs_next_var /\
   sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
   ~block_is_terminated sm) /\
  (same_blocks sm sb /\ cs_extends sm sb /\
   sm.cs_next_var <= sb.cs_next_var /\
   sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
   ~block_is_terminated sb) ==>
  same_blocks sa sb /\ cs_extends sa sb /\
  sa.cs_next_var <= sb.cs_next_var /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  ~block_is_terminated sb
Proof
  rpt gen_tac >> strip_tac >>
  `sb.cs_current_insts = sa.cs_current_insts ++
      (emitted_insts sa sm ++ emitted_insts sm sb)` by simp[] >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (CONV_TAC (LHS_CONV (REWR_CONV exprLoweringPropsTheory.emitted_insts_def)) >>
     qpat_x_assum `sb.cs_current_insts = sa.cs_current_insts ++ _`
       (fn th => pure_once_rewrite_tac[th]) >>
     pure_rewrite_tac[rich_listTheory.DROP_LENGTH_APPEND] >> REFL_TAC) >>
  fs[exprLoweringPropsTheory.same_blocks_def] >>
  metis_tac[compileEnvTheory.cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem immutable_words_static[local]:
  !count sa sb off.
  ~block_is_terminated sa /\
  compile_imm_copy_to_memory ctor imm src dst count off sa = ((),sb) ==>
  same_blocks sa sb /\ cs_extends sa sb /\
  sa.cs_next_var <= sb.cs_next_var /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  ~block_is_terminated sb
Proof
  Induct
  >- simp[compile_imm_copy_to_memory_def, comp_return_def,
          exprLoweringPropsTheory.same_blocks_def, cs_extends_def,
          exprLoweringPropsTheory.emitted_insts_def] >>
  rpt gen_tac >>
  simp[Once compile_imm_copy_to_memory_def, comp_bind_def,
       comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rename1 `compile_lit_byte_offset src off sa = (src_op,s1)` >>
  rename1 `compile_imm_load_word ctor imm src_op s1 = (value,s2)` >>
  rename1 `compile_lit_byte_offset dst off s2 = (dst_op,s3)` >>
  rename1 `emit_void MSTORE [dst_op; value] s3 = ((),s4)` >>
  drule_all immutable_byte_offset_static >> strip_tac >>
  qpat_x_assum `compile_lit_byte_offset src off sa = _` kall_tac >>
  drule immutable_iter_load_static >> strip_tac >>
  drule_all immutable_byte_offset_static >> strip_tac >>
  drule immutable_store_static >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  match_mp_tac immutable_static_trans >> qexists_tac `s1` >>
  conj_tac >- simp[] >>
  match_mp_tac immutable_static_trans >> qexists_tac `s2` >>
  conj_tac >- simp[] >>
  match_mp_tac immutable_static_trans >> qexists_tac `s3` >>
  conj_tac >- simp[] >>
  match_mp_tac immutable_static_trans >> qexists_tac `s4` >> simp[]
QED

Theorem immutable_iter_copy_static:
  ~block_is_terminated sa /\
  compile_iter_elem_copy cenv src dst stride LocCode F et et sa = ((),sb) ==>
  same_blocks sa sb /\ cs_extends sa sb /\
  sa.cs_next_var <= sb.cs_next_var /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  ~block_is_terminated sb
Proof
  strip_tac >> Cases_on `stride <= 32`
  >- (gvs[immutable_iter_small_copy, comp_bind_def] >>
      pairarg_tac >> gvs[] >>
      rename1 `compile_imm_load_word _ _ _ sa = (v,sm)` >>
      drule immutable_iter_load_static >> strip_tac >>
      drule immutable_store_static >> strip_tac >>
      match_mp_tac immutable_static_trans >> qexists_tac `sm` >> simp[]) >>
  `32 < stride` by decide_tac >>
  gvs[immutable_iter_large_copy] >>
  drule_all immutable_words_static >> simp[]
QED
