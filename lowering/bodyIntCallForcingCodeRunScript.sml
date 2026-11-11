(* Optional-base immutable materialization at the actual operational run. *)
Theory bodyIntCallForcingCodeRun
Ancestors
  bodyIntCallMaterializeLanding exprSimCopy exprSimStorageCopy
  immutableCopyExecution immutableConstructorRelation valueEncodingProps
  valueEncoding valueEncodingDefs valueCopy venomExecSemantics context intCallFrame
  fragGasMode entrySinkExtraction abiDecoderArrayInitExec stmtReasonMemory
  finite_map list rich_list words placeMemoryStaging venomState compileEnv loweringStateRelDefs
  fragExec emitHelperProps exprLoweringProps venomInst instIdxIndep
  bodyIntCallProtectedAlloc placeMemoryPrimitiveForward

Theorem optional_immutable_copy_snapshot:
  compile_imm_copy_to_memory ctor imm src dst n off sa = ((),sb) /\
  copy_old_operand sa src /\ copy_old_operand sa dst /\
  eval_operand src s = SOME (n2w a) /\ eval_operand dst s = SOME (n2w b) /\
  (!region. ctor /\ imm = SOME region ==>
     eval_operand region s = SOME 0w /\ copy_old_operand sa region) /\
  fresh_vars_wrt sa s /\ 0 < n /\
  a+off+32*n < dimword (:256) /\ b+off+32*n < dimword (:256) /\
  (ctor ==> regions_disjoint (a+off) (32*n) (b+off) (32*n)) ==>
  ?t. copy_runtime_frame sa s sb t /\
    t.vs_memory = (write_memory_with_expansion (b+off)
      (mem_bytes_at (a+off) (32*n)
        (if ctor then s.vs_memory else s.vs_data_section)) s).vs_memory
Proof
  strip_tac >> Cases_on `ctor` >> gvs[]
  >- (drule copy_ctor_run >> disch_then (qspec_then `s` mp_tac) >>
      simp[] >> strip_tac >>
      ` (immutable_transfers F T (n2w a) (n2w b) n off s).vs_memory =
          (mcopy (b+off) (a+off) (32*n) s).vs_memory` by
        (irule immutable_memory_transfers_snapshot >> fs[regions_disjoint_def]) >>
      qexists_tac `zz` >> fs[mcopy_def, read_memory_def, GSYM mem_bytes_at_def]) >>
  drule_all copy_runtime_run >> strip_tac >>
  drule immutable_compile_runtime_snapshot >>
  disch_then (qspecl_then [`a`, `s`, `b`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  gvs[copy_runtime_frame_def, immutable_execution_frame_def, GSYM mem_bytes_at_def]
QED

Theorem optional_immutable_copy_run:
  compile_imm_copy_to_memory ctor imm src dst n off sa = ((),sb) /\
  copy_old_operand sa src /\ copy_old_operand sa dst /\
  eval_operand src s = SOME (n2w a) /\ eval_operand dst s = SOME (n2w b) /\
  (!region. ctor /\ imm = SOME region ==>
     eval_operand region s = SOME 0w /\ copy_old_operand sa region) /\
  fresh_vars_wrt sa s /\
  a+off+32*n < dimword (:256) /\ b+off+32*n < dimword (:256) /\
  (ctor ==> regions_disjoint (a+off) (32*n) (b+off) (32*n)) ==>
  ?t. copy_runtime_frame sa s sb t /\
    t.vs_memory = if n = 0 then s.vs_memory else
      (write_memory_with_expansion (b+off)
        (mem_bytes_at (a+off) (32*n)
          (if ctor then s.vs_memory else s.vs_data_section)) s).vs_memory
Proof
  strip_tac >> Cases_on `n = 0`
  >- (gvs[compile_imm_copy_to_memory_def, comp_return_def] >>
      qexists_tac `s` >>
      simp[copy_runtime_frame_def, emitted_insts_def, run_inst_seq_def,
           same_blocks_def]) >>
  `0 < n` by decide_tac >>
  drule_all optional_immutable_copy_snapshot >> simp[]
QED

(* Empty layouts require relocation, not an empty expanding write. *)
Theorem materialization_snapshot_memory:
  mem = (if n = 0 then s.vs_memory else
    (write_memory_with_expansion dst
      (mem_bytes_at src (32*n) source) s).vs_memory) /\
  val_in_memory tv v src source /\ val_wf tv v /\ type_memory_size tv = 32*n ==>
  val_in_memory tv v dst mem /\ LENGTH s.vs_memory <= LENGTH mem /\
  (!p k. regions_disjoint p k dst (32*n) ==>
    mem_bytes_at p k mem = mem_bytes_at p k s.vs_memory)
Proof
  strip_tac >> Cases_on `n = 0` >> gvs[]
  >- (irule valueEncodingPropsTheory.val_in_memory_relocate >>
      simp[] >> qexistsl_tac [`source`, `0`, `src`] >> simp[mem_bytes_at_def]) >>
  conj_tac >- (irule immutable_copy_memory_value >> metis_tac[]) >>
  simp[immutableMemoryFrameTheory.immutable_write_memory_capacity] >>
  rpt strip_tac >> irule mem_bytes_at_write_disjoint >>
  fs[regions_disjoint_def, mem_bytes_at_def]
QED

Theorem optional_immutable_copy_landing:
  compile_imm_copy_to_memory ctor imm src dst n off sa = ((),sb) /\
  copy_old_operand sa src /\ copy_old_operand sa dst /\
  eval_operand src s = SOME (n2w a) /\ eval_operand dst s = SOME (n2w b) /\
  (!region. ctor /\ imm = SOME region ==>
     eval_operand region s = SOME 0w /\ copy_old_operand sa region) /\
  fresh_vars_wrt sa s /\
  a+off+32*n < dimword (:256) /\ b+off+32*n < dimword (:256) /\
  (ctor ==> regions_disjoint (a+off) (32*n) (b+off) (32*n)) /\
  val_in_memory tv v (a+off) (if ctor then s.vs_memory else s.vs_data_section) /\
  val_wf tv v /\ type_memory_size tv = 32*n /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    val_in_memory tv v (b+off) u.vs_memory /\
    copy_static u = copy_static s /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (!q. copy_old_operand sa q ==> eval_operand q u = eval_operand q s) /\
    LENGTH s.vs_memory <= LENGTH u.vs_memory /\
    (!p k. regions_disjoint p k (b+off) (32*n) ==>
      mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all optional_immutable_copy_run >> strip_tac >>
  drule_all materialization_snapshot_memory >> strip_tac >>
  `same_blocks sa sb /\ ?is. sb.cs_current_insts = sa.cs_current_insts ++ is /\
     EVERY (\i. MEM i.inst_opcode [ADD; ILOAD; DLOAD; MSTORE]) is` by
    (Cases_on `ctor` >> gvs[]
     >- (drule code_ctor_copy_insts >> strip_tac >> simp[] >>
         fs[EVERY_MEM] >> metis_tac[]) >>
     drule code_copy_insts >> strip_tac >> simp[] >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  `emitted_insts sa sb = is` by simp[emitted_insts_def, DROP_APPEND] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) is /\
   EVERY (\i. i.inst_opcode <> GAS) is` by
    (fs[EVERY_MEM] >> rpt strip_tac >> res_tac >> gvs[is_terminator_def]) >>
  fs[copy_runtime_frame_def] >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `gas_marked_path F ctx func s 0
     (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule straight_line_zero_gas_path >> simp[] >>
     qexistsl_tac [`is`, `sa`] >> fs[same_blocks_def]) >>
  `t.vs_current_bb = sb.cs_current_bb` by fs[same_blocks_def] >>
  drule copy_static_fields >> strip_tac >>
  qpat_x_assum `t.vs_memory = _` kall_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  fs[copy_static_def, lookup_var_def, eval_op_inst_idx] >>
  rpt strip_tac >> Cases_on `q` >>
  gvs[copy_old_operand_def, eval_operand_def, lookup_var_def]
QED
