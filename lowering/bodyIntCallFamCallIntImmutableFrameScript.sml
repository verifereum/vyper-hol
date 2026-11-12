(* Exact immutable byte frames follow from allocation separation, not
   equality of semantic immutable values. *)
Theory bodyIntCallFamCallIntImmutableFrame
Ancestors
  bodyIntCallFamCallIntForcingFrames exprSimAlloc exprLoweringProps
  intCallFrame compileEnv venomInst finite_map words
  exprLowering loweringHalt exprSimCopy
Libs
  monadsyntax

Theorem intcall_allocated_write_immutable_frame:
  stmt_state_rel ctx func ce cx es u /\ MEM inst (fn_insts func) /\
  inst.inst_opcode = ALLOCA /\
  FLOOKUP u.vs_allocas inst.inst_id = SOME (lb,len) /\
  (!p k. regions_disjoint p k lb len ==>
    mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) ==>
  (ce.ce_is_ctor ==> !name off itv iv.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    mem_bytes_at off (type_memory_size itv) u.vs_memory =
    mem_bytes_at off (type_memory_size itv) s.vs_memory)
Proof
  simp[stmt_state_rel_def, immutable_alloca_sep_def] >> rpt strip_tac >>
  first_x_assum irule >> metis_tac[]
QED

Theorem intcall_code_unwrap_alloca:
  unwrap_value ce (LocatedValue ty p) sa = (op,sb) /\
  ~is_word_type ty /\ p.ptr_location = LocCode /\ fn_has_code sa sb func ==>
  ?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = sa.cs_next_id
Proof
  strip_tac >>
  `?buf sm. compile_alloc_buffer (type_memory_bytes ce ty) sa = (buf,sm) /\
    compile_imm_copy_to_memory ce.ce_is_ctor ce.ce_imm_alloca p.ptr_operand
      buf.buf_operand ((type_memory_bytes ce ty + 31) DIV 32) 0 sm = ((),sb)` by
    (fs[exprLoweringTheory.unwrap_value_def, contextTheory.compile_ensure_in_memory_def,
        compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
        compileEnvTheory.comp_return_def] >>
     pairarg_tac >> fs[] >> pairarg_tac >> fs[]) >>
  `cs_extends sa sm` by metis_tac[compile_alloc_buffer_extends] >>
  `same_blocks sm sb /\ ?code. sb.cs_current_insts = sm.cs_current_insts ++ code` by
    (Cases_on `ce.ce_is_ctor` >> fs[] >>
     metis_tac[exprSimCopyTheory.code_ctor_copy_insts, exprSimCopyTheory.code_copy_insts]) >>
  `cs_extends sm sb` by
    (fs[exprLoweringPropsTheory.same_blocks_def, compileEnvTheory.cs_extends_def] >>
     qexists_tac `[]` >> simp[]) >>
  `fn_has_code sa sm func` by metis_tac[fragExecTheory.fn_has_code_split] >>
  drule_all buffer_alloc_code >> strip_tac >>
  goal_assum (drule_at Any) >> simp[venomInstTheory.mk_inst_def]
QED

Theorem intcall_storage_unwrap_alloca:
  unwrap_value ce (LocatedValue ty p) sa = (op,sb) /\ ~is_word_type ty /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  fn_has_code sa sb func ==>
  ?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = sa.cs_next_id
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?buf sm result.
    compile_alloc_buffer (type_memory_bytes ce ty) sa = (buf,sm) /\
    (if ((type_memory_bytes ce ty + 31) DIV 32) = 1 then
       do value <- emit_op (if p.ptr_location = LocStorage then SLOAD else TLOAD) [p.ptr_operand];
          emit_void MSTORE [buf.buf_operand; value] od
     else do compile_word_copy_loop p.ptr_operand buf.buf_operand
               ((type_memory_bytes ce ty + 31) DIV 32) p.ptr_location LocMemory F;
             return () od) sm = (result,sb)` by
    (drule exprSimStorageCopyTheory.ensure_storage_memory_layout >>
     disch_then (qspecl_then [`p.ptr_operand`, `type_memory_bytes ce ty`,
       `(type_memory_bytes ce ty + 31) DIV 32`, `ce.ce_is_ctor`, `ce.ce_imm_alloca`] assume_tac) >>
     fs[exprLoweringTheory.unwrap_value_def, compileEnvTheory.comp_bind_def,
        compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.comp_return_def] >>
     fs[compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
        compileEnvTheory.comp_return_def] >>
     pairarg_tac >> fs[] >> pairarg_tac >> fs[] >> metis_tac[]) >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    metis_tac[compile_alloc_buffer_extends,
      exprSimStorageCopyTheory.storage_copy_suffix_extends] >>
  `fn_has_code sa sm func` by metis_tac[fragExecTheory.fn_has_code_split] >>
  drule_all buffer_alloc_code >> strip_tac >>
  goal_assum (drule_at Any) >> simp[venomInstTheory.mk_inst_def]
QED
