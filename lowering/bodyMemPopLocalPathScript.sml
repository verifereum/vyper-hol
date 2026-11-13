(* Counted, memory-checked paths for a local array pop. *)
Theory bodyMemPopLocalPath
Ancestors
  exprSimPop bodyUnopFragMemory venomMemProofs fragExecMem
  exprLoweringProps venomInst venomInstProofs venomExecSemantics
  instMemFrontier list venomState storageCopyGasPath
  exprLowering compileEnv fragGasSeqMem allocaHistoryFragment
  allocaHistory rich_list fragExec

Theorem dynarray_pop_mem_checks:
  !p esz x0 x1 x2 x3 x4 x5 x6 id s w.
    EVERY (\x. x <> p) [x0; x1; x2; x3; x4; x5; x6] /\
    lookup_var p s = SOME w /\ w2n w + 32 <= s.vs_alloca_next ==>
    run_inst_seq_mem_ok
      [mk_inst id MLOAD [Var p] [x0];
       mk_inst (id + 1) ISZERO [Var x0] [x1];
       mk_inst (id + 2) ISZERO [Var x1] [x2];
       mk_inst (id + 3) ASSERT [Var x2] [];
       mk_inst (id + 4) SUB [Var x0; Lit 1w] [x3];
       mk_inst (id + 5) MSTORE [Var p; Var x3] [];
       mk_inst (id + 6) ADD [Var p; Lit 32w] [x4];
       mk_inst (id + 7) MUL [Var x3; Lit (n2w esz)] [x5];
       mk_inst (id + 8) ADD [Var x4; Var x5] [x6]] s
Proof
  rpt gen_tac >> strip_tac >>
  irule run_inst_seq_mem_ok_of_prefix_safe >> simp[mk_inst_def] >>
  rpt gen_tac >> strip_tac >>
  `!j. MEM j pre ==> MEM j (pre ++ i::post)` by simp[] >>
  `u.vs_alloca_next = s.vs_alloca_next` by
    (irule (SRULE [] (Q.ISPEC `\t:venom_state. t.vs_alloca_next` run_inst_seq_preserves_field)) >>
     qexists_tac `pre` >> simp[] >> rpt strip_tac >>
     irule step_inst_base_preserves_alloca_next >>
     qexists_tac `i'` >> simp[] >>
     qpat_x_assum `_ = pre ++ _ ++ _` (mp_tac o Q.AP_TERM `MEM i'`) >>
     simp[] >> rpt strip_tac >> gvs[]) >>
  `lookup_var p u = lookup_var p s` by
    (irule (Q.ISPEC `lookup_var p` run_inst_seq_preserves_field) >>
     qexists_tac `pre` >> simp[] >> rpt strip_tac >>
     irule step_preserves_non_output_vars >>
     qexistsl_tac [`ARB`, `0`, `i'`] >>
     qpat_x_assum `_ = pre ++ _ ++ _` (mp_tac o Q.AP_TERM `MEM i'`) >>
     simp[] >> rpt strip_tac >>
     gvs[step_inst_non_invoke, is_terminator_def]) >>
  qpat_x_assum `_ = pre ++ _ ++ _` (mp_tac o Q.AP_TERM `MEM i`) >>
  simp[] >> rpt strip_tac >> gvs[] >>
  rewrite_tac[GSYM mk_inst_def] >>
  simp[below_frontier_MLOAD, below_frontier_MSTORE,
       below_frontier_no_ranges, mk_inst_def, eval_operand_def]
QED

Theorem dynarray_pop_local_path_mem:
  !p esz ctor imm sa r sb s w ctx func.
    compile_dynarray_pop (Var p) 32 esz ctor imm LocMemory sa = (r,sb) /\
    not_fresh_at sa p /\ fn_has_code sa sb func /\
    fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
    lookup_var p s = SOME w /\ w2n w + 32 <= s.vs_alloca_next /\
    mload (w2n w) s <> 0w /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?u. gas_path_mem ctx func s 0
          (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
        alloca_history func (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
        u.vs_memory = (mstore (w2n w) (mload (w2n w) s - 1w) s).vs_memory /\
        u = s with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory|> /\
        (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
        eval_operand r u =
          SOME (w + 32w + (mload (w2n w) s - 1w) * n2w esz)
Proof
  rpt gen_tac >> strip_tac >>
  drule dynarray_pop_mem_shape >> strip_tac >>
  `ALL_DISTINCT [x6; x5; x4; x3; x2; x1; x0] /\
   EVERY (\x. x <> p) [x0; x1; x2; x3; x4; x5; x6]` by
    (fs[] >> metis_tac[]) >>
  drule_all dynarray_pop_mem_run >>
  disch_then (qspecl_then [`esz`, `sa.cs_next_id`] strip_assume_tac) >>
  `run_inst_seq (emitted_insts sa sb) s = OK u /\
   run_inst_seq_mem_ok (emitted_insts sa sb) s /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb) /\
   LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
    (simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
     conj_tac >- (irule dynarray_pop_mem_checks >> metis_tac[]) >>
     simp[mk_inst_def, is_terminator_def]) >>
  `same_blocks sa sb /\ isPREFIX sa.cs_current_insts sb.cs_current_insts` by
    simp[same_blocks_def, IS_PREFIX_APPEND] >>
  drule_all storage_copy_code_prefix >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    metis_tac[] >>
  drule_all run_inst_seq_gas_path_mem >> strip_tac >>
  `?rest. DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest`
    by fs[IS_PREFIX_APPEND] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    fs[EVERY_MEM] >>
  drule_all alloca_history_run_inst_seq >> strip_tac >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  qpat_x_assum `!ctx. gas_path_mem _ _ _ _ _`
    (qspec_then `ctx` mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `alloca_history func (u with vs_inst_idx := _)` mp_tac >>
  simp[] >> strip_tac >>
  qexists_tac `u` >> simp[eval_operand_def] >>
  conj_tac >-
    (qpat_x_assum `u = _` mp_tac >> simp[venom_state_component_equality]) >>
  rpt strip_tac >> first_x_assum irule >> fs[] >> metis_tac[]
QED

Theorem dynarray_pop_local_empty_path_mem:
  !p esz ctor imm sa r sb s w ctx func.
    compile_dynarray_pop (Var p) 32 esz ctor imm LocMemory sa = (r,sb) /\
    not_fresh_at sa p /\ fn_has_code sa sb func /\
    lookup_var p s = SOME w /\ w2n w + 32 <= s.vs_alloca_next /\
    mload (w2n w) s = 0w /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?a t. gas_marked_path T ctx func s 0 (Abort a t)
Proof
  rpt gen_tac >> strip_tac >>
  drule dynarray_pop_mem_shape >> strip_tac >>
  `ALL_DISTINCT [x6; x5; x4; x3; x2; x1; x0] /\
   EVERY (\x. x <> p) [x0; x1; x2; x3; x4; x5; x6]` by
    (fs[] >> metis_tac[]) >>
  drule_all dynarray_pop_mem_run_empty >>
  disch_then (qspecl_then [`esz`, `sa.cs_next_id`] strip_assume_tac) >>
  `run_inst_seq (emitted_insts sa sb) s = Abort a s' /\
   run_inst_seq_mem_ok (emitted_insts sa sb) s /\
   EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
              ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
     conj_tac >- (irule dynarray_pop_mem_checks >> metis_tac[]) >>
     simp[mk_inst_def, is_terminator_def]) >>
  `same_blocks sa sb /\ isPREFIX sa.cs_current_insts sb.cs_current_insts` by
    simp[same_blocks_def, IS_PREFIX_APPEND] >>
  drule_all storage_copy_code_prefix >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    metis_tac[] >>
  drule_all run_inst_seq_abort_zero_path_mem >> strip_tac >>
  metis_tac[]
QED
