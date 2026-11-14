Theory readonlyInvokeCopyFwdExecutionWordLoads
Ancestors
  readonlyInvokeCopyFwdExecutionMemoryScalars
  readonlyInvokeCopyFwdExecutionReadClassification
  readonlyInvokeCopyFwdExecutionLoads
  pointerConfinedDefs
  allocaFrontierBound
  readonlyInvokeCopyFwdExecutionLocal readonlyInvokeCopyFwdExecution
  readonlyInvokeCopyFwdExecutionOrdinary o1LowerDloadShared
  readonlyInvokeCopyFwdOperationalSupport readonlyInvokeCopyFwdSupportSeparation
  occurrenceGeometry o1LowerDloadStackFrontier o1LowerDloadJointMemoryRead
  readonlyInvokeCopyFwdOpaque frameViewFacts frameRel unitShapeDefs
  readonlyInvokeCopyFwdHeterogeneousLedger readonlyInvokeCopyFwdHeterogeneousMapOrigins
  readonlyInvokeCopyFwdAlignedOrigins readonlyInvokeCopyFwdEndpointBounds
  readonlyInvokeCopyFwdValues readonlyInvokeCopyFwdRel readonlyInvokeCopyFwdMemory
  o1LowerDloadOccurrence o1LowerDloadAddressArithmetic o1LowerDloadRelocationKernel
  internalReturnCopyFwdSim unitMemInv taintAgree ptrDiscipline memLocDefs
  venomExecSemantics venomState venomInst contextCodegenRel codegenRel
  finite_map list pred_set words arithmetic

Theorem ricf_execution_wordload_fixed_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  ssa_form fn /\ opaque_use_ok fn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode [MLOAD;ILOAD] /\ inst.inst_operands = [addr] /\
  op_prov G addr = NONE /\ step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_invariant vs C D stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
      n a U (occurrence_sites_step a B inst u) HP
      (occurrence_step a HP H inst u) ledger E sites maps targets
      (step_taint inst s u tn)
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `access_ok lo G fn inst s /\ taint_ok fn tn inst s` by
    metis_tac[ptr_discipline_def] >>
  `op_taint tn addr = {}` by
    (fs[MEM] >> gvs[taint_ok_def] >> metis_tac[]) >>
  `?out x. inst.inst_outputs = [out] /\ eval_operand addr s = SOME x /\
    u = update_var out (mload (w2n x) s) s` by
    (qpat_x_assum `step_inst fuel C inst s = OK u` mp_tac >> fs[MEM] >>
     gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_read1_def,
       AllCaseEqs()] >> metis_tac[]) >>
  `w2n x+32 <= lo` by
    (`MEM (w2n x,32) (source_memory_read_ranges inst s) /\
      mem_read_ops inst = SOME <|iao_ofst := addr; iao_size := SOME (Lit 32w);
        iao_max_size := SOME (Lit 32w)|>` by
       (fs[MEM] >> simp[source_memory_read_ranges_def, mem_read_ops_def]) >>
     mp_tac (Q.INST [`off` |-> `w2n (x:256 word)`, `len` |-> `32`,
       `ops` |-> `<|iao_ofst := addr; iao_size := SOME (Lit 32w);
         iao_max_size := SOME (Lit 32w)|>`] ricf_execution_unprovenanced_read) >>
     impl_tac >- simp[] >> simp[]) >>
  `~retpc_var fn out /\ (!name. addr = Var name ==> ~retpc_var fn name)` by
    (conj_tac
     >- (irule noncopy_output_not_retpc >> simp[] >> qexists_tac `inst` >>
         fs[MEM] >> metis_tac[active_inst_mem_fn_insts]) >>
     rpt gen_tac >> strip_tac >> irule ordinary_operand_not_retpc >> simp[] >>
     qexists_tac `inst` >> fs[MEM] >> metis_tac[active_inst_mem_fn_insts]) >>
  `eval_operand addr t = SOME x` by
    (`ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
       sites (ricf_complete_params PG s.vs_params) G tn s t` by
       fs[ricf_execution_invariant_def] >>
     drule_all ricf_opaque_frame_operand >> strip_tac >>
     `x = y` by
       (irule ld_value_agree_clean >> qexists_tac `sites` >>
        gvs[ricf_opaque_value_agree_def, ricf_is_zero_prov_def,
          ricf_value_agree_def]) >> gvs[]) >>
  `word_agree_except (mem_word_taint tn.t_mem (w2n x))
     (mload (w2n x) s) (mload (w2n x) t)` by
    (irule ld_mload_masked_bytes >> simp[mem_word_taint_def] >>
     mp_tac (Q.INST [`off` |-> `w2n (x:256 word)`, `len` |-> `32`,
       `rt` |-> `tn`] ricf_execution_fixed_read_bytes) >>
     impl_tac >- simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `step_inst fuel Ct inst t = OK (update_var out (mload (w2n x) t) t)` by
    (fs[MEM] >> simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
       exec_read1_def]) >>
  qexists_tac `update_var out (mload (w2n x) t) t` >> simp[] >> gvs[] >>
  irule (Q.INST [`p` |-> `NONE`, `m` |-> `mem_word_taint tn.t_mem (w2n (x:256 word))`,
    `x` |-> `mload (w2n (x:256 word)) s`, `y` |-> `mload (w2n (x:256 word)) t`,
    `rt` |-> `tn`, `fuel` |-> `fuel`, `Ct` |-> `Ct`]
    ricf_execution_bind_next) >>
  simp[ricf_opaque_value_agree_def, ricf_is_zero_prov_def,
    ricf_value_agree_def, ld_value_agree_def] >> fs[MEM] >>
  gvs[step_prov_def, out_prov_def, step_taint_def, out_taint_def,
    mem_taint_def, adopt_reset_def, store_taint_def,
    imm_taint_def, new_site_bytes_def, step_writes_def, written_taint_def,
    range_bytes_def, taint_component_equality, occurrence_sites_step_def,
    source_memory_write_ranges_def, update_var_def,
    FLOOKUP_DEF, is_terminator_def, SF CONJ_ss] >>
  metis_tac[update_var_def]
QED

Theorem ricf_execution_wordload_relocated_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  ssa_form fn /\ opaque_use_ok fn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode [MLOAD;ILOAD] /\ inst.inst_operands = [addr] /\
  op_prov G addr = SOME (db,sz) /\ FLOOKUP sites (db,sz) = SOME (db,sb,sz) /\
  step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_invariant vs C D stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
      n a U (occurrence_sites_step a B inst u) HP
      (occurrence_step a HP H inst u) ledger E sites maps targets
      (step_taint inst s u tn)
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `access_ok lo G fn inst s /\ taint_ok fn tn inst s` by
    metis_tac[ptr_discipline_def] >>
  `op_taint tn addr = {}` by
    (fs[MEM] >> gvs[taint_ok_def] >> metis_tac[]) >>
  `?out x. inst.inst_outputs = [out] /\ eval_operand addr s = SOME x /\
    u = update_var out (mload (w2n x) s) s` by
    (qpat_x_assum `step_inst fuel C inst s = OK u` mp_tac >>
     fs[MEM] >> gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_read1_def,
       AllCaseEqs()] >> metis_tac[]) >>
  `~retpc_var fn out /\ (!name. addr = Var name ==> ~retpc_var fn name)` by
    (conj_tac
     >- (irule noncopy_output_not_retpc >> simp[] >> qexists_tac `inst` >>
         fs[MEM] >> metis_tac[active_inst_mem_fn_insts]) >>
     rpt gen_tac >> strip_tac >> irule ordinary_operand_not_retpc >> simp[] >>
     qexists_tac `inst` >> fs[MEM] >> metis_tac[active_inst_mem_fn_insts]) >>
  `MEM (w2n x,32) (source_memory_read_ranges inst s) /\
   mem_read_ops inst = SOME <|iao_ofst := addr; iao_size := SOME (Lit 32w);
      iao_max_size := SOME (Lit 32w)|>` by
    (fs[MEM] >> simp[source_memory_read_ranges_def, mem_read_ops_def]) >>
  `?y delta. eval_operand addr t = SOME y /\
    w2n x = db+delta /\ w2n y = sb+delta /\ delta+32 <= sz /\
    (!k. k < 32 ==>
      (w2n x+k IN tn.t_mem <=> w2n y+k IN tn.t_mem) /\
      (w2n x+k NOTIN tn.t_mem ==>
        read_byte (w2n x+k) s.vs_memory = read_byte (w2n y+k) t.vs_memory))` by
    (mp_tac (Q.INST [`len` |-> `32`,
       `ops` |-> `<|iao_ofst := addr; iao_size := SOME (Lit 32w);
         iao_max_size := SOME (Lit 32w)|>`] ricf_execution_relocated_read) >>
     impl_tac >- simp[] >> simp[]) >>
  `word_agree_except (mem_word_taint tn.t_mem (w2n x))
    (mload (w2n x) s) (mload (w2n y) t)` by
    (irule ld_mload_masked_bytes >> simp[mem_word_taint_def] >>
     qx_gen_tac `k` >> strip_tac >>
     qpat_x_assum `!k. k < 32 ==> _` (qspec_then `k` mp_tac) >>
     `k+w2n x = db+(delta+k) /\ k+w2n y = delta+(k+sb) /\
      w2n x+k = db+(delta+k) /\ w2n y+k = delta+(k+sb)` by decide_tac >>
     metis_tac[]) >>
  `ricf_value_agree sites NONE (mem_word_taint tn.t_mem (w2n x))
    (mload (w2n x) s) (mload (w2n y) t)` by
    simp[ricf_value_agree_def, ld_value_agree_def] >>
  `step_inst fuel Ct inst t = OK (update_var out (mload (w2n y) t) t)` by
    (fs[MEM] >> gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_read1_def]) >>
  qexists_tac `update_var out (mload (w2n y) t) t` >> simp[] >> gvs[] >>
  (mp_tac (Q.INST [`p` |-> `NONE`, `m` |-> `mem_word_taint tn.t_mem (w2n (x:256 word))`,
    `x` |-> `mload (w2n (x:256 word)) s`, `y` |-> `mload (w2n (y:256 word)) t`,
    `rt` |-> `tn`, `fuel` |-> `fuel`, `Ct` |-> `Ct`]
    ricf_execution_bind_next) >>
  (impl_tac >- (fs[MEM] >>
  simp[ricf_opaque_value_agree_def, ricf_is_zero_prov_def,
    step_prov_def, out_prov_def, step_taint_def, out_taint_def,
    mem_taint_def, adopt_reset_def, store_taint_def,
    imm_taint_def, new_site_bytes_def, step_writes_def, written_taint_def,
    range_bytes_def, taint_component_equality, occurrence_sites_step_def,
    source_memory_write_ranges_def, update_var_def,
    FLOOKUP_DEF, is_terminator_def, SF CONJ_ss] >>
  metis_tac[update_var_def])) >> simp[])
QED

Theorem ricf_execution_storage_load_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  ssa_form fn /\ opaque_use_ok fn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\
  MEM inst.inst_opcode [SLOAD;TLOAD] /\
  step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_invariant vs C D stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
      n a U (occurrence_sites_step a B inst u) HP
      (occurrence_step a HP H inst u) ledger E sites maps targets
      (step_taint inst s u tn)
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `?kop key out. inst.inst_operands = [kop] /\ inst.inst_outputs = [out] /\
    eval_operand kop s = SOME key /\
    u = update_var out
      (if inst.inst_opcode = SLOAD then sload key s else tload key s) s` by
    (qpat_x_assum `step_inst fuel C inst s = OK u` mp_tac >> fs[MEM] >>
     gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_read1_def,
       AllCaseEqs()] >> metis_tac[]) >>
  `op_taint tn kop = {}` by
    (fs[MEM] >> gvs[taint_ok_def] >> metis_tac[]) >>
  `eval_operand kop t = SOME key` by
    (drule ricf_execution_nonaddress_operand >> disch_then irule >>
     fs[MEM] >> simp[is_pointer_preserving_op_def, mem_read_ops_def,
       mem_write_ops_def] >> metis_tac[MEM]) >>
  `~retpc_var fn out` by
    (irule noncopy_output_not_retpc >> simp[] >> qexists_tac `inst` >>
     fs[MEM] >> metis_tac[active_inst_mem_fn_insts]) >>
  `ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\
   t.vs_call_ctx = s.vs_call_ctx` by
    (`ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
       sites (ricf_complete_params PG s.vs_params) G tn s t` by
       fs[ricf_execution_invariant_def] >>
     qpat_x_assum `ricf_opaque_frame_agree _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[ricf_opaque_frame_agree_def, ricf_frame_agree_def] >> strip_tac >>
     drule taint_agree_shared >> drule taint_agree_call_ctx >>
     simp[ricf_opaque_view_def, ld_shared_agree_def]) >>
  qabbrev_tac `x = if inst.inst_opcode = SLOAD then sload key s else tload key s` >>
  qabbrev_tac `y = if inst.inst_opcode = SLOAD then sload key t else tload key t` >>
  `word_agree_except (out_taint tn inst s) x y` by
    (fs[MEM] >>
     gvs[Abbr `x`, Abbr `y`, out_taint_def, sload_def, tload_def,
       ld_shared_agree_def, key_taint_def, word_agree_except_def,
       contract_storage_def, contract_transient_def,
       vfmStateTheory.lookup_account_def, vfmStateTheory.lookup_storage_def] >>
     metis_tac[]) >>
  `step_inst fuel Ct inst t = OK (update_var out y t)` by
    (fs[MEM] >> simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
       exec_read1_def, Abbr `y`]) >>
  qexists_tac `update_var out y t` >> simp[] >> gvs[] >>
  irule (Q.INST [`p` |-> `NONE`, `m` |-> `out_taint tn inst s`]
    ricf_execution_bind_next) >>
  simp[ricf_opaque_value_agree_def, ricf_is_zero_prov_def,
    ricf_value_agree_def, ld_value_agree_def] >>
  fs[MEM] >>
  gvs[step_prov_def, out_prov_def, step_taint_def,
    mem_taint_def, adopt_reset_def, store_taint_def,
    imm_taint_def, new_site_bytes_def, step_writes_def, written_taint_def,
    range_bytes_def, taint_component_equality, occurrence_sites_step_def,
    source_memory_write_ranges_def, update_var_def,
    FLOOKUP_DEF, is_terminator_def, SF CONJ_ss] >>
  metis_tac[update_var_def]
QED

Theorem ricf_execution_wordload_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  ssa_form fn /\ opaque_use_ok fn /\
  ricf_mapped_support a B E PG G sites /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  EVERY wf_function C.ctx_functions /\ EVERY wf_ssa C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ mem_inv raw_mem_ok C vs /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode [MLOAD;ILOAD] /\ inst.inst_operands = [addr] /\
  step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_invariant vs C D stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
      n a U (occurrence_sites_step a B inst u) HP
      (occurrence_step a HP H inst u) ledger E sites maps targets
      (step_taint inst s u tn)
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `access_ok lo G fn inst s /\ taint_ok fn tn inst s` by
    metis_tac[ptr_discipline_def] >>
  `op_taint tn addr = {}` by
    (fs[MEM] >> gvs[taint_ok_def] >> metis_tac[]) >>
  `?out x. inst.inst_outputs = [out] /\ eval_operand addr s = SOME x /\
    u = update_var out (mload (w2n x) s) s` by
    (qpat_x_assum `step_inst fuel C inst s = OK u` mp_tac >>
     fs[MEM] >> gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_read1_def,
       AllCaseEqs()] >> metis_tac[]) >>
  `~retpc_var fn out /\ (!name. addr = Var name ==> ~retpc_var fn name)` by
    (conj_tac
     >- (irule noncopy_output_not_retpc >> simp[] >> qexists_tac `inst` >>
         fs[MEM] >> metis_tac[active_inst_mem_fn_insts]) >>
     rpt gen_tac >> strip_tac >> irule ordinary_operand_not_retpc >> simp[] >>
     qexists_tac `inst` >> fs[MEM] >> metis_tac[active_inst_mem_fn_insts]) >>
  `MEM (w2n x,32) (source_memory_read_ranges inst s) /\
   mem_read_ops inst = SOME <|iao_ofst := addr; iao_size := SOME (Lit 32w);
      iao_max_size := SOME (Lit 32w)|>` by
    (fs[MEM] >> simp[source_memory_read_ranges_def, mem_read_ops_def]) >>
  `?y. eval_operand addr t = SOME y /\
    (!k. k < 32 /\ w2n x+k NOTIN tn.t_mem ==>
      read_byte (w2n x+k) s.vs_memory = read_byte (w2n y+k) t.vs_memory)` by
    (mp_tac (Q.INST [`len` |-> `32`,
       `ops` |-> `<|iao_ofst := addr; iao_size := SOME (Lit 32w);
         iao_max_size := SOME (Lit 32w)|>`] ricf_execution_read_bytes) >>
     (impl_tac >- simp[]) >> simp[]) >>
  `word_agree_except (mem_word_taint tn.t_mem (w2n x))
    (mload (w2n x) s) (mload (w2n y) t)` by
    (irule ld_mload_masked_bytes >> simp[mem_word_taint_def] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  `ricf_value_agree sites NONE (mem_word_taint tn.t_mem (w2n x))
    (mload (w2n x) s) (mload (w2n y) t)` by
    simp[ricf_value_agree_def, ld_value_agree_def] >>
  `step_inst fuel Ct inst t = OK (update_var out (mload (w2n y) t) t)` by
    (fs[MEM] >> gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_read1_def]) >>
  qexists_tac `update_var out (mload (w2n y) t) t` >> simp[] >> gvs[] >>
  (mp_tac (Q.INST [`p` |-> `NONE`, `m` |-> `mem_word_taint tn.t_mem (w2n (x:256 word))`,
    `x` |-> `mload (w2n (x:256 word)) s`, `y` |-> `mload (w2n (y:256 word)) t`,
    `rt` |-> `tn`, `fuel` |-> `fuel`, `Ct` |-> `Ct`]
    ricf_execution_bind_next) >>
  (impl_tac >- (fs[MEM] >>
  simp[ricf_opaque_value_agree_def, ricf_is_zero_prov_def,
    step_prov_def, out_prov_def, step_taint_def, out_taint_def,
    mem_taint_def, adopt_reset_def, store_taint_def,
    imm_taint_def, new_site_bytes_def, step_writes_def, written_taint_def,
    range_bytes_def, taint_component_equality, occurrence_sites_step_def,
    source_memory_write_ranges_def, update_var_def,
    FLOOKUP_DEF, is_terminator_def, SF CONJ_ss] >>
  metis_tac[update_var_def])) >> simp[])
QED
