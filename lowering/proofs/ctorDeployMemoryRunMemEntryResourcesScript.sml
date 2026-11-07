Theory ctorDeployMemoryRunMemEntryResources
Ancestors
 ctorDeployMemoryRunMemEntryTaskBound deployEntryLayout ctorDeployDefs
 asmDataSuffixProps e2eEntry finite_map o1PassContract
 ctorDeployMemoryRunMemEntryLiteralPath ctorDeployLoweringEntryRoom
 ctorDeployMemoryRunMemEntryImmutableFrame compileEnv exprLoweringProps
 ctorDeployMemoryRunMemEntryZeroImmutables

Theorem ctor_entry_runtime_label:
 !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan es vs.
 deploy_phases policy tops (deploy_bc,runtime_bc) (rpolicy,dunit,dout,prog,cplan) /\
 gas_variant vs (deploy_entry_state prog cplan tops es) ==>
 IS_SOME (FLOOKUP vs.vs_labels "runtime_begin")
Proof
 rpt gen_tac >> strip_tac >>
 fs[deploy_phases_def] >>
 drule_all lower_vyper_deploy_unit_entry_runtime_label >>
 disch_then (qspecl_then [`[]`, `cplan`, `es`] mp_tac) >>
 simp[entry_venom_state_frame_fields, data_suffix_label_offsets] >>
 fs[gas_variant_def, deploy_entry_state_def, entry_venom_state_frame_fields] >>
 qpat_x_assum `_ = vs with vs_gas_readings := _`
   (mp_tac o Q.AP_TERM `\s. s.vs_labels`) >>
 simp[] >> disch_then (fn th => rewrite_tac[GSYM th]) >>
 simp[entry_venom_state_frame_fields]
QED

Theorem ctor_registered_landing_resources:
 gas_path_mem ctx func fixed g (OK actual) /\
 fn_inst_ids_distinct func /\ fixed.vs_allocas = FEMPTY /\
 fixed.vs_alloca_next = cap /\
 alloca_frontier_inv_from cap ctx func site actual /\
 cap + unit_alloca_budget ctx < dimword (:256) /\
 abi_encoder_registered_effect ids [] fixed actual /\
 fixed.vs_labels = initial.vs_labels /\ actual.vs_labels = fixed.vs_labels /\
 IS_SOME (FLOOKUP initial.vs_labels "runtime_begin") /\
 (!id b sz. local_region ce scopes actual id b sz ==> cap <= b) ==>
 alloca_room ctx func actual /\
 IS_SOME (FLOOKUP actual.vs_labels "runtime_begin") /\
 mem_bytes_at 0 cap actual.vs_memory = mem_bytes_at 0 cap fixed.vs_memory /\
 cap <= actual.vs_alloca_next /\
 (!id b sz. FLOOKUP actual.vs_allocas id = SOME (b,sz) ==> cap <= b) /\
 (!id b sz. local_region ce scopes actual id b sz ==> cap <= b) /\
 (!inst n b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit n] /\
   FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n)
Proof
 strip_tac >>
 `cap <= actual.vs_alloca_next /\
  (!id b sz. FLOOKUP actual.vs_allocas id = SOME (b,sz) ==> cap <= b)` by
   (drule ctor_gas_path_mem_lower_bound >>
    disch_then (qspecl_then [`actual`, `cap`] mp_tac) >> simp[] >> metis_tac[]) >>
 asm_rewrite_tac[] >> conj_tac
 >- (metis_tac[deploy_ctor_frontier_alloca_room]) >>
 conj_tac
 >- (metis_tac[ctor_registered_path_immutable_prefix, arithmeticTheory.LESS_EQ_REFL]) >>
 metis_tac[ctor_path_literal_sizes_empty]
QED

Theorem ctor_landing_immutable_separation:
 (!name tv v off.
   FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
   FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
     | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
   off + type_memory_size tv <= cap) /\
 cap <= actual.vs_alloca_next /\
 (!id b sz. FLOOKUP actual.vs_allocas id = SOME (b,sz) ==> cap <= b) /\
 (!id b sz. local_region ce es.scopes actual id b sz ==> cap <= b) ==>
 immutable_alloca_sep func ce cx es actual
Proof
 simp[immutable_alloca_sep_def, regions_disjoint_def] >> rpt strip_tac >>
 first_x_assum drule_all >> strip_tac >>
 res_tac >> decide_tac
QED

Theorem ctor_task_actual_resources:
 deploy_phases policy tops (deploy_bc,runtime_bc) (rpolicy,dunit,dout,prog,cplan) /\
 gas_variant vs (deploy_entry_state prog cplan tops es) /\
 gas_path_mem dunit.cu_context func fixed g (OK actual) /\
 fn_inst_ids_distinct func /\ fixed.vs_allocas = FEMPTY /\
 fixed.vs_alloca_next = imm_len tops /\
 alloca_frontier_inv_from (imm_len tops) dunit.cu_context func site actual /\
 imm_len tops + unit_alloca_budget dunit.cu_context < dimword (:256) /\
 abi_encoder_registered_effect ids [] fixed actual /\
 fixed.vs_labels = vs.vs_labels /\ actual.vs_labels = fixed.vs_labels /\
 (!id b sz. local_region ce scopes actual id b sz ==> imm_len tops <= b) ==>
 alloca_room dunit.cu_context func actual /\
 IS_SOME (FLOOKUP actual.vs_labels "runtime_begin") /\
 mem_bytes_at 0 (imm_len tops) actual.vs_memory =
   mem_bytes_at 0 (imm_len tops) fixed.vs_memory /\
 imm_len tops <= actual.vs_alloca_next /\
 (!id b sz. FLOOKUP actual.vs_allocas id = SOME (b,sz) ==> imm_len tops <= b) /\
 (!id b sz. local_region ce scopes actual id b sz ==> imm_len tops <= b) /\
 (!inst n b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit n] /\
   FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n)
Proof
 strip_tac >> drule_all ctor_entry_runtime_label >> strip_tac >>
 drule_all ctor_registered_landing_resources >> simp[]
QED

Theorem ctor_task_immutable_separation:
 deploy_source_ok tops am tx /\ deploy_state_rel tops deploy_bc am tx es /\
 deploy_ctor_start tops am tx (mut,nr,stmts,am_c,es0) /\
 immutable_section_layout ce tops /\ ce.ce_module = NONE /\ cx.txn = tx /\
 (!p. p < imm_len tops ==>
   mem_bytes_at p 1 actual.vs_memory = mem_bytes_at p 1 []) /\
 imm_len tops <= actual.vs_alloca_next /\
 (!id b sz. FLOOKUP actual.vs_allocas id = SOME (b,sz) ==> imm_len tops <= b) /\
 (!id b sz. local_region ce es0.scopes actual id b sz ==> imm_len tops <= b) ==>
 immutable_alloca_sep func ce cx (es0 with outcomes := SOME os) actual
Proof
 strip_tac >> irule ctor_landing_immutable_separation >>
 qexists `imm_len tops` >> simp[] >>
 conj_tac >- metis_tac[] >>
 reverse conj_tac >- metis_tac[] >>
 rpt strip_tac >>
 Cases_on `ALOOKUP es0.immutables tx.target` >> gvs[] >>
 drule_all ctor_source_zero_memory_location >> simp[]
QED

Theorem ctor_registered_operand_zero:
 eval_operand op fixed = SOME 0w /\ fresh_vars_wrt st fixed /\
 (!x w. not_fresh_at st x /\ lookup_var x fixed = SOME w ==>
   lookup_var x actual = SOME w) /\ actual.vs_labels = fixed.vs_labels ==>
 eval_operand op actual = SOME 0w
Proof
 Cases_on `op` >> simp[venomStateTheory.eval_operand_def] >>
 rpt strip_tac >> gvs[] >>
 `not_fresh_at st s` by
   (fs[not_fresh_at_def, fresh_vars_wrt_def, venomStateTheory.lookup_var_def,
       arithmeticTheory.GREATER_EQ, FLOOKUP_DEF] >> metis_tac[]) >>
 metis_tac[]
QED

Theorem ctor_registered_immutable_base_zero:
 ce.ce_imm_alloca = (if cap > 0 then SOME imm else NONE) /\
 eval_operand imm fixed = SOME 0w /\ fresh_vars_wrt st fixed /\
 (!x w. not_fresh_at st x /\ lookup_var x fixed = SOME w ==>
   lookup_var x actual = SOME w) /\ actual.vs_labels = fixed.vs_labels /\
 IS_SOME (FLOOKUP actual.vs_labels "runtime_begin") ==>
 immutable_base_zero ce actual
Proof
 strip_tac >> drule_all ctor_registered_operand_zero >>
 simp[immutable_base_zero_def] >> Cases_on `cap > 0` >> simp[]
QED
