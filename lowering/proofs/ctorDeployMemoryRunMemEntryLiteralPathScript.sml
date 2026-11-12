Theory ctorDeployMemoryRunMemEntryLiteralPath
Ancestors
  ctorDeployMemoryRunMemEntryImmutableFrame ctorDeployLoweringEntryRegisterSizes
  venomExecSemantics venomInstProofs venomState venomMemProofs localPtrsProps
  finite_map words fragGasPathMem unitShapeDefs venomExecProofs venomInst

Theorem ctor_step_literal_sizes:
  !fuel ctx site s t func.
  step_inst fuel ctx site s = OK t ==>
  fn_inst_ids_distinct func ==> MEM site (fn_insts func) ==>
  (!inst n base sz.
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (base,sz) ==> sz = w2n n) ==>
  !inst n base sz.
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (base,sz) ==> sz = w2n n
Proof
  rpt strip_tac >> Cases_on `site.inst_opcode = INVOKE`
  >- (gvs[Once step_inst_def, AllCaseEqs()] >> rpt strip_tac >>
      drule ctor_bind_outputs_alloca_fields >>
      Cases_on `ret.iret_adopt_fmp` >>
      simp[adopt_return_fmp_def, merge_callee_state_def] >> metis_tac[]) >>
  gvs[Once step_inst_def] >>
  Cases_on `site.inst_opcode = ALLOCA`
  >- (gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
      rpt strip_tac >> Cases_on `inst.inst_id = site.inst_id`
      >- (`inst = site` by metis_tac[fn_inst_ids_distinct_inj] >>
          gvs[exec_alloca_def, update_var_def, AllCaseEqs(), eval_operands_def,
              eval_operand_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
      gvs[exec_alloca_def, update_var_def, AllCaseEqs(), FLOOKUP_UPDATE] >>
      metis_tac[]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next`
    by (irule step_inst_base_preserves_alloca_fields >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem ctor_edge_literal_sizes:
  fn_inst_ids_distinct func /\ gas_path_mem_edge ctx func s g (OK t) /\
  (!inst n base sz.
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (base,sz) ==> sz = w2n n) ==>
  !inst n base sz.
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (base,sz) ==> sz = w2n n
Proof
  simp[gas_path_mem_edge_def, fragExecTheory.exit_result_def] >>
  rpt strip_tac >> gvs[] >>
  `MEM inst (fn_insts func)` by
    (gvs[fn_insts_def, get_instruction_def, AllCaseEqs()] >>
     irule MEM_fn_insts_blocks >> qexists `bb` >>
     metis_tac[lookup_block_MEM, listTheory.EL_MEM]) >>
  imp_res_tac ctor_eval_phis_alloca_fields >>
  gvs[] >>
  FIRST [qpat_x_assum `OK _ = step_inst _ _ _ _` (assume_tac o SYM), all_tac] >>
  drule_all ctor_step_literal_sizes >>
  disch_then irule >> simp[] >> metis_tac[]
QED

Theorem ctor_path_literal_sizes:
  !ctx func s g res.
  gas_path_mem ctx func s g res ==>
  !t. res = OK t ==> fn_inst_ids_distinct func ==>
  (!inst n base sz.
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (base,sz) ==> sz = w2n n) ==>
  !inst n base sz.
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (base,sz) ==> sz = w2n n
Proof
  ho_match_mp_tac gas_path_mem_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      gvs[] >> ntac 2 strip_tac >>
      qpat_x_assum `fn_inst_ids_distinct _ ==> _` mp_tac >> simp[] >>
      impl_tac >- (rpt strip_tac >> irule ctor_edge_literal_sizes >>
                   goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
      simp[])
  >> rpt strip_tac >> gvs[fragExecTheory.exit_result_def]
QED

Theorem ctor_path_literal_sizes_empty:
  gas_path_mem ctx func s g (OK t) /\ fn_inst_ids_distinct func /\
  s.vs_allocas = FEMPTY ==>
  !inst n base sz.
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (base,sz) ==> sz = w2n n
Proof
  strip_tac >> drule ctor_path_literal_sizes >> simp[]
QED
