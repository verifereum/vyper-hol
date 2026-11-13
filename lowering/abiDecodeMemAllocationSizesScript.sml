(* Literal allocation sizes survive the actual counted decoder path. *)
Theory abiDecodeMemAllocationSizes
Ancestors
  abiStepAllocRecords abiAllocationHistory fragGasPathMem exprLoweringProps localPtrsProps
  venomExecSemantics venomExecProofs venomMemProofs venomInstProofs1
  venomState venomInst finite_map list words

Theorem abi_decode_alloca_sizes_step[local]:
  fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\
  inst.inst_opcode = ALLOCA /\ step_inst_base inst s = OK t /\
  (!other w b sz. MEM other (fn_insts func) /\
    other.inst_opcode = ALLOCA /\ other.inst_operands = [Lit w] /\
    FLOOKUP s.vs_allocas other.inst_id = SOME (b,sz) ==> sz = w2n w) ==>
  !other w b sz. MEM other (fn_insts func) /\
    other.inst_opcode = ALLOCA /\ other.inst_operands = [Lit w] /\
    FLOOKUP t.vs_allocas other.inst_id = SOME (b,sz) ==> sz = w2n w
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `other.inst_id = inst.inst_id`
  >- (`other = inst` by metis_tac[fn_inst_ids_distinct_inj] >>
      gvs[] >>
      qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
      simp[step_inst_base_def, eval_operand_def] >> strip_tac >>
      gvs[exec_alloca_def, AllCaseEqs(), LET_THM, update_var_def, FLOOKUP_UPDATE] >>
      metis_tac[]) >>
  qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
  simp[step_inst_base_def] >> strip_tac >>
  gvs[AllCaseEqs(), exec_alloca_def, LET_THM, update_var_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem abi_decode_allocation_sizes_step:
  fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\
  step_inst fuel ctx inst s = OK t /\
  (!other w b sz. MEM other (fn_insts func) /\
    other.inst_opcode = ALLOCA /\ other.inst_operands = [Lit w] /\
    FLOOKUP s.vs_allocas other.inst_id = SOME (b,sz) ==> sz = w2n w) ==>
  !other w b sz. MEM other (fn_insts func) /\
    other.inst_opcode = ALLOCA /\ other.inst_operands = [Lit w] /\
    FLOOKUP t.vs_allocas other.inst_id = SOME (b,sz) ==> sz = w2n w
Proof
  strip_tac >> Cases_on `inst.inst_opcode = INVOKE`
  >- (drule_all step_inst_invoke_allocas >> disch_then SUBST1_TAC >>
      first_assum ACCEPT_TAC) >>
  `step_inst_base inst s = OK t` by fs[step_inst_non_invoke] >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (match_mp_tac (Q.INST [`inst` |-> `inst`, `s` |-> `s`]
        abi_decode_alloca_sizes_step) >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `t.vs_allocas = s.vs_allocas` by
    (irule step_inst_base_preserves_allocas >> qexists_tac `inst` >> simp[] >>
     metis_tac[]) >>
  pop_assum SUBST1_TAC >>
  first_assum ACCEPT_TAC
QED

Theorem abi_decode_allocation_sizes_edge[local]:
  fn_inst_ids_distinct func /\ gas_path_mem_edge ctx func s n (OK t) /\
  (!other w b sz. MEM other (fn_insts func) /\
    other.inst_opcode = ALLOCA /\ other.inst_operands = [Lit w] /\
    FLOOKUP s.vs_allocas other.inst_id = SOME (b,sz) ==> sz = w2n w) ==>
  !other w b sz. MEM other (fn_insts func) /\
    other.inst_opcode = ALLOCA /\ other.inst_operands = [Lit w] /\
    FLOOKUP t.vs_allocas other.inst_id = SOME (b,sz) ==> sz = w2n w
Proof
  strip_tac >>
  qpat_x_assum `gas_path_mem_edge _ _ _ _ _` mp_tac >>
  rw[gas_path_mem_edge_def] >> gvs[fragExecTheory.exit_result_def] >>
  rename1 `get_instruction bb ix = SOME inst` >>
  `MEM inst (fn_insts func)` by
    (irule abi_alloca_history_fn_member >> qexists_tac `bb` >>
     conj_tac >- metis_tac[lookup_block_MEM] >>
     fs[get_instruction_def] >> metis_tac[MEM_EL]) >>
  imp_res_tac eval_phis_preserves_alloca_fields >>
  gvs[jump_to_def] >>
  FIRST [qpat_assum `step_inst _ _ _ _ = OK _` mp_tac,
         qpat_assum `OK _ = step_inst _ _ _ _` (mp_tac o SYM)] >>
  disch_then (fn exec => assume_tac exec >>
    mp_tac (PART_MATCH (el 3 o strip_conj o fst o dest_imp)
      (Q.INST [`func` |-> `func`] abi_decode_allocation_sizes_step) (concl exec))) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qspecl_then [`other`,`w`,`b`,`sz`] mp_tac) >> simp[]
QED

Theorem abi_decode_allocation_sizes_path:
  !ctx func s n r. gas_path_mem ctx func s n r ==>
  !t. r = OK t /\ fn_inst_ids_distinct func /\
  (!other w b sz. MEM other (fn_insts func) /\
    other.inst_opcode = ALLOCA /\ other.inst_operands = [Lit w] /\
    FLOOKUP s.vs_allocas other.inst_id = SOME (b,sz) ==> sz = w2n w) ==>
  !other w b sz. MEM other (fn_insts func) /\
    other.inst_opcode = ALLOCA /\ other.inst_operands = [Lit w] /\
    FLOOKUP t.vs_allocas other.inst_id = SOME (b,sz) ==> sz = w2n w
Proof
  ho_match_mp_tac gas_path_mem_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
      qpat_x_assum `_ ==> !other w b sz. _` match_mp_tac >>
      qpat_assum `gas_path_mem_edge _ _ _ _ _` (fn edge =>
        mp_tac (PART_MATCH (el 2 o strip_conj o fst o dest_imp)
          abi_decode_allocation_sizes_edge (concl edge))) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then ACCEPT_TAC) >>
  rpt strip_tac >> gvs[fragExecTheory.exit_result_def]
QED
