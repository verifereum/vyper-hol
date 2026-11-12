Theory extRetWordInputsPtr
Ancestors
  allocationPtr abiBuiltinAllocation loweringHalt fragExec stmtLowering
  compileEnv venomInst venomState venomExecSemantics finite_map words list

Theorem external_return_word_alloca_member:
  compile_external_return (SOME op) T F ei msz F nkey ut iv st = (x,st') /\
  fn_has_code st st' func /\ ~block_is_terminated st ==>
  ?buf. MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w] [buf]) (fn_insts func)
Proof
  strip_tac >> drule compile_external_return_word_parts >> simp[] >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qexists_tac `buf` >> irule lookup_block_fn_insts >>
  qexistsl_tac [`bb`, `st.cs_current_bb`] >> simp[] >>
  qpat_x_assum `!i. _` (qspec_then `0` mp_tac) >>
  simp[get_instruction_def] >> metis_tac[EL_MEM]
QED

Theorem external_return_word_allocation_inputs:
  compile_external_return (SOME op) T F ei msz F nkey ut iv st = (x,st') /\
  fn_has_code st st' func /\ ~block_is_terminated st /\
  stmt_state_rel ctx func cenv cx ee t ==>
  ?base. FLOOKUP (abi_builtin_allocate_state st.cs_next_id 32 t).vs_allocas
    st.cs_next_id = SOME (base,32) /\ base < dimword (:256)
Proof
  strip_tac >> drule_all external_return_word_alloca_member >> strip_tac >>
  `32 < dimword (:256)` by
    simp[dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  Cases_on `FLOOKUP t.vs_allocas st.cs_next_id`
  >- (drule_all stmt_state_rel_alloca_fresh_bound >> strip_tac >>
      qexists_tac `t.vs_alloca_next` >>
      simp[abi_builtin_allocate_state_def, FLOOKUP_UPDATE] >> decide_tac) >>
  PairCases_on `x'` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >>
  gvs[abi_builtin_allocate_state_def] >> decide_tac
QED
