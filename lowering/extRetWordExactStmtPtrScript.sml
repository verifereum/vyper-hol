Theory extRetWordExactStmtPtr
Ancestors
  extRetWordStmtPartsPtr extRetWordSuffixPtr extRetNormalEvidencePtr
  exprLowering exprSimHypsDefs bodyPtrDefs
  compileEnv loweringPosts vyperInterpreter vyperState finite_map stmtSimReturn
  extRetSomeComposePtr extRetWordInputsPtr typedCopyPtr gasSummaryComposePtr
  allocationPtr abiBuiltinAllocation loweringHalt fragExec stmtLowering
  venomInst venomState venomExecSemantics words list

Theorem external_return_word_alloca_member_no_open:
  compile_external_return (SOME op) T F ei msz F nkey ut iv st = (x,st') /\
  fn_has_code st st' func ==>
  ?buf. MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w] [buf]) (fn_insts func)
Proof
  strip_tac >> drule compile_external_return_word_parts >> simp[] >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qexists_tac `buf` >> irule lookup_block_fn_insts >>
  qexistsl_tac [`bb`, `st.cs_current_bb`] >> simp[] >>
  qpat_x_assum `!i. _` (qspec_then `0` mp_tac) >>
  simp[get_instruction_def] >> metis_tac[EL_MEM]
QED

Theorem external_return_word_allocation_inputs_no_open:
  compile_external_return (SOME op) T F ei msz F nkey ut iv st = (x,st') /\
  fn_has_code st st' func /\
  stmt_state_rel ctx func cenv cx ee t ==>
  ?base. FLOOKUP (abi_builtin_allocate_state st.cs_next_id 32 t).vs_allocas
    st.cs_next_id = SOME (base,32) /\ base < dimword (:256)
Proof
  strip_tac >> drule_all external_return_word_alloca_member_no_open >> strip_tac >>
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

Theorem external_return_word_exact_stmt_frag_ptr:
  cenv.ce_return_pc = NONE /\ is_word_type ty /\
  is_word_type (expr_type e) /\ ~cenv.ce_raw_return /\
  cenv.ce_nonreentrant = (F,nkey,ut,iv) /\ well_typed_expr env e /\
  (!id t. FLOOKUP env.var_types id = SOME t ==>
          well_formed_type env.type_defs t) /\
  expr_sim_ptr d ctx PG func cenv cx ty e es ==>
  stmt_frag_ptr d ctx PG func cx lctx (\v es gt r. T) cenv
    (stmt_env cenv lctx ty (Return (SOME e)))
    (eval_stmt cx (Return (SOME e))) es
Proof
  strip_tac >> rw[stmt_frag_ptr_def] >>
  drule_all external_return_word_stmt_parts >> strip_tac >>
  drule return_forced_admissible >> strip_tac >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_sim_ptr_def] >>
  disch_then (drule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  dxrule gas_outcome_ptr_normal_evidence >> strip_tac >>
  drule_at (Pat `gas_outcome_ptr _ _ _ _ _ _ _ _`)
    external_return_some_outcome_ptr >>
  disch_then irule >> rpt gen_tac >> strip_tac >> gvs[] >>
  drule_all expr_post_ptr_return_inputs >> strip_tac >>
  drule_all external_return_word_allocation_inputs_no_open >> strip_tac >>
  irule compile_external_return_word_suffix_gas_path_ptr >> simp[] >> metis_tac[]
QED
