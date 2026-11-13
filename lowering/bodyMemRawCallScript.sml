(* Memory case of the body induction (bodyMemory's body_mem_mutual): raw_call
   to a target. *)
Theory bodyMemRawCall
Ancestors
  rawCallExpressionMemory bodyExprForceMemory bodyNonwordForceMemory exprSimRawCall exprSimDefs exprSimHypsDefs
  vyperAST vyperTypeSystem exprLowering compileEnv
  rawCallTailMemory rawCallAllocatedOracleMemory bodyMemoryPreds bodyMemRawCallRevert bodyMemRawCallBounds bodyMemRawCallFinish
  rawCallFinishPostMemory rawCallFinishPathMemory rawCallTupleMemory rawCallSuffixMemory rawCallArgumentMemory rawCallResultPathMemory rawCallPrefixMemory rawCallOracleMemory

Theorem body_raw_call_mem_case:
  !cx ty flags es v18.
    body_exprs_mem_ok cx es ==>
    body_expr_mem_ok cx (Call ty (RawCallTarget flags) es v18)
Proof
  rpt gen_tac >> strip_tac >> match_mp_tac body_expr_mem_ok_intro >>
  conj_tac >- (rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  drule raw_call_pre_operands >> strip_tac >> gvs[] >>
  `expr_vv_sim_mem ctx func cenv cx ty'
    (Call ty (RawCallTarget flags) (a::d::kws) v18) es'` by
    (irule raw_call_expr_vv_sim_mem >> metis_tac[]) >>
  simp[] >>
  Cases_on `is_word_type (expr_type (Call ty (RawCallTarget flags) (a::d::kws) v18))`
  >- (irule body_expr_sim_mem_of_vv_sim_mem >>
      first_assum (irule_at (Pat `expr_body_pre _ _ _ _ _`)) >> simp[]) >>
  irule body_nonword_expr_sim_mem_of_vv_sim_mem >>
  first_assum (irule_at (Pat `expr_body_pre _ _ _ _ _`)) >> simp[]
QED
