(* Memory-safe local Name body closure. *)
Theory bodyNameMemory
Ancestors
  bodyNameWordMemory bodyNameValueMemory bodyNameNonwordMemory
  bodyMemoryPreds exprSimDefs exprSimHypsDefs exprSimSource compileEnv
  vyperAST vyperTypeCallGraph

Theorem body_name_mem_case:
  !cx ann id. (word_value_type ann \/ ~is_word_type ann) ==>
    body_expr_mem_ok cx (Name ann id)
Proof
  rpt gen_tac >> strip_tac >> (rpt gen_tac >> match_mp_tac body_expr_mem_ok_intro >>
   conj_tac >- (rpt strip_tac >> gvs[])) >>
  rpt gen_tac >> strip_tac >>
  `expr_sim_pre cenv cx env (Name ann id) es` by
    simp[expr_sim_pre_body, int_calls_expr_def] >>
  metis_tac[compile_name_word_body_sim_mem, compile_name_nonword_body_sim_mem,
            compile_name_body_vv_sim_mem]
QED

