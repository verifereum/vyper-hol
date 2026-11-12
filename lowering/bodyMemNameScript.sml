(* Memory case of the body induction (bodyMemory's body_mem_mutual): a local
   name, split by its type: numeric, bool and flag words (bodyNameWordMemory),
   other word types (bodyNameWordTypeMemory) and non-words
   (bodyNameNonwordMemory), with the pointer case from bodyNameValueMemory. *)
Theory bodyMemName
Ancestors
  bodyMemoryPreds bodyNameMemory bodyNameWordTypeMemory bodyNameValueMemory
  exprSimSource exprSimHypsDefs vyperAST vyperTypeCallGraph

Theorem body_name_mem_ok:
  !cx ann id. body_expr_mem_ok cx (Name ann id)
Proof
  rpt gen_tac >>
  Cases_on `word_value_type ann \/ ~is_word_type ann`
  >- metis_tac[body_name_mem_case] >>
  gvs[] >> (rpt gen_tac >> match_mp_tac body_expr_mem_ok_intro >>
   conj_tac >- (rpt strip_tac >> gvs[])) >> rpt gen_tac >> strip_tac >>
  `expr_sim_pre cenv cx env (Name ann id) es` by
    simp[expr_sim_pre_body, int_calls_expr_def] >>
  metis_tac[compile_name_wordtype_body_sim_mem, compile_name_body_vv_sim_mem]
QED
