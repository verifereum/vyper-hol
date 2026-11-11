(* Memory case of the body induction (bodyMemory's body_mem_mutual): append. *)
Theory bodyMemAppend
Ancestors
  bodyMemoryPreds bodyMemAppendAdapter supportedStmts supportedExprs

Theorem body_append_storage_narrow_mem:
  !cx nid e tops ctx cenv vis mut elem dn slot.
    (!s'' p t'. eval_target_place cx (TopLevelNameTarget nid) s'' = (INL p,t') ==>
                body_expr_mem_ok cx e) /\
    body_inv tops ctx cenv cx /\
    supported_variable_decl tops nid =
      SOME (vis, mut, ArrayT elem (Dynamic dn), SOME slot) /\
    (mut = Storage \/ mut = Transient) /\ ~supported_full_word_type elem /\
    type_memory_bytes cenv elem < 2 ** 64 ==>
    body_stmt_mem_ok cx (Append (TopLevelNameTarget nid) e)
Proof
  cheat
QED

Theorem body_append_mem_case:
  !cx t e.
    (!s'' p t'. eval_target_place cx t s'' = (INL p,t') ==> body_expr_mem_ok cx e) /\
    body_base_target_mem_ok cx t ==>
    body_stmt_mem_ok cx (Append t e)
Proof
  rpt strip_tac >> Cases_on `?nid. t = TopLevelNameTarget nid`
  >- (gvs[] >> rw[body_stmt_mem_ok_def] >>
      Cases_on `supported_storage_dynamic_array tops nid`
      >- (Cases_on `nid` >>
          irule body_append_storage_fragment_mem >>
          gvs[supported_stmt_def] >> metis_tac[supported_expr_def]) >>
      gvs[supported_stmt_def, supported_append_target_def] >>
      `supported_stmt tops [] (Append (TopLevelNameTarget nid) e)` by
        (simp[supported_stmt_def, supported_append_target_def] >> metis_tac[]) >>
      drule bodyAppendStorageFactsTheory.body_append_element_alloc_bound >> strip_tac >>
      drule_at (Pat `supported_variable_decl _ _ = _`)
        body_append_storage_narrow_mem >>
      disch_then (qspecl_then [`cx`, `e`, `ctx`, `cenv`] mp_tac) >>
      simp[] >>
      rewrite_tac[body_stmt_mem_ok_def] >> disch_then drule_all >> simp[]) >>
  Cases_on `t` >> gvs[] >>
  rw[body_stmt_mem_ok_def, supported_stmt_def, supported_append_target_def]
QED
