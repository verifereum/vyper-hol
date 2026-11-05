(* A valued return's code starts with the code of its value. *)
Theory externalReturnPrefix
Ancestors
  stmtLoweringMono exprLoweringProps loweringPosts stmtLowering exprLowering
  compileEnv

(* Sequence ci_mono through binds, lets, conditionals and case splits,
   down to the operations named in rws (as in stmtLoweringMono). *)
fun ci_mono_chain_tac rws =
  let val close =
        FIRST (map MATCH_ACCEPT_TAC
                 (List.concat (map BODY_CONJUNCTS (ci_mono_comp_return :: rws))))
  in
    rpt gen_tac >>
    rpt (FIRST [MATCH_MP_TAC ci_mono_bind, MATCH_MP_TAC ci_mono_ignore_bind,
                close, FIRST_ASSUM MATCH_ACCEPT_TAC,
                IF_CASES_TAC, BasicProvers.TOP_CASE_TAC] >>
         rpt conj_tac >> rpt gen_tac >> PURE_REWRITE_TAC[LET_THM] >>
         BETA_TAC) >>
    simp (ci_mono_comp_return :: rws)
  end;

Theorem ci_mono_bind_after[local]:
  (!v s. ci_mono s (SND (k v s))) /\ m sa = (op, s1) ==>
  ci_mono s1 (SND (comp_bind m k sa))
Proof
  rw[comp_bind_def]
QED

Theorem return_value_code_prefix:
  stmt_env cenv lctx ty (Return (SOME e)) sa = (cenv', sb) /\
  lower_value compile_expr cenv ty e sa = (op, s1) ==> cs_extends s1 sb
Proof
  strip_tac >>
  `ci_mono s1 sb` suffices_by simp[ci_mono_def] >>
  `sb = SND (compile_stmt cenv lctx ty (Return (SOME e)) sa)` by
    (qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
     simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def, pairTheory.UNCURRY]) >>
  pop_assum SUBST1_TAC >> simp[Once compile_stmt_def] >>
  irule ci_mono_bind_after >> simp[] >>
  ci_mono_chain_tac
    [ci_mono_return_helpers, ci_mono_emit_op, ci_mono_compile_alloc_buffer,
     cj 1 ci_mono_typed_memory_family]
QED
