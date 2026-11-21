(* Project constant-name absence from the substituted statement. *)
structure bodyConstNameLib =
struct
open HolKernel boolLib bossLib
open bodySimTheory supportedStmtTraverseTheory
     supportedExprTraverseTheory exprSimHypsDefsTheory

val stmt_exists_defs =
  [supported_stmt_expr_exists_def, supported_assignment_exists_def,
   supported_iterator_exists_def, supported_assert_exists_def,
   supported_raise_exists_def, DE_MORGAN_THM]

val name_free_pat = ``~supported_expr_exists (const_name_root cx) e``

fun name_free_facts roots assumption =
  let
    val absence =
      MATCH_MP stmt_exprs_ok_module_const_name_free assumption
    val facts = CONJUNCTS (SIMP_RULE std_ss (roots :: stmt_exists_defs) absence)
  in
    filter (can (match_term name_free_pat) o concl) facts
  end handle HOL_ERR _ => []

fun irule_body_pre th =
  TRY (drule_then assume_tac body_inv_const_name_roots) >> irule th >>
  TRY (qpat_assum `const_name_root_mods _ = const_name_root _`
         (fn roots => ASSUM_LIST (fn assumptions =>
            PURE_REWRITE_TAC ([NOT_CLAUSES, AND_CLAUSES] @
              List.concat (map (name_free_facts roots) assumptions)))))

end
