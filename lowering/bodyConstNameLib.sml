(* Discharging const_name_root premises from body_inv: a supported
   expression or statement names no constant (body_inv_const_name_root and
   the no-name-root lemmas of supportedNameRoot). *)
structure bodyConstNameLib =
struct
open HolKernel boolLib bossLib
open bodySimTheory supportedNameRootTheory supportedStmtTraverseTheory
     supportedExprTraverseTheory exprSimHypsDefsTheory

(* Each takes a supported-code fact, then const_name_root's fact. *)
val expr_lemmas =
  [REWRITE_RULE [GSYM AND_IMP_INTRO] supported_expr_no_name_root,
   cj 1 supported_pure_no_name_root, cj 4 supported_pure_no_name_root,
   cj 1 supported_effect_no_name_root, cj 2 supported_effect_no_name_root]

val stmt_exists_defs =
  [supported_stmt_expr_exists_def, supported_assignment_exists_def,
   supported_iterator_exists_def, supported_assert_exists_def,
   supported_raise_exists_def, DE_MORGAN_THM]

val name_free_pat = ``~supported_expr_exists (const_name_root cx) e``

(* ~supported_expr_exists (const_name_root cx) e for every e that the
   assumption s says is supported, given pr from body_inv_const_name_root. *)
fun name_free_facts pr s =
  let
    fun try_mp l = SOME (MATCH_MP (MATCH_MP l s) pr) handle HOL_ERR _ => NONE
    val stmt =
      CONJUNCTS (SIMP_RULE std_ss stmt_exists_defs
        (MATCH_MP (MATCH_MP (cj 1 supported_stmts_no_name_root) s) pr))
      handle HOL_ERR _ => []
  in
    filter (can (match_term name_free_pat) o concl)
      (List.mapPartial try_mp expr_lemmas @ stmt)
  end

(* irule th, then drop its const-name premises that body_inv and the
   assumptions about supported code discharge. *)
fun irule_body_pre th =
  TRY (drule_then assume_tac body_inv_const_name_root) >> irule th >>
  TRY (qpat_x_assum `!x. const_name_root _ x ==> _`
         (fn pr => ASSUM_LIST (fn asms =>
            PURE_REWRITE_TAC ([NOT_CLAUSES, AND_CLAUSES] @
              List.concat (map (name_free_facts pr) asms)))))

end
