(* A checked induction specialization, not a proof of its branch premises.
 * All typing premises are inherited verbatim from the existing finite-horizon
 * theorem.  Only its final-trace premise and conclusions are strengthened. *)
Theory guardSourceOrdinarySchema
Ancestors
  guardSourceInstrumentation vyperFiniteStoragePreservation
Libs
  guardSourceSchemaLib

(* This is term-level schema construction, not a logical definition. *)
val (horizon, old_body) = dest_forall
  (concl vyperFiniteStoragePreservationTheory.eval_storage_well_formed_on_mutual);
val old_clauses = strip_conj old_body;
val structural_arities = [2,2,2,5,2,2,2,2,3,3,2];
val finite_prefix_extra = ``
  IS_SOME st.outcomes /\
  valid_horizon cx initial_st H st.storage_trace /\
  (?sfx. selected = st'.storage_trace ++ sfx) /\
  EVERY (\r. MEM r (FST H)) (storage_trace_regions selected) /\
  EVERY (\l. MEM l (SND H)) (storage_trace_locks selected) /\
  storage_roots_fit selected /\
  (!pre rq co sfx.
    selected = pre ++ StorageOutcome rq co :: sfx /\
    valid_horizon cx initial_st H pre /\
    storage_well_formed_on cx
      (empty_state with <|accounts := rq.cr_accounts;
                         tStorage := rq.cr_tStorage|>) (FST H) ==>
    storage_well_formed_on cx
      (empty_state with <|accounts := co.co_accounts;
                         tStorage := co.co_tStorage|>) (FST H))``;

fun finite_prefix_predicate (arity, clause) =
  let
    val (args, body) = strip_forall clause
    val (pre, post) = dest_imp body
    val premises = strip_conj pre
    val observation = List.nth (premises, length premises - 2)
    val _ = if #Name (dest_thy_const (#1 (strip_comb observation))) =
                 "storage_observations_ok" then ()
            else raise Fail "finite prefix schema: expected observation premise"
    val wf = find_term (fn tm =>
      (case strip_comb tm of (c,[_ ,_ ,_]) =>
         #Name (dest_thy_const c) = "storage_well_formed_on"
       | _ => false) handle HOL_ERR _ => false) post
    val strengthened_post = subst [wf |-> mk_conj (wf, observation)] post
    val _ = if aconv strengthened_post post then
              raise Fail "finite prefix schema: unchanged conclusion"
            else ()
    val new_premises = List.take (premises, length premises - 2) @
                       strip_conj finite_prefix_extra @ [List.last premises]
    fun extra_var name = List.find (fn v => fst (dest_var v) = name)
                                  (free_vars finite_prefix_extra)
                           |> valOf
    val extra_vars = map extra_var ["initial_st", "selected"]
  in
    list_mk_abs (List.take (args, arity),
      list_mk_forall (extra_vars @ List.drop (args, arity),
        mk_imp (list_mk_conj new_premises, strengthened_post)))
  end;

val finite_prefix_predicates = ListPair.map finite_prefix_predicate
  (structural_arities, old_clauses);
val (ind_vars, ind_body) = strip_forall (concl vyperInterpreterTheory.evaluate_ind);
val finite_prefix_ind_term = rhs (concl (DEPTH_CONV BETA_CONV
  (subst (ListPair.map (fn (v,p) => v |-> p)
     (ind_vars, finite_prefix_predicates)) ind_body)));

Theorem finite_prefix_evaluate_ind:
  ^finite_prefix_ind_term
Proof
  MATCH_ACCEPT_TAC (BETA_RULE
    (ISPECL finite_prefix_predicates vyperInterpreterTheory.evaluate_ind))
QED

(* Fail loudly if a source-interface change leaves unintended free variables,
 * changes the number of predicates, or changes a branch label. *)
val _ = if length finite_prefix_predicates = 11 andalso
           List.all (fn v => aconv v horizon) (free_vars finite_prefix_ind_term)
        then () else raise Fail "Unexpected free variables in prefix schema";
val finite_prefix_expected = list_mk_conj
  (ListPair.map (fn (p,clause) =>
     let val (args,_) = strip_abs p
         val applied = rhs (concl
           (DEPTH_CONV BETA_CONV (list_mk_comb (p,args))))
     in list_mk_forall (args,applied) end)
   (finite_prefix_predicates,old_clauses));
val _ = if aconv (#2 (dest_imp finite_prefix_ind_term)) finite_prefix_expected
        then () else raise Fail "Prefix induction conclusion differs from schema";
val _ = List.app (fn (name,_) =>
  print ("finite-prefix branch: " ^ guardSourceSchemaLib.owner name ^ " " ^ name ^ "\n"))
  (guardSourceSchemaLib.manifest finite_prefix_evaluate_ind);

val finite_prefix_labels =
  ["Pass", "Continue", "Break", "Return_NONE", "Return_SOME",
   "RaiseBare", "RaiseUnreachable", "RaiseReason", "RaiseCustomError",
   "AssertBare", "AssertUnreachable", "AssertReason", "AssertCustomError",
   "Log", "AnnAssign", "Append", "Assign_Base", "Assign_Tuple", "AugAssign",
   "If", "For", "Expr", "Stmts_nil", "Stmts_cons", "Iterator_Array",
   "Iterator_Range", "For_nil", "For_cons", "Expr_Name", "Expr_TopLevelName",
   "Expr_FlagMember", "Expr_IfExp", "Expr_Literal", "Expr_StructLit",
   "Expr_Subscript", "Expr_Attribute", "Expr_Builtin", "Expr_Pop",
   "Expr_TypeBuiltin", "Expr_Call_Send", "Expr_Call_ExtCall", "Expr_Call_IntCall",
   "Expr_Call_RawCallTarget", "Expr_Call_RawCallCalldataTarget", "Expr_Call_RawLog",
   "Expr_Call_RawRevert", "Expr_Call_SelfDestructTarget", "Expr_Call_CreateTarget",
   "Exprs_nil", "Exprs_cons", "BasePlaceRoot_NameTarget",
   "BasePlaceRoot_TopLevelNameTarget", "BasePlaceRoot_AttributeTarget",
   "BasePlaceRoot_SubscriptTarget", "TargetPlace", "TupleStore_BaseTarget",
   "TupleStore_TupleTarget", "TupleStores_nil_nil", "TupleStores_cons_cons",
   "TupleStores_nil_cons", "TupleStores_cons_nil", "Results_nil", "Results_cons"];
val _ = if map #1 (guardSourceSchemaLib.manifest finite_prefix_evaluate_ind) =
           finite_prefix_labels
        then () else raise Fail "Evaluator branch manifest has changed";
