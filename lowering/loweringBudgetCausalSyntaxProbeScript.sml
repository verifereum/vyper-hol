(* Structural validation only: no causal case is asserted by this probe. *)
Theory loweringBudgetCausalSyntaxProbe
Ancestors
  loweringBudgetCausalRecursion loweringBudgetECStopping loweringBudgetSendCausal
Libs
  loweringBudgetCausalSyntaxLib

fun check msg b = if b then () else raise Fail ("causal syntax: " ^ msg);
fun closed_bool t = null (free_vars t) andalso type_of t = bool;
fun has_const names tm =
  List.exists (fn c => List.exists (fn n => fst(dest_const c) = n) names)
    (find_terms is_const tm);
val old_names = ["body_stmt_full_ok","body_stmts_full_ok","body_iterator_full_ok",
  "body_for_full_ok","body_expr_full_ok","body_exprs_full_ok",
  "body_base_target_full_ok","body_tuple_target_full_ok",
  "body_tuple_targets_full_ok","body_results_full_ok",
  "expr_sim_full","expr_vv_sim_full","expr_map_sim_full","stmt_frag_full",
  "frame_ret_ok_full","gas_outcome_full"];
val named_args = ListPair.zip
  (["stmt","stmts","iterator","for","expr","exprs","base-place","base-target",
    "tuple","tuples","results"],induction_args);
val _ = check "eleven arguments" (length induction_args = 11);
val _ = ListPair.app (fn (v,t) => check "induction argument type" (type_of v = type_of t))
  (ind_vars,induction_args);
val _ = check "shared base argument" (aconv (List.nth(induction_args,6)) (List.nth(induction_args,7)));
val _ = List.app (fn (n,t) =>
  (check (n ^ " closed") (null (free_vars t));
   check (n ^ " no old recursive predicates") (not (has_const old_names t)))) named_args;
val _ = check "63 cases" (length case_terms = 63);
val _ = List.app (fn t => check "closed Boolean antecedent" (closed_bool t)) case_terms;
val _ = check "antecedent order" (ListPair.allEq (fn (a,b) => aconv a b)
  (case_terms,map (close_except []) (strip_conj(fst(dest_imp instantiated_induction)))));

(* The partition is zero-based, exactly as in bodySimFullMain. *)
val families =
 [("expr",[28,29,30,31,32,33,34,35,37]),
  ("stmt",[0,1,2,5,6,7,8,9,10,11,12,13,14,15,16,17,18,21]),
  ("control",[19,20,22,23,24,25,26,27]),
  ("traversal",List.tabulate(15,fn i => 48+i)),
  ("call",[39,40,42,43,44,45,46,47]),
  ("builtin",[36,38]),("frame",[3,4,41])];
val partition = List.concat(map #2 families);
val _ = check "family coverage without overlap"
  (length partition = 63 andalso List.all (fn i =>
    length (List.filter (fn j => j=i) partition) = 1) (List.tabulate(63,I)));

(* Forgetting precisely the new conjunction recovers every original scope:
   marks/res/ee/target-exit witnesses, actual storage trace, valid H and Q/R.
   This also checks the expanded frame-return callbacks, not just expr_sim. *)
fun forget_ledger tm =
  if is_conj tm andalso same_const (fst(strip_comb (fst(dest_conj tm))))
      ``gas_origin_ptr_path`` then fst(dest_conj tm)
  else if is_comb tm then let val(f,x)=dest_comb tm
       in mk_comb(forget_ledger f,forget_ledger x) end
  else if is_abs tm then let val(v,b)=dest_abs tm
       in mk_abs(v,forget_ledger b) end
  else tm;
val _ = check "gas alternatives and scopes"
  (aconv (forget_ledger (snd causal_gas_equation)) gas_rhs);
val _ = List.app (fn (_,rhs) => check "simulation/callback scopes"
  (aconv (forget_ledger (causal rhs))
         (expand (sim_equations @ [(gas_lhs,gas_rhs)]) rhs))) sim_equations;
val _ = check "ledger has actual marked replay and exact stopping boundary"
  (has_const ["gas_explicit"] ledger andalso has_const ["erase_storage_trace"] ledger
   andalso has_const ["active_inst"] ledger andalso has_const ["IntRet"] ledger
   andalso has_const ["lower_budget_certificate"] ledger
   andalso has_const ["empty_failed_outcome"] ledger);
val _ = check "no synthetic admissibility guards"
  (not (has_const ["source_storage_ok","call_outcomes_storage_ok","source_exempt",
     "storage_trace_domain","valid_horizon","gas_admissible"] ledger));

val equation_checks =
 [(expr_base_exists_tm,causal_expr_base_exists),
  (expr_base_equations_tm,causal_expr_base_equations),
  (tuple_exists_tm,causal_tuple_exists),
  (tuple_equations_tm,causal_tuple_equations),
  (list_equations_tm,causal_list_equations)];
val _ = List.app (fn (t,th) =>
  (check "closed equation theorem" (closed_bool t andalso null (hyp th));
   check "literal production interface" (aconv t (concl th)))) equation_checks;

(* These are literal generated terms, available to all family owners via the
   library; the log exposes them for scope/interface review without assertions. *)
val _ = List.app (fn (n,t) => print ("ARGUMENT " ^ n ^ "\n" ^ term_to_string t ^ "\n")) named_args;
val _ = List.app (fn (n,is) => print ("FAMILY " ^ n ^ ": " ^
  String.concatWith "," (map Int.toString is) ^ "\n")) families;
val _ = List.app (fn i => print ("CASE " ^ Int.toString i ^ "\n" ^
  term_to_string (List.nth(case_terms,i)) ^ "\n")) (List.tabulate(63,I));
val _ = print ("LEDGER normal/IntRet/nonreturning\n" ^ term_to_string ledger ^ "\n");
val _ = print ("All causal syntax and production recursion interface checks passed.\n");
