(* Closed causal quotations.  This module constructs terms only. *)
structure loweringBudgetCausalSyntaxLib =
struct
open HolKernel boolSyntax;
open bodyFullPredsTheory loweringCallBudgetHistoryTheory sourceCallCountWitnessTheory;

fun close_except keep tm =
  list_mk_forall (List.filter (fn v => not (List.exists (aconv v) keep)) (free_vars tm),tm);
fun equation th = dest_eq (snd (strip_forall (concl th)));
fun beta tm =
  if is_comb tm then
    let val (f,x) = dest_comb tm
        val f' = beta f and x' = beta x
    in if is_abs f' then beta (subst [fst(dest_abs f') |-> x'] (snd(dest_abs f')))
       else mk_comb(f',x') end
  else if is_abs tm then let val (v,b)=dest_abs tm in mk_abs(v,beta b) end
  else tm;
fun replace_consts pairs tm = beta (subst pairs tm);
fun rewrite_eq (lhs,rhs) tm =
  let val (ts,tys) = match_term lhs tm
  in SOME (subst ts (inst tys rhs)) end handle HOL_ERR _ => NONE;
fun expand eqs tm =
  case get_first (fn eq => rewrite_eq eq tm) eqs of
    SOME t => expand eqs t
  | NONE => if is_comb tm then
      let val (f,x)=dest_comb tm in beta (mk_comb(expand eqs f,expand eqs x)) end
    else if is_abs tm then let val (v,b)=dest_abs tm in mk_abs(v,expand eqs b) end
    else tm;

val (gas_lhs,gas_rhs) = equation gasOutcomeFullTheory.gas_outcome_full_def;
fun gasvar n = valOf (List.find (fn v => fst(dest_var v)=n) (all_vars gas_rhs @ all_vars gas_lhs));
val [df,lo,explicit,ctx,func,pg,es,s,g,tn,source,marks,res,ee,r,g',tn',h] =
  map gasvar ["DF","lo","explicit","ctx","func","PG","es","s","G","tn","source","marks","res","ee","r","G'","tn'","H"];
val ledger = ``
 (!f i. MEM f ^ctx.ctx_functions /\ MEM i (fn_insts f) ==>
          ~MEM i.inst_opcode [CREATE;CREATE2]) ==>
 !os zs rr ee_z rest.
   ^es.outcomes = SOME os /\
   zs = TAKE (LENGTH zs) os ++ REPLICATE (LENGTH zs - LENGTH os) empty_failed_outcome /\
   ^source (^es with <|outcomes := SOME zs;
     gas_obs := gas_explicit ^marks ^s.vs_gas_readings|>) = (rr,ee_z) /\
   ee_z.outcomes = SOME rest /\ rest <> [] ==>
   rr = ^res /\
   erase_storage_trace ee_z =
     erase_storage_trace (^ee with <|outcomes := SOME rest; gas_obs := []|>) /\
   (!t. ^r = OK t /\ (?i. active_inst ^func i t) ==>
     ?hc. lower_budget_path F (^df ^h,^lo,^explicit,^ctx)
       <|bp_stack:=[]; bp_params:=^pg; bp_prov:=^g; bp_taint:=^tn;
         bp_fn:=^func; bp_state:=^s|> hc ^marks
       <|bp_stack:=[]; bp_params:=^pg; bp_prov:=^g'; bp_taint:=^tn';
         bp_fn:=^func; bp_state:=t|> /\
       lower_history_count hc + LENGTH rest = LENGTH zs) /\
   (exit_result ^r ==>
     (!hc ms q. lower_budget_path F (^df ^h,^lo,^explicit,^ctx)
       <|bp_stack:=[]; bp_params:=^pg; bp_prov:=^g; bp_taint:=^tn;
         bp_fn:=^func; bp_state:=^s|> hc ms q ==>
       lower_history_count hc + (case ^r of IntRet v t => LENGTH rest | _ => 0)
         <= LENGTH zs) /\
     (!v t hc gc tc. ^r = IntRet v t /\
       lower_budget_certificate (^df ^h,^lo,^explicit,^ctx)
       <|bp_stack:=[]; bp_params:=^pg; bp_prov:=^g; bp_taint:=^tn;
         bp_fn:=^func; bp_state:=^s|> hc ^marks (INR (^r,gc,tc)) ==>
       lower_history_count hc + LENGTH rest = LENGTH zs))``;
fun insert_ledger tm =
  if same_const (fst(strip_comb tm)) ``gas_origin_ptr_path`` then mk_conj(tm,ledger)
  else if is_comb tm then let val(f,x)=dest_comb tm in mk_comb(insert_ledger f,insert_ledger x) end
  else if is_abs tm then let val(v,b)=dest_abs tm in mk_abs(v,insert_ledger b) end
  else tm;
val causal_gas_equation = (gas_lhs,insert_ledger gas_rhs);
val sim_equations = map equation
  [bodySimFullTheory.expr_map_sim_full_def,bodySimFullTheory.expr_sim_full_def,
   bodySimFullTheory.expr_vv_sim_full_def,bodySimFullTheory.stmt_frag_full_def,
   bodySimFullTheory.frame_ret_ok_full_def];
fun causal tm = expand (sim_equations @ [causal_gas_equation]) tm;

val cx = ``cx : evaluation_context``;
val e = ``e : expr``;
val bt = ``bt : base_assignment_target``;
val ep = ``E : expr -> bool``;
val bp = ``B : base_assignment_target -> bool``;
fun exprs_fold p = ``\cx es. FOLDR (\e acc. ^p cx e /\
  ((?s tv t s1 v t1. eval_expr cx e s = (INL tv,t) /\
     read_result cx tv s1 = (INL v,t1)) ==> acc)) T es``;
fun results_fold p = ``\cx es. FOLDR (\e acc. ^p cx e /\
  ((?s res t. eval_expr cx e s = (INL res,t)) ==> acc)) T es``;
val free_expr = ``\(cx:evaluation_context) e. ^ep e``;
val free_base = ``\(cx:evaluation_context) t. ^bp t``;
val recursive_subst =
  [``body_expr_full_ok`` |-> free_expr,
   ``body_exprs_full_ok`` |-> exprs_fold free_expr,
   ``body_base_target_full_ok`` |-> free_base];
val expr_eq = hd (strip_conj (concl bodyFullPredsTheory.body_expr_full_ok_def));
val base_eqs = strip_conj (concl bodyFullPredsTheory.body_base_target_full_ok_def);
val expr_base_body = list_mk_conj (map (close_except [cx,ep,bp] o
  replace_consts recursive_subst o causal o snd o strip_forall) (expr_eq::base_eqs));
val expr_base_pred = list_mk_abs([cx,ep,bp],expr_base_body);
val (expr_var,expr_equation) = dest_forall (hd (strip_conj expr_base_body));
val expr_conjuncts = strip_conj (rhs expr_equation);
val expr_nonrecursive = list_mk_abs([cx,expr_var],
  mk_conj(hd expr_conjuncts,List.nth(expr_conjuncts,2)));
val p = ``p : (expr -> bool) # (base_assignment_target -> bool)``;
val expr_base_exists_tm = ``!cx. ?p. ^expr_base_pred cx (FST p) (SND p)`` |> beta;
val selected_pair = ``\cx. @p. ^expr_base_pred cx (FST p) (SND p)`` |> beta;
val B_expr = ``\cx e. FST (^selected_pair cx) e`` |> beta;
val B_base = ``\cx t. SND (^selected_pair cx) t`` |> beta;
val B_exprs = exprs_fold B_expr |> beta;
val B_results = results_fold B_expr |> beta;
val expr_base_equations_tm = ``!cx. ^expr_base_pred cx (^B_expr cx) (^B_base cx)`` |> beta;

fun tuples_fold f = ``\cx gs. FOLDR
 (\g k vs. case vs of [] => T | v::rest => ^f cx g v /\
      ((?s x t. assign_tuple_targets cx g v s = (INL x,t)) ==> k rest))
 (\vs. T) gs``;
val tf = mk_var("tf", ``:assignment_target -> value -> bool``);
val free_tuple = ``\(cx:evaluation_context) g v. ^tf g v``;
val tuple_subst =
 [``body_tuple_target_full_ok`` |-> free_tuple,
  ``body_tuple_targets_full_ok`` |-> tuples_fold free_tuple,
  ``body_base_target_full_ok`` |-> B_base];
val tuple_body = list_mk_conj (map (close_except [cx,tf] o replace_consts tuple_subst o snd o strip_forall)
  (List.take(strip_conj(concl bodyFullPredsTheory.body_tuple_target_full_ok_def),2)));
val tuple_pred = list_mk_abs([cx,tf],tuple_body);
val tuple_exists_tm = ``!cx. ?f. ^tuple_pred cx f`` |> beta;
val selected_tuple = ``\cx. @f. ^tuple_pred cx f`` |> beta;
val B_tuple = ``\cx g v. ^selected_tuple cx g v`` |> beta;
val B_tuples = tuples_fold B_tuple |> beta;
val tuple_equations_tm = ``!cx. ^tuple_pred cx (^B_tuple cx)`` |> beta;

val replacements = [``body_expr_full_ok`` |-> B_expr,
 ``body_exprs_full_ok`` |-> B_exprs,``body_results_full_ok`` |-> B_results,
 ``body_base_target_full_ok`` |-> B_base,``body_tuple_target_full_ok`` |-> B_tuple,
 ``body_tuple_targets_full_ok`` |-> B_tuples];
fun direct th = let val(l,r)=equation th
 in (fst(strip_comb l), pairSyntax.list_mk_pabs(snd(strip_comb l),
      replace_consts replacements (causal r))) end;
val (stmt_const,B_stmt) = direct bodyFullPredsTheory.body_stmt_full_ok_def;
val (stmts_const,B_stmts) = direct bodyFullPredsTheory.body_stmts_full_ok_def;
val stmt_replacements = (stmt_const |-> B_stmt)::(stmts_const |-> B_stmts)::replacements;
val iterator_equations = map (fn t => let val(l,r)=dest_eq (snd(strip_forall t)) in
  (l, replace_consts stmt_replacements (causal r)) end)
  (strip_conj(concl bodyFullPredsTheory.body_iterator_full_ok_def));
val B_iterator = ``\cx it. case it of Array e => ^B_expr cx e
 | Range e1 e2 => ^B_expr cx e1 /\
    ((?s tv t s1 v t1. eval_expr cx e1 s = (INL tv,t) /\
      read_result cx tv s1 = (INL v,t1)) ==> ^B_expr cx e2)`` |> beta;
val B_for = let val(l,r)=equation bodyFullPredsTheory.body_for_full_ok_def
 in pairSyntax.list_mk_pabs(snd(strip_comb l),replace_consts stmt_replacements r) end;
val induction_args = [B_stmt,B_stmts,B_iterator,B_for,B_expr,B_exprs,
 B_base,B_base,B_tuple,B_tuples,B_results];
val (ind_vars,ind_body) = strip_forall(concl vyperInterpreterTheory.evaluate_ind);
val instantiated_induction = beta (subst (ListPair.map (fn(v,t)=> v |-> t)
 (ind_vars,induction_args)) ind_body);
val case_terms = map (close_except []) (strip_conj(fst(dest_imp instantiated_induction)));

val list_equations_tm = ``
 (!cx. ^B_exprs cx [] = T) /\
 (!cx e es. ^B_exprs cx (e::es) =
    (^B_expr cx e /\ ((?s tv t s1 v t1. eval_expr cx e s = (INL tv,t) /\
         read_result cx tv s1 = (INL v,t1)) ==> ^B_exprs cx es))) /\
 (!cx. ^B_results cx [] = T) /\
 (!cx e es. ^B_results cx (e::es) =
    (^B_expr cx e /\ ((?s res t. eval_expr cx e s = (INL res,t)) ==> ^B_results cx es))) /\
 (!cx vs. ^B_tuples cx [] vs = T) /\
 (!cx g gs. ^B_tuples cx (g::gs) [] = T) /\
 (!cx g gs v vs. ^B_tuples cx (g::gs) (v::vs) =
    (^B_tuple cx g v /\ ((?s x t. assign_tuple_targets cx g v s = (INL x,t)) ==>
       ^B_tuples cx gs vs)))`` |> beta;
end
