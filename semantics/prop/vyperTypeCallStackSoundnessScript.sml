(*
 * Checked call-stack and callable graph invariants.
 *)

Theory vyperTypeCallStackSoundness
Ancestors
  alist list rich_list relation vyperContext vyperInterpreter
  vyperTypeCallGraph vyperTypeCallGraphSoundness

(* ===== Generic stack-path and relation closure infrastructure ===== *)

Definition call_stack_follows_def:
  call_stack_follows R [] = T /\
  call_stack_follows R [current] = T /\
  call_stack_follows R (current::parent::rest) =
    (R parent current /\ call_stack_follows R (parent::rest))
End

Theorem RTC_then_R_TC:
  RTC R x y /\ R y z ==> TC R x z
Proof
  metis_tac[RTC_CASES_TC, TC_RULES]
QED

Theorem call_stack_follows_push:
  call_stack_follows R (owner::ancestors) /\
  R owner callee ==>
  call_stack_follows R (callee::owner::ancestors)
Proof
  simp[call_stack_follows_def]
QED

Theorem call_stack_member_reaches_head:
  call_stack_follows R (owner::ancestors) /\
  MEM node (owner::ancestors) ==>
  RTC R node owner
Proof
  qid_spec_tac `owner` >>
  Induct_on `ancestors`
  >- simp[call_stack_follows_def] >>
  simp[call_stack_follows_def] >>
  rpt strip_tac >>
  gvs[] >>
  first_x_assum (qspec_then `h` mp_tac) >>
  simp[] >>
  metis_tac[RTC_RULES_RIGHT1]
QED

Theorem acyclic_stack_target_not_mem:
  irreflexive (TC R) /\
  call_stack_follows R (owner::ancestors) /\
  R owner callee ==>
  ~MEM callee (owner::ancestors)
Proof
  rpt strip_tac >>
  drule_all call_stack_member_reaches_head >>
  disch_then assume_tac >>
  drule_all RTC_then_R_TC >>
  disch_then assume_tac >>
  gvs[irreflexive_def]
QED

(* ===== Ownership of extracted internal calls ===== *)

Definition calls_follow_call_graph_def:
  calls_follow_call_graph edges owner calls <=>
    EVERY (call_edge_rel edges owner) calls
End

Theorem calls_follow_call_graph_nil[simp]:
  calls_follow_call_graph edges owner []
Proof
  simp[calls_follow_call_graph_def]
QED

Theorem calls_follow_call_graph_cons[simp]:
  calls_follow_call_graph edges owner (callee::calls) <=>
  call_edge_rel edges owner callee /\
  calls_follow_call_graph edges owner calls
Proof
  simp[calls_follow_call_graph_def]
QED

Theorem calls_follow_call_graph_append[simp]:
  calls_follow_call_graph edges owner (xs ++ ys) <=>
  calls_follow_call_graph edges owner xs /\
  calls_follow_call_graph edges owner ys
Proof
  simp[calls_follow_call_graph_def, EVERY_APPEND]
QED

Theorem calls_follow_call_graph_DROP:
  calls_follow_call_graph edges owner xs ==>
  calls_follow_call_graph edges owner (DROP n xs)
Proof
  simp[calls_follow_call_graph_def, EVERY_DROP]
QED

(* ===== Syntax extraction decomposition ===== *)

Theorem calls_follow_int_calls_IntCall[simp]:
  calls_follow_call_graph edges owner
    (int_calls_expr (Call ty (IntCall callee) args default_ret)) <=>
  call_edge_rel edges owner callee /\
  calls_follow_call_graph edges owner (int_calls_exprs args)
Proof
  simp[int_calls_expr_def]
QED

Theorem calls_follow_int_calls_exprs_nil[simp]:
  calls_follow_call_graph edges owner (int_calls_exprs [])
Proof
  simp[int_calls_expr_def]
QED

Theorem calls_follow_int_calls_exprs_cons[simp]:
  calls_follow_call_graph edges owner (int_calls_exprs (e::es)) <=>
  calls_follow_call_graph edges owner (int_calls_expr e) /\
  calls_follow_call_graph edges owner (int_calls_exprs es)
Proof
  simp[int_calls_expr_def]
QED

Theorem calls_follow_int_calls_opt_NONE[simp]:
  calls_follow_call_graph edges owner (int_calls_opt NONE)
Proof
  simp[int_calls_expr_def]
QED

Theorem calls_follow_int_calls_opt_SOME[simp]:
  calls_follow_call_graph edges owner (int_calls_opt (SOME e)) <=>
  calls_follow_call_graph edges owner (int_calls_expr e)
Proof
  simp[int_calls_expr_def]
QED

Theorem calls_follow_int_calls_target_Subscript[simp]:
  calls_follow_call_graph edges owner
    (int_calls_target (SubscriptTarget tgt e)) <=>
  calls_follow_call_graph edges owner (int_calls_target tgt) /\
  calls_follow_call_graph edges owner (int_calls_expr e)
Proof
  simp[int_calls_expr_def]
QED

Theorem calls_follow_int_calls_atarget_Tuple[simp]:
  calls_follow_call_graph edges owner
    (int_calls_atarget (TupleTarget tgts)) <=>
  calls_follow_call_graph edges owner (int_calls_atargets tgts)
Proof
  simp[int_calls_atarget_def]
QED

Theorem calls_follow_int_calls_atargets_cons[simp]:
  calls_follow_call_graph edges owner (int_calls_atargets (t::ts)) <=>
  calls_follow_call_graph edges owner (int_calls_atarget t) /\
  calls_follow_call_graph edges owner (int_calls_atargets ts)
Proof
  simp[int_calls_atarget_def]
QED

Theorem calls_follow_int_calls_iterator_Range[simp]:
  calls_follow_call_graph edges owner (int_calls_iterator (Range x y)) <=>
  calls_follow_call_graph edges owner (int_calls_expr x) /\
  calls_follow_call_graph edges owner (int_calls_expr y)
Proof
  simp[int_calls_iterator_def]
QED

Theorem calls_follow_int_calls_stmt_For[simp]:
  calls_follow_call_graph edges owner
    (int_calls_stmt (For vars anns iter invs body)) <=>
  calls_follow_call_graph edges owner (int_calls_iterator iter) /\
  calls_follow_call_graph edges owner (int_calls_stmts body)
Proof
  simp[int_calls_stmt_def]
QED

Theorem calls_follow_int_calls_stmt_If[simp]:
  calls_follow_call_graph edges owner (int_calls_stmt (If e yes no)) <=>
  calls_follow_call_graph edges owner (int_calls_expr e) /\
  calls_follow_call_graph edges owner (int_calls_stmts yes) /\
  calls_follow_call_graph edges owner (int_calls_stmts no)
Proof
  simp[int_calls_stmt_def, CONJ_ASSOC]
QED

Theorem calls_follow_int_calls_stmts_cons[simp]:
  calls_follow_call_graph edges owner (int_calls_stmts (s::ss)) <=>
  calls_follow_call_graph edges owner (int_calls_stmt s) /\
  calls_follow_call_graph edges owner (int_calls_stmts ss)
Proof
  simp[int_calls_stmt_def]
QED

Theorem calls_follow_function_int_calls[simp]:
  calls_follow_call_graph edges owner (function_int_calls dflts body) <=>
  calls_follow_call_graph edges owner (int_calls_exprs dflts) /\
  calls_follow_call_graph edges owner (int_calls_stmts body)
Proof
  simp[function_int_calls_def]
QED

Theorem calls_follow_int_calls_atarget_Base[simp]:
  calls_follow_call_graph edges owner
    (int_calls_atarget (BaseTarget tgt)) <=>
  calls_follow_call_graph edges owner (int_calls_target tgt)
Proof
  simp[int_calls_atarget_def]
QED

Theorem calls_follow_int_calls_atargets_nil[simp]:
  calls_follow_call_graph edges owner (int_calls_atargets [])
Proof
  simp[int_calls_atarget_def]
QED

Theorem calls_follow_int_calls_iterator_Array[simp]:
  calls_follow_call_graph edges owner (int_calls_iterator (Array e)) <=>
  calls_follow_call_graph edges owner (int_calls_expr e)
Proof
  simp[int_calls_iterator_def]
QED

Theorem calls_follow_int_calls_stmt_Assign[simp]:
  calls_follow_call_graph edges owner (int_calls_stmt (Assign tgt e)) <=>
  calls_follow_call_graph edges owner (int_calls_atarget tgt) /\
  calls_follow_call_graph edges owner (int_calls_expr e)
Proof
  simp[int_calls_stmt_def]
QED

Theorem calls_follow_int_calls_stmts_nil[simp]:
  calls_follow_call_graph edges owner (int_calls_stmts [])
Proof
  simp[int_calls_stmt_def]
QED

Theorem calls_follow_int_calls_exprs_DROP:
  calls_follow_call_graph edges owner (int_calls_exprs dflts) ==>
  calls_follow_call_graph edges owner (int_calls_exprs (DROP n dflts))
Proof
  qid_spec_tac `dflts` >>
  Induct_on `n` >>
  Cases >>
  simp[]
QED

(* ===== Callable lookup ownership boundary ===== *)

Theorem module_fns_ALOOKUP_SOME_decompose:
  ALOOKUP (module_fns src ts) (src,fn) = SOME (dflts,body) ==>
  ?vis mut nr raw args ret.
    (vis = Internal \/ vis = Deploy) /\
    MEM (FunctionDecl vis mut nr raw fn args dflts ret body) ts
Proof
  strip_tac >>
  drule ALOOKUP_MEM >>
  simp[module_fns_def, MEM_MAP, MEM_APPEND, MEM_FLAT, PULL_EXISTS] >>
  strip_tac
  >- (rename1 `MEM entry ts` >>
      Cases_on `entry` >> gvs[dest_Internal_Fn_def] >>
      rename1 `MEM (FunctionDecl vis mut nr raw name args defaults ret stmts) ts` >>
      Cases_on `vis` >> gvs[dest_Internal_Fn_def] >> metis_tac[]) >>
  rename1 `MEM entry ts` >>
  Cases_on `entry` >> gvs[dest_Deploy_Fn_def] >>
  rename1 `MEM (FunctionDecl vis mut nr raw name args defaults ret stmts) ts` >>
  Cases_on `vis` >> gvs[dest_Deploy_Fn_def] >> metis_tac[]
QED

Theorem lookup_callable_function_SOME_decompose:
  lookup_callable_function in_deploy fn ts =
    SOME (mut,nr,args,dflts,ret,body) ==>
  (dflts = [] /\ body = []) \/
  ?vis mut' nr' raw args' ret'.
    (vis = Internal \/ vis = Deploy) /\
    MEM (FunctionDecl vis mut' nr' raw fn args' dflts ret' body) ts
Proof
  strip_tac >>
  Cases_on `(dflts,body) = ([],[])`
  >- gvs[] >>
  disj2_tac >>
  drule_all lookup_callable_function_eq_ALOOKUP_module_fns >>
  strip_tac >>
  first_x_assum (qspec_then `ARB` assume_tac) >>
  drule module_fns_ALOOKUP_SOME_decompose >>
  metis_tac[]
QED

(* ===== Callable graph ownership and stack irrelevance ===== *)

Definition functions_follow_call_graph_def:
  functions_follow_call_graph edges cx <=>
    !src fn ts mut nr args dflts ret body.
      get_module_code cx src = SOME ts /\
      lookup_callable_function cx.in_deploy fn ts =
        SOME (mut,nr,args,dflts,ret,body) ==>
      EVERY
        (call_edge_rel edges (src,fn))
        (function_int_calls dflts body)
End

Theorem functions_follow_call_graph_stk:
  functions_follow_call_graph edges (cx with stk updated_by f) <=>
  functions_follow_call_graph edges cx
Proof
  simp[functions_follow_call_graph_def, get_module_code_def]
QED

Theorem functions_follow_call_graph_push_stk:
  functions_follow_call_graph edges
    (cx with stk updated_by CONS callee) <=>
  functions_follow_call_graph edges cx
Proof
  simp[functions_follow_call_graph_stk]
QED

Theorem checked_contract_functions_follow_call_graph:
  check_contract cx.in_deploy layouts cx.txn.target mods = SOME art /\
  ALOOKUP cx.sources cx.txn.target = SOME mods ==>
  functions_follow_call_graph (contract_call_edges mods) cx
Proof
  rw[functions_follow_call_graph_def] >>
  gvs[get_module_code_def] >>
  drule ALOOKUP_MEM >>
  disch_then assume_tac >>
  drule lookup_callable_function_SOME_decompose >>
  strip_tac
  >- simp[function_int_calls_def, int_calls_expr_def, int_calls_stmt_def] >>
  rw[EVERY_MEM, call_edge_rel_def] >>
  irule contract_call_edges_function >>
  metis_tac[]
QED

(* ===== Safety of calls in the syntax currently being evaluated ===== *)

Definition call_evaluation_safe_def:
  call_evaluation_safe cx calls <=>
    ?edges owner ancestors.
      cx.stk = owner::ancestors /\
      call_stack_follows (call_edge_rel edges) cx.stk /\
      irreflexive (TC (call_edge_rel edges)) /\
      functions_follow_call_graph edges cx /\
      calls_follow_call_graph edges owner calls
End

Theorem call_evaluation_safe_mono:
  call_evaluation_safe cx calls /\
  (!callee. MEM callee subcalls ==> MEM callee calls) ==>
  call_evaluation_safe cx subcalls
Proof
  rw[call_evaluation_safe_def] >>
  qexistsl_tac [`edges`, `owner`, `ancestors`] >> simp[] >>
  gvs[calls_follow_call_graph_def, EVERY_MEM]
QED

Theorem call_evaluation_safe_append_left:
  call_evaluation_safe cx (xs ++ ys) ==>
  call_evaluation_safe cx xs
Proof
  strip_tac >> irule call_evaluation_safe_mono >>
  qexists_tac `xs ++ ys` >> simp[]
QED

Theorem call_evaluation_safe_append_right:
  call_evaluation_safe cx (xs ++ ys) ==>
  call_evaluation_safe cx ys
Proof
  strip_tac >> irule call_evaluation_safe_mono >>
  qexists_tac `xs ++ ys` >> simp[]
QED

Theorem call_evaluation_safe_DROP:
  call_evaluation_safe cx calls ==>
  call_evaluation_safe cx (DROP n calls)
Proof
  qid_spec_tac `calls` >> Induct_on `n`
  >- simp[] >>
  Cases >> simp[] >> strip_tac >>
  first_x_assum irule >>
  irule call_evaluation_safe_mono >>
  qexists_tac `h::t` >> simp[]
QED

Theorem call_evaluation_safe_target_not_mem:
  call_evaluation_safe cx (callee::calls) ==>
  ~MEM callee cx.stk
Proof
  rw[call_evaluation_safe_def] >>
  qpat_x_assum `cx.stk = owner::ancestors` SUBST_ALL_TAC >>
  strip_tac >>
  drule_all call_stack_member_reaches_head >> strip_tac >>
  drule_all RTC_then_R_TC >>
  gvs[irreflexive_def]
QED

Theorem call_evaluation_safe_push_callable:
  call_evaluation_safe cx (callee::calls) /\
  callee = (src,fn) /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts =
    SOME (mut,nr,args,dflts,ret,body) ==>
  call_evaluation_safe
    (cx with stk updated_by CONS callee)
    (function_int_calls dflts body)
Proof
  rw[call_evaluation_safe_def] >>
  qexists_tac `edges` >>
  simp[functions_follow_call_graph_stk] >>
  conj_tac
  >- (qpat_x_assum `cx.stk = owner::ancestors` SUBST_ALL_TAC >>
      irule call_stack_follows_push >> simp[]) >>
  gvs[functions_follow_call_graph_def, calls_follow_call_graph_def] >>
  first_x_assum drule_all >>
  simp[function_int_calls_def, EVERY_APPEND]
QED

Theorem call_evaluation_safe_push_defaults:
  call_evaluation_safe cx (callee::calls) /\
  callee = (src,fn) /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts =
    SOME (mut,nr,args,dflts,ret,body) ==>
  call_evaluation_safe
    (cx with stk updated_by CONS callee)
    (int_calls_exprs dflts)
Proof
  strip_tac >>
  drule_all call_evaluation_safe_push_callable >>
  simp[function_int_calls_def] >>
  metis_tac[call_evaluation_safe_append_left]
QED

Theorem call_evaluation_safe_push_needed_defaults:
  call_evaluation_safe cx (callee::calls) /\
  callee = (src,fn) /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts =
    SOME (mut,nr,args,dflts,ret,body) ==>
  call_evaluation_safe
    (cx with stk updated_by CONS callee)
    (int_calls_exprs (DROP n dflts))
Proof
  strip_tac >>
  drule_all call_evaluation_safe_push_defaults >>
  rw[call_evaluation_safe_def] >>
  qexists_tac `edges` >> simp[] >>
  irule calls_follow_int_calls_exprs_DROP >> simp[]
QED

Theorem call_evaluation_safe_push_body:
  call_evaluation_safe cx (callee::calls) /\
  callee = (src,fn) /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts =
    SOME (mut,nr,args,dflts,ret,body) ==>
  call_evaluation_safe
    (cx with stk updated_by CONS callee)
    (int_calls_stmts body)
Proof
  strip_tac >>
  drule_all call_evaluation_safe_push_callable >>
  simp[function_int_calls_def] >>
  metis_tac[call_evaluation_safe_append_right]
QED

Theorem call_evaluation_safe_singleton:
  irreflexive (TC (call_edge_rel edges)) /\
  functions_follow_call_graph edges cx /\
  calls_follow_call_graph edges owner calls ==>
  call_evaluation_safe (cx with stk := [owner]) calls
Proof
  rw[call_evaluation_safe_def] >>
  qexists_tac `edges` >>
  simp[call_stack_follows_def, functions_follow_call_graph_stk]
QED

Theorem checked_contract_call_evaluation_safe_singleton:
  check_contract cx.in_deploy layouts cx.txn.target mods = SOME art /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  calls_follow_call_graph (contract_call_edges mods) owner calls ==>
  call_evaluation_safe (cx with stk := [owner]) calls
Proof
  rw[call_evaluation_safe_def] >>
  qexists_tac `contract_call_edges mods` >>
  simp[call_stack_follows_def, functions_follow_call_graph_stk] >>
  conj_tac
  >- (drule checked_contract_call_graph_irreflexive >> simp[]) >>
  drule_all checked_contract_functions_follow_call_graph >> simp[]
QED
