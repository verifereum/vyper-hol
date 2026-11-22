(* The evaluator induction with an additional rule for the syntax of a
 * selected internal callee after environment-dependent transformations. *)
Theory entryCreateEvalInd
Ancestors
  vyperInterpreter vyperContext vyperState vyperAST alist list pred_set arithmetic

Theorem remcode_keys_push[local]:
  set (MAP FST (remcode (cx with stk updated_by CONS k))) =
  set (MAP FST (remcode cx)) DELETE k
Proof
  Cases_on `k` >> simp[remcode_def] >>
  Cases_on `ALOOKUP cx.sources cx.txn.target` >>
  simp[EXTENSION, MEM_MAP, MEM_FILTER, pairTheory.EXISTS_PROD] >>
  gen_tac >> rename1 `_ ⇔ _ ∧ key ≠ _` >> Cases_on `key` >>
  simp[] >> metis_tac[]
QED

Theorem remcode_rank_push[local]:
  CARD (set (MAP FST (remcode (cx with stk updated_by CONS k)))) <=
  CARD (set (MAP FST (remcode cx)))
Proof
  simp[remcode_keys_push, CARD_DELETE] >> rw[]
QED

Theorem callable_key_remaining[local]:
  ~MEM (src,fn) cx.stk /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,ss) /\
  (dflts,ss) <> ([],[]) ==>
  (src,fn) IN set (MAP FST (remcode cx))
Proof
  strip_tac >>
  drule_all_then (qspec_then `src` assume_tac) lookup_callable_function_eq_ALOOKUP_module_fns >>
  gvs[get_module_code_def, AllCaseEqs()] >>
  drule_all ALOOKUP_FLAT_MAP_module_fns >> strip_tac >>
  drule ALOOKUP_MEM >> strip_tac >>
  simp[remcode_def, MEM_MAP, MEM_FILTER, pairTheory.EXISTS_PROD] >>
  metis_tac[]
QED

Theorem callable_rank_push[local]:
  ~MEM (src,fn) cx.stk /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,ss) /\
  (dflts,ss) <> ([],[]) ==>
  CARD (set (MAP FST (remcode (cx with stk updated_by CONS (src,fn))))) <
  CARD (set (MAP FST (remcode cx)))
Proof
  strip_tac >> drule_all callable_key_remaining >> strip_tac >>
  pure_rewrite_tac[remcode_keys_push] >> irule CARD_PSUBSET >>
  simp[PSUBSET_DEF, EXTENSION] >> qexists_tac `(src,fn)` >> simp[]
QED

(* Derive the schema from evaluate_ind, retaining even the evaluator's two
 * distinct predicates on base targets.  Only the IntCall clause changes. *)
val (ind_vars, ind_body) = strip_forall (concl evaluate_ind);
val (ind_hyps, ind_concl) = dest_imp ind_body;
val ind_cases = strip_conj ind_hyps;
val [_, p_stmts, _, _, _, p_exprs, _, _, _, _] = ind_vars;
fun case_result tm =
  let val (_,body) = strip_forall tm in
    if is_imp body then snd (dest_imp body) else body
  end;
fun ast_ctor name tm =
  is_const tm andalso
  let val {Thy,Name,...} = dest_thy_const tm
  in Thy = "vyperAST" andalso Name = name end;
fun intcall_decomposition tm =
  case strip_comb (case_result tm) of
    (_, [cx,e]) =>
      (case strip_comb e of
         (c,[_,target,_,_]) =>
           (case strip_comb target of
              (t,[key]) =>
                if ast_ctor "Call" c andalso ast_ctor "IntCall" t
                then SOME (cx,key) else NONE
            | _ => NONE)
       | _ => NONE)
  | _ => NONE;
fun is_intcall_case tm = isSome (intcall_decomposition tm);
val _ = case List.filter is_intcall_case ind_cases of
          [_] => () | _ => raise Fail "expected one evaluator IntCall clause";
fun add_pushed_ih tm =
  case intcall_decomposition tm of NONE => tm | SOME (cx,key) =>
  let
    val (vars, body) = strip_forall tm
    val (pre, post) = dest_imp body
    val (src,fname) = pairSyntax.dest_pair key
    val extra = ``!ts mut nr args dflts ret ss B D.
      ~MEM ^key (^cx).stk /\ get_module_code ^cx ^src = SOME ts /\
      lookup_callable_function (^cx).in_deploy ^fname ts =
        SOME (mut,nr,args,dflts,ret,ss) /\ B [] = [] /\ D [] = [] ==>
      ^p_stmts (^cx with stk updated_by CONS ^key) (B ss) /\
      ^p_exprs (^cx with stk updated_by CONS ^key) (D dflts)``
  in list_mk_forall (vars, mk_imp (mk_conj (pre,extra), post)) end;
val pushed_hyps = list_mk_conj (map add_pushed_ih ind_cases);

val rank = ``rank:num``;
fun ranked_predicate clause =
  let val (args, result) = strip_forall clause
      val cx = hd args
  in list_mk_abs (args, mk_imp
       (``CARD (set (MAP FST (remcode ^cx))) <= ^rank``, result))
  end;
val ranked_ind =
  BETA_RULE (ISPECL (map ranked_predicate (strip_conj ind_concl)) evaluate_ind);
val ranked_concl = snd (dest_imp (concl ranked_ind));

fun prove_original_ih simps =
  qpat_x_assum `!m:num. m < rank ==> _` kall_tac >>
  qpat_assum `CARD (set (MAP FST (remcode cx))) <= rank` (fn bound =>
    RULE_ASSUM_TAC (SIMP_RULE bool_ss (bound :: simps)) >>
    SIMP_TAC bool_ss simps) >>
  first_assum ACCEPT_TAC;

fun nil_case_for p th =
  case strip_comb (case_result (concl th)) of
    (q,[_,xs]) => aconv p q andalso listSyntax.is_nil xs
  | _ => false;

(* The conjunct order is inherited from the same evaluator theorem on both
 * sides of the case transfer.  No handwritten list of branch positions. *)
fun prove_ranked_cases closures =
  let
    val cases = CONJUNCTS closures
    val nil_cases = map (fn p => valOf (List.find (nil_case_for p) cases))
                        [p_stmts,p_exprs]
    fun branch th =
      if is_intcall_case (concl th) then
        assume_tac th >> map_every assume_tac nil_cases >> suspend "intcall"
      else rpt strip_tac >> irule th >> rpt conj_tac >> prove_original_ih []
    fun prove [] = ALL_TAC
      | prove [th] = branch th
      | prove (th :: rest) = conj_tac >- branch th >> prove rest
  in prove cases end;

Theorem entry_create_evaluate_ranked:
  ^(list_mk_forall (ind_vars, mk_imp (pushed_hyps, mk_forall (rank, ranked_concl))))
Proof
  rpt gen_tac >> disch_then (fn closures =>
    completeInduct_on `rank` >> match_mp_tac ranked_ind >> prove_ranked_cases closures)
QED

Resume entry_create_evaluate_ranked[intcall]:
  rpt strip_tac >> first_x_assum match_mp_tac >> reverse conj_tac
  >- (rpt gen_tac >> strip_tac >> Cases_on `(dflts,ss) = ([],[])`
      >- (qpat_x_assum `(dflts,ss) = ([],[])`
            (strip_assume_tac o REWRITE_RULE [pairTheory.PAIR_EQ]) >>
          asm_rewrite_tac[]) >>
      `CARD (set (MAP FST (remcode (cx with stk updated_by CONS (src_id_opt,fn))))) < rank`
        by (irule LESS_LESS_EQ_TRANS >> goal_assum (drule_at Any) >>
            drule_all callable_rank_push >> simp[]) >>
      qpat_x_assum `!m:num. m < rank ==> _` (drule_then strip_assume_tac) >>
      conj_tac >> first_x_assum irule >> simp[]) >>
  `CARD (set (MAP FST (remcode (cx with stk updated_by CONS (src_id_opt,fn))))) <= rank`
    by (irule LESS_EQ_TRANS >> goal_assum (drule_at Any) >> simp[remcode_rank_push]) >>
  qpat_assum `CARD (set (MAP FST (remcode (_ with stk updated_by CONS _)))) <= rank`
    (fn bound => rpt conj_tac >> prove_original_ih
      [bound, push_function_def, return_def, pairTheory.PAIR_EQ, sumTheory.INL_11])
QED

Finalise entry_create_evaluate_ranked[local]

Theorem entry_create_evaluate_ind:
  ^(list_mk_forall (ind_vars, mk_imp (pushed_hyps, ind_concl)))
Proof
  rpt gen_tac >> disch_then (assume_tac o MATCH_MP entry_create_evaluate_ranked) >>
  rpt conj_tac >> qx_gen_tac `cx` >> rpt gen_tac >>
  first_x_assum (qspec_then `CARD (set (MAP FST (remcode cx)))` strip_assume_tac) >>
  first_x_assum irule >> simp[]
QED
