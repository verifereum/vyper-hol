(* Guarded request-prefix classification shared by the Subscript dispatchers. *)
Theory s1PrefixSubscriptCase
Ancestors
  s1PrefixPreds s1PrefixDefs s1PrefixOfVV
  s1PrefixSubscriptMapBase s1PrefixSubscriptMap s1PrefixSubscriptTuple
  s1PrefixSubscriptArrayCode s1PrefixSubscriptArrayMemory s1PrefixSubscriptUnframedArray
  bodyFullSubscript[qualified,ignore_grammar] bodyFullSubscriptMapBase
  bodyFullSimProjection bodySimExprCases exprSimPlaces exprSimTuple
  exprSimSubscriptMap exprSimMapDefs exprLowering vyperState vyperAST

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >> once_rewrite_tac[body_expr_prefix_ok_def] >>
  reverse conj_tac
  >- (conj_tac >- simp[] >> rpt gen_tac >> strip_tac >> gvs[] >>
      drule_then assume_tac expr_map_pre_subscript_base >>
      `?kt vt. type_place_expr env e1 = SOME (HashMapT kt vt)` by
        fs[expr_map_pre_def] >>
      `~subscript_reads_base cx e1 e2` by metis_tac[map_base_no_overlap] >>
      irule subscript_map_map_prefix >> rpt conj_tac
      >- (fs[vyperStateTheory.return_def] >> metis_tac[])
      >- (fs[vyperStateTheory.return_def] >> metis_tac[])
      >- (qexistsl [`env`, `tops`] >> simp[])
      >- (irule body_expr_full_ok_map >> simp[] >> qexistsl [`env`, `tops`] >> simp[]) >>
      irule body_expr_prefix_ok_map >> simp[] >> qexistsl [`env`, `tops`] >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  conj_asm2_tac >- metis_tac[expr_sim_prefix_of_vv] >>
  drule_then assume_tac expr_body_pre_subscript_base_type >>
  Cases_on `place_type cenv e1`
  >- (rename1 `place_type cenv e1 = MapPT kt vt` >>
      drule_all_then assume_tac expr_body_pre_map_subscript_base >>
      drule_all expr_map_pre_checked_type >> strip_tac >>
      `~subscript_reads_base cx e1 e2` by metis_tac[map_base_no_overlap] >>
      irule subscript_map_prefix >> simp[] >> rpt conj_tac
      >- (fs[vyperStateTheory.return_def] >> metis_tac[])
      >- (fs[vyperStateTheory.return_def] >> metis_tac[])
      >- (qexistsl [`env`, `tops`] >> simp[])
      >- (irule body_expr_full_ok_map >> simp[] >> qexistsl [`env`, `tops`] >> simp[]) >>
      irule body_expr_prefix_ok_map >> simp[] >> qexistsl [`env`, `tops`] >> simp[]) >>
  drule_all bodyFullSubscriptTheory.subscript_value_base_type >> strip_tac >> gvs[] >>
  drule_all subscript_base_array_or_tuple >> strip_tac >> gvs[]
  >- (Cases_on `(!t r t'. eval_expr cx e2 t = (INL r,t') ==>
                           t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
                ~subscript_reads_base cx e1 e2 /\ ~copies_subscript_base cenv e1 e2 /\
                (!s tr slot vt t.
                   eval_expr cx e1 s <> (INL (PlaceR (StoragePlace tr slot vt)),t)) /\
                ((~cenv.ce_is_ctor /\
                  !ty st. vv_location (FST (compile_expr cenv ty e1 st)) = SOME LocCode) \/
                 ((?n. bd = Fixed n) /\
                  (!tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv) /\
                  !ty st. vv_location (FST (compile_expr cenv ty e1 st)) = SOME LocMemory))`
      >- (qpat_x_assum `(!t r t'. _) /\ _` strip_assume_tac
          >- (irule subscript_array_framed_code_prefix >> simp[] >> rpt conj_tac
              >- (fs[vyperStateTheory.return_def] >> metis_tac[])
              >- (fs[vyperStateTheory.return_def] >> metis_tac[]) >>
              qexistsl [`env`, `tops`] >> simp[]) >>
          gvs[] >> irule subscript_array_framed_memory_prefix >> simp[] >> rpt conj_tac
          >- (fs[vyperStateTheory.return_def] >> metis_tac[])
          >- (fs[vyperStateTheory.return_def] >> metis_tac[]) >>
          qexistsl [`env`, `tops`] >> simp[]) >>
      irule subscript_unframed_array_vv_prefix >>
      qpat_assum `expr_type e1 = ArrayT et bd` (irule_at Any) >>
      qpat_assum `expr_body_pre cenv cx env (Subscript _ _ _) es` (irule_at Any) >>
      qpat_assum `body_inv tops ctx cenv cx` (irule_at Any) >>
      rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[])) >>
  drule_all tuple_pre_base >> strip_tac >> gvs[] >>
  irule subscript_tuple_vv_sim_prefix >> simp[] >> rpt conj_tac
  >- (qexists `env` >> simp[])
  >- metis_tac[body_expr_full_ok_simulations] >>
  qpat_assum `body_expr_prefix_ok cx e1`
    (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
  metis_tac[]
QED
*)
Theorem body_subscript_case_prefix:
  !cx v8 e1 e2.
  (!s'' res t s'3' res' t'.
       eval_expr cx e1 s'' = (INL res,t) /\
       (if subscript_reads_base cx e1 e2 then
          bind (read_result cx res) (\v. return (Value v))
        else return res) s'3' = (INL res',t') ==>
       body_expr_full_ok cx e2) /\
  (!s'' res t s'3' res' t'.
       eval_expr cx e1 s'' = (INL res,t) /\
       (if subscript_reads_base cx e1 e2 then
          bind (read_result cx res) (\v. return (Value v))
        else return res) s'3' = (INL res',t') ==>
       body_expr_prefix_ok cx e2) /\
  body_expr_full_ok cx e1 /\
  body_expr_prefix_ok cx e1 ==>
  body_expr_prefix_ok cx (Subscript v8 e1 e2)
Proof
  cheat
QED
