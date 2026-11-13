(* Memory case of the body induction (bodyMemory's body_mem_mutual):
   subscript. *)
Theory bodyMemSubscript
Ancestors
  bodyMemoryPreds bodyMemSubscriptArray bodyMemSubscriptTuple
  bodyMemSubscriptMismatch bodySubscriptMappingMemory bodyExprForceMemory
  bodySimExprCases exprSimPlaces exprLowering compileEnv

(* A mapping base reads no base value (map_base_no_overlap), so the
   read-gated index premise gives the plain one the mapping cases take. *)
Theorem map_base_gated_premise[local]:
  expr_map_pre cenv cx env e1 es /\
  (!s'' res t s3 res' t'.
     eval_expr cx e1 s'' = (INL res,t) /\
     (if subscript_reads_base cx e1 e2 then
        bind (read_result cx res) (\v. return (Value v))
      else return res) s3 = (INL res',t') ==>
     body_expr_mem_ok cx e2) ==>
  !s tv t. eval_expr cx e1 s = (INL tv,t) ==> body_expr_mem_ok cx e2
Proof
  rpt strip_tac >>
  `?kt vt. type_place_expr env e1 = SOME (HashMapT kt vt)` by
    fs[exprSimMapDefsTheory.expr_map_pre_def] >>
  drule_then (qspecl_then [`cenv`, `e2`, `cx`] strip_assume_tac)
    exprSimSubscriptMapTheory.map_base_no_overlap >>
  first_x_assum (qspecl_then [`s`, `tv`, `t`, `t`, `tv`, `t`] mp_tac) >>
  gs[vyperStateTheory.return_def]
QED

Theorem body_subscript_mem_case:
  !cx v8 e1 e2.
    (!s'' res t s3 res' t'.
       eval_expr cx e1 s'' = (INL res,t) /\
       (if subscript_reads_base cx e1 e2 then
          bind (read_result cx res) (\v. return (Value v))
        else return res) s3 = (INL res',t') ==>
       body_expr_mem_ok cx e2) /\
    body_expr_mem_ok cx e1 ==>
    body_expr_mem_ok cx (Subscript v8 e1 e2)
Proof
  rpt strip_tac >> simp[Once body_expr_mem_ok_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule expr_body_pre_subscript_base_type >> strip_tac >>
      `expr_vv_sim_mem ctx func cenv cx ty (Subscript v8 e1 e2) es` by
        (Cases_on `place_type cenv e1`
         >- (drule_all_then assume_tac
               exprSimSubscriptMapTheory.expr_body_pre_map_subscript_base >>
             drule_all_then assume_tac map_base_gated_premise >>
             metis_tac[body_subscript_map_vv_mem]) >>
         rename1 `ValPT bt` >> Cases_on `bt <> expr_type e1`
         >- metis_tac[compile_subscript_mismatch_vv_sim_mem] >>
         gvs[] >> drule_all subscript_base_array_or_tuple >> strip_tac
         >- metis_tac[body_subscript_array_vv_mem] >>
         metis_tac[body_subscript_tuple_vv_mem]) >>
      simp[] >> irule body_expr_sim_mem_of_vv_sim_mem >>
      simp[] >> conj_tac
      >- (rpt gen_tac >> strip_tac >>
          qpat_x_assum `compile_expr _ _ (Subscript _ _ _) _ = _` mp_tac >>
          Cases_on `place_type cenv e1`
          >- (simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def,
                   compile_subscript_def, comp_bind_def, comp_return_def] >>
              rpt (pairarg_tac >> gvs[])) >>
          rename1 `place_type cenv e1 = ValPT bt` >> Cases_on `bt` >>
          simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def,
               compile_subscript_def, comp_bind_def, comp_return_def] >>
          rpt (pairarg_tac >> gvs[])) >>
      goal_assum drule) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule_all_then assume_tac exprSimSubscriptMapTheory.expr_map_pre_subscript_base >>
  drule_all_then assume_tac map_base_gated_premise >>
  metis_tac[body_subscript_map_mem]
QED
