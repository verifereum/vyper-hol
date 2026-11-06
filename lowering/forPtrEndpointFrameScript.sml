(* Endpoint transport at the expression interface.  Word provenance is
   independent of taint cleanliness and must be transported explicitly. *)
Theory forPtrEndpointFrame
Ancestors wordArgsPtr exprSimWordArgs stmtFragPtr stmtSimProps
  bodyPtrDefs ptrDiscipline compileEnv loweringPosts venomState
  exprLoweringProps finite_map list vyperInterpreter vyperState
Libs monadsyntax

Theorem ghost_kept_operand_prov:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  (!x. op = Var x ==> not_fresh_at sa x) ==>
  op_prov G op = op_prov G0 op
Proof
  Cases_on `op` >> simp[op_prov_def, ghost_kept_def] >> metis_tac[]
QED

(* Prepending one expression prefix to an arbitrary checked tail needs only
   its old-variable frame, not the stronger memory clauses of ghost_kept. *)
Theorem for_endpoint_prefix_frame:
  sa.cs_next_var <= sb.cs_next_var /\
  wb_frame cenv es sa s0 s1 /\
  ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
  (!x w. not_fresh_at sb x /\ lookup_var x s1 = SOME w ==>
    lookup_var x s2 = SOME w) /\
  (!x. not_fresh_at sb x ==> FLOOKUP G2 x = FLOOKUP G1 x /\
    op_taint tn2 (Var x) = op_taint tn1 (Var x)) ==>
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
    lookup_var x s2 = SOME w) /\
  (!x. not_fresh_at sa x ==> FLOOKUP G2 x = FLOOKUP G0 x /\
    op_taint tn2 (Var x) = op_taint tn0 (Var x))
Proof
  strip_tac >> conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sb x` by
        (irule stmtFragPtrTheory.not_fresh_at_mono >> goal_assum (drule_at Any) >> simp[]) >>
      `lookup_var x s1 = SOME w` by (drule_all wb_frame_vars >> simp[]) >>
      first_x_assum irule >> simp[]) >>
  fs[ghost_kept_def] >> rpt strip_tac >>
  `not_fresh_at sb x` by
    (irule stmtFragPtrTheory.not_fresh_at_mono >> goal_assum (drule_at Any) >> simp[]) >>
  metis_tac[]
QED

(* Source normalization at precisely the two forced-expression boundaries. *)
Theorem for_endpoint_iterator_source:
  !cx e1 e2.
  eval_iterator cx (Range e1 e2) =
  do v1 <- (do raw <- eval_expr cx e1; read_result cx raw od);
     v2 <- (do raw <- eval_expr cx e2; read_result cx raw od);
     rl <- lift_sum (get_range_limits v1 v2);
     return (GENLIST (\j. IntV (FST rl + &j)) (SND rl)) od
Proof
  rpt gen_tac >> simp[Once evaluate_def, FUN_EQ_THM, bind_def] >>
  qx_gen_tac `es` >> Cases_on `eval_expr cx e1 es` >>
  rename1 `_ = (raw1, es1)` >> Cases_on `raw1` >> simp[] >>
  rename1 `read_result cx tv1 es1` >>
  Cases_on `read_result cx tv1 es1` >> rename1 `_ = (r1, es2)` >>
  Cases_on `r1` >> simp[] >>
  Cases_on `eval_expr cx e2 es2` >> rename1 `_ = (raw2, es3)` >>
  Cases_on `raw2` >> simp[] >>
  rename1 `read_result cx tv2 es3` >>
  Cases_on `read_result cx tv2 es3` >> rename1 `_ = (r2, es4)` >>
  Cases_on `r2` >> simp[]
QED

Theorem for_endpoint_stmt_source:
  !cx fty tyv id e1 e2 bound body.
  evaluate_type (get_tenv cx) fty = SOME tyv ==>
  eval_stmt cx (For id fty (Range e1 e2) bound body) =
  do v1 <- (do raw <- eval_expr cx e1; read_result cx raw od);
     v2 <- (do raw <- eval_expr cx e2; read_result cx raw od);
     rl <- lift_sum (get_range_limits v1 v2);
     check (compatible_bound (Dynamic bound) (SND rl)) "For too long";
     eval_for cx tyv id body
       (GENLIST (\j. IntV (FST rl + &j)) (SND rl)) od
Proof
  rpt gen_tac >> strip_tac >> pure_once_rewrite_tac[Once evaluate_def] >>
  simp[LET_THM, lift_option_type_def, for_endpoint_iterator_source,
       bind_assoc, bind_return, LENGTH_GENLIST]
QED
