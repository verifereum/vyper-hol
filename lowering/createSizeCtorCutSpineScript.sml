(* The actual callback and snapshot rows of constructor argument lowering. *)
Theory createSizeCtorCutSpine
Ancestors
  exprLowering compileEnv list pair

Theorem create_ctor_cut_spine:
  !es a vals b.
    compile_create_ctor_args cfn ce es a = (vals,b) ==>
    ?cs mid vs.
      LENGTH cs = SUC (LENGTH es) /\ HD cs = a /\ LAST cs = b /\
      LENGTH mid = LENGTH es /\ LENGTH vs = LENGTH es /\
      LENGTH vals = LENGTH es /\
      !i. i < LENGTH es ==>
        cfn ce (expr_type (EL i es)) (EL i es) (EL i cs) =
          (EL i vs, EL i mid) /\
        compile_snapshot_vv ce (exprs_can_mutate ce (DROP (SUC i) es))
          (ext_call_arg_value (lowered_value_type ce (EL i es)) (EL i vs))
          (EL i mid) = (EL i vals, EL (SUC i) cs)
Proof
  Induct_on `es`
  >- (simp[compile_create_ctor_args_def,comp_return_def] >>
      rpt strip_tac >> qexists `[a]` >> simp[]) >>
  qx_gen_tac `e` >> rpt gen_tac >>
  Cases_on `cfn ce (expr_type e) e a` >>
  rename1 `cfn ce (expr_type e) e a = (v,m)` >>
  Cases_on `compile_snapshot_vv ce (exprs_can_mutate ce es)
    (ext_call_arg_value (lowered_value_type ce e) v) m` >>
  rename1 `compile_snapshot_vv ce _ _ m = (x,n)` >>
  Cases_on `compile_create_ctor_args cfn ce es n` >>
  rename1 `compile_create_ctor_args cfn ce es n = (xs,t)` >>
  simp[Once compile_create_ctor_args_def,comp_bind_def,comp_return_def] >>
  strip_tac >> gvs[] >>
  first_x_assum (drule_then strip_assume_tac) >>
  Cases_on `cs` >> gvs[] >>
  qmatch_goalsub_rename_tac `LAST (n::ss)` >>
  qexistsl_tac [`a::n::ss`,`m::mid`,`v::vs`] >> simp[] >>
  Cases >> simp[]
QED
