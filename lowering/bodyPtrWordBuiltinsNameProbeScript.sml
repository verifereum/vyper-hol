(* The proposed raw stack-Name witness is ruled out by expr_sim_inv. *)
Theory bodyPtrWordBuiltinsNameProbe
Ancestors
  exprSimNameValue exprSimHypsDefs exprLowering compileEnv
  vyperTypeSystem finite_map

Theorem typed_name_compiles_memory_probe:
  !cenv cx env ann id es ty sa.
    expr_sim_inv cenv cx env es /\ well_typed_expr env (Name ann id) ==>
    ?p sz.
      FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
      compile_expr cenv ty (Name ann id) sa =
        (LocatedValue ann (mk_ptr (Var p) LocMemory), sa)
Proof
  rpt strip_tac >>
  `?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    (gvs[expr_sim_inv_def, well_typed_expr_def] >> metis_tac[]) >>
  qexistsl_tac [`p`, `sz`] >> simp[] >> irule compile_name_value_ptr >> simp[]
QED
