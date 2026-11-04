(* Selected external compilation slices, before runtime embedding. *)
Theory entryRuntimeSlice
Ancestors
  moduleLowering compileEnv list

Theorem compile_external_fn_bodies_append[local]:
  !xs ys st.
    compile_external_fn_bodies (xs ++ ys) st =
    compile_external_fn_bodies ys (SND (compile_external_fn_bodies xs st))
Proof
  Induct >> simp[compile_external_fn_bodies_def, comp_return_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[compile_external_fn_bodies_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem compile_external_fn_bodies_member:
  MEM (lbl, cenv0, pos_args, min_cds, is_payable, is_nr, nkey, ut,
       iv, fbody, rt) packages /\
  compile_external_fn_bodies packages start = ((), st_final) ==>
  ?pre post sb old sc sd cenv sa se.
    packages = pre ++
      (lbl, cenv0, pos_args, min_cds, is_payable, is_nr, nkey, ut,
       iv, fbody, rt) :: post /\
    compile_external_fn_bodies pre start = ((), sb) /\
    new_block lbl sb = (old, sc) /\
    compile_entry_checks min_cds is_payable sc = ((), sd) /\
    compile_register_positional_args cenv0 pos_args 4 sd = (cenv, sa) /\
    compile_guarded_body cenv is_nr nkey ut iv fbody rt sa = ((), se) /\
    compile_external_fn_bodies post se = ((), st_final)
Proof
  strip_tac >>
  qpat_x_assum `MEM _ _` mp_tac >>
  rewrite_tac[MEM_SPLIT] >> strip_tac >> gvs[] >>
  fs[compile_external_fn_bodies_append, compile_external_fn_bodies_def,
     compile_external_function_body_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  qexistsl [`l1`, `l2`] >>
  Cases_on `compile_external_fn_bodies l1 start` >> gvs[] >>
  metis_tac[]
QED
