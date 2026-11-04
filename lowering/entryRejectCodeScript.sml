Theory entryRejectCode
Ancestors
  entryCodeOwnership entryRawFunction moduleLowering compileEnv list pair

Theorem compile_external_fn_bodies_append[local]:
  !xs ys.
  compile_external_fn_bodies (xs ++ ys) =
  comp_ignore_bind (compile_external_fn_bodies xs)
                   (compile_external_fn_bodies ys)
Proof
  Induct
  >- simp[compile_external_fn_bodies_def, comp_ignore_bind_def,
          FUN_EQ_THM, comp_bind_def, comp_return_def] >>
  qx_gen_tac `h` >> PairCases_on `h` >>
  simp[compile_external_fn_bodies_def, comp_ignore_bind_def, comp_bind_def,
       FUN_EQ_THM] >> rpt gen_tac >> rpt (pairarg_tac >> simp[])
QED

Theorem compile_external_fn_bodies_selected_checks:
  MEM (lbl,ce,pa,mc,pay,nr,key,tr,view,stmts,rt) fns /\
  compile_external_fn_bodies fns sa = ((),sz) ==>
  ?pre post sp sc sd sb.
    fns = pre ++ (lbl,ce,pa,mc,pay,nr,key,tr,view,stmts,rt)::post /\
    compile_external_fn_bodies pre sa = ((),sp) /\
    new_block lbl sp = (sp.cs_current_bb,sc) /\
    compile_entry_checks mc pay sc = ((),sd) /\
    compile_external_function_body ce pa nr key tr view stmts rt sd = ((),sb) /\
    compile_external_fn_bodies post sb = ((),sz)
Proof
  strip_tac >>
  drule (iffLR MEM_SPLIT) >> strip_tac >> gvs[] >>
  qpat_x_assum `compile_external_fn_bodies _ _ = _` mp_tac >>
  simp[compile_external_fn_bodies_append, compile_external_fn_bodies_def,
       comp_ignore_bind_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  qexistsl_tac [`l1`, `l2`] >> simp[] >>
  rpt (goal_assum (drule_at Any)) >> gvs[new_block_def]
QED
