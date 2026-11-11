(* Positional static annotations of effect-free call arguments. *)
Theory bodyIntCallCompilerListTags
Ancestors bodyIntCallCompilerTags exprLowering context compileEnv

Theorem intcall_compile_multi_vvs_tags:
  !es sa vvs sb.
    EVERY (\e. ~expr_has_effect e) es /\
    compile_multi_vvs compile_expr ce es sa = (vvs,sb) ==>
    MAP vv_type vvs = MAP expr_type es
Proof
  Induct >> simp[compile_multi_vvs_def, comp_return_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[compile_multi_vvs_def, comp_bind_def, comp_return_def,
      pairTheory.ELIM_UNCURRY] >>
  conj_tac
  >- (irule intcall_compile_expr_tag >> simp[]) >>
  first_x_assum irule >> simp[] >> metis_tac[pairTheory.PAIR]
QED
