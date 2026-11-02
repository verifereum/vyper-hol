(* TOP-LEVEL: compile_bind_contains locates the actual code for both parts
   of an append-only compiler bind in its final containing function.
   Helper: cs_appends_result_extends exposes the returned compile states. *)
Theory compileAppendProps
Ancestors
  compileEnv fragExec

Theorem cs_appends_result_extends:
  !m cs ret cs'. cs_appends m /\ m cs = (ret,cs') ==> cs_extends cs cs'
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `cs_appends m` (mp_tac o REWRITE_RULE [cs_appends_def]) >>
  disch_then (qspecl_then [`cs`, `ret`, `cs'`] mp_tac) >> simp[]
QED

Theorem compile_bind_contains:
  !m f cs ret cs' func.
    cs_appends m /\ (!value. cs_appends (f value)) /\
    comp_bind m f cs = (ret,cs') /\ fn_has_code cs cs' func ==>
    ?value mid. m cs = (value,mid) /\ f value mid = (ret,cs') /\
      fn_has_code cs mid func /\ fn_has_code mid cs' func
Proof
  rpt gen_tac >> strip_tac >> Cases_on `m cs` >> rename1 `m cs = (value,mid)` >>
  `f value mid = (ret,cs')` by gvs[comp_bind_def] >>
  `cs_extends cs mid` by (drule_all cs_appends_result_extends >> simp[]) >>
  `cs_extends mid cs'` by
    (qpat_x_assum `!value. cs_appends (f value)` (qspec_then `value` mp_tac) >>
     simp_tac bool_ss [cs_appends_def] >>
     disch_then (qspecl_then [`mid`, `ret`, `cs'`] mp_tac) >> simp[]) >>
  drule_all fn_has_code_split >> strip_tac >> qexistsl_tac [`value`, `mid`] >> simp[]
QED
