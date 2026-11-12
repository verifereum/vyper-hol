Theory runtimeSymSrcFunctionLists
Ancestors
  runtimeSymSrcEmissionProbe moduleLowering compileEnv loweringShapeDefs list

Theorem runtime_sym_internal_fn_bodies:
  !xs.
    (!lbl ce params rb nr key trans view ctor len body rt s u s'.
       MEM (lbl,ce,params,rb,nr,key,trans,view,ctor,len,body,rt) xs /\
       EVERY P (state_insts s) /\
       compile_internal_function ce params rb nr key trans view ctor len body rt s = (u,s') ==>
       EVERY P (state_insts s')) ==>
    !s u s'. EVERY P (state_insts s) /\
      compile_internal_fn_bodies xs s = (u,s') ==>
      EVERY P (state_insts s')
Proof
  Induct
  >- simp[compile_internal_fn_bodies_def, comp_return_def] >>
  gen_tac >> PairCases_on `h` >> rpt strip_tac >>
  gvs[compile_internal_fn_bodies_def, comp_ignore_bind_def, comp_bind_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  `EVERY P (state_insts cs')` by
    (mp_tac (runtime_sym_new_block |> Q.INST [`label` |-> `h0`, `st` |-> `s`]) >> simp[]) >>
  qpat_assum `!lbl ce params rb nr key trans view ctor len body rt s s'. _`
    (drule_at (Pat `compile_internal_function _ _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!lbl. _` (qspec_then `h0` mp_tac) >>
  simp_tac bool_ss [] >> strip_tac >>
  qpat_x_assum `_ ==> !s s'. _` mp_tac >>
  impl_tac
  >- (rpt strip_tac >> first_x_assum irule >> simp[] >> metis_tac[]) >>
  disch_then drule_all >> simp[]
QED

Theorem runtime_sym_external_fn_bodies:
  !xs.
    EVERY (\(lbl,ce,args,cds,payable,nr,key,trans,view,body,rt).
      (!s u s'. EVERY P (state_insts s) /\
         compile_entry_checks cds payable s = (u,s') ==>
         EVERY P (state_insts s')) /\
      (!s u s'. EVERY P (state_insts s) /\
         compile_external_function_body ce args nr key trans view body rt s = (u,s') ==>
         EVERY P (state_insts s'))) xs ==>
    !s u s'. EVERY P (state_insts s) /\
      compile_external_fn_bodies xs s = (u,s') ==>
      EVERY P (state_insts s')
Proof
  Induct
  >- simp[compile_external_fn_bodies_def, comp_return_def] >>
  gen_tac >> PairCases_on `h` >> rpt strip_tac >>
  gvs[compile_external_fn_bodies_def, comp_ignore_bind_def, comp_bind_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  `EVERY P (state_insts cs')` by
    (mp_tac (runtime_sym_new_block |> Q.INST [`label` |-> `h0`, `st` |-> `s`]) >> simp[]) >>
  metis_tac[]
QED
