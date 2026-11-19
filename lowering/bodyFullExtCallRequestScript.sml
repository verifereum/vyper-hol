Theory bodyFullExtCallRequest
Ancestors
  exprLowering compileEnv vyperInterpreter list

(* The source and compiler pick the same first gas keyword. The compiler
   state at that keyword is the result of compiling exactly its prefix. *)
Theorem extcall_gas_keyword_cut:
  !ks es vs sa vo go d sb v.
    LENGTH es = LENGTH vs /\
    compile_ext_call_kwargs cfn cenv rt ks es sa = ((vo,go,d),sb) /\
    ext_call_kwarg EKGas ks vs = SOME v ==>
    ?n op sm e sp.
      n < LENGTH ks /\ n < LENGTH es /\ EL n ks = EKGas /\
      EL n vs = v /\ EL n es = e /\ go = SOME op /\
      sm = SND (compile_ext_call_kwargs cfn cenv rt (TAKE n ks) (TAKE n es) sa) /\
      lower_value cfn cenv (BaseT (UintT 256)) e sm = (op,sp)
Proof
  Induct >> simp[ext_call_kwarg_def] >>
  qx_gen_tac `k` >> Cases >> Cases >> simp[ext_call_kwarg_def] >>
  rpt gen_tac >> strip_tac >>
  rename1 `compile_ext_call_kwargs cfn cenv rt (k::ks) (e::es) sa = _` >>
  Cases_on `compile_ext_call_kwarg cfn cenv rt k e sa` >>
  rename1 `compile_ext_call_kwarg _ _ _ _ _ _ = (kop,sk)` >>
  PairCases_on `kop` >>
  Cases_on `compile_ext_call_kwargs cfn cenv rt ks es sk` >>
  rename1 `compile_ext_call_kwargs _ _ _ ks es sk = (kw,sf)` >>
  PairCases_on `kw` >>
  Cases_on `k = EKGas`
  >- (gvs[ext_call_kwarg_def, compile_ext_call_kwargs_def, comp_bind_def,
          comp_return_def] >>
      qexists_tac `0` >> simp[compile_ext_call_kwargs_def, comp_return_def] >>
      gvs[compile_ext_call_kwarg_def, comp_bind_def, comp_return_def] >>
      pairarg_tac >> gvs[]) >>
  `go = kw1` by
    (Cases_on `k = EKValue` >>
     gvs[compile_ext_call_kwargs_def, comp_bind_def, comp_return_def]) >>
  fs[ext_call_kwarg_def] >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `SUC n` >>
  simp[listTheory.EL, compile_ext_call_kwargs_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> rename1 `compile_ext_call_kwargs _ _ _ _ _ _ = (prefix,_)` >>
  PairCases_on `prefix` >> gvs[comp_return_def] >> metis_tac[]
QED
