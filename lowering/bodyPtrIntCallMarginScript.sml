(* Allocation charge available at an internal-call boundary. *)
Theory bodyPtrIntCallMargin
Ancestors exprLoweringProps relation finite_map pred_set list arithmetic words
  bodySim exprSimHyps compileEnv compileVyper loweringShapeProps

Theorem alloca_room_call_margin:
  !ctx func s finish margin callee.
    alloca_room ctx func s /\
    fn_directly_calls ctx func.fn_name callee /\
    finish <= s.vs_alloca_next /\ margin <= unit_alloca_frame ctx ==>
    finish + margin < dimword (:256)
Proof
  rpt strip_tac >> fs[alloca_room_def] >>
  `TC (fn_directly_calls ctx) func.fn_name callee` by
    metis_tac[TC_SUBSET] >>
  `0 < CARD {g | TC (fn_directly_calls ctx) func.fn_name g}` by
    (spose_not_then assume_tac >>
     `CARD {g | TC (fn_directly_calls ctx) func.fn_name g} = 0` by decide_tac >>
     ` {g | TC (fn_directly_calls ctx) func.fn_name g} = {}` by
       metis_tac[CARD_EQ_0] >>
     fs[EXTENSION]) >>
  `unit_alloca_frame ctx <=
   CARD {g | TC (fn_directly_calls ctx) func.fn_name g} *
     unit_alloca_frame ctx` by
    (Cases_on `CARD {g | TC (fn_directly_calls ctx) func.fn_name g}` >>
     fs[MULT_CLAUSES]) >>
  decide_tac
QED

(* Both runtime and deploy compilation check every internal declaration. *)
Theorem body_inv_internal_allocs_ok:
  body_inv tops ctx cenv cx /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops ==>
  fn_allocs_ok tops (mut,nr,rr,name,args,dflts,ret,ss)
Proof
  rpt strip_tac >>
  `MEM (mut,nr,rr,name,args,dflts,ret,ss)
     (FST (SND (classify_functions tops)))` by
    simp[MEM_classify_internal] >>
  gvs[body_inv_def] >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >> gvs[] >>
  Cases_on `cx.in_deploy` >> gvs[] >>
  metis_tac[lower_vyper_runtime_unit_allocs_ok,
            lower_vyper_deploy_unit_allocs_ok]
QED

(* The caller's coherent type metadata suffices; no callee ghost is needed
   to establish the size bound before invoking the body induction. *)
Theorem body_inv_internal_return_size:
  body_inv tops ctx cenv cx /\
  expr_sim_inv cenv cx env es /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  evaluate_type (get_tenv cx) ret = SOME tv ==>
  type_memory_size tv + 64 < dimword (:256)
Proof
  rpt strip_tac >>
  drule_all body_inv_internal_allocs_ok >>
  simp[fn_allocs_ok_def] >> strip_tac >>
  `type_memory_bytes cenv ret = type_memory_size tv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `cenv.ce_struct_fields =
   (build_compile_env tops Internal mut name args ret ss F).ce_struct_fields` by
    gvs[body_inv_def, build_compile_env_ce_struct_fields] >>
  drule type_memory_bytes_frame >> strip_tac >>
  gvs[] >> fs[dimword_def]
QED
