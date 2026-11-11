(* Primitive projections for the common internal-call staging endpoint. *)
Theory bodyIntCallSeamPrefixSupport
Ancestors
  bodyIntCallStageDistinctReturn bodyIntCallPackageEntryInterface
  bodyIntCallArgPrefixFrame bodyIntCallMetadata bodyIntCallStageDescriptors
  vyperInterpreter vyperState
  compileEnv venomExecSemantics venomState list pair

Theorem compute_pass_via_stack_word_flags:
  !tys n. LIST_REL (\ty flag. flag ==> is_word_type ty)
    tys (compute_pass_via_stack tys n)
Proof
  Induct >> simp[compute_pass_via_stack_def] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[]
QED

Theorem body_internal_decl_staging_flags:
  body_inv tops ctx ce cx /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret bd) tops /\
  ce.ce_func_info (nsid_to_string (NONE,name)) = (rcn,rbs,pvs) ==>
  LENGTH pvs = LENGTH args /\
  LIST_REL (\ty flag. flag ==> is_word_type ty) (MAP SND args) pvs
Proof
  strip_tac >>
  drule_all bodyIntCallPkgEntryMetadataTheory.body_internal_decl_pass_flags >>
  simp[LENGTH_compute_pass_via_stack, compute_pass_via_stack_word_flags]
QED


Theorem intcall_arg_staging_layout:
  expr_body_pre ce cx env e es ==>
  type_memory_bytes ce (expr_type e) < dimword(:256) /\
  ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
       type_memory_bytes ce (expr_type e) = type_memory_size tv
Proof
  strip_tac >>
  drule exprSimHypsTheory.expr_body_pre_type_evaluates >>
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  `expr_sim_inv ce cx env es` by fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
  `type_memory_bytes ce (expr_type e) = type_memory_size x` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  Cases_on `is_word_type (expr_type e)`
  >- (drule_all entryDecodeStaticPropsTheory.word_type_memory_size >>
      simp[wordsTheory.dimword_def]) >>
  drule_all exprSimHypsTheory.expr_body_pre_copy_ok >>
  simp[wordsTheory.dimword_def]
QED

Theorem intcall_arg_list_staging_layout:
  EVERY (\e. expr_body_pre ce cx env e es /\ ~expr_has_effect e) args /\
  compile_multi_vvs compile_expr ce args sa = (vals,sb) /\
  LENGTH raws = LENGTH args ==>
  EVERY (\(ty,raw,vv). vv_type vv = ty /\
    type_memory_bytes ce ty < dimword(:256) /\
    ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
         type_memory_bytes ce ty = type_memory_size tv)
    (MAP (\(e,(raw,vv)). (expr_type e,raw,vv))
      (ZIP(args,ZIP(raws,vals))))
Proof
  strip_tac >>
  `EVERY (\e. ~expr_has_effect e) args` by fs[EVERY_MEM] >>
  drule_all bodyIntCallCompilerListTagsTheory.intcall_compile_multi_vvs_tags >>
  qpat_x_assum `compile_multi_vvs _ _ _ _ = _` kall_tac >>
  qpat_x_assum `LENGTH raws = _` mp_tac >>
  qpat_x_assum `EVERY (\e. expr_body_pre _ _ _ _ _ /\ _) _` mp_tac >>
  qid_spec_tac `vals` >> qid_spec_tac `raws` >>
  Induct_on `args`
  >- simp[] >>
  gen_tac >> disch_tac >> rpt gen_tac >>
  Cases_on `raws` >> Cases_on `vals` >> simp[] >>
  rpt disch_tac >> gvs[] >>
  drule intcall_arg_staging_layout >> strip_tac >> simp[] >>
  first_x_assum irule >> simp[]
QED

(* Normalize only the administrative source prefix; k is the untouched
   callee/rest continuation, not an alternate definition of the seam. *)
Theorem intcall_source_read_bind_push:
  read_results cx raws es = (INL vals,es) /\
  bind_arguments (get_tenv cx) args vals = SOME penv /\
  evaluate_type (get_tenv cx) ret = SOME rtv ==>
  (do prev <- get_scopes;
      vs <- read_results cx raws;
      env <- lift_option_type (bind_arguments (get_tenv cx) args vs)
        "IntCall bind_arguments";
      rt <- lift_option_type (evaluate_type (get_tenv cx) ret)
        "IntCall eval ret";
      lock_if_nr cx F (is_view_mut mut);
      cxf <- push_function id env cx;
      k prev rt cxf
   od) es =
  k es.scopes rtv (cx with stk updated_by CONS id) (es with scopes := [penv])
Proof
  strip_tac >>
  simp[get_scopes_def, bind_def, return_def, lift_option_type_def,
       lock_if_nr_def, push_function_def, ignore_bind_def]
QED

(* The held-list representation is a zip, not a second source evaluation. *)
Theorem intcall_held_list_projections:
  !xs ys zs f. LENGTH ys = LENGTH xs /\ LENGTH zs = LENGTH xs ==>
  MAP (\(ty,raw,vv). ty)
    (MAP (\(e,(raw,vv)). (f e,raw,vv)) (ZIP(xs,ZIP(ys,zs)))) = MAP f xs /\
  MAP (\(ty,raw,vv). raw)
    (MAP (\(e,(raw,vv)). (f e,raw,vv)) (ZIP(xs,ZIP(ys,zs)))) = ys /\
  MAP (\(ty,raw,vv). vv)
    (MAP (\(e,(raw,vv)). (f e,raw,vv)) (ZIP(xs,ZIP(ys,zs)))) = zs
Proof
  Induct >> rpt gen_tac >> Cases_on `ys` >> Cases_on `zs` >> simp[]
QED
