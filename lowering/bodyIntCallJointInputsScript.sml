(* Narrow compiler-entry bridges for the joint statement producer. *)
Theory bodyIntCallJointInputs
Ancestors
  bodyIntCallJointEntry bodyIntCallSemanticEntry allocLimitsProps
  compileVyper compileEnv intCallCallee bodySim list pair

Theorem packaged_internal_prologue_alloc_env_agree:
  set_internal_package_target target
    (package_internal_fn tops use_trans nkeys is_ctor imm_size
      (mut,nr,rr,name,args,dflts,ret,ss)) =
    (lbl,ce,params,has_rb,is_nr,key,trans,view,ctor,imm_len,ss',rt) /\
  compile_internal_prologue ce params has_rb rt st0 = ((ce2,pc),st1) ==>
  alloc_env_agree
    (build_compile_env tops Internal mut name args ret ss F)
    (ce2 with ce_alloca_locals := T)
Proof
  strip_tac >> drule compile_internal_prologue_fields >>
  simp[compile_env_component_equality] >> strip_tac >>
  gvs[package_internal_fn_def, set_internal_package_target_def,
      update_cenv_nonreentrant_def] >>
  simp[alloc_env_agree_def, build_compile_env_def, ELIM_UNCURRY]
QED
