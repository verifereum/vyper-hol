Theory bodyIntCallInvokeExistence
Ancestors
  bodyIntCallPackageBoundary intCallLookup bodySim compileVyper
  venomExecSemantics venomInst

Theorem body_inv_internal_lookup_nonempty:
  !tops ctx ce cx mut nr rr name args dflts ret ss.
  body_inv tops ctx ce cx /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops ==>
  ?callee.
    lookup_function
      (internal_fn_label (ce.ce_func_ids (nsid_to_string (NONE,name)))
        (nsid_to_string (NONE,name))
        (ce.ce_func_param_types (nsid_to_string (NONE,name))) ce.ce_is_ctor)
      ctx.ctx_functions = SOME callee /\ ~NULL callee.fn_blocks
Proof
  rpt gen_tac >> strip_tac >>
  `internal_fn_label (ce.ce_func_ids (nsid_to_string (NONE,name)))
     (nsid_to_string (NONE,name))
     (ce.ce_func_param_types (nsid_to_string (NONE,name))) ce.ce_is_ctor =
   FST (package_internal_fn tops F (K 0) ce.ce_is_ctor 0
     (mut,nr,rr,name,args,dflts,ret,ss))` by
    (irule internal_call_package_label >> gvs[body_inv_def]) >>
  asm_rewrite_tac[package_internal_fn_call_label] >>
  qpat_x_assum `body_inv _ _ _ _` mp_tac >>
  simp[body_inv_def] >> strip_tac >> gvs[] >>
  Cases_on `cx.in_deploy` >> gvs[]
  >- (drule_all lower_vyper_deploy_unit_internal_lookup >>
      strip_tac >> simp[compileEnvTheory.nsid_to_string_def] >>
      simp[vyperCompilerTheory.mk_internal_function_metadata, listTheory.NULL_EQ]) >>
  drule_all lower_vyper_runtime_unit_internal_lookup >>
  strip_tac >> simp[compileEnvTheory.nsid_to_string_def] >>
  simp[vyperCompilerTheory.mk_internal_function_metadata, listTheory.NULL_EQ]
QED

Theorem body_inv_internal_invoke_entry:
  !tops ctx cenv cx mut rr name args ret ss t func bb inst ops argv.
  body_inv tops ctx cenv cx /\
  MEM (FunctionDecl Internal mut F rr name args [] ret ss) tops /\
  ~t.vs_halted /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME
    (internal_fn_label (cenv.ce_func_ids (nsid_to_string (NONE,name)))
      (nsid_to_string (NONE,name))
      (cenv.ce_func_param_types (nsid_to_string (NONE,name))) cenv.ce_is_ctor,ops) /\
  eval_operands ops t = SOME argv ==>
  ?callee entered. gas_invoke_entry (ctx,func) t callee entered
Proof
  rpt gen_tac >> strip_tac >>
  drule_all body_inv_internal_lookup_nonempty >> strip_tac >>
  `?setup. setup_callee callee argv t = SOME setup` by
    simp[setup_callee_def] >>
  drule_all body_inv_gas_invoke_entry >> metis_tac[]
QED
