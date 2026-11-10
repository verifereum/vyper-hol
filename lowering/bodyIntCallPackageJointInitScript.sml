(* Joint resources at the packaged callee's body boundary. *)
Theory bodyIntCallPackageJointInit
Ancestors
  bodyIntCallPackageRoot bodyIntCallPackageRootResource
  bodyIntCallPackageRootSemantic bodyIntCallPackageInputs bodyIntCallPackageGeometry
  bodyIntCallActualJointInit bodyIntCallActualEntrySemantic
  bodyIntCallActualEntryFields bodyIntCallActualEntryProtection
  bodyIntCallJointInputs bodyIntCallEntryInputs bodyIntCallSeamDefs
  bodyIntCallJointContract bodyIntCallActualEntryWitness bodySim
  compileVyper compileEnv vyperContext vyperState venomState list pair

Theorem intcall_entry_joint_res:
  body_inv tops ctx cenv cx /\ cenv_module_pins tops cenv /\
  MEM (FunctionDecl Internal mut F rr name args [] ret ss) tops /\
  intcall_entry tops ctx func cenv cx tenv name es sa sb vv s0 es0
    (mut,args,ret,ss,rr) prev penv rtv es1 t /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,arg_ops) /\ eval_operands arg_ops t = SOME argv /\
  lookup_function lbl ctx.ctx_functions = SOME callee /\
  setup_callee callee argv t = SOME entered /\
  cenv.ce_func_info (nsid_to_string (NONE,name)) = (nret,rbs,pvs) /\
  set_internal_package_target cenv.ce_target
    (package_internal_fn tops use_trans (nkeys:string->num) cenv.ce_is_ctor ilen
      (mut,F,rr,name,args,([]:expr list),ret,ss)) =
    (label,ce,params,has_rb,is_nr,key,trans,view,ctor,ilen',ss',rt) /\
  compile_internal_function_entry ce params has_rb ctor ilen' rt entry =
    ((ce2,rpc,imm),body_start) /\
  fn_has_code entry body_start callee /\ fn_inst_ids_distinct callee /\
  run_inst_seq (emitted_insts entry body_start) entered = OK u /\
  (!a k. P a k <=> a + k <= t.vs_alloca_next /\
    !aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==> regions_disjoint a k off asz) /\
  (!b z. staged b z <=> ?i po.
    i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po z) /\
    b = w2n (EL ((if has_rb then 1 else 0) + i) argv)) /\
  intcall_frame_ok fp /\ fp.jc_ctx = ctx /\ fp.jc_func = callee /\
  fp.jc_cx = (cx with stk updated_by CONS (NONE,name)) /\
  fp.jc_root_ce = (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>) /\
  fp.jc_oorig = u /\ fp.jc_morig = t /\ fp.jc_lo = t.vs_alloca_next /\
  fp.jc_prot = P /\ fp.jc_staged = staged /\
  fp.jc_rb = (if has_rb then SOME (HD argv,type_memory_size rtv) else NONE) /\
  (!op x. fp.jc_reserved op /\ op = Var x ==> not_fresh_at body_start x) /\
  env.current_src = NONE /\ env.type_defs = get_tenv cx /\
  env.fn_sigs = tenv.fn_sigs /\ env.bare_globals = tenv.bare_globals /\
  env.bare_global_assignable = tenv.bare_global_assignable /\
  env.toplevel_vtypes = tenv.toplevel_vtypes /\ env.flag_members = tenv.flag_members /\
  (!n ty. MEM (n,ty) args ==> FLOOKUP env.var_types n = SOME ty) /\
  (!n ty. FLOOKUP env.var_types n = SOME ty ==> MEM (n,ty) args) /\
  env_consistent env (cx with stk updated_by CONS (NONE,name)) es1 ==>
  intcall_joint_res fp fp.jc_root_ce env es1 body_start
    (u with vs_inst_idx := LENGTH body_start.cs_current_insts)
Proof
  strip_tac >>
  drule_all intcall_entry_package_inputs >> strip_tac >>
  drule_all intcall_entry_package_separation >> strip_tac >>
  drule_all intcall_entry_root_geometry >> strip_tac >>
  drule_all packaged_internal_entry_return_fields >> strip_tac >>
  drule_all intcall_entry_root_expr_inv >> strip_tac >>
  drule_all packaged_internal_entry_locals_declared >> strip_tac >>
  drule_all body_inv_internal_allocs_ok >> strip_tac >>
  drule_all packaged_internal_entry_locals_alloc_ok >> strip_tac >>
  `supported_function_body tops Internal args ss` by
    (drule_at (Pat `MEM (FunctionDecl _ _ _ _ _ _ _ _ _) _`)
       supported_programTheory.supported_program_function >> fs[body_inv_def]) >>
  drule_all packaged_internal_entry_reserved >> strip_tac >>
  drule intcall_entry_source >> strip_tac >>
  `es1 with scopes := [penv] = es1` by simp[evaluation_state_component_equality] >>
  qpat_assum `es1 with scopes := [penv] = es1`
    (fn th => once_rewrite_tac[GSYM th]) >>
  irule internal_entry_joint_res_init >>
  rpt conj_tac >> simp[state_rel_call_stack]
QED
