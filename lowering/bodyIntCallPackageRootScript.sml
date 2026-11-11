(* The actual packaged callee's root frame, instantiated at the body boundary. *)
Theory bodyIntCallPackageRoot
Ancestors
  bodyIntCallPackageRootResource bodyIntCallPackageRun bodyIntCallPackageSemantic
  bodyIntCallActualEntrySemantic allocLimitsProps bodySim vyperContext vyperState
  bodyIntCallInvokeEntry bodyIntCallActualJointInit compileVyper compileEnv
  bodyIntCallActualEntryProtection bodyIntCallActualEntryLanding
  bodyIntCallActualEntryWitness bodyIntCallPackageInputs bodyIntCallPackageGeometry
  bodyIntCallEntryInputs bodyIntCallSeamDefs bodyIntCallActualRootFrame list pair

Theorem intcall_entry_root_frame:
  body_inv tops ctx cenv cx /\ cenv_module_pins tops cenv /\
  MEM (FunctionDecl Internal mut F rr name args [] ret ss) tops /\
  call_stack_follows (call_edge_rel E) ((NONE,name)::cx.stk) /\
  irreflexive (TC (call_edge_rel E)) /\
  functions_follow_call_graph E (cx with stk updated_by CONS (NONE,name)) /\
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
    b = w2n (EL ((if has_rb then 1 else 0) + i) argv)) ==>
  ?fp. intcall_frame_ok fp /\
    fp.jc_tops = tops /\ fp.jc_ctx = ctx /\ fp.jc_func = callee /\
    fp.jc_cx = (cx with stk updated_by CONS (NONE,name)) /\
    fp.jc_owner = (NONE,name) /\ fp.jc_ancestors = cx.stk /\ fp.jc_edges = E /\
    fp.jc_ret_ty = ret /\ fp.jc_ret_tv = rtv /\
    fp.jc_lo = t.vs_alloca_next /\ fp.jc_morig = t /\ fp.jc_oorig = u /\
    fp.jc_root_ce = (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>) /\
    fp.jc_rpc = rpc /\ fp.jc_pc = entered.vs_return_pc_token /\
    fp.jc_rb = (if has_rb then SOME (HD argv,type_memory_size rtv) else NONE) /\
    fp.jc_prot = P /\ fp.jc_staged = staged /\
    fp.jc_reserved = (\op. op = rpc \/
      (?sz. (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>).
        ce_return_buf = SOME (PtrVar op sz)) \/
      (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>).ce_imm_alloca = SOME op) /\
    (!op x. fp.jc_reserved op /\ op = Var x ==> not_fresh_at body_start x)
Proof
  strip_tac >>
  drule_all intcall_entry_package_inputs >> strip_tac >>
  drule_all intcall_entry_root_geometry >> strip_tac >>
  drule_all packaged_internal_entry_return_fields >> strip_tac >>
  drule_all internal_entry_installed_operands >> strip_tac >>
  drule intcall_entry_semantic_inputs >> strip_tac >>
  drule intcall_entry_source >> strip_tac >>
  `supported_program tops` by fs[body_inv_def] >>
  qpat_x_assum `!a k. P a k <=> _` kall_tac >>
  qpat_x_assum `!b z. staged b z <=> _` kall_tac >>
  qpat_x_assum `has_rb <=> nret = 0 /\ _` kall_tac >>
  qpat_x_assum `evaluate_type (get_tenv cx) ret = SOME rtv`
    (assume_tac o SRULE [get_tenv_def]) >>
  qhdtm_x_assum `body_inv` kall_tac >>
  qhdtm_x_assum `intcall_entry` kall_tac >>
  irule internal_entry_root_frame_exists >>
  rpt conj_tac >> simp[get_tenv_def]
QED
