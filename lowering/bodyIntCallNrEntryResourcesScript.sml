(* VM materialization resources of the actual package, before its guard. *)
Theory bodyIntCallNrEntryResources
Ancestors
  bodyIntCallNrPackageInputs bodyIntCallPackageRootResource
  bodyIntCallPackageControl bodyIntCallActualEntryLanding
  bodyIntCallActualEntryProtection bodyIntCallActualEntrySemantic
  bodyIntCallResourceNormalize bodyIntCallSeamDefs bodyIntCallInvokeEntry
  bodyIntCallActualEntryFields bodyIntCallActualEntryWitness
  bodyIntCallActualEntryReservation bodyIntCallJointContract
  bodySim exprLoweringProps loweringStateRelDefs compileEnv compileVyper
  moduleLowering vyperState vyperContext intCallCallee intCallFrame
  calleeTransport finite_map list words arithmetic

Theorem intcall_entry_declared_immutable_separation_nr:
  cenv_module_pins tops cenv /\
  intcall_entry tops ctx func cenv cx tenv name es sa sb vv s0 es0
    (mut,nr,args,ret,ss,rr) prev penv rtv es1 t /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,arg_ops) /\
  eval_operands arg_ops t = SOME argv /\
  lookup_function lbl ctx.ctx_functions = SOME callee /\
  setup_callee callee argv t = SOME setup /\
  set_internal_package_target cenv.ce_target
    (package_internal_fn tops use_trans (nkeys:string->num) cenv.ce_is_ctor ilen
      (mut,nr,rr,name,args,([]:expr list),ret,ss)) =
    (label,ce,params,has_rb,is_nr,key,trans,view,ctor,ilen',ss',rt) ==>
  (ce.ce_is_ctor ==> !i po psz nm ty tv io.
     i < LENGTH params /\ ~SND (EL i params) /\
     FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) /\
     FLOOKUP ce.ce_module_vars (ce.ce_module,nm) = SOME (ImmutableLoc io) /\
     ce.ce_module_var_type (ce.ce_module,nm) = SOME ty /\
     evaluate_type (get_tenv (cx with stk updated_by CONS (NONE,name))) ty = SOME tv ==>
     regions_disjoint io (type_memory_size tv)
       (w2n (EL ((if has_rb then 1 else 0) + i) argv)) psz)
Proof
  strip_tac >> drule_all intcall_entry_package_separation_nr >> strip_tac >>
  `stmt_state_rel ctx func cenv cx (es1 with scopes := prev) t` by
    (fs[intcall_entry_def]) >>
  `ce.ce_module = cenv.ce_module /\
   ce.ce_module_vars = cenv.ce_module_vars /\
   ce.ce_module_var_type = cenv.ce_module_var_type /\
   ce.ce_is_ctor = cenv.ce_is_ctor` by
    (gvs[package_internal_fn_def, set_internal_package_target_def,
         update_cenv_nonreentrant_def, cenv_module_pins_def,
         build_compile_env_def, pairTheory.ELIM_UNCURRY]) >>
  rpt strip_tac >>
  qpat_x_assum `!i po psz. _ ==> ?aid off asz. _` drule_all >> strip_tac >>
  fs[stmt_state_rel_def, immutable_alloca_sep_def, immutable_decl_sep_def,
     get_tenv_def] >>
  gvs[] >>
  qpat_x_assum `!name ty tv off. _ /\ _ /\ evaluate_type _ _ = _ ==> _`
    drule_all >> strip_tac >>
  qpat_x_assum `!aid b sz. FLOOKUP t.vs_allocas aid = SOME (b,sz) ==> _` drule >>
  simp[regions_disjoint_def] >> decide_tac
QED

Theorem intcall_entry_prelock_resources_nr:
  cenv_module_pins tops cenv /\
  supported_function_body tops Internal args ss /\
  intcall_entry tops ctx func cenv cx tenv name es sa sb vv s0 es0
    (mut,nr,args,ret,ss,rr) prev penv rtv es1 t /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,arg_ops) /\ eval_operands arg_ops t = SOME argv /\
  lookup_function lbl ctx.ctx_functions = SOME callee /\
  setup_callee callee argv t = SOME entered /\
  cenv.ce_func_info (nsid_to_string (NONE,name)) = (nret,rbs,pvs) /\
  set_internal_package_target cenv.ce_target
    (package_internal_fn tops use_trans (nkeys:string->num) cenv.ce_is_ctor ilen
      (mut,nr,rr,name,args,([]:expr list),ret,ss)) =
    (label,ce,params,has_rb,is_nr,key,trans,view,ctor,ilen',ss',rt) /\
  compile_internal_function_entry ce params has_rb ctor ilen' rt entry =
    ((ce2,rpc,imm),prelock) /\
  entry.cs_current_insts = [] /\
  entry.cs_current_bb = (HD callee.fn_blocks).bb_label /\
  fn_has_code entry prelock callee /\ fn_inst_ids_distinct callee /\
  (!a k. P a k <=> a + k <= t.vs_alloca_next /\
    !aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==> regions_disjoint a k off asz) /\
  (!b z. staged b z <=> ?i po.
    i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po z) /\
    b = w2n (EL ((if has_rb then 1 else 0) + i) argv)) ==>
  ?v.
    run_inst_seq (emitted_insts entry prelock) entered = OK v /\
    gas_path ctx callee entered
      (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts entry prelock)))
      (OK (v with vs_inst_idx := LENGTH prelock.cs_current_insts)) /\
    ~v.vs_halted /\ v.vs_current_bb = prelock.cs_current_bb /\
    (?x. rpc = Var x /\ not_fresh_at prelock x /\
      lookup_var x v = SOME entered.vs_return_pc_token) /\
    (!op sz. (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>).
      ce_return_buf = SOME (PtrVar op sz) ==>
      ?x w. op = Var x /\ not_fresh_at prelock x /\ lookup_var x v = SOME w) /\
    (!op. (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>).
      ce_imm_alloca = SOME op ==>
      ?x w. op = Var x /\ not_fresh_at prelock x /\ lookup_var x v = SOME w) /\
    stmt_state_rel ctx callee
      (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>)
      (cx with stk updated_by CONS (NONE,name)) es1 v /\
    local_ptrs_reserved
      (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>) prelock /\
    allocas_above t.vs_alloca_next v /\
    (!a k. P a k ==> mem_bytes_at a k v.vs_memory = mem_bytes_at a k t.vs_memory) /\
    (!n p k. local_region
      (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>) es1.scopes v n p k ==>
      t.vs_alloca_next <= p \/ ?b z. staged b z /\ b <= p /\ p + k <= b + z) /\
    return_buf_frame (if has_rb then SOME (HD argv,type_memory_size rtv) else NONE)
      (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>) prelock v /\
    (!a k. P a k ==> a + k <= t.vs_alloca_next) /\
    (!b z. staged b z ==> !a k. P a k ==> regions_disjoint a k b z) /\
    cenv_module_pins tops (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>) /\
    ce2.ce_return_pc = SOME (PtrVar rpc 0) /\
    ce2.ce_returns_count = returns_stack_count
      (\nm. MAP (FST o SND) (get_struct_fields ce2.ce_struct_fields nm)) ret /\
    (has_rb <=> ce2.ce_returns_count = 0 /\ ret <> NoneT) /\
    (has_rb /\ ce2.ce_is_ctor ==> !nm tv iv io.
      FLOOKUP ce2.ce_module_vars (ce2.ce_module,nm) = SOME (ImmutableLoc io) /\
      FLOOKUP (case ALOOKUP es1.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables ce2.ce_module imms) nm = SOME (tv,iv) ==>
      regions_disjoint io (type_memory_size tv) (w2n (HD argv)) (type_memory_size rtv)) /\
    (has_rb ==> w2n (HD argv) + type_memory_size rtv <= t.vs_alloca_next /\
      (!b z. staged b z ==> regions_disjoint (w2n (HD argv)) (type_memory_size rtv) b z) /\
      (!a k. P a k ==> regions_disjoint a k (w2n (HD argv)) (type_memory_size rtv)))
Proof
  strip_tac >> drule_all intcall_entry_package_inputs_nr >> strip_tac >>
  drule_all intcall_entry_package_separation_nr >> strip_tac >>
  drule intcall_entry_declared_immutable_separation_nr >>
  rpt (disch_then drule) >> strip_tac >>
  drule_all packaged_internal_entry_return_fields >> strip_tac >>
  drule_all intcall_entry_root_geometry_nr >> strip_tac >>
  drule_all internal_entry_counted_resources >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all internal_entry_installed_operands >> strip_tac >>
  drule_all packaged_internal_entry_reserved >> strip_tac >>
  `es1 with scopes := [penv] = es1` by
    (fs[intcall_entry_def, evaluation_state_component_equality]) >>
  `ce.ce_is_ctor ==> !i po psz nm ty tv io.
     i < LENGTH params /\ ~SND (EL i params) /\
     FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) /\
     FLOOKUP ce.ce_module_vars (ce.ce_module,nm) = SOME (ImmutableLoc io) /\
     ce.ce_module_var_type (ce.ce_module,nm) = SOME ty /\
     evaluate_type (get_tenv cx) ty = SOME tv ==>
     regions_disjoint io (type_memory_size tv)
       (w2n (EL ((if has_rb then 1 else 0) + i) argv)) psz` by
    (fs[get_tenv_def] >> metis_tac[]) >>
  drule_all internal_entry_landing_stmt_state_rel >>
  disch_then (qspec_then `u.vs_inst_idx` assume_tac) >>
  drule_all internal_entry_landing_allocas_above >> strip_tac >>
  drule internal_parameter_staged_containment >> strip_tac >>
  `!a k. P a k ==> mem_bytes_at a k entered.vs_memory = mem_bytes_at a k t.vs_memory` by
    (drule setup_callee_shared_fields >> simp[]) >>
  drule_all internal_entry_installed_protection >> strip_tac >>
  `has_rb ==> (?off sz. ce.ce_return_buf = SOME (MemLoc off sz)) /\
     w2n (HD argv) + type_memory_size rtv <= t.vs_alloca_next` by metis_tac[] >>
  drule_all internal_entry_landing_return_buf >> strip_tac >>
  `ce2.ce_is_ctor = ce.ce_is_ctor /\
   ce2.ce_module_vars = ce.ce_module_vars /\ ce2.ce_module = ce.ce_module` by
    (drule compile_internal_entry_fields >>
     simp[compile_env_component_equality]) >>
  qexists `u` >>
  qpat_x_assum `!a k. P a k <=> _` kall_tac >>
  qpat_x_assum `!b z. staged b z <=> _` kall_tac >>
  fs[stmt_state_rel_inst_idx] >>
  fs[stmt_state_rel_def, state_rel_call_stack, immutable_alloca_sep_def,
     immutable_decl_sep_def, get_tenv_def] >>
  `es1.scopes = [penv]` by
    (fs[intcall_entry_def]) >> fs[] >>
  conj_tac >- (conj_tac >- metis_tac[] >> metis_tac[]) >>
  metis_tac[]
QED
