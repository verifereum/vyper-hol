(* TOP-LEVEL: the argument-list invariant, concrete compiler readiness,
   and the per-expression lowering induction contract. The latter exposes
   expression execution and write geometry, never a saved prefix result.
   Charges depend only on the source expression and its source input.
   Runtime SSA bindings may survive earlier visits to the same cut;
   operand lifetimes protect live values without requiring their absence. *)
Theory logArgumentListContract
Ancestors
  logArgumentOrigins logArgumentBackingFrames sourceAllocationPrivacy sourceMemoryFrames
  logArgumentExecution logArgumentWriters
  allocationGrowth abiAllocationWindows abiMemoryFrame abiRequestCredit abiFieldOperands typedLogArgs
  compileAllocationRequests compileAllocaProvenance compileIdFlow compileVyper vyperTypeContract vyperContext
  exprLowering stmtLowering context compileEnv vyperTypeInvariants vyperExprEffects vyperTypeExprSoundness
  vyperInterpreter fragExec venomMemDefs venomState list pair words arithmetic

Definition log_prefix_ready_def:
  log_prefix_ready env cx cenv func ids reserved requests final_cut suffix cs es ss credit prefix ptvs pvs <=>
    runtime_consistent env cx es /\
    env_scopes_consistent env cx es /\ state_well_typed es /\ state_rel_simple cenv cx es ss /\
    local_ptrs_rel func cenv es.scopes ss /\ source_alloca_floor cenv es.scopes ids ss /\
    (!name entry p region_size. lookup_scopes name es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> abi_operand_before cs.cs_next_var (Var p)) /\
    log_argument_writers func cenv es.scopes ids (compiler_alloca_ids cs final_cut) /\
    alloca_inv ss /\ log_args_rel prefix ptvs pvs ss /\
    EVERY (\arg. abi_operand_before cs.cs_next_var (FST arg)) prefix /\
    log_args_origins cenv es.scopes ss (compiler_alloca_ids cs final_cut) (EVERY pure_expr suffix) prefix ptvs /\
    abi_request_credit reserved requests credit ss /\ compiler_id_history cs /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts
End

Definition log_argument_load_certificate_def:
  log_argument_load_certificate env ctx func cenv cx es es1 e tv v src suffix cs load_cut save_cut final_cut
    before loaded reserved requests credit writes <=>
    fragment_path ctx func before loaded /\
    loaded.vs_current_bb = load_cut.cs_current_bb /\ loaded.vs_inst_idx = LENGTH load_cut.cs_current_insts /\
    loaded.vs_halted = before.vs_halted /\
    lowered_value_rel (lowered_value_type cenv e) tv v src loaded /\ abi_operand_before load_cut.cs_next_var src /\
    runtime_consistent env cx es1 /\ env_scopes_consistent env cx es1 /\ state_well_typed es1 /\
    state_rel_simple cenv cx es1 loaded /\ local_ptrs_rel func cenv es1.scopes loaded /\
    alloca_inv loaded /\ allocation_growth before loaded /\ cs.cs_next_var <= load_cut.cs_next_var /\
    (fresh_vars_wrt cs before ==> fresh_vars_wrt load_cut loaded) /\ compiler_id_history load_cut /\
    (!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op loaded = eval_operand arg_op before) /\
    source_writes_contained cenv es.scopes before writes /\ (EVERY pure_expr (e::suffix) ==> writes = []) /\
    abi_memory_frame (writes ++ abi_allocation_windows (compiler_alloca_ids cs final_cut) loaded ++
      [(before.vs_alloca_next,loaded.vs_alloca_next - before.vs_alloca_next)]) before loaded /\
    (~is_word_type (lowered_value_type cenv e) /\ EVERY pure_expr suffix ==> !src_addr.
      eval_operand src loaded = SOME src_addr ==>
      argument_origin cenv es1.scopes loaded (compiler_alloca_ids save_cut final_cut) T
        (w2n src_addr) (type_memory_size tv)) /\
    abi_request_credit reserved requests credit loaded
End

Definition log_argument_lowering_def:
  log_argument_lowering tops env ctx func cenv cx ids reserved requests final_cut charge e <=>
    !suffix cs src load_cut saved save_cut tv es es1 v ss credit prefix ptvs pvs.
      log_prefix_ready env cx cenv func ids reserved requests final_cut (e::suffix) cs es ss credit prefix ptvs pvs /\
      eval_argument cx e es = (INL v,es1) /\ charge e es <= credit /\
      lower_value compile_expr cenv (expr_type e) e cs = (src,load_cut) /\
      compile_log_save_arg cenv (lowered_value_type cenv e) src suffix load_cut = (saved,save_cut) /\
      evaluate_type (type_env tops) (lowered_value_type cenv e) = SOME tv /\
      type_memory_size tv < dimword(:256) /\ fn_inst_ids_distinct func /\
      (!request. MEM request (compiler_alloca_requests cs load_cut) ==> MEM request requests) /\
      cs_extends cs load_cut /\ cs_extends save_cut final_cut /\
      fn_has_code cs load_cut func /\ fn_has_code load_cut save_cut func /\ fn_has_code save_cut final_cut func ==>
      ?loaded writes. log_argument_load_certificate env ctx func cenv cx es es1 e tv v src suffix
        cs load_cut save_cut final_cut ss loaded reserved requests (credit - charge e es) writes
End

Definition log_argument_plan_def:
  log_argument_plan tops cenv func ids requests final_cut [] cs cut = (cut = cs) /\
  log_argument_plan tops cenv func ids requests final_cut (e::suffix) cs cut =
    (?src load_cut saved save_cut tv.
      lower_value compile_expr cenv (expr_type e) e cs = (src,load_cut) /\
      compile_log_save_arg cenv (lowered_value_type cenv e) src suffix load_cut = (saved,save_cut) /\
      evaluate_type (type_env tops) (lowered_value_type cenv e) = SOME tv /\
      type_memory_size tv < dimword(:256) /\
      (!request. MEM request (compiler_alloca_requests cs load_cut) ==> MEM request requests) /\
      cs_extends cs load_cut /\ cs_extends save_cut final_cut /\
      fn_has_code cs load_cut func /\ fn_has_code load_cut save_cut func /\ fn_has_code save_cut final_cut func /\
      (~is_word_type (lowered_value_type cenv e) /\ ~EVERY pure_expr suffix ==>
        MEM (load_cut.cs_next_id,type_memory_size tv) requests /\ MEM load_cut.cs_next_id ids) /\
      log_argument_plan tops cenv func ids requests final_cut suffix save_cut cut)
End

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed Log list induction contracts: " ^ name)
  end) (DB.thms "logArgumentListContract")
