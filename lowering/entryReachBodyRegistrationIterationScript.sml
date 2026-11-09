(* Indexed iteration over the original canonical positional argument list. *)
Theory entryReachBodyRegistrationIteration
Ancestors
  loweringStateRelDefs entryReachBodyRegistrationSlotAssembly entryReachBodyRegistrationInitialization
  entryReachBodyRegistrationIndexedShell entryReachBodyPackageAlignment
  actualRegistrationCode moduleLowering compileVyper compileEnv rich_list list arithmetic

Theorem entry_registration_prefix_next[local]:
  compile_register_positional_args ce (TAKE i pos) 4 start = (cei,st) /\
  compile_register_positional_args cei [EL i pos] off st = (cei1,last) /\
  off = 4 + SUM (MAP (\(name,prim,dyn,sz,info). sz) (TAKE i pos)) /\
  i < LENGTH pos ==>
  compile_register_positional_args ce (TAKE (SUC i) pos) 4 start = (cei1,last)
Proof
  strip_tac >> gvs[] >>
  simp[TAKE_SUC_BY_TAKE, SNOC_APPEND, register_positional_args_append]
QED

Theorem entry_registration_prefix_run:
  lower_vyper_runtime_unit tops policy = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  initial_venom_state_rel tops am tx vs /\
  valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
  lookup_function NONE tx.function_name External tops = SOME (mut,F,args,[],ret,fbody) /\
  bind_arguments (type_env tops) args tx.args = SOME scope /\
  set_external_package_target target
    (package_external_fn tops F keys (mut,F,raw,tx.function_name,args,([]:expr list),ret,fbody)) =
    (lbl,ce,pos,cds,pay,F,key,ut,view,fbody,rt) /\
  compile_register_positional_args ce pos 4 start = (cef,registered) /\
  compile_guarded_body cef F key ut view fbody rt registered = ((),final) /\
  fn_has_code start final fn /\ cs_extends final entry_end /\
  fn = mk_raw_function "__entry" (all_blocks entry_end) /\ fn_inst_ids_distinct fn /\
  entry_prefix_witness fn (type_env tops) args tx.args 0 ce start s /\
  alloca_inv s /\ alloca_frontier_inv unit.cu_context fn site s /\
  abi_alloca_history (fn_insts fn) s /\ fresh_vars_wrt final s /\
  (!id r. FLOOKUP s.vs_allocas id = SOME r ==> id < start.cs_next_id) /\
  entry_loop_fields vs s /\ ~s.vs_halted /\
  s.vs_current_bb = start.cs_current_bb /\ s.vs_inst_idx = LENGTH start.cs_current_insts ==>
  !i cei sti. i <= LENGTH args /\
    compile_register_positional_args ce (TAKE i pos) 4 start = (cei,sti) ==>
  ?t. entry_prefix_witness fn (type_env tops) args tx.args i cei sti t /\
    alloca_inv t /\ alloca_frontier_inv unit.cu_context fn site t /\
    abi_alloca_history (fn_insts fn) t /\ fresh_vars_wrt final t /\
    (!id r. FLOOKUP t.vs_allocas id = SOME r ==> id < sti.cs_next_id) /\
    entry_loop_fields vs t /\ ~t.vs_halted /\
    t.vs_current_bb = sti.cs_current_bb /\ t.vs_inst_idx = LENGTH sti.cs_current_insts /\
    cei.ce_is_ctor = F /\
    (!fuel r. run_from fuel unit.cu_context fn t = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' unit.cu_context fn s = r)
Proof
  strip_tac >>
  `ce.ce_is_ctor = F /\ LENGTH pos = LENGTH args` by
    (drule entry_runtime_package_layout >> simp[build_positional_args_def]) >>
  Induct
  >- (rpt gen_tac >> simp[compile_register_positional_args_def, comp_return_def] >> strip_tac >>
      gvs[] >> qexists_tac `s` >> simp[] >> rpt strip_tac >>
      qexists_tac `fuel` >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `i < LENGTH args /\ i <= LENGTH args` by decide_tac >>
  drule_all entry_selected_indexed_shell >> strip_tac >>
  first_x_assum (qspecl_then [`cei'`, `sti'`] mp_tac) >> simp[] >> strip_tac >>
  suspend "successor"
QED

Resume entry_registration_prefix_run[successor]:
  `SUM (MAP (\(name,prim,dyn,sz,info). sz) (TAKE i pos)) =
    SUM (MAP abi_member_head_size
      (TAKE i (MAP (vyper_to_abi_type (type_env tops)) (MAP SND args))))` by
    (drule_all entry_selected_prefix_offset >> simp[]) >>
  `compile_register_positional_args ce (TAKE (SUC i) pos) 4 start = (cei1,sti1)` by
    (irule entry_registration_prefix_next >>
     qpat_assum `compile_register_positional_args ce (TAKE i pos) _ _ = _` (irule_at Any) >>
     qpat_assum `compile_register_positional_args cei' [_] _ _ = _` (irule_at Any) >> simp[]) >>
  gvs[] >>
  `?u. entry_prefix_witness (mk_raw_function "__entry" (all_blocks entry_end)) (type_env tops) args tx.args (SUC i) cei sti u /\
    alloca_inv u /\ alloca_frontier_inv unit.cu_context
      (mk_raw_function "__entry" (all_blocks entry_end)) site u /\
    abi_alloca_history (fn_insts (mk_raw_function "__entry" (all_blocks entry_end))) u /\
    fresh_vars_wrt final u /\
    (!id r. FLOOKUP u.vs_allocas id = SOME r ==> id < sti.cs_next_id) /\
    entry_loop_fields vs u /\ ~u.vs_halted /\
    u.vs_current_bb = sti.cs_current_bb /\ u.vs_inst_idx = LENGTH sti.cs_current_insts /\
    cei.ce_is_ctor = F /\
    (!fuel r. run_from fuel unit.cu_context (mk_raw_function "__entry" (all_blocks entry_end)) u = r /\
      (!e. r <> Error e) ==> ?fuel'. run_from fuel' unit.cu_context
        (mk_raw_function "__entry" (all_blocks entry_end)) t = r)` by
    (irule entry_selected_slot_run >>
     qpat_assum `compile_register_positional_args cei' [_] _ _ = _` (irule_at Any) >>
     qpat_assum `compile_register_positional_args ce (TAKE i pos) _ _ = _` (irule_at Any) >>
     qpat_assum `entry_prefix_witness _ _ _ _ i _ _ t` (irule_at Any) >>
     qpat_assum `set_external_package_target _ _ = _` (irule_at Any) >>
     qpat_assum `lower_vyper_runtime_unit _ _ = _` (irule_at Any) >>
     qpat_assum `source_typing_ok _ _ _` (irule_at Any) >>
     simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  suspend "compose"
QED

Resume entry_registration_prefix_run[compose]:
  qexists_tac `u` >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!fuel r. _ ==> ?fuel'. run_from fuel' _ _ t = r`
    (qspecl_then [`fuel`, `run_from fuel unit.cu_context
      (mk_raw_function "__entry" (all_blocks entry_end)) u`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!fuel. _ ==> ?fuel'. run_from fuel' _ _ s = _`
    (qspec_then `fuel'` mp_tac) >> simp[]
QED

Finalise entry_registration_prefix_run

Theorem entry_registration_full_run:
  lower_vyper_runtime_unit tops policy = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  initial_venom_state_rel tops am tx vs /\
  valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
  lookup_function NONE tx.function_name External tops = SOME (mut,F,args,[],ret,fbody) /\
  bind_arguments (type_env tops) args tx.args = SOME scope /\
  set_external_package_target target
    (package_external_fn tops F keys (mut,F,raw,tx.function_name,args,([]:expr list),ret,fbody)) =
    (lbl,ce,pos,cds,pay,F,key,ut,view,fbody,rt) /\
  compile_register_positional_args ce pos 4 start = (cef,registered) /\
  compile_guarded_body cef F key ut view fbody rt registered = ((),final) /\
  fn_has_code start final fn /\ cs_extends final entry_end /\
  fn = mk_raw_function "__entry" (all_blocks entry_end) /\ fn_inst_ids_distinct fn /\
  entry_prefix_witness fn (type_env tops) args tx.args 0 ce start s /\
  alloca_inv s /\ alloca_frontier_inv unit.cu_context fn site s /\
  abi_alloca_history (fn_insts fn) s /\ fresh_vars_wrt final s /\
  (!id r. FLOOKUP s.vs_allocas id = SOME r ==> id < start.cs_next_id) /\
  entry_loop_fields vs s /\ ~s.vs_halted /\
  s.vs_current_bb = start.cs_current_bb /\ s.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?t. entry_prefix_witness fn (type_env tops) args tx.args (LENGTH args) cef registered t /\
    alloca_inv t /\ alloca_frontier_inv unit.cu_context fn site t /\
    abi_alloca_history (fn_insts fn) t /\ fresh_vars_wrt final t /\
    (!id r. FLOOKUP t.vs_allocas id = SOME r ==> id < registered.cs_next_id) /\
    entry_loop_fields vs t /\ ~t.vs_halted /\
    t.vs_current_bb = registered.cs_current_bb /\
    t.vs_inst_idx = LENGTH registered.cs_current_insts /\ cef.ce_is_ctor = F /\
    (!fuel r. run_from fuel unit.cu_context fn t = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' unit.cu_context fn s = r)
Proof
  strip_tac >>
  `LENGTH pos = LENGTH args` by
    (drule entry_runtime_package_layout >> simp[build_positional_args_def]) >>
  irule entry_registration_prefix_run >>
  qpat_assum `set_external_package_target _ _ = _` (irule_at Any) >>
  qpat_assum `compile_guarded_body _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `lower_vyper_runtime_unit _ _ = _` (irule_at Any) >>
  qpat_assum `source_typing_ok _ _ _` (irule_at Any) >>
  qpat_assum `entry_prefix_witness _ _ _ _ 0 _ _ s` (irule_at Any) >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >>
  qpat_x_assum `LENGTH pos = LENGTH args` (SUBST1_TAC o SYM) >> simp[]
QED
