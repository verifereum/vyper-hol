(* Compose prefix and registration certificates at one shared endpoint. *)
Theory defaultEntryEndpointAssembly
Ancestors
  runtimeEntryEndpoint defaultConcreteRegistrationDefs fragGasPathMem
  fragGasOriginPtr fragExec venomExecSemantics

Theorem default_entry_endpoint_from_certificates:
  set_external_package_target rpolicy.rpol_target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,F,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
       tx.function_name,args,([]:expr list),ret,fbody)) =
    (lbl,ce_ext,pa,mc,pay,F,key,ut,view,fbody,rt) /\
  ((ce = ce_ext /\
    runtime_selected_body_start tops rpolicy
      (lbl,ce,pa,mc,pay,F,key,ut,view,fbody,rt) st) \/
   (tx.function_name = "__default__" /\ args = [] /\ pa = [] /\ mc = 4 /\
    ce_ext = (if ret <> NoneT then update_cenv_ret_abi ce ret else ce) /\
    runtime_fallback_body_start tops rpolicy
      (lbl,ce,pa,mc,pay,F,key,ut,view,fbody,rt) st)) /\
  compile_register_positional_args ce pa 4 st = (cef,sa) /\
  compile_guarded_body cef F key ut view fbody rt sa = ((),sb) /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cef sa /\ ~block_is_terminated sa /\
  unit.cu_context.ctx_entry = SOME "__entry" /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME "__entry" /\
  lookup_block "__entry" fn.fn_blocks = SOME bb /\
  phi_prefix_length bb.bb_instructions = 0 /\
  gas_path_mem unit.cu_context fn
    (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>)
    0 (OK s) /\
  (!D explicit. gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
    (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>,
     FEMPTY,entry_taint) [] (OK s,G,tn)) /\
  (!D. (!fuel. ptr_safe_run D 0 fuel unit.cu_context fn [] G tn s) ==>
    !fuel. ptr_safe_blocks D 0 fuel unit.cu_context fn [] FEMPTY entry_taint
      (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>)) /\
  gas_path_mem unit.cu_context fn s 0 (OK out) /\
  (!D explicit. gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
    (s,G,tn) [] (OK out,Hg,u)) /\
  (!D. (!fuel. ptr_safe_run D 0 fuel unit.cu_context fn [] Hg u out) ==>
    !fuel. ptr_safe_run D 0 fuel unit.cu_context fn [] G tn s) /\
  alloca_history fn out /\ return_buf_frame NONE cef sa out /\
  ~out.vs_halted /\ out.vs_current_bb = sa.cs_current_bb /\
  out.vs_inst_idx = LENGTH sa.cs_current_insts /\
  default_registration_entry_frame vs out /\
  (!st0 H. valid_horizon
    (initial_evaluation_context am.sources am.layouts tx NONE) st0 H es0.storage_trace ==>
    ghost_inv_at (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
      0 NONE cef (initial_evaluation_context am.sources am.layouts tx NONE) es0 Hg u out /\
    stmt_state_rel H unit.cu_context fn cef
      (initial_evaluation_context am.sources am.layouts tx NONE) es0 out) ==>
  runtime_entry_endpoint tops rpolicy unit am tx vs es0 mut args ret fbody
Proof
  strip_tac >>
  `gas_path_mem unit.cu_context fn
    (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>)
    0 (OK out)` by
    (drule_all gas_path_mem_then >> simp[]) >>
  `gas_path unit.cu_context fn
    (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>)
    0 (OK out)` by metis_tac[gas_path_mem_exec] >>
  `!fuel r. run_from fuel unit.cu_context fn out = r /\ (!e. r <> Error e) ==>
    ?fuel'. run_context fuel' unit.cu_context vs = r` by
    (rpt strip_tac >>
     qpat_x_assum `gas_path_mem _ _ (_ with <|vs_prev_bb := _; vs_current_bb := _; vs_inst_idx := _|>) _ (OK out)`
       (mp_tac o MATCH_MP gas_path_mem_exec) >>
     simp[] >> strip_tac >> gvs[exit_result_def] >>
     first_x_assum (qspec_then `fuel` mp_tac) >> simp[] >> strip_tac >>
     qexists `SUC fuel'` >>
     simp[run_context_def,run_function_def,run_blocks_run_from_no_phi]) >>
  pure_rewrite_tac[runtime_entry_endpoint_def] >>
  qexistsl [`lbl`,`ce_ext`,`ce`,`pa`,`mc`,`pay`,`key`,`ut`,`view`,`rt`,`st`,
    `cef`,`sa`,`sb`,`fn`,`out`,`Hg`,`u`] >>
  gvs[default_registration_entry_frame_def] >>
  rpt strip_tac >> simp[] >>
  metis_tac[gas_origin_ptr_path_append, listTheory.APPEND]
QED
