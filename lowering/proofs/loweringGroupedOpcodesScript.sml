(* Opcode preservation for grouped external dispatch and keyword defaults. *)
Theory loweringGroupedOpcodes
Ancestors
  loweringRuntimeOpcodes loweringFunctionOpcodes ctorCallFreeABIDecode
  ctorCallFreeCallbacks ctorCallFreeRules ctorCallFreeValues ctorCallFreeStmtReturns
  moduleLowering compileEnv context emitHelper venomInst loweringShapeDefs loweringShapeProps
  supportedExprTraverse supportedStmtTraverse list pair

val _ = Parse.hide "body";

Definition kwarg_defaults_avoid_def:
  kwarg_defaults_avoid root vars <=>
    EVERY (\(_,_,_,e). ~supported_expr_exists root e) vars
End

Definition kwarg_specs_avoid_def:
  kwarg_specs_avoid root specs <=>
    EVERY (\(_,_,e). ~supported_expr_exists root e) specs
End

local
  fun preserve ths = rpt (FIRST [
    CHANGED_TAC (simp[stmt_return_bind]),
    IF_CASES_TAC >> gvs[] >> qid_spec_tac `st`,
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp (ths @ [opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst, every_state_insts_return,
      every_state_insts_fresh_label, every_state_insts_new_block])),
    CASE_TAC >> gvs[] >> qid_spec_tac `st`]);
in

Theorem compile_create_kwarg_allocas_avoid:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  !specs ce st.
    kwarg_specs_avoid root specs /\ EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    kwarg_defaults_avoid root (FST (compile_create_kwarg_allocas ce specs st)) /\
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_create_kwarg_allocas ce specs st)))
Proof
  strip_tac >> Induct >-
    simp[compile_create_kwarg_allocas_def, comp_return_def,
         kwarg_specs_avoid_def, kwarg_defaults_avoid_def] >>
  qx_gen_tac `spec` >> PairCases_on `spec` >> rpt strip_tac >>
  gvs[compile_create_kwarg_allocas_def, comp_bind_def, comp_return_def,
      kwarg_specs_avoid_def] >>
  pairarg_tac >> gvs[] >>
  rename1 `compile_alloc_buffer _ st = (_,st')` >>
  `EVERY (\i. P i.inst_opcode) (state_insts st')` by
    metis_tac[(UNDISCH opcode_every_alloc_buffer), SND] >>
  first_x_assum (qspecl_then [`ce`, `st'`] mp_tac) >>
  simp[kwarg_defaults_avoid_def] >> pairarg_tac >> gvs[]
QED

Theorem opcode_every_init_kwargs:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (!e ce ty st. ~supported_expr_exists root e /\
    EVERY (\nd. ~supported_exprs_exists root (SND nd)) ce.ce_func_defaults ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_expr ce ty e st)))) ==>
  !vars ce off k hi st.
    kwarg_defaults_avoid root vars /\
    EVERY (\nd. ~supported_exprs_exists root (SND nd)) ce.ce_func_defaults ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_init_kwargs ce vars off k hi st)))
Proof
  ntac 2 strip_tac >> Induct >> simp[compile_init_kwargs_def, every_state_insts_return] >>
  qx_gen_tac `v` >> PairCases_on `v` >> rpt gen_tac >>
  simp[kwarg_defaults_avoid_def] >> strip_tac >> qid_spec_tac `st` >>
  simp[compile_init_kwargs_def] >>
  preserve [UNDISCH opcode_every_abi_arg_ptr_guard,
    cj 1 (UNDISCH opcode_every_abi_decode_opcode), UNDISCH opcode_every_store_bytestring,
    every_state_insts_lower_value, UNDISCH opcode_every_unwrap_value,
    GSYM kwarg_defaults_avoid_def] >>
  TRY (irule every_state_insts_lower_value >> simp[] >> conj_tac
       >- (rpt strip_tac >> first_x_assum irule >> simp[]) >>
       simp[UNDISCH opcode_every_unwrap_value]) >>
  TRY (rpt strip_tac >> first_x_assum irule >> simp[kwarg_defaults_avoid_def])
QED

Theorem opcode_every_group_entries:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (!e ce ty st. ~supported_expr_exists root e /\
    EVERY (\nd. ~supported_exprs_exists root (SND nd)) ce.ce_func_defaults ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_expr ce ty e st)))) ==>
  kwarg_defaults_avoid root vars /\
  EVERY (\nd. ~supported_exprs_exists root (SND nd)) common.ec_env.ce_func_defaults ==>
  !entries st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_group_entries mid entries common vars off st)))
Proof
  ntac 3 strip_tac >>
  `!k st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts
      (SND (compile_init_kwargs common.ec_env vars off k (Lit 0w) st)))` by
    (rpt gen_tac >> strip_tac >> irule (UNDISCH opcode_every_init_kwargs) >>
     TRY (qexists_tac `root`) >> simp[] >> metis_tac[]) >>
  Induct >> simp[compile_group_entries_def, every_state_insts_return] >>
  qx_gen_tac `e` >> PairCases_on `e` >>
  simp[compile_group_entries_def, compile_entry_point_kwargs_def] >>
  preserve [UNDISCH opcode_every_entry_checks]
QED

Theorem register_kwarg_vars_defaults:
  !vars ce. (compile_register_kwarg_vars ce vars).ce_func_defaults = ce.ce_func_defaults
Proof
  Induct >> simp[compile_register_kwarg_vars_def] >>
  qx_gen_tac `v` >> PairCases_on `v` >> simp[compile_register_kwarg_vars_def]
QED

Theorem opcode_every_common_body:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (!ce ty ss st.
    package_body_avoids root ce ss ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_stmts ce NoLoop ty ss st)))) ==>
  package_body_avoids root common.ec_env common.ec_body ==>
  !st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND
      (compile_common_function_body common.ec_env common.ec_pos_args vars
        common.ec_nonreentrant common.ec_nkey common.ec_transient common.ec_view
        common.ec_body common.ec_return st)))
Proof
  ntac 3 strip_tac >>
  fs[package_body_avoids_def] >>
  simp[compile_common_function_body_def] >>
  ho_match_mp_tac (Q.INST [`root` |-> `root`] every_state_insts_defaults_bind) >>
  rpt conj_tac
  >- simp[register_positional_args_defaults, register_kwarg_vars_defaults]
  >- simp[UNDISCH opcode_every_register_positional_args] >>
  rpt strip_tac >> irule (UNDISCH opcode_every_guarded_body) >>
  TRY (qexists_tac `root`) >> simp[] >> metis_tac[]
QED

end

Definition external_group_avoids_def:
  external_group_avoids root (ExternalSingle selector package) =
    external_package_avoids root package /\
  external_group_avoids root (ExternalDefaults common entries specs offset) =
    (kwarg_specs_avoid root specs /\
     package_body_avoids root common.ec_env common.ec_body)
End

Definition external_job_avoids_def:
  external_job_avoids root (ExternalLegacyJob package) =
    external_package_avoids root package /\
  external_job_avoids root (ExternalCommonJob common vars) =
    package_body_avoids root common.ec_env common.ec_body
End

Theorem opcode_every_external_groups:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (!e ce ty st. package_body_avoids root ce [] /\ ~supported_expr_exists root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_expr ce ty e st)))) ==>
  !groups mid st.
    EVERY (external_group_avoids root) groups /\ EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (external_job_avoids root) (FST (compile_external_groups mid groups st)) /\
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_external_groups mid groups st)))
Proof
  ntac 2 strip_tac >> Induct >-
    simp[compile_external_groups_def, comp_return_def] >>
  Cases_on `h` >> rpt gen_tac
  >- (rename1 `ExternalSingle selector package` >> PairCases_on `selector` >>
      strip_tac >> gvs[external_group_avoids_def, compile_external_groups_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
      pairarg_tac >> gvs[] >>
      rename1 `compile_selector_checks _ _ st = (_,st1)` >>
      `EVERY (\i. P i.inst_opcode) (state_insts st1)` by
        metis_tac[UNDISCH opcode_every_selector_checks, SND] >>
      first_x_assum (qspecl_then [`mid`, `st1`] mp_tac) >>
      simp[external_job_avoids_def] >> pairarg_tac >> gvs[external_job_avoids_def]) >>
  strip_tac >> gvs[external_group_avoids_def, compile_external_groups_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  rename1 `compile_create_kwarg_allocas _ _ st = (vars,st1)` >>
  `kwarg_defaults_avoid root vars /\ EVERY (\i. P i.inst_opcode) (state_insts st1)` by
    metis_tac[compile_create_kwarg_allocas_avoid, FST, SND] >>
  pairarg_tac >> gvs[] >>
  rename1 `compile_group_entries mid entries common vars off st1 = (_,st2)` >>
  `EVERY (\i. P i.inst_opcode) (state_insts
    (SND (compile_group_entries mid entries common vars off st1)))` by
    (irule (UNDISCH opcode_every_group_entries) >>
     TRY (qexists_tac `root`) >>
     fs[package_body_avoids_def, supported_stmt_expr_exists_def] >>
     metis_tac[]) >>
  `EVERY (\i. P i.inst_opcode) (state_insts st2)` by metis_tac[SND] >>
  first_x_assum (qspecl_then [`mid`, `st2`] mp_tac) >>
  simp[external_job_avoids_def] >> pairarg_tac >> gvs[external_job_avoids_def]
QED

Theorem opcode_every_external_jobs:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (!ce ty ss st. package_body_avoids root ce ss ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_stmts ce NoLoop ty ss st)))) ==>
  !jobs st.
    EVERY (external_job_avoids root) jobs /\ EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_external_jobs jobs st)))
Proof
  ntac 2 strip_tac >> Induct >> simp[compile_external_jobs_def, every_state_insts_return] >>
  Cases_on `h` >>
  simp[compile_external_jobs_def, external_job_avoids_def, comp_ignore_bind_def, comp_bind_def] >>
  rpt strip_tac >> rpt (pairarg_tac >> gvs[])
  >- (`EVERY (\i. P i.inst_opcode) (state_insts
          (SND (compile_external_fn_bodies [p] st)))` by
        (irule (UNDISCH opcode_every_external_fn_bodies) >> conj_tac
         >- first_assum ACCEPT_TAC >>
         qexists_tac `root` >> fs[package_body_avoids_def] >> metis_tac[]) >>
      metis_tac[SND]) >>
  rename1 `new_block common.ec_common_label st = (_,opened)` >>
  rename1 `compile_common_function_body common.ec_env common.ec_pos_args vars
    common.ec_nonreentrant common.ec_nkey common.ec_transient common.ec_view
    common.ec_body common.ec_return opened = ((),closed)` >>
  `EVERY (\i. P i.inst_opcode) (state_insts opened)` by
    metis_tac[every_state_insts_new_block, SND] >>
  `EVERY (\i. P i.inst_opcode) (state_insts
      (SND (compile_common_function_body common.ec_env common.ec_pos_args vars
        common.ec_nonreentrant common.ec_nkey common.ec_transient common.ec_view
        common.ec_body common.ec_return opened)))` by
    (irule (UNDISCH opcode_every_common_body) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     qexists_tac `root` >> fs[]) >>
  metis_tac[SND]
QED

local
  fun preserve_last ths = rpt (FIRST [
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp (ths @ [opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst, every_state_insts_return,
      every_state_insts_fresh_label, every_state_insts_new_block])),
    CASE_TAC >> gvs[] >> qid_spec_tac `st`]);
in

Theorem opcode_every_group_dispatch_linear:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (!e ce ty st. package_body_avoids root ce [] /\ ~supported_expr_exists root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_expr ce ty e st)))) ==>
  EVERY (external_group_avoids root) groups ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (external_job_avoids root) (FST (compile_group_dispatch_linear groups fb st)) /\
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_group_dispatch_linear groups fb st)))
Proof
  ntac 3 strip_tac >>
  `!mid st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (external_job_avoids root) (FST (compile_external_groups mid groups st)) /\
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_external_groups mid groups st)))` by
    (rpt strip_tac >>
     qpat_assum `!e ce ty st. _`
       (mp_tac o MATCH_MP (UNDISCH opcode_every_external_groups)) >>
     disch_then (qspecl_then [`groups`, `mid`, `st`] mp_tac) >>
     simp[]) >>
  simp[compile_group_dispatch_linear_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> gen_tac >> strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op CALLDATASIZE [] st = (cds,st1)` >>
  rename1 `emit_op LT [cds; Lit 4w] st1 = (short,st2)` >>
  rename1 `emit_op ISZERO [short] st2 = (has_sel,st3)` >>
  rename1 `fresh_label "dispatch" st3 = (dispatch,st4)` >>
  rename1 `emit_inst JNZ [has_sel; Label dispatch; Label fb] [] st4 = ((),st5)` >>
  rename1 `new_block dispatch st5 = (_,st6)` >>
  rename1 `emit_op CALLDATALOAD [Lit 0w] st6 = (raw,st7)` >>
  rename1 `emit_op SHR [Lit 224w; raw] st7 = (mid,st8)` >>
  rename1 `compile_external_groups mid groups st8 = (jobs,st9)` >>
  `P CALLDATASIZE /\ P LT /\ P ISZERO /\ P JNZ /\ P CALLDATALOAD /\ P SHR /\ P JMP` by
    (rpt conj_tac >> first_x_assum match_mp_tac >> simp[]) >>
  `EVERY (\i. P i.inst_opcode) (state_insts st1)` by metis_tac[opcode_every_emit_op, SND] >>
  `EVERY (\i. P i.inst_opcode) (state_insts st2)` by metis_tac[opcode_every_emit_op, SND] >>
  `EVERY (\i. P i.inst_opcode) (state_insts st3)` by metis_tac[opcode_every_emit_op, SND] >>
  `EVERY (\i. P i.inst_opcode) (state_insts st4)` by metis_tac[every_state_insts_fresh_label, SND] >>
  `EVERY (\i. P i.inst_opcode) (state_insts st5)` by metis_tac[opcode_every_emit_inst, SND] >>
  `EVERY (\i. P i.inst_opcode) (state_insts st6)` by metis_tac[every_state_insts_new_block, SND] >>
  `EVERY (\i. P i.inst_opcode) (state_insts st7)` by metis_tac[opcode_every_emit_op, SND] >>
  `EVERY (\i. P i.inst_opcode) (state_insts st8)` by metis_tac[opcode_every_emit_op, SND] >>
  `EVERY (external_job_avoids root) jobs /\
   EVERY (\i. P i.inst_opcode) (state_insts st9)` by
    (qpat_assum `compile_external_groups mid groups st8 = (jobs,st9)` (fn compiled =>
     qpat_assum `EVERY (\i. P i.inst_opcode) (state_insts st8)` (fn safe =>
     qpat_assum `!md st. _ ==> EVERY _ (FST (compile_external_groups md groups st)) /\ _`
       (fn preserve => ACCEPT_TAC (REWRITE_RULE [compiled,FST,SND]
         (MATCH_MP (Q.SPECL [`mid`,`st8`] preserve) safe)))))) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  metis_tac[opcode_every_emit_inst, SND]
QED

Theorem opcode_every_generate_grouped_runtime:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (!e ce ty st. package_body_avoids root ce [] /\ ~supported_expr_exists root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_expr ce ty e st)))) ==>
  (!ce ty ss st. package_body_avoids root ce ss ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_stmts ce NoLoop ty ss st)))) ==>
  EVERY (external_group_avoids root) groups /\ EVERY (internal_package_avoids root) ints /\
  fallback_package_avoids root fb ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_generate_grouped_runtime groups ints fb st)))
Proof
  ntac 4 strip_tac >>
  `!lbl st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (external_job_avoids root) (FST (compile_group_dispatch_linear groups lbl st)) /\
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_group_dispatch_linear groups lbl st)))` by
    (rpt gen_tac >>
     qpat_assum `!e ce ty st. package_body_avoids root ce [] /\ _ ==> _`
       (fn step => qpat_assum `EVERY (external_group_avoids root) groups`
         (fn ok => ACCEPT_TAC (Q.SPEC `st` (Q.INST [`fb` |-> `lbl`]
           (MATCH_MP (MATCH_MP (UNDISCH opcode_every_group_dispatch_linear) step) ok)))))) >>
  `!jobs st. EVERY (external_job_avoids root) jobs /\ EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_external_jobs jobs st)))` by
    (qpat_assum `!ce ty ss st. package_body_avoids root ce ss ==> _`
       (ACCEPT_TAC o MATCH_MP (UNDISCH opcode_every_external_jobs))) >>
  simp[compile_generate_grouped_runtime_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> rpt strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `fresh_label "fallback" st = (lbl,st1)` >>
  rename1 `compile_group_dispatch_linear groups lbl st1 = (jobs,st2)` >>
  rename1 `compile_external_jobs jobs st2 = ((),st3)` >>
  rename1 `new_block lbl st3 = (_,st4)` >>
  `EVERY (\i. P i.inst_opcode) (state_insts st1)` by
    metis_tac[every_state_insts_fresh_label, SND] >>
  `EVERY (external_job_avoids root) jobs /\
    EVERY (\i. P i.inst_opcode) (state_insts st2)` by
    (qpat_assum `compile_group_dispatch_linear groups lbl st1 = (jobs,st2)` (fn compiled =>
     qpat_assum `EVERY (\i. P i.inst_opcode) (state_insts st1)` (fn safe =>
     qpat_assum `!lbl st. _ ==> EVERY _ (FST (compile_group_dispatch_linear groups lbl st)) /\ _`
       (fn preserve => ACCEPT_TAC (REWRITE_RULE [compiled,FST,SND]
         (MATCH_MP (Q.SPECL [`lbl`,`st1`] preserve) safe)))))) >>
  `EVERY (\i. P i.inst_opcode) (state_insts st3)` by metis_tac[SND] >>
  `EVERY (\i. P i.inst_opcode) (state_insts st4)` by
    metis_tac[every_state_insts_new_block, SND] >>
  `!s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
        EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_internal_fn_bodies ints s)))` by
    (rpt strip_tac >> irule (UNDISCH opcode_every_internal_fn_bodies) >> conj_tac
     >- first_assum ACCEPT_TAC >>
     qexists_tac `root` >> fs[package_body_avoids_def] >> metis_tac[]) >>
  Cases_on `fb` >> gvs[fallback_package_avoids_def]
  >- (rpt (pairarg_tac >> gvs[]) >>
      `P REVERT` by (first_x_assum match_mp_tac >> simp[]) >>
      metis_tac[opcode_every_emit_inst, SND]) >>
  PairCases_on `x` >> gvs[fallback_package_avoids_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `compile_fallback_body ce pay nr key trans view stmts ret st4 = ((),st5)` >>
  `EVERY (\i. P i.inst_opcode) (state_insts
    (SND (compile_fallback_body ce pay nr key trans view stmts ret st4)))` by
    (irule (UNDISCH opcode_every_fallback_body) >> conj_tac
     >- first_assum ACCEPT_TAC >>
     qexists_tac `root` >> fs[package_body_avoids_def] >> metis_tac[]) >>
  metis_tac[SND]
QED

end
