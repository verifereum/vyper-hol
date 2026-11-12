Theory runtimeSymSrcModuleDispatch
Ancestors
  runtimeSymSrcInterfaces runtimeSymSrcEmission moduleLowering compileEnv
  emitHelper list pair loweringShapeDefs runtimeSymSrcEmissionProbe stackPlanTypes

Theorem runtime_sym_new_block_result:
  new_block l s = (u,s') ==> state_insts s' = state_insts s
Proof
  metis_tac[runtime_sym_new_block, pairTheory.SND]
QED

Theorem runtime_sym_selector_checks:
  !sels mid s u s'. ~is_label_operand mid /\
    EVERY (\(sel,lbl). runtime_sym_label lbl) sels /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_selector_checks mid sels s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')
Proof
  Induct >- simp[compile_selector_checks_def, comp_return_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_selector_checks_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  drule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >>
  simp[is_label_operand_def] >> strip_tac >>
  imp_res_tac runtime_sym_fresh_label >> gvs[] >>
  drule_at (Pat `emit_inst JNZ _ _ _ = _`) runtime_sym_jnz >>
  simp[] >> strip_tac >>
  imp_res_tac runtime_sym_new_block_result >> gvs[] >>
  drule_at (Pat `emit_inst JMP _ _ _ = _`) runtime_sym_jump >>
  simp[] >> strip_tac >>
  first_x_assum (drule_at (Pat `compile_selector_checks _ _ _ = _`)) >> simp[]
QED

Theorem runtime_sym_selector_dispatch_linear:
  EVERY (\(sel,lbl). runtime_sym_label lbl) sels /\
  runtime_sym_label fallback /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_selector_dispatch_linear sels fallback s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  simp[compile_selector_dispatch_linear_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  ntac 3 (rev_dxrule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >>
    simp[is_label_operand_def] >> strip_tac) >>
  imp_res_tac runtime_sym_fresh_label >> gvs[] >>
  rev_dxrule_at (Pat `emit_inst JNZ _ _ _ = _`) runtime_sym_jnz >> simp[] >> strip_tac >>
  imp_res_tac runtime_sym_new_block_result >> gvs[] >>
  ntac 2 (rev_dxrule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >>
    simp[is_label_operand_def] >> strip_tac) >>
  rev_dxrule_at (Pat `compile_selector_checks _ _ _ = _`) runtime_sym_selector_checks >>
  simp[] >> strip_tac >>
  drule_at (Pat `emit_inst JMP _ _ _ = _`) runtime_sym_jump >> simp[]
QED

Theorem runtime_sym_entry_checks:
  EVERY runtime_sym_inst (state_insts s) /\
  compile_entry_checks n payable s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  simp[compile_entry_checks_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  `EVERY runtime_sym_inst (state_insts cs')` by
    (qpat_x_assum `(if ~payable then _ else _) _ = _` mp_tac >>
     Cases_on `payable` >> simp[comp_return_def, comp_bind_def, comp_ignore_bind_def]
     >- (strip_tac >> gvs[]) >>
     rpt (pairarg_tac >> simp[]) >> strip_tac >>
     ntac 2 (rev_dxrule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >>
       simp[] >> strip_tac) >>
     drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >> simp[]) >>
  qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
  reverse IF_CASES_TAC >> simp[comp_return_def, comp_bind_def, comp_ignore_bind_def]
  >- (strip_tac >> gvs[]) >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  ntac 3 (rev_dxrule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >>
    simp[is_label_operand_def] >> strip_tac) >>
  drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >> simp[]
QED

Theorem runtime_sym_group_entries:
  (!k s u s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_entry_point_kwargs common.ec_env vars off k common.ec_common_label s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  !entries mid s u s'. ~is_label_operand mid /\
    EVERY (\(sel,lbl,mincd,k). runtime_sym_label lbl) entries /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_group_entries mid entries common vars off s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >> Induct >- simp[compile_group_entries_def, comp_return_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_group_entries_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  dxrule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >>
  simp[is_label_operand_def] >> strip_tac >>
  imp_res_tac runtime_sym_fresh_label >> gvs[] >>
  dxrule_at (Pat `emit_inst JNZ _ _ _ = _`) runtime_sym_jnz >> simp[] >> strip_tac >>
  imp_res_tac runtime_sym_new_block_result >> gvs[] >>
  dxrule_at (Pat `compile_entry_checks _ _ _ = _`) runtime_sym_entry_checks >>
  simp[] >> strip_tac >>
  first_assum (drule_at (Pat `compile_entry_point_kwargs _ _ _ _ _ _ = _`)) >>
  simp[] >> strip_tac >>
  first_x_assum (drule_at (Pat `compile_group_entries _ _ _ _ _ _ = _`)) >> simp[]
QED

(* These provenance projections carry arbitrary package/stmts/default facts
   through dispatch allocation. They avoid repeating eleven-field tuples and
   do not impose any new compiler semantics or assume source safety. *)
Definition runtime_sym_group_def:
  runtime_sym_group P Q D (ExternalSingle (sel,lbl,tz) p) =
    (runtime_sym_label lbl /\ P p) /\
  runtime_sym_group P Q D (ExternalDefaults c entries specs off) =
    (Q c /\ EVERY (\(sel,lbl,n,k). runtime_sym_label lbl) entries /\ EVERY D specs)
End

Definition runtime_sym_job_def:
  runtime_sym_job P Q D (ExternalLegacyJob p) = P p /\
  runtime_sym_job P Q D (ExternalCommonJob c vars) =
    (Q c /\ EVERY (\(n,op,ty,e). ~is_label_operand op /\ D (n,ty,e)) vars)
End

Theorem runtime_sym_kwarg_projection:
  EVERY (\(n,op,ty,e). ~is_label_operand op) vars /\
  MAP (\(n,op,ty,e). (n,ty,e)) vars = specs /\ EVERY D specs ==>
  EVERY (\(n,op,ty,e). ~is_label_operand op /\ D (n,ty,e)) vars
Proof
  qid_spec_tac `specs` >> Induct_on `vars` >> simp[] >>
  gen_tac >> PairCases_on `h` >> simp[]
QED

Theorem runtime_sym_external_groups:
  (!c specs s vars s'. Q c /\ EVERY D specs /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_create_kwarg_allocas c.ec_env specs s = (vars,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\
    EVERY (\(n,op,ty,e). ~is_label_operand op) vars /\
    MAP (\(n,op,ty,e). (n,ty,e)) vars = specs) /\
  (!c vars off k s u s'. Q c /\
    EVERY (\(n,op,ty,e). ~is_label_operand op /\ D (n,ty,e)) vars /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_entry_point_kwargs c.ec_env vars off k c.ec_common_label s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  !groups mid s jobs s'. ~is_label_operand mid /\
    EVERY (runtime_sym_group P Q D) groups /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_external_groups mid groups s = (jobs,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ EVERY (runtime_sym_job P Q D) jobs
Proof
  strip_tac >> Induct >- simp[compile_external_groups_def, comp_return_def] >>
  gen_tac >> Cases_on `h`
  >- (PairCases_on `p` >> rpt gen_tac >>
      simp[compile_external_groups_def, comp_bind_def, comp_ignore_bind_def,
           runtime_sym_group_def] >>
      rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[comp_return_def] >>
      drule_at (Pat `compile_selector_checks _ _ _ = _`) runtime_sym_selector_checks >>
      simp[] >> strip_tac >>
      first_x_assum (drule_at (Pat `compile_external_groups _ _ _ = _`)) >>
      simp[runtime_sym_job_def]) >>
  rpt gen_tac >>
  simp[compile_external_groups_def, comp_bind_def, comp_ignore_bind_def,
       runtime_sym_group_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[comp_return_def] >>
  first_assum (drule_at (Pat `compile_create_kwarg_allocas _ _ _ = _`)) >>
  simp[] >> strip_tac >>
  `EVERY (\(n,op,ty,e). ~is_label_operand op /\ D (n,ty,e)) kwvars` by
    (irule runtime_sym_kwarg_projection >> goal_assum (drule_at Any) >> simp[]) >>
  `EVERY runtime_sym_inst (state_insts cs'')` by
    (drule_at (Pat `compile_group_entries _ _ _ _ _ _ = _`) runtime_sym_group_entries >>
     disch_then irule >> simp[] >> rpt strip_tac >>
     first_assum (drule_at (Pat `compile_entry_point_kwargs _ _ _ _ _ _ = _`)) >> simp[]) >>
  first_x_assum (drule_at (Pat `compile_external_groups _ _ _ = _`)) >>
  simp[runtime_sym_job_def]
QED

Theorem runtime_sym_group_dispatch_linear:
  (!mid s jobs s'. ~is_label_operand mid /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_external_groups mid groups s = (jobs,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ EVERY (runtime_sym_job P Q D) jobs) ==>
  !fallback s jobs s'. runtime_sym_label fallback /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_group_dispatch_linear groups fallback s = (jobs,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ EVERY (runtime_sym_job P Q D) jobs
Proof
  strip_tac >> rpt gen_tac >>
  simp[compile_group_dispatch_linear_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[comp_return_def] >>
  ntac 3 (rev_dxrule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >>
    simp[is_label_operand_def] >> strip_tac) >>
  imp_res_tac runtime_sym_fresh_label >> gvs[] >>
  dxrule_at (Pat `emit_inst JNZ _ _ _ = _`) runtime_sym_jnz >> simp[] >> strip_tac >>
  imp_res_tac runtime_sym_new_block_result >> gvs[] >>
  ntac 2 (rev_dxrule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >>
    simp[is_label_operand_def] >> strip_tac) >>
  first_assum (drule_at (Pat `compile_external_groups _ _ _ = _`)) >>
  simp[] >> strip_tac >>
  drule_at (Pat `emit_inst JMP _ _ _ = _`) runtime_sym_jump >> simp[]
QED

Theorem runtime_sym_external_jobs:
  (!p s u s'. P p /\ EVERY runtime_sym_inst (state_insts s) /\
    compile_external_fn_bodies [p] s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!c vars s u s'. Q c /\
    EVERY (\(n,op,ty,e). ~is_label_operand op /\ D (n,ty,e)) vars /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_common_function_body c.ec_env c.ec_pos_args vars c.ec_nonreentrant
      c.ec_nkey c.ec_transient c.ec_view c.ec_body c.ec_return s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  !jobs s u s'. EVERY (runtime_sym_job P Q D) jobs /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_external_jobs jobs s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >> Induct >- simp[compile_external_jobs_def, comp_return_def] >>
  gen_tac >> Cases_on `h` >> rpt gen_tac >>
  simp[compile_external_jobs_def, comp_bind_def, comp_ignore_bind_def, runtime_sym_job_def] >>
  rpt (pairarg_tac >> pure_asm_rewrite_tac[] >>
       CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV)) >> strip_tac
  >- (first_assum (drule_at (Pat `compile_external_fn_bodies _ _ = _`)) >>
      simp[] >> strip_tac >>
      first_x_assum (drule_at (Pat `compile_external_jobs _ _ = _`)) >> simp[]) >>
  imp_res_tac runtime_sym_new_block_result >> gvs[] >>
  first_assum (drule_at (Pat `compile_common_function_body _ _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >> strip_tac >>
  first_x_assum (drule_at (Pat `compile_external_jobs _ _ = _`)) >> simp[]
QED

Theorem runtime_sym_runtime_fallback:
  (!ce pay nr key tr view stmts ret s u s'.
    fallback = SOME (ce,pay,nr,key,tr,view,stmts,ret) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_fallback_body ce pay nr key tr view stmts ret s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  !s u s'. EVERY runtime_sym_inst (state_insts s) /\
    (case fallback of NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
     | SOME (ce,pay,nr,key,tr,view,stmts,ret) =>
       compile_fallback_body ce pay nr key tr view stmts ret) s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >> Cases_on `fallback`
  >- (simp[] >> rpt strip_tac >>
      drule_at (Pat `emit_inst _ _ _ _ = _`) runtime_sym_emit_inst >>
      disch_then irule >> simp[] >> qexists `s.cs_next_id` >>
      irule runtime_sym_ordinary_inst >> simp[is_label_operand_def]) >>
  PairCases_on `x` >> simp[] >> metis_tac[]
QED

Theorem runtime_sym_generate_runtime:
  (!s u s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_external_fn_bodies external_fns s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!s u s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_internal_fn_bodies internal_fns s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!ce pay nr key tr view stmts ret s u s'.
    fallback = SOME (ce,pay,nr,key,tr,view,stmts,ret) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_fallback_body ce pay nr key tr view stmts ret s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  !s u s'. EVERY (\(sel,lbl,tz). runtime_sym_label lbl) selectors /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_generate_runtime selectors external_fns internal_fns fallback Linear
      buckets metadata dense entry_info s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >> rpt gen_tac >>
  simp[compile_generate_runtime_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> pure_asm_rewrite_tac[] >>
       CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV)) >>
  strip_tac >> gvs[comp_return_def] >>
  imp_res_tac runtime_sym_fresh_label >>
  imp_res_tac runtime_sym_new_block_result >> gvs[] >>
  drule_at (Pat `compile_selector_dispatch_linear _ _ _ = _`)
    runtime_sym_selector_dispatch_linear >>
  simp[EVERY_MAP, LAMBDA_PROD] >> strip_tac >>
  first_assum (drule_at (Pat `compile_external_fn_bodies _ _ = _`)) >>
  simp[] >> strip_tac >>
  Cases_on `fallback`
  >- (gvs[] >>
      qmatch_asmsub_rename_tac `emit_inst REVERT _ _ before = _` >>
      drule_at (Pat `emit_inst _ _ _ _ = _`) runtime_sym_emit_inst >>
      disch_then (qspec_then `0` mp_tac) >>
      simp[runtime_sym_ordinary_inst, is_label_operand_def] >> strip_tac >>
      first_assum (drule_at (Pat `compile_internal_fn_bodies _ _ = _`)) >> simp[]) >>
  PairCases_on `x` >> gvs[] >>
  first_assum (drule_at (Pat `compile_fallback_body _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >> strip_tac >>
  first_assum (drule_at (Pat `compile_internal_fn_bodies _ _ = _`)) >> simp[]
QED

Theorem runtime_sym_generate_grouped_runtime:
  (!mid s jobs s'. ~is_label_operand mid /\
    EVERY (runtime_sym_group P Q D) groups /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_external_groups mid groups s = (jobs,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ EVERY (runtime_sym_job P Q D) jobs) /\
  (!jobs s u s'. EVERY (runtime_sym_job P Q D) jobs /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_external_jobs jobs s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!s u s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_internal_fn_bodies internal_fns s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!ce pay nr key tr view stmts ret s u s'.
    fallback = SOME (ce,pay,nr,key,tr,view,stmts,ret) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_fallback_body ce pay nr key tr view stmts ret s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  !s u s'. EVERY (runtime_sym_group P Q D) groups /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_generate_grouped_runtime groups internal_fns fallback s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >> rpt gen_tac >>
  simp[compile_generate_grouped_runtime_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> pure_asm_rewrite_tac[] >>
       CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV)) >>
  strip_tac >> gvs[comp_return_def] >>
  imp_res_tac runtime_sym_fresh_label >>
  imp_res_tac runtime_sym_new_block_result >> gvs[] >>
  drule_at (Pat `compile_group_dispatch_linear _ _ _ = _`)
    runtime_sym_group_dispatch_linear >>
  disch_then (qspecl_then [`Q`,`P`,`D`] mp_tac) >>
  simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  first_assum (drule_at (Pat `compile_external_jobs _ _ = _`)) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!mid s jobs s'. _ /\ _ /\ compile_external_groups _ _ _ = _ ==> _` kall_tac >>
  qpat_x_assum `!jobs s s'. _ /\ _ /\ compile_external_jobs _ _ = _ ==> _` kall_tac >>
  Cases_on `fallback`
  >- (gvs[] >>
      drule_at (Pat `emit_inst _ _ _ _ = _`) runtime_sym_emit_inst >>
      disch_then (qspec_then `0` mp_tac) >>
      simp[runtime_sym_ordinary_inst, is_label_operand_def] >> strip_tac >>
      first_assum (drule_at (Pat `compile_internal_fn_bodies _ _ = _`)) >> simp[]) >>
  PairCases_on `x` >> gvs[] >>
  first_assum (drule_at (Pat `compile_fallback_body _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >> strip_tac >>
  first_assum (drule_at (Pat `compile_internal_fn_bodies _ _ = _`)) >> simp[]
QED
