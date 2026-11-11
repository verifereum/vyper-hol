(*
 * LowerDload against the O1 pass contract: the stage part, and the
 * contract theorem.
 *
 * LowerDload is walk run 1: it takes row 1 of o1_inv (o1_src_inv) to
 * row 2 (o1_src_inv again).  Each DLOAD becomes ALLOCA 32, an ADD of the
 * offset to "code_end", a CODECOPY into the new site and an MLOAD from
 * it; each DLOADBYTES becomes the ADD and a CODECOPY.  So the output has
 * no DLOAD/DLOADBYTES, and one more 32-byte ALLOCA site per DLOAD, which
 * moves the later sites of a frame.
 *
 * TOP-LEVEL:
 *   lower_dload_stage_shape        - no eom and no DALLOCA kept
 *   lower_dload_stage_fmp_free     - no FMP signature or raw FMP op kept
 *   lower_dload_stage_callee_first - the callee-first order kept
 *   lower_dload_stage_ssa_form     - SSA form kept
 *   lower_dload_stage_dload_ok     - the DLOAD offset bound, vacuous after
 *   lower_dload_stage_headroom     - the DLOAD headroom bound, raw_mem_ok's
 *                                    frontier bound after
 *   (the simulation and the raw memory, pointer and taint rows are in
 *    o1ContractLowerDload{Sim,Mem,Ptr,Taint})
 *   lower_dload_fn_row             - function row 1 to row 2
 *   o1_contract_lower_dload        - the contract theorem
 *)
Theory o1ContractLowerDloadStage
Ancestors
  o1ContractLowerDload o1PassContract ptrDiscipline unitMemInv
  lowerDloadDefs venomPassSchedule list venomInst venomWf
  contextRawReachable contextCodegenRel fcgDefs fcgBridge
  venomFnScheduleRunner o1ContractLowerDloadSim o1ContractLowerDloadMem
  o1ContractLowerDloadPtr o1ContractLowerDloadTaint lowerDloadMakeSsaInput
  venomFnScheduleRunnerProps

(* ===== Helpers for the shape and DLOAD-bound lemmas ===== *)

(* Every output function of the stage is the lowering of an input one. *)
Theorem lower_dload_stage_fn[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  MEM g C'.ctx_functions ==>
  ?f s t. MEM f C.ctx_functions /\ lower_dload_function_supply s f = (g,t)
Proof
  rw[ctx_pass_stage_def, LIST_REL_EL_EQN, MEM_EL] >>
  first_x_assum (qspec_then `n` mp_tac) >> impl_tac >- fs[] >> strip_tac >>
  gvs[fn_pass_step_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem lookup_function_name_rel[local]:
  !fs gs f.
    LIST_REL R fs gs /\ (!f g. R f g ==> g.fn_name = f.fn_name) /\
    lookup_function name fs = SOME f ==>
    ?g. lookup_function name gs = SOME g /\ R f g
Proof
  Induct >> Cases_on `gs` >> simp[lookup_function_def, FIND_thm] >>
  rpt strip_tac >> rename1 `R h1 h2` >>
  `h2.fn_name = h1.fn_name` by metis_tac[] >>
  Cases_on `h1.fn_name = name` >> gvs[] >>
  fs[GSYM lookup_function_def] >> metis_tac[]
QED

(* The output's entry function is the lowering of the input's. *)
Theorem lower_dload_stage_lookup[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  lookup_function name C.ctx_functions = SOME f ==>
  ?g s t. lookup_function name C'.ctx_functions = SOME g /\
          lower_dload_function_supply s f = (g,t)
Proof
  rw[ctx_pass_stage_def] >>
  drule_then (qspecl_then [`name`, `f`] mp_tac) lookup_function_name_rel >>
  impl_tac
  >- (simp[] >> rpt strip_tac >> gvs[fn_pass_step_def]) >>
  strip_tac >> gvs[fn_pass_step_def, AllCaseEqs()] >> metis_tac[]
QED

(* A well-formed DLOAD or DLOADBYTES is always expanded. *)
Theorem lower_dload_inst_supply_no_dload[local]:
  lower_dload_inst_supply s i = (xs,t) /\ inst_wf i ==>
  EVERY (\j. j.inst_opcode <> DLOAD /\ j.inst_opcode <> DLOADBYTES) xs
Proof
  strip_tac >> Cases_on `i.inst_opcode = DLOAD`
  >- (fs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
      gvs[lower_dload_inst_supply_def, AllCaseEqs()]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (fs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
      gvs[lower_dload_inst_supply_def, AllCaseEqs()]) >>
  gvs[lower_dload_inst_supply_def]
QED

Theorem raw_reachable_lookup[local]:
  !vs ctx fn inst s. raw_reachable vs ctx fn inst s ==>
    active_inst fn inst s /\ ?nm. lookup_function nm ctx.ctx_functions = SOME fn
Proof
  Induct_on `raw_reachable` >> rw[] >> metis_tac[]
QED

(* The output has no DLOAD or DLOADBYTES. *)
Theorem lower_dload_stage_no_dload[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  o1_ctx_shape C /\ MEM g C'.ctx_functions /\ MEM inst (fn_insts g) ==>
  inst.inst_opcode <> DLOAD /\ inst.inst_opcode <> DLOADBYTES
Proof
  strip_tac >> drule_all lower_dload_stage_fn >> strip_tac >>
  drule_all lower_dload_function_supply_member >> strip_tac >>
  `inst_wf i` by
    (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def, fn_inst_wf_def,
        fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  drule_all lower_dload_inst_supply_no_dload >> simp[EVERY_MEM] >>
  disch_then drule >> simp[]
QED

(* So its DLOAD offset bound holds at every reachable instruction. *)
Theorem lower_dload_stage_dload_ok:
  !rpolicy view C C' vs.
    ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
    o1_ctx_shape C /\ o1_run_state_ok vs /\
    mem_inv raw_mem_ok C vs ==>
    mem_inv dload_offset_ok C' vs
Proof
  rpt strip_tac >> fs[mem_inv_raw_reachable] >> conj_tac
  >- (drule_all lower_dload_stage_lookup >> strip_tac >>
      drule lower_dload_function_supply_labels >> strip_tac >>
      fs[ctx_pass_stage_def] >> metis_tac[]) >>
  rpt strip_tac >> rename1 `raw_reachable vs C' g inst s` >>
  drule raw_reachable_lookup >> strip_tac >>
  `MEM g C'.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `MEM inst (fn_insts g)` by
    (fs[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >>
     metis_tac[EL_MEM]) >>
  drule_all lower_dload_stage_no_dload >> simp[dload_offset_ok_def]
QED

(* And no DLOAD to need headroom for: the bound is raw_mem_ok's frontier
   bound. *)
Theorem lower_dload_stage_headroom:
  !rpolicy view C C' vs.
    ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
    o1_ctx_shape C /\ mem_inv raw_mem_ok C' vs ==>
    mem_inv dload_headroom_ok C' vs
Proof
  rpt strip_tac >>
  `ctx_dload_count C' = 0` by
    (simp[ctx_dload_count_def, SUM_eq_0, MEM_MAP, PULL_EXISTS,
          FILTER_EQ_NIL, EVERY_MEM] >>
     metis_tac[lower_dload_stage_no_dload]) >>
  irule mem_inv_mono >> qexists_tac `raw_mem_ok` >>
  simp[raw_mem_ok_def, dload_headroom_ok_def]
QED

(* ===== The cheap rows ===== *)

Theorem lower_dload_inst_supply_no_dalloca[local]:
  lower_dload_inst_supply s i = (xs,t) /\ i.inst_opcode <> DALLOCA ==>
  EVERY (\j. j.inst_opcode <> DALLOCA) xs
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >> rpt strip_tac >>
      gvs[]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >> rpt strip_tac >>
      gvs[]) >>
  rw[lower_dload_inst_supply_def] >> gvs[]
QED

Theorem lower_dload_inst_supply_no_raw_fmp[local]:
  lower_dload_inst_supply s i = (xs,t) /\ ~is_raw_fmp_opcode i.inst_opcode ==>
  EVERY (\j. ~is_raw_fmp_opcode j.inst_opcode) xs
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >> rpt strip_tac >>
      gvs[is_raw_fmp_opcode_def]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >> rpt strip_tac >>
      gvs[is_raw_fmp_opcode_def]) >>
  rw[lower_dload_inst_supply_def] >> gvs[]
QED

(* The expansion keeps an unset layout end and adds no DALLOCA. *)
Theorem lower_dload_stage_shape:
  !rpolicy view C C'.
    ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
    EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\ ~ctx_has_dalloca C ==>
    EVERY (\fn. fn.fn_eom = NONE) C'.ctx_functions /\ ~ctx_has_dalloca C'
Proof
  rpt strip_tac
  >- (rw[EVERY_MEM] >> drule_all lower_dload_stage_fn >> strip_tac >>
      fs[EVERY_MEM] >> first_x_assum drule >>
      gvs[lower_dload_function_supply_def, AllCaseEqs()] >> rw[]) >>
  fs[ctx_has_dalloca_def, EXISTS_MEM] >> rpt strip_tac >>
  drule_all lower_dload_stage_fn >> strip_tac >>
  drule_all lower_dload_function_supply_member >> strip_tac >>
  `i.inst_opcode <> DALLOCA` by metis_tac[] >>
  `EVERY (\j. j.inst_opcode <> DALLOCA) ys` by
    metis_tac[lower_dload_inst_supply_no_dalloca] >>
  fs[EVERY_MEM] >> metis_tac[]
QED

(* The expansion keeps the FMP signature and adds no raw FMP opcode. *)
Theorem lower_dload_stage_fmp_free:
  !rpolicy view C C'.
    ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
    fmp_free_ctx C ==> fmp_free_ctx C'
Proof
  rw[fmp_free_ctx_def, EVERY_MEM] >>
  drule_all lower_dload_stage_fn >> strip_tac >>
  first_x_assum drule >> strip_tac
  >- gvs[lower_dload_function_supply_def, AllCaseEqs()] >>
  fs[no_raw_fmp_ops_def] >> rpt strip_tac >>
  drule_all lower_dload_function_supply_member >> strip_tac >>
  `EVERY (\j. ~is_raw_fmp_opcode j.inst_opcode) ys` by
    metis_tac[lower_dload_inst_supply_no_raw_fmp] >>
  fs[EVERY_MEM] >> metis_tac[]
QED

(* Every INVOKE of an output function is one of its input's, so the
   output's call edges are among the input's. *)
Theorem lower_dload_function_supply_invoke_targets[local]:
  lower_dload_function_supply s f = (g,t) /\
  MEM n (fn_invoke_targets g) ==> MEM n (fn_invoke_targets f)
Proof
  rw[fn_invoke_targets_def, fcg_scan_function_def, mem_get_invoke_targets] >>
  `MEM inst (fn_insts f)` by
    (irule lower_dload_function_supply_control >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem lower_dload_stage_callee_first:
  !rpolicy view C C' names.
    ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
    callee_first names C.ctx_functions ==>
    callee_first names C'.ctx_functions
Proof
  rw[callee_first_def] >>
  drule_all lower_dload_stage_fn >> strip_tac >>
  drule lower_dload_function_supply_labels >> strip_tac >>
  drule_all lower_dload_function_supply_invoke_targets >> strip_tac >>
  metis_tac[]
QED

(* LowerDload's fresh variables keep SSA form. *)
Theorem lower_dload_stage_ssa_form:
  !rpolicy view C C'.
    ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
    EVERY ssa_form C.ctx_functions ==>
    EVERY ssa_form C'.ctx_functions
Proof
  rw[ctx_pass_stage_def, EVERY_EL, LIST_REL_EL_EQN] >>
  rename1 `n < LENGTH C.ctx_functions` >>
  qpat_x_assum `!n. n < LENGTH C.ctx_functions ==> ?observed. _`
    (qspec_then `n` mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  drule lower_dload_step_supply >> strip_tac >>
  metis_tac[lower_dload_function_supply_ssa_form]
QED

(* LowerDload keeps the inputs MakeSSA needs: it adds no PHI, keeps every
   block reachable, and each variable it introduces is defined before its
   uses in the same block. *)
Theorem lower_dload_stage_make_ssa_input_ok:
  !rpolicy view C C'.
    ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
    o1_ctx_shape C /\
    EVERY make_ssa_input_ok C.ctx_functions ==>
    EVERY make_ssa_input_ok C'.ctx_functions
Proof
  rw[ctx_pass_stage_def, EVERY_EL, LIST_REL_EL_EQN] >>
  rename1 `n < LENGTH C.ctx_functions` >>
  qpat_x_assum `!n. n < LENGTH C.ctx_functions ==> ?observed. _`
    (qspec_then `n` mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  `fn_inst_ids_distinct (EL n C.ctx_functions) /\
   fn_inst_wf (EL n C.ctx_functions)` by
    gvs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_EL] >>
  `make_ssa_input_ok (EL n C.ctx_functions)` by gvs[] >>
  metis_tac[lower_dload_fn_pass_step_make_ssa_input_ok]
QED

Theorem lower_dload_run_contract:
  o1_run_contract rpolicy D 1
Proof
  `EL 1 o1_fn_passes = CFP_Simple VP_LowerDload` by
    simp[o1_fn_passes_def] >>
  simp[o1_run_contract_def, o1_stage_contract_def, o1_inv_def] >>
  rpt gen_tac >> strip_tac >>
  `ctx_sim D C C' vs vs` by metis_tac[lower_dload_stage_sim] >>
  `mem_inv raw_mem_ok C' vs` by metis_tac[lower_dload_stage_mem] >>
  `taint_within D C' vs` by metis_tac[lower_dload_stage_taint] >>
  `mem_inv dload_offset_ok C' vs` by
    (irule lower_dload_stage_dload_ok >> fs[o1_src_inv_def] >>
     metis_tac[]) >>
  `mem_inv dload_headroom_ok C' vs` by
    metis_tac[lower_dload_stage_headroom] >>
  `EVERY (\fn. fn.fn_eom = NONE) C'.ctx_functions /\ ~ctx_has_dalloca C'` by
    (irule lower_dload_stage_shape >> fs[o1_src_inv_def] >> metis_tac[]) >>
  `fmp_free_ctx C'` by
    (irule lower_dload_stage_fmp_free >> fs[o1_src_inv_def] >> metis_tac[]) >>
  `callee_first names C'.ctx_functions` by
    metis_tac[lower_dload_stage_callee_first] >>
  `EVERY make_ssa_input_ok C'.ctx_functions` by
    (irule lower_dload_stage_make_ssa_input_ok >> fs[o1_src_inv_def] >>
     metis_tac[]) >>
  `EVERY ssa_form C'.ctx_functions` by
    metis_tac[lower_dload_stage_ssa_form] >>
  fs[o1_src_inv_def] >>
  `ptr_discipline lo C' vs` by
    (irule lower_dload_stage_ptr >> simp[o1_src_inv_def] >> metis_tac[]) >>
  `C'.ctx_global_reserved = C.ctx_global_reserved` by fs[ctx_pass_stage_def] >>
  fs[fixed_region_reserved_def] >> metis_tac[]
QED

(* One run takes function row 1 to row 2: it keeps a valid MakeSSA
   input, adds no raw FMP operation and keeps the FMP convention. *)
Theorem lower_dload_fn_row:
  fn_pass_step rpolicy (CFP_Simple VP_LowerDload) observed s fn out /\
  o1_ctx_shape observed.cu_context /\ o1_fn_row 1 fn ==>
  o1_fn_row 2 out.fpo_function
Proof
  strip_tac >>
  `MEM fn observed.cu_context.ctx_functions` by
    (gvs[fn_pass_step_def] >>
     metis_tac[lookup_unique_function_member]) >>
  `fn_inst_ids_distinct fn /\ fn_inst_wf fn` by
    gvs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >>
  gvs[o1_fn_row_def] >> rpt conj_tac
  >- metis_tac[lower_dload_fn_pass_step_make_ssa_input_ok]
  >- (drule lower_dload_step_supply >> strip_tac >>
      fs[no_raw_fmp_ops_def] >> rpt strip_tac >>
      drule_all lower_dload_function_supply_member >> strip_tac >>
      `EVERY (\j. ~is_raw_fmp_opcode j.inst_opcode) ys` by
        metis_tac[lower_dload_inst_supply_no_raw_fmp] >>
      fs[EVERY_MEM] >> metis_tac[]) >>
  drule fn_pass_step_fmp_sig_no_param >> simp[fn_pass_tag_def]
QED

Theorem o1_contract_lower_dload:
  o1_step_contract_at 1 rpolicy (CFP_Simple VP_LowerDload) /\
  o1_run_contract rpolicy D 1
Proof
  simp[lower_dload_run_contract] >>
  irule o1_step_contract_at_preserve >>
  simp[lower_dload_step_contract] >> metis_tac[lower_dload_fn_row]
QED
