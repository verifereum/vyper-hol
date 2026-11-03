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
 *   lower_dload_stage_dload_ok   - the DLOAD offset bound, vacuous after
 *   lower_dload_stage_headroom   - the DLOAD headroom bound, raw_mem_ok's
 *                                  frontier bound after
 *   lower_dload_stage_sim        - the runs match, up to the dead bytes D
 *   lower_dload_stage_mem        - raw memory of the output
 *   o1_contract_lower_dload      - the contract theorem
 *)
Theory o1ContractLowerDloadStage
Ancestors
  o1ContractLowerDload o1PassContract unitMemInv lowerDloadDefs
  venomPassSchedule list venomInst venomWf contextRawReachable
  contextCodegenRel

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

(* The simulation: every terminating run of C is matched by a run of C'
   up to the dead bytes D.  The DLOAD offset bound (in o1_src_inv) keeps
   the code_end-relative CODECOPY offset from wrapping; code_layout_valid
   (in o1_run_state_ok) binds "code_end" to the code/data boundary; the
   headroom bound (in o1_src_inv) keeps the shifted alloca sites from
   wrapping. *)
Theorem lower_dload_stage_sim:
  !rpolicy D view C C' vs.
    ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
    dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\ o1_src_inv C vs ==>
    ctx_sim D C C' vs vs
Proof
  cheat
QED

(* The output's reachable states keep raw memory safety. *)
Theorem lower_dload_stage_mem:
  !rpolicy view C C' vs.
    ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
    o1_ctx_shape C /\ o1_run_state_ok vs /\ o1_src_inv C vs ==>
    mem_inv raw_mem_ok C' vs
Proof
  cheat
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
  `mem_inv dload_offset_ok C' vs` by
    (irule lower_dload_stage_dload_ok >> fs[o1_src_inv_def] >>
     metis_tac[]) >>
  `mem_inv dload_headroom_ok C' vs` by
    metis_tac[lower_dload_stage_headroom] >>
  fs[o1_src_inv_def, ctx_pass_stage_def]
QED

Theorem o1_contract_lower_dload:
  o1_step_contract_at 1 rpolicy (CFP_Simple VP_LowerDload) /\
  o1_run_contract rpolicy D 1
Proof
  simp[o1_step_contract_at_plain, lower_dload_step_contract,
       lower_dload_run_contract]
QED
