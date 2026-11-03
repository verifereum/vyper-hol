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
 *   lower_dload_stage_shape      - no eom and no DALLOCA kept
 *   lower_dload_stage_dload_ok   - the DLOAD offset bound, vacuous after
 *   lower_dload_stage_sim        - the runs match, up to the dead bytes D
 *   lower_dload_stage_mem        - raw memory, pointer discipline, taint
 *   o1_contract_lower_dload      - the contract theorem
 *)
Theory o1ContractLowerDloadStage
Ancestors
  o1ContractLowerDload o1PassContract ptrDiscipline unitMemInv
  lowerDloadDefs venomPassSchedule

(* The conjuncts of the output's row that don't read its runs. *)
Theorem lower_dload_stage_shape:
  !rpolicy view C C'.
    ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
    o1_ctx_shape C /\
    EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\ ~ctx_has_dalloca C ==>
    EVERY (\fn. fn.fn_eom = NONE) C'.ctx_functions /\ ~ctx_has_dalloca C'
Proof
  cheat
QED

(* The output has no DLOAD or DLOADBYTES, so its DLOAD offset bound holds
   at every reachable instruction. *)
Theorem lower_dload_stage_dload_ok:
  !rpolicy view C C' vs.
    ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
    o1_ctx_shape C /\ o1_run_state_ok vs /\
    mem_inv raw_mem_ok C vs ==>
    mem_inv dload_offset_ok C' vs
Proof
  cheat
QED

(* The simulation: every terminating run of C is matched by a run of C'
   up to the dead bytes D.  The DLOAD offset bound (in o1_src_inv) keeps
   the code_end-relative CODECOPY offset from wrapping; code_layout_valid
   (in o1_run_state_ok) binds "code_end" to the code/data boundary. *)
Theorem lower_dload_stage_sim:
  !rpolicy D view C C' vs.
    ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
    o1_ctx_shape C /\ o1_run_state_ok vs /\ o1_src_inv D C vs ==>
    ctx_sim D C C' vs vs
Proof
  cheat
QED

(* The conjuncts of the output's row that read its reachable states. *)
Theorem lower_dload_stage_mem:
  !rpolicy D view C C' vs.
    ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
    o1_ctx_shape C /\ o1_run_state_ok vs /\ o1_src_inv D C vs ==>
    mem_inv raw_mem_ok C' vs /\
    (?lo. fixed_region_reserved lo C' /\ ptr_discipline lo C' vs) /\
    taint_within D C' vs
Proof
  cheat
QED

Theorem lower_dload_run_contract:
  o1_run_contract rpolicy D 1
Proof
  `EL 1 o1_fn_passes = CFP_Simple VP_LowerDload` by
    simp[o1_fn_passes_def] >>
  simp[o1_run_contract_def, o1_stage_contract_def, o1_inv_def, o1_pre_def] >>
  rpt gen_tac >> strip_tac >>
  `ctx_sim D C C' vs vs` by metis_tac[lower_dload_stage_sim] >>
  drule_all lower_dload_stage_mem >> strip_tac >>
  fs[o1_src_inv_def] >>
  `mem_inv dload_offset_ok C' vs` by metis_tac[lower_dload_stage_dload_ok] >>
  drule_all lower_dload_stage_shape >> strip_tac >> simp[] >>
  metis_tac[]
QED

Theorem o1_contract_lower_dload:
  o1_step_contract rpolicy (CFP_Simple VP_LowerDload) /\
  o1_run_contract rpolicy D 1
Proof
  simp[lower_dload_step_contract, lower_dload_run_contract]
QED
