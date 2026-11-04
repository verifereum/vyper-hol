(*
 * LowerDload against the O1 pass contract: the runs of the input and the
 * output match up to the dead bytes D.
 * Kept in its own theory so its proof can be worked on apart from the
 * other rows; o1ContractLowerDloadStage assembles them.
 *
 * TOP-LEVEL:
 *   lower_dload_stage_sim
 *)
Theory o1ContractLowerDloadSim
Ancestors
  o1ContractLowerDload o1PassContract ptrDiscipline unitMemInv
  lowerDloadDefs venomPassSchedule list venomFnScheduleRunner
  venomCompilerTypes irSupply venomPassDispatcher venomInst

(* The runner supplies a covering supply separately for each function. *)
Theorem lower_dload_stage_supply_rel:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' ==>
  LIST_REL (\f g. ?s t. ir_supply_covers_fn s f /\
                         lower_dload_function_supply s f = (g,t))
    C.ctx_functions C'.ctx_functions
Proof
  rw[ctx_pass_stage_def] >>
  irule LIST_REL_mono >> goal_assum (drule_at Any) >>
  rpt strip_tac >> gvs[fn_pass_step_def, AllCaseEqs()] >>
  rename1 `lower_dload_function_supply s f = (g,t)` >>
  `MEM f observed.cu_context.ctx_functions` by
    (gvs[lookup_unique_function_def, AllCaseEqs()] >>
     `MEM f (FILTER (\g. g.fn_name = f.fn_name)
                observed.cu_context.ctx_functions)` by simp[] >>
     gvs[MEM_FILTER]) >>
  qexistsl [`s`, `t`] >> simp[] >>
  gvs[ir_supply_covers_unit_def, ir_supply_covers_fn_def, list_subset_def,
      unit_ir_inst_ids_def, unit_ir_vars_def, unit_ir_labels_def,
      EVERY_MEM, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  metis_tac[]
QED

Theorem lower_dload_stage_lookup_supply:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  lookup_function name C.ctx_functions = SOME f ==>
  ?g s t. lookup_function name C'.ctx_functions = SOME g /\
          ir_supply_covers_fn s f /\
          lower_dload_function_supply s f = (g,t)
Proof
  strip_tac >> drule lower_dload_stage_supply_rel >>
  qpat_x_assum `ctx_pass_stage _ _ _ _ _` kall_tac >>
  qpat_x_assum `lookup_function _ _ = _` mp_tac >>
  qid_spec_tac `f` >>
  Q.SPEC_TAC (`C'.ctx_functions`, `gs`) >>
  Q.SPEC_TAC (`C.ctx_functions`, `fs`) >>
  Induct >> Cases_on `gs` >>
  simp[lookup_function_def, FIND_thm] >> rpt strip_tac >>
  rename1 `lower_dload_function_supply supply src = (dst,supply')` >>
  drule lower_dload_function_supply_labels >> strip_tac >>
  Cases_on `src.fn_name = name` >> gvs[] >>
  fs[GSYM lookup_function_def] >> metis_tac[]
QED

(* Zero-size allocation provenance cannot license a pointer comparison. *)
Theorem access_ok_zero_size_comparison:
  access_ok lo G fn inst s /\
  (inst.inst_opcode = LT \/ inst.inst_opcode = GT \/ inst.inst_opcode = EQ) /\
  inst.inst_operands = [Var u; Var w] /\ FLOOKUP G u = SOME (b,0)
  ==> F
Proof
  strip_tac >>
  `u IN FDOM G` by metis_tac[finite_mapTheory.FLOOKUP_DEF, optionTheory.NOT_SOME_NONE] >>
  fs[access_ok_def] >>
  first_x_assum (qspecl_then [`u`, `w`] mp_tac) >> simp[]
QED

(* Allocation boundary equations: no memory is initialized by ALLOCA. *)
Theorem lower_dload_alloca_fresh:
  inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE ==>
  exec_alloca inst s amount =
    OK (update_var out (n2w s.vs_alloca_next)
      (s with <|vs_allocas := s.vs_allocas |+
                    (inst.inst_id, (s.vs_alloca_next, w2n amount));
                vs_alloca_next := s.vs_alloca_next + w2n amount|>))
Proof
  simp[venomExecSemanticsTheory.exec_alloca_def]
QED

Theorem lower_dload_alloca_repeated:
  inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (addr,sz) ==>
  exec_alloca inst s amount = OK (update_var out (n2w addr) s)
Proof
  simp[venomExecSemanticsTheory.exec_alloca_def]
QED

Theorem lower_dload_merge_allocation_memory:
  (merge_callee_state caller callee).vs_allocas = caller.vs_allocas /\
  (merge_callee_state caller callee).vs_alloca_next = caller.vs_alloca_next /\
  (merge_callee_state caller callee).vs_memory = callee.vs_memory
Proof
  simp[venomExecSemanticsTheory.merge_callee_state_def]
QED

(* Within a nonwrapping site, unsigned comparison is independent of base. *)
Theorem lower_dload_site_comparisons:
  !b c sz i j.
    i <= sz /\ j <= sz /\
    b + sz < dimword (:256) /\ c + sz < dimword (:256) ==>
    (((n2w (b+i):bytes32) = n2w (b+j)) <=>
       ((n2w (c+i):bytes32) = n2w (c+j))) /\
    ((w2n (n2w (b+i):bytes32) < w2n (n2w (b+j):bytes32)) <=>
       (w2n (n2w (c+i):bytes32) < w2n (n2w (c+j):bytes32)))
Proof
  rpt strip_tac >>
  `b+i < dimword (:256) /\ b+j < dimword (:256) /\
   c+i < dimword (:256) /\ c+j < dimword (:256)` by decide_tac >>
  simp[GSYM wordsTheory.w2n_11, wordsTheory.w2n_n2w,
       arithmeticTheory.LESS_MOD]
QED

(* The simulation: every terminating run of C is matched by a run of C'
   up to the dead bytes D.  The DLOAD offset bound (in o1_src_inv) keeps
   the code_end-relative CODECOPY offset from wrapping; code_layout_valid
   (in o1_run_state_ok) binds "code_end" to the code/data boundary; the
   headroom bound (in o1_src_inv) and the callee-first order keep the
   shifted alloca sites from wrapping; the pointer discipline and the
   taint bound (in o1_src_inv) keep the shifted alloca addresses out of
   what the run observes. *)
Theorem lower_dload_stage_sim:
  !rpolicy D view C C' vs names.
    ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
    dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
    o1_src_inv D C vs /\ callee_first names C.ctx_functions ==>
    ctx_sim D C C' vs vs
Proof
  cheat
QED
