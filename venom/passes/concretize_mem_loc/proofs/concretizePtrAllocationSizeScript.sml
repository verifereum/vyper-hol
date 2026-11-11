Theory concretizePtrAllocationSize
Ancestors venomWfProps
  concretizePtrActivationSupport concretizePtrAllocationOrigins
  concretizeMemLocDefs concretizeMemLocTransitionProofs concretizeAnalysisBoundary
  o1PassContract unitTransformDefs ptrDiscipline ptrDisciplineEmptyTaint
  venomWf venomInst venomState venomExecSemantics venomMemProps
  contextCodegenRel removeUnusedSsaProofs finite_map list words

(* General unique-key FIND interface, not tied to instruction records. *)
Theorem find_unique_key[local]:
  !xs x. ALL_DISTINCT (MAP key xs) /\ MEM x xs /\ Q x ==>
  FIND (\y. Q y /\ key y = key x) xs = SOME x
Proof
  Induct >> simp[FIND_thm] >> rpt strip_tac >> gvs[] >>
  IF_CASES_TAC >> gvs[MEM_MAP] >> metis_tac[]
QED

Theorem ptr_alloca_inst_size:
  fn_inst_ids_distinct fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit n] ==>
  get_alloca_size fn (Allocation inst.inst_id) = w2n n
Proof
  strip_tac >>
  `FIND (\i. is_alloca_op i.inst_opcode /\ i.inst_id = inst.inst_id)
    (FLAT (MAP (\bb. bb.bb_instructions) fn.fn_blocks)) = SOME inst` by
    (ho_match_mp_tac find_unique_key >> simp[is_alloca_op_def] >>
     gvs[fn_inst_ids_distinct_def, fn_insts_def, fn_insts_blocks_flat,
         MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss]) >>
  simp[get_alloca_size_def]
QED

Theorem ptr_size_step[local]:
  alloca_sizes_match fn s /\ fn_inst_ids_distinct fn /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode <> DALLOCA /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel ctx inst s = OK s' ==>
  alloca_sizes_match fn s'
Proof
  strip_tac >> Cases_on `inst.inst_opcode = ALLOCA`
  >- (qpat_x_assum `step_inst fuel ctx inst s = OK s'` mp_tac >>
      simp[step_inst_non_invoke] >> pure_once_rewrite_tac[step_inst_base_def] >>
      pure_asm_rewrite_tac[] >> simp[AllCaseEqs()] >> strip_tac >>
      `get_alloca_size fn (Allocation inst.inst_id) = w2n alloc_size` by
        metis_tac[ptr_alloca_inst_size] >>
      gvs[exec_alloca_def, AllCaseEqs(), update_var_def] >>
      fs[alloca_sizes_match_def, FLOOKUP_UPDATE, AllCaseEqs()] >> metis_tac[]) >>
  `~is_alloca_op inst.inst_opcode` by
    (Cases_on `inst.inst_opcode` >> gvs[is_alloca_op_def]) >>
  `s'.vs_allocas = s.vs_allocas` by
    metis_tac[step_inst_non_alloca_preserves_allocas] >>
  fs[alloca_sizes_match_def]
QED

Theorem ptr_frame_sizes:
  !vs ctx stk PG G tn fn inst s.
  frame_reachable vs ctx stk PG G tn fn inst s ==>
  o1_run_state_ok vs /\ o1_ctx_shape ctx /\ ~ctx_has_dalloca ctx ==>
  MEM fn ctx.ctx_functions /\ alloca_sizes_match fn s /\
  EVERY (\f. MEM f.cf_fn ctx.ctx_functions /\
             alloca_sizes_match f.cf_fn f.cf_state) stk
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- (rpt strip_tac >>
      `s.vs_allocas = vs.vs_allocas` by (drule enters_block_allocas >> simp[]) >>
      fs[alloca_sizes_match_def, o1_run_state_ok_def, o1_initial_state_ok_def] >>
      metis_tac[lookup_function_MEM])
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      qpat_x_assum `_ ==> _` mp_tac >> simp[] >> strip_tac >>
      `MEM inst (fn_insts fn)` by
        (gvs[active_inst_def, fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
         metis_tac[MEM_EL]) >>
      `alloca_sizes_match fn s'` by
        (irule ptr_size_step >>
         fs[o1_ctx_shape_def, o1_fn_shape_def, ctx_has_dalloca_def,
            EVERY_MEM, wf_function_def] >> metis_tac[]) >>
      fs[alloca_sizes_match_def])
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      qpat_x_assum `_ ==> _` mp_tac >> simp[] >> strip_tac >>
      `~is_alloca_op inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
        (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def, is_alloca_op_def]) >>
      `s'.vs_allocas = s.vs_allocas` by
        metis_tac[step_inst_non_alloca_preserves_allocas] >>
      drule enters_block_allocas >> fs[alloca_sizes_match_def])
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      qpat_x_assum `_ ==> _` mp_tac >> simp[] >> strip_tac >>
      `cs.vs_allocas = FEMPTY` by metis_tac[setup_callee_empty_allocas] >>
      `s''.vs_allocas = FEMPTY` by metis_tac[enters_block_allocas] >>
      simp[alloca_sizes_match_def] >> metis_tac[lookup_function_MEM]) >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  qpat_x_assum `_ ==> _` mp_tac >> simp[] >> strip_tac >>
  `s'.vs_allocas = f.cf_state.vs_allocas` by metis_tac[ptr_return_allocas] >>
  fs[alloca_sizes_match_def]
QED

Theorem ptr_frame_current_allocation_size:
  frame_reachable vs ctx stk PG G tn fn inst s /\
  o1_run_state_ok vs /\ o1_ctx_shape ctx /\ ~ctx_has_dalloca ctx /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
  get_alloca_size fn (Allocation aid) = sz
Proof
  strip_tac >> drule_all ptr_frame_sizes >>
  simp[alloca_sizes_match_def] >> metis_tac[]
QED

Theorem ptr_frame_saved_allocation_size:
  frame_reachable vs ctx stk PG G tn fn inst s /\
  o1_run_state_ok vs /\ o1_ctx_shape ctx /\ ~ctx_has_dalloca ctx /\
  MEM f stk /\ FLOOKUP f.cf_state.vs_allocas aid = SOME (b,sz) ==>
  get_alloca_size f.cf_fn (Allocation aid) = sz
Proof
  strip_tac >> drule_all ptr_frame_sizes >>
  simp[EVERY_MEM, alloca_sizes_match_def] >> metis_tac[]
QED

Theorem ptr_context_size_without_import:
  ~MEM a (MAP FST imports) ==>
  context_alloca_size fn imports a = get_alloca_size fn a
Proof
  Induct_on `imports` >> simp[context_alloca_size_def, FIND_thm] >>
  gen_tac >> PairCases_on `h` >> fs[context_alloca_size_def, FIND_thm]
QED

Theorem ptr_frame_context_allocation_size:
  frame_reachable vs ctx stk PG G tn fn inst s /\
  o1_run_state_ok vs /\ o1_ctx_shape ctx /\ ~ctx_has_dalloca ctx /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
  ~MEM (Allocation aid) (MAP FST imports) ==>
  context_alloca_size fn imports (Allocation aid) = sz
Proof
  metis_tac[ptr_frame_current_allocation_size, ptr_context_size_without_import]
QED
