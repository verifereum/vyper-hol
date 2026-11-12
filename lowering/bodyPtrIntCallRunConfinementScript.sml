Theory bodyPtrIntCallRunConfinement
Ancestors vyperCompiler compileVyper bodyPtrIntCallRunBlock bodyPtrIntCallAllocation
  bodyPtrIntCallConfinement bodyPtrIntCallTaintBounds bodyPtrIntCallWriteFrame
  ptrSafeRun ptrDiscipline venomExecSemantics venomExecProofs venomExecProps
  venomInst venomInstProps venomState unitShapeDefs finite_map pred_set list arithmetic

Theorem intcall_checked_fn_no_setfmp[local]:
  fn_ptr_ok_check PL fn /\ MEM inst (fn_insts fn) ==>
  inst.inst_opcode <> SETFMP
Proof
  simp[fn_ptr_ok_check_def] >>
  rpt BasicProvers.TOP_CASE_TAC >> simp[] >> rpt strip_tac >>
  fs[EVERY_MEM, inst_ptr_ok_check_def] >> metis_tac[]
QED

Theorem intcall_context_instruction_no_setfmp[local]:
  lowering_context_ok ctx /\ ~ctx_has_dalloca ctx /\ MEM fn ctx.ctx_functions /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst ==>
  inst.inst_opcode <> SETFMP
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `MEM inst bb.bb_instructions` by
    (fs[get_instruction_def, AllCaseEqs()] >> metis_tac[EL_MEM]) >>
  `MEM inst (fn_insts fn)` by
    metis_tac[fn_insts_def, MEM_fn_insts_blocks_iff] >>
  fs[lowering_context_ok_def, ptr_ok_check_def, ctx_has_dalloca_def,
     EXISTS_MEM, EVERY_MEM] >>
  metis_tac[intcall_checked_fn_no_setfmp]
QED

Theorem intcall_context_instruction_no_dalloca[local]:
  ~ctx_has_dalloca ctx /\ MEM fn ctx.ctx_functions /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst ==>
  inst.inst_opcode <> DALLOCA
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `MEM inst bb.bb_instructions` by
    (fs[get_instruction_def, AllCaseEqs()] >> metis_tac[EL_MEM]) >>
  fs[ctx_has_dalloca_def, EXISTS_MEM, fn_insts_def,
     MEM_fn_insts_blocks_iff] >> metis_tac[]
QED

Theorem intcall_mem_frame_entry[local]:
  intcall_mem_frame P tn0 (entry_taint_vars fn s tn) <=>
  intcall_mem_frame P tn0 tn
Proof
  simp[entry_taint_vars_def, intcall_mem_frame_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[]
QED

Theorem intcall_mem_frame_invoke[local]:
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm, ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  intcall_mem_frame P tn0
    (SND (ghost_blocks fuel ctx callee (MAP (op_prov G) ops) FEMPTY
            (tn with t_var := FEMPTY) cs)) ==>
  intcall_mem_frame P tn0 (SND (ghost_step fuel ctx PG G tn inst s))
Proof
  strip_tac >> drule_all ghost_step_invoke >>
  disch_then (fn th => rewrite_tac[th]) >> gvs[intcall_mem_frame_def]
QED

Theorem intcall_cursor_lookup[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  step_inst fuel ctx inst s = OK t /\ ~is_terminator inst.inst_opcode ==>
  lookup_block (t with vs_inst_idx := k).vs_current_bb fn.fn_blocks = SOME bb
Proof
  strip_tac >> drule_all step_preserves_control_flow >> simp[]
QED

Theorem intcall_ordinary_cursor[local]:
  lowering_context_ok ctx /\ ~ctx_has_dalloca ctx /\
  MEM fn ctx.ctx_functions /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel ctx inst s = OK t /\
  ptr_safe_step D 0 fuel ctx fn PG G tn inst s /\
  intcall_alloc_outside P s /\ intcall_prov_outside P PG G /\
  intcall_word_taint_bounded tn /\ intcall_mem_frame P tn0 tn ==>
  intcall_alloc_outside P (t with vs_inst_idx := k) /\
  intcall_prov_outside P PG (FST (ghost_step fuel ctx PG G tn inst s)) /\
  intcall_word_taint_bounded (SND (ghost_step fuel ctx PG G tn inst s)) /\
  intcall_mem_frame P tn0 (SND (ghost_step fuel ctx PG G tn inst s))
Proof
  strip_tac >>
  `inst.inst_opcode <> SETFMP` by
    metis_tac[intcall_context_instruction_no_setfmp] >>
  `inst.inst_opcode <> DALLOCA` by
    metis_tac[intcall_context_instruction_no_dalloca] >>
  `intcall_alloc_outside P t` by metis_tac[intcall_step_alloc_outside] >>
  `access_ok 0 G fn inst s` by fs[ptr_safe_step_def, ptr_inst_ok_def] >>
  `intcall_mem_frame P tn (step_taint inst s t tn)` by
    (irule intcall_mem_frame_step >> conj_tac
     >- metis_tac[intcall_step_new_site_outside] >>
     drule intcall_word_taint_operands >> strip_tac >>
     metis_tac[intcall_written_taint_outside_zero]) >>
  simp[Once ghost_step_def] >> rpt conj_tac
  >- (fs[intcall_alloc_outside_def] >> metis_tac[])
  >- metis_tac[intcall_step_prov_outside]
  >- metis_tac[intcall_word_taint_ghost_step] >>
  drule_all ghost_step_non_invoke >> strip_tac >> simp[] >>
  metis_tac[intcall_mem_frame_trans]
QED

Theorem intcall_invoke_frame_lift[local]:
  (!callee PG G tn cs.
    MEM callee ctx.ctx_functions /\ intcall_alloc_outside P cs /\
    intcall_prov_outside P PG G /\ intcall_word_taint_bounded tn /\
    ptr_safe_blocks D 0 fuel ctx callee PG G tn cs ==>
    intcall_mem_frame P tn (SND (ghost_blocks fuel ctx callee PG G tn cs))) /\
  inst.inst_opcode = INVOKE /\
  ptr_safe_step D 0 fuel ctx fn PG G tn inst s /\
  intcall_alloc_outside P s /\ intcall_prov_outside P PG G /\
  intcall_word_taint_bounded tn ==>
  intcall_mem_frame P tn (SND (ghost_step fuel ctx PG G tn inst s))
Proof
  strip_tac >>
  Cases_on `decode_invoke inst` >- simp[Once ghost_step_def, intcall_mem_frame_refl] >>
  PairCases_on `x` >>
  Cases_on `lookup_function x0 ctx.ctx_functions`
  >- simp[Once ghost_step_def, intcall_mem_frame_refl] >>
  Cases_on `eval_operands x1 s`
  >- simp[Once ghost_step_def, intcall_mem_frame_refl] >>
  Cases_on `setup_callee x x' s`
  >- simp[Once ghost_step_def, intcall_mem_frame_refl] >>
  rename1 `setup_callee callee args s = SOME cs` >>
  irule intcall_mem_frame_invoke >> goal_assum (drule_at Any) >> simp[] >>
  `MEM callee ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `intcall_alloc_outside P cs` by
    (irule intcall_alloc_setup >> goal_assum (drule_at Any) >>
     fs[intcall_alloc_outside_def]) >>
  `intcall_prov_outside P (MAP (op_prov G) x1) FEMPTY` by
    metis_tac[intcall_prov_outside_invoke] >>
  `ptr_safe_blocks D 0 fuel ctx callee (MAP (op_prov G) x1)
     FEMPTY (tn with t_var := FEMPTY) cs` by fs[ptr_safe_step_def] >>
  `intcall_word_taint_bounded (tn with t_var := FEMPTY)` by
    simp[intcall_word_taint_empty] >>
  first_x_assum (drule_at (Pat `ptr_safe_blocks _ _ _ _ _ _ _ _ _`)) >>
  simp[intcall_mem_frame_def] >> disch_then irule >>
  irule intcall_prov_outside_invoke >> qexists_tac `PG` >> first_assum ACCEPT_TAC
QED

Theorem intcall_invoke_prov[local]:
  inst.inst_opcode = INVOKE /\ intcall_prov_outside P PG G ==>
  intcall_prov_outside P PG (FST (ghost_step fuel ctx PG G tn inst s))
Proof
  strip_tac >> simp[Once ghost_step_def] >>
  Cases_on `decode_invoke inst` >> simp[] >> PairCases_on `x` >> simp[] >>
  Cases_on `lookup_function x0 ctx.ctx_functions` >> simp[] >>
  Cases_on `eval_operands x1 s` >> simp[] >>
  Cases_on `setup_callee x x' s` >> simp[] >>
  fs[intcall_prov_outside_def, FLOOKUP_DRESTRICT] >> metis_tac[]
QED

Definition intcall_cursor_inv_def:
  intcall_cursor_inv P fn bb PG tn0 s G tn <=>
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    intcall_alloc_outside P s /\ intcall_prov_outside P PG G /\
    intcall_word_taint_bounded tn /\ intcall_mem_frame P tn0 tn
End

Theorem intcall_cursor_step[local]:
  (!callee PG G tn cs.
    MEM callee ctx.ctx_functions /\ intcall_alloc_outside P cs /\
    intcall_prov_outside P PG G /\ intcall_word_taint_bounded tn /\
    ptr_safe_blocks D 0 fuel ctx callee PG G tn cs ==>
    intcall_mem_frame P tn (SND (ghost_blocks fuel ctx callee PG G tn cs))) /\
  lowering_context_ok ctx /\ ~ctx_has_dalloca ctx /\ MEM fn ctx.ctx_functions /\
  intcall_cursor_inv P fn bb PG tn0 s G tn /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  ptr_safe_step D 0 fuel ctx fn PG G tn inst s /\
  step_inst fuel ctx inst s = OK t /\ ~is_terminator inst.inst_opcode ==>
  intcall_cursor_inv P fn bb PG tn0 (t with vs_inst_idx := SUC s.vs_inst_idx)
    (FST (ghost_step fuel ctx PG G tn inst s))
    (SND (ghost_step fuel ctx PG G tn inst s))
Proof
  simp[intcall_cursor_inv_def] >> strip_tac >>
  `lookup_block (t with vs_inst_idx := SUC s.vs_inst_idx).vs_current_bb
      fn.fn_blocks = SOME bb` by metis_tac[intcall_cursor_lookup] >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (rpt conj_tac
      >- fs[]
      >- (drule_all intcall_invoke_alloc_outside >> simp[])
      >- metis_tac[intcall_invoke_prov]
      >- metis_tac[intcall_word_taint_ghost_step] >>
      `intcall_mem_frame P tn (SND (ghost_step fuel ctx PG G tn inst s))` by
        (drule_at (Pat `ptr_safe_step _ _ _ _ _ _ _ _ _ _`) intcall_invoke_frame_lift >>
         simp[] >> disch_then irule >> first_assum ACCEPT_TAC) >>
      metis_tac[intcall_mem_frame_trans]) >>
  drule_all intcall_ordinary_cursor >> fs[]
QED

Theorem intcall_terminator_cursor[local]:
  lowering_context_ok ctx /\ ~ctx_has_dalloca ctx /\ MEM fn ctx.ctx_functions /\
  intcall_cursor_inv P fn bb PG tn0 s G tn /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  step_inst fuel ctx inst s = OK t /\ is_terminator inst.inst_opcode ==>
  intcall_alloc_outside P t /\
  intcall_prov_outside P PG (entry_prov fn t G) /\
  intcall_word_taint_bounded (entry_taint_vars fn t tn) /\
  intcall_mem_frame P tn0 (entry_taint_vars fn t tn)
Proof
  simp[intcall_cursor_inv_def] >> strip_tac >>
  `inst.inst_opcode <> INVOKE` by
    (Cases_on `inst.inst_opcode` >> fs[is_terminator_def]) >>
  `inst.inst_opcode <> SETFMP` by metis_tac[intcall_context_instruction_no_setfmp] >>
  `inst.inst_opcode <> DALLOCA` by metis_tac[intcall_context_instruction_no_dalloca] >>
  rpt conj_tac
  >- metis_tac[intcall_step_alloc_outside]
  >- metis_tac[intcall_entry_prov_outside]
  >- metis_tac[intcall_word_taint_entry] >>
  simp[intcall_mem_frame_entry]
QED

Theorem intcall_block_frame_lift[local]:
  (!callee PG G tn cs.
    MEM callee ctx.ctx_functions /\ intcall_alloc_outside P cs /\
    intcall_prov_outside P PG G /\ intcall_word_taint_bounded tn /\
    ptr_safe_blocks D 0 fuel ctx callee PG G tn cs ==>
    intcall_mem_frame P tn (SND (ghost_blocks fuel ctx callee PG G tn cs))) /\
  lowering_context_ok ctx /\ ~ctx_has_dalloca ctx /\ MEM fn ctx.ctx_functions /\
  intcall_cursor_inv P fn bb PG tn0 s G tn /\
  ptr_safe_block D 0 fuel ctx fn PG G tn bb s ==>
  intcall_mem_frame P tn0 (SND (ghost_block fuel ctx fn PG G tn bb s))
Proof
  strip_tac >> ho_match_mp_tac intcall_ghost_block_invariant >>
  qexists_tac `intcall_cursor_inv P fn bb PG tn0` >>
  qexistsl_tac [`D`, `0`] >> rpt conj_tac
  >- simp[intcall_cursor_inv_def]
  >- (rpt strip_tac >> irule intcall_cursor_step >>
      goal_assum (drule_at Any) >> simp[] >> qexists_tac `D` >> simp[])
  >- (rpt strip_tac >> drule_all intcall_terminator_cursor >> strip_tac >>
      first_x_assum (drule_at (Pat `ptr_safe_blocks _ _ _ _ _ _ _ _ _`)) >>
      simp[] >> strip_tac >> metis_tac[intcall_mem_frame_trans])
  >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC
QED

Theorem intcall_blocks_mem_frame:
  !fuel fn PG G tn s.
  lowering_context_ok ctx /\ ~ctx_has_dalloca ctx /\ MEM fn ctx.ctx_functions /\
  intcall_alloc_outside P s /\ intcall_prov_outside P PG G /\
  intcall_word_taint_bounded tn /\ ptr_safe_blocks D 0 fuel ctx fn PG G tn s ==>
  intcall_mem_frame P tn (SND (ghost_blocks fuel ctx fn PG G tn s))
Proof
  Induct_on `fuel`
  >- simp[Once ghost_blocks_def, intcall_mem_frame_refl] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- simp[Once ghost_blocks_def, intcall_mem_frame_refl] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >>
  simp[Once ghost_blocks_def, intcall_mem_frame_refl] >>
  rename1 `eval_phis s bb.bb_instructions = OK t` >>
  `t.vs_current_bb = s.vs_current_bb` by metis_tac[eval_phis_preserves_current_bb] >>
  `intcall_alloc_outside P (t with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    metis_tac[intcall_alloc_phis_entry] >>
  irule intcall_block_frame_lift >>
  simp[intcall_cursor_inv_def, intcall_mem_frame_refl] >>
  qexists_tac `D` >>
  conj_tac >- (rpt strip_tac >> first_x_assum irule >> simp[]) >>
  fs[Once ptr_safe_blocks_def]
QED

Theorem intcall_block_mem_frame:
  lowering_context_ok ctx /\ ~ctx_has_dalloca ctx /\ MEM fn ctx.ctx_functions /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  intcall_alloc_outside P s /\ intcall_prov_outside P PG G /\
  intcall_word_taint_bounded tn /\ ptr_safe_block D 0 fuel ctx fn PG G tn bb s ==>
  intcall_mem_frame P tn (SND (ghost_block fuel ctx fn PG G tn bb s))
Proof
  strip_tac >> irule intcall_block_frame_lift >>
  simp[intcall_cursor_inv_def, intcall_mem_frame_refl] >>
  qexists_tac `D` >> simp[] >> rpt strip_tac >>
  irule intcall_blocks_mem_frame >> goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `D` >> first_assum ACCEPT_TAC
QED

Theorem intcall_run_mem_frame:
  lowering_context_ok ctx /\ ~ctx_has_dalloca ctx /\ MEM fn ctx.ctx_functions /\
  intcall_alloc_outside P s /\ intcall_prov_outside P PG G /\
  intcall_word_taint_bounded tn /\ ptr_safe_run D 0 fuel ctx fn PG G tn s ==>
  intcall_mem_frame P tn (SND (ghost_run fuel ctx fn PG G tn s))
Proof
  strip_tac >> Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- simp[ghost_run_def, intcall_mem_frame_refl] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  simp[ghost_run_def] >> irule intcall_block_mem_frame >>
  goal_assum (drule_at Any) >> fs[ptr_safe_run_def] >>
  qexists_tac `D` >> first_assum ACCEPT_TAC
QED

(* Consumer handoff: choose P at the caller expression entry and retain it
   across nested calls. Staging supplies intcall_alloc_outside and complete
   operand-site separation, not merely footprint disjointness. A callee's
   empty local t_var supplies intcall_word_taint_empty. The compiler check
   supplies lowering_context_ok; the pointer judgment supplies no DALLOCA.
   Apply intcall_blocks_mem_frame or intcall_run_mem_frame for ghost memory
   framing, and intcall_ghost_kept_frame for the caller's protected set.
   Concrete memory equality on successful IntRet is supplied separately by
   the authorized S1 intcall_callee_exit frame; it is NOT asserted here on
   unsuccessful runs. Its exclusion of allocations with id >= sa.cs_next_id
   matches fresh return-buffer/staging sites. The final caller local-value
   robustness proof must combine that concrete frame with this taint frame.
*)
