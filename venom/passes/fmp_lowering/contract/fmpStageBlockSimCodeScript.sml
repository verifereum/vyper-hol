(*
 * Target-side facts for FmpLowering's block simulation (fmpStageBlockSim):
 * the lowered function's blocks are well formed with distinct labels, a
 * straight-line run of a block's non-final instructions is skipped by
 * exec_block, a related INVOKE has a target instruction to run, and a
 * related RET returns the source's values.
 *
 * TOP-LEVEL:
 *   fmp_stage_target_shape   - the lowered function is well formed
 *   exec_block_run_prefix    - exec_block skips a run of non-final insts
 *   fmp_target_run_exec_block - likewise for fmp_target_run
 *   fmp_stage_invoke_target  - a related INVOKE has a target instruction
 *   fmp_stage_ret_step       - a related RET returns the same values
 *)
Theory fmpStageBlockSimCode
Ancestors
  o1LowerDloadOpaque ptrStaticDiscipline pointerConfinedDefs memLocDefs pred_set
  fmpStageOpBaseActual fmpStepStructural fmpStepLayout fmpLowerDefs
  fmpStageOpBase fmpStageControl fmpStageRel passSharedProps runInstsProps
  venomWf o1PassContract ptrDiscipline contextCodegenRel analysisSimDefs
  venomExecSemantics venomState venomInst finite_map list rich_list
  fmpLowerProps fmpLowerIndexedProps fmpStageControlWalk dftGasToListReachBoundary

(* Why: the block simulation reads the target's next instruction off the
   lowered block (unique labels) and knows that only its last
   instruction is a terminator. *)
Theorem fmp_stage_target_shape:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\ MEM fn C.ctx_functions /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' ==>
  ALL_DISTINCT (fn_labels fn') /\ EVERY bb_well_formed fn'.fn_blocks
Proof
  strip_tac >>
  drule_all fmp_stage_actual_witness >> strip_tac >>
  `o1_fn_shape C fn` by gvs[fmp_stage_ctx_def, o1_ctx_shape_def, EVERY_MEM] >>
  `wf_function fn /\ first_block_no_phi fn` by gvs[o1_fn_shape_def] >>
  gvs[fmp_stage_lowered_def] >>
  `fmp_lower_function ctx0 sp fn = SOME (fn',sp')` by
    simp[fmp_lower_function_def] >>
  drule_all fmp_lower_function_structure >>
  drule fmp_lower_function_preserves_labels >>
  gvs[wf_function_def]
QED

(* Why: the restores, DALLOCA's expansion and the root run straight-line
   (run_insts); when an instruction of the block follows them, none of
   them is the block's terminator, so exec_block runs them the same way. *)
Theorem exec_block_run_prefix_gen[local]:
  !n fuel ctx bb j s s1.
    bb_well_formed bb /\ j + n < LENGTH bb.bb_instructions /\
    run_insts fuel ctx (TAKE n (DROP j bb.bb_instructions)) s = OK s1 ==>
    exec_block fuel ctx bb (s with vs_inst_idx := j) =
    exec_block fuel ctx bb (s1 with vs_inst_idx := j + n)
Proof
  Induct >- simp[run_insts_def] >>
  rpt strip_tac >>
  `j < LENGTH bb.bb_instructions` by simp[] >>
  `DROP j bb.bb_instructions =
   EL j bb.bb_instructions :: DROP (SUC j) bb.bb_instructions` by
    (qspecl_then [`bb.bb_instructions`,`j`] mp_tac
       rich_listTheory.DROP_EL_CONS >>
     impl_tac >- simp[] >> simp[arithmeticTheory.ADD1]) >>
  gvs[run_insts_def, AllCaseEqs()] >>
  rename1 `step_inst _ _ _ s = OK s2` >>
  `~is_terminator (EL j bb.bb_instructions).inst_opcode` by
    (strip_tac >> gvs[bb_well_formed_def] >> res_tac >> simp[]) >>
  drule_then (qspecl_then [`fuel`,`ctx`,`s`,`j`] mp_tac)
    step_inst_non_term_idx >>
  simp[] >> strip_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  simp[get_instruction_def] >>
  first_x_assum (qspecl_then [`fuel`,`ctx`,`bb`,`SUC j`,`s2`,`s1`] mp_tac) >>
  simp[arithmeticTheory.ADD_CLAUSES]
QED

Theorem exec_block_run_prefix:
  !n fuel ctx bb s s1.
    bb_well_formed bb /\ s.vs_inst_idx + n < LENGTH bb.bb_instructions /\
    run_insts fuel ctx (TAKE n (DROP s.vs_inst_idx bb.bb_instructions)) s =
      OK s1 ==>
    exec_block fuel ctx bb s =
    exec_block fuel ctx bb (s1 with vs_inst_idx := s.vs_inst_idx + n)
Proof
  rpt strip_tac >>
  qspecl_then [`n`,`fuel`,`ctx`,`bb`,`s.vs_inst_idx`,`s`,`s1`] mp_tac
    exec_block_run_prefix_gen >>
  simp[]
QED

Theorem fmp_target_run_exec_block:
  fmp_target_run fuel C' name t n t1 /\
  lookup_function name C'.ctx_functions = SOME fn' /\
  EVERY bb_well_formed fn'.fn_blocks /\
  lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
  t.vs_inst_idx + n < LENGTH bb'.bb_instructions ==>
  exec_block fuel C' bb' t = exec_block fuel C' bb' t1
Proof
  rw[fmp_target_run_def] >> gvs[] >>
  `!lbl bbs bb. lookup_block lbl bbs = SOME bb ==> MEM bb bbs` by
    (Induct_on `bbs` >> rw[lookup_block_def, FIND_thm] >>
     gvs[lookup_block_def] >> res_tac >> simp[]) >>
  `bb_well_formed bb'` by (res_tac >> gvs[EVERY_MEM]) >>
  `t.vs_inst_idx + n < LENGTH bb'.bb_instructions` by simp[] >>
  drule_all exec_block_run_prefix >> simp[]
QED

Theorem fmp_code_invoke_root[local]:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fmp_stage_root infos ctx fn = SOME (lbl,rp) /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  idx < LENGTH bb.bb_instructions /\
  (EL idx bb.bb_instructions).inst_opcode = INVOKE ==>
  rp <= idx
Proof
  simp[fmp_stage_root_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule split_fmp_entry_reconstruct >> strip_tac >>
  drule split_fmp_entry_users >> strip_tac >>
  Cases_on `retpc` >>
  (gvs[lookup_block_def, FIND_thm, callLayoutDefsTheory.OPTION_TO_LIST_def] >>
   imp_res_tac split_fmp_entry_retpc_opcode >>
   spose_not_then assume_tac >>
   Cases_on `idx < LENGTH users`
   >- (gvs[EL_APPEND1, EVERY_EL] >>
       qpat_x_assum `!n. n < LENGTH users ==> _` drule >> simp[]) >>
   gvs[EL_APPEND_EQN] >>
   `idx = LENGTH users` by decide_tac >> gvs[] >>
   gvs[fmp_stage_lowered_def, fmp_lower_function_with_info_def,
       fmp_make_root_layout_def, AllCaseEqs()])
QED

Theorem fmp_code_walk_bound[local]:
  fmp_lower_indexed infos ctx runner lbl k sp rs (inst::xs) = SOME (out,left,sp') /\
  (!j b. MEM ((lbl,j),b) rs <=> k <= j /\ FLOOKUP plan (lbl,j) = SOME b) ==>
  (if (lbl,k) IN FDOM plan then 1 else 0) < LENGTH out
Proof
  simp[fmp_lower_indexed_cons] >> rpt strip_tac >> gvs[] >>
  drule fmp_control_emit_length >> strip_tac >>
  drule fmp_control_inst_length >> strip_tac >>
  drule fmp_select_point_restores_once >> strip_tac >>
  Cases_on `(lbl,k) IN FDOM plan` >> simp[]
  >- (`?b. FLOOKUP plan (lbl,k) = SOME b` by simp[flookup_thm] >>
      `MEM b bases` by metis_tac[arithmeticTheory.LESS_EQ_REFL] >>
      `0 < LENGTH bases` by (Cases_on `bases` >> gvs[]) >>
      Cases_on `inst.inst_opcode = DALLOCA` >> gvs[]) >>
  Cases_on `inst.inst_opcode = DALLOCA` >> gvs[]
QED

Theorem fmp_code_unlowered_no_raw[local]:
  fmp_stage_lowered infos ctx runner fn fn' /\
  ~(fn.fn_fmp_signature = NONE /\
    ?info. FLOOKUP infos fn.fn_name = SOME info /\
      (info.fi_needs_fmp \/ info.fi_publishes_fmp)) ==>
  no_raw_fmp_ops fn
Proof
  simp[fmp_stage_lowered_def] >> strip_tac >>
  gvs[fmp_lower_function_with_info_def, AllCaseEqs()] >>
  irule fmp_no_need_input_no_raw >> metis_tac[]
QED

Theorem fmp_code_empty_index[local]:
  !idx. idx <= LENGTH xs /\ EVERY (\i. i.inst_opcode <> DALLOCA) xs ==>
  fmp_stage_tidx FEMPTY NONE lbl xs idx = idx
Proof
  Induct >> simp[fmp_stage_tidx_def, GENLIST, SUM_SNOC] >>
  rpt strip_tac >>
  `idx <= LENGTH xs` by decide_tac >>
  first_x_assum drule >> simp[fmp_stage_tidx_def] >> strip_tac >>
  `idx < LENGTH xs` by decide_tac >>
  gvs[EVERY_EL] >> first_x_assum drule >> simp[]
QED

Theorem fmp_code_unlowered_index[local]:
  fmp_stage_lowered infos ctx runner fn fn' /\
  ~(fn.fn_fmp_signature = NONE /\
    ?info. FLOOKUP infos fn.fn_name = SOME info /\
      (info.fi_needs_fmp \/ info.fi_publishes_fmp)) /\
  MEM bb fn.fn_blocks /\ idx < LENGTH bb.bb_instructions ==>
  fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
    lbl bb.bb_instructions idx = idx
Proof
  rpt strip_tac >>
  drule_all fmp_stage_unlowered >> strip_tac >>
  drule_all fmp_code_unlowered_no_raw >> strip_tac >>
  simp[] >> irule fmp_code_empty_index >> simp[] >>
  gvs[no_raw_fmp_ops_def, EVERY_MEM] >> rpt strip_tac >>
  `MEM i (fn_insts fn)` by
    (simp[fn_insts_def] >> irule venomFnInstsProofsTheory.mem_fn_insts_blocks >>
     qexists_tac `bb` >> simp[]) >>
  first_x_assum drule >> simp[is_raw_fmp_opcode_def] >> metis_tac[]
QED

Theorem fmp_code_invoke_bound[local]:
  fmp_stage_lowered infos ctx runner fn fn' /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  idx < LENGTH bb.bb_instructions /\
  (EL idx bb.bb_instructions).inst_opcode = INVOKE ==>
  ?bb'. lookup_block lbl fn'.fn_blocks = SOME bb' /\
    fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
      lbl bb.bb_instructions idx +
      (if (lbl,idx) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0)
      < LENGTH bb'.bb_instructions
Proof
  rpt strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    (fs[lookup_block_def] >> imp_res_tac stackPlanGenTheory.FIND_SOME_MEM >> gvs[]) >>
  Cases_on `fn.fn_fmp_signature = NONE /\
    ?info. FLOOKUP infos fn.fn_name = SOME info /\
      (info.fi_needs_fmp \/ info.fi_publishes_fmp)`
  >- (`!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) /\
         bb.bb_label = rl ==> rp <= idx` by
        (rpt strip_tac >> irule fmp_code_invoke_root >> metis_tac[]) >>
      `idx <= LENGTH bb.bb_instructions` by decide_tac >>
      drule fmp_stage_tidx_code >> simp[] >>
      disch_then (qspecl_then [`idx`, `bb`] mp_tac) >>
      simp[] >> strip_tac >>
      `DROP idx bb.bb_instructions =
         EL idx bb.bb_instructions :: DROP (SUC idx) bb.bb_instructions` by
        simp[DROP_CONS_EL] >>
      qpat_x_assum `DROP idx bb.bb_instructions = _` SUBST_ALL_TAC >>
      drule_all fmp_code_walk_bound >> strip_tac >>
      qmatch_asmsub_rename_tac `lookup_block lbl fn'.fn_blocks = SOME target` >>
      qexists_tac `target` >> simp[] >>
      Cases_on `(lbl,idx) IN FDOM (fmp_stage_plan infos ctx fn)` >>
      fs[LENGTH_DROP] >> decide_tac) >>
  drule_all fmp_code_unlowered_index >> strip_tac >>
  drule_all fmp_stage_unlowered >> strip_tac >>
  qexists_tac `bb` >> gvs[]
QED

(* Why: fmp_invoke_sim takes the target INVOKE as given; at a related
   point past the restores the target has an instruction there (the
   lowered INVOKE). *)
Theorem fmp_stage_invoke_target:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  inst.inst_opcode = INVOKE /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' ==>
  ?inst'. active_inst fn' inst' t
Proof
  strip_tac >>
  drule_all fmp_stage_frame_facts >> strip_tac >>
  `ALL_DISTINCT (fn_labels fn)` by
    gvs[o1_fn_shape_def, wf_function_def] >>
  drule_all dftGasToListReachBoundaryTheory.active_inst_lookup_distinct >>
  strip_tac >>
  gvs[get_instruction_def, AllCaseEqs()] >>
  gvs[fmp_stage_rel_def, fmp_frame_rel_def] >>
  drule_all fmp_code_invoke_bound >> strip_tac >>
  qmatch_asmsub_rename_tac `lookup_block t.vs_current_bb fn'.fn_blocks = SOME target` >>
  qexists_tac `EL t.vs_inst_idx target.bb_instructions` >>
  simp[active_inst_def] >> qexists_tac `target` >>
  gvs[lookup_block_def] >>
  imp_res_tac stackPlanGenTheory.FIND_SOME_MEM >> gvs[]
QED

Theorem fmp_run_ret_clean[local]:
  ptr_use_static_ok P pv inst /\ inst.inst_opcode = RET /\
  FDOM G SUBSET pv /\ MEM op inst.inst_operands ==>
  op_prov G op = NONE
Proof
  strip_tac >> Cases_on `op` >> simp[op_prov_def] >>
  rename1 `MEM (Var v) inst.inst_operands` >>
  `v NOTIN pv` by
    (strip_tac >> gvs[ptr_use_static_ok_def, is_pointer_preserving_op_def,
       mem_read_ops_def, mem_write_ops_def] >> metis_tac[]) >>
  fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem fmp_run_operand_defined[local]:
  fmp_env_rel sm fn live G tv s t /\ s.vs_labels = t.vs_labels /\
  eval_operand op s = SOME x ==> ?y. eval_operand op t = SOME y
Proof
  Cases_on `op` >>
  simp[eval_operand_def, lookup_var_def, fmp_env_rel_def] >> metis_tac[]
QED

Theorem fmp_run_ret_front_operand[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  inst.inst_opcode = RET /\ inst.inst_operands <> [] /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  MEM op (FRONT inst.inst_operands) /\ eval_operand op s = SOME x ==>
  eval_operand op t = SOME x
Proof
  strip_tac >> drule_all fmp_stage_frame_facts >> strip_tac >>
  `MEM op inst.inst_operands` by metis_tac[rich_listTheory.MEM_FRONT_NOT_NIL] >>
  `!v. op = Var v ==> ~retpc_var fn v` by
    (gvs[o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def] >>
     metis_tac[o1LowerDloadOpaqueTheory.ret_front_non_retpc]) >>
  `ptr_use_static_ok P (fn_pv P fn) inst` by
    (gvs[EVERY_MEM, fn_static_ptr_ok_def] >> metis_tac[]) >>
  drule fmp_stage_prov_support >> disch_then (qspec_then `P` mp_tac) >>
  simp[] >> strip_tac >>
  `op_prov G op = NONE` by metis_tac[fmp_run_ret_clean] >>
  `op_taint tn op = {}` by metis_tac[o1LowerDloadGhostTheory.ret_operand_untainted] >>
  `inst.inst_opcode <> PHI` by simp[] >>
  drule_all fmp_stage_operand >> simp[] >> strip_tac >>
  gvs[fmp_value_rel_def, o1LowerDloadRelocationKernelTheory.ld_value_agree_def,
      word_agree_except_bits] >>
  simp[fcpTheory.CART_EQ]
QED

Theorem fmp_run_eval_front_transfer[local]:
  !ops xs s t.
  eval_operands ops s = SOME xs /\
  (!op x. MEM op ops /\ eval_operand op s = SOME x ==>
     ?y. eval_operand op t = SOME y) /\
  (!op x. MEM op (FRONT ops) /\ eval_operand op s = SOME x ==>
     eval_operand op t = SOME x) ==>
  ?ys. eval_operands ops t = SOME ys /\ LENGTH ys = LENGTH xs /\
       FRONT ys = FRONT xs
Proof
  Induct >> simp[eval_operands_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `ops`
  >- (gvs[eval_operands_def, AllCaseEqs()] >> metis_tac[]) >>
  gvs[eval_operands_def, AllCaseEqs()] >>
  first_x_assum (qspecl_then [`v'::vs'`, `s`, `t`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  strip_tac >> qexists `v::ys` >>
  `eval_operand h t = SOME v` by metis_tac[] >>
  gvs[eval_operands_def]
QED

(* Why: fmp_stage_result's RET case.  RET returns its front operands,
   which carry no provenance (no pointer reaches RET: ptr_use_static_ok)
   and no taint (taint_ok) and aren't the return pc (opaque_use_ok), so
   the relation makes them equal; RET changes no state. *)
Theorem fmp_stage_ret_step:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  inst.inst_opcode = RET /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  step_inst k C inst s = IntRet ir s1 ==>
  s1 = s /\ ir.iret_adopt_fmp = NONE /\
  ?jr. (!k'. step_inst k' C' inst t = IntRet jr t) /\
       jr.iret_values = ir.iret_values /\ jr.iret_adopt_fmp = NONE
Proof
  strip_tac >>
  `fmp_env_rel sm fn
     (live_vars_at (liveness_analyze fn) s.vs_current_bb s.vs_inst_idx)
     G tn.t_var s t /\ s.vs_labels = t.vs_labels` by
    (gvs[fmp_stage_rel_def, fmp_frame_rel_def] >> metis_tac[]) >>
  `!op x. MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
     ?y. eval_operand op t = SOME y` by
    metis_tac[fmp_run_operand_defined] >>
  `inst.inst_operands <> []` by
    (strip_tac >> gvs[step_inst_non_invoke, step_inst_base_def, eval_operands_def]) >>
  `!op x. MEM op (FRONT inst.inst_operands) /\
     eval_operand op s = SOME x ==> eval_operand op t = SOME x` by
    metis_tac[fmp_run_ret_front_operand] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  drule_all fmp_run_eval_front_transfer >> strip_tac >>
  qexists `<|iret_values := FRONT ys; iret_adopt_fmp := NONE|>` >>
  Cases_on `ys` >> gvs[step_inst_non_invoke, step_inst_base_def]
QED
