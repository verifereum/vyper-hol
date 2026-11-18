(*
 * Backward progress for FmpLowering's coverage across function
 * boundaries: the context entry's first block can be entered, a reachable
 * INVOKE enters its (non-entry) callee, and a RET the target takes returns
 * into the source caller (see fmpStageCoverBack for the setting).
 *
 * TOP-LEVEL:
 *   fmp_stage_back_entry - the context entry's block can be entered
 *   fmp_stage_back_call  - an INVOKE can enter its callee
 *   fmp_stage_back_ret   - a RET returns into its caller
 *)
Theory fmpStageCoverCall
Ancestors
  fmpStageCoverBack fmpCoverSavedOutputs
  fnFrameBoundaryInvoke
  fmpStageOpBase fmpStageRel o1PassContract ptrDiscipline contextCodegenRel
  unitTransformDefs passSimulationDefs venomExecSemantics venomState venomInst
  simplifyCfgAvailability o1ContractSimplifyCfgSrcFrame
  o1LowerDloadReadiness venomInstProofs1 concretizePtrOwnerPath
  venomWf
  finite_map words list
  o1LowerDloadStackFunctions ctxLookupAgreeHelpers
  unitShapeDefs venomWf

Theorem fmp_call_entry_ancestry[local]:
  !vs C stk PG G tn fn inst s.
    frame_reachable vs C stk PG G tn fn inst s ==>
    !names. callee_first names C.ctx_functions ==>
    EVERY (\g. C.ctx_entry = SOME g.fn_name \/
      ?root. C.ctx_entry = SOME root /\ list_precedes g.fn_name root names)
      (fn :: MAP (\f. f.cf_fn) stk)
Proof
  ho_match_mp_tac frame_reachable_strongind >> rpt conj_tac
  >- (rpt strip_tac >> drule lookup_function_selected_name >> simp[])
  >- (rpt strip_tac >> metis_tac[])
  >- (rpt strip_tac >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
      first_x_assum drule >> strip_tac >>
      `MEM fn C.ctx_functions` by
        metis_tac[scfg_frame_reachable_functions] >>
      `list_precedes fn'.fn_name fn.fn_name names` by
        (irule ld_active_callee_precedes >> metis_tac[]) >>
      gvs[] >> metis_tac[ld_list_precedes_trans])
  >> rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  first_x_assum drule >> simp[]
QED

(* Saved INVOKE control survives the return merge and output assignment. *)
Theorem fmp_back_saved_continuation[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C (f::stk) PG G tn fn rinst s /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state s_end)) = SOME s' ==>
  ?inst'. active_inst f.cf_fn inst'
    (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
Proof
  strip_tac >>
  drule scfg_frame_reachable_functions >> simp[] >> strip_tac >>
  drule ptr_owner_frame_active >> simp[] >> strip_tac >>
  `wf_function f.cf_fn` by
    (fs[fmp_stage_ctx_def, o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >>
     metis_tac[]) >>
  `s'.vs_current_bb = f.cf_state.vs_current_bb` by
    (qspec_then `\u. u.vs_current_bb` mp_tac bind_outputs_preserves >>
     simp[update_var_def] >> disch_then drule >>
     Cases_on `ret.iret_adopt_fmp` >>
     simp[adopt_return_fmp_def, merge_callee_state_def]) >>
  irule ld_nonterminator_successor >> simp[] >>
  qexists_tac `f.cf_inst` >> simp[is_terminator_def]
QED

(* Why it holds: the entry fn is wf_function with first_block_no_phi,
   and the initial state is o1_initial_state_ok. *)
Theorem fmp_stage_back_entry:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  C.ctx_entry = SOME name /\ lookup_function name C.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl ==>
  ?s1 inst.
    enters_block fn
      (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                  vs_inst_idx := 0 |>) s1 /\
    active_inst fn inst s1
Proof
  strip_tac >>
  `MEM fn C.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `wf_function fn /\ first_block_no_phi fn` by
    (fs[fmp_stage_ctx_def, o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >>
     metis_tac[]) >>
  Cases_on `fn.fn_blocks` >>
  gvs[fn_entry_label_def, entry_block_def] >>
  rename1 `fn.fn_blocks = bb::bbs` >>
  `bb.bb_instructions <> []` by
    metis_tac[wf_function_def, bb_well_formed_def, MEM] >>
  Cases_on `bb.bb_instructions` >> gvs[] >>
  rename1 `bb.bb_instructions = inst::rest` >>
  `inst.inst_opcode <> PHI` by fs[first_block_no_phi_def] >>
  qexistsl_tac
    [`vs with <|vs_prev_bb := NONE; vs_current_bb := bb.bb_label; vs_inst_idx := 0|>`,
     `inst`] >>
  simp[enters_block_def, active_inst_def, get_instruction_def,
       lookup_block_def, FIND_thm, eval_phis_def, phi_prefix_length_def] >>
  qexists_tac `bb` >> simp[]
QED

(* Why it holds: callee_first (o1PassContract) orders callees strictly
   before callers (list_precedes), so every active or saved frame's
   function is the entry or precedes it, and an INVOKE of the entry would
   make it precede itself.  INVOKE args hold no Labels, so eval_operands
   reduces to fmp_stage_src_defined; setup_callee needs nonempty blocks
   (wf_function); the callee's first block has no PHIs. *)
Theorem fmp_stage_back_call:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn ivk s /\ active_inst fn ivk s /\
  ivk.inst_opcode = INVOKE ==>
  ?nm ops callee args cs s1 inst.
    decode_invoke ivk = SOME (nm,ops) /\ C.ctx_entry <> SOME nm /\
    lookup_function nm C.ctx_functions = SOME callee /\
    eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
    enters_block callee cs s1 /\ active_inst callee inst s1
Proof
  strip_tac >>
  drule_all fmp_stage_frame_facts >> strip_tac >>
  `?nm ops. ivk.inst_operands = Label nm :: ops /\
     MEM nm (ctx_fn_names C)` by
    metis_tac[o1_fn_shape_def, fn_invoke_ok_def] >>
  `decode_invoke ivk = SOME (nm,ops)` by simp[decode_invoke_def] >>
  `?callee. lookup_function nm C.ctx_functions = SOME callee` by
    (Cases_on `lookup_function nm C.ctx_functions` >>
     fs[ctx_fn_names_def] >> metis_tac[lookup_function_not_mem]) >>
  `?names. callee_first names C.ctx_functions` by
    (fs[fmp_stage_ctx_def, o1_inv_def] >> metis_tac[]) >>
  `list_precedes callee.fn_name fn.fn_name names` by
    (irule ld_active_callee_precedes >> metis_tac[]) >>
  `C.ctx_entry <> SOME nm` by
    (drule_all fmp_call_entry_ancestry >> simp[] >> strip_tac >>
     drule lookup_function_selected_name >> strip_tac >>
     strip_tac >> gvs[] >>
     metis_tac[ld_list_precedes_trans, ld_list_precedes_irrefl]) >>
  `EVERY (\op. ~is_label_operand op) ops` by
    (`inst_shape_ok ivk` by
       (fs[o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM] >> metis_tac[]) >>
     qpat_x_assum `inst_shape_ok ivk` mp_tac >>
     simp[inst_shape_ok_def, label_positions_ok_def]) >>
  `IS_SOME (eval_operands ops s)` by
    (simp[eval_operands_IS_SOME_EVERY, EVERY_MEM] >> rpt strip_tac >>
     Cases_on `op` >> simp[eval_operand_def]
     >- (rename1 `MEM (Var v) ops` >>
         `MEM (Var v) ivk.inst_operands /\ ivk.inst_opcode <> PHI` by simp[] >>
         drule_all fmp_stage_src_defined >> simp[]) >>
     rename1 `MEM (Label l) ops` >>
     qpat_x_assum `EVERY (\op. ~is_label_operand op) ops` mp_tac >>
     simp[EVERY_MEM] >> disch_then (qspec_then `Label l` mp_tac) >>
     simp[stackPlanTypesTheory.is_label_operand_def]) >>
  Cases_on `eval_operands ops s` >> gvs[] >>
  `wf_function callee /\ first_block_no_phi callee` by
    (fs[fmp_stage_ctx_def, o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >>
     metis_tac[lookup_function_MEM]) >>
  `callee.fn_blocks <> []` by
    (fs[wf_function_def, fn_has_entry_def] >> Cases_on `callee.fn_blocks` >> fs[]) >>
  Cases_on `callee.fn_blocks` >> gvs[] >> rename1 `callee.fn_blocks = bb::bbs` >>
  `bb.bb_instructions <> []` by
    metis_tac[wf_function_def, bb_well_formed_def, MEM] >>
  Cases_on `bb.bb_instructions` >> gvs[] >> rename1 `bb.bb_instructions = first::rest` >>
  `first.inst_opcode <> PHI` by fs[first_block_no_phi_def] >>
  simp[setup_callee_def] >>
  qmatch_goalsub_abbrev_tac `enters_block callee cs` >>
  qexistsl_tac [`cs`, `first`] >>
  simp[enters_block_def, active_inst_def, Abbr `cs`, lookup_block_def,
       get_instruction_def, eval_phis_def, phi_prefix_length_def, FIND_thm] >>
  qexists_tac `bb` >> simp[]
QED

(* Why it holds: the source RET has nonempty, defined operands, so it
   returns IntRet; the target steps the same rinst, so the value lists
   have equal length.  The target INVOKE's outputs add [runner] only when
   the callee publishes its fmp, which no row-3 callee does (pre_fmp_ops
   excludes RETFMP and DRET), so the binds succeed together. *)
Theorem fmp_stage_back_ret:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C (f::stk) PG G tn fn rinst s /\
  active_inst fn rinst s /\ ~s.vs_halted /\ rinst.inst_opcode = RET /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T (f::stk) PG G tn fn s lo t
    ((tc,lc)::ts) /\
  lookup_function f.cf_fn.fn_name C'.ctx_functions = SOME fc' /\
  active_inst fc' ivk' tc /\
  step_inst k' C' rinst t = IntRet ret' t_end /\
  bind_outputs ivk'.inst_outputs ret'.iret_values
    (adopt_return_fmp ret' (merge_callee_state tc t_end)) = SOME t' ==>
  ?ret s_end s' inst'.
    step_inst k C rinst s = IntRet ret s_end /\
    bind_outputs f.cf_inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state f.cf_state s_end)) =
      SOME s' /\
    active_inst f.cf_fn inst'
      (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
Proof
  strip_tac >>
  `ivk'.inst_outputs = f.cf_inst.inst_outputs` by
    (irule fmp_cover_saved_outputs >> metis_tac[]) >>
  `s.vs_labels = t.vs_labels` by
    (fs[fmp_stage_rel_def, fmp_frame_rel_def] >> metis_tac[]) >>
  `rinst.inst_opcode <> PHI` by simp[] >>
  `!v. MEM (Var v) rinst.inst_operands ==> IS_SOME (lookup_var v s)` by
    (rpt strip_tac >> drule_all fmp_stage_src_defined >> simp[]) >>
  qpat_x_assum `step_inst k' C' rinst t = _` mp_tac >>
  simp[Once step_inst_def, step_inst_base_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  `IS_SOME (eval_operands rinst.inst_operands s)` by
    (`IS_SOME (eval_operands rinst.inst_operands t)` by simp[] >>
     fs[eval_operands_IS_SOME_EVERY, EVERY_MEM] >>
     rpt strip_tac >> Cases_on `op` >> fs[eval_operand_def] >>
     metis_tac[eval_operand_def]) >>
  Cases_on `eval_operands rinst.inst_operands s` >> gvs[] >>
  rename1 `eval_operands rinst.inst_operands s = SOME srcvals` >>
  rename1 `eval_operands rinst.inst_operands t = SOME (hdval::tlvals)` >>
  `LENGTH srcvals = LENGTH (hdval::tlvals)` by
    metis_tac[eval_operands_some_length] >>
  `srcvals <> []` by (Cases_on `srcvals` >> fs[]) >>
  `LENGTH f.cf_inst.inst_outputs = LENGTH (FRONT srcvals)` by
    (fs[bind_outputs_def] >>
     simp[LENGTH_FRONT] >> fs[]) >>
  `?s'. bind_outputs f.cf_inst.inst_outputs (FRONT srcvals)
      (merge_callee_state f.cf_state s) = SOME s'` by
    simp[bind_outputs_def] >>
  `bind_outputs f.cf_inst.inst_outputs
     (<| iret_values := FRONT srcvals; iret_adopt_fmp := NONE |>).iret_values
     (adopt_return_fmp
       <| iret_values := FRONT srcvals; iret_adopt_fmp := NONE |>
       (merge_callee_state f.cf_state s)) = SOME s'` by
    simp[adopt_return_fmp_def] >>
  drule_all fmp_back_saved_continuation >> strip_tac >>
  qexistsl [`<| iret_values := FRONT srcvals; iret_adopt_fmp := NONE |>`, `s`, `s'`, `inst'`] >>
  simp[adopt_return_fmp_def] >>
  Cases_on `srcvals` >> gvs[Once step_inst_def, step_inst_base_def]
QED
