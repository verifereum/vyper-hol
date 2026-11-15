Theory fmpStageFmpStepsRetpcControl
Ancestors
  fmpStageFmpStepsRetpcLayout fmpStageFmpStepsRetpcPrefix
  fmpStageOpBase fmpStageControl fmpStageRel fmpLowerDefs fmpWfDefs
  o1PassContract unitShapeDefs callLayoutDefs contextCodegenRel venomExecProofs
  fmpLowerProps fmpStepLayout combinatorics
  venomInst venomState list rich_list finite_map words

Theorem fmp_retpc_source_facts:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  inst.inst_opcode = RETPC_PARAM ==>
  fn.fn_fmp_signature = NONE /\
  C.ctx_entry <> SOME fn.fn_name
Proof
  strip_tac >> drule_all fmp_stage_frame_facts >> strip_tac >>
  fs[o1_fn_shape_def, fn_shape_ok_def] >>
  strip_tac >> fs[entry_fn_no_params_def, EVERY_MEM] >>
  metis_tac[is_param_opcode_def]
QED

Theorem fmp_retpc_lowered_info[local]:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fn.fn_fmp_signature = NONE ==>
  canonical_param_prefix fn /\ ?info. FLOOKUP infos fn.fn_name = SOME info
Proof
  simp[fmp_stage_lowered_def] >> strip_tac >>
  gvs[fmp_lower_function_with_info_def, fmp_lower_input_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem fmp_retpc_layout:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  inst.inst_opcode = RETPC_PARAM /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  fmp_stage_lowered infos ctx runner fn fn' ==>
  ?users suffix pc.
    split_fmp_entry fn = SOME (FmpEntryLayout users (SOME inst) suffix) /\
    users = fn_user_param_insts fn /\ s.vs_inst_idx = LENGTH users /\
    s.vs_current_bb = (HD fn.fn_blocks).bb_label /\
    inst.inst_operands = [Lit (n2w (LENGTH users))] /\
    inst.inst_outputs = [pc] /\ LENGTH users < dimword (:256) /\
    ~((s.vs_current_bb,s.vs_inst_idx) IN FDOM (fmp_stage_plan infos ctx fn)) /\
    (fmp_stage_root infos ctx fn = NONE \/
     fmp_stage_root infos ctx fn = SOME (s.vs_current_bb,SUC s.vs_inst_idx) /\
     ~fn_is_context_entry ctx fn)
Proof
  strip_tac >> drule_all fmp_retpc_source_facts >> strip_tac >>
  drule_all fmp_retpc_lowered_info >> strip_tac >>
  drule_all fmp_retpc_user_arity >> strip_tac >>
  drule_all fmp_retpc_split_location >> strip_tac >> gvs[] >>
  Cases_on `fn.fn_blocks` >- gvs[split_fmp_entry_def] >>
  conj_tac >- (irule fmp_retpc_prefix_plan_absent >> simp[] >> metis_tac[]) >>
  Cases_on `fmp_stage_root infos ctx fn` >> simp[] >>
  rename1 `fmp_stage_root infos ctx fn = SOME x` >> PairCases_on `x` >>
  `MEM fn C.ctx_functions` by metis_tac[fmp_stage_frame_facts] >>
  drule_all fmp_stage_witness_pin >> strip_tac >>
  `~fn_is_context_entry ctx fn` by metis_tac[] >>
  drule_all fmp_retpc_lowered_info >> strip_tac >>
  drule_all fmp_retpc_root_location >> gvs[]
QED

Theorem fmp_retpc_prefix_tidx:
  split_fmp_entry fn = SOME (FmpEntryLayout users (SOME inst) suffix) /\
  fn.fn_blocks = entry::rest /\ n <= LENGTH users ==>
  fmp_stage_tidx (fmp_stage_plan infos ctx fn) root entry.bb_label
    entry.bb_instructions n = n +
    (case root of NONE => 0 | SOME (rl,rp) =>
      if entry.bb_label = rl /\ rp <= n then 1 else 0)
Proof
  strip_tac >> pure_rewrite_tac[fmp_stage_tidx_def] >>
  `EVERY (\i. i.inst_opcode = PARAM) users` by
    metis_tac[split_fmp_entry_users] >>
  drule split_fmp_entry_reconstruct >> simp[] >> strip_tac >>
  `GENLIST (\j. (if (entry.bb_label,j) IN FDOM (fmp_stage_plan infos ctx fn)
                  then 1 else 0) +
                (if (EL j entry.bb_instructions).inst_opcode = DALLOCA
                 then 4 else 1)) n = GENLIST (K (1:num)) n` by
    (irule GENLIST_CONG >> simp[] >> rpt strip_tac >>
     `m < LENGTH users` by decide_tac >>
     `~((entry.bb_label,m) IN FDOM (fmp_stage_plan infos ctx fn))` by
       (irule fmp_retpc_prefix_plan_absent >> simp[] >> metis_tac[]) >>
     `EL m entry.bb_instructions = EL m users` by simp[EL_APPEND1] >>
     fs[EVERY_EL, EL_APPEND1]) >>
  pop_assum mp_tac >> simp[SUM_GENLIST_K] >>
  disch_then (mp_tac o AP_TERM ``SUM : num list -> num``) >>
  simp[SUM_GENLIST_K]
QED

Theorem fmp_retpc_target_prefix:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fn.fn_fmp_signature = NONE /\
  split_fmp_entry fn = SOME (FmpEntryLayout users (SOME inst) suffix) /\
  (fmp_stage_root infos ctx fn = NONE \/
   fmp_stage_root infos ctx fn = SOME (lbl,SUC (LENGTH users)) /\
   ~fn_is_context_entry ctx fn) ==>
  ?entry rest tail.
    fn'.fn_blocks = entry::rest /\
    fn_entry_label fn = SOME entry.bb_label /\
    (if fmp_stage_root infos ctx fn = NONE then
       entry.bb_instructions = users ++ inst::tail
     else ?id. entry.bb_instructions = users ++
       mk_inst id FMP_PARAM [Lit (n2w (LENGTH users))] [runner] ::
       set_param_index (SUC (LENGTH users)) inst :: tail)
Proof
  strip_tac >> drule_all fmp_retpc_lowered_info >> strip_tac >>
  Cases_on `fmp_stage_root infos ctx fn = NONE`
  >- (`~info.fi_needs_fmp` by
        (fs[fmp_stage_root_def] >> Cases_on `fn.fn_blocks` >>
         gvs[split_fmp_entry_def]) >>
      drule_all fmp_retpc_lowered_no_root_prefix >> strip_tac >>
      drule_all fmp_retpc_lowered_entry_label >> strip_tac >>
      qexistsl [`entry`, `rest`, `tail`] >> simp[]) >>
  `~fn_is_context_entry ctx fn` by metis_tac[] >>
  `info.fi_needs_fmp` by (gvs[fmp_stage_root_def]) >>
  drule_all fmp_retpc_lowered_root_prefix >> strip_tac >>
  drule_all fmp_retpc_lowered_entry_label >> strip_tac >>
  qexistsl [`entry`, `rest`, `tail`] >> gvs[] >> qexists `id` >> simp[]
QED

Theorem fmp_retpc_successor_tidx:
  split_fmp_entry fn = SOME (FmpEntryLayout users (SOME inst) suffix) /\
  fn.fn_blocks = entry::rest /\ inst.inst_opcode = RETPC_PARAM /\
  (root = NONE \/ root = SOME (entry.bb_label,SUC (LENGTH users))) ==>
  fmp_stage_tidx (fmp_stage_plan infos ctx fn) root entry.bb_label
    entry.bb_instructions (SUC (LENGTH users)) =
    LENGTH users + (if root = NONE then 1 else 2)
Proof
  strip_tac >>
  drule split_fmp_entry_reconstruct >> simp[] >> strip_tac >>
  `EL (LENGTH users) entry.bb_instructions = inst` by simp[EL_APPEND_EQN] >>
  `~((entry.bb_label,LENGTH users) IN FDOM (fmp_stage_plan infos ctx fn))` by
    (irule fmp_retpc_prefix_plan_absent >> simp[] >> metis_tac[]) >>
  `fmp_stage_tidx (fmp_stage_plan infos ctx fn) root entry.bb_label
     entry.bb_instructions (LENGTH users) = LENGTH users` by
    (drule (Q.INST [`n` |-> `LENGTH users`, `root` |-> `root`] fmp_retpc_prefix_tidx) >>
     simp[] >> disch_then drule >> gvs[]) >>
  fs[fmp_stage_tidx_def, GENLIST, SUM_SNOC] >> gvs[]
QED

Theorem fmp_retpc_target_run:
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  fmp_stage_lowered infos ctx runner fn fn' /\ fn.fn_fmp_signature = NONE /\
  split_fmp_entry fn = SOME (FmpEntryLayout users (SOME inst) suffix) /\
  s.vs_current_bb = (HD fn.fn_blocks).bb_label /\ s.vs_inst_idx = LENGTH users /\
  t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = LENGTH users /\
  inst.inst_opcode = RETPC_PARAM /\ inst.inst_outputs = [pc] /\
  inst.inst_operands = [Lit (n2w (LENGTH users))] /\
  LENGTH users < dimword (:256) /\
  (fmp_stage_root infos ctx fn = NONE \/
   fmp_stage_root infos ctx fn = SOME (s.vs_current_bb,SUC s.vs_inst_idx) /\
   ~fn_is_context_entry ctx fn) /\
  (fmp_stage_root infos ctx fn <> NONE ==>
    LENGTH users < LENGTH t.vs_params /\ EL (LENGTH users) t.vs_params = n2w lo) ==>
  ?n t1. 1 <= n /\ n <= 2 /\
    (!fuel. fmp_target_run fuel C' fn.fn_name t n t1) /\
    (if fmp_stage_root infos ctx fn = NONE then
       n = 1 /\ t1 = (update_var pc t.vs_return_pc_token t) with
         vs_inst_idx := t.vs_inst_idx + 1
     else n = 2 /\
       t1 = (update_var pc t.vs_return_pc_token (update_var runner (n2w lo) t)) with
         vs_inst_idx := t.vs_inst_idx + 2)
Proof
  strip_tac >>
  drule fmp_retpc_target_prefix >>
  simp[] >> strip_tac >>
  `t.vs_current_bb = entry.bb_label` by
    (Cases_on `fn.fn_blocks` >> gvs[split_fmp_entry_def,
      fn_entry_label_def, entry_block_def]) >>
  `lookup_block t.vs_current_bb fn'.fn_blocks = SOME entry` by
    simp[lookup_block_def, FIND_thm] >>
  Cases_on `fmp_stage_root infos ctx fn = NONE` >> gvs[]
  >- (`DROP t.vs_inst_idx entry.bb_instructions = inst::tail` by (asm_rewrite_tac[] >> pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
      metis_tac[fmp_retpc_single_run]) >>
  `DROP t.vs_inst_idx entry.bb_instructions =
    mk_inst id FMP_PARAM [Lit (n2w (LENGTH users))] [runner] ::
    set_param_index (SUC (LENGTH users)) inst :: tail` by (asm_rewrite_tac[] >> pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
  metis_tac[fmp_retpc_root_run]
QED
