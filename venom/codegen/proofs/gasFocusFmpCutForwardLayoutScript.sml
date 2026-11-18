(* Static layout of a forwarding interval at the actual FmpLowering edge. *)
Theory gasFocusFmpCutForwardLayout
Ancestors
  gasFocusFmpStagePin fmpStageCoverForwardInterval fmpStageCoverForwardPrefix
  fmpStageRel fmpStepBridge fmpStepSupply concretizeStageLookup lowerDloadPtrForward
  contextCodegenRel ctxLookupAgreeHelpers venomFnScheduleRunner
  venomFnScheduleRunnerProps irSupply o1PassContract venomWf venomWfProps
  venomInst venomExecSemantics venomExecProofs rich_list list finite_map

Theorem cut_forward_fetches[local]:
  fmp_stage_lowered infos ctx runner fn fn' /\
  (!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) ==>
    fn_is_context_entry ctx fn ==> entry_fn_no_params fn) /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ revert_forward_pair bb p j ==>
  let plan = fmp_stage_plan infos ctx fn;
      root = fmp_stage_root infos ctx fn;
      q = fmp_stage_tidx plan root lbl bb.bb_instructions p
  in
  ?bb'. lookup_block lbl fn'.fn_blocks = SOME bb' /\
    !h. h <= j-p ==>
      (lbl,p+h) NOTIN FDOM plan /\
      fmp_stage_tidx plan root lbl bb.bb_instructions (p+h) = q+h /\
      get_instruction bb' (q+h) = get_instruction bb (p+h)
Proof
  strip_tac >> simp[] >>
  `!h. h <= j-p ==>
    fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
       lbl bb.bb_instructions (p+h) =
    fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
       lbl bb.bb_instructions p+h` by metis_tac[fmp_cover_interval_tidx] >>
  `p <= j` by metis_tac[revert_forward_pair_def, arithmeticTheory.LESS_IMP_LESS_OR_EQ] >>
  `p <= p` by simp[] >> drule_all fmp_cover_interval_fetch >> strip_tac >>
  qexists_tac `bb'` >> simp[Once arithmeticTheory.ADD_COMM] >>
  gen_tac >> disch_tac >>
  `p <= p+h /\ p+h <= j` by decide_tac >> conj_tac
  >- (irule fmp_cover_interval_point >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
  `?b. lookup_block lbl fn'.fn_blocks = SOME b /\
    get_instruction b
      (fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
        lbl bb.bb_instructions (p+h)) = SOME (EL (p+h) bb.bb_instructions)` by
    (irule fmp_cover_interval_fetch >> metis_tac[]) >>
  `b = bb'` by metis_tac[optionTheory.SOME_11] >>
  `p+h < LENGTH bb.bb_instructions` by metis_tac[fmp_cover_interval_opcode] >>
  gvs[get_instruction_def]
QED

Theorem cut_forward_middle_slice[local]:
  p < j /\ get_instruction bb j = SOME last /\
  (!h. h <= j-p ==> get_instruction bb' (q+h) = get_instruction bb (p+h)) ==>
  TAKE (q+(j-p)-SUC q) (DROP (SUC q) bb'.bb_instructions) =
  TAKE (j-SUC p) (DROP (SUC p) bb.bb_instructions)
Proof
  strip_tac >>
  `j < LENGTH bb.bb_instructions` by gvs[get_instruction_def, AllCaseEqs()] >>
  `get_instruction bb' (q+(j-p)) = SOME last` by
    (first_x_assum (qspec_then `j-p` mp_tac) >> simp[]) >>
  `q+(j-p) < LENGTH bb'.bb_instructions` by
    gvs[get_instruction_def, AllCaseEqs()] >>
  irule LIST_EQ >> simp[LENGTH_TAKE, LENGTH_DROP] >>
  rpt strip_tac >>
  `x < j-SUC p /\ SUC x <= j-p /\
   x + SUC p < LENGTH bb.bb_instructions /\
   x + SUC q < LENGTH bb'.bb_instructions` by decide_tac >>
  simp[EL_TAKE, EL_DROP] >>
  first_x_assum (qspec_then `SUC x` mp_tac) >>
  simp[get_instruction_def, arithmeticTheory.ADD_CLAUSES, arithmeticTheory.ADD_COMM]
QED

Theorem cut_forward_operand_var[local]:
  lookup_block lbl fn.fn_blocks = SOME bb /\ MEM i bb.bb_instructions /\
  MEM (Var v) i.inst_operands ==> MEM v (fn_ir_vars fn)
Proof
  strip_tac >> simp[fn_ir_vars_member] >>
  qexistsl_tac [`bb`,`i`] >> simp[inst_uses_def, MEM_operand_vars_eq_Var] >>
  metis_tac[venomExecProofsTheory.lookup_block_MEM]
QED

Theorem cut_forward_resolved_var[local]:
  lookup_block lbl fn.fn_blocks = SOME bb /\
  (!v. op = Var v ==> MEM v (fn_ir_vars fn)) /\
  resolve_block_assigns (REVERSE (TAKE n (DROP i bb.bb_instructions))) op = Var v ==>
  MEM v (fn_ir_vars fn)
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`REVERSE (TAKE n (DROP i bb.bb_instructions))`,
                   `op`, `set (fn_ir_vars fn)`] resolve_block_assigns_tracked) >>
  simp[] >> disch_then irule >> rpt strip_tac >>
  irule cut_forward_operand_var >> qexistsl_tac [`bb`,`q`,`lbl`] >> simp[] >>
  metis_tac[MEM_TAKE, MEM_DROP_IMP]
QED

(* The unchanged middle slice resolves to source operands; the actual pass
   equation and its covered supply transport the three pre-copy comparisons. *)
Theorem cut_forward_pair[local]:
  fmp_lower_function actual sp fn = SOME (fn',sp') /\
  ir_supply_covers_fn sp fn /\ pre_fmp_ops fn /\ fn.fn_fmp_signature = NONE /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  lookup_block lbl fn'.fn_blocks = SOME bb' /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb'.bb_instructions) /\
  revert_forward_pair bb p j /\
  (!h. h <= j-p ==> get_instruction bb' (q+h) = get_instruction bb (p+h)) ==>
  revert_forward_pair bb' q (q+(j-p))
Proof
  strip_tac >>
  qpat_x_assum `revert_forward_pair bb p j` mp_tac >>
  rewrite_tac[revert_forward_pair_def] >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `icopy` (qx_choose_then `irevert`
      (qx_choose_then `dst` (qx_choose_then `src`
        (qx_choose_then `rds` (qx_choose_then `rdst`
          (qx_choose_then `rsize` strip_assume_tac))))))))) >>
  `get_instruction bb' q = SOME icopy /\
   get_instruction bb' (q+(j-p)) = SOME irevert` by
    (conj_tac >- (qpat_assum `!h. h <= j-p ==> get_instruction bb' _ = get_instruction bb _`
       (qspec_then `0` (mp_tac o REWRITE_RULE
         [arithmeticTheory.ADD_0, arithmeticTheory.ZERO_LESS_EQ])) >> metis_tac[]) >>
     qpat_assum `!h. h <= j-p ==> _` (qspec_then `j-p` mp_tac) >> simp[]) >>
  `TAKE (q+(j-p)-SUC q) (DROP (SUC q) bb'.bb_instructions) =
   TAKE (j-SUC p) (DROP (SUC p) bb.bb_instructions)` by
    (irule cut_forward_middle_slice >> metis_tac[]) >>
  `MEM icopy bb.bb_instructions /\ MEM irevert bb.bb_instructions` by
    (simp[MEM_EL] >> gvs[get_instruction_def, AllCaseEqs()] >>
     conj_tac >- (qexists `p` >> decide_tac) >> qexists `j` >> simp[]) >>
  `!arg v. MEM arg [dst;src;rds;rdst;rsize] /\ arg = Var v ==>
    MEM v (fn_ir_vars fn)` by
    (rpt strip_tac >> fs[] >> metis_tac[cut_forward_operand_var, MEM]) >>
  `!a b. (!v. a = Var v ==> MEM v (fn_ir_vars fn)) /\
         (!v. b = Var v ==> MEM v (fn_ir_vars fn)) /\
         same_after_assigns (REVERSE (TAKE p bb.bb_instructions)) a b ==>
         same_after_assigns (REVERSE (TAKE q bb'.bb_instructions)) a b` by
    (rpt strip_tac >> drule_all fmp_prefix_function_same_after >> simp[]) >>
  rewrite_tac[revert_forward_pair_def] >>
  `q < q+(j-p)` by decide_tac >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      `p < p+(k-q) /\ p+(k-q) < j /\ k-q <= j-p /\ q+(k-q) = k` by decide_tac >>
      `get_instruction bb (p+(k-q)) = SOME inst` by metis_tac[] >> metis_tac[]) >>
  conj_tac >>
  qpat_assum `!a b. _ ==> same_after_assigns (REVERSE (TAKE q bb'.bb_instructions)) a b` irule >>
  simp[] >> metis_tac[cut_forward_resolved_var, MEM]
QED

Theorem focus_fmp_cut_forward_layout:
  ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
    (o1_walk_view rpolicy 3) C C' /\
  o1_ctx_shape C /\ o1_ctx_shape C' /\ o1_fn_row 3 fn /\
  lookup_function name C.ctx_functions = SOME fn /\
  lookup_function name C'.ctx_functions = SOME fn' /\
  fn.fn_fmp_signature = NONE /\ fmp_stage_lowered infos ctx runner fn fn' /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ revert_forward_pair bb p j ==>
  let plan = fmp_stage_plan infos ctx fn;
      root = fmp_stage_root infos ctx fn;
      q = fmp_stage_tidx plan root lbl bb.bb_instructions p
  in
  ?bb'. lookup_block lbl fn'.fn_blocks = SOME bb' /\
    revert_forward_pair bb' q (q+(j-p)) /\
    !h. h <= j-p ==>
      (lbl,p+h) NOTIN FDOM plan /\
      fmp_stage_tidx plan root lbl bb.bb_instructions (p+h) = q+h /\
      get_instruction bb' (q+h) = get_instruction bb (p+h)
Proof
  strip_tac >> simp[] >>
  `pre_fmp_ops fn` by fs[o1_fn_row_def] >>
  `o1_fn_shape C fn /\ o1_fn_shape C' fn'` by
    (fs[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[venomInstTheory.lookup_function_MEM]) >>
  `!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) ==>
    fn_is_context_entry ctx fn ==> entry_fn_no_params fn` by
    (rpt gen_tac >> disch_tac >> drule_all focus_fmp_selected_root_pin >> strip_tac >>
     `fn.fn_name = name` by metis_tac[lookup_function_selected_name] >>
     `fn'' = fn'` by metis_tac[optionTheory.SOME_11] >>
     fs[o1_fn_shape_def] >> metis_tac[]) >>
  drule_all cut_forward_fetches >> simp[] >> strip_tac >>
  qexists_tac `bb'` >> simp[] >>
  drule_all ctx_pass_stage_lookup >> strip_tac >>
  drule fmp_fn_pass_step_result >> strip_tac >>
  `ir_supply_covers_fn s fn` by
    (irule ir_supply_covers_unit_member >> qexists `observed` >>
     gvs[fn_pass_step_def] >> metis_tac[lookup_unique_function_member]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb'.bb_instructions)` by
    (irule all_distinct_flat_map_member >>
     qexists `MAP (\b. b.bb_instructions) fn'.fn_blocks` >>
     simp[MAP_MAP_o, combinTheory.o_DEF] >>
     fs[o1_fn_shape_def, wf_function_def, fn_inst_ids_distinct_def, MEM_MAP] >>
     metis_tac[venomExecProofsTheory.lookup_block_MEM]) >>
  `fmp_lower_function observed.cu_context s fn = SOME (fn',out.fpo_supply)` by
    metis_tac[optionTheory.SOME_11] >>
  irule cut_forward_pair >> simp[] >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  simp[] >> metis_tac[arithmeticTheory.ADD_COMM]
QED
