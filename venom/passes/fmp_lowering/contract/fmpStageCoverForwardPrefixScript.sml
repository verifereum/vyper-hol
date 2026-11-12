(* Backward ASSIGN comparisons through FMP lowering prefixes. *)
Theory fmpStageCoverForwardPrefix
Ancestors
  fmpStageRel fmpStepBridge fmpStepLayout fmpStepRewrite
  fmpLowerDefs fmpLowerProps fmpLowerSequenceExec lowerDloadPtrForward contextCodegenRel
  simplifyCfgFrameRf fmpStageControlLayout fmpStepOpaque callLayoutDefs
  irSupply venomFnScheduleRunner o1PassContract venomInst list rich_list pred_set

Theorem fmp_prefix_chunk_outputs[local]:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') /\
  MEM v s.irs_used_vars /\ v <> runner /\ pre_fmp_opcode inst.inst_opcode ==>
  ((?i. MEM i out /\ MEM v i.inst_outputs) <=> MEM v inst.inst_outputs)
Proof
  Cases_on `inst.inst_opcode = DALLOCA`
  >- (rpt strip_tac >>
      gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def, AllCaseEqs()] >>
      rpt (drule (cj 1 fresh_ir_var_contract) >> strip_tac >>
           dxrule (cj 2 fresh_ir_var_contract) >> strip_tac) >>
      gvs[mk_inst_def, LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR,
          EXISTS_OR_THM] >> metis_tac[]) >>
  rpt strip_tac >>
  gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def, AllCaseEqs(),
      pre_fmp_opcode_def, is_raw_fmp_opcode_def] >>
  Cases_on `info.fi_publishes_fmp` >> gvs[MEM_APPEND]
QED

Theorem fmp_prefix_chunk_same_after[local]:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') /\
  pre_fmp_opcode inst.inst_opcode /\
  (!v. v IN V ==> MEM v s.irs_used_vars /\ v <> runner) /\
  (!v. a = Var v ==> v IN V) /\ (!v. b = Var v ==> v IN V) ==>
  same_after_assigns (REVERSE out ++ tail) a b =
  same_after_assigns (inst::tail) a b
Proof
  rpt strip_tac >> Cases_on `inst.inst_opcode = ASSIGN`
  >- gvs[fmp_lower_inst_def, is_raw_fmp_opcode_def] >>
  irule same_after_nonassign_chunk_replace >> simp[] >>
  reverse conj_tac
  >- (gvs[fmp_lower_inst_def, AllCaseEqs(), pre_fmp_opcode_def,
          is_raw_fmp_opcode_def, mk_inst_def]) >>
  qexists `V` >> simp[] >>
  simp[EXTENSION] >> rpt strip_tac >>
  Cases_on `x IN V` >> simp[] >>
  `MEM x s.irs_used_vars /\ x <> runner` by metis_tac[] >>
  drule_all fmp_prefix_chunk_outputs >> simp[] >>
  simp[MEM_MAP] >> metis_tac[]
QED

Theorem fmp_prefix_back_closed[local]:
  step_back_assign inst a = SOME b /\
  (!v. a = Var v ==> v IN V) /\
  (!v. MEM (Var v) inst.inst_operands ==> v IN V) ==>
  !v. b = Var v ==> v IN V
Proof
  Cases_on `a` >>
  gvs[step_back_assign_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  `MEM (HD inst.inst_operands) inst.inst_operands` by
    (Cases_on `inst.inst_operands` >> gvs[]) >> metis_tac[]
QED

Theorem fmp_prefix_tail_cong[local]:
  !xs a b. (!i v. MEM i xs /\ MEM (Var v) i.inst_operands ==> v IN V) /\
  (!a b. (!v. a = Var v ==> v IN V) /\ (!v. b = Var v ==> v IN V) ==>
    same_after_assigns left a b = same_after_assigns right a b) /\
  (!v. a = Var v ==> v IN V) /\ (!v. b = Var v ==> v IN V) ==>
  same_after_assigns (xs ++ left) a b = same_after_assigns (xs ++ right) a b
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  simp[same_after_assigns_def] >> Cases_on `a = b` >> simp[] >>
  Cases_on `step_back_assign h a` >> Cases_on `step_back_assign h b` >>
  simp[] >> first_x_assum irule >> simp[] >>
  metis_tac[fmp_prefix_back_closed]
QED

Theorem fmp_prefix_restores_same_after[local]:
  fmp_emit_restores runner s bases = (out,s') /\
  (!v. a = Var v ==> v <> runner) /\
  (!v. b = Var v ==> v <> runner) ==>
  same_after_assigns (REVERSE out ++ tail) a b = same_after_assigns tail a b
Proof
  map_every qid_spec_tac [`tail`, `s'`, `out`, `s`] >> Induct_on `bases`
  >- simp[fmp_emit_restores_def] >>
  simp[fmp_emit_restores_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  first_x_assum drule >> disch_then (qspec_then
    `mk_inst id ASSIGN [Var h] [runner]::tail` mp_tac) >>
  simp[] >> strip_tac >> simp[] >>
  Cases_on `a = b`
  >- (Cases_on `tail` >> simp[same_after_assigns_def]) >>
  Cases_on `a` >> Cases_on `b` >>
  gvs[same_after_assigns_def, step_back_assign_def, mk_inst_def]
QED

Theorem fmp_prefix_inst_vars_mono[local]:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') ==>
  !v. MEM v s.irs_used_vars ==> MEM v s'.irs_used_vars
Proof
  Cases_on `inst.inst_opcode = DALLOCA`
  >- (rpt strip_tac >>
      gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def, AllCaseEqs()] >>
      rpt (dxrule (cj 2 fresh_ir_var_contract) >> strip_tac) >>
      gvs[fresh_inst_id_def]) >>
  rpt strip_tac >> gvs[fmp_lower_inst_def, AllCaseEqs()]
QED

Theorem fmp_prefix_restores_vars[local]:
  fmp_emit_restores runner s bases = (out,s') ==>
  s'.irs_used_vars = s.irs_used_vars
Proof
  map_every qid_spec_tac [`s'`, `out`, `s`] >> Induct_on `bases` >>
  simp[fmp_emit_restores_def, AllCaseEqs(), fresh_inst_id_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem fmp_prefix_indexed_vars_mono[local]:
  !xs k s restores out leftover s'.
  fmp_lower_indexed infos ctx runner label k s restores xs = SOME (out,leftover,s') ==>
  !v. MEM v s.irs_used_vars ==> MEM v s'.irs_used_vars
Proof
  Induct >- simp[fmp_lower_indexed_def] >>
  simp[fmpLowerIndexedPropsTheory.fmp_lower_indexed_cons] >>
  rpt strip_tac >> gvs[] >>
  drule fmp_prefix_restores_vars >> strip_tac >>
  drule fmp_prefix_inst_vars_mono >> strip_tac >>
  first_x_assum drule >> metis_tac[]
QED

Theorem fmp_prefix_indexed_same_after[local]:
  !xs k s restores out leftover s' tail a b.
  fmp_lower_indexed infos ctx runner label k s restores xs = SOME (out,leftover,s') /\
  EVERY (\i. pre_fmp_opcode i.inst_opcode) xs /\
  (!i v. MEM i xs /\ MEM (Var v) i.inst_operands ==> v IN V) /\
  (!v. v IN V ==> MEM v s.irs_used_vars /\ v <> runner) /\
  (!v. a = Var v ==> v IN V) /\ (!v. b = Var v ==> v IN V) ==>
  same_after_assigns (REVERSE out ++ tail) a b =
  same_after_assigns (REVERSE xs ++ tail) a b
Proof
  Induct using SNOC_INDUCT
  >- simp[fmp_lower_indexed_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[SNOC_APPEND] >>
  drule fmp_lower_indexed_append >> strip_tac >>
  gvs[fmpLowerIndexedPropsTheory.fmp_lower_indexed_cons,
      fmp_lower_indexed_def] >>
  `!v. v IN V ==> MEM v sp1.irs_used_vars /\ v <> runner` by
    (drule fmp_prefix_indexed_vars_mono >> metis_tac[]) >>
  `!v. v IN V ==> MEM v s0.irs_used_vars /\ v <> runner` by
    (drule fmp_prefix_restores_vars >> metis_tac[]) >>
  simp[REVERSE_APPEND, APPEND_ASSOC] >>
  `same_after_assigns (REVERSE head ++ (REVERSE prefix ++ REVERSE c1 ++ tail)) a b =
   same_after_assigns (x::(REVERSE prefix ++ REVERSE c1 ++ tail)) a b` by
    (irule fmp_prefix_chunk_same_after >> simp[] >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  fs[APPEND_ASSOC] >>
  irule (fmp_prefix_tail_cong |> Q.SPEC `[x]` |> SRULE [APPEND]) >>
  qexists `V` >> simp[] >>
  map_every qx_gen_tac [`a'`, `b'`] >> strip_tac >>
  `same_after_assigns (REVERSE prefix ++ (REVERSE c1 ++ tail)) a' b' =
   same_after_assigns (REVERSE c1 ++ tail) a' b'` by
    (irule fmp_prefix_restores_same_after >> metis_tac[]) >>
  fs[APPEND_ASSOC] >> first_x_assum irule >> metis_tac[]
QED

Theorem fmp_prefix_indexed_endpoint[local]:
  fmp_lower_indexed infos ctx runner label k s rs xs = SOME (code,left,s') /\
  EVERY (\i. pre_fmp_opcode i.inst_opcode) xs /\
  (!i v. MEM i xs /\ MEM (Var v) i.inst_operands ==> v IN V) /\
  (!v. v IN V ==> MEM v s.irs_used_vars /\ v <> runner) /\
  p < LENGTH xs /\ (EL p xs).inst_opcode = RETURNDATACOPY /\
  (!v. a = Var v ==> v IN V) /\ (!v. b = Var v ==> v IN V) ==>
  ?q. q < LENGTH code /\ EL q code = EL p xs /\
    same_after_assigns (REVERSE (TAKE q code)) a b =
    same_after_assigns (REVERSE (TAKE p xs)) a b
Proof
  rpt strip_tac >>
  `xs = TAKE p xs ++ DROP p xs` by simp[] >>
  mp_tac (fmp_lower_indexed_append |> Q.SPEC `TAKE p xs`
    |> Q.SPECL [`k`, `s`, `rs`, `DROP p xs`]) >>
  simp[] >> strip_tac >>
  `DROP p xs = EL p xs :: DROP (SUC p) xs` by
    metis_tac[DROP_CONS_EL] >>
  gvs[fmpLowerIndexedPropsTheory.fmp_lower_indexed_cons,
      fmp_lower_inst_def, is_raw_fmp_opcode_def] >>
  qexists `LENGTH c1 + LENGTH prefix` >>
  simp[EL_APPEND, TAKE_APPEND, TAKE_LENGTH_TOO_LONG, REVERSE_APPEND,
       arithmeticTheory.ADD_SUB] >>
  `!v. v IN V ==> MEM v sp1.irs_used_vars /\ v <> runner` by
    (qpat_assum `fmp_lower_indexed _ _ _ _ _ _ _ (TAKE p xs) = _`
       (mp_then Any mp_tac fmp_prefix_indexed_vars_mono) >> metis_tac[]) >>
  `same_after_assigns (REVERSE prefix ++ REVERSE c1) a b =
   same_after_assigns (REVERSE c1) a b` by
    (irule fmp_prefix_restores_same_after >> metis_tac[]) >>
  `LENGTH c1 + LENGTH prefix - (LENGTH c1 + (LENGTH prefix + 1)) = 0` by decide_tac >>
  simp[] >> irule (fmp_prefix_indexed_same_after |> Q.SPEC `TAKE p xs`
    |> Q.SPECL [`k`, `s`, `rs`, `c1`, `l1`, `sp1`, `[]`, `a`, `b`]
    |> SRULE [APPEND_NIL]) >> simp[] >>
  metis_tac[MEM_TAKE, EVERY_TAKE]
QED

Theorem fmp_prefix_blocks_vars[local]:
  !bbs s rs out left s'.
  fmp_lower_blocks infos ctx runner s rs bbs = SOME (FmpBlocksResult out left s') ==>
  !v. MEM v s.irs_used_vars ==> MEM v s'.irs_used_vars
Proof
  Induct >> simp[fmp_lower_blocks_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule fmp_prefix_indexed_vars_mono >> strip_tac >>
  first_x_assum drule >> metis_tac[]
QED

Theorem fmp_prefix_blocks_walk[local]:
  !bbs s rs out left s' lbl bb.
  fmp_lower_blocks infos ctx runner s rs bbs = SOME (FmpBlocksResult out left s') /\
  lookup_block lbl bbs = SOME bb ==>
  ?code s0 rs0 l0 s1.
    lookup_block lbl out = SOME (bb with bb_instructions := code) /\
    fmp_lower_indexed infos ctx runner lbl 0 s0 rs0 bb.bb_instructions =
      SOME (code,l0,s1) /\
    (!v. MEM v s.irs_used_vars ==> MEM v s0.irs_used_vars)
Proof
  Induct >> simp[fmp_lower_blocks_def, lookup_block_def, FIND_thm,
                 AllCaseEqs()] >> rpt strip_tac >> gvs[]
  >- (qexistsl [`insts`, `s`, `rs`, `later`, `s2`] >> simp[FIND_thm]) >>
  first_x_assum drule >>
  disch_then (qspecl_then [`lbl`, `bb`] mp_tac) >>
  simp[lookup_block_def] >> strip_tac >>
  qexistsl [`code`, `s0`, `rs0`, `l0`, `s1`] >> simp[FIND_thm] >>
  metis_tac[fmp_prefix_indexed_vars_mono]
QED

Theorem fmp_prefix_header_replace[local]:
  EVERY (\i. i.inst_opcode <> ASSIGN) header /\
  LENGTH header <= p /\ p < LENGTH (header ++ suffix) /\
  same_after_assigns (REVERSE (TAKE p (header ++ suffix))) a b ==>
  same_after_assigns
    (REVERSE (TAKE (LENGTH newheader + (p - LENGTH header)) (newheader ++ suffix))) a b
Proof
  strip_tac >>
  simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG, REVERSE_APPEND] >>
  gvs[TAKE_APPEND, TAKE_LENGTH_TOO_LONG, REVERSE_APPEND] >>
  irule scfg_same_after_assigns_replace >>
  goal_assum (drule_at Any) >> simp[EVERY_REVERSE]
QED

Theorem fmp_prefix_unique_position[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) xs) /\
  p < LENGTH xs /\ q < LENGTH xs /\ EL p xs = EL q xs ==> p = q
Proof
  strip_tac >>
  drule ALL_DISTINCT_EL_IMP >> simp[] >>
  disch_then (qspecl_then [`p`, `q`] mp_tac) >> simp[EL_MAP]
QED

Theorem fmp_prefix_install_endpoint[local]:
  entry.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ suffix /\
  EVERY (\i. MEM i.inst_opcode [PARAM; RETPC_PARAM; FMP_PARAM])
    (users ++ OPTION_TO_LIST oldpc) /\
  (newpc = NONE <=> oldpc = NONE) /\
  fmp_install_root ctx fn (FmpRootLayout (LENGTH users) root newpc s) (entry::rest) =
    SOME (out,s') /\
  lookup_block lbl (entry::rest) = SOME bb /\
  q < LENGTH bb.bb_instructions /\ (EL q bb.bb_instructions).inst_opcode = RETURNDATACOPY /\
  same_after_assigns (REVERSE (TAKE q bb.bb_instructions)) a b ==>
  ?bb' q'. lookup_block lbl out = SOME bb' /\ q' < LENGTH bb'.bb_instructions /\
    EL q' bb'.bb_instructions = EL q bb.bb_instructions /\
    same_after_assigns (REVERSE (TAKE q' bb'.bb_instructions)) a b
Proof
  rpt strip_tac >> Cases_on `lbl = entry.bb_label`
  >- (gvs[lookup_block_def, FIND_thm] >>
      `LENGTH (users ++ OPTION_TO_LIST oldpc) <= q` by
        (spose_not_then assume_tac >>
         `q < LENGTH (users ++ OPTION_TO_LIST oldpc)` by (fs[] >> decide_tac) >>
         `MEM (EL q bb.bb_instructions) (users ++ OPTION_TO_LIST oldpc)` by
           (qpat_x_assum `bb.bb_instructions = _` SUBST1_TAC >>
            pure_rewrite_tac[APPEND_ASSOC] >>
            asm_simp_tac bool_ss [EL_APPEND1] >> metis_tac[EL_MEM]) >>
         fs[EVERY_MEM] >> res_tac >> gvs[]) >>
      drule_all fmp_install_root_exact_prefix >> strip_tac >>
      gvs[] >>
      qmatch_goalsub_abbrev_tac `FIND pred (newentry::rest)` >>
      qexistsl [`newentry`,
        `LENGTH newentry.bb_instructions - LENGTH suffix + (q - LENGTH (users ++ OPTION_TO_LIST oldpc))`] >>
      simp[Abbr `newentry`, Abbr `pred`, lookup_block_def, FIND_thm] >>
      Cases_on `fn_is_context_entry ctx fn` >>
      gvs[EL_APPEND, APPEND_ASSOC, TAKE_APPEND, TAKE_LENGTH_TOO_LONG,
          REVERSE_APPEND] >>
      pure_rewrite_tac[GSYM APPEND_ASSOC] >>
      irule scfg_same_after_assigns_replace >>
      qexists `REVERSE (OPTION_TO_LIST oldpc) ++ REVERSE users` >>
      (conj_tac >- (fs[EVERY_REVERSE, EVERY_MEM] >> rpt strip_tac >> res_tac >> gvs[])) >>
      pure_rewrite_tac[APPEND_ASSOC] >> first_assum ACCEPT_TAC) >>
  drule_all fmp_control_install_other >> strip_tac >>
  qexistsl [`bb`, `q`] >> simp[]
QED

Theorem fmp_prefix_function_same_after:
  fmp_lower_function ctx sp fn = SOME (fn',sp') /\
  ir_supply_covers_fn sp fn /\ pre_fmp_ops fn /\ fn.fn_fmp_signature = NONE /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  lookup_block lbl fn'.fn_blocks = SOME bb' /\
  get_instruction bb p = SOME inst /\ inst.inst_opcode = RETURNDATACOPY /\
  get_instruction bb' tp = SOME inst /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb'.bb_instructions) /\
  (!v. a = Var v ==> MEM v (fn_ir_vars fn)) /\
  (!v. b = Var v ==> MEM v (fn_ir_vars fn)) /\
  same_after_assigns (REVERSE (TAKE p bb.bb_instructions)) a b ==>
  same_after_assigns (REVERSE (TAKE tp bb'.bb_instructions)) a b
Proof
  rpt strip_tac >>
  gvs[fmp_lower_function_def, fmp_lower_function_with_info_def,
      fmp_checked_seal_def, fmp_seal_def, AllCaseEqs()]
  >- (gvs[get_instruction_def, AllCaseEqs()] >>
      `p = tp` by (irule fmp_prefix_unique_position >> metis_tac[]) >>
      qpat_x_assum `p = tp` (SUBST_ALL_TAC) >> first_assum ACCEPT_TAC) >>
  Cases_on `root_layout` >> fs[] >>
  rename1 `fmp_make_root_layout ctx fn info runner s1 = SOME (FmpRootLayout n root pc s2)` >>
  `s2.irs_used_vars = s1.irs_used_vars` by metis_tac[fmp_make_root_layout_used_vars] >>
  `?users oldpc suffix. n = LENGTH users /\
      split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix) /\
      (pc = NONE <=> oldpc = NONE)` by
    (fs[fmp_make_root_layout_def, AllCaseEqs()] >>
     Cases_on `info.fi_needs_fmp` >>
     Cases_on `fn_is_context_entry ctx fn` >>
     gvs[AllCaseEqs()]) >>
  pop_assum strip_assume_tac >> gvs[] >>
  drule_all fmp_prefix_blocks_walk >> strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecProofsTheory.lookup_block_MEM] >>
  `EVERY (\i. pre_fmp_opcode i.inst_opcode) bb.bb_instructions` by
    (fs[pre_fmp_ops_def, EVERY_MEM, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  `!i v. MEM i bb.bb_instructions /\ MEM (Var v) i.inst_operands ==>
      v IN set (fn_ir_vars fn)` by
    (rpt strip_tac >> simp[fn_ir_vars_def, MEM_FLAT, MEM_MAP] >>
     qexists `block_ir_vars bb` >> conj_tac
     >- (qexists `bb` >> simp[]) >>
     simp[block_ir_vars_def, MEM_FLAT, MEM_MAP] >>
     qexists `inst_ir_vars i` >> conj_tac
     >- (qexists `i` >> simp[]) >>
     simp[inst_ir_vars_def, inst_uses_def] >>
     simp[MEM_operand_vars_eq_Var]) >>
  `!v. v IN set (fn_ir_vars fn) ==> MEM v s0.irs_used_vars /\ v <> runner` by
    (drule fresh_ir_var_contract >> strip_tac >>
     fs[ir_supply_covers_fn_def, list_subset_def, EVERY_MEM] >> metis_tac[]) >>
  `?q. q < LENGTH code /\ EL q code = EL p bb.bb_instructions /\
      same_after_assigns (REVERSE (TAKE q code)) a b =
      same_after_assigns (REVERSE (TAKE p bb.bb_instructions)) a b` by
    (qpat_assum `fmp_lower_indexed _ _ _ _ _ _ _ _ = _`
       (mp_then Any mp_tac (fmp_prefix_indexed_endpoint |>
         Q.INST [`V` |-> `set (fn_ir_vars fn)`])) >>
     disch_then (qspecl_then [`p`, `fn`, `b`, `a`] mp_tac) >>
     fs[get_instruction_def, AllCaseEqs()] >>
     impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  pop_assum strip_assume_tac >>
  drule_all fmp_lower_blocks_checked_entry_prefix >> strip_tac >>
  drule split_fmp_entry_parameter_prefix >> strip_tac >>
  fs[get_instruction_def, AllCaseEqs()] >>
  `entry.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ tail` by
    (Cases_on `oldpc` >> fs[OPTION_TO_LIST_def]) >>
  `EVERY (\i. MEM i.inst_opcode [PARAM; RETPC_PARAM; FMP_PARAM])
      (users ++ OPTION_TO_LIST oldpc)` by
    (Cases_on `oldpc` >> fs[EVERY_APPEND, OPTION_TO_LIST_def]) >>
  `?endbb endq. lookup_block lbl blocks' = SOME endbb /\
      endq < LENGTH endbb.bb_instructions /\
      EL endq endbb.bb_instructions = EL p bb.bb_instructions /\
      same_after_assigns (REVERSE (TAKE endq endbb.bb_instructions)) a b` by
    (qpat_x_assum `blocks = entry::rest` SUBST_ALL_TAC >>
     `same_after_assigns (REVERSE (TAKE q code)) a b` by metis_tac[] >>
     `q < LENGTH (bb with bb_instructions := code).bb_instructions /\
      (EL q (bb with bb_instructions := code).bb_instructions).inst_opcode = RETURNDATACOPY /\
      same_after_assigns (REVERSE (TAKE q (bb with bb_instructions := code).bb_instructions)) a b` by simp[] >>
     drule_all fmp_prefix_install_endpoint >> simp[] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  `endbb = bb'` by metis_tac[optionTheory.SOME_11] >>
  `endq = tp` by
    (irule fmp_prefix_unique_position >>
     fs[get_instruction_def, AllCaseEqs()] >> metis_tac[]) >>
  metis_tac[]
QED
