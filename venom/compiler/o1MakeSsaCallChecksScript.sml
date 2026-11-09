Theory o1MakeSsaCallChecks
Ancestors
  o1MakeSsaCallOwnership o1MakeSsaCallPaths o1MakeSsaFlags unitShapeDefs
  makeSsaDefs list pred_set

Theorem current_flag_fails_operands:
  current_flag_alias rs vs ws /\ LENGTH bbs = LENGTH bbs' /\
  (!n l. revert_path bbs n l ==> revert_path bbs' n l) /\
  flag_fails bbs vs inst ==>
  flag_fails bbs' ws
    (inst with inst_operands := rename_current_operands rs inst.inst_operands)
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >>
  gvs[flag_fails_def] >>
  Cases_on `inst.inst_operands` >> gvs[rename_current_operands_def] >>
  Cases_on `h` >> gvs[rename_current_operands_def] >>
  Cases_on `t` >> gvs[rename_current_operands_def, current_flag_alias_def] >>
  Cases_on `h` >> gvs[rename_current_operands_def] >>
  Cases_on `t'` >> gvs[rename_current_operands_def] >>
  Cases_on `h` >> gvs[rename_current_operands_def] >>
  Cases_on `t` >> gvs[rename_current_operands_def]
QED

Theorem mssa_flag_path_cons[local]:
  flag_path bbs vs (i::rest) <=>
  i.inst_opcode <> INVOKE /\
  (flag_fails bbs vs i \/
   flag_path bbs
    (if write_effects i.inst_opcode <> empty_effects then []
     else if i.inst_opcode = ASSIGN /\
             (?u. i.inst_operands = [Var u] /\ MEM u vs)
          then i.inst_outputs ++ vs
          else FILTER (\x. ~MEM x i.inst_outputs) vs) rest)
Proof
  Cases_on `i.inst_opcode` >> simp[flag_path_def] >>
  Cases_on `i.inst_operands` >> simp[] >>
  Cases_on `h` >> simp[] >> Cases_on `t` >> simp[]
QED

Theorem current_flag_path_block_insts:
  !insts s rs rs' s' insts' V H vs ws bbs bbs'.
  rename_current_block_insts s rs insts = (rs',s',insts') /\
  current_rename_owner V H s rs /\ set vs SUBSET V /\
  current_flag_alias rs vs ws /\
  EVERY (\i. set i.inst_outputs SUBSET V) insts /\
  EVERY (\i. i.inst_opcode <> PHI) insts /\
  LENGTH bbs = LENGTH bbs' /\
  (!n l. revert_path bbs n l ==> revert_path bbs' n l) /\
  flag_path bbs vs insts ==>
  flag_path bbs' ws insts'
Proof
  Induct >- simp[flag_path_def] >>
  rpt gen_tac >> simp[rename_current_block_insts_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule_all current_rename_owner_inst >> strip_tac >>
  qpat_x_assum `rename_current_inst _ _ _ = _` mp_tac >>
  simp[rename_current_inst_def] >>
  pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  qpat_x_assum `flag_path _ _ (_::_)` mp_tac >>
  rewrite_tac[mssa_flag_path_cons] >> simp[] >> strip_tac >> simp[]
  >- (disj1_tac >>
      drule_all current_flag_fails_operands >>
      simp[flag_fails_def]) >>
  disj2_tac >>
  qmatch_asmsub_abbrev_tac `flag_path bbs av insts` >>
  qmatch_goalsub_abbrev_tac `flag_path bbs' aw rest'` >>
  `set av SUBSET V` by
    (simp[Abbr `av`] >> rpt IF_CASES_TAC >>
     gvs[SUBSET_DEF, MEM_FILTER, MEM_APPEND] >> metis_tac[]) >>
  `current_flag_alias rs'' av aw` by
    (Cases_on `write_effects h.inst_opcode <> empty_effects` >>
     gvs[Abbr `av`, Abbr `aw`] >>
     Cases_on `h.inst_opcode = ASSIGN` >> gvs[]
     >- (Cases_on `h.inst_operands` >> gvs[rename_current_operands_def]
         >- metis_tac[current_flag_alias_outputs_kill] >>
         Cases_on `h'` >> gvs[rename_current_operands_def]
         >- metis_tac[current_flag_alias_outputs_kill]
         >- (Cases_on `t` >> gvs[rename_current_operands_def]
             >- (rename1 `MEM u vs` >>
                 Cases_on `MEM u vs` >> gvs[]
                 >- (`MEM (latest_current_name rs u) ws` by
                       metis_tac[current_flag_alias_def] >>
                     simp[] >> metis_tac[current_flag_alias_outputs_copy]) >>
                 Cases_on `MEM (latest_current_name rs u) ws` >> gvs[]
                 >- (drule_all current_flag_alias_outputs_copy >>
                     simp[current_flag_alias_def, MEM_FILTER, MEM_APPEND] >>
                     metis_tac[current_flag_alias_def]) >>
                 metis_tac[current_flag_alias_outputs_kill]) >>
             Cases_on `h'` >> gvs[rename_current_operands_def] >>
             drule_all current_flag_alias_outputs_kill >> simp[]) >>
         metis_tac[current_flag_alias_outputs_kill]) >>
     metis_tac[current_flag_alias_outputs_kill]) >>
  metis_tac[]
QED

Theorem current_calls_flagged_block_insts:
  !insts s rs rs' s' insts' V H bbs bbs'.
  rename_current_block_insts s rs insts = (rs',s',insts') /\
  current_rename_owner V H s rs /\
  EVERY (\i. set i.inst_outputs SUBSET V) insts /\
  EVERY (\i. i.inst_opcode <> PHI) insts /\
  LENGTH bbs = LENGTH bbs' /\
  (!n l. revert_path bbs n l ==> revert_path bbs' n l) /\
  calls_flagged bbs insts ==>
  calls_flagged bbs' insts'
Proof
  Induct >- simp[rename_current_block_insts_def, calls_flagged_def] >>
  rpt gen_tac >> simp[rename_current_block_insts_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule_all current_rename_owner_inst >> strip_tac >>
  qpat_x_assum `calls_flagged _ (_::_)` mp_tac >>
  rewrite_tac[calls_flagged_def] >> strip_tac >>
  gvs[] >> rewrite_tac[calls_flagged_def] >> conj_tac
  >- (qpat_x_assum `rename_current_inst _ _ _ = _` mp_tac >>
      simp[rename_current_inst_def] >>
      pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
      strip_tac >>
      Cases_on `h.inst_outputs` >> gvs[] >>
      Cases_on `t` >> gvs[] >>
      qpat_x_assum `rename_current_outputs _ _ _ = _` mp_tac >>
      simp[rename_current_outputs_def] >>
      pairarg_tac >> gvs[rename_current_outputs_def] >> strip_tac >> gvs[] >>
      drule current_flag_alias_call >> strip_tac >>
      `set [h'] SUBSET V` by simp[] >>
      drule_all current_flag_path_block_insts >> simp[]) >>
  metis_tac[]
QED
