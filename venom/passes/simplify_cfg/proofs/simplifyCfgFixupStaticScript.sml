(* Static positional boundaries for PHI fixup. *)
Theory simplifyCfgFixupStatic
Ancestors
  simplifyCfgPhiBlockSemantics simplifyCfgPhiSemantics simplifyCfgLabelProps
  simplifyCfgDefs venomInst venomWf venomExecProofs analysisSimProofsBase cfgTransform list rich_list
  simplifyCfgStruct

Theorem scfg_partition_length[local]:
  !P xs. LENGTH (FILTER P xs) + LENGTH (FILTER (\i. ~P i) xs) = LENGTH xs
Proof
  gen_tac >> Induct >> simp[] >> Cases_on `P h` >> simp[]
QED

Theorem scfg_fix_phis_length:
  bb.bb_instructions = ps ++ tail /\
  EVERY (\i. i.inst_opcode <> PHI) tail ==>
  LENGTH (fix_phis_in_block actual_preds bb).bb_instructions = LENGTH bb.bb_instructions
Proof
  strip_tac >>
  `!xs. LENGTH (FILTER (\i. (fix_phi_inst actual_preds i).inst_opcode = PHI) xs) +
         LENGTH (FILTER (\i. (fix_phi_inst actual_preds i).inst_opcode <> PHI) xs) =
         LENGTH xs` by
    metis_tac[scfg_partition_length] >>
  `(fix_phis_in_block actual_preds bb).bb_instructions =
    MAP (fix_phi_inst actual_preds) (FILTER (\i. (fix_phi_inst actual_preds i).inst_opcode = PHI) ps) ++
    MAP (fix_phi_inst actual_preds) (FILTER (\i. (fix_phi_inst actual_preds i).inst_opcode <> PHI) ps) ++ tail` by
    (irule scfg_fix_phis_partition_instructions >> metis_tac[]) >>
  simp[]
QED

Theorem scfg_fix_phis_tail_el:
  bb.bb_instructions = ps ++ tail /\
  EVERY (\i. i.inst_opcode <> PHI) tail /\ k < LENGTH tail ==>
  EL (LENGTH ps + k) (fix_phis_in_block actual_preds bb).bb_instructions = EL k tail
Proof
  strip_tac >>
  `(fix_phis_in_block actual_preds bb).bb_instructions =
    MAP (fix_phi_inst actual_preds) (FILTER (\i. (fix_phi_inst actual_preds i).inst_opcode = PHI) ps) ++
    MAP (fix_phi_inst actual_preds) (FILTER (\i. (fix_phi_inst actual_preds i).inst_opcode <> PHI) ps) ++ tail` by
    (irule scfg_fix_phis_partition_instructions >> metis_tac[]) >>
  `LENGTH (fix_phis_in_block actual_preds bb).bb_instructions = LENGTH bb.bb_instructions` by
    metis_tac[scfg_fix_phis_length] >>
  `LENGTH (FILTER (\i. (fix_phi_inst actual_preds i).inst_opcode = PHI) ps) +
   LENGTH (FILTER (\i. (fix_phi_inst actual_preds i).inst_opcode <> PHI) ps) = LENGTH ps` by
    (qpat_x_assum `LENGTH (fix_phis_in_block _ _).bb_instructions = _` mp_tac >>
     asm_rewrite_tac[LENGTH_APPEND, LENGTH_MAP] >> decide_tac) >>
  simp[EL_APPEND]
QED

Theorem scfg_fix_prefix_output[local]:
  EVERY (\i. (fix_phi_inst actual_preds i).inst_opcode <> NOP) ps /\
  MEM i ps /\ MEM v i.inst_outputs ==>
  ?j. j < LENGTH ps /\
    MEM v (EL j
      (MAP (fix_phi_inst actual_preds) (FILTER (\i. (fix_phi_inst actual_preds i).inst_opcode = PHI) ps) ++
       MAP (fix_phi_inst actual_preds) (FILTER (\i. (fix_phi_inst actual_preds i).inst_opcode <> PHI) ps))).inst_outputs
Proof
  strip_tac >>
  `(fix_phi_inst actual_preds i).inst_outputs = i.inst_outputs` by
    (irule scfg_fix_phi_outputs >> fs[EVERY_MEM]) >>
  `MEM (fix_phi_inst actual_preds i)
      (MAP (fix_phi_inst actual_preds) (FILTER (\i. (fix_phi_inst actual_preds i).inst_opcode = PHI) ps) ++
       MAP (fix_phi_inst actual_preds) (FILTER (\i. (fix_phi_inst actual_preds i).inst_opcode <> PHI) ps))` by
    (simp[MEM_MAP, MEM_FILTER] >> Cases_on `(fix_phi_inst actual_preds i).inst_opcode = PHI` >>
     metis_tac[]) >>
  pop_assum (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  qexists_tac `n` >>
  qspecl_then [`\i. (fix_phi_inst actual_preds i).inst_opcode = PHI`, `ps`]
    assume_tac scfg_partition_length >>
  conj_tac >- (fs[] >> decide_tac) >> metis_tac[]
QED

Theorem scfg_fix_phis_prefix_output[local]:
  bb.bb_instructions = ps ++ tail /\
  EVERY (\i. i.inst_opcode <> PHI) tail /\
  EVERY (\i. (fix_phi_inst actual_preds i).inst_opcode <> NOP) ps /\
  MEM i ps /\ MEM v i.inst_outputs ==>
  ?j. j < LENGTH ps /\
      MEM v (EL j (fix_phis_in_block actual_preds bb).bb_instructions).inst_outputs
Proof
  strip_tac >> drule_all scfg_fix_prefix_output >> strip_tac >>
  qexists_tac `j` >> conj_tac >- simp[] >>
  `(fix_phis_in_block actual_preds bb).bb_instructions =
    MAP (fix_phi_inst actual_preds) (FILTER (\i. (fix_phi_inst actual_preds i).inst_opcode = PHI) ps) ++
    MAP (fix_phi_inst actual_preds) (FILTER (\i. (fix_phi_inst actual_preds i).inst_opcode <> PHI) ps) ++ tail` by
    (irule scfg_fix_phis_partition_instructions >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `EL j prefix` >>
  `LENGTH prefix = LENGTH ps` by
    (qspecl_then [`\i. (fix_phi_inst actual_preds i).inst_opcode = PHI`, `ps`]
       mp_tac scfg_partition_length >> simp[Abbr `prefix`]) >>
  `(fix_phis_in_block actual_preds bb).bb_instructions = prefix ++ tail` by
    simp[Abbr `prefix`, APPEND_ASSOC] >>
  `EL j (prefix ++ tail) = EL j prefix` by simp[EL_APPEND] >>
  asm_rewrite_tac[]
QED

Theorem scfg_fix_phis_tail_output:
  bb.bb_instructions = ps ++ tail /\
  EVERY (\i. i.inst_opcode <> PHI) tail /\
  EVERY (\i. (fix_phi_inst actual_preds i).inst_opcode <> NOP) ps /\
  k < LENGTH tail /\ i < LENGTH ps + k /\
  MEM v (EL i bb.bb_instructions).inst_outputs ==>
  ?j. j < LENGTH ps + k /\
      MEM v (EL j (fix_phis_in_block actual_preds bb).bb_instructions).inst_outputs
Proof
  strip_tac >> Cases_on `i < LENGTH ps`
  >- (`MEM (EL i ps) ps /\ MEM v (EL i ps).inst_outputs` by
        (gvs[EL_APPEND] >> metis_tac[EL_MEM]) >>
      drule_all scfg_fix_phis_prefix_output >> strip_tac >>
      qexists_tac `j` >> simp[]) >>
  `i - LENGTH ps < LENGTH tail` by decide_tac >>
  `EL i (fix_phis_in_block actual_preds bb).bb_instructions = EL (i - LENGTH ps) tail` by
    (`i = LENGTH ps + (i - LENGTH ps)` by decide_tac >>
     metis_tac[scfg_fix_phis_tail_el]) >>
  qexists_tac `i` >> gvs[EL_APPEND]
QED

Theorem scfg_fix_phis_end_output:
  bb.bb_instructions = ps ++ tail /\
  EVERY (\i. i.inst_opcode <> PHI) tail /\
  EVERY (\i. (fix_phi_inst actual_preds i).inst_opcode <> NOP) ps /\
  i < LENGTH bb.bb_instructions /\ MEM v (EL i bb.bb_instructions).inst_outputs ==>
  ?j. j < LENGTH (fix_phis_in_block actual_preds bb).bb_instructions /\
      MEM v (EL j (fix_phis_in_block actual_preds bb).bb_instructions).inst_outputs
Proof
  strip_tac >>
  `LENGTH (fix_phis_in_block actual_preds bb).bb_instructions = LENGTH ps + LENGTH tail` by
    (drule_all scfg_fix_phis_length >> simp[]) >>
  Cases_on `i < LENGTH ps`
  >- (`MEM (EL i ps) ps /\ MEM v (EL i ps).inst_outputs` by
        (gvs[EL_APPEND] >> metis_tac[EL_MEM]) >>
      drule_all scfg_fix_phis_prefix_output >> strip_tac >>
      qexists_tac `j` >> simp[]) >>
  `i - LENGTH ps < LENGTH tail` by (gvs[] >> decide_tac) >>
  `EL i (fix_phis_in_block actual_preds bb).bb_instructions = EL (i - LENGTH ps) tail` by
    (`i = LENGTH ps + (i - LENGTH ps)` by decide_tac >>
     metis_tac[scfg_fix_phis_tail_el]) >>
  qexists_tac `i` >> gvs[EL_APPEND]
QED

Theorem scfg_fix_phi_prefix_covered_not_nop:
  actual_preds <> [] /\
  EVERY (\i. i.inst_opcode = PHI /\ phi_well_formed i.inst_operands /\
    EVERY (\p. ?op. resolve_phi p i.inst_operands = SOME op) actual_preds) ps ==>
  EVERY (\i. (fix_phi_inst actual_preds i).inst_opcode <> NOP) ps
Proof
  strip_tac >> rewrite_tac[EVERY_MEM] >> gen_tac >> disch_tac >>
  BETA_TAC >> irule scfg_fix_phi_covered_not_nop >> fs[EVERY_MEM]
QED

Theorem scfg_fix_phis_covered_tail_output:
  bb.bb_instructions = ps ++ tail /\
  EVERY (\i. i.inst_opcode <> PHI) tail /\
  actual_preds <> [] /\
  EVERY (\i. i.inst_opcode = PHI /\ phi_well_formed i.inst_operands /\
    EVERY (\p. ?op. resolve_phi p i.inst_operands = SOME op) actual_preds) ps /\
  k < LENGTH tail /\ i < LENGTH ps + k /\
  MEM v (EL i bb.bb_instructions).inst_outputs ==>
  ?j. j < LENGTH ps + k /\
      MEM v (EL j (fix_phis_in_block actual_preds bb).bb_instructions).inst_outputs
Proof
  strip_tac >>
  drule_all scfg_fix_phi_prefix_covered_not_nop >> strip_tac >>
  irule scfg_fix_phis_tail_output >> metis_tac[]
QED

Theorem scfg_fix_phis_covered_end_output:
  bb.bb_instructions = ps ++ tail /\
  EVERY (\i. i.inst_opcode <> PHI) tail /\
  actual_preds <> [] /\
  EVERY (\i. i.inst_opcode = PHI /\ phi_well_formed i.inst_operands /\
    EVERY (\p. ?op. resolve_phi p i.inst_operands = SOME op) actual_preds) ps /\
  i < LENGTH bb.bb_instructions /\ MEM v (EL i bb.bb_instructions).inst_outputs ==>
  ?j. j < LENGTH (fix_phis_in_block actual_preds bb).bb_instructions /\
      MEM v (EL j (fix_phis_in_block actual_preds bb).bb_instructions).inst_outputs
Proof
  strip_tac >>
  drule_all scfg_fix_phi_prefix_covered_not_nop >> strip_tac >>
  irule scfg_fix_phis_end_output >> metis_tac[]
QED

Theorem scfg_fix_all_phis_mem:
  MEM bb' (fix_all_phis fn).fn_blocks <=>
  ?bb. MEM bb fn.fn_blocks /\
       bb' = fix_phis_in_block (pred_labels fn bb.bb_label) bb
Proof
  simp[fix_all_phis_def, MEM_MAP] >> metis_tac[]
QED

Theorem scfg_fix_all_phis_edge:
  wf_function fn ==>
  (fn_cfg_edge (fix_all_phis fn) a b <=> fn_cfg_edge fn a b)
Proof
  strip_tac >> simp[fn_cfg_edge_def, scfg_fix_all_phis_mem] >>
  `!bb. MEM bb fn.fn_blocks ==>
    bb_succs (fix_phis_in_block (pred_labels fn bb.bb_label) bb) = bb_succs bb` by
    (rpt strip_tac >> irule fix_phis_in_block_succs >> fs[wf_function_def]) >>
  eq_tac >> strip_tac
  >- (gvs[bb_label_fix_phis_in_block] >> metis_tac[]) >>
  qexists_tac `fix_phis_in_block (pred_labels fn bb.bb_label) bb` >>
  simp[bb_label_fix_phis_in_block] >> metis_tac[]
QED

Theorem scfg_fix_all_phis_preds:
  wf_function fn ==> pred_labels (fix_all_phis fn) lbl = pred_labels fn lbl
Proof
  strip_tac >>
  simp[pred_labels_def, block_preds_def, fix_all_phis_def,
       FILTER_MAP, MAP_MAP_o, combinTheory.o_DEF, bb_label_fix_phis_in_block] >>
  AP_TERM_TAC >> simp[FILTER_EQ] >> rpt strip_tac >>
  `bb_well_formed bb` by fs[wf_function_def] >> simp[fix_phis_in_block_succs]
QED

Theorem scfg_path_snoc_iff[local]:
  !route. route <> [] ==>
  (is_fn_path fn (route ++ [b]) <=>
   is_fn_path fn route /\ fn_cfg_edge fn (LAST route) b)
Proof
  Induct >> simp[] >> Cases_on `route` >> gvs[is_fn_path_def] >>
  metis_tac[]
QED

Theorem scfg_path_last_split:
  is_fn_path fn path /\ path <> [] /\ HD path <> b /\ LAST path = b ==>
  ?route. path = route ++ [b] /\ route <> [] /\
    is_fn_path fn route /\ fn_cfg_edge fn (LAST route) b /\ HD route = HD path
Proof
  strip_tac >>
  `FRONT path <> []` by
    (namedCases_on `path` ["", "x rest"] >> gvs[] >> Cases_on `rest` >> gvs[]) >>
  `path = FRONT path ++ [b]` by metis_tac[APPEND_FRONT_LAST] >>
  `is_fn_path fn (FRONT path ++ [b])` by metis_tac[] >>
  `HD (FRONT path) = HD path` by
    (namedCases_on `path` ["", "x rest"] >> gvs[] >> Cases_on `rest` >> gvs[]) >>
  qexists_tac `FRONT path` >> simp[] >> metis_tac[scfg_path_snoc_iff]
QED

Theorem scfg_reachable_nonentry_preds:
  fn_reachable fn b /\ fn_entry_label fn <> SOME b ==>
  pred_labels fn b <> []
Proof
  strip_tac >> gvs[fn_reachable_def] >>
  drule rtc_to_fn_path >> strip_tac >>
  `HD path <> b` by metis_tac[] >>
  drule_all scfg_path_last_split >> strip_tac >>
  `MEM (LAST route) (pred_labels fn b)` by
    (gvs[fn_cfg_edge_def] >>
     simp[NoAsms, pred_labels_def, block_preds_def, MEM_MAP, MEM_FILTER] >>
     metis_tac[]) >>
  metis_tac[MEM]
QED

Theorem scfg_fn_fix_phi_not_nop:
  wf_function fn /\ fn_inst_wf fn /\ simplify_cfg_fn_ok fn /\
  (!b. MEM b fn.fn_blocks ==> fn_reachable fn b.bb_label) /\
  MEM bb fn.fn_blocks /\ MEM i bb.bb_instructions /\ i.inst_opcode = PHI ==>
  (fix_phi_inst (pred_labels fn bb.bb_label) i).inst_opcode <> NOP
Proof
  strip_tac >>
  `fn_entry_label fn <> SOME bb.bb_label` by
    (irule scfg_phi_not_entry >> metis_tac[]) >>
  `pred_labels fn bb.bb_label <> []` by
    (irule scfg_reachable_nonentry_preds >> metis_tac[]) >>
  irule scfg_fix_phi_covered_not_nop >>
  `inst_wf i` by metis_tac[fn_inst_wf_def, EVERY_MEM] >>
  simp[] >> conj_tac >- gvs[inst_wf_def] >>
  irule scfg_reachable_pred_coverage >> metis_tac[]
QED

Theorem scfg_phi_suffix_nonphi:
  !xs. (!i j. i < j /\ j < LENGTH xs /\ (EL j xs).inst_opcode = PHI ==>
                  (EL i xs).inst_opcode = PHI) ==>
  EVERY (\i. i.inst_opcode <> PHI) (DROP (phi_prefix_length xs) xs)
Proof
  Induct >> simp[venomExecSemanticsTheory.phi_prefix_length_def] >>
  qx_gen_tac `x` >> strip_tac >> Cases_on `x.inst_opcode = PHI`
  >- (simp[venomExecSemanticsTheory.phi_prefix_length_def] >>
      first_x_assum irule >> rpt strip_tac >>
      first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]) >>
  simp[venomExecSemanticsTheory.phi_prefix_length_def, EVERY_EL] >>
  qx_gen_tac `n` >> disch_tac >> namedCases_on `n` ["", "m"] >> simp[] >>
  strip_tac >>
  first_x_assum (qspecl_then [`0`, `SUC m`] mp_tac) >> simp[]
QED

Theorem scfg_fn_fix_phis_parts:
  wf_function fn /\ fn_inst_wf fn /\ simplify_cfg_fn_ok fn /\
  (!b. MEM b fn.fn_blocks ==> fn_reachable fn b.bb_label) /\
  MEM bb fn.fn_blocks /\
  ps = TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions /\
  tail = DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions ==>
  EVERY (\i. (fix_phi_inst (pred_labels fn bb.bb_label) i).inst_opcode <> NOP) ps /\
  EVERY (\i. i.inst_opcode <> PHI) tail
Proof
  strip_tac >> conj_tac
  >- (simp[EVERY_MEM] >> gen_tac >> disch_tac >>
      `MEM i bb.bb_instructions /\ i.inst_opcode = PHI` by
        (mp_tac (Q.SPEC `bb.bb_instructions` phi_prefix_all_phi) >>
         gvs[EVERY_MEM] >> metis_tac[TAKE_DROP, MEM_APPEND]) >>
      irule scfg_fn_fix_phi_not_nop >> metis_tac[]) >>
  gvs[] >> irule scfg_phi_suffix_nonphi >>
  fs[wf_function_def, bb_well_formed_def] >> metis_tac[]
QED

