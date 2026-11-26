Theory functionInlinerWf
Ancestors
  functionInlinerDefs ASCIInumbers rich_list string arithmetic list
  venomInst venomState venomWf venomExecProofs
  simplifyCfgLocalShape simplifyCfgGraphShape simplifyCfgStruct cfgTransform cfgTransformProps cfgTransformProofs fmpStepChunk fmpStepList indexedLists passSimulationProps
  sorting venomInstIdsProps irSupply fcgDefs


Theorem digit_separator_prefix[local]:
  !xs ys tail.
    EVERY isDigit xs /\ EVERY isDigit ys /\
    isPREFIX (xs ++ "_") (ys ++ "_" ++ tail) ==> xs = ys
Proof
  Induct_on `xs` >> Cases_on `ys` >> simp[] >>
  rpt strip_tac >> gvs[] >> EVAL_TAC >> metis_tac[]
QED

Theorem inline_prefix_overlap:
  !n k l. isPREFIX (inline_prefix n) (STRCAT (inline_prefix k) l) <=> n = k
Proof
  rpt gen_tac >> eq_tac
  >- (simp[inline_prefix_def, STRCAT_ASSOC] >> strip_tac >>
      metis_tac[digit_separator_prefix,
                EVERY_isDigit_num_to_dec_string, toString_11])
  >> strip_tac >> gvs[inline_prefix_def, isPREFIX_STRCAT] >>
  metis_tac[]
QED

Theorem inline_label_bound_mono:
  !n m l. n <= m /\
    (~isPREFIX "inl" l \/ ?k. k < n /\ isPREFIX (inline_prefix k) l) ==>
    (~isPREFIX "inl" l \/ ?k. k < m /\ isPREFIX (inline_prefix k) l)
Proof
  rpt strip_tac >> metis_tac[LESS_LESS_EQ_TRANS]
QED

Theorem inline_label_bound_fresh:
  !n l.
    (~isPREFIX "inl" l \/ ?k. k < n /\ isPREFIX (inline_prefix k) l) ==>
    ~isPREFIX (inline_prefix n) l
Proof
  rpt gen_tac >> strip_tac
  >- (simp[inline_prefix_def, isPREFIX_STRCAT] >>
      rpt strip_tac >> gvs[])
  >> qpat_x_assum `isPREFIX (inline_prefix k) l`
       (strip_assume_tac o REWRITE_RULE [isPREFIX_STRCAT]) >>
  gvs[inline_prefix_overlap]
QED

Theorem inline_prefix_not_return_suffix:
  !n c. ~isPREFIX (inline_prefix n)
    (STRCAT "inline_return" (num_to_dec_string c))
Proof
  rpt gen_tac >>
  mp_tac (Q.SPEC `n` EVERY_isDigit_num_to_dec_string) >>
  simp[inline_prefix_def] >>
  Cases_on `num_to_dec_string n` >> simp[] >>
  strip_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `isDigit #"i"` (mp_tac o EVAL_RULE) >> simp[]
QED

Theorem inline_label_bound_not_return_suffix:
  !n l c.
    (~isPREFIX "inl" l \/ ?k. k < n /\ isPREFIX (inline_prefix k) l) ==>
    l <> STRCAT "inline_return" (num_to_dec_string c)
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  gvs[] >> qspecl_then [`k`, `c`] mp_tac inline_prefix_not_return_suffix >>
  simp[]
QED

Theorem inline_label_bound_clone:
  !n l. ~isPREFIX "inl" (STRCAT (inline_prefix n) l) \/
    ?k. k < SUC n /\ isPREFIX (inline_prefix k) (STRCAT (inline_prefix n) l)
Proof
  rpt gen_tac >> disj2_tac >> qexists_tac `n` >>
  simp[inline_prefix_overlap]
QED

Theorem inline_label_bound_return:
  !n c. ~isPREFIX "inl" (return_block_label (inline_prefix n) c) \/
    ?k. k < SUC n /\
      isPREFIX (inline_prefix k) (return_block_label (inline_prefix n) c)
Proof
  rewrite_tac[return_block_label_def] >>
  MATCH_ACCEPT_TAC inline_label_bound_clone
QED

Theorem inline_return_clone_distinct:
  !n l c.
    (~isPREFIX "inl" l \/ ?k. k < n /\ isPREFIX (inline_prefix k) l) ==>
    return_block_label (inline_prefix n) c <> STRCAT (inline_prefix n) l
Proof
  rpt gen_tac >> strip_tac >>
  pure_rewrite_tac[return_block_label_def, STRCAT_11] >>
  metis_tac[inline_label_bound_not_return_suffix]
QED

Theorem find_invoke_idx_bounds[local]:
  !insts name id n i. find_invoke_idx name id insts n = SOME i ==>
    n <= i /\ i - n < LENGTH insts /\
    (EL (i - n) insts).inst_opcode = INVOKE
Proof
  Induct_on `insts` >- simp[find_invoke_idx_def] >>
  rpt gen_tac >> simp[Once find_invoke_idx_def] >>
  IF_CASES_TAC >- (strip_tac >> gvs[]) >>
  strip_tac >> first_x_assum drule >> strip_tac >>
  `i - n = SUC (i - (n + 1))` by decide_tac >>
  simp[]
QED

Theorem find_invoke_site_indices[local]:
  !bbs name id n b i. find_invoke_site name id bbs n = SOME (b,i) ==>
    n <= b /\ b - n < LENGTH bbs /\
    i < LENGTH (EL (b - n) bbs).bb_instructions /\
    (EL i (EL (b - n) bbs).bb_instructions).inst_opcode = INVOKE
Proof
  Induct_on `bbs` >- simp[find_invoke_site_def] >>
  rpt gen_tac >> simp[Once find_invoke_site_def] >>
  Cases_on `find_invoke_idx name id h.bb_instructions 0` >> simp[]
  >- (strip_tac >> first_x_assum drule >> strip_tac >>
      `b - n = SUC (b - SUC n)` by decide_tac >> simp[]) >>
  strip_tac >> gvs[] >> drule find_invoke_idx_bounds >> simp[]
QED

Theorem invoke_before_terminator:
  !bb i. bb_well_formed bb /\ i < LENGTH bb.bb_instructions /\
    (EL i bb.bb_instructions).inst_opcode = INVOKE ==>
    i + 1 < LENGTH bb.bb_instructions
Proof
  rpt gen_tac >> simp[bb_well_formed_def] >> strip_tac >>
  `i <> PRE (LENGTH bb.bb_instructions)` by
    (strip_tac >> gvs[GSYM LAST_EL, is_terminator_def]) >>
  decide_tac
QED

Theorem inline_return_well_formed:
  !bb i lbl. bb_well_formed bb /\ i + 1 < LENGTH bb.bb_instructions ==>
    bb_well_formed <|bb_label := lbl;
      bb_instructions := DROP (i + 1) bb.bb_instructions|>
Proof
  rpt gen_tac >> rewrite_tac[bb_well_formed_def] >> strip_tac >>
  simp_tac (srw_ss()) [] >>
  conj_tac >- simp[DROP_EQ_NIL] >>
  conj_tac >- simp[last_drop] >>
  conj_tac >- (rpt strip_tac >> gvs[EL_DROP] >>
    qpat_x_assum `!k. _ /\ is_terminator _ ==> _`
      (qspec_then `i' + (i + 1)` mp_tac) >> simp[] >> decide_tac) >>
  rpt strip_tac >>
  `i' + (i + 1) < LENGTH bb.bb_instructions /\
   j + (i + 1) < LENGTH bb.bb_instructions` by decide_tac >>
  fs[EL_DROP] >>
  first_x_assum (qspecl_then [`i' + (i + 1)`, `j + (i + 1)`] mp_tac) >> simp[]
QED

Theorem inline_return_succs:
  !bb i lbl. i + 1 < LENGTH bb.bb_instructions ==>
    bb_succs <|bb_label := lbl;
      bb_instructions := DROP (i + 1) bb.bb_instructions|> = bb_succs bb
Proof
  rpt strip_tac >>
  `DROP (i + 1) bb.bb_instructions <> []` by simp[DROP_EQ_NIL] >>
  `bb.bb_instructions <> []` by (Cases_on `bb.bb_instructions` >> gvs[]) >>
  `LAST (DROP (i + 1) bb.bb_instructions) = LAST bb.bb_instructions`
    by simp[last_drop] >>
  Cases_on `DROP (i + 1) bb.bb_instructions` >>
  Cases_on `bb.bb_instructions` >> gvs[bb_succs_def]
QED

Theorem inline_truncated_well_formed:
  !bb i jmp. bb_well_formed bb /\ i < LENGTH bb.bb_instructions /\
    jmp.inst_opcode = JMP ==>
    bb_well_formed (bb with bb_instructions :=
      TAKE i bb.bb_instructions ++ [jmp])
Proof
  rpt gen_tac >> rewrite_tac[bb_well_formed_def] >> strip_tac >>
  simp_tac (srw_ss()) [] >>
  simp[LAST_APPEND, is_terminator_def, LENGTH_TAKE] >>
  conj_tac >- (rpt strip_tac >>
    Cases_on `i' < i` >> gvs[EL_APPEND, EL_TAKE] >>
    qpat_x_assum `!k. _ /\ is_terminator _ ==> _`
      (qspec_then `i'` mp_tac) >> simp[] >> decide_tac) >>
  rpt strip_tac >>
  `j < i` by
    (Cases_on `j < i` >- simp[] >>
     `j = i` by decide_tac >> gvs[EL_APPEND, EL_TAKE]) >>
  gvs[EL_APPEND, EL_TAKE] >>
  `j < LENGTH bb.bb_instructions` by decide_tac >> metis_tac[]
QED

Theorem clone_function_labels:
  !p f. fn_labels (clone_function p f) = MAP (STRCAT p) (fn_labels f)
Proof
  simp[clone_function_def, fn_labels_def, MAP_MAP_o, combinTheory.o_DEF,
       clone_basic_block_def]
QED

Theorem rewrite_inline_blocks_labels:
  !bbs ops outs r q bbs' q'.
    rewrite_inline_blocks ops outs r bbs q = (bbs',q') ==>
    MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) bbs
Proof
  Induct_on `bbs` >- simp[rewrite_inline_blocks_def] >>
  rpt gen_tac >> simp[Once rewrite_inline_blocks_def] >>
  pairarg_tac >>
  Cases_on `rewrite_inline_blocks ops outs r bbs q` >>
  simp[] >> strip_tac >> gvs[] >>
  first_x_assum drule >> simp[] >>
  gvs[rewrite_inline_block_def] >>
  Cases_on `rewrite_inline_insts ops outs r h.bb_instructions q` >> gvs[]
QED

Theorem clone_basic_block_well_formed:
  !p labels bb. bb_well_formed bb ==>
    bb_well_formed (clone_basic_block p labels bb)
Proof
  rpt strip_tac >>
  `bb_well_formed (bb with bb_instructions :=
      MAP (clone_instruction p labels) bb.bb_instructions)` by
    (irule map_bb_well_formed >> simp[clone_instruction_def]) >>
  qpat_x_assum `bb_well_formed (_ with bb_instructions := _)` mp_tac >>
  rewrite_tac[bb_well_formed_def, clone_basic_block_def] >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  gvs[LAST_MAP, clone_instruction_def] >> first_assum ACCEPT_TAC
QED

Theorem rewrite_inline_inst_shape:
  !ops outs r inst q xs q'.
    rewrite_inline_inst ops outs r inst q = (xs,q') ==>
    xs <> [] /\
    (if is_terminator inst.inst_opcode then
       list_terminal (\j. is_terminator j.inst_opcode) xs
     else EVERY (\j. ~is_terminator j.inst_opcode) xs) /\
    EVERY (\j. (j.inst_opcode = PHI <=> inst.inst_opcode = PHI)) xs
Proof
  rpt gen_tac >> rewrite_tac[rewrite_inline_inst_def] >>
  Cases_on `is_param_opcode inst.inst_opcode`
  >- (gvs[is_param_opcode_iff] >> IF_CASES_TAC >>
      simp[] >> strip_tac >> gvs[list_terminal_def, is_terminator_def]) >>
  Cases_on `inst.inst_opcode = RET \/ inst.inst_opcode = RETFMP`
  >- (simp[] >> strip_tac >> gvs[] >>
      simp[list_terminal_append, list_terminal_def, EVERY_EL, EL_MAPi,
           is_terminator_def]) >>
  simp[] >> strip_tac >> gvs[list_terminal_def] >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[]
QED

Theorem rewrite_inline_insts_shape:
  !insts ops outs r q xs q'.
    rewrite_inline_insts ops outs r insts q = (xs,q') ==>
    (xs = [] <=> insts = []) /\
    (EVERY (\j. ~is_terminator j.inst_opcode) insts ==>
       EVERY (\j. ~is_terminator j.inst_opcode) xs) /\
    (EVERY (\j. j.inst_opcode <> PHI) insts ==>
       EVERY (\j. j.inst_opcode <> PHI) xs) /\
    (list_terminal (\j. is_terminator j.inst_opcode) insts ==>
       list_terminal (\j. is_terminator j.inst_opcode) xs) /\
    (list_prefix (\j. j.inst_opcode = PHI) insts ==>
       list_prefix (\j. j.inst_opcode = PHI) xs)
Proof
  Induct_on `insts` >- simp[rewrite_inline_insts_def, list_terminal_def,
                            list_prefix_def] >>
  rpt gen_tac >> simp[Once rewrite_inline_insts_def] >>
  pairarg_tac >>
  Cases_on `rewrite_inline_insts ops outs r insts pi'` >>
  simp[] >> strip_tac >> gvs[] >>
  drule rewrite_inline_inst_shape >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  simp[EVERY_APPEND] >>
  conj_tac >- (strip_tac >> gvs[]) >>
  conj_tac >- (gvs[EVERY_MEM] >> metis_tac[]) >>
  conj_tac
  >- (Cases_on `insts = []` >>
      gvs[list_terminal_def, list_terminal_append] >> strip_tac >> gvs[]) >>
  rewrite_tac[list_prefix_def, list_prefix_append] >> strip_tac >>
  conj_tac
  >- (Cases_on `h.inst_opcode = PHI`
      >- (irule list_prefix_every >> gvs[EVERY_MEM]) >>
      irule list_prefix_none >> gvs[EVERY_MEM]) >>
  conj_tac >- metis_tac[] >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem rewrite_inline_block_well_formed:
  !bb ops outs r q bb' q'.
    bb_well_formed bb /\
    rewrite_inline_block ops outs r bb q = (bb',q') ==>
    bb_well_formed bb'
Proof
  rpt gen_tac >> rewrite_tac[rewrite_inline_block_def] >>
  Cases_on `rewrite_inline_insts ops outs r bb.bb_instructions q` >>
  simp[] >> strip_tac >> gvs[] >>
  drule rewrite_inline_insts_shape >>
  gvs[bb_well_formed_list]
QED

Theorem rewrite_inline_blocks_well_formed:
  !bbs ops outs r q bbs' q'.
    EVERY bb_well_formed bbs /\
    rewrite_inline_blocks ops outs r bbs q = (bbs',q') ==>
    EVERY bb_well_formed bbs' /\ (bbs' = [] <=> bbs = [])
Proof
  Induct_on `bbs` >- simp[rewrite_inline_blocks_def] >>
  rpt gen_tac >> simp[Once rewrite_inline_blocks_def] >>
  pairarg_tac >>
  Cases_on `rewrite_inline_blocks ops outs r bbs q` >>
  simp[] >> strip_tac >> gvs[] >>
  first_x_assum drule >> simp[] >> strip_tac >>
  drule_all rewrite_inline_block_well_formed >> simp[]
QED

Theorem rewrite_inline_inst_successors:
  !ops outs r inst q xs q' l.
    rewrite_inline_inst ops outs r inst q = (xs,q') /\
    MEM l (get_successors (LAST xs)) ==>
    l = r \/ MEM l (get_successors inst)
Proof
  rpt gen_tac >> rewrite_tac[rewrite_inline_inst_def] >>
  Cases_on `is_param_opcode inst.inst_opcode`
  >- (gvs[is_param_opcode_iff] >> IF_CASES_TAC >> simp[] >>
      strip_tac >> gvs[get_successors_def, is_terminator_def]) >>
  Cases_on `inst.inst_opcode = RET \/ inst.inst_opcode = RETFMP`
  >- (simp[] >> strip_tac >>
      gvs[LAST_APPEND_CONS, get_successors_def, is_terminator_def,
          get_label_def]) >>
  simp[] >> strip_tac >> gvs[]
QED

Theorem rewrite_inline_insts_successors:
  !insts ops outs r q xs q' l.
    insts <> [] /\
    rewrite_inline_insts ops outs r insts q = (xs,q') /\
    MEM l (get_successors (LAST xs)) ==>
    l = r \/ MEM l (get_successors (LAST insts))
Proof
  Induct_on `insts` >- simp[] >>
  rpt gen_tac >> simp[Once rewrite_inline_insts_def] >>
  pairarg_tac >>
  Cases_on `rewrite_inline_insts ops outs r insts pi'` >>
  simp[] >> strip_tac >> gvs[] >>
  Cases_on `insts = []`
  >- (gvs[rewrite_inline_insts_def] >>
      drule_all rewrite_inline_inst_successors >> simp[]) >>
  drule rewrite_inline_insts_shape >> strip_tac >>
  gvs[LAST_APPEND_NOT_NIL, LAST_CONS_cond] >>
  first_x_assum drule >> simp[]
QED

Theorem rewrite_inline_block_successors:
  !bb ops outs r q bb' q' l.
    rewrite_inline_block ops outs r bb q = (bb',q') /\
    MEM l (bb_succs bb') ==> l = r \/ MEM l (bb_succs bb)
Proof
  rpt gen_tac >> rewrite_tac[rewrite_inline_block_def] >>
  namedCases_on `rewrite_inline_insts ops outs r bb.bb_instructions q`
    ["insts q2"] >>
  simp[] >> strip_tac >> gvs[] >>
  drule rewrite_inline_insts_shape >> strip_tac >>
  Cases_on `bb.bb_instructions = []` >- gvs[bb_succs_def] >>
  Cases_on `insts` >> Cases_on `bb.bb_instructions` >>
  gvs[bb_succs_def, MEM_nub] >>
  drule_at (Pos (el 2)) rewrite_inline_insts_successors >> simp[]
QED

Theorem rewrite_inline_blocks_successors:
  !bbs ops outs r q bbs' q' bb' l.
    rewrite_inline_blocks ops outs r bbs q = (bbs',q') /\
    MEM bb' bbs' /\ MEM l (bb_succs bb') ==>
    l = r \/ ?bb. MEM bb bbs /\ MEM l (bb_succs bb)
Proof
  Induct_on `bbs` >- simp[rewrite_inline_blocks_def] >>
  rpt gen_tac >> simp[Once rewrite_inline_blocks_def] >>
  pairarg_tac >>
  Cases_on `rewrite_inline_blocks ops outs r bbs q` >>
  simp[] >> strip_tac >> gvs[]
  >- (drule_all rewrite_inline_block_successors >> metis_tac[]) >>
  first_x_assum drule >> metis_tac[]
QED

Theorem clone_operand_labels[local]:
  !ops p labels.
    MAP THE (FILTER IS_SOME (MAP get_label (MAP (clone_operand p labels) ops))) =
    MAP (\l. if MEM l labels then STRCAT p l else l)
      (MAP THE (FILTER IS_SOME (MAP get_label ops)))
Proof
  Induct_on `ops` >- simp[] >>
  rpt gen_tac >> Cases_on `h` >>
  simp[clone_operand_def, get_label_def] >>
  Cases_on `MEM s labels` >> simp[get_label_def]
QED

Theorem clone_instruction_successors:
  !p labels inst.
    get_successors (clone_instruction p labels inst) =
    MAP (\l. if MEM l labels then STRCAT p l else l) (get_successors inst)
Proof
  simp[clone_instruction_def, get_successors_def, clone_operand_labels] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[]
QED

Theorem clone_basic_block_successors:
  !p labels bb l.
    MEM l (bb_succs (clone_basic_block p labels bb)) <=>
    ?k. MEM k (bb_succs bb) /\
        l = (if MEM k labels then STRCAT p k else k)
Proof
  rpt gen_tac >> Cases_on `bb.bb_instructions` >>
  simp[bb_succs_def, clone_basic_block_def, LAST_CONS_cond, LAST_MAP,
       clone_instruction_successors, MEM_nub, MEM_MAP] >>
  Cases_on `t = []` >> simp[clone_instruction_successors, MEM_MAP] >>
  metis_tac[]
QED

Theorem clone_function_successors:
  !f p bb l.
    fn_succs_closed f /\
    MEM bb (clone_function p f).fn_blocks /\ MEM l (bb_succs bb) ==>
    ?k. MEM k (fn_labels f) /\ l = STRCAT p k
Proof
  simp[clone_function_def, MEM_MAP] >> rpt strip_tac >> gvs[] >>
  gvs[clone_basic_block_successors] >>
  `MEM k (fn_labels f)` by metis_tac[fn_succs_closed_def] >>
  gvs[] >> metis_tac[]
QED

Theorem clone_rewrite_blocks_structure:
  !f p ops outs r q bbs q'.
    wf_function f /\
    rewrite_inline_blocks ops outs r (clone_function p f).fn_blocks q = (bbs,q') ==>
    bbs <> [] /\
    MAP (\bb. bb.bb_label) bbs = MAP (STRCAT p) (fn_labels f) /\
    EVERY bb_well_formed bbs /\
    (!bb l. MEM bb bbs /\ MEM l (bb_succs bb) ==>
      l = r \/ ?k. MEM k (fn_labels f) /\ l = STRCAT p k)
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY bb_well_formed (clone_function p f).fn_blocks` by
    (gvs[clone_function_def, EVERY_MAP, EVERY_MEM, MEM_MAP, wf_function_def] >>
     metis_tac[clone_basic_block_well_formed]) >>
  drule_all rewrite_inline_blocks_well_formed >> strip_tac >>
  conj_tac
  >- (gvs[clone_function_def, wf_function_def, fn_has_entry_def]) >>
  conj_tac
  >- (drule rewrite_inline_blocks_labels >>
      rewrite_tac[GSYM fn_labels_def, clone_function_labels] >> simp[]) >>
  conj_tac >- simp[] >>
  rpt strip_tac >> drule_all rewrite_inline_blocks_successors >>
  strip_tac >- simp[] >>
  metis_tac[clone_function_successors, wf_function_def]
QED

Theorem inline_phi_inst_fields[local]:
  !old new i.
    (if i.inst_opcode <> PHI then i else subst_label_inst old new i).inst_opcode =
      i.inst_opcode /\
    (if i.inst_opcode <> PHI then i else subst_label_inst old new i).inst_id =
      i.inst_id /\
    get_successors (if i.inst_opcode <> PHI then i else subst_label_inst old new i) =
      get_successors i
Proof
  rpt gen_tac >> Cases_on `i.inst_opcode = PHI` >>
  simp[subst_label_inst_fields, get_successors_def, is_terminator_def]
QED

Theorem inline_phi_block_fields[local]:
  !old new bb.
    (bb with bb_instructions := MAP (\i.
      if i.inst_opcode <> PHI then i else subst_label_inst old new i)
      bb.bb_instructions).bb_label = bb.bb_label /\
    (bb_well_formed bb ==>
      bb_well_formed (bb with bb_instructions := MAP (\i.
        if i.inst_opcode <> PHI then i else subst_label_inst old new i)
        bb.bb_instructions)) /\
    bb_succs (bb with bb_instructions := MAP (\i.
      if i.inst_opcode <> PHI then i else subst_label_inst old new i)
      bb.bb_instructions) = bb_succs bb /\
    MAP (\i. i.inst_id) (MAP (\i.
      if i.inst_opcode <> PHI then i else subst_label_inst old new i)
      bb.bb_instructions) = MAP (\i. i.inst_id) bb.bb_instructions
Proof
  rpt gen_tac >> simp[] >> conj_tac
  >- (strip_tac >> irule map_bb_well_formed >> simp[inline_phi_inst_fields]) >>
  conj_tac
  >- (irule bb_succs_map_preserve >> simp[inline_phi_inst_fields]) >>
  simp[MAP_MAP_o, combinTheory.o_DEF, inline_phi_inst_fields]
QED

Theorem fix_inline_phis_structure:
  !old new ret f.
    fn_labels (fix_inline_phis old new ret f) = fn_labels f /\
    (fn_has_entry (fix_inline_phis old new ret f) <=> fn_has_entry f) /\
    (EVERY bb_well_formed f.fn_blocks ==>
      EVERY bb_well_formed (fix_inline_phis old new ret f).fn_blocks) /\
    (fn_succs_closed (fix_inline_phis old new ret f) <=> fn_succs_closed f) /\
    (fn_inst_ids_distinct (fix_inline_phis old new ret f) <=> fn_inst_ids_distinct f)
Proof
  rpt gen_tac >>
  qabbrev_tac `tr = \bb. if MEM bb.bb_label (bb_succs ret) then
    bb with bb_instructions := MAP (\i.
      if i.inst_opcode <> PHI then i else subst_label_inst old new i)
      bb.bb_instructions else bb` >>
  `!bb. (tr bb).bb_label = bb.bb_label /\
        (bb_well_formed bb ==> bb_well_formed (tr bb)) /\
        bb_succs (tr bb) = bb_succs bb /\
        MAP (\i. i.inst_id) (tr bb).bb_instructions =
        MAP (\i. i.inst_id) bb.bb_instructions` by
    (gen_tac >> simp[Abbr `tr`] >> IF_CASES_TAC >>
     simp[inline_phi_block_fields]) >>
  `fix_inline_phis old new ret f = f with fn_blocks := MAP tr f.fn_blocks` by
    simp[Abbr `tr`, fix_inline_phis_def] >>
  asm_rewrite_tac[] >>
  simp[fn_labels_def, fn_has_entry_def, fn_succs_closed_def,
       fn_inst_ids_distinct_def, MAP_MAP_o, combinTheory.o_DEF, MEM_MAP,
       EVERY_MEM] >> metis_tac[]
QED

Theorem renumber_insts_fold[local]:
  !insts n acc.
    FOLDL (\(id, acc) inst. (id + 1n, acc ++ [inst with inst_id := id]))
      (n,acc) insts =
    (n + LENGTH insts,
     acc ++ MAPi (\k i. i with inst_id := n + k) insts)
Proof
  Induct_on `insts` >- simp[] >>
  rpt gen_tac >> simp[Once FOLDL] >>
  first_x_assum (qspecl_then [`n + 1`, `acc ++ [h with inst_id := n]`] SUBST1_TAC) >>
  pure_once_rewrite_tac[MAPi_def] >>
  simp_tac (srw_ss()) [APPEND_ASSOC, ADD_ASSOC, LENGTH, ADD_CLAUSES] >>
  AP_THM_TAC >> AP_TERM_TAC >>
  simp_tac (srw_ss()) [FUN_EQ_THM, combinTheory.o_DEF, ADD_CLAUSES, ADD_ASSOC] >>
  rewrite_tac[ADD1]
QED


Theorem renumber_block_structure:
  !n bb.
    FST (renumber_block_inst_ids n bb) = n + LENGTH bb.bb_instructions /\
    (SND (renumber_block_inst_ids n bb)).bb_label = bb.bb_label /\
    (bb_well_formed bb ==> bb_well_formed (SND (renumber_block_inst_ids n bb))) /\
    bb_succs (SND (renumber_block_inst_ids n bb)) = bb_succs bb /\
    MAP (\i. i.inst_id) (SND (renumber_block_inst_ids n bb)).bb_instructions =
      GENLIST (\k. n + k) (LENGTH bb.bb_instructions)
Proof
  rpt gen_tac >> simp[renumber_block_inst_ids_def, renumber_insts_fold] >>
  conj_tac
  >- (strip_tac >> irule mapi_transform_bb_well_formed >> simp[]) >>
  conj_tac
  >- (irule mapi_transform_bb_succs_weak >> simp[get_successors_def]) >>
  irule LIST_EQ >> simp[EL_MAPi, EL_GENLIST, LENGTH_MAPi, combinTheory.o_DEF]
QED

Theorem renumber_inline_blocks_structure[local]:
  !bbs n.
    MAP (\bb. (bb.bb_label, bb_succs bb)) (SND (renumber_inline_blocks n bbs)) =
      MAP (\bb. (bb.bb_label, bb_succs bb)) bbs /\
    (EVERY bb_well_formed bbs ==>
      EVERY bb_well_formed (SND (renumber_inline_blocks n bbs))) /\
    FST (renumber_inline_blocks n bbs) = n + LENGTH (fn_insts_blocks bbs) /\
    MAP (\i. i.inst_id) (fn_insts_blocks (SND (renumber_inline_blocks n bbs))) =
      GENLIST (\k. n + k) (LENGTH (fn_insts_blocks bbs))
Proof
  Induct_on `bbs` >- simp[renumber_inline_blocks_def, fn_insts_blocks_def] >>
  rpt gen_tac >> simp[renumber_inline_blocks_def] >>
  qspecl_then [`n`, `h`] strip_assume_tac renumber_block_structure >>
  Cases_on `renumber_block_inst_ids n h` >>
  first_x_assum (qspec_then `q` mp_tac) >>
  Cases_on `renumber_inline_blocks q bbs` >>
  asm_simp_tac bool_ss [pairTheory.UNCURRY_DEF, pairTheory.FST,
    pairTheory.SND] >> strip_tac >>
  gvs[fn_insts_blocks_def] >>
  simp[LIST_EQ_REWRITE, EL_APPEND_EQN, EL_GENLIST] >>
  rpt strip_tac >> rw[] >> decide_tac
QED

Theorem renumber_inline_blocks_labels[local]:
  !bbs n.
    MAP (\bb. bb.bb_label) (SND (renumber_inline_blocks n bbs)) =
    MAP (\bb. bb.bb_label) bbs
Proof
  rpt gen_tac >> qspecl_then [`bbs`,`n`] strip_assume_tac
    renumber_inline_blocks_structure >>
  pop_assum kall_tac >>
  qpat_x_assum `MAP _ _ = MAP _ _` (mp_tac o Q.AP_TERM `MAP FST :
    (string # string list) list -> string list`) >>
  simp[MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem inline_call_site_labels[local]:
  !caller callee p r n b i.
    b < LENGTH caller.fn_blocks ==>
    fn_labels (SND (inline_call_site p r n caller callee b i)) =
      fn_labels caller ++ [r] ++ MAP (STRCAT p) (fn_labels callee)
Proof
  rpt strip_tac >>
  asm_simp_tac (srw_ss() -* ["indexedLists"]) [inline_call_site_def, oEL_THM, LET_THM] >>
  pairarg_tac >>
  drule rewrite_inline_blocks_labels >> strip_tac >>
  `LUPDATE (EL b caller.fn_blocks).bb_label b (fn_labels caller) =
     fn_labels caller` by
    (`(EL b caller.fn_blocks).bb_label = EL b (fn_labels caller)` by
       simp[fn_labels_def, EL_MAP] >>
     pop_assum SUBST1_TAC >> irule LUPDATE_SAME >> simp[fn_labels_def]) >>
  asm_simp_tac (srw_ss() -* ["indexedLists"]) [fn_labels_def,
    renumber_inline_blocks_labels, LUPDATE_MAP] >>
  gvs[GSYM fn_labels_def] >>
  simp[GSYM fn_labels_def, clone_function_labels]
QED

Theorem inline_call_site_label_bound[local]:
  !caller callee n c fresh b i.
    b < LENGTH caller.fn_blocks /\
    EVERY (\bb. ~isPREFIX "inl" bb.bb_label \/
      ?k. k < n /\ isPREFIX (inline_prefix k) bb.bb_label) caller.fn_blocks ==>
    EVERY (\bb. ~isPREFIX "inl" bb.bb_label \/
      ?k. k < SUC n /\ isPREFIX (inline_prefix k) bb.bb_label)
      (SND (inline_call_site (inline_prefix n)
        (return_block_label (inline_prefix n) c) fresh caller callee b i)).fn_blocks
Proof
  rpt strip_tac >>
  qmatch_goalsub_abbrev_tac `EVERY _ out.fn_blocks` >>
  `fn_labels out = fn_labels caller ++ [return_block_label (inline_prefix n) c] ++
      MAP (STRCAT (inline_prefix n)) (fn_labels callee)` by
    simp[Abbr `out`, inline_call_site_labels] >>
  `EVERY (\l. ~isPREFIX "inl" l \/
     ?k. k < SUC n /\ isPREFIX (inline_prefix k) l) (fn_labels out)`
  suffices_by simp_tac bool_ss [fn_labels_def, EVERY_MAP, combinTheory.o_DEF] >>
  asm_rewrite_tac[] >>
  simp_tac bool_ss [EVERY_APPEND, EVERY_DEF, EVERY_MAP,
    combinTheory.o_DEF, inline_label_bound_return, inline_label_bound_clone] >>
  simp_tac bool_ss [fn_labels_def, EVERY_MAP, combinTheory.o_DEF] >>
  qpat_x_assum `EVERY _ caller.fn_blocks` mp_tac >>
  simp_tac bool_ss [EVERY_MEM] >>
  metis_tac[inline_label_bound_mono, LESS_EQ_SUC_REFL]
QED

Theorem inline_call_site_blocks_well_formed[local]:
  !caller callee p r n b i.
    wf_function caller /\ wf_function callee /\
    b < LENGTH caller.fn_blocks /\
    i < LENGTH (EL b caller.fn_blocks).bb_instructions /\
    (EL i (EL b caller.fn_blocks).bb_instructions).inst_opcode = INVOKE ==>
    EVERY bb_well_formed (SND (inline_call_site p r n caller callee b i)).fn_blocks
Proof
  rpt strip_tac >>
  qabbrev_tac `bb = EL b caller.fn_blocks` >>
  `bb_well_formed bb` by metis_tac[wf_function_def, MEM_EL] >>
  `i + 1 < LENGTH bb.bb_instructions` by metis_tac[invoke_before_terminator] >>
  asm_simp_tac (srw_ss() -* ["indexedLists"])
    [inline_call_site_def, oEL_THM, LET_THM] >> pairarg_tac >>
  drule_all clone_rewrite_blocks_structure >> strip_tac >>
  simp[EVERY_APPEND, renumber_inline_blocks_structure] >>
  conj_tac
  >- (irule IMP_EVERY_LUPDATE >> conj_tac
      >- (irule inline_truncated_well_formed >> simp[Abbr `bb`]) >>
      simp[EVERY_MEM, GSYM AND_IMP_INTRO] >> metis_tac[wf_function_def]) >>
  metis_tac[inline_return_well_formed]
QED

Theorem inline_call_site_labels_distinct[local]:
  !caller callee n c fresh b i.
    wf_function caller /\ wf_function callee /\
    b < LENGTH caller.fn_blocks /\
    EVERY (\bb. ~isPREFIX "inl" bb.bb_label \/
      ?k. k < n /\ isPREFIX (inline_prefix k) bb.bb_label) caller.fn_blocks /\
    EVERY (\bb. ~isPREFIX "inl" bb.bb_label \/
      ?k. k < n /\ isPREFIX (inline_prefix k) bb.bb_label) callee.fn_blocks ==>
    ALL_DISTINCT (fn_labels (SND (inline_call_site (inline_prefix n)
      (return_block_label (inline_prefix n) c) fresh caller callee b i)))
Proof
  rpt strip_tac >>
  drule inline_call_site_labels >>
  disch_then (qspecl_then [`callee`, `inline_prefix n`,
    `return_block_label (inline_prefix n) c`, `fresh`, `i`] SUBST1_TAC) >>
  `ALL_DISTINCT (fn_labels caller) /\ ALL_DISTINCT (fn_labels callee)` by
    metis_tac[wf_function_def] >>
  asm_simp_tac bool_ss [ALL_DISTINCT_APPEND, ALL_DISTINCT, MEM_APPEND, MEM,
    ALL_DISTINCT_MAP, STRCAT_11, MEM_MAP] >>
  conj_tac
  >- (strip_tac >>
      `?bb. MEM bb caller.fn_blocks /\
        bb.bb_label = return_block_label (inline_prefix n) c` by
        (gvs[fn_labels_def, MEM_MAP] >> metis_tac[]) >>
      qpat_x_assum `EVERY _ caller.fn_blocks` mp_tac >>
      pure_rewrite_tac[EVERY_MEM] >> BETA_TAC >> strip_tac >>
      first_x_assum drule >>
      disch_then (mp_tac o MATCH_MP inline_label_bound_fresh) >>
      asm_simp_tac bool_ss [return_block_label_def, isPREFIX_STRCAT, STRCAT_11]) >>
  conj_tac
  >- (irule ALL_DISTINCT_MAP_INJ >> simp[STRCAT_11]) >>
  rpt gen_tac >> strip_tac
  >- (rpt strip_tac >>
      `?bb. MEM bb caller.fn_blocks /\ bb.bb_label = e` by
        (gvs[fn_labels_def, MEM_MAP] >> metis_tac[]) >>
      qpat_x_assum `EVERY _ caller.fn_blocks` mp_tac >>
      pure_rewrite_tac[EVERY_MEM] >> BETA_TAC >> strip_tac >>
      first_x_assum drule >>
      disch_then (mp_tac o MATCH_MP inline_label_bound_fresh) >>
      asm_simp_tac bool_ss [isPREFIX_STRCAT, STRCAT_11]) >>
  rpt strip_tac >>
  `?bb. MEM bb callee.fn_blocks /\ bb.bb_label = y` by
    (gvs[fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  qpat_x_assum `EVERY _ callee.fn_blocks` mp_tac >>
  pure_rewrite_tac[EVERY_MEM] >> BETA_TAC >> strip_tac >>
  first_x_assum drule >>
  disch_then (mp_tac o MATCH_MP inline_return_clone_distinct) >>
  metis_tac[]
QED

Theorem inline_call_site_succs_closed[local]:
  !caller callee p r n b i.
    wf_function caller /\ wf_function callee /\
    b < LENGTH caller.fn_blocks /\
    i < LENGTH (EL b caller.fn_blocks).bb_instructions /\
    (EL i (EL b caller.fn_blocks).bb_instructions).inst_opcode = INVOKE ==>
    fn_succs_closed (SND (inline_call_site p r n caller callee b i))
Proof
  rpt strip_tac >>
  qabbrev_tac `bb = EL b caller.fn_blocks` >>
  `bb_well_formed bb` by metis_tac[wf_function_def, MEM_EL] >>
  `i + 1 < LENGTH bb.bb_instructions` by metis_tac[invoke_before_terminator] >>
  `callee.fn_blocks <> []` by metis_tac[wf_function_def, fn_has_entry_def] >>
  drule inline_call_site_labels >>
  disch_then (qspecl_then [`callee`,`p`,`r`,`n`,`i`] assume_tac) >>
  simp_tac (srw_ss()) [fn_succs_closed_def] >>
  asm_simp_tac (srw_ss() -* ["indexedLists"])
    [inline_call_site_def, oEL_THM, LET_THM] >> pairarg_tac >>
  drule_all clone_rewrite_blocks_structure >> strip_tac >>
  qmatch_goalsub_abbrev_tac `LUPDATE trunc b _` >>
  qmatch_goalsub_abbrev_tac `[retbb]` >>
  `bb_succs retbb = bb_succs bb` by
    fs[Abbr `retbb`, Abbr `bb`, inline_return_succs] >>
  `bb_succs trunc = [STRCAT p (HD callee.fn_blocks).bb_label]` by
    (Cases_on `callee.fn_blocks` >- gvs[] >>
     Cases_on `TAKE i bb.bb_instructions` >>
     simp[Abbr `trunc`, clone_function_def, clone_basic_block_def,
       bb_succs_def, LAST_APPEND_CONS, LAST_CONS_cond, LAST_APPEND, get_successors_def,
       is_terminator_def, get_label_def, nub_def]) >>
  `!bb l. MEM bb caller.fn_blocks /\ MEM l (bb_succs bb) ==>
    MEM l (fn_labels caller)` by metis_tac[wf_function_def, fn_succs_closed_def] >>
  simp[MEM_MAP] >> rpt strip_tac
  >- (drule MEM_LUPDATE_E >> strip_tac >> gvs[]
      >- (disj2_tac >> Cases_on `callee.fn_blocks` >> gvs[fn_labels_def]) >>
      metis_tac[fn_labels_def, MEM_MAP])
  >- (fs[Abbr `bb`] >> metis_tac[MEM_EL]) >>
  rename1 `MEM new_bb (SND (renumber_inline_blocks _ bbs))` >>
  `MEM (new_bb.bb_label, bb_succs new_bb)
        (MAP (\bb. (bb.bb_label, bb_succs bb)) bbs)` by
    (qspecl_then [`bbs`, `SUC n`] (SUBST1_TAC o SYM o CONJUNCT1)
       renumber_inline_blocks_structure >>
     simp[MEM_MAP] >> qexists_tac `new_bb` >> simp[]) >>
  pop_assum mp_tac >> simp[MEM_MAP] >> metis_tac[]
QED

Theorem fn_labels_every_cong:
  !f g P. fn_labels f = fn_labels g ==>
    (EVERY (\bb. P bb.bb_label) f.fn_blocks <=>
     EVERY (\bb. P bb.bb_label) g.fn_blocks)
Proof
  rpt strip_tac >>
  `EVERY P (fn_labels f) = EVERY P (fn_labels g)` by simp[] >>
  pop_assum mp_tac >>
  simp_tac bool_ss [fn_labels_def, EVERY_MAP, combinTheory.o_DEF]
QED

Theorem fix_inline_phis_ids[local]:
  !old new ret fn.
    fn_ir_inst_ids (fix_inline_phis old new ret fn) = fn_ir_inst_ids fn
Proof
  simp[fn_ir_inst_ids_def, fix_inline_phis_def, MAP_MAP_o,
       combinTheory.o_DEF] >>
  rpt gen_tac >> AP_TERM_TAC >> irule MAP_CONG >> simp[] >>
  gen_tac >> strip_tac >> IF_CASES_TAC >>
  simp[block_ir_inst_ids_def, inline_phi_block_fields]
QED

Theorem lupdate_split[local]:
  !bbs b x. b < LENGTH bbs ==>
    LUPDATE x b bbs = TAKE b bbs ++ x::DROP (SUC b) bbs
Proof
  Induct >> Cases_on `b` >> simp[LUPDATE_def]
QED

Theorem inliner_blocks_ids[local]:
  !bbs. FLAT (MAP block_ir_inst_ids bbs) =
        MAP (\inst. inst.inst_id) (fn_insts_blocks bbs)
Proof
  simp_tac bool_ss [fn_insts_blocks_map_id, GSYM block_ir_inst_ids_def, ETA_AX]
QED

(* Moving the continuation permutes the retained ids. The only old id
   removed is that of the INVOKE, and the new ids are one interval. *)
Theorem inline_call_site_id_layout[local]:
  !caller callee p r n b i n' caller'.
    b < LENGTH caller.fn_blocks /\
    i < LENGTH (EL b caller.fn_blocks).bb_instructions /\
    inline_call_site p r n caller callee b i = (n',caller') ==>
    ?removed kept.
      PERM (fn_ir_inst_ids caller) (removed::kept) /\
      PERM (fn_ir_inst_ids caller')
           (kept ++ GENLIST (\k. n + k) (n' - n)) /\
      n < n'
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `bb = EL b caller.fn_blocks` >>
  qabbrev_tac `before = TAKE b caller.fn_blocks` >>
  qabbrev_tac `after = DROP (SUC b) caller.fn_blocks` >>
  qabbrev_tac `ids = block_ir_inst_ids bb` >>
  `LENGTH ids = LENGTH bb.bb_instructions` by
    simp[Abbr `ids`, block_ir_inst_ids_def] >>
  qexistsl_tac [`EL i ids`,
    `FLAT (MAP block_ir_inst_ids before) ++ TAKE i ids ++
     FLAT (MAP block_ir_inst_ids after) ++ DROP (SUC i) ids`] >>
  conj_tac
  >- (`caller.fn_blocks = before ++ [bb] ++ after` by
        simp[Abbr `before`, Abbr `bb`, Abbr `after`, TAKE_DROP_SUC] >>
      `ids = TAKE i ids ++ [EL i ids] ++ DROP (SUC i) ids` by
        simp[SimpRHS, TAKE_DROP_SUC] >>
      simp[fn_ir_inst_ids_def, MAP_APPEND, FLAT_APPEND] >>
      qpat_x_assum `ids = _`
        (fn th => CONV_TAC (RATOR_CONV (RAND_CONV (ONCE_REWRITE_CONV [th])))) >>
      simp[PERM_alt, FILTER_APPEND_DISTRIB] >> rpt gen_tac >>
      rw[] >> decide_tac) >>
  qpat_x_assum `inline_call_site _ _ _ _ _ _ _ = _` mp_tac >>
  simp[inline_call_site_def, oEL_THM, lupdate_split] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `rewrite_inline_blocks _ _ _ _ 0 = (bbs,_)` >>
  qspecl_then [`bbs`, `SUC n`] strip_assume_tac
    renumber_inline_blocks_structure >>
  `FLAT (MAP block_ir_inst_ids (SND (renumber_inline_blocks (SUC n) bbs))) =
    GENLIST (\k. SUC n + k) (LENGTH (fn_insts_blocks bbs))` by
    (pure_rewrite_tac[inliner_blocks_ids] >>
     first_assum ACCEPT_TAC) >>
  `GENLIST (\k. n + k) (SUC n + LENGTH (fn_insts_blocks bbs) - n) =
    n :: GENLIST (\k. SUC n + k) (LENGTH (fn_insts_blocks bbs))` by
    (`SUC n + LENGTH (fn_insts_blocks bbs) - n =
       SUC (LENGTH (fn_insts_blocks bbs))` by decide_tac >>
     ONCE_ASM_REWRITE_TAC[] >>
     simp[LIST_EQ_REWRITE, EL_GENLIST] >>
     gen_tac >> Cases_on `x` >> simp[EL_GENLIST] >> decide_tac) >>
  simp_tac (srw_ss()) [fn_ir_inst_ids_def, MAP_APPEND, FLAT_APPEND] >>
  ONCE_ASM_REWRITE_TAC[] >>
  simp[block_ir_inst_ids_def, MAP_TAKE, MAP_DROP, Abbr `ids`, Abbr `bb`,
       Abbr `before`, Abbr `after`, GSYM ADD1] >>
  qpat_x_assum `GENLIST _ _ = n :: _` mp_tac >> simp[] >> strip_tac >>
  simp[] >>
  simp[PERM_alt, FILTER_APPEND_DISTRIB] >> rpt gen_tac >>
  rw[] >> decide_tac
QED

Theorem inliner_fresh_ids[local]:
  !ids ids' rest lo hi removed kept.
    PERM ids (removed::kept) /\
    PERM ids' (kept ++ GENLIST (\k. lo + k) (hi - lo)) /\
    lo < hi /\ EVERY (\id. id < lo) (ids ++ rest) ==>
    EVERY (\id. id < hi) (ids' ++ rest) /\
    (ALL_DISTINCT (ids ++ rest) ==> ALL_DISTINCT (ids' ++ rest))
Proof
  rpt strip_tac >>
  `PERM (ids ++ rest) (removed::(kept ++ rest))` by
    metis_tac[PERM_APPEND_IFF, APPEND] >>
  `PERM (ids' ++ rest) ((kept ++ GENLIST (\k. lo + k) (hi - lo)) ++ rest)` by
    simp[PERM_APPEND_IFF] >>
  qpat_x_assum `PERM (ids ++ rest) _` (fn th =>
    assume_tac (Q.INST [`P` |-> `\id. id < lo`] (MATCH_MP PERM_EVERY th)) >>
    assume_tac (MATCH_MP ALL_DISTINCT_PERM th)) >>
  qpat_x_assum `PERM (ids' ++ rest) _` (fn th =>
    assume_tac (Q.INST [`P` |-> `\id. id < hi`] (MATCH_MP PERM_EVERY th)) >>
    assume_tac (MATCH_MP ALL_DISTINCT_PERM th)) >>
  asm_rewrite_tac[] >>
  gs[EVERY_APPEND, ALL_DISTINCT_APPEND, ALL_DISTINCT_GENLIST,
     EVERY_GENLIST, MEM_GENLIST, MEM_APPEND, EVERY_MEM] >>
  rpt strip_tac >> gs[] >> res_tac >> decide_tac
QED

Theorem inline_one_site_ids[local]:
  !caller callee site ist caller' ist' rest.
    EVERY (\id. id < ist.is_next_inst_id) (fn_ir_inst_ids caller ++ rest) /\
    inline_one_site caller callee site ist = SOME (caller',ist') ==>
    ist.is_next_inst_id <= ist'.is_next_inst_id /\
    EVERY (\id. id < ist'.is_next_inst_id) (fn_ir_inst_ids caller' ++ rest) /\
    (ALL_DISTINCT (fn_ir_inst_ids caller ++ rest) ==>
     ALL_DISTINCT (fn_ir_inst_ids caller' ++ rest))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `inline_one_site _ _ _ _ = _` mp_tac >>
  simp[inline_one_site_def] >>
  Cases_on `find_invoke_site callee.fn_name site caller.fn_blocks 0` >> simp[] >>
  PairCases_on `x` >>
  drule find_invoke_site_indices >> simp[] >> strip_tac >>
  pairarg_tac >>
  drule_all inline_call_site_id_layout >> strip_tac >>
  drule_all inliner_fresh_ids >> strip_tac >>
  Cases_on `lookup_block
     (return_block_label (inline_prefix ist.is_inline_count) ist.is_label_counter)
     caller''.fn_blocks` >>
  simp[] >> rpt strip_tac >> gvs[fix_inline_phis_ids]
QED

Theorem inliner_fn_ids_distinct[local]:
  !fn. fn_inst_ids_distinct fn = ALL_DISTINCT (fn_ir_inst_ids fn)
Proof
  simp_tac bool_ss [fn_inst_ids_distinct_def, fn_ir_inst_ids_def,
                    GSYM block_ir_inst_ids_def, ETA_AX]
QED

Theorem inliner_ctx_ids_distinct[local]:
  !ctx. ctx_inst_ids_distinct ctx =
    ALL_DISTINCT (FLAT (MAP fn_ir_inst_ids ctx.ctx_functions))
Proof
  simp_tac bool_ss [ctx_inst_ids_distinct_def, GSYM block_ir_inst_ids_def,
                    ETA_AX, GSYM fn_ir_inst_ids_def]
QED

Theorem inline_one_site_structure[local]:
  !caller callee site ist caller' ist'.
    wf_function caller /\ wf_function callee /\
    EVERY (\id. id < ist.is_next_inst_id) (fn_ir_inst_ids caller) /\
    EVERY (\bb. ~isPREFIX "inl" bb.bb_label \/
      ?k. k < ist.is_inline_count /\ isPREFIX (inline_prefix k) bb.bb_label)
      caller.fn_blocks /\
    EVERY (\bb. ~isPREFIX "inl" bb.bb_label \/
      ?k. k < ist.is_inline_count /\ isPREFIX (inline_prefix k) bb.bb_label)
      callee.fn_blocks /\
    inline_one_site caller callee site ist = SOME (caller',ist') ==>
    wf_function caller' /\
    EVERY (\bb. ~isPREFIX "inl" bb.bb_label \/
      ?k. k < ist'.is_inline_count /\ isPREFIX (inline_prefix k) bb.bb_label)
      caller'.fn_blocks /\
    ist'.is_inline_count = SUC ist.is_inline_count
Proof
  rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT (fn_ir_inst_ids caller')` by
    (qspecl_then [`caller`, `callee`, `site`, `ist`, `caller'`, `ist'`, `[]`]
       mp_tac inline_one_site_ids >>
     gvs[wf_function_def, inliner_fn_ids_distinct]) >>
  qpat_x_assum `inline_one_site _ _ _ _ = _` mp_tac >>
  simp_tac (srw_ss() -* ["string"]) [inline_one_site_def, LET_THM] >>
  Cases_on `find_invoke_site callee.fn_name site caller.fn_blocks 0` >>
  simp[Excl "isPREFIX", Excl "isPREFIX_def"] >>
  PairCases_on `x` >>
  drule find_invoke_site_indices >> simp[Excl "isPREFIX", Excl "isPREFIX_def"] >>
  strip_tac >>
  pairarg_tac >>
  rename1 `inline_call_site _ _ _ _ _ b i = (next,spliced)` >>
  qabbrev_tac `p = inline_prefix ist.is_inline_count` >>
  qabbrev_tac `r = return_block_label p ist.is_label_counter` >>
  qspecl_then [`caller`,`callee`,`p`,`r`,`ist.is_next_inst_id`,`b`,`i`] mp_tac
    inline_call_site_blocks_well_formed >>
  qspecl_then [`caller`,`callee`,`p`,`r`,`ist.is_next_inst_id`,`b`,`i`] mp_tac
    inline_call_site_succs_closed >>
  qspecl_then [`caller`,`callee`,`p`,`r`,`ist.is_next_inst_id`,`b`,`i`] mp_tac
    inline_call_site_labels >>
  qspecl_then [`caller`,`callee`,`ist.is_inline_count`,`ist.is_label_counter`,
    `ist.is_next_inst_id`,`b`,`i`] mp_tac inline_call_site_labels_distinct >>
  qspecl_then [`caller`,`callee`,`ist.is_inline_count`,`ist.is_label_counter`,
    `ist.is_next_inst_id`,`b`,`i`] mp_tac inline_call_site_label_bound >>
  qpat_x_assum `Abbrev (p = _)`
    (assume_tac o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_x_assum `Abbrev (r = _)`
    (assume_tac o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  asm_simp_tac (srw_ss() -* ["string"]) [] >>
  rpt strip_tac >>
  `fn_has_entry spliced` by
    (qpat_x_assum `fn_labels spliced = _` mp_tac >>
     Cases_on `spliced.fn_blocks` >> simp[fn_has_entry_def, fn_labels_def]) >>
  Cases_on `lookup_block r spliced.fn_blocks` >>
  gvs[wf_function_def, inliner_fn_ids_distinct, fix_inline_phis_structure,
      fix_inline_phis_ids, GSYM EVERY_MEM,
      Excl "isPREFIX", Excl "isPREFIX_def"] >>
  fs[ADD1] >>
  rename1 `lookup_block _ _.fn_blocks = SOME ret` >>
  qspecl_then [`fix_inline_phis (EL b caller.fn_blocks).bb_label
      (return_block_label (inline_prefix ist.is_inline_count) ist.is_label_counter)
      ret spliced`,
    `spliced`, `\l. ~isPREFIX "inl" l \/
      ?k. k < SUC ist.is_inline_count /\ isPREFIX (inline_prefix k) l`]
    mp_tac fn_labels_every_cong >>
  simp[fix_inline_phis_structure, ADD1]
QED

Theorem inline_blocks_bound_mono:
  !bbs n m. n <= m /\
    EVERY (\b. ~isPREFIX "inl" b.bb_label \/
      ?k. k < n /\ isPREFIX (inline_prefix k) b.bb_label) bbs ==>
    EVERY (\b. ~isPREFIX "inl" b.bb_label \/
      ?k. k < m /\ isPREFIX (inline_prefix k) b.bb_label) bbs
Proof
  rpt gen_tac >> pure_rewrite_tac[EVERY_MEM] >> BETA_TAC >>
  metis_tac[inline_label_bound_mono]
QED

Theorem inline_functions_bound_mono[local]:
  !fns n m. n <= m /\
    EVERY (\f. EVERY (\b. ~isPREFIX "inl" b.bb_label \/
      ?k. k < n /\ isPREFIX (inline_prefix k) b.bb_label) f.fn_blocks) fns ==>
    EVERY (\f. EVERY (\b. ~isPREFIX "inl" b.bb_label \/
      ?k. k < m /\ isPREFIX (inline_prefix k) b.bb_label) f.fn_blocks) fns
Proof
  rpt gen_tac >> pure_rewrite_tac[EVERY_MEM] >> BETA_TAC >>
  metis_tac[inline_label_bound_mono]
QED

Theorem all_distinct_append_swap[local]:
  !xs ys zs. ALL_DISTINCT (xs ++ ys ++ zs) <=>
             ALL_DISTINCT (ys ++ xs ++ zs)
Proof
  simp[ALL_DISTINCT_APPEND, MEM_APPEND] >> metis_tac[]
QED

Theorem inline_at_site_ids[local]:
  !fns reachable callee site ist fns' ist' rest.
    EVERY (\id. id < ist.is_next_inst_id) (FLAT (MAP fn_ir_inst_ids fns) ++ rest) /\
    inline_at_site reachable callee site fns ist = (fns',ist') ==>
    ist.is_next_inst_id <= ist'.is_next_inst_id /\
    EVERY (\id. id < ist'.is_next_inst_id) (FLAT (MAP fn_ir_inst_ids fns') ++ rest) /\
    (ALL_DISTINCT (FLAT (MAP fn_ir_inst_ids fns) ++ rest) ==>
     ALL_DISTINCT (FLAT (MAP fn_ir_inst_ids fns') ++ rest))
Proof
  Induct_on `fns` >- simp[inline_at_site_def] >>
  rpt gen_tac >> simp[Once inline_at_site_def] >>
  Cases_on `if MEM h.fn_name reachable' then
              inline_one_site h callee site ist else NONE`
  >- (pairarg_tac >> strip_tac >> gvs[] >>
      first_x_assum (qspecl_then [`reachable'`, `callee`, `site`, `ist`,
        `rest'`, `ist'`, `fn_ir_inst_ids h ++ rest`] mp_tac) >>
      simp[EVERY_APPEND] >>
      metis_tac[all_distinct_append_swap, APPEND_ASSOC]) >>
  PairCases_on `x` >> strip_tac >> gvs[AllCaseEqs()] >>
  qspecl_then [`h`,`callee`,`site`,`ist`,`x0`,`ist'`,
    `FLAT (MAP fn_ir_inst_ids fns) ++ rest`] mp_tac inline_one_site_ids >>
  simp[]
QED

Theorem inline_at_site_wf[local]:
  !fns reachable callee site ist fns' ist'.
    EVERY (\id. id < ist.is_next_inst_id) (FLAT (MAP fn_ir_inst_ids fns)) /\
    EVERY wf_function (callee::fns) /\
    EVERY (\f. EVERY (\b. ~isPREFIX "inl" b.bb_label \/
      ?k. k < ist.is_inline_count /\ isPREFIX (inline_prefix k) b.bb_label)
      f.fn_blocks) (callee::fns) /\
    inline_at_site reachable callee site fns ist = (fns',ist') ==>
    EVERY wf_function (callee::fns') /\
    EVERY (\f. EVERY (\b. ~isPREFIX "inl" b.bb_label \/
      ?k. k < ist'.is_inline_count /\ isPREFIX (inline_prefix k) b.bb_label)
      f.fn_blocks) (callee::fns') /\
    ist.is_inline_count <= ist'.is_inline_count
Proof
  Induct_on `fns` >- simp[inline_at_site_def] >>
  rpt gen_tac >> simp[Once inline_at_site_def, EVERY_APPEND] >>
  Cases_on `if MEM h.fn_name reachable' then
              inline_one_site h callee site ist else NONE`
  >- (pairarg_tac >> strip_tac >> gvs[] >>
      first_x_assum drule_all >> strip_tac >> simp[] >>
      qspecl_then [`h.fn_blocks`,`ist.is_inline_count`,`ist'.is_inline_count`]
        mp_tac inline_blocks_bound_mono >>
      simp[]) >>
  PairCases_on `x` >> strip_tac >> gvs[AllCaseEqs()] >>
  drule_all (SIMP_RULE (srw_ss()) [] inline_one_site_structure) >>
  strip_tac >> simp[] >>
  conj_tac
  >- (irule (SIMP_RULE (srw_ss()) [] inline_blocks_bound_mono) >>
      metis_tac[LESS_EQ_SUC_REFL]) >>
  irule (SIMP_RULE (srw_ss()) [] inline_functions_bound_mono) >>
  metis_tac[LESS_EQ_SUC_REFL]
QED

Theorem inline_candidate_fold_invariants[local]:
  !sites fns reachable callee ist fns' ist'.
    EVERY (\id. id < ist.is_next_inst_id) (FLAT (MAP fn_ir_inst_ids fns)) /\
    FOLDL (\(fns,st) site. inline_at_site reachable callee site.inst_id fns st)
      (fns,ist) sites = (fns',ist') ==>
    EVERY (\id. id < ist'.is_next_inst_id) (FLAT (MAP fn_ir_inst_ids fns')) /\
    (ALL_DISTINCT (FLAT (MAP fn_ir_inst_ids fns)) ==>
     ALL_DISTINCT (FLAT (MAP fn_ir_inst_ids fns'))) /\
    (EVERY wf_function (callee::fns) /\
     EVERY (\f. EVERY (\b. ~isPREFIX "inl" b.bb_label \/
       ?k. k < ist.is_inline_count /\ isPREFIX (inline_prefix k) b.bb_label)
       f.fn_blocks) (callee::fns) ==>
     EVERY wf_function (callee::fns') /\
     EVERY (\f. EVERY (\b. ~isPREFIX "inl" b.bb_label \/
       ?k. k < ist'.is_inline_count /\ isPREFIX (inline_prefix k) b.bb_label)
       f.fn_blocks) (callee::fns'))
Proof
  Induct_on `sites` >- (simp[] >> metis_tac[]) >>
  rpt gen_tac >> simp[Once FOLDL] >>
  Cases_on `inline_at_site reachable' callee h.inst_id fns ist` >>
  rename1 `inline_at_site _ _ _ _ _ = (mid,st)` >>
  strip_tac >>
  qspecl_then [`fns`,`reachable'`,`callee`,`h.inst_id`,`ist`,`mid`,`st`,`[]`]
    mp_tac inline_at_site_ids >>
  simp[] >> strip_tac >>
  first_x_assum (qspecl_then [`mid`,`reachable'`,`callee`,`st`,`fns'`,`ist'`] mp_tac) >>
  simp[] >> strip_tac >> simp[] >>
  qspecl_then [`fns`,`reachable'`,`callee`,`h.inst_id`,`ist`,`mid`,`st`]
    mp_tac inline_at_site_wf >>
  simp[] >> metis_tac[]
QED

Theorem inliner_ids_filter[local]:
  !fns P.
    (!id. MEM id (FLAT (MAP fn_ir_inst_ids (FILTER P fns))) ==>
          MEM id (FLAT (MAP fn_ir_inst_ids fns))) /\
    (ALL_DISTINCT (FLAT (MAP fn_ir_inst_ids fns)) ==>
     ALL_DISTINCT (FLAT (MAP fn_ir_inst_ids (FILTER P fns))))
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `P h` >> simp[ALL_DISTINCT_APPEND, MEM_APPEND] >> metis_tac[]
QED

Theorem function_inliner_round_invariants[local]:
  !ctx walk threshold ist ctx' walk' ist'.
    EVERY (\id. id < ist.is_next_inst_id) (FLAT (MAP fn_ir_inst_ids ctx.ctx_functions)) /\
    function_inliner_round ctx walk threshold ist = SOME (ctx',walk',ist') ==>
    EVERY (\id. id < ist'.is_next_inst_id) (FLAT (MAP fn_ir_inst_ids ctx'.ctx_functions)) /\
    (ctx_inst_ids_distinct ctx ==> ctx_inst_ids_distinct ctx') /\
    (EVERY wf_function ctx.ctx_functions /\
     EVERY (\f. EVERY (\b. ~isPREFIX "inl" b.bb_label \/
       ?k. k < ist.is_inline_count /\ isPREFIX (inline_prefix k) b.bb_label)
       f.fn_blocks) ctx.ctx_functions ==>
     EVERY wf_function ctx'.ctx_functions /\
     EVERY (\f. EVERY (\b. ~isPREFIX "inl" b.bb_label \/
       ?k. k < ist'.is_inline_count /\ isPREFIX (inline_prefix k) b.bb_label)
       f.fn_blocks) ctx'.ctx_functions)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `function_inliner_round _ _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [function_inliner_round_def, LET_THM] >>
  Cases_on `select_inline_candidate ctx (fcg_analyze ctx) threshold walk` >>
  simp[] >> Cases_on `lookup_function x ctx.ctx_functions` >> simp[] >>
  drule lookup_function_MEM >> strip_tac >>
  simp[inline_candidate_def] >>
  Cases_on `FOLDL
    (\(fns,st) site. inline_at_site (fcg_analyze ctx).fcg_reachable
      x' site.inst_id fns st)
    (ctx.ctx_functions,ist) (fcg_get_call_sites (fcg_analyze ctx) x'.fn_name)` >>
  rename1 `FOLDL (\(fns,st) site. inline_at_site _ _ site.inst_id fns st)
    (ctx.ctx_functions,ist) _ = (mid,st)` >>
  qspecl_then [`fcg_get_call_sites (fcg_analyze ctx) (x'.fn_name)`,
    `ctx.ctx_functions`,`(fcg_analyze ctx).fcg_reachable`,`x'`,`ist`,`mid`,`st`]
    mp_tac inline_candidate_fold_invariants >>
  simp[] >> strip_tac >>
  strip_tac >> gvs[remove_function_def] >>
  simp[inliner_ctx_ids_distinct] >>
  conj_tac >- (gvs[EVERY_MEM] >> metis_tac[inliner_ids_filter]) >>
  conj_tac >- metis_tac[inliner_ids_filter] >>
  strip_tac >>
  qpat_x_assum `_ ==> EVERY wf_function _ /\ _` mp_tac >>
  fs[EVERY_MEM, MEM_FILTER] >> metis_tac[]
QED

Theorem function_inliner_loop_invariants[local]:
  !fuel ctx walk threshold ist.
    EVERY (\id. id < ist.is_next_inst_id) (FLAT (MAP fn_ir_inst_ids ctx.ctx_functions)) ==>
    (ctx_inst_ids_distinct ctx ==>
     ctx_inst_ids_distinct (function_inliner_loop fuel ctx walk threshold ist)) /\
    (EVERY wf_function ctx.ctx_functions /\
     EVERY (\f. EVERY (\b. ~isPREFIX "inl" b.bb_label \/
       ?k. k < ist.is_inline_count /\ isPREFIX (inline_prefix k) b.bb_label)
       f.fn_blocks) ctx.ctx_functions ==>
     EVERY wf_function
       (function_inliner_loop fuel ctx walk threshold ist).ctx_functions)
Proof
  Induct_on `fuel` >- simp[function_inliner_loop_def] >>
  rpt gen_tac >> strip_tac >>
  simp_tac (srw_ss()) [function_inliner_loop_def] >>
  Cases_on `function_inliner_round ctx walk threshold ist` >- simp[] >>
  PairCases_on `x` >> simp[] >>
  drule_all (SIMP_RULE (srw_ss()) [] function_inliner_round_invariants) >>
  strip_tac >>
  first_x_assum (qspecl_then [`x0`,`x1`,`threshold`,`x2`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem inliner_initial_id_bound[local]:
  !ids n.
    EVERY (\id. id < FOLDL (\n id. MAX n (SUC id)) n ids) ids /\
    n <= FOLDL (\n id. MAX n (SUC id)) n ids
Proof
  Induct_on `ids` >- simp[] >> rpt gen_tac >>
  first_x_assum (qspec_then `MAX n (SUC h)` strip_assume_tac) >>
  simp[] >> fs[MAX_DEF] >> decide_tac
QED

Theorem function_inliner_ctx_invariants:
  !ctx threshold.
    (ctx_inst_ids_distinct ctx ==>
     ctx_inst_ids_distinct (function_inliner_ctx threshold ctx)) /\
    (EVERY wf_function ctx.ctx_functions /\
     EVERY (\func. EVERY (\bb. ~isPREFIX "inl" bb.bb_label) func.fn_blocks)
       ctx.ctx_functions ==>
     EVERY wf_function (function_inliner_ctx threshold ctx).ctx_functions)
Proof
  rpt gen_tac >>
  simp_tac (srw_ss() -* ["string"]) [function_inliner_ctx_def, LET_THM] >>
  qspecl_then [`LENGTH ctx.ctx_functions`, `ctx`,
    `case ctx.ctx_entry of NONE => [] | SOME entry => build_call_walk (fcg_analyze ctx) entry`,
    `threshold`,
    `<| is_inline_count := 0; is_label_counter := 0;
        is_next_inst_id := FOLDL (\n id. MAX n (SUC id)) 0
          (FLAT (MAP fn_ir_inst_ids ctx.ctx_functions)) |>`]
    mp_tac function_inliner_loop_invariants >>
  simp[inliner_initial_id_bound]
QED
