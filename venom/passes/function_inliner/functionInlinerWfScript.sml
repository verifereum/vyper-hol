Theory functionInlinerWf
Ancestors
  functionInlinerDefs ASCIInumbers rich_list string arithmetic list
  venomInst venomState venomWf venomExecProofs
  simplifyCfgLocalShape simplifyCfgGraphShape simplifyCfgStruct cfgTransform cfgTransformProps cfgTransformProofs fmpStepChunk fmpStepList indexedLists passSimulationProps


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

Theorem find_invoke_idx_bounds:
  !insts name n i. find_invoke_idx name insts n = SOME i ==>
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

Theorem find_invoke_site_member:
  !bbs name lbl i. find_invoke_site name bbs = SOME (lbl,i) ==>
    ?bb. MEM bb bbs /\ bb.bb_label = lbl /\
      i < LENGTH bb.bb_instructions /\
      (EL i bb.bb_instructions).inst_opcode = INVOKE
Proof
  Induct_on `bbs` >- simp[find_invoke_site_def] >>
  rpt gen_tac >> simp[Once find_invoke_site_def] >>
  Cases_on `find_invoke_idx name h.bb_instructions 0`
  >- (simp[] >> metis_tac[]) >>
  simp[] >> strip_tac >> gvs[] >>
  drule find_invoke_idx_bounds >> simp[] >> metis_tac[]
QED

Theorem find_invoke_site_lookup:
  !f name lbl i.
    ALL_DISTINCT (fn_labels f) /\
    find_invoke_site name f.fn_blocks = SOME (lbl,i) ==>
    ?bb. lookup_block lbl f.fn_blocks = SOME bb /\
      i < LENGTH bb.bb_instructions /\
      (EL i bb.bb_instructions).inst_opcode = INVOKE
Proof
  rpt strip_tac >> drule find_invoke_site_member >> strip_tac >>
  gvs[fn_labels_def] >> metis_tac[MEM_lookup_block]
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
  rpt strip_tac >> gvs[EL_DROP] >>
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

Theorem renumber_blocks_fold_structure[local]:
  !bbs n acc n' res.
    FOLDL (\(n,acc) bb.
      let (n',bb') = renumber_block_inst_ids n bb in (n',acc ++ [bb']))
      (n,acc) bbs = (n',res) ==>
    MAP (\bb. (bb.bb_label, bb_succs bb)) res =
      MAP (\bb. (bb.bb_label, bb_succs bb)) (acc ++ bbs) /\
    (EVERY bb_well_formed (acc ++ bbs) ==> EVERY bb_well_formed res)
Proof
  Induct_on `bbs` >- simp[] >>
  rpt gen_tac >> simp[Once FOLDL] >>
  Cases_on `renumber_block_inst_ids n h` >> simp[] >> strip_tac >>
  gvs[LET_THM] >> first_x_assum drule >>
  qspecl_then [`n`,`h`] mp_tac renumber_block_structure >>
  simp[] >> strip_tac >>
  simp[MAP_APPEND, EVERY_APPEND, APPEND_ASSOC] >>
  metis_tac[]
QED

Theorem numbered_ids_append[local]:
  !ids n len.
    ALL_DISTINCT ids /\ EVERY (\id. id < n) ids ==>
    ALL_DISTINCT (ids ++ GENLIST (\k. n+k) len) /\
    EVERY (\id. id < n+len) (ids ++ GENLIST (\k. n+k) len)
Proof
  rpt strip_tac >>
  simp[ALL_DISTINCT_APPEND, ALL_DISTINCT_GENLIST, EVERY_APPEND,
       EVERY_MEM, MEM_GENLIST] >>
  gvs[EVERY_MEM] >> rpt strip_tac >>
  res_tac >> decide_tac
QED

Theorem renumber_blocks_fold_ids[local]:
  !bbs n acc n' res.
    FOLDL (\(n,acc) bb.
      let (n',bb') = renumber_block_inst_ids n bb in (n',acc ++ [bb']))
      (n,acc) bbs = (n',res) /\
    ALL_DISTINCT (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) acc)) /\
    EVERY (\id. id < n) (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) acc)) ==>
    ALL_DISTINCT (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) res)) /\
    EVERY (\id. id < n') (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) res))
Proof
  Induct_on `bbs` >- simp[] >>
  rpt gen_tac >> simp[Once FOLDL] >>
  Cases_on `renumber_block_inst_ids n h` >> simp[] >> strip_tac >>
  qspecl_then [`n`,`h`] mp_tac renumber_block_structure >>
  simp[] >> strip_tac >>
  drule_all numbered_ids_append >>
  disch_then (qspec_then `LENGTH h.bb_instructions` strip_assume_tac) >>
  gvs[LET_THM] >> first_x_assum irule >>
  qexistsl_tac [`acc ++ [r]`, `n + LENGTH h.bb_instructions`] >>
  simp[MAP_APPEND]
QED

Theorem renumber_fn_structure:
  !f.
    MAP (\bb. (bb.bb_label, bb_succs bb)) (renumber_fn_inst_ids f).fn_blocks =
      MAP (\bb. (bb.bb_label, bb_succs bb)) f.fn_blocks /\
    (EVERY bb_well_formed f.fn_blocks ==>
      EVERY bb_well_formed (renumber_fn_inst_ids f).fn_blocks) /\
    fn_inst_ids_distinct (renumber_fn_inst_ids f)
Proof
  gen_tac >> simp[renumber_fn_inst_ids_def] >>
  pairarg_tac >> gvs[LET_THM] >>
  drule (REWRITE_RULE [LET_THM] renumber_blocks_fold_structure) >> simp[] >> strip_tac >>
  drule_at (Pos (el 1)) (REWRITE_RULE [LET_THM] renumber_blocks_fold_ids) >>
  simp[fn_inst_ids_distinct_def]
QED

Theorem renumber_fn_labels:
  !f. fn_labels (renumber_fn_inst_ids f) = fn_labels f
Proof
  gen_tac >> qspec_then `f` mp_tac renumber_fn_structure >> strip_tac >>
  `MAP FST (MAP (\bb. (bb.bb_label, bb_succs bb)) (renumber_fn_inst_ids f).fn_blocks) =
   MAP FST (MAP (\bb. (bb.bb_label, bb_succs bb)) f.fn_blocks)` by simp[] >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, fn_labels_def]
QED

Theorem renumber_fn_has_entry:
  !f. fn_has_entry (renumber_fn_inst_ids f) <=> fn_has_entry f
Proof
  gen_tac >> qspec_then `f` mp_tac renumber_fn_labels >>
  simp[fn_has_entry_def, fn_labels_def] >>
  Cases_on `f.fn_blocks` >> Cases_on `(renumber_fn_inst_ids f).fn_blocks` >> simp[]
QED

Theorem renumber_fn_succs_closed:
  !f. fn_succs_closed (renumber_fn_inst_ids f) <=> fn_succs_closed f
Proof
  gen_tac >> qspec_then `f` mp_tac renumber_fn_structure >> strip_tac >>
  rewrite_tac[fn_succs_closed_def, renumber_fn_labels] >>
  `EVERY (\x. EVERY (\l. MEM l (fn_labels f)) (SND x))
     (MAP (\bb. (bb.bb_label, bb_succs bb)) (renumber_fn_inst_ids f).fn_blocks) <=>
   EVERY (\x. EVERY (\l. MEM l (fn_labels f)) (SND x))
     (MAP (\bb. (bb.bb_label, bb_succs bb)) f.fn_blocks)` by simp[] >>
  gvs[EVERY_MAP, EVERY_MEM, combinTheory.o_DEF] >> metis_tac[]
QED

Theorem renumber_fn_well_formed:
  !f. fn_has_entry f /\ ALL_DISTINCT (fn_labels f) /\
      EVERY bb_well_formed f.fn_blocks /\ fn_succs_closed f ==>
      wf_function (renumber_fn_inst_ids f)
Proof
  rpt strip_tac >>
  qspec_then `f` strip_assume_tac renumber_fn_structure >>
  simp[wf_function_def, renumber_fn_labels, renumber_fn_has_entry,
       renumber_fn_succs_closed, GSYM EVERY_MEM]
QED

Theorem inline_call_site_labels:
  !caller callee p r lbl i bb.
    lookup_block lbl caller.fn_blocks = SOME bb ==>
    fn_labels (inline_call_site p r caller callee lbl i) =
      fn_labels caller ++ [r] ++ MAP (STRCAT p) (fn_labels callee)
Proof
  rpt strip_tac >>
  drule lookup_block_label >> strip_tac >>
  simp[inline_call_site_def] >> pairarg_tac >>
  drule rewrite_inline_blocks_labels >> strip_tac >>
  simp[fn_labels_def, fn_labels_replace_block] >>
  rewrite_tac[GSYM fn_labels_def, clone_function_labels]
QED

Theorem inline_call_site_label_bound:
  !caller callee n c lbl i bb.
    lookup_block lbl caller.fn_blocks = SOME bb /\
    EVERY (\b. ~isPREFIX "inl" b.bb_label \/
      ?k. k < n /\ isPREFIX (inline_prefix k) b.bb_label) caller.fn_blocks ==>
    EVERY (\b. ~isPREFIX "inl" b.bb_label \/
      ?k. k < SUC n /\ isPREFIX (inline_prefix k) b.bb_label)
      (inline_call_site (inline_prefix n)
        (return_block_label (inline_prefix n) c) caller callee lbl i).fn_blocks
Proof
  rpt strip_tac >>
  drule inline_call_site_labels >>
  disch_then (qspecl_then [`callee`, `inline_prefix n`,
    `return_block_label (inline_prefix n) c`, `i`] mp_tac) >>
  rewrite_tac[fn_labels_def] >> strip_tac >>
  pure_rewrite_tac[EVERY_MEM] >> rpt strip_tac >>
  rename1 `MEM b (inline_call_site _ _ _ _ _ _).fn_blocks` >>
  `MEM b.bb_label
    (MAP (\bb. bb.bb_label)
      (inline_call_site (inline_prefix n) (return_block_label (inline_prefix n) c)
        caller callee lbl i).fn_blocks)` by
    (simp_tac bool_ss [MEM_MAP] >> metis_tac[]) >>
  qpat_x_assum `MAP _ _ = _` SUBST_ALL_TAC >>
  pop_assum mp_tac >>
  simp_tac bool_ss [MEM_APPEND, MEM_MAP, MEM, EVERY_MEM] >>
  rpt strip_tac >> gvs[Excl "isPREFIX"]
  >- (irule inline_label_bound_mono >> qexists_tac `n` >>
      simp_tac bool_ss [LESS_EQ_SUC_REFL] >>
      qpat_x_assum `EVERY _ _` mp_tac >>
      simp_tac bool_ss [EVERY_MEM] >> metis_tac[])
  >- MATCH_ACCEPT_TAC inline_label_bound_return >>
  MATCH_ACCEPT_TAC inline_label_bound_clone
QED

Theorem inline_call_site_blocks_well_formed:
  !caller callee p r lbl i bb.
    wf_function caller /\ wf_function callee /\
    lookup_block lbl caller.fn_blocks = SOME bb /\
    i < LENGTH bb.bb_instructions /\
    (EL i bb.bb_instructions).inst_opcode = INVOKE ==>
    EVERY bb_well_formed (inline_call_site p r caller callee lbl i).fn_blocks
Proof
  rpt strip_tac >>
  `MEM bb caller.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `bb_well_formed bb` by metis_tac[wf_function_def] >>
  `i + 1 < LENGTH bb.bb_instructions` by
    metis_tac[invoke_before_terminator] >>
  simp[inline_call_site_def] >> pairarg_tac >>
  drule_all clone_rewrite_blocks_structure >> strip_tac >>
  asm_simp_tac (srw_ss()) [EVERY_APPEND, EVERY_DEF] >>
  conj_tac
  >- (irule EVERY_replace_block >> conj_tac
      >- (irule inline_truncated_well_formed >> simp[]) >>
      qpat_x_assum `wf_function caller` mp_tac >>
      simp[wf_function_def, EVERY_MEM]) >>
  metis_tac[inline_return_well_formed]
QED

Theorem inline_call_site_labels_distinct:
  !caller callee n c lbl i bb.
    wf_function caller /\ wf_function callee /\
    lookup_block lbl caller.fn_blocks = SOME bb /\
    EVERY (\b. ~isPREFIX "inl" b.bb_label \/
      ?k. k < n /\ isPREFIX (inline_prefix k) b.bb_label) caller.fn_blocks /\
    EVERY (\b. ~isPREFIX "inl" b.bb_label \/
      ?k. k < n /\ isPREFIX (inline_prefix k) b.bb_label) callee.fn_blocks ==>
    ALL_DISTINCT (fn_labels (inline_call_site (inline_prefix n)
      (return_block_label (inline_prefix n) c) caller callee lbl i))
Proof
  rpt strip_tac >>
  drule inline_call_site_labels >>
  disch_then (qspecl_then [`callee`, `inline_prefix n`,
    `return_block_label (inline_prefix n) c`, `i`] SUBST1_TAC) >>
  `ALL_DISTINCT (fn_labels caller) /\ ALL_DISTINCT (fn_labels callee)` by
    metis_tac[wf_function_def] >>
  asm_simp_tac bool_ss [ALL_DISTINCT_APPEND, ALL_DISTINCT, MEM_APPEND, MEM,
    ALL_DISTINCT_MAP, STRCAT_11, MEM_MAP] >>
  conj_tac
  >- (strip_tac >>
      `?b. MEM b caller.fn_blocks /\
        b.bb_label = return_block_label (inline_prefix n) c` by
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
      `?b. MEM b caller.fn_blocks /\ b.bb_label = e` by
        (gvs[fn_labels_def, MEM_MAP] >> metis_tac[]) >>
      qpat_x_assum `EVERY _ caller.fn_blocks` mp_tac >>
      pure_rewrite_tac[EVERY_MEM] >> BETA_TAC >> strip_tac >>
      first_x_assum drule >>
      disch_then (mp_tac o MATCH_MP inline_label_bound_fresh) >>
      asm_simp_tac bool_ss [isPREFIX_STRCAT, STRCAT_11]) >>
  rpt strip_tac >>
  `?b. MEM b callee.fn_blocks /\ b.bb_label = y` by
    (gvs[fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  qpat_x_assum `EVERY _ callee.fn_blocks` mp_tac >>
  pure_rewrite_tac[EVERY_MEM] >> BETA_TAC >> strip_tac >>
  first_x_assum drule >>
  disch_then (mp_tac o MATCH_MP inline_return_clone_distinct) >>
  metis_tac[]
QED

Theorem inline_call_site_succs_closed:
  !caller callee p r lbl i bb.
    wf_function caller /\ wf_function callee /\
    lookup_block lbl caller.fn_blocks = SOME bb /\
    i < LENGTH bb.bb_instructions /\
    (EL i bb.bb_instructions).inst_opcode = INVOKE ==>
    fn_succs_closed (inline_call_site p r caller callee lbl i)
Proof
  rpt strip_tac >>
  `MEM bb caller.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `bb_well_formed bb` by metis_tac[wf_function_def] >>
  `i + 1 < LENGTH bb.bb_instructions` by
    metis_tac[invoke_before_terminator] >>
  `bb.bb_label = lbl` by metis_tac[lookup_block_label] >>
  `callee.fn_blocks <> []` by
    metis_tac[wf_function_def, fn_has_entry_def] >>
  simp[inline_call_site_def] >> pairarg_tac >>
  drule_all clone_rewrite_blocks_structure >> strip_tac >>
  qmatch_goalsub_abbrev_tac `replace_block lbl trunc _` >>
  qmatch_goalsub_abbrev_tac `[retbb]` >>
  `MAP (\b. b.bb_label) (replace_block lbl trunc caller.fn_blocks) =
    fn_labels caller` by
    (simp[Abbr `trunc`, fn_labels_replace_block, fn_labels_def]) >>
  `bb_succs retbb = bb_succs bb` by
    (simp[Abbr `retbb`, inline_return_succs]) >>
  `bb_succs trunc = [STRCAT p (HD callee.fn_blocks).bb_label]` by
    (Cases_on `callee.fn_blocks` >- gvs[] >>
     Cases_on `TAKE i bb.bb_instructions` >>
     simp[Abbr `trunc`, clone_function_def, clone_basic_block_def,
       bb_succs_def, LAST_APPEND_CONS, LAST_CONS_cond, LAST_APPEND, get_successors_def,
       is_terminator_def, get_label_def, nub_def]) >>
  asm_simp_tac (srw_ss()) [fn_succs_closed_def, fn_labels_def, MAP_APPEND, MAP] >>
  rpt strip_tac
  >- (qpat_x_assum `MEM _ (replace_block _ _ _)` mp_tac >>
      simp_tac bool_ss [replace_block_def, MEM_MAP] >>
      strip_tac >> rename1 `MEM old caller.fn_blocks` >>
      Cases_on `old.bb_label = lbl` >> gvs[]
      >- (disj2_tac >> simp[MEM_MAP, fn_labels_def] >>
          qexists_tac `HD callee.fn_blocks` >>
          Cases_on `callee.fn_blocks` >> gvs[]) >>
      disj1_tac >> disj1_tac >>
      qpat_x_assum `wf_function caller` mp_tac >>
      simp[wf_function_def, fn_succs_closed_def, fn_labels_def, MEM_MAP] >>
      metis_tac[]) 
  >- (disj1_tac >> disj1_tac >>
      qpat_x_assum `wf_function caller` mp_tac >>
      gvs[wf_function_def, fn_succs_closed_def, fn_labels_def] >>
      metis_tac[]) >>
  qpat_x_assum `!bb l. _` drule >>
  disch_then drule >> strip_tac
  >- simp[Abbr `retbb`] >>
  disj2_tac >> simp[MEM_MAP] >>
  qpat_x_assum `MEM k (fn_labels callee)` mp_tac >>
  simp[fn_labels_def, MEM_MAP]
QED

Theorem inline_call_site_has_entry:
  !caller callee p r lbl i bb.
    lookup_block lbl caller.fn_blocks = SOME bb ==>
    fn_has_entry (inline_call_site p r caller callee lbl i)
Proof
  rpt strip_tac >> drule inline_call_site_labels >>
  disch_then (qspecl_then [`callee`, `p`, `r`, `i`] mp_tac) >>
  simp[fn_has_entry_def, fn_labels_def] >>
  Cases_on `(inline_call_site p r caller callee lbl i).fn_blocks` >> simp[]
QED

Theorem inline_call_site_structure:
  !caller callee n c lbl i bb.
    wf_function caller /\ wf_function callee /\
    lookup_block lbl caller.fn_blocks = SOME bb /\
    i < LENGTH bb.bb_instructions /\
    (EL i bb.bb_instructions).inst_opcode = INVOKE /\
    EVERY (\b. ~isPREFIX "inl" b.bb_label \/
      ?k. k < n /\ isPREFIX (inline_prefix k) b.bb_label) caller.fn_blocks /\
    EVERY (\b. ~isPREFIX "inl" b.bb_label \/
      ?k. k < n /\ isPREFIX (inline_prefix k) b.bb_label) callee.fn_blocks ==>
    fn_has_entry (inline_call_site (inline_prefix n)
      (return_block_label (inline_prefix n) c) caller callee lbl i) /\
    ALL_DISTINCT (fn_labels (inline_call_site (inline_prefix n)
      (return_block_label (inline_prefix n) c) caller callee lbl i)) /\
    EVERY bb_well_formed (inline_call_site (inline_prefix n)
      (return_block_label (inline_prefix n) c) caller callee lbl i).fn_blocks /\
    fn_succs_closed (inline_call_site (inline_prefix n)
      (return_block_label (inline_prefix n) c) caller callee lbl i)
Proof
  rpt gen_tac >> strip_tac >>
  conj_tac >- (irule inline_call_site_has_entry >> metis_tac[]) >>
  conj_tac >- (irule inline_call_site_labels_distinct >> metis_tac[]) >>
  conj_tac >- (irule inline_call_site_blocks_well_formed >> metis_tac[]) >>
  irule inline_call_site_succs_closed >> metis_tac[]
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

Theorem inline_one_site_structure:
  !caller callee ist caller' ist'.
    wf_function caller /\ wf_function callee /\
    EVERY (\b. ~isPREFIX "inl" b.bb_label \/
      ?k. k < ist.is_inline_count /\ isPREFIX (inline_prefix k) b.bb_label)
      caller.fn_blocks /\
    EVERY (\b. ~isPREFIX "inl" b.bb_label \/
      ?k. k < ist.is_inline_count /\ isPREFIX (inline_prefix k) b.bb_label)
      callee.fn_blocks /\
    inline_one_site caller callee ist = SOME (caller',ist') ==>
    wf_function caller' /\
    EVERY (\b. ~isPREFIX "inl" b.bb_label \/
      ?k. k < ist'.is_inline_count /\ isPREFIX (inline_prefix k) b.bb_label)
      caller'.fn_blocks /\
    ist'.is_inline_count = SUC ist.is_inline_count
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `inline_one_site _ _ _ = _` mp_tac >>
  rewrite_tac[inline_one_site_def] >>
  Cases_on `find_invoke_site callee.fn_name caller.fn_blocks` >- simp[] >>
  PairCases_on `x` >> simp[Excl "isPREFIX"] >>
  `ALL_DISTINCT (fn_labels caller)` by metis_tac[wf_function_def] >>
  drule_all find_invoke_site_lookup >> strip_tac >>
  drule_all inline_call_site_structure >>
  disch_then (qspec_then `ist.is_label_counter` mp_tac) >>
  BETA_TAC >> strip_tac >>
  drule_all inline_call_site_label_bound >>
  disch_then (qspecl_then [`callee`, `ist.is_label_counter`, `x1`] assume_tac) >>
  qmatch_goalsub_abbrev_tac `lookup_block ret_lbl f.fn_blocks` >>
  Cases_on `lookup_block ret_lbl f.fn_blocks` >>
  asm_simp_tac (srw_ss() -* ["string"]) [] >> strip_tac >>
  gvs[Excl "isPREFIX", Excl "isPREFIX_def"]
  >- (conj_tac >- (irule renumber_fn_well_formed >> simp[]) >>
      qspec_then `f` assume_tac renumber_fn_labels >>
      drule fn_labels_every_cong >>
      disch_then (qspec_then `\l. ~isPREFIX "inl" l \/
        ?k. k < SUC ist.is_inline_count /\ isPREFIX (inline_prefix k) l` mp_tac) >>
      qpat_x_assum `EVERY (\b. ~isPREFIX _ _ \/ _) f.fn_blocks` mp_tac >>
      simp[GSYM ADD1]) >>
  qspecl_then [`x0`, `ret_lbl`, `x`, `f`] strip_assume_tac
    fix_inline_phis_structure >>
  conj_tac
  >- (irule renumber_fn_well_formed >> simp[]) >>
  `fn_labels (renumber_fn_inst_ids (fix_inline_phis x0 ret_lbl x f)) =
    fn_labels f` by simp[renumber_fn_labels] >>
  drule fn_labels_every_cong >>
  disch_then (qspec_then `\l. ~isPREFIX "inl" l \/
    ?k. k < SUC ist.is_inline_count /\ isPREFIX (inline_prefix k) l` mp_tac) >>
  qpat_x_assum `EVERY (\b. ~isPREFIX _ _ \/ _) f.fn_blocks` mp_tac >>
  simp[GSYM ADD1]
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

Theorem inline_at_sites_structure:
  !fuel caller callee ist caller' ist'.
    wf_function caller /\ wf_function callee /\
    EVERY (\b. ~isPREFIX "inl" b.bb_label \/
      ?k. k < ist.is_inline_count /\ isPREFIX (inline_prefix k) b.bb_label)
      caller.fn_blocks /\
    EVERY (\b. ~isPREFIX "inl" b.bb_label \/
      ?k. k < ist.is_inline_count /\ isPREFIX (inline_prefix k) b.bb_label)
      callee.fn_blocks /\
    inline_at_sites fuel caller callee ist = (caller',ist') ==>
    wf_function caller' /\
    EVERY (\b. ~isPREFIX "inl" b.bb_label \/
      ?k. k < ist'.is_inline_count /\ isPREFIX (inline_prefix k) b.bb_label)
      caller'.fn_blocks /\
    ist.is_inline_count <= ist'.is_inline_count
Proof
  Induct_on `fuel`
  >- (simp_tac (srw_ss()) [inline_at_sites_def] >> rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `inline_at_sites _ _ _ _ = _` mp_tac >>
  rewrite_tac[inline_at_sites_def] >>
  Cases_on `inline_one_site caller callee ist`
  >- (simp_tac (srw_ss()) [] >> strip_tac >> gvs[]) >>
  PairCases_on `x` >> simp_tac (srw_ss()) [] >> strip_tac >>
  drule_all inline_one_site_structure >> strip_tac >>
  `EVERY (\b. ~isPREFIX "inl" b.bb_label \/
      ?k. k < x1.is_inline_count /\ isPREFIX (inline_prefix k) b.bb_label)
      callee.fn_blocks` by
    (irule inline_blocks_bound_mono >> qexists_tac `ist.is_inline_count` >> simp[]) >>
  first_x_assum drule_all >> strip_tac >>
  gvs[] >> decide_tac
QED

Theorem inline_functions_bound_mono:
  !fns n m. n <= m /\
    EVERY (\f. EVERY (\b. ~isPREFIX "inl" b.bb_label \/
      ?k. k < n /\ isPREFIX (inline_prefix k) b.bb_label) f.fn_blocks) fns ==>
    EVERY (\f. EVERY (\b. ~isPREFIX "inl" b.bb_label \/
      ?k. k < m /\ isPREFIX (inline_prefix k) b.bb_label) f.fn_blocks) fns
Proof
  rpt gen_tac >> pure_rewrite_tac[EVERY_MEM] >> BETA_TAC >>
  metis_tac[inline_label_bound_mono]
QED

Theorem inline_candidate_fold_structure[local]:
  !todo done callee ist done' ist'.
    EVERY wf_function (callee::done ++ todo) /\
    EVERY (\f. EVERY (\b. ~isPREFIX "inl" b.bb_label \/
      ?k. k < ist.is_inline_count /\ isPREFIX (inline_prefix k) b.bb_label)
      f.fn_blocks) (callee::done ++ todo) /\
    FOLDL (\(fns,st) caller.
      let (caller',st') = inline_at_sites (LENGTH (fn_insts caller)) caller callee st in
      (SNOC caller' fns, st')) (done,ist) todo = (done',ist') ==>
    EVERY wf_function (callee::done') /\
    EVERY (\f. EVERY (\b. ~isPREFIX "inl" b.bb_label \/
      ?k. k < ist'.is_inline_count /\ isPREFIX (inline_prefix k) b.bb_label)
      f.fn_blocks) (callee::done') /\
    ist.is_inline_count <= ist'.is_inline_count
Proof
  Induct_on `todo`
  >- (simp_tac (srw_ss()) [FOLDL] >> rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> pure_rewrite_tac[EVERY_DEF, EVERY_APPEND] >> BETA_TAC >>
  strip_tac >>
  qpat_x_assum `FOLDL _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [FOLDL, LET_THM] >> pairarg_tac >>
  drule_all inline_at_sites_structure >> strip_tac >>
  strip_tac >>
  `EVERY (\f. EVERY (\b. ~isPREFIX "inl" b.bb_label \/
      ?k. k < st'.is_inline_count /\ isPREFIX (inline_prefix k) b.bb_label)
      f.fn_blocks) (callee::done ++ todo)` by
    (irule inline_functions_bound_mono >> qexists_tac `ist.is_inline_count` >>
     asm_simp_tac bool_ss [EVERY_DEF, EVERY_APPEND]) >>
  qpat_x_assum `EVERY _ (_::_ ++ _)` mp_tac >>
  pure_rewrite_tac[EVERY_DEF, EVERY_APPEND] >> BETA_TAC >> strip_tac >>
  qpat_x_assum `FOLDL _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [] >> strip_tac >>
  first_x_assum (qspecl_then [`SNOC caller' done`, `callee`, `st'`] mp_tac) >>
  asm_simp_tac (srw_ss()) [EVERY_DEF, EVERY_APPEND, EVERY_SNOC, LET_THM] >>
  strip_tac >> gvs[] >> decide_tac
QED

Theorem inline_candidate_structure:
  !ctx callee ist ctx' ist'.
    EVERY wf_function (callee::ctx.ctx_functions) /\
    EVERY (\f. EVERY (\b. ~isPREFIX "inl" b.bb_label \/
      ?k. k < ist.is_inline_count /\ isPREFIX (inline_prefix k) b.bb_label)
      f.fn_blocks) (callee::ctx.ctx_functions) /\
    inline_candidate ctx callee ist = (ctx',ist') ==>
    EVERY wf_function ctx'.ctx_functions /\
    EVERY (\f. EVERY (\b. ~isPREFIX "inl" b.bb_label \/
      ?k. k < ist'.is_inline_count /\ isPREFIX (inline_prefix k) b.bb_label)
      f.fn_blocks) ctx'.ctx_functions /\
    ist.is_inline_count <= ist'.is_inline_count
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `inline_candidate _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [inline_candidate_def, LET_THM] >> pairarg_tac >>
  drule_at (Pat `FOLDL _ _ _ = _`)
    (REWRITE_RULE [LET_THM] inline_candidate_fold_structure) >>
  simp_tac (srw_ss()) [EVERY_DEF] >>
  (impl_tac >- gvs[]) >> strip_tac >>
  strip_tac >> gvs[]
QED

Theorem function_inliner_round_structure:
  !ctx walk threshold ist ctx' walk' ist'.
    EVERY wf_function ctx.ctx_functions /\
    EVERY (\f. EVERY (\b. ~isPREFIX "inl" b.bb_label \/
      ?k. k < ist.is_inline_count /\ isPREFIX (inline_prefix k) b.bb_label)
      f.fn_blocks) ctx.ctx_functions /\
    function_inliner_round ctx walk threshold ist = SOME (ctx',walk',ist') ==>
    EVERY wf_function ctx'.ctx_functions /\
    EVERY (\f. EVERY (\b. ~isPREFIX "inl" b.bb_label \/
      ?k. k < ist'.is_inline_count /\ isPREFIX (inline_prefix k) b.bb_label)
      f.fn_blocks) ctx'.ctx_functions /\
    ist.is_inline_count <= ist'.is_inline_count
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `function_inliner_round _ _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [function_inliner_round_def, LET_THM] >>
  Cases_on `select_inline_candidate ctx (fcg_analyze ctx) threshold walk` >>
  simp[] >>
  Cases_on `lookup_function x ctx.ctx_functions` >> simp[] >>
  drule lookup_function_MEM >> strip_tac >>
  pairarg_tac >>
  drule_at (Pat `inline_candidate _ _ _ = _`) inline_candidate_structure >>
  (impl_tac >- (gvs[EVERY_MEM] >> metis_tac[])) >> strip_tac >>
  strip_tac >> gvs[remove_function_def, EVERY_FILTER, EVERY_MEM, MEM_FILTER] >>
  metis_tac[]
QED

Theorem function_inliner_loop_wf:
  !fuel ctx walk threshold ist.
    EVERY wf_function ctx.ctx_functions /\
    EVERY (\f. EVERY (\b. ~isPREFIX "inl" b.bb_label \/
      ?k. k < ist.is_inline_count /\ isPREFIX (inline_prefix k) b.bb_label)
      f.fn_blocks) ctx.ctx_functions ==>
    EVERY wf_function
      (function_inliner_loop fuel ctx walk threshold ist).ctx_functions
Proof
  Induct_on `fuel` >- simp[function_inliner_loop_def] >>
  rpt gen_tac >> strip_tac >>
  simp_tac (srw_ss()) [function_inliner_loop_def] >>
  Cases_on `function_inliner_round ctx walk threshold ist` >- simp[] >>
  PairCases_on `x` >> simp[] >>
  drule_all function_inliner_round_structure >> strip_tac >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[]
QED
