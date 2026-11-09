(* Exact raw one-site layout, before PHI repair and renumbering. *)
Theory functionInlinerSiteLayout
Ancestors
  functionInlinerDefs functionInlinerWf cfgTransformProps cfgTransform
  venomInst list rich_list pred_set

Theorem rewrite_inline_blocks_map:
  !bbs args outs r k.
    FST (rewrite_inline_blocks args outs r bbs k) =
    MAP (\bb. FST (rewrite_inline_block args outs r bb k)) bbs
Proof
  Induct >> simp[rewrite_inline_blocks_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[]) >>
  first_x_assum (qspecl_then [`args`, `outs`, `r`, `k`] mp_tac) >>
  simp[]
QED

Theorem rewrite_inline_block_label[simp]:
  (FST (rewrite_inline_block args outs r bb k)).bb_label = bb.bb_label
Proof
  simp[rewrite_inline_block_def] >> pairarg_tac >> simp[]
QED

Theorem rewrite_inline_blocks_lookup:
  !bbs args outs r k l.
    lookup_block l (FST (rewrite_inline_blocks args outs r bbs k)) =
    OPTION_MAP (\bb. FST (rewrite_inline_block args outs r bb k))
      (lookup_block l bbs)
Proof
  simp[rewrite_inline_blocks_map] >> Induct >>
  simp[lookup_block_def, FIND_thm] >> rpt gen_tac >>
  Cases_on `h.bb_label = l` >> gvs[lookup_block_def]
QED

Theorem inline_clone_lookup:
  !bbs p labels l.
    lookup_block (STRCAT p l) (MAP (clone_basic_block p labels) bbs) =
    OPTION_MAP (clone_basic_block p labels) (lookup_block l bbs)
Proof
  Induct >> simp[lookup_block_def, FIND_thm, clone_basic_block_def] >>
  rpt gen_tac >> Cases_on `h.bb_label = l` >>
  gvs[lookup_block_def, clone_basic_block_def]
QED

Theorem inline_call_site_lookup_call:
  lookup_block lbl caller.fn_blocks = SOME bb ==>
  lookup_block lbl (inline_call_site p r caller callee lbl i).fn_blocks =
    SOME (bb with bb_instructions := TAKE i bb.bb_instructions ++
      [<|inst_id := 0; inst_opcode := JMP;
         inst_operands := [Label (case (clone_function p callee).fn_blocks of
           [] => "" | eb::_ => eb.bb_label)]; inst_outputs := []|>])
Proof
  strip_tac >> drule venomExecPropsTheory.lookup_block_label >> strip_tac >>
  simp[inline_call_site_def] >> pairarg_tac >>
  qmatch_goalsub_abbrev_tac `replace_block lbl trunc caller.fn_blocks` >>
  `lookup_block lbl (replace_block lbl trunc caller.fn_blocks) = SOME trunc` by
    (irule lookup_block_replace_eq >> simp[Abbr `trunc`] >> metis_tac[]) >>
  gvs[lookup_block_def, callLayoutDefsTheory.FIND_APPEND_CASE, Abbr `trunc`]
QED

Theorem inline_call_site_lookup_return:
  lookup_block lbl caller.fn_blocks = SOME bb /\
  ~MEM r (fn_labels caller) ==>
  lookup_block r (inline_call_site p r caller callee lbl i).fn_blocks =
    SOME <|bb_label := r; bb_instructions := DROP (i+1) bb.bb_instructions|>
Proof
  strip_tac >> drule venomExecPropsTheory.lookup_block_label >> strip_tac >>
  `lookup_block r caller.fn_blocks = NONE` by
    (Cases_on `lookup_block r caller.fn_blocks` >> simp[] >>
     metis_tac[venomExecPropsTheory.lookup_block_MEM,
       venomExecPropsTheory.lookup_block_label, fn_labels_def, MEM_MAP]) >>
  `r <> lbl` by
    (metis_tac[venomExecPropsTheory.lookup_block_MEM, fn_labels_def, MEM_MAP]) >>
  simp[inline_call_site_def] >> pairarg_tac >>
  qmatch_goalsub_abbrev_tac `replace_block lbl trunc caller.fn_blocks` >>
  `lookup_block r (replace_block lbl trunc caller.fn_blocks) = NONE` by
    (simp[lookup_block_replace_neq, Abbr `trunc`]) >>
  gvs[lookup_block_def, callLayoutDefsTheory.FIND_APPEND_CASE, FIND_thm]
QED

Theorem inline_call_site_lookup_clone:
  lookup_block lbl caller.fn_blocks = SOME bb /\
  lookup_block cl callee.fn_blocks = SOME cb /\
  ~MEM (STRCAT p cl) (fn_labels caller) /\ STRCAT p cl <> r ==>
  lookup_block (STRCAT p cl)
    (inline_call_site p r caller callee lbl i).fn_blocks =
  SOME (FST (rewrite_inline_block
    (rotate_invoke_ops (EL i bb.bb_instructions).inst_operands)
    (EL i bb.bb_instructions).inst_outputs r
    (clone_basic_block p (fn_labels callee) cb) 0))
Proof
  strip_tac >> drule venomExecPropsTheory.lookup_block_label >> strip_tac >>
  `bb.bb_label = lbl` by metis_tac[venomExecPropsTheory.lookup_block_label] >>
  `lookup_block (STRCAT p cl) caller.fn_blocks = NONE` by
    (Cases_on `lookup_block (STRCAT p cl) caller.fn_blocks` >> simp[] >>
     metis_tac[venomExecPropsTheory.lookup_block_MEM,
       venomExecPropsTheory.lookup_block_label, fn_labels_def, MEM_MAP]) >>
  `STRCAT p cl <> lbl` by
    (metis_tac[venomExecPropsTheory.lookup_block_MEM, fn_labels_def, MEM_MAP]) >>
  simp[inline_call_site_def, pairTheory.UNCURRY] >>
  qmatch_goalsub_abbrev_tac `replace_block lbl trunc caller.fn_blocks` >>
  `lookup_block (STRCAT p cl) (replace_block lbl trunc caller.fn_blocks) = NONE` by
    (simp[lookup_block_replace_neq, Abbr `trunc`]) >>
  fs[lookup_block_def] >>
  simp[callLayoutDefsTheory.FIND_APPEND_CASE, FIND_thm] >>
  rewrite_tac[GSYM lookup_block_def] >>
  simp[rewrite_inline_blocks_lookup, clone_function_def] >>
  simp[inline_clone_lookup] >> simp[lookup_block_def]
QED

Theorem inline_call_site_lookup_other:
  lookup_block lbl caller.fn_blocks = SOME bb /\
  lookup_block l caller.fn_blocks = SOME old /\ l <> lbl ==>
  lookup_block l (inline_call_site p r caller callee lbl i).fn_blocks = SOME old
Proof
  strip_tac >> drule venomExecPropsTheory.lookup_block_label >> strip_tac >>
  `bb.bb_label = lbl` by metis_tac[venomExecPropsTheory.lookup_block_label] >>
  simp[inline_call_site_def, pairTheory.UNCURRY] >>
  qmatch_goalsub_abbrev_tac `replace_block lbl trunc caller.fn_blocks` >>
  `lookup_block l (replace_block lbl trunc caller.fn_blocks) = SOME old` by
    simp[lookup_block_replace_neq, Abbr `trunc`] >>
  gvs[lookup_block_def, callLayoutDefsTheory.FIND_APPEND_CASE]
QED

Theorem inline_call_site_prefix_getter:
  lookup_block lbl caller.fn_blocks = SOME bb /\
  lookup_block lbl (inline_call_site p r caller callee lbl i).fn_blocks = SOME tb /\
  i <= LENGTH bb.bb_instructions /\ k < i ==>
  k < LENGTH tb.bb_instructions /\
  EL k tb.bb_instructions = EL k bb.bb_instructions
Proof
  strip_tac >> rev_drule inline_call_site_lookup_call >>
  disch_then (qspecl_then [`r`, `p`, `i`, `callee`] mp_tac) >>
  strip_tac >> gvs[] >> simp[EL_APPEND1, EL_TAKE]
QED

Theorem inline_call_site_return_getter:
  lookup_block lbl caller.fn_blocks = SOME bb /\
  ~MEM r (fn_labels caller) /\
  lookup_block r (inline_call_site p r caller callee lbl i).fn_blocks = SOME rb /\
  k < LENGTH bb.bb_instructions - (i+1) ==>
  k < LENGTH rb.bb_instructions /\
  EL k rb.bb_instructions = EL (i+1+k) bb.bb_instructions
Proof
  strip_tac >> drule_all inline_call_site_lookup_return >>
  disch_then (qspecl_then [`p`, `i`, `callee`] mp_tac) >>
  strip_tac >> gvs[] >> simp[EL_DROP]
QED
