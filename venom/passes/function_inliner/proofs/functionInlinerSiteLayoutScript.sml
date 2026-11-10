(* Located one-site layout, with raw assembly and final semantic projections. *)
Theory functionInlinerSiteLayout
Ancestors
  functionInlinerDefs functionInlinerWf functionInlinerOrigin
  cfgTransformProps cfgTransform
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

Theorem rewrite_inline_insts_append:
  !pre args outs r rest k.
  rewrite_inline_insts args outs r (pre ++ rest) k =
    (FST (rewrite_inline_insts args outs r pre k) ++
     FST (rewrite_inline_insts args outs r rest
       (SND (rewrite_inline_insts args outs r pre k))),
     SND (rewrite_inline_insts args outs r rest
       (SND (rewrite_inline_insts args outs r pre k))))
Proof
  Induct >> simp[rewrite_inline_insts_def, pairTheory.UNCURRY] >>
  rpt gen_tac >> simp[APPEND_ASSOC]
QED

Theorem rewrite_inline_insts_focus:
  rewrite_inline_insts args outs r (pre ++ inst::post) k =
    (FST (rewrite_inline_insts args outs r pre k) ++
     FST (rewrite_inline_inst args outs r inst
       (SND (rewrite_inline_insts args outs r pre k))) ++
     FST (rewrite_inline_insts args outs r post
       (SND (rewrite_inline_inst args outs r inst
         (SND (rewrite_inline_insts args outs r pre k))))),
     SND (rewrite_inline_insts args outs r post
       (SND (rewrite_inline_inst args outs r inst
         (SND (rewrite_inline_insts args outs r pre k))))))
Proof
  simp[rewrite_inline_insts_append, rewrite_inline_insts_def, pairTheory.UNCURRY]
QED

Theorem inline_call_site_lookup_clone_focus:
  lookup_block lbl caller.fn_blocks = SOME bb /\
  lookup_block cl callee.fn_blocks = SOME cb /\
  ~MEM (STRCAT p cl) (fn_labels caller) /\ STRCAT p cl <> r /\
  cb.bb_instructions = pre ++ inst::post ==>
  let args = rotate_invoke_ops (EL i bb.bb_instructions).inst_operands;
      outs = (EL i bb.bb_instructions).inst_outputs;
      labs = fn_labels callee;
      a = rewrite_inline_insts args outs r (MAP (clone_instruction p labs) pre) 0;
      b = rewrite_inline_inst args outs r (clone_instruction p labs inst) (SND a);
      c = rewrite_inline_insts args outs r (MAP (clone_instruction p labs) post) (SND b)
  in lookup_block (STRCAT p cl)
       (inline_call_site p r caller callee lbl i).fn_blocks =
     SOME (clone_basic_block p labs cb with
       bb_instructions := FST a ++ FST b ++ FST c)
Proof
  strip_tac >> drule_all inline_call_site_lookup_clone >>
  disch_then (qspec_then `i` assume_tac) >> simp[] >>
  simp[rewrite_inline_block_def, clone_basic_block_def, pairTheory.UNCURRY,
       MAP_APPEND, rewrite_inline_insts_focus]
QED

Theorem inline_rewrite_focus_getter:
  instrs = FST a ++ FST b ++ FST c /\ j < LENGTH (FST b) ==>
  LENGTH (FST a) + j < LENGTH instrs /\
  EL (LENGTH (FST a) + j) instrs = EL j (FST b)
Proof
  strip_tac >> gvs[] >> simp[EL_APPEND2, EL_APPEND1]
QED

(* Unlike fn_insts projections, this retains each block's location. *)
Theorem inline_renumber_blocks_located[local]:
  !bbs n acc n' res f.
    (!i k. f (i with inst_id := k) = f i) /\
    FOLDL (\(n,acc) bb.
      let (n',bb') = renumber_block_inst_ids n bb in (n',acc ++ [bb']))
      (n,acc) bbs = (n',res) ==>
    MAP (\bb. (bb.bb_label, MAP f bb.bb_instructions)) res =
    MAP (\bb. (bb.bb_label, MAP f bb.bb_instructions)) (acc ++ bbs)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `FOLDL _ _ _ = _` mp_tac >> simp[Once FOLDL] >>
  Cases_on `renumber_block_inst_ids n h` >> simp[] >> strip_tac >>
  gvs[LET_THM] >> first_x_assum drule_all >>
  simp[MAP_APPEND, APPEND_ASSOC] >>
  qspecl_then [`n`, `h`] mp_tac renumber_block_structure >>
  drule renumber_block_projection >>
  disch_then (qspecl_then [`n`, `h`] mp_tac) >> simp[]
QED

Theorem inline_renumber_fn_located:
  (!i k. f (i with inst_id := k) = f i) ==>
  MAP (\bb. (bb.bb_label, MAP f bb.bb_instructions))
    (renumber_fn_inst_ids fn).fn_blocks =
  MAP (\bb. (bb.bb_label, MAP f bb.bb_instructions)) fn.fn_blocks
Proof
  strip_tac >> simp[renumber_fn_inst_ids_def] >> pairarg_tac >> simp[] >>
  drule_all (SRULE [LET_THM] inline_renumber_blocks_located) >> simp[]
QED

Theorem inline_lookup_located_projection[local]:
  !bbs bbs' f l.
  MAP (\bb. (bb.bb_label, MAP f bb.bb_instructions)) bbs =
  MAP (\bb. (bb.bb_label, MAP f bb.bb_instructions)) bbs' ==>
  OPTION_MAP (\bb. (bb.bb_label, MAP f bb.bb_instructions)) (lookup_block l bbs) =
  OPTION_MAP (\bb. (bb.bb_label, MAP f bb.bb_instructions)) (lookup_block l bbs')
Proof
  Induct >> Cases_on `bbs'` >> simp[lookup_block_def] >>
  rpt strip_tac >> gvs[] >> simp[FIND_thm] >>
  IF_CASES_TAC >> gvs[GSYM lookup_block_def]
QED

Theorem inline_renumber_lookup_projection:
  (!i k. f (i with inst_id := k) = f i) ==>
  OPTION_MAP (\bb. (bb.bb_label, MAP f bb.bb_instructions))
    (lookup_block l (renumber_fn_inst_ids fn).fn_blocks) =
  OPTION_MAP (\bb. (bb.bb_label, MAP f bb.bb_instructions))
    (lookup_block l fn.fn_blocks)
Proof
  strip_tac >> irule inline_lookup_located_projection >>
  irule inline_renumber_fn_located >> simp[]
QED

Definition inline_inst_fields_def:
  inline_inst_fields inst = (inst.inst_opcode, inst.inst_operands, inst.inst_outputs)
End

Theorem inline_renumber_lookup_none[simp]:
  lookup_block l (renumber_fn_inst_ids fn).fn_blocks = NONE <=>
  lookup_block l fn.fn_blocks = NONE
Proof
  mp_tac (Q.ISPEC `inline_inst_fields` (Q.GEN `f` inline_renumber_lookup_projection)) >>
  simp[inline_inst_fields_def] >>
  Cases_on `lookup_block l (renumber_fn_inst_ids fn).fn_blocks` >>
  Cases_on `lookup_block l fn.fn_blocks` >> simp[]
QED

Theorem inline_renumber_lookup_some:
  lookup_block l fn.fn_blocks = SOME bb ==>
  ?bb'. lookup_block l (renumber_fn_inst_ids fn).fn_blocks = SOME bb' /\
    bb'.bb_label = bb.bb_label /\
    MAP inline_inst_fields bb'.bb_instructions = MAP inline_inst_fields bb.bb_instructions
Proof
  strip_tac >>
  mp_tac (Q.ISPEC `inline_inst_fields` (Q.GEN `f` inline_renumber_lookup_projection)) >>
  simp[inline_inst_fields_def] >>
  Cases_on `lookup_block l (renumber_fn_inst_ids fn).fn_blocks` >> simp[]
QED

Theorem inline_fields_get_instruction:
  MAP inline_inst_fields bb'.bb_instructions = MAP inline_inst_fields bb.bb_instructions ==>
  OPTION_MAP inline_inst_fields (get_instruction bb' k) =
  OPTION_MAP inline_inst_fields (get_instruction bb k)
Proof
  strip_tac >>
  `LENGTH bb'.bb_instructions = LENGTH bb.bb_instructions` by
    metis_tac[LENGTH_MAP] >>
  simp[get_instruction_def] >> IF_CASES_TAC >> simp[] >>
  gvs[LIST_EQ_REWRITE, EL_MAP]
QED

(* Fetched semantic fields retain a concrete block and instruction witness. *)
Definition inline_fetched_fields_def:
  inline_fetched_fields fn b j fields <=>
    ?bb inst. lookup_block b fn.fn_blocks = SOME bb /\
      get_instruction bb j = SOME inst /\ inline_inst_fields inst = fields
End

Theorem inline_fetched_fields_elim:
  inline_fetched_fields fn b j fields ==>
  ?bb inst. lookup_block b fn.fn_blocks = SOME bb /\
    get_instruction bb j = SOME inst /\ inline_inst_fields inst = fields
Proof
  simp[inline_fetched_fields_def]
QED

Theorem inline_fetched_invoke_embedding:
  lookup_block lbl caller.fn_blocks = SOME callbb /\
  lookup_block b callee.fn_blocks = SOME cb /\
  cb.bb_instructions = pre ++ call::post /\ call.inst_opcode = INVOKE /\
  ~MEM (STRCAT p b) (fn_labels caller) /\ STRCAT p b <> ret ==>
  let args = rotate_invoke_ops (EL i callbb.bb_instructions).inst_operands;
      outs = (EL i callbb.bb_instructions).inst_outputs;
      k = LENGTH (FST (rewrite_inline_insts args outs ret
            (MAP (clone_instruction p (fn_labels callee)) pre) 0));
      final = renumber_fn_inst_ids (inline_call_site p ret caller callee lbl i)
  in inline_fetched_fields final (STRCAT p b) k
       (inline_inst_fields (clone_instruction p (fn_labels callee) call))
Proof
  strip_tac >> simp[LET_THM] >>
  qmatch_goalsub_abbrev_tac `inline_fetched_fields final _ k fields` >>
  drule_all inline_call_site_lookup_clone_focus >>
  disch_then (qspec_then `i` mp_tac) >>
  simp[rewrite_inline_inst_def, clone_instruction_def, is_param_opcode_def] >>
  qmatch_goalsub_abbrev_tac `SOME raw` >> strip_tac >>
  `get_instruction raw k = SOME (clone_instruction p (fn_labels callee) call)` by
    simp[Abbr `raw`, Abbr `k`, get_instruction_def, clone_instruction_def,
         EL_APPEND2, EL_APPEND1] >>
  drule inline_renumber_lookup_some >> strip_tac >>
  drule inline_fields_get_instruction >> disch_then (qspec_then `k` mp_tac) >>
  simp[] >> Cases_on `get_instruction bb' k` >> simp[] >> strip_tac >>
  simp[inline_fetched_fields_def, Abbr `final`, Abbr `fields`] >>
  metis_tac[]
QED

Theorem inline_clone_fields_cong:
  inline_inst_fields a = inline_inst_fields b ==>
  inline_inst_fields (clone_instruction p labs a) =
  inline_inst_fields (clone_instruction p labs b)
Proof
  simp[inline_inst_fields_def, clone_instruction_def]
QED

(* Indexed consumer, so a renumbered first embedding can be the callee of
   the second. Its actual intermediate instruction need not have the old ID. *)
Theorem inline_fetched_invoke_embedding_indexed:
  inline_fetched_fields callee b j (inline_inst_fields call) /\
  call.inst_opcode = INVOKE /\
  lookup_block lbl caller.fn_blocks = SOME callbb /\
  ~MEM (STRCAT p b) (fn_labels caller) /\ STRCAT p b <> ret ==>
  ?cb. lookup_block b callee.fn_blocks = SOME cb /\
    inline_fetched_fields
      (renumber_fn_inst_ids (inline_call_site p ret caller callee lbl i))
      (STRCAT p b)
      (LENGTH (FST (rewrite_inline_insts
        (rotate_invoke_ops (EL i callbb.bb_instructions).inst_operands)
        (EL i callbb.bb_instructions).inst_outputs ret
        (MAP (clone_instruction p (fn_labels callee))
          (TAKE j cb.bb_instructions)) 0)))
      (inline_inst_fields (clone_instruction p (fn_labels callee) call))
Proof
  strip_tac >> drule inline_fetched_fields_elim >> strip_tac >>
  fs[get_instruction_def] >>
  `bb.bb_instructions = TAKE j bb.bb_instructions ++
      EL j bb.bb_instructions :: DROP (SUC j) bb.bb_instructions` by
    metis_tac[TAKE_DROP, DROP_CONS_EL] >>
  `(EL j bb.bb_instructions).inst_opcode = INVOKE` by
    gvs[inline_inst_fields_def] >>
  drule_all inline_fetched_invoke_embedding >>
  disch_then (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
  drule inline_clone_fields_cong >>
  disch_then (qspecl_then [`p`, `fn_labels callee`] assume_tac) >>
  gvs[]
QED

Theorem inline_fetched_invoke_two_embeddings:
  inline_fetched_fields callee b j (inline_inst_fields call) /\
  call.inst_opcode = INVOKE /\
  lookup_block lbl1 caller1.fn_blocks = SOME callbb1 /\
  ~MEM (STRCAT p1 b) (fn_labels caller1) /\ STRCAT p1 b <> ret1 /\
  lookup_block lbl2 caller2.fn_blocks = SOME callbb2 /\
  ~MEM (STRCAT p2 (STRCAT p1 b)) (fn_labels caller2) /\
  STRCAT p2 (STRCAT p1 b) <> ret2 ==>
  let mid = renumber_fn_inst_ids (inline_call_site p1 ret1 caller1 callee lbl1 i1);
      final = renumber_fn_inst_ids (inline_call_site p2 ret2 caller2 mid lbl2 i2)
  in ?cb1 k1 cb2 k2.
    lookup_block b callee.fn_blocks = SOME cb1 /\
    k1 = LENGTH (FST (rewrite_inline_insts
      (rotate_invoke_ops (EL i1 callbb1.bb_instructions).inst_operands)
      (EL i1 callbb1.bb_instructions).inst_outputs ret1
      (MAP (clone_instruction p1 (fn_labels callee))
        (TAKE j cb1.bb_instructions)) 0)) /\
    lookup_block (STRCAT p1 b) mid.fn_blocks = SOME cb2 /\
    k2 = LENGTH (FST (rewrite_inline_insts
      (rotate_invoke_ops (EL i2 callbb2.bb_instructions).inst_operands)
      (EL i2 callbb2.bb_instructions).inst_outputs ret2
      (MAP (clone_instruction p2 (fn_labels mid))
        (TAKE k1 cb2.bb_instructions)) 0)) /\
    inline_fetched_fields mid (STRCAT p1 b) k1
      (inline_inst_fields (clone_instruction p1 (fn_labels callee) call)) /\
    inline_fetched_fields final (STRCAT p2 (STRCAT p1 b)) k2
      (inline_inst_fields (clone_instruction p2 (fn_labels mid)
        (clone_instruction p1 (fn_labels callee) call)))
Proof
  strip_tac >> simp[LET_THM] >>
  drule_all inline_fetched_invoke_embedding_indexed >>
  disch_then (qspec_then `i1` strip_assume_tac) >>
  qpat_x_assum `inline_fetched_fields callee b j _` kall_tac >>
  `(clone_instruction p1 (fn_labels callee) call).inst_opcode = INVOKE` by
    simp[clone_instruction_def] >>
  drule_all inline_fetched_invoke_embedding_indexed >>
  disch_then (qspec_then `i2` strip_assume_tac) >>
  gvs[]
QED

Theorem inline_one_site_first_label:
  ALL_DISTINCT (fn_labels caller) /\ caller.fn_blocks <> [] /\
  inline_one_site caller callee ist = SOME (final,next) ==>
  final.fn_blocks <> [] /\
  (HD final.fn_blocks).bb_label = (HD caller.fn_blocks).bb_label
Proof
  strip_tac >>
  Cases_on `find_invoke_site callee.fn_name caller.fn_blocks`
  >- gvs[inline_one_site_def] >>
  PairCases_on `x` >>
  drule_all find_invoke_site_lookup >> strip_tac >>
  drule inline_call_site_labels >>
  disch_then (qspecl_then [`callee`, `inline_prefix ist.is_inline_count`,
    `return_block_label (inline_prefix ist.is_inline_count) ist.is_label_counter`,
    `x1`] assume_tac) >>
  `fn_labels final = fn_labels caller ++
     [return_block_label (inline_prefix ist.is_inline_count) ist.is_label_counter] ++
     MAP (STRCAT (inline_prefix ist.is_inline_count)) (fn_labels callee)` by
    (qpat_x_assum `inline_one_site _ _ _ = _` mp_tac >>
     simp[inline_one_site_def, LET_THM] >> CASE_TAC >> strip_tac >>
     gvs[renumber_fn_labels, fix_inline_phis_structure]) >>
  Cases_on `caller.fn_blocks` >> Cases_on `final.fn_blocks` >>
  gvs[fn_labels_def]
QED
