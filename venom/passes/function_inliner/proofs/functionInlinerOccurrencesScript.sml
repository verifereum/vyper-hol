(* Original call occurrences retain their leaf and instruction addresses. *)
Theory functionInlinerOccurrences
Ancestors
  functionInlinerRoutedProvenance functionInlinerLocation
  functionInlinerEnvelopes functionInlinerOrigin functionInlinerActivation
  functionInlinerDefs venomInst list rich_list combin dfAnalyzeProofs

Definition inline_entry_address_def:
  (inline_entry_address (InlineNamespaceLeaf fn) = []) /\
  (inline_entry_address (InlineNamespaceEdit ist caller callee a b) =
    F::inline_entry_address a)
End

Definition inline_entry_function_def:
  (inline_entry_function (InlineNamespaceLeaf fn) = fn) /\
  (inline_entry_function (InlineNamespaceEdit ist caller callee a b) =
    inline_entry_function a)
End

Theorem inline_entry_leaf:
  !cert. inline_namespace_leaf_at cert (inline_entry_address cert) I
    (inline_entry_function cert)
Proof
  Induct >>
  simp[inline_entry_address_def, inline_entry_function_def,
       inline_namespace_leaf_at_def, inline_namespace_node_edit] >>
  gvs[inline_namespace_leaf_at_def]
QED

Theorem inline_annotated_entry_identity:
  !ctx n root cert. inline_annotated_origin ctx n root cert ==>
    MEM (inline_entry_function cert) ctx.ctx_functions /\
    (inline_entry_function cert).fn_name = root.fn_name
Proof
  ho_match_mp_tac inline_annotated_origin_ind >> rpt conj_tac >>
  simp[inline_entry_function_def] >> rpt strip_tac >>
  metis_tac[inline_one_site_name]
QED

Theorem inline_annotated_entry_route:
  inline_annotated_origin ctx n root cert ==>
  ?path. inline_routed_leaf cert root (inline_entry_address cert)
           (inline_entry_function cert) path /\
         inline_path_rename path = I
Proof
  metis_tac[inline_annotated_origin_routed_leaf, inline_entry_leaf]
QED

(* A non-PHI call never changes during predecessor-label repair. *)
Theorem inline_edit_repair_invoke:
  inst.inst_opcode = INVOKE ==>
  inline_edit_repair e bb l inst = inst
Proof
  simp[inline_edit_repair_def]
QED

(* Strict address order records the first edit separating two leaves. *)
Definition inline_leaf_before_def:
  inline_leaf_before (p:bool list) q <=>
    ?u a b. p = u ++ [F] ++ a /\ q = u ++ [T] ++ b
End

Theorem inline_leaf_before_cons[simp]:
  !h p q. inline_leaf_before (h::p) (h::q) <=> inline_leaf_before p q
Proof
  rpt gen_tac >> simp[inline_leaf_before_def] >> eq_tac
  >- (rpt strip_tac >> Cases_on `u` >> gvs[] >> metis_tac[]) >>
  rpt strip_tac >> qexists `h::u` >> simp[] >> metis_tac[]
QED

Theorem inline_leaf_before_nil[simp]:
  (!p. ~inline_leaf_before [] p) /\
  (!p. ~inline_leaf_before p [])
Proof
  simp[inline_leaf_before_def]
QED

Theorem inline_leaf_before_split[simp]:
  (!p q. inline_leaf_before (F::p) (T::q)) /\
  (!p q. ~inline_leaf_before (T::p) (F::q))
Proof
  simp[inline_leaf_before_def] >> conj_tac
  >- (rpt gen_tac >> qexists `[]` >> simp[]) >>
  rpt strip_tac >> Cases_on `u` >> gvs[]
QED

Theorem inline_leaf_before_irreflexive:
  !p. ~inline_leaf_before p p
Proof
  Induct >> simp[]
QED

Theorem inline_leaf_before_transitive:
  !p q r. inline_leaf_before p q /\ inline_leaf_before q r ==>
    inline_leaf_before p r
Proof
  Induct >> simp[] >> Cases_on `h` >>
  Cases_on `q` >> simp[] >> Cases_on `r` >> simp[] >>
  Cases_on `h` >> Cases_on `h'` >> simp[] >> metis_tac[]
QED

(* Every unselected caller call has a concrete residual cursor. *)
Theorem inline_edit_keep_invoke:
  inline_site_edit_valid e /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME source_bb /\
  e.ise_index < LENGTH source_bb.bb_instructions /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  lookup_block l e.ise_caller.fn_blocks = SOME bb /\
  get_instruction bb j = SOME inst /\ inst.inst_opcode = INVOKE /\
  (l <> e.ise_block \/ j <> e.ise_index) ==>
  ?loc. inline_choice_location (InlineKeep e)
          <|il_block := l; il_phase := InlineAtInstruction j; il_counter := k|> = SOME loc /\
        inline_fetched_fields e.ise_final loc.il_block
          (case loc.il_phase of InlineAtInstruction i => i | _ => 0)
          (inline_inst_fields inst)
Proof
  rpt gen_tac >> disch_tac >> Cases_on `l = e.ise_block`
  >- (gvs[] >>
      `e.ise_index <= LENGTH bb.bb_instructions` by decide_tac >>
      `j < LENGTH bb.bb_instructions /\ inst = EL j bb.bb_instructions` by
        gvs[get_instruction_def] >>
      Cases_on `j < e.ise_index`
      >- (qexists `<|il_block := e.ise_block;
                    il_phase := InlineAtInstruction j; il_counter := k|>` >>
          simp[inline_choice_location_def] >>
          drule_all inline_edit_prefix_fetch >>
          gvs[inline_edit_repair_def]) >>
      `e.ise_index < j` by decide_tac >>
      qexists `<|il_block := e.ise_return;
                 il_phase := InlineAtInstruction (j - (e.ise_index+1));
                 il_counter := k|>` >>
      simp[inline_choice_location_def] >>
      drule_all inline_edit_suffix_fetch >>
      gvs[inline_edit_repair_def]) >>
  gvs[] >>
  qexists `<|il_block := l; il_phase := InlineAtInstruction j; il_counter := k|>` >>
  simp[inline_choice_location_def] >>
  drule_all inline_edit_other_fetch >> gvs[inline_edit_repair_def]
QED

(* Callee calls have singleton expansion, even among expanded parameters. *)
Theorem inline_edit_enter_invoke:
  inline_site_edit_valid e /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME source_bb /\
  e.ise_index < LENGTH source_bb.bb_instructions /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  lookup_block l e.ise_callee.fn_blocks = SOME bb /\
  ~MEM (STRCAT e.ise_prefix l) (fn_labels e.ise_caller) /\
  STRCAT e.ise_prefix l <> e.ise_return /\
  get_instruction bb j = SOME inst /\ inst.inst_opcode = INVOKE ==>
  ?loc i. inline_choice_location (InlineEnter e)
          <|il_block := l; il_phase := InlineAtInstruction j; il_counter := k|> = SOME loc /\
        loc.il_phase = InlineAtInstruction i /\
        inline_fetched_fields e.ise_final loc.il_block i
          (inline_inst_fields (clone_instruction e.ise_prefix
            (fn_labels e.ise_callee) inst))
Proof
  strip_tac >>
  `j < LENGTH bb.bb_instructions /\ inst = EL j bb.bb_instructions` by
    gvs[get_instruction_def] >>
  drule_all inline_edit_enter_focus_fetch >>
  simp[LET_THM] >> disch_then (qspec_then `0` mp_tac) >>
  gvs[rewrite_inline_inst_def, clone_instruction_def, is_param_opcode_def] >>
  strip_tac >>
  simp[inline_choice_location_def] >>
  gvs[inline_edit_repair_def]
QED

Datatype:
  inline_call_outcome =
    InlineResidual inline_location instruction
  | InlineSelected (bool list) (bool list) inline_site_edit (inline_layout_choice list)
End

(* Each rule is a syntactic edit step, not a target-execution premise.
   Selected carries the separating node, the exact entry address, and the
   inner-to-outer zipper of later edits. *)
Inductive inline_call_incidence:
  (!fn l j bb inst.
    lookup_block l fn.fn_blocks = SOME bb /\
    get_instruction bb j = SOME inst /\ inst.inst_opcode = INVOKE ==>
    inline_call_incidence (InlineNamespaceLeaf fn) fn [] fn l j inst
      (InlineResidual
        <|il_block := l; il_phase := InlineAtInstruction j; il_counter := 0|> inst)) /\
  (!ist caller callee a b e p fn l j orig loc inst loc'.
    inline_call_incidence a caller p fn l j orig (InlineResidual loc inst) /\
    inline_site_edit_valid e /\ e.ise_caller = caller /\
    e.ise_callee = callee /\ e.ise_state = ist /\
    inline_choice_location (InlineKeep e) loc = SOME loc' ==>
    inline_call_incidence (InlineNamespaceEdit ist caller callee a b)
      e.ise_final (F::p) fn l j orig (InlineResidual loc' inst)) /\
  (!ist caller callee a b e p fn l j orig loc inst loc'.
    inline_call_incidence b callee p fn l j orig (InlineResidual loc inst) /\
    inline_site_edit_valid e /\ e.ise_caller = caller /\
    e.ise_callee = callee /\ e.ise_state = ist /\
    inline_choice_location (InlineEnter e) loc = SOME loc' ==>
    inline_call_incidence (InlineNamespaceEdit ist caller callee a b)
      e.ise_final (T::p) fn l j orig
      (InlineResidual loc' (clone_instruction e.ise_prefix (fn_labels callee) inst))) /\
  (!ist caller callee a b e p fn l j orig loc inst.
    inline_call_incidence a caller p fn l j orig (InlineResidual loc inst) /\
    inline_site_edit_valid e /\ e.ise_caller = caller /\
    e.ise_callee = callee /\ e.ise_state = ist /\
    loc.il_block = e.ise_block /\ loc.il_phase = InlineAtInstruction e.ise_index ==>
    inline_call_incidence (InlineNamespaceEdit ist caller callee a b)
      e.ise_final (F::p) fn l j orig
      (InlineSelected [] (T::inline_entry_address b) e [])) /\
  (!ist caller callee a b e p fn l j orig u q selected zipper.
    inline_call_incidence a caller p fn l j orig
      (InlineSelected u q selected zipper) /\
    inline_site_edit_valid e /\ e.ise_caller = caller /\
    e.ise_callee = callee /\ e.ise_state = ist ==>
    inline_call_incidence (InlineNamespaceEdit ist caller callee a b)
      e.ise_final (F::p) fn l j orig
      (InlineSelected (F::u) (F::q) selected (zipper ++ [InlineKeep e]))) /\
  (!ist caller callee a b e p fn l j orig u q selected zipper.
    inline_call_incidence b callee p fn l j orig
      (InlineSelected u q selected zipper) /\
    inline_site_edit_valid e /\ e.ise_caller = caller /\
    e.ise_callee = callee /\ e.ise_state = ist ==>
    inline_call_incidence (InlineNamespaceEdit ist caller callee a b)
      e.ise_final (T::p) fn l j orig
      (InlineSelected (T::u) (T::q) selected (zipper ++ [InlineEnter e])))
End

Theorem inline_call_incidence_source:
  !cert root p fn l j orig outcome.
    inline_call_incidence cert root p fn l j orig outcome ==>
    (?rho. inline_namespace_leaf_at cert p rho fn) /\
    (?bb. lookup_block l fn.fn_blocks = SOME bb /\
          get_instruction bb j = SOME orig) /\ orig.inst_opcode = INVOKE
Proof
  ho_match_mp_tac inline_call_incidence_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >>
  gvs[inline_namespace_leaf_at_def, inline_namespace_node_edit] >>
  metis_tac[]
QED

Theorem inline_call_incidence_selected_order:
  !cert root p fn l j orig outcome.
    inline_call_incidence cert root p fn l j orig outcome ==>
    !u q e zipper. outcome = InlineSelected u q e zipper ==>
      inline_leaf_before p q
Proof
  ho_match_mp_tac inline_call_incidence_ind >> rpt conj_tac >>
  simp[]
QED

Theorem inline_call_incidence_residual_phase:
  !cert root p fn l j orig outcome.
    inline_call_incidence cert root p fn l j orig outcome ==>
    !loc inst. outcome = InlineResidual loc inst ==>
      (?i. loc.il_phase = InlineAtInstruction i) /\ inst.inst_opcode = INVOKE
Proof
  ho_match_mp_tac inline_call_incidence_ind >> rpt conj_tac >>
  simp[] >> rpt strip_tac >>
  gvs[inline_choice_location_def, clone_instruction_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem inline_call_incidence_selected_node:
  !cert root p fn l j orig outcome.
    inline_call_incidence cert root p fn l j orig outcome ==>
    !u q e zipper. outcome = InlineSelected u q e zipper ==>
      inline_site_edit_valid e /\
      (?a b. inline_namespace_node_at cert u (inline_path_rename zipper)
               (InlineNamespaceEdit e.ise_state e.ise_caller e.ise_callee a b) /\
             q = u ++ [T] ++ inline_entry_address b)
Proof
  ho_match_mp_tac inline_call_incidence_ind >> rpt conj_tac >> simp[] >>
  rpt strip_tac >>
  gvs[inline_path_rename_def, inline_path_rename_append,
      inline_choice_rename_def, inline_namespace_node_edit, o_DEF,
      inline_site_edit_valid_def, SF ETA_ss] >>
  metis_tac[inline_namespace_node_at_rules]
QED

(* Counter weakening does not hide the edit that produced this tree node. *)
Theorem inline_annotated_origin_edit_elim:
  !ctx n root cert. inline_annotated_origin ctx n root cert ==>
    !ist caller callee a b.
      cert = InlineNamespaceEdit ist caller callee a b ==>
      inline_annotated_origin ctx ist.is_inline_count caller a /\
      inline_annotated_origin ctx ist.is_inline_count callee b /\
      fcg_is_reachable (fcg_analyze ctx) callee.fn_name /\
      ?next. inline_one_site caller callee ist = SOME (root,next)
Proof
  ho_match_mp_tac inline_annotated_origin_strongind >> rpt conj_tac >>
  simp[] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem inline_annotated_origin_labels:
  inline_annotated_origin ctx n fn cert ==>
    ALL_DISTINCT (fn_labels fn) /\
    !l. MEM l (fn_labels fn) ==>
      ~isPREFIX "inl" l \/ ?k. k < n /\ isPREFIX (inline_prefix k) l
Proof
  strip_tac >> drule inline_annotated_origin_erasure >>
  disch_then (strip_assume_tac o MATCH_MP qualified_origin_erasure) >>
  drule inliner_fn_origin_structure >>
  simp[venomWfTheory.wf_function_def, fn_labels_def, EVERY_MEM, MEM_MAP,
       Excl "isPREFIX", Excl "isPREFIX_def"] >> metis_tac[]
QED

Theorem inline_annotated_edit_fetch_facts:
  inline_annotated_origin ctx e.ise_state.is_inline_count e.ise_caller a /\
  inline_annotated_origin ctx e.ise_state.is_inline_count e.ise_callee b /\
  inline_site_edit_valid e ==>
  (?bb. lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
        e.ise_index < LENGTH bb.bb_instructions) /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  !l. MEM l (fn_labels e.ise_callee) ==>
    ~MEM (STRCAT e.ise_prefix l) (fn_labels e.ise_caller) /\
    STRCAT e.ise_prefix l <> e.ise_return
Proof
  strip_tac >>
  `ALL_DISTINCT (fn_labels e.ise_caller)` by
    metis_tac[inline_annotated_origin_labels] >>
  `!l. MEM l (fn_labels e.ise_caller) ==>
     ~isPREFIX (inline_prefix e.ise_state.is_inline_count) l` by
    metis_tac[inline_annotated_origin_labels,
      functionInlinerWfTheory.inline_label_bound_fresh] >>
  gvs[inline_site_edit_valid_def] >> conj_tac
  >- metis_tac[functionInlinerWfTheory.find_invoke_site_lookup] >>
  conj_tac
  >- (strip_tac >>
      metis_tac[return_block_label_def, stringTheory.isPREFIX_STRCAT]) >>
  rpt strip_tac
  >- metis_tac[stringTheory.isPREFIX_STRCAT] >>
  metis_tac[inline_annotated_origin_labels,
    functionInlinerWfTheory.inline_return_clone_distinct]
QED

(* An emitted call occupies the unique cell of an unchanged expansion. *)
Theorem inline_rewrite_invoke_cell:
  !args outs ret inst pi k ri.
    k < LENGTH (FST (rewrite_inline_inst args outs ret inst pi)) /\
    EL k (FST (rewrite_inline_inst args outs ret inst pi)) = ri /\
    ri.inst_opcode = INVOKE ==>
    k = 0 /\ ri = inst /\
    rewrite_inline_inst args outs ret inst pi = ([inst],pi)
Proof
  rpt strip_tac >>
  `ri = inst` by
    (irule rewrite_inline_inst_survivor >> simp[] >>
     metis_tac[MEM_EL]) >>
  gvs[rewrite_inline_inst_def, is_param_opcode_def] >>
  `k = 0` by decide_tac >> gvs[]
QED

Theorem inline_rewrite_invoke_index:
  !insts args outs ret pi k ri.
    k < LENGTH (FST (rewrite_inline_insts args outs ret insts pi)) /\
    EL k (FST (rewrite_inline_insts args outs ret insts pi)) = ri /\
    ri.inst_opcode = INVOKE ==>
    ?j. j < LENGTH insts /\ EL j insts = ri /\
        k = LENGTH (FST (rewrite_inline_insts args outs ret (TAKE j insts) pi))
Proof
  Induct >- simp[rewrite_inline_insts_def] >>
  map_every qx_gen_tac [`h`,`args`,`outs`,`ret`,`idx`,`k`,`ri`] >>
  simp[rewrite_inline_insts_def, LET_THM, pairTheory.UNCURRY] >>
  strip_tac >>
  Cases_on `k < LENGTH (FST (rewrite_inline_inst args outs ret h idx))`
  >- (gvs[rich_listTheory.EL_APPEND1, rich_listTheory.EL_APPEND2] >>
      drule inline_rewrite_invoke_cell >> simp[] >> strip_tac >>
      qexists `0` >> simp[rewrite_inline_insts_def]) >>
  gvs[rich_listTheory.EL_APPEND1, rich_listTheory.EL_APPEND2] >>
  first_x_assum (drule_at Any) >>
  (impl_tac >- decide_tac) >> strip_tac >>
  qexists `SUC j` >>
  simp[rewrite_inline_insts_def, LET_THM, pairTheory.UNCURRY] >>
  decide_tac
QED

Theorem inline_rewrite_expansion_nonempty:
  0 < LENGTH (FST (rewrite_inline_inst args outs ret inst idx))
Proof
  Cases_on `rewrite_inline_inst args outs ret inst idx` >>
  drule functionInlinerWfTheory.rewrite_inline_inst_shape >>
  simp[] >> Cases_on `q` >> simp[]
QED

Theorem inline_rewrite_prefix_strict:
  !insts args outs ret idx j k.
    j < k /\ k <= LENGTH insts ==>
    LENGTH (FST (rewrite_inline_insts args outs ret (TAKE j insts) idx)) <
    LENGTH (FST (rewrite_inline_insts args outs ret (TAKE k insts) idx))
Proof
  Induct >- simp[] >>
  map_every qx_gen_tac [`h`,`args`,`outs`,`ret`,`idx`,`j`,`k`] >>
  Cases_on `k` >- simp[] >>
  Cases_on `j` >>
  simp[rewrite_inline_insts_def, LET_THM, pairTheory.UNCURRY] >>
  rpt strip_tac
  >- (mp_tac (Q.INST [`inst` |-> `h`] inline_rewrite_expansion_nonempty) >> simp[]) >>
  first_x_assum irule >> simp[]
QED

Theorem inline_rewrite_prefix_injective:
  j <= LENGTH insts /\ k <= LENGTH insts /\
  LENGTH (FST (rewrite_inline_insts args outs ret (TAKE j insts) idx)) =
  LENGTH (FST (rewrite_inline_insts args outs ret (TAKE k insts) idx)) ==>
  j = k
Proof
  rpt strip_tac >>
  Cases_on `j < k`
  >- (drule_all inline_rewrite_prefix_strict >>
      disch_then (qspecl_then [`args`,`outs`,`ret`,`idx`] mp_tac) >> simp[]) >>
  Cases_on `k < j`
  >- (drule_all inline_rewrite_prefix_strict >>
      disch_then (qspecl_then [`args`,`outs`,`ret`,`idx`] mp_tac) >> simp[]) >>
  decide_tac
QED

Theorem inline_rewrite_invoke_unique_index:
  k < LENGTH (FST (rewrite_inline_insts args outs ret insts idx)) /\
  EL k (FST (rewrite_inline_insts args outs ret insts idx)) = ri /\
  ri.inst_opcode = INVOKE ==>
  ?!j. j < LENGTH insts /\ EL j insts = ri /\
       k = LENGTH (FST (rewrite_inline_insts args outs ret (TAKE j insts) idx))
Proof
  strip_tac >> drule_all inline_rewrite_invoke_index >> strip_tac >>
  simp[EXISTS_UNIQUE_THM] >>
  conj_tac >- (qexists `j` >> simp[]) >>
  rpt strip_tac >> irule inline_rewrite_prefix_injective >>
  metis_tac[arithmeticTheory.LESS_IMP_LESS_OR_EQ]
QED

(* Recover a source occurrence from a call in a rewritten cloned block. *)
Theorem inline_rewrite_clone_invoke_inverse:
  get_instruction
    (FST (rewrite_inline_block args outs ret (clone_basic_block p labs bb) idx))
    k = SOME ri /\ ri.inst_opcode = INVOKE ==>
  ?j inst. get_instruction bb j = SOME inst /\ inst.inst_opcode = INVOKE /\
    ri = clone_instruction p labs inst /\
    k = LENGTH (FST (rewrite_inline_insts args outs ret
          (MAP (clone_instruction p labs) (TAKE j bb.bb_instructions)) idx))
Proof
  simp[rewrite_inline_block_def, clone_basic_block_def,
       LET_THM, pairTheory.UNCURRY, get_instruction_def] >>
  strip_tac >> drule_all inline_rewrite_invoke_index >> strip_tac >>
  gvs[EL_MAP, GSYM MAP_TAKE] >>
  qexists `j` >> simp[clone_instruction_def] >>
  qpat_x_assum `clone_instruction _ _ _ = _` (mp_tac o GSYM) >>
  disch_then SUBST_ALL_TAC >> gvs[clone_instruction_def]
QED

Theorem inline_edit_final_labels:
  inline_site_edit_valid e ==>
  fn_labels e.ise_final =
  fn_labels (inline_call_site e.ise_prefix e.ise_return e.ise_caller
    e.ise_callee e.ise_block e.ise_index)
Proof
  simp[inline_site_edit_valid_def] >> strip_tac >>
  gvs[inline_one_site_def, functionInlinerWfTheory.renumber_fn_labels,
      AllCaseEqs()] >>
  qpat_x_assum `renumber_fn_inst_ids _ = _` (mp_tac o GSYM) >>
  disch_then SUBST_ALL_TAC >>
  simp[functionInlinerWfTheory.renumber_fn_labels] >>
  CASE_TAC >> simp[functionInlinerWfTheory.fix_inline_phis_structure]
QED


Theorem inline_edit_final_invoke_inverse:
  inline_site_edit_valid e /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME source_bb /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  inline_fetched_fields e.ise_final l k (inline_inst_fields call) /\
  call.inst_opcode = INVOKE ==>
  ?bb inst. lookup_block l
      (inline_call_site e.ise_prefix e.ise_return e.ise_caller e.ise_callee
        e.ise_block e.ise_index).fn_blocks = SOME bb /\
    get_instruction bb k = SOME inst /\ inst.inst_opcode = INVOKE /\
    inline_inst_fields inst = inline_inst_fields call
Proof
  strip_tac >>
  `fn_labels e.ise_final =
    fn_labels (inline_call_site e.ise_prefix e.ise_return e.ise_caller
      e.ise_callee e.ise_block e.ise_index)` by
    metis_tac[inline_edit_final_labels] >>
  gvs[functionInlinerSiteLayoutTheory.inline_fetched_fields_def] >>
  `MEM l (fn_labels e.ise_final)` by
    (gvs[fn_labels_def] >>
     metis_tac[venomExecPropsTheory.lookup_block_label,
               venomExecPropsTheory.lookup_block_MEM, MEM_MAP]) >>
  `?bb. lookup_block l
      (inline_call_site e.ise_prefix e.ise_return e.ise_caller e.ise_callee
        e.ise_block e.ise_index).fn_blocks = SOME bb` by
    (metis_tac[dfAnalyzeProofsTheory.lookup_block_exists, fn_labels_def]) >>
  gvs[inline_site_edit_valid_def] >>
  drule_at (Pat `inline_one_site _ _ _ = _`)
    functionInlinerPhiTransportTheory.inline_one_site_lookup_fields >>
  simp[] >> disch_then drule >> strip_tac >> gvs[] >>
  qpat_x_assum `MAP inline_inst_fields _ = _` mp_tac >>
  simp[LIST_EQ_REWRITE] >> strip_tac >>
  gvs[get_instruction_def] >>
  first_x_assum (qspec_then `k` mp_tac) >>
  qmatch_goalsub_abbrev_tac `if guard then _ else _` >>
  Cases_on `guard` >>
  gvs[EL_MAP, functionInlinerSiteLayoutTheory.inline_inst_fields_def,
      cfgTransformTheory.subst_label_inst_def, AllCaseEqs()] >>
  Cases_on `(EL k bb'.bb_instructions).inst_opcode = PHI` >> gvs[]
QED

Theorem inline_call_incidence_residual_fetch:
  !cert root p fn l j orig outcome.
    inline_call_incidence cert root p fn l j orig outcome ==>
    !ctx n loc inst. inline_annotated_origin ctx n root cert /\
      outcome = InlineResidual loc inst ==>
      ?k. loc.il_phase = InlineAtInstruction k /\
        inline_fetched_fields root loc.il_block k (inline_inst_fields inst)
Proof
  ho_match_mp_tac inline_call_incidence_strongind >> rpt conj_tac
  >- simp[functionInlinerSiteLayoutTheory.inline_fetched_fields_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[] >>
  drule inline_annotated_origin_edit_elim >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule_all inline_annotated_edit_fetch_facts >> strip_tac >>
  drule inline_call_incidence_residual_phase >> simp[] >> strip_tac >>
  gvs[functionInlinerSiteLayoutTheory.inline_fetched_fields_def] >>
  `inst'.inst_opcode = INVOKE` by
    gvs[functionInlinerSiteLayoutTheory.inline_inst_fields_def] >>
  Cases_on `loc` >> gvs[]
  >- (`s <> e.ise_block \/ k <> e.ise_index` by
        (spose_not_then strip_assume_tac >>
         gvs[inline_choice_location_def]) >>
      drule inline_edit_keep_invoke >> disch_then drule >> simp[] >>
      disch_then (drule_at (Pat `get_instruction _ _ = _`)) >>
      disch_then (qspecl_then [`s`,`n'`] mp_tac) >>
      simp[] >> strip_tac >>
      gvs[functionInlinerSiteLayoutTheory.inline_fetched_fields_def,
          inline_choice_location_def, AllCaseEqs()] >> metis_tac[]) >>
  `MEM s (fn_labels e.ise_callee)` by
    (simp[fn_labels_def, MEM_MAP] >>
     metis_tac[venomExecPropsTheory.lookup_block_MEM,
               venomExecPropsTheory.lookup_block_label]) >>
  first_x_assum drule >> strip_tac >>
  drule_all inline_edit_enter_invoke >>
  disch_then (qspec_then `n'` strip_assume_tac) >>
  gvs[functionInlinerSiteLayoutTheory.inline_fetched_fields_def] >>
  `<|il_block := s; il_phase := InlineAtInstruction k; il_counter := n'|> =
   inline_location s (InlineAtInstruction k) n'` by
    simp[inline_location_component_equality] >>
  gvs[] >>
  `inline_inst_fields (clone_instruction e.ise_prefix (fn_labels e.ise_callee) inst') =
   inline_inst_fields (clone_instruction e.ise_prefix (fn_labels e.ise_callee) inst)` by
    (irule functionInlinerSiteLayoutTheory.inline_clone_fields_cong >> simp[]) >>
  qexists_tac `i` >> simp[] >>
  qexistsl_tac [`bb''`,`inst''`] >> simp[]
QED

Theorem inline_call_incidence_total:
  !ctx n root cert. inline_annotated_origin ctx n root cert ==>
    !p rho fn l j bb inst.
      inline_namespace_leaf_at cert p rho fn /\
      lookup_block l fn.fn_blocks = SOME bb /\
      get_instruction bb j = SOME inst /\ inst.inst_opcode = INVOKE ==>
      ?outcome. inline_call_incidence cert root p fn l j inst outcome
Proof
  ho_match_mp_tac inline_annotated_origin_strongind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[inline_namespace_leaf_at_def] >>
      metis_tac[inline_call_incidence_rules])
  >- (rpt strip_tac >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule inline_one_site_edit_exists >> strip_tac >>
  gvs[] >>
  drule_all inline_annotated_edit_fetch_facts >> strip_tac >>
  gvs[inline_namespace_leaf_at_def, inline_namespace_node_edit] >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `outcome`
  >- (rename1 `InlineResidual loc call` >>
      drule inline_call_incidence_residual_fetch >> simp[] >>
      disch_then drule >> strip_tac >>
      drule inline_call_incidence_residual_phase >> simp[] >> strip_tac >>
      gvs[functionInlinerSiteLayoutTheory.inline_fetched_fields_def] >>
      Cases_on `loc.il_block = e.ise_block /\ loc.il_phase = InlineAtInstruction e.ise_index`
      >- metis_tac[cj 4 inline_call_incidence_rules] >>
      `inst'.inst_opcode = INVOKE` by
        gvs[functionInlinerSiteLayoutTheory.inline_inst_fields_def] >>
      drule inline_edit_keep_invoke >> disch_then drule >> simp[] >>
      disch_then (drule_at (Pat `get_instruction _ _ = _`)) >>
      disch_then (qspecl_then [`loc.il_block`,`loc.il_counter`] mp_tac) >>
      simp[] >> strip_tac >>
      Cases_on `loc` >> gvs[] >>
      `<|il_block := s; il_phase := InlineAtInstruction k; il_counter := n|> =
       inline_location s (InlineAtInstruction k) n` by
        simp[inline_location_component_equality] >>
      gvs[] >> metis_tac[cj 2 inline_call_incidence_rules])
  >- metis_tac[cj 5 inline_call_incidence_rules]
  >- (rename1 `InlineResidual loc call` >>
      drule inline_call_incidence_residual_fetch >> simp[] >>
      disch_then drule >> strip_tac >>
      drule inline_call_incidence_residual_phase >> simp[] >> strip_tac >>
      gvs[functionInlinerSiteLayoutTheory.inline_fetched_fields_def] >>
      `inst'.inst_opcode = INVOKE` by
        gvs[functionInlinerSiteLayoutTheory.inline_inst_fields_def] >>
      `MEM loc.il_block (fn_labels e.ise_callee)` by
        (simp[fn_labels_def, MEM_MAP] >>
         metis_tac[venomExecPropsTheory.lookup_block_MEM,
                   venomExecPropsTheory.lookup_block_label]) >>
      first_x_assum drule >> strip_tac >>
      drule inline_edit_enter_invoke >> disch_then drule >> simp[] >>
      disch_then (drule_at (Pat `get_instruction _ _ = _`)) >>
      disch_then (qspecl_then [`loc.il_block`,`loc.il_counter`] mp_tac) >>
      simp[] >> strip_tac >>
      Cases_on `loc` >> gvs[] >>
      `<|il_block := s; il_phase := InlineAtInstruction k; il_counter := n|> =
       inline_location s (InlineAtInstruction k) n` by
        simp[inline_location_component_equality] >>
      gvs[] >> metis_tac[cj 3 inline_call_incidence_rules]) >>
  metis_tac[cj 6 inline_call_incidence_rules]
QED

(* Invert caller-derived calls by their physical block and instruction index. *)
Theorem inline_edit_raw_caller_invoke_inverse:
  inline_site_edit_valid e /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME source_bb /\
  e.ise_index < LENGTH source_bb.bb_instructions /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  (MEM l (fn_labels e.ise_caller) \/ l = e.ise_return) /\
  lookup_block l
    (inline_call_site e.ise_prefix e.ise_return e.ise_caller e.ise_callee
       e.ise_block e.ise_index).fn_blocks = SOME bb /\
  get_instruction bb k = SOME call /\ call.inst_opcode = INVOKE ==>
  ?loc. inline_choice_location (InlineKeep e) loc = SOME
      <|il_block := l; il_phase := InlineAtInstruction k; il_counter := 0|> /\
    inline_fetched_fields e.ise_caller loc.il_block
      (case loc.il_phase of InlineAtInstruction j => j | _ => 0)
      (inline_inst_fields call)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `e.ise_block <> e.ise_return` by
    (qpat_assum `lookup_block e.ise_block e.ise_caller.fn_blocks = SOME source_bb`
       (mp_then Any assume_tac venomExecPropsTheory.lookup_block_MEM) >>
     qpat_assum `lookup_block e.ise_block e.ise_caller.fn_blocks = SOME source_bb`
       (mp_then Any assume_tac venomExecPropsTheory.lookup_block_label) >>
     gvs[fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  (Cases_on `l = e.ise_block`
  >- (gvs[] >>
      qpat_assum `lookup_block e.ise_block e.ise_caller.fn_blocks = SOME source_bb`
        (mp_then Any mp_tac functionInlinerSiteLayoutTheory.inline_call_site_lookup_call) >>
      disch_then (qspecl_then [`e.ise_return`,`e.ise_prefix`,`e.ise_index`,`e.ise_callee`] mp_tac) >>
      strip_tac >> gvs[get_instruction_def] >>
      Cases_on `k < e.ise_index`
      >- (qexists_tac `<|il_block := e.ise_block; il_phase := InlineAtInstruction k; il_counter := 0|>` >>
          simp[inline_choice_location_def,
               functionInlinerSiteLayoutTheory.inline_fetched_fields_def,
               get_instruction_def] >>
          gvs[EL_APPEND_EQN, EL_TAKE] >> metis_tac[]) >>
      `k = e.ise_index` by decide_tac >>
      gvs[EL_APPEND_EQN, LENGTH_TAKE]) >>
  Cases_on `l = e.ise_return`
  >- (gvs[] >>
      qpat_assum `lookup_block e.ise_block e.ise_caller.fn_blocks = SOME source_bb`
        (mp_then Any mp_tac functionInlinerSiteLayoutTheory.inline_call_site_lookup_return) >>
      disch_then (qspecl_then [`e.ise_return`,`e.ise_prefix`,`e.ise_index`,`e.ise_callee`] mp_tac) >>
      simp[] >> strip_tac >> gvs[get_instruction_def] >>
      qexists_tac `<|il_block := e.ise_block; il_phase := InlineAtInstruction (k + e.ise_index + 1); il_counter := 0|>` >>
      simp[inline_choice_location_def,
           functionInlinerSiteLayoutTheory.inline_fetched_fields_def,
           get_instruction_def, EL_DROP]) >>
  `?old. lookup_block l e.ise_caller.fn_blocks = SOME old` by
    (gvs[] >> fs[fn_labels_def] >>
     metis_tac[dfAnalyzeProofsTheory.lookup_block_exists]) >>
  `bb = old` by
    metis_tac[functionInlinerSiteLayoutTheory.inline_call_site_lookup_other,
              optionTheory.SOME_11] >>
  gvs[] >>
  qexists_tac `<|il_block := l; il_phase := InlineAtInstruction k; il_counter := 0|>` >>
  simp[inline_choice_location_def,
       functionInlinerSiteLayoutTheory.inline_fetched_fields_def] >>
  metis_tac[])
QED

Theorem inline_edit_raw_clone_invoke_inverse:
  inline_site_edit_valid e /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME source_bb /\
  e.ise_index < LENGTH source_bb.bb_instructions /\
  lookup_block l e.ise_callee.fn_blocks = SOME cb /\
  ~MEM (STRCAT e.ise_prefix l) (fn_labels e.ise_caller) /\
  STRCAT e.ise_prefix l <> e.ise_return /\
  lookup_block (STRCAT e.ise_prefix l)
    (inline_call_site e.ise_prefix e.ise_return e.ise_caller e.ise_callee
      e.ise_block e.ise_index).fn_blocks = SOME bb /\
  get_instruction bb k = SOME call /\ call.inst_opcode = INVOKE ==>
  ?j inst c. get_instruction cb j = SOME inst /\ inst.inst_opcode = INVOKE /\
    inline_choice_location (InlineEnter e)
      <|il_block := l; il_phase := InlineAtInstruction j; il_counter := 0|> =
      SOME <|il_block := STRCAT e.ise_prefix l;
             il_phase := InlineAtInstruction k; il_counter := c|> /\
    inline_inst_fields call =
      inline_inst_fields (clone_instruction e.ise_prefix (fn_labels e.ise_callee) inst)
Proof
  strip_tac >>
  `bb = FST (rewrite_inline_block
      (rotate_invoke_ops (EL e.ise_index source_bb.bb_instructions).inst_operands)
      (EL e.ise_index source_bb.bb_instructions).inst_outputs e.ise_return
      (clone_basic_block e.ise_prefix (fn_labels e.ise_callee) cb) 0)` by
    metis_tac[functionInlinerSiteLayoutTheory.inline_call_site_lookup_clone,
              optionTheory.SOME_11] >>
  gvs[] >> drule_all inline_rewrite_clone_invoke_inverse >> strip_tac >>
  qexistsl_tac [`j`,`inst`] >>
  gvs[get_instruction_def] >>
  simp[inline_choice_location_def]
QED

(* Every physical residual call comes from exactly one side of an edit. *)
Theorem inline_edit_invoke_preimage:
  inline_site_edit_valid e /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME source_bb /\
  e.ise_index < LENGTH source_bb.bb_instructions /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  (!cl. MEM cl (fn_labels e.ise_callee) ==>
     ~MEM (STRCAT e.ise_prefix cl) (fn_labels e.ise_caller) /\
     STRCAT e.ise_prefix cl <> e.ise_return) /\
  inline_fetched_fields e.ise_final l k (inline_inst_fields call) /\
  call.inst_opcode = INVOKE ==>
  (?loc. inline_choice_location (InlineKeep e) loc = SOME
      <|il_block := l; il_phase := InlineAtInstruction k; il_counter := 0|> /\
     inline_fetched_fields e.ise_caller loc.il_block
       (case loc.il_phase of InlineAtInstruction j => j | _ => 0)
       (inline_inst_fields call)) \/
  (?cl j inst cb c. lookup_block cl e.ise_callee.fn_blocks = SOME cb /\
     get_instruction cb j = SOME inst /\ inst.inst_opcode = INVOKE /\
     inline_choice_location (InlineEnter e)
       <|il_block := cl; il_phase := InlineAtInstruction j; il_counter := 0|> =
       SOME <|il_block := l; il_phase := InlineAtInstruction k; il_counter := c|> /\
     inline_inst_fields call = inline_inst_fields
       (clone_instruction e.ise_prefix (fn_labels e.ise_callee) inst))
Proof
  strip_tac >> drule_all inline_edit_final_invoke_inverse >> strip_tac >>
  `MEM l (fn_labels (inline_call_site e.ise_prefix e.ise_return e.ise_caller
        e.ise_callee e.ise_block e.ise_index))` by
    (simp[fn_labels_def, MEM_MAP] >>
     metis_tac[venomExecPropsTheory.lookup_block_MEM,
               venomExecPropsTheory.lookup_block_label]) >>
  Cases_on `MEM l (fn_labels e.ise_caller) \/ l = e.ise_return`
  >- (disj1_tac >> drule_all inline_edit_raw_caller_invoke_inverse >>
      strip_tac >> metis_tac[]) >>
  disj2_tac >>
  `?cl. MEM cl (fn_labels e.ise_callee) /\ l = STRCAT e.ise_prefix cl` by
    gvs[functionInlinerWfTheory.inline_call_site_labels, MEM_MAP] >>
  gvs[] >>
  `?cb. lookup_block cl e.ise_callee.fn_blocks = SOME cb` by
    metis_tac[dfAnalyzeProofsTheory.lookup_block_exists, fn_labels_def] >>
  metis_tac[inline_edit_raw_clone_invoke_inverse]
QED

(* Layout positions do not depend on the incoming bookkeeping counter. *)
Theorem inline_choice_location_counter:
  inline_choice_location choice loc = SOME dst ==>
  ?dst'. inline_choice_location choice (loc with il_counter := c) = SOME dst' /\
    dst'.il_block = dst.il_block /\ dst'.il_phase = dst.il_phase
Proof
  Cases_on `choice` >> Cases_on `loc` >>
  simp[inline_choice_location_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem inline_call_incidence_residual_preimage:
  !ctx n root cert. inline_annotated_origin ctx n root cert ==>
  !l k call. inline_fetched_fields root l k (inline_inst_fields call) /\
    call.inst_opcode = INVOKE ==>
    ?p fn sl sj orig loc inst.
      inline_call_incidence cert root p fn sl sj orig (InlineResidual loc inst) /\
      loc.il_block = l /\ loc.il_phase = InlineAtInstruction k /\
      inline_inst_fields inst = inline_inst_fields call
Proof
  ho_match_mp_tac inline_annotated_origin_strongind >> rpt conj_tac
  >- (rpt strip_tac >>
      gvs[functionInlinerSiteLayoutTheory.inline_fetched_fields_def] >>
      `inst.inst_opcode = INVOKE` by
        gvs[functionInlinerSiteLayoutTheory.inline_inst_fields_def] >>
      qexistsl_tac [`[]`,`root`,`l`,`k`,`inst`,
        `<|il_block := l; il_phase := InlineAtInstruction k; il_counter := 0|>`,
        `inst`] >> simp[] >> metis_tac[cj 1 inline_call_incidence_rules])
  >- (rpt strip_tac >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule inline_one_site_edit_exists >> strip_tac >> gvs[] >>
  drule_all inline_annotated_edit_fetch_facts >> strip_tac >>
  drule_all inline_edit_invoke_preimage >> strip_tac
  >- (`?i. loc.il_phase = InlineAtInstruction i` by
        (Cases_on `loc.il_phase` >>
         gvs[inline_choice_location_def, AllCaseEqs()]) >>
      gvs[] >>
      qpat_x_assum `!l k call. inline_fetched_fields e.ise_caller _ _ _ /\ _ ==> _`
        drule_all >> strip_tac >>
      rename1 `inline_call_incidence cert e.ise_caller p fn sl sj orig
        (InlineResidual src inst)` >>
      `src = loc with il_counter := src.il_counter` by
        simp[inline_location_component_equality] >>
      drule inline_choice_location_counter >>
      disch_then (qspec_then `src.il_counter` strip_assume_tac) >>
      gvs[] >> metis_tac[cj 2 inline_call_incidence_rules]) >>
  `inline_fetched_fields e.ise_callee cl j (inline_inst_fields inst)` by
    (simp[functionInlinerSiteLayoutTheory.inline_fetched_fields_def] >>
     metis_tac[]) >>
  qpat_x_assum `!l k call. inline_fetched_fields e.ise_callee _ _ _ /\ _ ==> _`
    drule_all >> strip_tac >>
  rename1 `inline_call_incidence cert' e.ise_callee p fn sl sj orig
    (InlineResidual src residual)` >>
  `src = <|il_block := cl; il_phase := InlineAtInstruction j;
           il_counter := 0|> with il_counter := src.il_counter` by
    simp[inline_location_component_equality] >>
  drule inline_choice_location_counter >>
  disch_then (qspec_then `src.il_counter` strip_assume_tac) >>
  `inline_inst_fields (clone_instruction e.ise_prefix (fn_labels e.ise_callee) residual) =
   inline_inst_fields (clone_instruction e.ise_prefix (fn_labels e.ise_callee) inst)` by
    (irule functionInlinerSiteLayoutTheory.inline_clone_fields_cong >> simp[]) >>
  gvs[] >> metis_tac[cj 3 inline_call_incidence_rules]
QED

Theorem inline_keep_cell_injective:
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  MEM a.il_block (fn_labels e.ise_caller) /\
  MEM b.il_block (fn_labels e.ise_caller) /\
  a.il_phase = InlineAtInstruction i /\ b.il_phase = InlineAtInstruction j /\
  inline_choice_location (InlineKeep e) a = SOME x /\
  inline_choice_location (InlineKeep e) b = SOME y /\
  x.il_block = y.il_block /\ x.il_phase = y.il_phase ==>
  a.il_block = b.il_block /\ i = j
Proof
  strip_tac >>
  gvs[inline_choice_location_def, AllCaseEqs()] >> decide_tac
QED

Theorem inline_enter_cell_injective:
  a.il_phase = InlineAtInstruction i /\ b.il_phase = InlineAtInstruction j /\
  inline_choice_location (InlineEnter e) a = SOME x /\
  inline_choice_location (InlineEnter e) b = SOME y /\
  x.il_block = y.il_block /\ x.il_phase = y.il_phase ==>
  a.il_block = b.il_block /\ i = j
Proof
  strip_tac >> gvs[inline_choice_location_def, AllCaseEqs()] >>
  qpat_x_assum `LENGTH _ = LENGTH _` mp_tac >>
  pure_rewrite_tac[MAP_TAKE] >> strip_tac >>
  irule inline_rewrite_prefix_injective >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem inline_edit_cell_images_disjoint:
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  (!cl. MEM cl (fn_labels e.ise_callee) ==>
    ~MEM (STRCAT e.ise_prefix cl) (fn_labels e.ise_caller) /\
    STRCAT e.ise_prefix cl <> e.ise_return) /\
  MEM a.il_block (fn_labels e.ise_caller) /\
  MEM b.il_block (fn_labels e.ise_callee) /\
  a.il_phase = InlineAtInstruction i /\ b.il_phase = InlineAtInstruction j /\
  inline_choice_location (InlineKeep e) a = SOME x /\
  inline_choice_location (InlineEnter e) b = SOME y ==>
  x.il_block <> y.il_block
Proof
  strip_tac >> gvs[inline_choice_location_def, AllCaseEqs()] >> metis_tac[]
QED

(* Context bookkeeping fields before/after are intentionally unconstrained. *)
Theorem inline_site_edit_layout_unique:
  inline_site_edit_valid e /\ inline_site_edit_valid f /\
  e.ise_state = f.ise_state /\ e.ise_caller = f.ise_caller /\
  e.ise_callee = f.ise_callee ==>
  e.ise_prefix = f.ise_prefix /\ e.ise_return = f.ise_return /\
  e.ise_block = f.ise_block /\ e.ise_index = f.ise_index /\
  inline_choice_location (InlineKeep e) = inline_choice_location (InlineKeep f) /\
  inline_choice_location (InlineEnter e) = inline_choice_location (InlineEnter f)
Proof
  strip_tac >> gvs[inline_site_edit_valid_def] >>
  simp[FUN_EQ_THM, inline_choice_location_def]
QED

Theorem inline_call_incidence_edit_residual:
  inline_site_edit_valid e /\
  inline_call_incidence
    (InlineNamespaceEdit e.ise_state e.ise_caller e.ise_callee a b)
    e.ise_final p fn l j orig (InlineResidual loc inst) ==>
  (?q src. p = F::q /\
    inline_call_incidence a e.ise_caller q fn l j orig (InlineResidual src inst) /\
    inline_choice_location (InlineKeep e) src = SOME loc) \/
  (?q src ri. p = T::q /\
    inline_call_incidence b e.ise_callee q fn l j orig (InlineResidual src ri) /\
    inst = clone_instruction e.ise_prefix (fn_labels e.ise_callee) ri /\
    inline_choice_location (InlineEnter e) src = SOME loc)
Proof
  strip_tac >>
  qpat_x_assum `inline_call_incidence _ _ _ _ _ _ _ _` mp_tac >>
  simp[Once inline_call_incidence_cases] >> rpt strip_tac >>
  drule_all inline_site_edit_layout_unique >> strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem inline_call_incidence_residual_label:
  inline_call_incidence cert root p fn l j orig (InlineResidual loc inst) /\
  inline_annotated_origin ctx n root cert ==>
  MEM loc.il_block (fn_labels root)
Proof
  strip_tac >> drule inline_call_incidence_residual_fetch >>
  disch_then drule >> simp[] >> strip_tac >>
  gvs[functionInlinerSiteLayoutTheory.inline_fetched_fields_def, fn_labels_def, MEM_MAP] >>
  metis_tac[venomExecPropsTheory.lookup_block_MEM,
            venomExecPropsTheory.lookup_block_label]
QED

Theorem inline_call_incidence_residual_unique:
  !ctx n root cert. inline_annotated_origin ctx n root cert ==>
  !p fn l j orig loc inst q gn m k other dst ri.
    inline_call_incidence cert root p fn l j orig (InlineResidual loc inst) /\
    inline_call_incidence cert root q gn m k other (InlineResidual dst ri) /\
    loc.il_block = dst.il_block /\ loc.il_phase = dst.il_phase ==>
    p = q /\ fn = gn /\ l = m /\ j = k /\ orig = other
Proof
  ho_match_mp_tac inline_annotated_origin_strongind >> rpt conj_tac
  >- (rpt strip_tac >>
      gvs[Once inline_call_incidence_cases] >>
      gvs[Once inline_call_incidence_cases] >> metis_tac[optionTheory.SOME_11])
  >- (rpt strip_tac >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!p fn l j orig loc inst q gn m k other dst ri.
    inline_call_incidence cert root _ _ _ _ _ _ /\ _ ==> _` (mk_asm "caller_ih") >>
  qpat_x_assum `!p fn l j orig loc inst q gn m k other dst ri.
    inline_call_incidence cert' root' _ _ _ _ _ _ /\ _ ==> _` (mk_asm "callee_ih") >>
  drule inline_one_site_edit_exists >> strip_tac >>
  qpat_x_assum `e.ise_caller = root` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `e.ise_callee = root'` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `e.ise_state = ist` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `e.ise_final = root''` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `e.ise_state.is_inline_count = n` (SUBST_ALL_TAC o SYM) >>
  drule_all inline_annotated_edit_fetch_facts >> strip_tac >>
  qpat_x_assum `inline_call_incidence _ _ p _ _ _ _ _`
    (mp_then Any mp_tac inline_call_incidence_edit_residual) >>
  simp[] >> strip_tac >>
  qpat_x_assum `inline_call_incidence _ _ q _ _ _ _ _`
    (mp_then Any mp_tac inline_call_incidence_edit_residual) >>
  simp[] >> strip_tac >>
  imp_res_tac inline_call_incidence_residual_phase >>
  imp_res_tac inline_call_incidence_residual_label >>
  gvs[]
  >- (drule_all inline_keep_cell_injective >> strip_tac >>
      asm "caller_ih" irule >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
      metis_tac[])
  >- metis_tac[inline_edit_cell_images_disjoint]
  >- metis_tac[inline_edit_cell_images_disjoint] >>
  drule_all inline_enter_cell_injective >> strip_tac >>
  asm "callee_ih" irule >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
  metis_tac[]
QED

(* The selected physical cell has an original occurrence, not merely a name. *)
Theorem inline_selected_site_preimage:
  inline_annotated_origin ctx e.ise_state.is_inline_count e.ise_caller a /\
  inline_site_edit_valid e ==>
  ?p fn l j orig loc inst args.
    inline_call_incidence a e.ise_caller p fn l j orig (InlineResidual loc inst) /\
    loc.il_block = e.ise_block /\ loc.il_phase = InlineAtInstruction e.ise_index /\
    inst.inst_opcode = INVOKE /\ inst.inst_operands = Label e.ise_callee.fn_name::args
Proof
  strip_tac >>
  `ALL_DISTINCT (fn_labels e.ise_caller)` by
    metis_tac[inline_annotated_origin_labels] >>
  `find_invoke_site e.ise_callee.fn_name e.ise_caller.fn_blocks =
    SOME (e.ise_block,e.ise_index)` by gvs[inline_site_edit_valid_def] >>
  drule_all functionInlinerNamespaceTheory.find_invoke_site_lookup_signature >>
  strip_tac >>
  `inline_fetched_fields e.ise_caller e.ise_block e.ise_index
     (inline_inst_fields (EL e.ise_index bb.bb_instructions))` by
    (simp[functionInlinerSiteLayoutTheory.inline_fetched_fields_def] >>
     metis_tac[get_instruction_def]) >>
  drule_all inline_call_incidence_residual_preimage >> strip_tac >>
  gvs[functionInlinerSiteLayoutTheory.inline_inst_fields_def] >> metis_tac[]
QED

Theorem inline_call_incidence_residual_routing:
  !cert root p fn l j orig outcome.
    inline_call_incidence cert root p fn l j orig outcome ==>
    !loc inst. outcome = InlineResidual loc inst ==>
    ?path. inline_routed_leaf cert root p fn path /\
      inst.inst_outputs = MAP (inline_path_rename path) orig.inst_outputs /\
      inst.inst_operands = FOLDL (\ops c. case c of
        InlineKeep e => ops
      | InlineEnter e => MAP (clone_operand e.ise_prefix (fn_labels e.ise_callee)) ops)
        orig.inst_operands path
Proof
  ho_match_mp_tac inline_call_incidence_ind >> rpt conj_tac >> simp[]
  >- (rpt strip_tac >> qexists `[]` >>
      simp[inline_path_rename_def, inline_routed_leaf_rules])
  >- (rpt strip_tac >> qexists `path ++ [InlineKeep e]` >>
      simp[inline_path_rename_append, inline_path_rename_def,
        inline_choice_rename_def, FOLDL_APPEND, o_DEF, SF ETA_ss] >>
      metis_tac[inline_routed_leaf_rules]) >>
  rpt strip_tac >> qexists `path ++ [InlineEnter e]` >>
  simp[inline_path_rename_append, inline_path_rename_def,
    inline_choice_rename_def, FOLDL_APPEND, clone_instruction_def, MAP_MAP_o, o_DEF] >>
  metis_tac[inline_routed_leaf_rules]
QED

Theorem inline_call_incidence_residual_target:
  !cert root p fn l j orig outcome.
    inline_call_incidence cert root p fn l j orig outcome ==>
    !ctx n loc inst.
      inline_annotated_origin ctx n root cert /\ outcome = InlineResidual loc inst ==>
      ?target args actual.
        orig.inst_operands = Label target::args /\
        inst.inst_operands = Label target::actual
Proof
  ho_match_mp_tac inline_call_incidence_strongind >> rpt conj_tac >> simp[]
  >- (rpt strip_tac >>
      drule inline_annotated_origin_erasure >> strip_tac >>
      `MEM orig (fn_insts root)` by
        (gvs[get_instruction_def, AllCaseEqs(), fn_insts_def,
             unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >>
         metis_tac[venomExecPropsTheory.lookup_block_MEM, MEM_EL]) >>
      drule_all qualified_origin_calls_aux >> metis_tac[])
  >- (rpt strip_tac >>
      drule inline_annotated_origin_edit_elim >> simp[] >> strip_tac >>
      metis_tac[]) >>
  rpt strip_tac >>
  drule inline_annotated_origin_edit_elim >> simp[] >> strip_tac >>
  `?target args actual. orig.inst_operands = Label target::args /\
     inst.inst_operands = Label target::actual` by metis_tac[] >>
  `qualified_origin ctx e.ise_state.is_inline_count e.ise_callee` by
    metis_tac[inline_annotated_origin_erasure] >>
  `?k. loc.il_phase = InlineAtInstruction k /\
     inline_fetched_fields e.ise_callee loc.il_block k (inline_inst_fields inst)` by
    metis_tac[inline_call_incidence_residual_fetch] >>
  `inst.inst_opcode = INVOKE` by metis_tac[inline_call_incidence_residual_phase] >>
  `~MEM target (fn_labels e.ise_callee)` by
    (gvs[functionInlinerSiteLayoutTheory.inline_fetched_fields_def,
         functionInlinerSiteLayoutTheory.inline_inst_fields_def] >>
     `MEM inst' (fn_insts e.ise_callee)` by
       (gvs[get_instruction_def, AllCaseEqs(), fn_insts_def,
         unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >>
        metis_tac[venomExecPropsTheory.lookup_block_MEM, MEM_EL]) >>
     metis_tac[qualified_origin_call_target_external]) >>
  metis_tac[clone_instruction_call_signature]
QED

Theorem inline_selected_site_original_callee:
  inline_annotated_origin ctx e.ise_state.is_inline_count e.ise_caller a /\
  inline_annotated_origin ctx e.ise_state.is_inline_count e.ise_callee b /\
  inline_site_edit_valid e ==>
  ?p fn l j orig loc inst args actual.
    inline_call_incidence a e.ise_caller p fn l j orig (InlineResidual loc inst) /\
    loc.il_block = e.ise_block /\ loc.il_phase = InlineAtInstruction e.ise_index /\
    orig.inst_operands = Label (inline_entry_function b).fn_name::args /\
    inst.inst_operands = Label (inline_entry_function b).fn_name::actual /\
    MEM (inline_entry_function b) ctx.ctx_functions
Proof
  strip_tac >> drule_all inline_selected_site_preimage >> strip_tac >>
  `?target args actual. orig.inst_operands = Label target::args /\
      inst.inst_operands = Label target::actual` by
    metis_tac[inline_call_incidence_residual_target] >>
  drule inline_annotated_entry_identity >> strip_tac >>
  gvs[] >> metis_tac[]
QED
