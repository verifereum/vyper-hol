(* Original call occurrences retain their leaf and instruction addresses. *)
Theory functionInlinerOccurrences
Ancestors
  functionInlinerRoutedProvenance functionInlinerLocation
  functionInlinerEnvelopes functionInlinerOrigin functionInlinerActivation
  functionInlinerDefs venomInst list combin

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

