(* Static retained namespaces: erased source occurrences remain in the tree. *)
Theory functionInlinerEnvelopes
Ancestors
  functionInlinerNamespace functionInlinerOrigin functionInlinerDefs
  functionInlinerWf cfgTransform pred_set list string

Datatype:
  inline_namespace =
    InlineNamespaceLeaf ir_function
  | InlineNamespaceEdit inline_state ir_function ir_function
      inline_namespace inline_namespace
End

Definition inline_namespace_envelope_def:
  (inline_namespace_envelope (InlineNamespaceLeaf fn) =
    set (cfgTransform$fn_all_vars fn)) /\
  (inline_namespace_envelope (InlineNamespaceEdit ist caller callee a b) =
    inline_namespace_envelope a UNION
      IMAGE (STRCAT (inline_prefix ist.is_inline_count))
        (inline_namespace_envelope b))
End

Inductive inline_annotated_origin:
  (!ctx fn. inliner_input_ok ctx /\ MEM fn ctx.ctx_functions ==>
    inline_annotated_origin ctx 0 fn (InlineNamespaceLeaf fn)) /\
  (!ctx n m fn cert. inline_annotated_origin ctx n fn cert /\ n <= m ==>
    inline_annotated_origin ctx m fn cert) /\
  (!ctx n caller callee ist caller' ist' a b.
    inline_annotated_origin ctx n caller a /\
    inline_annotated_origin ctx n callee b /\
    fcg_is_reachable (fcg_analyze ctx) callee.fn_name /\
    ist.is_inline_count = n /\
    inline_one_site caller callee ist = SOME (caller',ist') ==>
    inline_annotated_origin ctx ist'.is_inline_count caller'
      (InlineNamespaceEdit ist caller callee a b))
End

Theorem inline_annotated_origin_erasure:
  !ctx n fn cert. inline_annotated_origin ctx n fn cert ==>
    qualified_origin ctx n fn
Proof
  ho_match_mp_tac inline_annotated_origin_ind >> rpt conj_tac >>
  metis_tac[qualified_origin_rules]
QED

Theorem inline_annotated_origin_exists:
  !ctx n fn. qualified_origin ctx n fn ==>
    ?cert. inline_annotated_origin ctx n fn cert
Proof
  ho_match_mp_tac qualified_origin_ind >> rpt conj_tac >>
  metis_tac[inline_annotated_origin_rules]
QED

Theorem inline_namespace_envelope_finite:
  !cert. FINITE (inline_namespace_envelope cert)
Proof
  Induct >> simp[inline_namespace_envelope_def]
QED

Theorem inline_namespace_envelope_bound:
  !ctx n fn cert. inline_annotated_origin ctx n fn cert ==>
    !v. v IN inline_namespace_envelope cert ==>
      ~isPREFIX "inl" v \/ ?k. k < n /\ isPREFIX (inline_prefix k) v
Proof
  ho_match_mp_tac inline_annotated_origin_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `qualified_origin ctx 0 fn` by metis_tac[qualified_origin_init] >>
      simp[inline_namespace_envelope_def, Excl "isPREFIX", Excl "isPREFIX_def"] >>
      metis_tac[qualified_origin_vars_bound, prim_recTheory.NOT_LESS_0])
  >- (rpt strip_tac >> metis_tac[inline_label_bound_mono]) >>
  rpt gen_tac >> strip_tac >> drule inline_one_site_counter >> strip_tac >>
  simp[inline_namespace_envelope_def, pred_setTheory.IN_UNION,
       pred_setTheory.IN_IMAGE, PULL_EXISTS,
       Excl "isPREFIX", Excl "isPREFIX_def"] >>
  rpt strip_tac
  >- (irule inline_label_bound_mono >> qexists `n` >> simp[] >> metis_tac[]) >>
  gvs[Excl "isPREFIX", Excl "isPREFIX_def"] >>
  metis_tac[inline_label_bound_clone]
QED

Theorem inline_namespace_envelope_fresh:
  inline_annotated_origin ctx n fn cert /\
  v IN inline_namespace_envelope cert ==>
  ~isPREFIX (inline_prefix n) v
Proof
  metis_tac[inline_namespace_envelope_bound, inline_label_bound_fresh]
QED

Theorem inline_namespace_envelope_split:
  inline_annotated_origin ctx n caller a ==>
  DISJOINT (inline_namespace_envelope a)
    (IMAGE (STRCAT (inline_prefix n)) (inline_namespace_envelope b))
Proof
  simp[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION,
    pred_setTheory.IN_INTER, pred_setTheory.IN_IMAGE, PULL_EXISTS] >>
  metis_tac[inline_namespace_envelope_fresh, stringTheory.isPREFIX_STRCAT]
QED

Theorem inline_namespace_disjoint_embedding:
  DISJOINT a b ==>
  DISJOINT (IMAGE (STRCAT p) a) (IMAGE (STRCAT p) b)
Proof
  simp[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION,
    pred_setTheory.IN_INTER, pred_setTheory.IN_IMAGE, PULL_EXISTS] >>
  metis_tac[stringTheory.STRCAT_11]
QED

(* Leaf paths are static embeddings, not dynamic activation identities. *)
Inductive inline_namespace_leaf:
  (!fn. inline_namespace_leaf (InlineNamespaceLeaf fn) I fn) /\
  (!ist caller callee a b rho fn.
    inline_namespace_leaf a rho fn ==>
    inline_namespace_leaf (InlineNamespaceEdit ist caller callee a b) rho fn) /\
  (!ist caller callee a b rho fn.
    inline_namespace_leaf b rho fn ==>
    inline_namespace_leaf (InlineNamespaceEdit ist caller callee a b)
      (STRCAT (inline_prefix ist.is_inline_count) o rho) fn)
End

Theorem inline_namespace_leaf_support:
  !cert rho fn. inline_namespace_leaf cert rho fn ==>
    IMAGE rho (set (cfgTransform$fn_all_vars fn)) SUBSET
      inline_namespace_envelope cert
Proof
  ho_match_mp_tac inline_namespace_leaf_ind >> rpt conj_tac >>
  simp[inline_namespace_envelope_def, pred_setTheory.SUBSET_DEF,
    pred_setTheory.IN_IMAGE, PULL_EXISTS] >> metis_tac[]
QED

(* Addresses run from root to node: F chooses caller/left, T callee/right.
   The outer embedding composes on the left of every inner prefix. *)
Inductive inline_namespace_node_at:
  (!cert. inline_namespace_node_at cert [] I cert) /\
  (!ist caller callee a b p rho sub.
    inline_namespace_node_at a p rho sub ==>
    inline_namespace_node_at (InlineNamespaceEdit ist caller callee a b)
      (F::p) rho sub) /\
  (!ist caller callee a b p rho sub.
    inline_namespace_node_at b p rho sub ==>
    inline_namespace_node_at (InlineNamespaceEdit ist caller callee a b)
      (T::p) (STRCAT (inline_prefix ist.is_inline_count) o rho) sub)
End

Definition inline_namespace_leaf_at_def:
  inline_namespace_leaf_at cert p rho fn <=>
    inline_namespace_node_at cert p rho (InlineNamespaceLeaf fn)
End

Theorem inline_namespace_node_injective:
  !cert p rho sub. inline_namespace_node_at cert p rho sub ==>
    INJ rho UNIV UNIV
Proof
  ho_match_mp_tac inline_namespace_node_at_ind >> rpt conj_tac >>
  simp[pred_setTheory.INJ_DEF] >> metis_tac[stringTheory.STRCAT_11]
QED

Theorem inline_namespace_node_support:
  !cert p rho sub. inline_namespace_node_at cert p rho sub ==>
    IMAGE rho (inline_namespace_envelope sub) SUBSET
      inline_namespace_envelope cert
Proof
  ho_match_mp_tac inline_namespace_node_at_ind >> rpt conj_tac >>
  simp[inline_namespace_envelope_def, pred_setTheory.SUBSET_DEF,
    pred_setTheory.IN_IMAGE, PULL_EXISTS] >> metis_tac[]
QED

Theorem inline_namespace_node_leaf[simp]:
  !fn p (rho:string -> string) sub. inline_namespace_node_at (InlineNamespaceLeaf fn) p rho sub <=>
    p = [] /\ rho = I /\ sub = InlineNamespaceLeaf fn
Proof
  simp[Once inline_namespace_node_at_cases] >> metis_tac[]
QED

Theorem inline_namespace_node_edit:
  !ist caller callee a b p (rho:string -> string) sub.
  inline_namespace_node_at (InlineNamespaceEdit ist caller callee a b) p rho sub <=>
    (p = [] /\ rho = I /\ sub = InlineNamespaceEdit ist caller callee a b) \/
    (?q. p = F::q /\ inline_namespace_node_at a q rho sub) \/
    (?q sigma. p = T::q /\
      rho = STRCAT (inline_prefix ist.is_inline_count) o sigma /\
      inline_namespace_node_at b q sigma sub)
Proof
  simp[Once inline_namespace_node_at_cases] >> metis_tac[]
QED

Definition inline_namespace_incomparable_def:
  inline_namespace_incomparable (p:bool list) q <=>
    ~IS_PREFIX p q /\ ~IS_PREFIX q p
End

Theorem inline_namespace_nodes_separate:
  !ctx n fn cert. inline_annotated_origin ctx n fn cert ==>
    !p q (rho:string -> string) sigma a b.
      inline_namespace_node_at cert p rho a /\
      inline_namespace_node_at cert q sigma b /\
      inline_namespace_incomparable p q ==>
      DISJOINT (IMAGE rho (inline_namespace_envelope a))
        (IMAGE sigma (inline_namespace_envelope b))
Proof
  ho_match_mp_tac inline_annotated_origin_strongind >> rpt conj_tac
  >- simp[inline_namespace_incomparable_def]
  >- metis_tac[] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[inline_namespace_node_edit, inline_namespace_incomparable_def,
    rich_listTheory.IS_PREFIX, PULL_EXISTS] >>
  rpt strip_tac >> gvs[]
  >- metis_tac[inline_namespace_incomparable_def]
  >- (qpat_x_assum `inline_namespace_node_at cert _ _ _`
        (strip_assume_tac o MATCH_MP inline_namespace_node_support) >>
      qpat_x_assum `inline_namespace_node_at cert' _ _ _`
        (strip_assume_tac o MATCH_MP inline_namespace_node_support) >>
      `DISJOINT (inline_namespace_envelope cert)
         (IMAGE (STRCAT (inline_prefix ist.is_inline_count))
           (inline_namespace_envelope cert'))` by
        metis_tac[inline_namespace_envelope_split] >>
      rewrite_tac[pred_setTheory.IMAGE_COMPOSE] >>
      metis_tac[pred_setTheory.IMAGE_SUBSET, pred_setTheory.DISJOINT_SUBSET,
        pred_setTheory.DISJOINT_SUBSET'])
  >- (qpat_x_assum `inline_namespace_node_at cert _ _ _`
        (strip_assume_tac o MATCH_MP inline_namespace_node_support) >>
      qpat_x_assum `inline_namespace_node_at cert' _ _ _`
        (strip_assume_tac o MATCH_MP inline_namespace_node_support) >>
      `DISJOINT (inline_namespace_envelope cert)
         (IMAGE (STRCAT (inline_prefix ist.is_inline_count))
           (inline_namespace_envelope cert'))` by
        metis_tac[inline_namespace_envelope_split] >>
      rewrite_tac[pred_setTheory.IMAGE_COMPOSE] >>
      metis_tac[pred_setTheory.IMAGE_SUBSET, pred_setTheory.DISJOINT_SUBSET,
        pred_setTheory.DISJOINT_SUBSET', pred_setTheory.DISJOINT_SYM]) >>
  rewrite_tac[pred_setTheory.IMAGE_COMPOSE] >>
  irule inline_namespace_disjoint_embedding >>
  metis_tac[inline_namespace_incomparable_def]
QED

Theorem inline_namespace_leaf_addresses:
  !cert p q (rho:string -> string) sigma fn gn.
    inline_namespace_leaf_at cert p rho fn /\
    inline_namespace_leaf_at cert q sigma gn /\ p <> q ==>
    inline_namespace_incomparable p q
Proof
  Induct >>
  simp[inline_namespace_leaf_at_def, inline_namespace_node_edit,
    inline_namespace_incomparable_def, rich_listTheory.IS_PREFIX,
    PULL_EXISTS] >> rpt strip_tac >> gvs[] >>
  metis_tac[inline_namespace_leaf_at_def, inline_namespace_incomparable_def]
QED

Theorem inline_namespace_leaves_separate:
  !ctx n root cert p q (rho:string -> string) sigma fn gn.
    inline_annotated_origin ctx n root cert ==>
    inline_namespace_leaf_at cert p rho fn ==>
    inline_namespace_leaf_at cert q sigma gn ==> p <> q ==>
    DISJOINT (IMAGE rho (set (cfgTransform$fn_all_vars fn)))
      (IMAGE sigma (set (cfgTransform$fn_all_vars gn)))
Proof
  rpt strip_tac >>
  drule_all inline_namespace_leaf_addresses >> strip_tac >>
  gvs[inline_namespace_leaf_at_def] >>
  drule_all inline_namespace_nodes_separate >>
  simp[inline_namespace_envelope_def]
QED
