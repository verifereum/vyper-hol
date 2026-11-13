Theory concretizePtrActivationChronology
Ancestors
  concretizePtrOwnerPath concretizePtrChronologicalHistory finite_map list rich_list

Definition ptr_activation_tokens_def:
  ptr_activation_tokens h a b tokens =
    if LENGTH b.po_stack = SUC (LENGTH a.po_stack) then LENGTH h :: tokens
    else if LENGTH a.po_stack = SUC (LENGTH b.po_stack) then TL tokens
    else tokens
End

Definition ptr_activation_registry_def:
  ptr_activation_registry h a b registry =
    if LENGTH b.po_stack = SUC (LENGTH a.po_stack)
    then registry |+ (LENGTH h,b.po_fn) else registry
End

Inductive ptr_ledger_source_activations:
[~root:]
  (!vs0 C a. ptr_chrono_history vs0 C [a] a /\ a.po_stack = [] ==>
    ptr_ledger_source_activations vs0 C [a] a [0] (FEMPTY |+ (0,a.po_fn)))
[~snoc:]
  (!vs0 C h a tokens registry b.
    ptr_ledger_source_activations vs0 C h a tokens registry /\
    ptr_chrono_step C a b ==>
    ptr_ledger_source_activations vs0 C (h ++ [b]) b
      (ptr_activation_tokens h a b tokens)
      (ptr_activation_registry h a b registry))
End

Theorem ptr_activation_step_lengths:
  ptr_chrono_step C a b ==>
  LENGTH b.po_stack = LENGTH a.po_stack \/
  LENGTH b.po_stack = SUC (LENGTH a.po_stack) \/
  LENGTH a.po_stack = SUC (LENGTH b.po_stack)
Proof
  simp[Once ptr_chrono_step_cases] >> rpt strip_tac >>
  gvs[ptr_observe_def]
QED

Theorem ptr_source_activations_total:
  !vs0 C h a. ptr_chrono_history vs0 C h a ==>
    ?tokens registry. ptr_ledger_source_activations vs0 C h a tokens registry
Proof
  ho_match_mp_tac ptr_chrono_history_ind >> conj_tac
  >- (rpt strip_tac >> irule_at Any (cj 1 ptr_ledger_source_activations_rules) >>
      conj_tac >- (irule (cj 1 ptr_chrono_history_rules) >> metis_tac[]) >>
      simp[ptr_observe_def]) >>
  metis_tac[ptr_ledger_source_activations_rules]
QED

Theorem ptr_source_activations_sound:
  !vs0 C h a tokens registry.
  ptr_ledger_source_activations vs0 C h a tokens registry ==>
  ptr_chrono_history vs0 C h a
Proof
  ho_match_mp_tac ptr_ledger_source_activations_ind >>
  metis_tac[ptr_chrono_history_rules]
QED

Theorem ptr_activation_geometry_step[local]:
  ptr_chrono_step C a b /\
  LENGTH tokens = SUC (LENGTH a.po_stack) /\ ALL_DISTINCT tokens /\
  EVERY (\t. t < LENGTH h) tokens /\
  (!t. t IN FDOM registry ==> t < LENGTH h) ==>
  LENGTH (ptr_activation_tokens h a b tokens) = SUC (LENGTH b.po_stack) /\
  ALL_DISTINCT (ptr_activation_tokens h a b tokens) /\
  EVERY (\t. t < LENGTH (h ++ [b])) (ptr_activation_tokens h a b tokens) /\
  (!t. t IN FDOM (ptr_activation_registry h a b registry) ==> t < LENGTH (h ++ [b]))
Proof
  strip_tac >> drule ptr_activation_step_lengths >> strip_tac >>
  gvs[ptr_activation_tokens_def, ptr_activation_registry_def, EVERY_MEM]
  >- (rpt conj_tac >> rpt strip_tac >> first_x_assum drule >> decide_tac)
  >- (conj_tac >- (strip_tac >> first_x_assum drule >> simp[]) >>
      rpt conj_tac >> rpt strip_tac >> gvs[] >>
      first_x_assum drule >> decide_tac) >>
  Cases_on `tokens` >> gvs[EVERY_MEM] >>
  rpt conj_tac >> rpt strip_tac >>
  `t' < LENGTH h` by metis_tac[] >> decide_tac
QED

Theorem ptr_source_activations_geometry[local]:
  !vs0 C h a tokens registry.
  ptr_ledger_source_activations vs0 C h a tokens registry ==>
  LENGTH tokens = SUC (LENGTH a.po_stack) /\ ALL_DISTINCT tokens /\
  EVERY (\t. t < LENGTH h) tokens /\
  (!t. t IN FDOM registry ==> t < LENGTH h)
Proof
  ho_match_mp_tac ptr_ledger_source_activations_ind >> conj_tac
  >- simp[] >> rpt gen_tac >> strip_tac >>
  drule_all ptr_activation_geometry_step >> simp[]
QED

Theorem ptr_source_activations_length:
  ptr_ledger_source_activations vs0 C h a tokens registry ==>
  LENGTH tokens = SUC (LENGTH a.po_stack)
Proof
  metis_tac[ptr_source_activations_geometry]
QED

Theorem ptr_source_activations_distinct:
  ptr_ledger_source_activations vs0 C h a tokens registry ==>
  ALL_DISTINCT tokens
Proof
  metis_tac[ptr_source_activations_geometry]
QED

Theorem ptr_source_activations_registry_bound:
  ptr_ledger_source_activations vs0 C h a tokens registry /\ t IN FDOM registry ==>
  t < LENGTH h
Proof
  metis_tac[ptr_source_activations_geometry]
QED

Theorem ptr_source_activations_registry_retained:
  ptr_ledger_source_activations vs0 C h a tokens registry /\ t IN FDOM registry ==>
  FLOOKUP (ptr_activation_registry h a b registry) t = FLOOKUP registry t
Proof
  strip_tac >> drule_all ptr_source_activations_registry_bound >> strip_tac >>
  `t <> LENGTH h` by decide_tac >>
  Cases_on `LENGTH b.po_stack = SUC (LENGTH a.po_stack)` >>
  simp[ptr_activation_registry_def, FLOOKUP_UPDATE]
QED

Theorem ptr_activation_lookup_step[local]:
  ptr_chrono_step C a b /\
  LENGTH tokens = SUC (LENGTH a.po_stack) /\
  EVERY (\t. t < LENGTH h) tokens /\
  (!d. d <= LENGTH a.po_stack ==>
    FLOOKUP registry (EL (LENGTH a.po_stack - d) tokens) =
      SOME (ptr_owner_view d a).cf_fn) ==>
  !d. d <= LENGTH b.po_stack ==>
    FLOOKUP (ptr_activation_registry h a b registry)
      (EL (LENGTH b.po_stack - d) (ptr_activation_tokens h a b tokens)) =
      SOME (ptr_owner_view d b).cf_fn
Proof
  strip_tac >> drule ptr_activation_step_lengths >> strip_tac
  >- (simp[ptr_activation_registry_def, ptr_activation_tokens_def] >>
      rpt strip_tac >> irule ptr_owner_view_step_function >> simp[] >>
      qexists `C` >> simp[]) 
  >- (simp[ptr_activation_registry_def, ptr_activation_tokens_def] >>
      rpt strip_tac >> Cases_on `d = LENGTH b.po_stack`
      >- simp[FLOOKUP_UPDATE, ptr_owner_view_def] >>
      `d <= LENGTH a.po_stack /\
       LENGTH b.po_stack - d = SUC (LENGTH a.po_stack - d)` by decide_tac >>
      simp[EL, FLOOKUP_UPDATE] >>
      `EL (LENGTH a.po_stack - d) tokens < LENGTH h` by
        (gvs[EVERY_EL] >> first_x_assum irule >> decide_tac) >>
      `SUC (LENGTH a.po_stack) - d = SUC (LENGTH a.po_stack - d)` by decide_tac >>
      `LENGTH h <> EL (LENGTH a.po_stack - d) tokens` by decide_tac >>
      simp[EL] >> irule ptr_owner_view_step_function >> simp[] >>
      qexists `C` >> simp[]) >>
  simp[ptr_activation_registry_def, ptr_activation_tokens_def] >>
  rpt strip_tac >>
  `d <= LENGTH a.po_stack /\
   LENGTH a.po_stack - d = SUC (LENGTH b.po_stack - d)` by decide_tac >>
  `(ptr_owner_view d a).cf_fn = (ptr_owner_view d b).cf_fn` by
    (irule ptr_owner_view_step_function >> simp[] >> qexists `C` >> simp[]) >>
  qpat_x_assum `!d. _` (qspec_then `d` mp_tac) >>
  `SUC (LENGTH b.po_stack) - d = SUC (LENGTH b.po_stack - d)` by decide_tac >>
  Cases_on `tokens` >> gvs[EL, TL]
QED

Theorem ptr_source_activations_lookup_invariant[local]:
  !vs0 C h a tokens registry.
  ptr_ledger_source_activations vs0 C h a tokens registry ==>
  ptr_ledger_source_activations vs0 C h a tokens registry /\
  (!d. d <= LENGTH a.po_stack ==>
    FLOOKUP registry (EL (LENGTH a.po_stack - d) tokens) =
      SOME (ptr_owner_view d a).cf_fn)
Proof
  ho_match_mp_tac ptr_ledger_source_activations_ind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- metis_tac[ptr_ledger_source_activations_rules] >>
      rpt strip_tac >> gvs[ptr_owner_view_def, FLOOKUP_UPDATE]) >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- metis_tac[ptr_ledger_source_activations_rules] >>
  drule ptr_source_activations_geometry >> strip_tac >>
  rpt strip_tac >> irule ptr_activation_lookup_step >> metis_tac[]
QED

Theorem ptr_source_activations_owner_lookup:
  ptr_ledger_source_activations vs0 C h a tokens registry /\
  d <= LENGTH a.po_stack ==>
  FLOOKUP registry (EL (LENGTH a.po_stack - d) tokens) =
    SOME (ptr_owner_view d a).cf_fn
Proof
  metis_tac[ptr_source_activations_lookup_invariant]
QED
