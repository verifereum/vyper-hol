(* Completed outputs retain their source-derived well-formedness separately. *)
Theory bodyIntCallFamCallIntCompletedEffect
Ancestors
  bodyIntCallFamCallIntStageInterface bodyIntCallCopySharpDynamic
  placeMemoryCopyEffect valueEncodingProps

val completed = ``\cx start current ty flag v op s.
  ?tv w. evaluate_type (get_tenv cx) ty = SOME tv /\
    eval_operand op s = SOME w /\
    (!x. op = Var x ==> not_fresh_at current x) /\
    (if flag then is_word_type ty /\ w = typed_val_to_w256 tv v
     else val_in_memory tv v (w2n w) s.vs_memory /\
       ?aid len. FLOOKUP s.vs_allocas aid = SOME (w2n w,len) /\
         start.cs_next_id <= aid /\ aid < current.cs_next_id /\
         type_memory_size tv <= len /\
         w2n w + len <= s.vs_alloca_next /\
         w2n w + len < dimword (:256))``;

val completed_prefix = ``\cx start current tys flags values ops s.
  LENGTH flags = LENGTH tys /\ LENGTH values = LENGTH tys /\
  LENGTH ops = LENGTH tys /\
  !i. i < LENGTH tys ==>
    ^completed cx start current (EL i tys) (EL i flags)
      (EL i values) (EL i ops) s``;

Theorem intcall_completed_store_effect:
  ^completed cx start sa ty flag v op s /\
  (~flag ==> !tv. evaluate_type (get_tenv cx) ty = SOME tv ==> val_wf tv v) /\
  typed_copy_effect ctx func sa sb s u dst sz /\
  sa.cs_next_id <= sb.cs_next_id /\ sa.cs_next_var <= sb.cs_next_var /\
  (!aid w len. ~flag /\ eval_operand op s = SOME w /\
    FLOOKUP s.vs_allocas aid = SOME (w2n w,len) /\
    start.cs_next_id <= aid /\ aid < sa.cs_next_id ==>
    regions_disjoint (w2n w) len dst sz) ==>
  ^completed cx start sb ty flag v op u
Proof
  BETA_TAC >> strip_tac >>
  `eval_operand op u = eval_operand op s` by
    (drule typed_copy_effect_operand_preserved >> disch_then irule >> simp[]) >>
  `!x. op = Var x ==> not_fresh_at sb x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  qexistsl_tac [`tv`, `w`] >> simp[] >>
  Cases_on `flag` >> gvs[] >>
  `val_wf tv v` by metis_tac[] >>
  `mem_bytes_at (w2n w) len u.vs_memory =
   mem_bytes_at (w2n w) len s.vs_memory` by
    (irule typed_copy_effect_bytes >>
     metis_tac[compileEnvTheory.regions_disjoint_def]) >>
  conj_tac
  >- (irule val_in_memory_mem_agree >> simp[] >> qexistsl_tac [`len`, `s.vs_memory`] >> simp[]) >>
  drule typed_copy_effect_allocas >> strip_tac >>
  drule typed_copy_effect_record >> strip_tac >>
  `u.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `(u with <|vs_vars := _; vs_memory := _;
       vs_prev_bb := _; vs_current_bb := _; vs_inst_idx := _|>) = s` mp_tac >>
     simp[Once venomStateTheory.venom_state_component_equality]) >>
  qexistsl_tac [`aid`, `len`] >> simp[]
QED

Theorem intcall_completed_prefix_store_effect:
  ^completed_prefix cx start sa tys flags values ops s /\
  (!i tv. i < LENGTH tys /\ ~EL i flags /\
    evaluate_type (get_tenv cx) (EL i tys) = SOME tv ==> val_wf tv (EL i values)) /\
  typed_copy_effect ctx func sa sb s u dst sz /\
  sa.cs_next_id <= sb.cs_next_id /\ sa.cs_next_var <= sb.cs_next_var /\
  (!i aid w len. i < LENGTH tys /\ ~EL i flags /\
    eval_operand (EL i ops) s = SOME w /\
    FLOOKUP s.vs_allocas aid = SOME (w2n w,len) /\
    start.cs_next_id <= aid /\ aid < sa.cs_next_id ==>
    regions_disjoint (w2n w) len dst sz) ==>
  ^completed_prefix cx start sb tys flags values ops u
Proof
  BETA_TAC >> strip_tac >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  irule (BETA_RULE intcall_completed_store_effect) >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`ctx`, `dst`, `func`, `s`, `sa`, `sz`] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >> simp[]
QED
