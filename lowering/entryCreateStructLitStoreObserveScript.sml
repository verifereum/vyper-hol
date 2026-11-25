(* Interpret the aggregate field's semantic supplier at the selected store
   endpoint. The administrative visit cut does not depend on that endpoint. *)
Theory entryCreateStructLitStoreObserve
Ancestors
  bodyFullStructLit bodyFullIfExpObserve entryCreateStructLitAggregateStore
  entryCreateIfExpTypedStore entryCreateFocusSpec entryCreateBodyCut
  createSizeCutRegion fragFuel logStoreDataOriginPtr venomRunBounded

Triviality structlit_typed_store_visit_cut:
  compile_store_memory_typed ce (Var xd) dty (Var xs) sty sa = ((),sb) /\
  structlit_aggregate_store_pre ce tenv sty dty stv dtv v sa sb ctx f lo
    s G tn xs xd sw dw ==>
  create_operand_cut sa sb E ctx f tops cx st0 source (es,s)
Proof
  simp_tac bool_ss [structlit_aggregate_store_pre_def] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_assum `create_operand_at sa s`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [create_operand_at_def]) >>
  mp_tac (Q.INST [`cenv` |-> `ce`, `func` |-> `f`, `explicit` |-> `E`]
    ifexp_typed_store_selected_site) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >> rw[create_operand_cut_def] >>
  first_x_assum drule >> strip_tac >>
  gvs[create_body_cut_def, inst_create_size_ok_def]
QED

Triviality structlit_typed_store_from_observation:
  ifexp_observed_typed_store
    (\ctx f a b s t. create_layout a b /\ no_phi_fn f ==>
       create_operand_at a s /\ create_operand_full_scope a b E ctx f s [] (OK t)) /\
  create_layout sa sb /\ no_phi_fn f /\
  compile_store_memory_typed ce (Var xd) dty (Var xs) sty sa = ((),sb) /\
  structlit_aggregate_store_pre ce tenv sty dty stv dtv v sa sb ctx f lo
    s G tn xs xd sw dw ==>
  ?t Gf tnf.
    structlit_aggregate_store_post lo E ctx f PG s G tn sa sb dtv v dw t Gf tnf /\
    create_operand_full_scope sa sb E ctx f s [] (OK t) /\
    create_operand_cut sa sb E ctx f tops cx st0 source (es,s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all structlit_typed_store_visit_cut >> strip_tac >>
  qhdtm_x_assum `structlit_aggregate_store_pre`
    (REPEAT_TCL CONJUNCTS_THEN assume_tac o
       REWRITE_RULE [structlit_aggregate_store_pre_def, create_operand_at_def]) >>
  qpat_x_assum `ifexp_observed_typed_store _`
    (mp_tac o REWRITE_RULE [ifexp_observed_typed_store_def]) >>
  disch_then (qspecl_then [`ce`,`xd`,`dty`,`xs`,`sty`,`sa`,`sb`,`tenv`,
    `stv`,`dtv`,`v`,`s`,`sw`,`dw`,`G`,`tn`,`lo`,`ctx`,`f`,`E`,`PG`] mp_tac) >>
  simp_tac bool_ss [] >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp_tac bool_ss [] >>
  disch_then (REPEAT_TCL CHOOSE_THEN (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >>
  simp[structlit_aggregate_store_post_def, create_operand_at_def] >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >> first_assum ACCEPT_TAC
QED

Theorem structlit_aggregate_observation_from_typed:
  (!ce tenv sty dty stv dtv v sa sb ctx f lo s G tn xs xd sw dw E PG
      tops cx st0 (source : evaluation_state -> 'a evaluation_result) es.
    (compile_store_memory_typed ce (Var xd) dty (Var xs) sty sa = ((),sb) ==>
     ?t Gf tnf.
       structlit_aggregate_store_post lo E ctx f PG s G tn sa sb dtv v dw t Gf tnf /\
       create_operand_full_scope sa sb E ctx f s [] (OK t) /\
       create_operand_cut sa sb E ctx f tops cx st0 source (es,s)) /\
    compile_store_memory ce (Var xs) (Var xd) dty sty sa = ((),sb) /\
    ~is_word_type dty /\ ~is_bytestring_type dty /\ 0 < type_memory_size stv /\
    type_memory_bytes ce dty = type_memory_size dtv /\
    structlit_aggregate_store_pre ce tenv sty dty stv dtv v sa sb ctx f lo
      s G tn xs xd sw dw ==>
    ?t Gf tnf.
      structlit_aggregate_store_post lo E ctx f PG s G tn sa sb dtv v dw t Gf tnf /\
      create_operand_full_scope sa sb E ctx f s [] (OK t) /\
      create_operand_cut sa sb E ctx f tops cx st0 source (es,s)) /\
  ifexp_observed_typed_store
    (\ctx f a b s t. create_layout a b /\ no_phi_fn f ==>
       create_operand_at a s /\ create_operand_full_scope a b E ctx f s [] (OK t)) ==>
  structlit_aggregate_store_observed
    (\a b s t. create_layout a b /\ no_phi_fn f ==>
       create_operand_full_scope a b E ctx f s [] (OK t) /\
       !tops cx st0 (source : evaluation_state -> 'a evaluation_result) es. create_operand_cut a b E ctx f tops cx st0 source (es,s))
    ctx f E
Proof
  simp_tac bool_ss [structlit_aggregate_store_observed_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  rename1 `compile_store_memory ce (Var xs) (Var xd) dty sty sa = ((),sb)` >>
  Cases_on `create_layout sa sb /\ no_phi_fn f`
  >- (qpat_x_assum `create_layout sa sb /\ no_phi_fn f` strip_assume_tac >>
      `structlit_aggregate_store_pre ce tenv sty dty stv dtv v sa sb ctx f lo
        s G tn xs xd sw dw` by
        (rewrite_tac[structlit_aggregate_store_pre_def, create_operand_at_def] >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `!tops cx st0 (source : evaluation_state -> 'a evaluation_result) es. ?t Gf tnf.
        structlit_aggregate_store_post lo E ctx f PG s G tn sa sb dtv v dw t Gf tnf /\
        create_operand_full_scope sa sb E ctx f s [] (OK t) /\
        create_operand_cut sa sb E ctx f tops cx st0 source (es,s)` by
        (rpt gen_tac >> first_x_assum irule >> rpt (first_assum (irule_at Any)) >>
         strip_tac >> irule structlit_typed_store_from_observation >>
         rpt (first_assum (irule_at Any))) >>
      `!tops cx st0 (source : evaluation_state -> 'a evaluation_result) es. create_operand_cut sa sb E ctx f tops cx st0 source (es,s)` by
        (rpt gen_tac >>
         qpat_assum `!tops cx st0 (source : evaluation_state -> 'a evaluation_result) es. ?t Gf tnf. _`
           (qspecl_then [`tops`,`cx`,`st0`,`source`,`es`] strip_assume_tac) >>
         first_assum ACCEPT_TAC) >>
      qpat_x_assum `!tops cx st0 (source : evaluation_state -> 'a evaluation_result) es. ?t Gf tnf. _`
        (strip_assume_tac o SPEC_ALL) >>
      qexistsl_tac [`t`,`Gf`,`tnf`] >>
      qhdtm_x_assum `structlit_aggregate_store_post`
        (REPEAT_TCL CONJUNCTS_THEN assume_tac o
         SIMP_RULE bool_ss [structlit_aggregate_store_post_def, create_operand_at_def]) >>
      conj_tac
      >- (disch_tac >> asm_rewrite_tac[]) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all compile_store_memory_origin_ptr_path >>
  disch_then (qspecl_then [`E`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >> simp[]
QED
