Theory createCtorTupleCaptureFrame
Ancestors
  targetPurePostTransport exprSimVVFrame exprSimProps exprSimWordArgs valueEncodingProofs
  exprSimSubscriptArrayFrame exprBopSimProps
  loweringPosts loweringStateRelDefs vyperState vyperStorageBackend
  context finite_map words compileEnv valueEncoding
  targetPureSourceFrame exprSimHypsDefs

(* Rebase raw provenance without replacing a local PlaceR by its value. *)
Theorem ctor_capture_at_frame[local]:
  vv_at ce cx ty origin cut es raw vv s /\
  read_result cx raw es = (INL v,es) /\
  read_result cx raw ee = (INL v,ee) /\
  (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==>
     FLOOKUP u.vs_allocas aid = SOME row) /\
  eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s /\
  (!n b sz. local_region ce ee.scopes u n b sz <=>
             local_region ce es.scopes s n b sz) /\
  cut.cs_next_id <= next.cs_next_id ==>
  vv_at ce cx ty origin next ee raw vv u
Proof
  Cases_on `vv` >> simp[vv_at_def, vv_operand_def, expr_val_at_def] >>
  rpt strip_tac >> gvs[]
  >>~- ([`FLOOKUP s.vs_allocas aid = SOME (b,sz)`],
        disj1_tac >> qexistsl [`aid`, `b`, `sz`] >> simp[] >> metis_tac[])
  >>~- ([`local_region ce es.scopes s n b sz`],
        disj2_tac >> disj1_tac >> qexistsl [`n`, `b`, `sz`] >> simp[])
  >> metis_tac[]
QED

(* Oracle and trace observations do not alter any delayed read. *)
Theorem ctor_capture_read_frame[local]:
  es'.scopes = es.scopes /\ es'.immutables = es.immutables /\
  (!tr. get_storage cx es' tr = get_storage cx es tr) ==>
  (read_result cx raw es' = (INL v,es') <=>
   read_result cx raw es = (INL v,es))
Proof
  strip_tac >> Cases_on `raw` >>
  simp[read_result_def, return_def, raise_def] >>
  rename1 `read_place cx p` >> Cases_on `p` >> simp[read_place_def]
  >~ [`read_storage_slot cx tr`]
  >- (simp[vyperStorageBackendTheory.read_storage_slot_eq,
           AllCaseEqs()] >> metis_tac[]) >>
  simp[get_scopes_def, get_immutables_def, get_address_immutables_def,
       bind_def, lift_option_type_def, lift_sum_def, return_def, raise_def,
       vyperMiscTheory.option_CASE_rator, vyperMiscTheory.sum_CASE_rator,
       vyperMiscTheory.prod_CASE_rator, AllCaseEqs()] >> metis_tac[]
QED





Theorem ctor_capture_holds_frame[local]:
  vv_holds ce cx ty raw vv es s /\ vv_at ce cx ty origin endpoint es raw vv s /\
  wb_frame ce es es' cut s u /\ endpoint.cs_next_id <= cut.cs_next_id /\
  es'.scopes = es.scopes /\ es'.immutables = es.immutables /\
  (!tr. get_storage cx es' tr = get_storage cx es tr) /\
  (!p tr w. vv = LocatedValue ty p /\
     p.ptr_location = (if tr then LocTransient else LocStorage) /\
     eval_operand p.ptr_operand s = SOME w /\
     storage_holds cx tr ty raw w es s ==>
     storage_holds cx tr ty raw w es' u) /\
  (!w. eval_operand (vv_operand vv) s = SOME w ==>
       eval_operand (vv_operand vv) u = SOME w) ==>
  vv_holds ce cx ty raw vv es' u
Proof
  strip_tac >>
  `!v. read_result cx raw es' = (INL v,es') <=>
        read_result cx raw es = (INL v,es)` by
    (gen_tac >> irule ctor_capture_read_frame >> simp[]) >>
  Cases_on `vv`
  >- (gvs[vv_holds_def, vv_at_def, vv_operand_def] >>
      irule saved_stack_value_frame >> metis_tac[]) >>
  qpat_x_assum `vv_holds _ _ _ _ _ _ _` mp_tac >>
  simp[vv_holds_def] >>
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `eval_operand p.ptr_operand u = SOME w` by
    (gvs[vv_operand_def] >> metis_tac[]) >>
  simp[] >>
  Cases_on `p.ptr_location` >> simp[] >>
  qpat_x_assum `case _ of LocMemory => _ | LocStorage => _ | LocTransient => _ | LocCode => _ | LocCalldata => _` mp_tac >>
  simp[] >> strip_tac
  >- (simp[] >> gen_tac >> disch_tac >> rename1 `evaluate_type _ ty = SOME tvt` >>
      `mem_bytes_at (w2n w) (val_footprint tvt v) u.vs_memory =
       mem_bytes_at (w2n w) (val_footprint tvt v) s.vs_memory` by
        (irule saved_value_region_bytes >> metis_tac[]) >>
      `val_wf tvt v` by (gvs[vv_at_def] >> metis_tac[]) >>
      conj_tac
      >- (irule val_in_memory_footprint_agree >> simp[] >> qexists `s.vs_memory` >> simp[]) >>
      strip_tac >>
      `val_footprint tvt v = 32` by
        (irule targetPurePostTransportTheory.target_saved_word_footprint >> metis_tac[]) >>
      gvs[valueEncodingDefsTheory.mem_word_at_def,
          valueEncodingDefsTheory.mem_bytes_at_def])
  >- (gvs[vv_operand_def] >> metis_tac[])
  >- (gvs[vv_operand_def] >> metis_tac[]) >>
  gvs[immutable_holds_def] >> metis_tac[]
QED

Theorem ctor_capture_frame:
  vv_holds ce cx ty raw vv es s /\
  vv_at ce cx ty origin endpoint es raw vv s /\
  read_result cx raw es = (INL value,es) /\
  stmt_state_rel H ctx func ce cx es s /\
  stmt_state_rel H' ctx func ce cx es' s' /\
  local_ptrs_reserved ce cut /\ wb_frame ce es es' cut s s' /\
  endpoint.cs_next_id <= cut.cs_next_id /\
  endpoint.cs_next_id <= endpoint'.cs_next_id /\
  es' with <|gas_obs := []; outcomes := NONE; storage_trace := []|> =
    es with <|gas_obs := []; outcomes := NONE; storage_trace := []|> /\
  contract_storage s' = contract_storage s /\
  contract_transient s' = contract_transient s /\
  (!t op. vv = StackValue t op ==>
    (!x. op = Var x ==> not_fresh_at cut x) /\ (!l. op <> Label l)) /\
  (!t p. vv = LocatedValue t p ==>
    (!x. p.ptr_operand = Var x ==> not_fresh_at cut x) /\
    (!l. p.ptr_operand <> Label l)) ==>
  vv_holds ce cx ty raw vv es' s' /\
  vv_at ce cx ty origin endpoint' es' raw vv s' /\
  read_result cx raw es' = (INL value,es')
Proof
  strip_tac >>
  `es'.scopes = es.scopes /\ es'.immutables = es.immutables /\
   (!tr. get_storage cx es' tr = get_storage cx es tr)` by
    (fs[evaluation_state_component_equality] >>
     Cases_on `tr` >> simp[get_storage_def]) >>
  `(!x. vv_operand vv = Var x ==> not_fresh_at cut x) /\
   (!l. vv_operand vv <> Label l)` by
    (Cases_on `vv` >> gvs[vv_operand_def] >> metis_tac[]) >>
  `!w. eval_operand (vv_operand vv) s = SOME w ==>
       eval_operand (vv_operand vv) s' = SOME w` by
    (rpt strip_tac >> irule eval_operand_frame >>
     conj_tac >- simp[] >> qexistsl [`cut`,`s`] >> gvs[wb_frame_def]) >>
  `eval_operand (vv_operand vv) s' = eval_operand (vv_operand vv) s` by
    (Cases_on `vv` >> gvs[vv_holds_def, vv_operand_def, expr_val_rel_def]) >>
  `read_result cx raw es' = (INL value,es')` by
    (drule ctor_capture_read_frame >> simp[]) >>
  `!n b sz. local_region ce es'.scopes s' n b sz <=>
             local_region ce es.scopes s n b sz` by
    (rpt gen_tac >> simp[] >> irule local_region_wb_frame >>
     conj_tac
     >- (qexists `func` >>
         gvs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def]) >>
     qexistsl [`es'`,`cut`] >> simp[]) >>
  `!tr w. eval_operand (vv_operand vv) s = SOME w /\
     storage_holds cx tr ty raw w es s ==>
     storage_holds cx tr ty raw w es' s'` by
    (rpt strip_tac >>
     gvs[storage_holds_def, vyperStorageBackendTheory.read_storage_slot_eq,
         AllCaseEqs()] >> metis_tac[]) >>
  rpt conj_tac
  >- (irule ctor_capture_holds_frame >> metis_tac[vv_operand_def])
  >- (irule ctor_capture_at_frame >> gvs[wb_frame_def] >> metis_tac[]) >>
  simp[]
QED

Theorem ctor_capture_storage_holds_live[local]:
  storage_holds cx tr ty raw w es s /\
  es'.scopes = es.scopes /\ es'.immutables = es.immutables /\
  (!b. get_storage cx es' b = get_storage cx es b) /\
  (!tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    storage_read_live H tr (get_storage cx es tr) w tv) /\
  storage_agree (storage_dead H tr (get_storage cx es' tr))
    (get_storage cx es' tr)
    (if tr then contract_transient u else contract_storage u) ==>
  storage_holds cx tr ty raw w es' u
Proof
  strip_tac >>
  `!v. read_result cx raw es' = (INL v,es') <=>
        read_result cx raw es = (INL v,es)` by
    (gen_tac >> irule ctor_capture_read_frame >> simp[]) >>
  gvs[storage_holds_def, vyperStorageBackendTheory.read_storage_slot_eq,
      AllCaseEqs()] >>
  irule accountsRelPropsTheory.storage_range_agree_of_live >>
  conj_tac >- gvs[accountsRelPropsTheory.storage_range_agree_def] >>
  qexistsl [`H`,`tr`] >> simp[]
QED

Theorem ctor_capture_live_frame:
  vv_holds ce cx ty raw vv es s /\
  vv_at ce cx ty origin endpoint es raw vv s /\
  read_result cx raw es = (INL value,es) /\
  stmt_state_rel H ctx func ce cx es s /\
  stmt_state_rel H ctx func ce cx es' s' /\
  local_ptrs_reserved ce cut /\ wb_frame ce es es' cut s s' /\
  endpoint.cs_next_id <= cut.cs_next_id /\
  endpoint.cs_next_id <= endpoint'.cs_next_id /\
  es' with <|gas_obs := []; outcomes := NONE; storage_trace := []|> =
    es with <|gas_obs := []; outcomes := NONE; storage_trace := []|> /\
  vv_storage_live H cx vv es s /\
  (!t op. vv = StackValue t op ==>
    (!x. op = Var x ==> not_fresh_at cut x) /\ (!l. op <> Label l)) /\
  (!t p. vv = LocatedValue t p ==>
    (!x. p.ptr_operand = Var x ==> not_fresh_at cut x) /\
    (!l. p.ptr_operand <> Label l)) ==>
  vv_holds ce cx ty raw vv es' s' /\
  vv_at ce cx ty origin endpoint' es' raw vv s' /\
  read_result cx raw es' = (INL value,es') /\
  vv_storage_live H cx vv es' s'
Proof
  strip_tac >>
  `es'.scopes = es.scopes /\ es'.immutables = es.immutables /\
   (!tr. get_storage cx es' tr = get_storage cx es tr)` by
    (fs[evaluation_state_component_equality] >>
     Cases_on `tr` >> simp[get_storage_def]) >>
  `(!x. vv_operand vv = Var x ==> not_fresh_at cut x) /\
   (!l. vv_operand vv <> Label l)` by
    (Cases_on `vv` >> gvs[vv_operand_def] >> metis_tac[]) >>
  `!w. eval_operand (vv_operand vv) s = SOME w ==>
       eval_operand (vv_operand vv) s' = SOME w` by
    (rpt strip_tac >> irule eval_operand_frame >>
     conj_tac >- simp[] >> qexistsl [`cut`,`s`] >> gvs[wb_frame_def]) >>
  `eval_operand (vv_operand vv) s' = eval_operand (vv_operand vv) s` by
    (Cases_on `vv` >> gvs[vv_holds_def, vv_operand_def, expr_val_rel_def]) >>
  `read_result cx raw es' = (INL value,es')` by
    (drule ctor_capture_read_frame >> simp[]) >>
  `!n b sz. local_region ce es'.scopes s' n b sz <=>
             local_region ce es.scopes s n b sz` by
    (rpt gen_tac >> simp[] >> irule local_region_wb_frame >>
     conj_tac
     >- (qexists `func` >>
         gvs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def]) >>
     qexistsl [`es'`,`cut`] >> simp[]) >>
  `!p tr w. vv = LocatedValue ty p /\
     p.ptr_location = (if tr then LocTransient else LocStorage) /\
     eval_operand p.ptr_operand s = SOME w /\
     storage_holds cx tr ty raw w es s ==>
     storage_holds cx tr ty raw w es' s'` by
    (rpt strip_tac >> irule ctor_capture_storage_holds_live >>
     qexistsl [`H`,`es`,`s`] >> simp[] >>
     conj_tac
     >- (Cases_on `tr` >> gvs[vv_storage_live_def]) >>
     Cases_on `tr` >>
     gvs[evaluation_state_component_equality,
         exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def,
         storage_rel_def, transient_rel_def, get_storage_def,
         vfmStateTheory.lookup_account_def]) >>
  rpt conj_tac
  >- (irule ctor_capture_holds_frame >> metis_tac[])
  >- (irule ctor_capture_at_frame >> gvs[wb_frame_def] >> metis_tac[])
  >- simp[] >>
  Cases_on `vv` >> gvs[vv_operand_def, vv_storage_live_def]
QED

(* A successful ordinary effect-free child preserves an earlier raw capture.
   Liveness is used only for this internal pure-list induction step. *)
Theorem ctor_capture_pure_child_frame:
  vv_holds ce cx ty raw vv es s /\
  vv_at ce cx ty origin endpoint es raw vv s /\
  read_result cx raw es = (INL value,es) /\
  stmt_state_rel H ctx func ce cx es s /\
  storage_well_formed_on cx es (FST H) /\
  local_ptrs_reserved ce cut /\
  endpoint.cs_next_id <= cut.cs_next_id /\
  cut.cs_next_id <= cfinish.cs_next_id /\
  (!t op. vv = StackValue t op ==>
    (!x. op = Var x ==> not_fresh_at cut x) /\ (!l. op <> Label l)) /\
  (!t p. vv = LocatedValue t p ==>
    (!x. p.ptr_operand = Var x ==> not_fresh_at cut x) /\
    (!l. p.ptr_operand <> Label l)) /\
  expr_body_pre ce cx env child es /\ ~expr_has_effect child /\
  compile_expr ce (expr_type child) child cut = (child_vv,cfinish) /\
  eval_expr cx child es = (INL child_raw,es') /\
  vv_post H ctx func ce cx child es cut cfinish s es' child_raw child_vv s' /\
  vv_storage_live H cx vv es s ==>
  vv_holds ce cx ty raw vv es' s' /\
  vv_at ce cx ty origin cfinish es' raw vv s' /\
  read_result cx raw es' = (INL value,es') /\
  vv_storage_live H cx vv es' s'
Proof
  strip_tac >>
  `es' with <|gas_obs := []; outcomes := NONE; storage_trace := []|> =
   es with <|gas_obs := []; outcomes := NONE; storage_trace := []|>` by
    (irule effect_free_source_projection >> metis_tac[]) >>
  `wb_frame ce es es' cut s s'` by
    (fs[vv_post_def] >> rewrite_tac[wb_frame_def] >> metis_tac[]) >>
  `stmt_state_rel H ctx func ce cx es' s'` by fs[vv_post_def] >>
  irule ctor_capture_live_frame >>
  qexistsl [`ctx`,`cut`,`endpoint`,`es`,`func`,`s`] >>
  simp[]
QED
