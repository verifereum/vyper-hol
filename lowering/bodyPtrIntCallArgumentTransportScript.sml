Theory bodyPtrIntCallArgumentTransport
Ancestors
  bodyPtrIntCallPureReads bodyPtrIntCallStageArgument
  bodyPtrBopRepresentationFrame bodyPtrIfExpAllocSource
  exprSimVVFrame exprSimProps loweringPosts bodyPtrDefs context
  vyperInterpreter vyperState venomState venomExecSemantics
  finite_map list allocaSiteResource venomMemDefs valueEncodingProofs valueEncodingDefs
  abiDecodeStaticProps exprPtrUnwrapFacts abiStaticAggregateProps
  bodyPtrIntCallEntryContracts ghostObservationPtr

(* Source observations, rather than equality of gas/oracle bookkeeping. *)
Theorem intcall_vv_storage_observations:
  vv_storage_live cx vv es s /\
  ee.accounts = es.accounts /\ ee.tStorage = es.tStorage /\
  eval_operand (vv_operand vv) q = eval_operand (vv_operand vv) s ==>
  vv_storage_live cx vv ee q
Proof
  Cases_on `vv` >>
  simp[vv_storage_live_def, vv_operand_def] >>
  rpt strip_tac >> gvs[vyperStorageBackendTheory.get_storage_def]
QED

Theorem intcall_ptr_buf_frame:
  ptr_buf_ok ce e op G s /\
  eval_operand op q = eval_operand op s /\
  (!x. op = Var x ==> FLOOKUP H x = FLOOKUP G x) ==>
  ptr_buf_ok ce e op H q
Proof
  simp[ptr_buf_ok_def] >> metis_tac[]
QED

(* Every byte of an original represented footprint is covered, including
   nested dynamic-array length words.  The compile interval is unchanged. *)
Theorem intcall_vv_at_taint_frame:
  vv_at ce cx ty sa sb es raw vv s /\
  ((?ann op. vv = StackValue ann op /\ ~is_word_type ty) \/
   (?ann p. vv = LocatedValue ann p /\ p.ptr_location = LocMemory)) /\
  read_result cx raw es = (INL v,es) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand (vv_operand vv) s = SOME w /\
  ghost_kept ce es sb G tn s H un ==>
  !i. w2n w <= i /\ i < w2n w + val_footprint tv v /\
      i IN un.t_mem ==> i IN tn.t_mem
Proof
  strip_tac >>
  gvs[vv_at_def, expr_val_at_def, vv_operand_def] >>
  gvs[ghost_kept_def] >> rpt strip_tac
  >>~- ([`FLOOKUP s.vs_allocas aid = SOME (b,sz)`],
    qpat_x_assum `!aid off sz i. FLOOKUP _ _ = _ /\ _ ==> _`
      (qspecl_then [`aid`, `b`, `sz`, `i`] mp_tac) >> simp[] >> metis_tac[])
  >>~- ([`local_region ce es.scopes s n b sz`],
    qpat_x_assum `!n b sz i. local_region _ _ _ _ _ _ /\ _ ==> _`
      (qspecl_then [`n`, `b`, `sz`, `i`] mp_tac) >> simp[]) >>
  gvs[] >> decide_tac
QED

Theorem intcall_vv_at_bytes_frame:
  vv_at ce cx ty sa sb es raw vv s /\
  ((?ann op. vv = StackValue ann op /\ ~is_word_type ty) \/
   (?ann p. vv = LocatedValue ann p /\ p.ptr_location = LocMemory)) /\
  read_result cx raw es = (INL v,es) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand (vv_operand vv) s = SOME w /\
  pure_frame ce fn es sb s q /\ alloca_inv q /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
               FLOOKUP q.vs_allocas aid = SOME entry) ==>
  mem_bytes_at (w2n w) (val_footprint tv v) q.vs_memory =
  mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory
Proof
  strip_tac >>
  gvs[vv_at_def, expr_val_at_def, vv_operand_def]
  >>~- ([`FLOOKUP s.vs_allocas aid = SOME (b,sz)`],
    irule mem_bytes_at_bytewise >> rpt strip_tac >>
    fs[pure_frame_def] >> first_x_assum irule >> rpt strip_tac >>
    `FLOOKUP q.vs_allocas aid = SOME (b,sz)` by metis_tac[] >>
    `aid <> inst.inst_id` by decide_tac >>
    drule_all alloca_site_registered_disjoint >>
    simp[venomMemDefsTheory.regions_disjoint_def,
         loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac)
  >>~- ([`local_region ce es.scopes s n b sz`],
    `mem_bytes_at b sz q.vs_memory = mem_bytes_at b sz s.vs_memory` by
      metis_tac[pure_frame_def] >>
    drule mem_bytes_at_agree_window >> simp[]) >>
  simp[mem_bytes_at_def]
QED

Theorem intcall_read_result_observations_iff:
  ee.scopes = es.scopes /\ ee.accounts = es.accounts /\
  ee.tStorage = es.tStorage /\ ee.immutables = es.immutables ==>
  (read_result cx raw ee = (INL v,ee) <=>
   read_result cx raw es = (INL v,es))
Proof
  metis_tac[intcall_read_result_observations]
QED

Theorem intcall_vv_at_observations:
  ee.scopes = es.scopes /\ ee.accounts = es.accounts /\
  ee.tStorage = es.tStorage /\ ee.immutables = es.immutables ==>
  (vv_at ce cx ty sa sb ee raw vv s <=> vv_at ce cx ty sa sb es raw vv s)
Proof
  strip_tac >>
  `!v. read_result cx raw ee = (INL v,ee) <=>
       read_result cx raw es = (INL v,es)` by
    metis_tac[intcall_read_result_observations_iff] >>
  Cases_on `vv` >> simp[vv_at_def, expr_val_at_def]
QED

(* One physical memory boundary serves both stack buffers and places. *)
Theorem intcall_memory_ptr_frame:
  vv_at ce cx ty sa sb es raw vv s /\
  ((?ann op. vv = StackValue ann op /\ ~is_word_type ty) \/
   (?ann p. vv = LocatedValue ann p /\ p.ptr_location = LocMemory)) /\
  read_result cx raw es = (INL v,es) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  ptr_mem_ok cx ty v (vv_operand vv) G tn s /\
  eval_operand (vv_operand vv) q = eval_operand (vv_operand vv) s /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sb x) /\
  pure_frame ce fn es sb s q /\ alloca_inv q /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
               FLOOKUP q.vs_allocas aid = SOME entry) /\
  ghost_kept ce es sb G tn s H un ==>
  ptr_mem_ok cx ty v (vv_operand vv) H un q
Proof
  strip_tac >>
  (gvs[] >>
   `val_wf tv v` by (gvs[vv_at_def, expr_val_at_def] >> metis_tac[]) >>
   irule bop_ptr_mem_ok_frame >>
   qexistsl_tac [`G`, `s`, `tn`, `tv`] >> simp[] >>
   (conj_tac >- (gvs[ghost_kept_def] >> metis_tac[])) >>
   gen_tac >> disch_tac >>
   (conj_tac >- (irule intcall_vv_at_bytes_frame >> metis_tac[])) >>
   metis_tac[intcall_vv_at_taint_frame])
QED

Theorem intcall_ptr_vv_pure_frame:
  ptr_vv_ok cx ty raw vv es G tn s /\
  vv_at ce cx ty sa sb es raw vv s /\
  (!v. read_result cx raw ee = (INL v,ee) <=>
       read_result cx raw es = (INL v,es)) /\
  eval_operand (vv_operand vv) q = eval_operand (vv_operand vv) s /\
  op_taint un (vv_operand vv) = op_taint tn (vv_operand vv) /\
  op_prov H (vv_operand vv) = op_prov G (vv_operand vv) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sb x) /\
  pure_frame ce fn es sb s q /\ alloca_inv q /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
               FLOOKUP q.vs_allocas aid = SOME entry) /\
  ghost_kept ce es sb G tn s H un /\
  contract_storage q = contract_storage s /\
  contract_transient q = contract_transient s /\
  un.t_stor SUBSET tn.t_stor /\ un.t_trans SUBSET tn.t_trans ==>
  ptr_vv_ok cx ty raw vv ee H un q
Proof
  strip_tac >>
  `!v. read_result cx raw es = (INL v,es) /\
       ((?ann op. vv = StackValue ann op /\ ~is_word_type ty) \/
        (?ann p. vv = LocatedValue ann p /\ p.ptr_location = LocMemory)) ==>
       ptr_mem_ok cx ty v (vv_operand vv) G tn s ==>
       ptr_mem_ok cx ty v (vv_operand vv) H un q` by
    (rpt gen_tac >>
     disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >> disch_tac >>
     Cases_on `evaluate_type (get_tenv cx) ty`
     >- simp[ptr_mem_ok_def] >>
     drule intcall_memory_ptr_frame >>
     disch_then irule >> simp[] >>
     (conj_tac >- metis_tac[]) >>
     qexistsl_tac [`G`, `tn`] >> gvs[]) >>
  Cases_on `vv` >> gvs[vv_operand_def, ptr_vv_ok_def, ptr_val_ok_def] >>
  conj_tac
  >- (strip_tac >> gvs[] >> metis_tac[]) >>
  rpt strip_tac >>
  gvs[venomStateTheory.contract_storage_def, venomStateTheory.contract_transient_def,
      vfmStateTheory.lookup_account_def, pred_setTheory.SUBSET_DEF] >> metis_tac[]
QED

Theorem intcall_vv_holds_observations:
  ee.scopes = es.scopes /\ ee.accounts = es.accounts /\
  ee.tStorage = es.tStorage /\ ee.immutables = es.immutables ==>
  (vv_holds ce cx ty raw vv ee s <=> vv_holds ce cx ty raw vv es s)
Proof
  strip_tac >>
  `!v. read_result cx raw ee = (INL v,ee) <=>
       read_result cx raw es = (INL v,es)` by
    metis_tac[intcall_read_result_observations_iff] >>
  Cases_on `vv` >> simp[vv_holds_def] >>
  rename1 `p.ptr_location` >> Cases_on `p.ptr_location` >>
  simp[storage_holds_def, immutable_holds_def,
       vyperStateTheory.read_storage_slot_def,
       vyperStorageBackendTheory.get_storage_def,
       get_storage_backend_def, bind_def, lift_option_def,
       get_accounts_def, get_transient_storage_def, return_def,
       CaseEq "option", raise_def, COND_RATOR, optionTheory.option_case_compute,
       SF boolSimps.COND_elim_ss]
QED

Theorem intcall_vv_holds_pure_frame:
  vv_holds ce cx ty raw vv es s /\ vv_at ce cx ty sa sb es raw vv s /\
  ~ce.ce_is_ctor /\
  eval_operand (vv_operand vv) q = eval_operand (vv_operand vv) s /\
  pure_frame ce fn es sb s q /\ alloca_inv q /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
               FLOOKUP q.vs_allocas aid = SOME entry) /\
  contract_storage q = contract_storage s /\
  contract_transient q = contract_transient s ==>
  vv_holds ce cx ty raw vv es q
Proof
  strip_tac >>
  `!tv v w. read_result cx raw es = (INL v,es) /\
     evaluate_type (get_tenv cx) ty = SOME tv /\
     eval_operand (vv_operand vv) s = SOME w /\
     ((?ann op. vv = StackValue ann op /\ ~is_word_type ty) \/
      (?ann p. vv = LocatedValue ann p /\ p.ptr_location = LocMemory)) ==>
     val_in_memory tv v (w2n w) s.vs_memory ==>
     val_in_memory tv v (w2n w) q.vs_memory /\
     (is_word_type ty ==> mem_word_at (w2n w) q.vs_memory =
                         mem_word_at (w2n w) s.vs_memory)` by
    (rpt gen_tac >> disch_tac >> disch_tac >>
     `val_wf tv v` by (gvs[vv_at_def, expr_val_at_def, vv_operand_def] >> metis_tac[]) >>
     `mem_bytes_at (w2n w) (val_footprint tv v) q.vs_memory =
      mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory` by
       (drule intcall_vv_at_bytes_frame >> disch_then irule >> metis_tac[]) >>
     (conj_tac >- metis_tac[val_in_memory_footprint_agree]) >>
     strip_tac >>
     `val_footprint tv v = 32` by metis_tac[word_value_memory_extent] >>
     gvs[mem_word_at_bytes]) >>
  Cases_on `vv` >> gvs[vv_holds_def, vv_operand_def, expr_val_rel_def]
  >- (rpt strip_tac >> Cases_on `is_word_type ty` >> gvs[] >> metis_tac[]) >>
  Cases_on `p.ptr_location` >>
  gvs[storage_holds_def, immutable_holds_def] >> metis_tac[]
QED

(* A delayed value retains its own compile interval, not the tail's interval. *)
Theorem intcall_argument_pure_transport:
  vv_holds ce cx ty raw vv es s /\
  vv_at ce cx ty sa sb es raw vv s /\
  vv_storage_live cx vv es s /\ ptr_vv_ok cx ty raw vv es G tn s /\
  (!ann op. vv = StackValue ann op /\ ~is_word_type ty ==>
    ptr_buf_ok ce e op G s) /\
  (!ann p. vv = LocatedValue ann p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\
  ~ce.ce_is_ctor /\
  ee.scopes = es.scopes /\ ee.accounts = es.accounts /\
  ee.tStorage = es.tStorage /\ ee.immutables = es.immutables /\
  eval_operand (vv_operand vv) q = eval_operand (vv_operand vv) s /\
  op_taint un (vv_operand vv) = op_taint tn (vv_operand vv) /\
  op_prov H (vv_operand vv) = op_prov G (vv_operand vv) /\
  (!x. vv_operand vv = Var x ==> FLOOKUP H x = FLOOKUP G x) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sb x) /\
  pure_frame ce fn es sb s q /\ alloca_inv q /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
               FLOOKUP q.vs_allocas aid = SOME entry) /\
  (!n b sz. local_region ce es.scopes q n b sz <=>
             local_region ce es.scopes s n b sz) /\
  ghost_kept ce es sb G tn s H un /\
  contract_storage q = contract_storage s /\
  contract_transient q = contract_transient s /\
  un.t_stor SUBSET tn.t_stor /\ un.t_trans SUBSET tn.t_trans ==>
  vv_holds ce cx ty raw vv ee q /\
  vv_at ce cx ty sa sb ee raw vv q /\
  vv_storage_live cx vv ee q /\ ptr_vv_ok cx ty raw vv ee H un q /\
  (!ann op. vv = StackValue ann op /\ ~is_word_type ty ==>
    ptr_buf_ok ce e op H q) /\
  (!ann p. vv = LocatedValue ann p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand H q)
Proof
  strip_tac >>
  `!v. read_result cx raw ee = (INL v,ee) <=>
       read_result cx raw es = (INL v,es)` by
    metis_tac[intcall_read_result_observations_iff] >>
  (conj_tac >-
    (drule_all intcall_vv_holds_pure_frame >>
     metis_tac[intcall_vv_holds_observations])) >>
  (conj_tac >-
    (`vv_at ce cx ty sa sb es raw vv q` by
       (drule vv_at_alloc_map_frame >>
        disch_then (qspecl_then [`sb`, `q`] mp_tac) >> simp[]) >>
     drule_all intcall_vv_at_observations >> simp[])) >>
  (conj_tac >- (drule_all intcall_vv_storage_observations >> simp[])) >>
  (conj_tac >- (drule_all intcall_ptr_vv_pure_frame >> simp[])) >>
  conj_tac >> rpt strip_tac >>
  irule intcall_ptr_buf_frame >> gvs[vv_operand_def] >> metis_tac[]
QED

(* Counted staging stores publish these two frames at their actual endpoint.
   A reused site is allowed: its instruction identity, not address age, is fresh. *)
Theorem intcall_staging_write_frames:
  MEM (mk_inst aid ALLOCA ops outs) (fn_insts fn) /\
  sb.cs_next_id <= aid /\ FLOOKUP q.vs_allocas aid = SOME (b,n) /\
  (!name a k. local_region ce es.scopes s name a k ==>
    regions_disjoint b n a k) /\
  (!off len. regions_disjoint off len b n ==>
    mem_bytes_at off len q.vs_memory = mem_bytes_at off len s.vs_memory) /\
  intcall_site_outside (intcall_protected ce es sb s) (b,n) /\
  (!x. not_fresh_at sb x ==>
    FLOOKUP H x = FLOOKUP G x /\ op_taint un (Var x) = op_taint tn (Var x)) /\
  (!i. ~(b <= i /\ i < b+n) /\ i IN un.t_mem ==> i IN tn.t_mem) ==>
  pure_frame ce fn es sb s q /\ ghost_kept ce es sb G tn s H un
Proof
  strip_tac >> conj_tac
  >- (irule pure_frame_fresh_alloca >>
      conj_tac
      >- (rpt strip_tac >> first_x_assum irule >>
          fs[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
      qexistsl_tac [`b`, `aid`, `ops`, `outs`, `n`] >> simp[]) >>
  simp[bodyPtrIntCallConfinementTheory.intcall_ghost_kept_frame] >>
  fs[bodyPtrIntCallConfinementTheory.intcall_mem_frame_def,
     bodyPtrIntCallConfinementTheory.intcall_site_outside_def,
     pred_setTheory.IN_DISJOINT, pred_setTheory.SUBSET_DEF] >>
  rpt strip_tac >> first_x_assum irule >> simp[] >> metis_tac[]
QED

(* Exterior framing uses the represented footprint, not the allocation age.
   Thus it also applies when a staging ALLOCA reuses its instruction's site. *)
Theorem intcall_local_value_exterior_transport:
  intcall_local_value entry p sz G tn s /\
  lookup_var p t = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
  op_taint un (Var p) = op_taint tn (Var p) /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!w i. lookup_var p s = SOME w /\
    w2n w <= i /\ i < w2n w + val_footprint entry.type entry.value ==>
    i NOTIN R) /\
  (!i. i NOTIN R ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
  (!i. i NOTIN R /\ i IN un.t_mem ==> i IN tn.t_mem) ==>
  intcall_local_value entry p sz H un t
Proof
  strip_tac >> fs[intcall_local_value_def] >>
  conj_tac >- metis_tac[ptr_covers_def] >>
  rpt strip_tac >> irule robust_val_in_memory_exterior_no_new_taint >>
  conj_tac >- simp[] >>
  qexistsl_tac [`R`, `s.vs_memory`, `t.vs_memory`, `tn.t_mem`, `un.t_mem`] >>
  simp[]
QED

Theorem intcall_completed_exterior_transport:
  intcall_completed env ce G tn s /\
  (!p sz name. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    lookup_var p t = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
    op_taint un (Var p) = op_taint tn (Var p)) /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!name entry p sz w i. FLOOKUP env name = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w /\ w2n w <= i /\
    i < w2n w + val_footprint entry.type entry.value ==> i NOTIN R) /\
  (!i. i NOTIN R ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
  (!i. i NOTIN R /\ i IN un.t_mem ==> i IN tn.t_mem) ==>
  intcall_completed env ce H un t
Proof
  strip_tac >> simp[intcall_completed_def] >> rpt strip_tac >>
  qpat_x_assum `intcall_completed _ _ _ _ _` mp_tac >>
  simp[intcall_completed_def] >> disch_then drule >> strip_tac >>
  qexistsl_tac [`p`, `sz`] >> simp[] >>
  irule intcall_local_value_exterior_transport >>
  qexistsl_tac [`G`, `R`, `s`, `tn`] >> simp[] >> metis_tac[]
QED

Theorem intcall_pending_exterior_transport:
  intcall_pending env ce caps G tn s /\
  (!op. MEM op (MAP (SND o SND) caps) ==>
    eval_operand op t = eval_operand op s /\
    op_taint un op = op_taint tn op /\
    (!p. op = Var p ==> FLOOKUP H p = FLOOKUP G p)) /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!name stack op entry w i. MEM (name,stack,op) caps /\ ~stack /\
    FLOOKUP env name = SOME entry /\ eval_operand op s = SOME w /\
    w2n w <= i /\ i < w2n w + val_footprint entry.type entry.value ==>
    i NOTIN R) /\
  (!i. i NOTIN R ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
  (!i. i NOTIN R /\ i IN un.t_mem ==> i IN tn.t_mem) ==>
  intcall_pending env ce caps H un t
Proof
  strip_tac >> simp[intcall_pending_def, EVERY_MEM] >>
  gen_tac >> strip_tac >> PairCases_on `e` >> gvs[] >>
  qpat_x_assum `intcall_pending _ _ _ _ _ _` mp_tac >>
  simp[intcall_pending_def, EVERY_MEM] >>
  disch_then (qspec_then `(e0,e1,e2)` mp_tac) >> simp[] >> strip_tac >>
  `MEM e2 (MAP (SND o SND) caps)` by
    (simp[MEM_MAP] >> qexists_tac `(e0,e1,e2)` >> simp[]) >>
  qpat_x_assum `!op. MEM op _ ==> _` drule >> strip_tac >>
  qexistsl_tac [`entry`, `off`, `sz`, `w`] >> simp[] >>
  Cases_on `e1` >> gvs[] >>
  irule intcall_local_value_exterior_transport >>
  qexistsl_tac [`G`, `R`, `s`, `tn`] >>
  gvs[eval_operand_def] >> metis_tac[eval_operand_def]
QED
