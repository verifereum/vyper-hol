(* Value resources at the endpoint of the concrete RaiseReason head. *)
Theory bodyFullRaiseReasonHeadValue
Ancestors
  bodyFullRaiseReasonHeadGhost bodyFullRaiseReasonHead
  stmtReasonMemory revertReasonLayout revertReasonPrefixFramePtr
  exprSimVVFrame exprSimIfExpWidenedAdapter exprSimProps exprLoweringProps
  valueEncodingProofs valueTypingMemoryProps
  loweringPosts exprLowering exprSimMemDefs loweringStateRelDefs
  bodyPtrDefs context venomState finite_map words arithmetic
  allocaSiteResource venomMemDefs abiEncoderZeroFrame pred_set
  bodyPtrBopRepresentationFrame logValueFramePtr ptrDiscipline
  revertReasonPrefixPtr venomExecSemantics venomInst venomMemProps

Theorem reason_head_operand_frame:
  (!x k. op = Var x /\ k < 3 ==>
    x <> STRING #"%" (toString (v+k))) /\
  run_inst_seq (reason_head id v M) s = OK t ==>
  eval_operand op t = eval_operand op s
Proof
  strip_tac >>
  `run_inst_seq (revert_reason_prefix id v M) s = OK t` by
    fs[reason_head_def, revert_reason_prefix_def] >>
  drule revert_reason_prefix_labels_frame >> strip_tac >>
  Cases_on `op` >> simp[eval_operand_def] >>
  irule revert_reason_prefix_lookup_frame >> metis_tac[]
QED

Theorem reason_head_local_regions:
  (!k. k < 3 ==> not_local_ptr cenv scopes (STRING #"%" (toString (v+k)))) /\
  run_inst_seq (reason_head id v M) s = OK t ==>
  !n b sz. local_region cenv scopes t n b sz <=>
           local_region cenv scopes s n b sz
Proof
  strip_tac >>
  `run_inst_seq (revert_reason_prefix id v M) s = OK t` by
    fs[reason_head_def, revert_reason_prefix_def] >>
  `!x. (!k. k < 3 ==> x <> STRING #"%" (toString (v+k))) ==>
       lookup_var x t = lookup_var x s` by
    metis_tac[revert_reason_prefix_lookup_frame] >>
  simp[local_region_def] >> rpt gen_tac >>
  `!entry p sz. lookup_scopes n scopes = SOME entry /\
    FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var p) sz) ==>
    lookup_var p t = lookup_var p s` by
    (rpt strip_tac >> first_x_assum irule >> rpt strip_tac >>
     fs[not_local_ptr_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem reason_head_vv_at_own:
  vv_at cenv cx ty sa sm es tv vv s /\
  vv_own cenv cx ty sa sm es tv vv s /\
  (!x k. vv_operand vv = Var x /\ k < 3 ==>
    x <> STRING #"%" (toString (v+k))) /\
  (!k. k < 3 ==> not_local_ptr cenv es.scopes (STRING #"%" (toString (v+k)))) /\
  run_inst_seq (reason_head id v M) s = OK t ==>
  vv_at cenv cx ty sa sm es tv vv t /\
  vv_own cenv cx ty sa sm es tv vv t
Proof
  strip_tac >>
  drule_all reason_head_operand_frame >> strip_tac >>
  drule_all reason_head_local_regions >> strip_tac >>
  `!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP t.vs_allocas aid = SOME entry` by
    (`run_inst_seq (revert_reason_prefix id v M) s = OK t` by
       fs[reason_head_def, revert_reason_prefix_def] >>
     drule revert_reason_prefix_allocation_frame >> simp[]) >>
  conj_tac
  >- (irule vv_at_alloc_mono_frame >> qexistsl_tac [`s`, `sm`] >> simp[]) >>
  irule vv_own_alloc_mono_frame >> qexistsl_tac [`s`, `sm`] >> simp[]
QED

Theorem reason_head_vv_storage_live:
  vv_storage_live H cx vv es s /\
  (!x k. vv_operand vv = Var x /\ k < 3 ==>
    x <> STRING #"%" (toString (v+k))) /\
  run_inst_seq (reason_head id v M) s = OK t ==>
  vv_storage_live H cx vv es t
Proof
  strip_tac >> drule_all reason_head_operand_frame >> strip_tac >>
  Cases_on `vv` >> fs[vv_operand_def] >> metis_tac[]
QED

Theorem reason_head_ptr_buf_ok:
  ptr_buf_ok cenv e op G s /\
  (!x k. op = Var x /\ k < 3 ==>
    x <> STRING #"%" (toString (v+k))) /\
  run_inst_seq (reason_head id v M) s = OK t /\
  inst_seq_ptr D lo ctx func PG G tn (reason_head id v M) s Gf tnf ==>
  ptr_buf_ok cenv e op Gf t
Proof
  strip_tac >> drule_all reason_head_operand_frame >> strip_tac >>
  `inst_seq_ptr D lo ctx func PG G tn (revert_reason_prefix id v M) s Gf tnf` by
    fs[reason_head_def, revert_reason_prefix_def] >>
  drule revert_reason_prefix_ghost_observations >> strip_tac >>
  fs[ptr_buf_ok_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl_tac [`x`, `b`, `sz`] >> simp[] >>
  metis_tac[]
QED

(* The complete old value window, not only the encoder's length word. *)
Theorem reason_head_region_exterior:
  stmt_state_rel H ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  MEM (mk_inst id ALLOCA [Lit (n2w (64+M))]
    [STRING #"%" (toString v)]) (fn_insts func) /\
  MEM (mk_inst (id+3) ALLOCA [Lit (n2w M)]
    [STRING #"%" (toString (v+2))]) (fn_insts func) /\
  (!k. k < 3 ==> not_local_ptr cenv es.scopes (STRING #"%" (toString (v+k)))) /\
  64+M < dimword (:256) /\
  run_inst_seq (reason_head id v M) s = OK t /\ alloca_inv t /\
  FLOOKUP t.vs_allocas id = SOME (b,64+M) /\
  FLOOKUP t.vs_allocas (id+3) = SOME (c,M) /\
  ((?aid a sz. FLOOKUP s.vs_allocas aid = SOME (a,sz) /\ aid < id /\
      a <= addr /\ addr+len <= a+sz) \/
   (?name a sz. local_region cenv es.scopes s name a sz /\
      a <= addr /\ addr+len <= a+sz)) /\
  addr <= i /\ i < addr+len ==>
  i NOTIN ({i | b <= i /\ i < b+(64+M)} UNION {i | c <= i /\ i < c+M})
Proof
  strip_tac >>
  `run_inst_seq (revert_reason_prefix id v M) s = OK t` by
    fs[reason_head_def, revert_reason_prefix_def]
  >- (`FLOOKUP t.vs_allocas aid = SOME (a,sz)` by
        (drule revert_reason_prefix_allocation_frame >> disch_then irule >> simp[]) >>
      `aid <> id /\ aid <> id+3` by decide_tac >>
      `venomMemDefs$regions_disjoint (a,sz) (b,64+M)` by
        (irule alloca_site_registered_disjoint >> metis_tac[]) >>
      `venomMemDefs$regions_disjoint (a,sz) (c,M)` by
        (irule alloca_site_registered_disjoint >> metis_tac[]) >>
      fs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `a <= i /\ i < a+sz` by decide_tac >>
  drule_all revert_reason_prefix_local_exterior >> simp[]
QED

Theorem reason_head_region_frame:
  stmt_state_rel H ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  MEM (mk_inst id ALLOCA [Lit (n2w (64+M))]
    [STRING #"%" (toString v)]) (fn_insts func) /\
  MEM (mk_inst (id+3) ALLOCA [Lit (n2w M)]
    [STRING #"%" (toString (v+2))]) (fn_insts func) /\
  (!k. k < 3 ==> not_local_ptr cenv es.scopes (STRING #"%" (toString (v+k)))) /\
  64+M < dimword (:256) /\
  run_inst_seq (reason_head id v M) s = OK t /\ alloca_inv t /\
  inst_seq_ptr D lo ctx func PG G tn (reason_head id v M) s Gf tnf /\
  ((?aid a sz. FLOOKUP s.vs_allocas aid = SOME (a,sz) /\ aid < id /\
      a <= addr /\ addr+len <= a+sz) \/
   (?name a sz. local_region cenv es.scopes s name a sz /\
      a <= addr /\ addr+len <= a+sz)) ==>
  mem_bytes_at addr len t.vs_memory = mem_bytes_at addr len s.vs_memory /\
  (!i. addr <= i /\ i < addr+len /\ i IN tnf.t_mem ==> i IN tn.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `run_inst_seq (revert_reason_prefix id v M) s = OK t /\
   inst_seq_ptr D lo ctx func PG G tn (revert_reason_prefix id v M) s Gf tnf` by
    fs[reason_head_def, revert_reason_prefix_def] >>
  drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)
    revert_reason_prefix_memory_effects >> disch_then drule >>
  disch_then (qspec_then `t` mp_tac) >> impl_tac >- simp[ADD_COMM] >> strip_tac >>
  `!i. addr <= i /\ i < addr+len ==>
    i NOTIN ({i | b <= i /\ i < b+(64+M)} UNION {i | c <= i /\ i < c+M})` by
    (metis_tac[reason_head_region_exterior]) >>
  conj_tac
  >- (irule abi_encoder_mem_bytes_singletons >> metis_tac[]) >>
  metis_tac[]
QED

Theorem reason_head_value_bytes:
  stmt_state_rel H ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  MEM (mk_inst id ALLOCA [Lit (n2w (64+M))]
    [STRING #"%" (toString vn)]) (fn_insts func) /\
  MEM (mk_inst (id+3) ALLOCA [Lit (n2w M)]
    [STRING #"%" (toString (vn+2))]) (fn_insts func) /\
  (!k. k < 3 ==> not_local_ptr cenv es.scopes (STRING #"%" (toString (vn+k)))) /\
  64+M < dimword (:256) /\ sm.cs_next_id <= id /\
  run_inst_seq (reason_head id vn M) s = OK t /\ alloca_inv t /\
  inst_seq_ptr D lo ctx func PG G tn (reason_head id vn M) s Gf tnf /\
  vv_at cenv cx ty sa sm es raw vv s /\
  ((?ty'. vv = StackValue ty' op /\ ~is_word_type ty) \/
   (?ty' p. vv = LocatedValue ty' p /\ p.ptr_location = LocMemory /\ p.ptr_operand = op)) /\
  read_result cx raw es = (INL val, es) /\
  evaluate_type (get_tenv cx) ty = SOME rt /\ eval_operand op s = SOME w ==>
  val_wf rt val /\
  mem_bytes_at (w2n w) (val_footprint rt val) t.vs_memory =
    mem_bytes_at (w2n w) (val_footprint rt val) s.vs_memory /\
  (!i. w2n w <= i /\ i < w2n w + val_footprint rt val /\
       i IN tnf.t_mem ==> i IN tn.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`) reason_head_region_frame >>
  disch_then drule >> disch_then (qspec_then `t` mp_tac) >>
  disch_then (qspecl_then [`val_footprint rt val`, `w2n w`] assume_tac) >>
  gvs[vv_at_def, expr_val_at_def] >>
  (Cases_on `val_footprint rt val = 0`
   >- (simp[valueEncodingDefsTheory.mem_bytes_at_def] >> rpt strip_tac >>
       qpat_x_assum `i < w2n w` mp_tac >>
       qpat_x_assum `w2n w <= i` mp_tac >> simp[GSYM NOT_LESS]) >>
   gvs[] >> first_x_assum irule >> simp[])
  >>~- ([`FLOOKUP s.vs_allocas aid = SOME (b,sz)`],
        disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >> decide_tac)
  >>~- ([`local_region cenv es.scopes s n b sz`],
        disj2_tac >> qexistsl_tac [`n`, `b`, `sz`] >> simp[])
QED

Theorem reason_head_vv_holds:
  stmt_state_rel H ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  MEM (mk_inst id ALLOCA [Lit (n2w (64+M))]
    [STRING #"%" (toString vn)]) (fn_insts func) /\
  MEM (mk_inst (id+3) ALLOCA [Lit (n2w M)]
    [STRING #"%" (toString (vn+2))]) (fn_insts func) /\
  (!k. k < 3 ==> not_local_ptr cenv es.scopes (STRING #"%" (toString (vn+k)))) /\
  (!x k. vv_operand vv = Var x /\ k < 3 ==>
    x <> STRING #"%" (toString (vn+k))) /\
  64+M < dimword (:256) /\ sm.cs_next_id <= id /\
  run_inst_seq (reason_head id vn M) s = OK t /\ alloca_inv t /\
  inst_seq_ptr D lo ctx func PG G tn (reason_head id vn M) s Gf tnf /\
  vv_at cenv cx ty sa sm es raw vv s /\
  vv_holds cenv cx ty raw vv es s /\
  (!rt val. evaluate_type (get_tenv cx) ty = SOME rt /\
    read_result cx raw es = (INL val,es) ==> value_has_type rt val) ==>
  vv_holds cenv cx ty raw vv es t
Proof
  strip_tac >>
  drule_all reason_head_operand_frame >> strip_tac >>
  `run_inst_seq (revert_reason_prefix id vn M) s = OK t` by
    fs[reason_head_def, revert_reason_prefix_def] >>
  drule revert_reason_prefix_data_frame >> strip_tac >>
  `!op rt val w.
    ((?ty'. vv = StackValue ty' op /\ ~is_word_type ty) \/
     (?ty' p. vv = LocatedValue ty' p /\ p.ptr_location = LocMemory /\ p.ptr_operand = op)) /\
    read_result cx raw es = (INL val,es) /\
    evaluate_type (get_tenv cx) ty = SOME rt /\ eval_operand op s = SOME w /\
    val_in_memory rt val (w2n w) s.vs_memory ==>
    val_in_memory rt val (w2n w) t.vs_memory` by
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     `val_wf rt val /\
      mem_bytes_at (w2n w) (val_footprint rt val) t.vs_memory =
      mem_bytes_at (w2n w) (val_footprint rt val) s.vs_memory` by
       (drule_all reason_head_value_bytes >> simp[]) >>
     irule exprSimPropsTheory.val_in_memory_footprint_agree >>
     simp[] >> qexists_tac `s.vs_memory` >> simp[]) >>
  Cases_on `vv` >> fs[vv_operand_def, vv_holds_def, expr_val_rel_def]
  >- (Cases_on `is_word_type ty` >> simp[] >> metis_tac[]) >>
  Cases_on `p.ptr_location` >>
  fs[storage_holds_def, immutable_holds_def,
     contract_storage_def, contract_transient_def] >>
  rpt strip_tac >> metis_tac[exprSimPropsTheory.val_in_memory_word_type]
QED

Theorem reason_head_pure_frame:
  stmt_state_rel H ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  MEM (mk_inst id ALLOCA [Lit (n2w (64+M))]
    [STRING #"%" (toString vn)]) (fn_insts func) /\
  MEM (mk_inst (id+3) ALLOCA [Lit (n2w M)]
    [STRING #"%" (toString (vn+2))]) (fn_insts func) /\
  (!k. k < 3 ==> not_local_ptr cenv es.scopes (STRING #"%" (toString (vn+k)))) /\
  64+M < dimword (:256) /\ sm.cs_next_id <= id /\
  run_inst_seq (reason_head id vn M) s = OK t /\ alloca_inv t /\
  inst_seq_ptr D lo ctx func PG G tn (reason_head id vn M) s Gf tnf ==>
  pure_frame cenv func es sm s t
Proof
  strip_tac >>
  `!name b sz. local_region cenv es.scopes s name b sz ==>
    mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory` by
    (rpt strip_tac >>
     drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`) reason_head_region_frame >>
     disch_then drule >> disch_then (qspec_then `t` mp_tac) >>
     disch_then (qspecl_then [`sz`, `b`] mp_tac) >>
     impl_tac >- (simp[] >> disj2_tac >> qexistsl_tac [`name`, `b`, `sz`] >> simp[]) >> simp[]) >>
  `run_inst_seq (revert_reason_prefix id vn M) s = OK t /\
   inst_seq_ptr D lo ctx func PG G tn (revert_reason_prefix id vn M) s Gf tnf` by
    fs[reason_head_def, revert_reason_prefix_def] >>
  drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)
    revert_reason_prefix_memory_effects >> disch_then drule >>
  disch_then (qspec_then `t` mp_tac) >> impl_tac >- simp[ADD_COMM] >> strip_tac >>
  rewrite_tac[pure_frame_def] >> conj_tac >- metis_tac[] >> rpt strip_tac >>
  `regions_disjoint off len b (64+M) /\ regions_disjoint off len c M` by
    (first_x_assum (fn th =>
      mp_tac (Q.SPECL [`mk_inst id ALLOCA [Lit (n2w (64+M))] [STRING #"%" (toString (vn:num))]`, `b`, `64+M`] th) >>
      mp_tac (Q.SPECL [`mk_inst (id+3) ALLOCA [Lit (n2w M)] [STRING #"%" (toString ((vn:num)+2))]`, `c`, `M`] th)) >>
     fs[venomInstTheory.mk_inst_def] >> decide_tac) >>
  irule abi_encoder_mem_bytes_singletons >> rpt strip_tac >>
  qpat_assum `!i. _ ==> mem_bytes_at i 1 _ = _` irule >>
  fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem reason_head_vv_post:
  vv_post H ctx func cenv cx e es sa sm s0 ee tv vv s /\
  fn_inst_ids_distinct func /\
  MEM (mk_inst id ALLOCA [Lit (n2w (64+M))]
    [STRING #"%" (toString vn)]) (fn_insts func) /\
  MEM (mk_inst (id+3) ALLOCA [Lit (n2w M)]
    [STRING #"%" (toString (vn+2))]) (fn_insts func) /\
  (!k. k < 3 ==> not_local_ptr cenv ee.scopes (STRING #"%" (toString (vn+k)))) /\
  (!x k. vv_operand vv = Var x /\ k < 3 ==>
    x <> STRING #"%" (toString (vn+k))) /\
  (!x k. not_fresh_at sa x /\ k < 3 ==>
    x <> STRING #"%" (toString (vn+k))) /\
  64+M < dimword (:256) /\ sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id <= id /\
  local_ptrs_reserved cenv sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  (!rt val. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
    read_result cx tv ee = (INL val,ee) ==> value_has_type rt val) /\
  run_inst_seq (reason_head id vn M) s = OK t /\ alloca_inv t /\
  inst_seq_ptr D lo ctx func PG G tn (reason_head id vn M) s Gf tnf ==>
  vv_post H ctx func cenv cx e es sa sm s0 ee tv vv t
Proof
  strip_tac >>
  `run_inst_seq (revert_reason_prefix id vn M) s = OK t` by
    fs[reason_head_def, revert_reason_prefix_def] >>
  `!aid site. FLOOKUP s.vs_allocas aid = SOME site ==>
    FLOOKUP t.vs_allocas aid = SOME site` by
    metis_tac[revert_reason_prefix_allocation_frame] >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by
    metis_tac[revert_reason_prefix_lookup_frame] >>
  `!n b sz. local_region cenv ee.scopes t n b sz <=>
    local_region cenv ee.scopes s n b sz` by
    metis_tac[reason_head_local_regions] >>
  `eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s` by
    (drule_at (Pat `run_inst_seq _ _ = _`) reason_head_operand_frame >>
     disch_then (qspec_then `vv_operand vv` mp_tac) >>
     impl_tac >- (qpat_x_assum `!x k. vv_operand vv = Var x /\ _ ==> _` mp_tac >>
                  simp[ADD_COMM]) >> simp[]) >>
  fs[vv_post_def] >>
  rpt conj_tac
  >- (irule revertReasonPrefixPtrTheory.revert_reason_prefix_state_rel >>
      simp[] >> qexistsl_tac [`id`, `M`, `s`, `vn`] >> simp[ADD_COMM])
  >- (drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`) reason_head_vv_holds >>
      disch_then drule >>
      disch_then (drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`)) >>
      disch_then (qspec_then `t` mp_tac) >>
      impl_tac >- (simp[ADD_COMM] >> metis_tac[]) >> simp[])
  >- suspend "at"
  >- (strip_tac >> irule vv_own_alloc_mono_frame >>
      qexistsl_tac [`s`, `sm`] >> simp[])
  >- (strip_tac >> irule reason_head_vv_storage_live >>
      qexistsl_tac [`M`, `id`, `s`, `vn`] >> simp[ADD_COMM])
  >- suspend "old_memory"
  >- suspend "locals"
  >> strip_tac >> irule exprSimPropsTheory.pure_frame_trans >>
  simp[] >> qexistsl_tac [`ee`, `sm`, `s`] >> simp[] >>
  drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`) reason_head_pure_frame >>
  disch_then drule >> disch_then (qspecl_then [`t`, `sm`] mp_tac) >> simp[ADD_COMM]
QED

Resume reason_head_vv_post[at]:
  irule vv_at_alloc_mono_frame >> qexistsl_tac [`s`, `sm`] >>
  simp[]
QED

Resume reason_head_vv_post[old_memory]:
  rpt strip_tac >>
  `FLOOKUP s.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
  `mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s.vs_memory` by
    (drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`) reason_head_region_frame >>
     disch_then drule >> disch_then (qspec_then `t` mp_tac) >>
     disch_then (qspecl_then [`sz`, `off`] mp_tac) >>
     impl_tac >- (simp[ADD_COMM] >> disj1_tac >>
       qexistsl_tac [`aid`, `off`, `sz`] >> simp[] >> decide_tac) >> simp[]) >>
  simp[] >> qpat_x_assum `!aid off sz. _` irule >>
  conj_tac >- (first_assum ACCEPT_TAC) >> qexists_tac `aid` >> simp[]
QED

Resume reason_head_vv_post[locals]:
  irule exprSimPropsTheory.locals_kept_regions_tail >>
  qexists_tac `s` >> simp[] >> rpt strip_tac >>
  `local_region cenv ee.scopes s n b sz` by
    (irule exprSimPropsTheory.local_region_frame_fwd >>
     qexistsl_tac [`s0`, `sa`, `es.scopes`] >> simp[]) >>
  drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`) reason_head_region_frame >>
  disch_then drule >> disch_then (qspec_then `t` mp_tac) >>
  disch_then (qspecl_then [`sz`, `b`] mp_tac) >>
  impl_tac >- (simp[ADD_COMM] >> disj2_tac >>
    qexistsl_tac [`n`, `b`, `sz`] >> simp[]) >> simp[]
QED

Finalise reason_head_vv_post

Theorem reason_head_ptr_vv_ok:
  stmt_state_rel H ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  MEM (mk_inst id ALLOCA [Lit (n2w (64+M))]
    [STRING #"%" (toString vn)]) (fn_insts func) /\
  MEM (mk_inst (id+3) ALLOCA [Lit (n2w M)]
    [STRING #"%" (toString (vn+2))]) (fn_insts func) /\
  (!k. k < 3 ==> not_local_ptr cenv es.scopes (STRING #"%" (toString (vn+k)))) /\
  (!x k. vv_operand vv = Var x /\ k < 3 ==>
    x <> STRING #"%" (toString (vn+k))) /\
  64+M < dimword (:256) /\ sm.cs_next_id <= id /\
  run_inst_seq (reason_head id vn M) s = OK t /\ alloca_inv t /\
  inst_seq_ptr D lo ctx func PG G tn (reason_head id vn M) s Gf tnf /\
  vv_at cenv cx ty sa sm es raw vv s /\
  evaluate_type (get_tenv cx) ty = SOME rt /\
  ptr_vv_ok cx ty raw vv es G tn s ==>
  ptr_vv_ok cx ty raw vv es Gf tnf t
Proof
  strip_tac >> drule_all reason_head_operand_frame >> strip_tac >>
  `inst_seq_ptr D lo ctx func PG G tn (revert_reason_prefix id vn M) s Gf tnf` by
    fs[reason_head_def, revert_reason_prefix_def] >>
  drule revert_reason_prefix_ghost_observations >> strip_tac >>
  `op_taint tnf (vv_operand vv) = op_taint tn (vv_operand vv) /\
   op_prov Gf (vv_operand vv) = op_prov G (vv_operand vv) /\
   (!x. vv_operand vv = Var x ==> FLOOKUP Gf x = FLOOKUP G x)` by
    (Cases_on `vv_operand vv` >> simp[op_taint_def, op_prov_def] >> metis_tac[]) >>
  `!op val. ((?ty'. vv = StackValue ty' op /\ ~is_word_type ty) \/
     (?ty' p. vv = LocatedValue ty' p /\ p.ptr_location = LocMemory /\ p.ptr_operand = op)) /\
    read_result cx raw es = (INL val,es) /\ ptr_mem_ok cx ty val op G tn s ==>
    ptr_mem_ok cx ty val op Gf tnf t` by
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     `op = vv_operand vv` by (fs[vv_operand_def] >> metis_tac[]) >>
     `eval_operand op t = eval_operand op s` by metis_tac[] >>
     Cases_on `eval_operand op s`
     >- simp[ptr_mem_ok_def] >>
     drule_all reason_head_value_bytes >> strip_tac >>
     irule bop_ptr_mem_ok_frame >> qexistsl_tac [`G`, `s`, `tn`, `rt`] >>
     simp[] >> metis_tac[]) >>
  Cases_on `vv` >> fs[vv_operand_def]
  >- (fs[ptr_vv_ok_def, ptr_val_ok_def] >> metis_tac[]) >>
  Cases_on `p.ptr_location = LocMemory`
  >- (fs[ptr_vv_ok_def] >> metis_tac[]) >>
  irule revert_reason_prefix_ptr_vv_nonmemory >>
  conj_tac >- simp[] >>
  qexistsl_tac [`D`, `G`, `PG`, `ctx`, `func`, `id`, `lo`, `M`, `s`, `tn`, `vn`] >>
  fs[reason_head_def, revert_reason_prefix_def] >> metis_tac[]
QED

Theorem reason_head_code_value:
  stmt_state_rel H ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  MEM (mk_inst id ALLOCA [Lit (n2w (64+M))]
    [STRING #"%" (toString vn)]) (fn_insts func) /\
  MEM (mk_inst (id+3) ALLOCA [Lit (n2w M)]
    [STRING #"%" (toString (vn+2))]) (fn_insts func) /\
  (!k. k < 2 ==> not_local_ptr cenv es.scopes (STRING #"%" (toString (vn+k)))) /\
  64+M < dimword (:256) /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  run_inst_seq (reason_head id vn M) s = OK t /\
  inst_seq_ptr D lo ctx func PG G tn (reason_head id vn M) s Gf tnf /\
  val_wf rt val /\ w2n w + type_memory_size rt <= lo /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory rt val (w2n w) mem) ==>
  !mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
    val_in_memory rt val (w2n w) mem
Proof
  strip_tac >> drule_all (SRULE [] reason_head_lo_frame) >> strip_tac >>
  `w2n w + val_footprint rt val <= lo` by
    (drule exprSimPropsTheory.val_footprint_le >> decide_tac) >>
  `mem_bytes_at (w2n w) (val_footprint rt val) t.vs_memory =
    mem_bytes_at (w2n w) (val_footprint rt val) s.vs_memory` by
    (drule valueEncodingProofsTheory.mem_bytes_at_agree_window >> simp[] >> metis_tac[]) >>
  rpt strip_tac >> irule robust_val_in_memory_footprint_frame >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`, `t.vs_memory`, `tn.t_mem`, `tnf.t_mem`] >>
  simp[] >> rpt strip_tac >> first_x_assum irule >> simp[] >> decide_tac
QED

Theorem reason_head_unwrap_value_resources:
  stmt_state_rel H ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  MEM (mk_inst id ALLOCA [Lit (n2w (64+M))]
    [STRING #"%" (toString vn)]) (fn_insts func) /\
  MEM (mk_inst (id+3) ALLOCA [Lit (n2w M)]
    [STRING #"%" (toString (vn+2))]) (fn_insts func) /\
  (!k. k < 3 ==> not_local_ptr cenv es.scopes (STRING #"%" (toString (vn+k)))) /\
  (!x k. vv_operand vv = Var x /\ k < 3 ==>
    x <> STRING #"%" (toString (vn+k))) /\
  64+M < dimword (:256) /\ sm.cs_next_id <= id /\
  run_inst_seq (reason_head id vn M) s = OK t /\ alloca_inv t /\
  inst_seq_ptr D lo ctx func PG G tn (reason_head id vn M) s Gf tnf /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  vv_at cenv cx ty sa sm es raw vv s /\
  evaluate_type (get_tenv cx) ty = SOME rt /\
  (!val. read_result cx raw es = (INL val,es) ==> value_has_type rt val) /\
  vv_store_bound cx st lt es raw vv s /\ ptr_vv_ok cx ty raw vv es G tn s /\
  (!vt op. vv = StackValue vt op /\ ~is_word_type ty ==> ptr_buf_ok cenv e op G s) /\
  (!vt p. vv = LocatedValue vt p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e p.ptr_operand G s) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?val. read_result cx raw es = (INL val,es) /\
      !rty w. evaluate_type (get_tenv cx) ty = SOME rty /\
        eval_operand (vv_operand vv) s = SOME w ==>
        w2n w + type_memory_size rty <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rty val (w2n w) mem)) ==>
  vv_store_bound cx st lt es raw vv t /\ ptr_vv_ok cx ty raw vv es Gf tnf t /\
  (!vt op. vv = StackValue vt op /\ ~is_word_type ty ==> ptr_buf_ok cenv e op Gf t) /\
  (!vt p. vv = LocatedValue vt p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e p.ptr_operand Gf t) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?val. read_result cx raw es = (INL val,es) /\
      !rty w. evaluate_type (get_tenv cx) ty = SOME rty /\
        eval_operand (vv_operand vv) t = SOME w ==>
        w2n w + type_memory_size rty <= lo /\
        (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
          val_in_memory rty val (w2n w) mem))
Proof
  strip_tac >> drule_all reason_head_operand_frame >> strip_tac >>
  conj_tac >- suspend "store" >>
  conj_tac >- (drule_all reason_head_ptr_vv_ok >> simp[]) >>
  conj_tac >- suspend "stack_buffer" >>
  conj_tac >- suspend "located_buffer" >>
  strip_tac >>
  qpat_x_assum `cenv.ce_is_ctor /\ _ ==> _` drule_all >>
  disch_then (qx_choose_then `val` strip_assume_tac) >>
  qexists_tac `val` >> simp[] >> rpt gen_tac >> strip_tac >>
  `w2n w + type_memory_size rt <= lo /\
   (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory rt val (w2n w) mem)` by metis_tac[] >>
  simp[] >> rpt strip_tac >> irule reason_head_code_value >>
  conj_tac >- metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  goal_assum (drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
  simp[] >> metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf, DECIDE ``k < 2 ==> k < 3``]
QED

Resume reason_head_unwrap_value_resources[stack_buffer]:
  rpt strip_tac >> irule reason_head_ptr_buf_ok >>
  goal_assum (drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)) >>
  fs[vv_operand_def] >> metis_tac[]
QED

Resume reason_head_unwrap_value_resources[located_buffer]:
  rpt strip_tac >> irule reason_head_ptr_buf_ok >>
  goal_assum (drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)) >>
  fs[vv_operand_def] >> metis_tac[]
QED

Resume reason_head_unwrap_value_resources[store]:
  `s.vs_alloca_next <= t.vs_alloca_next` by
    (qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
     simp[reason_head_def] >> strip_tac >>
     drule run_inst_seq_four_endpoint >> strip_tac >>
     `!i a b. step_inst_base i a = OK b /\
       ~is_terminator i.inst_opcode /\ ~is_ext_call_op i.inst_opcode /\
       i.inst_opcode <> INVOKE ==> a.vs_alloca_next <= b.vs_alloca_next` by
       (rpt strip_tac >> irule step_inst_alloca_next_mono >>
        qexistsl_tac [`ARB`, `0`, `i`] >> simp[step_inst_non_invoke]) >>
     qpat_assum `!i a b. _` (fn th =>
       map_every (fn pat => qpat_assum pat (mp_then Any mp_tac th) >>
         simp[mk_inst_def, is_terminator_def, is_ext_call_op_def] >> strip_tac)
         [`step_inst_base _ s = _`, `step_inst_base _ s1 = _`,
          `step_inst_base _ s2 = _`, `step_inst_base _ s3 = _`]) >> decide_tac) >>
  Cases_on `vv` >> fs[vv_operand_def, vv_store_bound_def] >>
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >> gvs[] >> decide_tac
QED

Finalise reason_head_unwrap_value_resources
