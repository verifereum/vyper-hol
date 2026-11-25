(* Carry the captured entry and its memory representation through the key.
   Only the root lookup of the captured place, not all scopes, is unchanged. *)
Theory bodyArrayCapturedAtKeyMods
Ancestors
  bodyArrayNoCopyCutsMods bodyFullPostsMods loweringPosts bodyPtrDefs
  exprSimWordArgs exprSimProps exprBopSimProps exprSimMemDefs
  exprLoweringProps stateRelProj bodyPtrBopRepresentationFrame
  vyperPlaceTyping vyperTyping vyperInterpreter vyperState
  valueEncoding valueEncodingProofs valueEncodingDefs ptrDiscipline
  compileEnv loweringStateRelDefs context finite_map words

Theorem captured_read_frame[local]:
  lookup_scopes id fin.scopes = lookup_scopes id mid.scopes /\
  read_result cx (PlaceR (MemoryPlace id path)) mid = (INL v,mid) ==>
  read_result cx (PlaceR (MemoryPlace id path)) fin = (INL v,fin)
Proof
  strip_tac >> qpat_x_assum `read_result _ _ _ = _` mp_tac >>
  Cases_on `lookup_scopes id mid.scopes` >>
  simp[read_result_def, read_place_def, get_scopes_def, bind_def,
       lift_option_type_def, lift_sum_def, return_def, raise_def] >>
  Cases_on `read_memory_path x path` >> simp[return_def, raise_def]
QED

Theorem captured_address_frame[local]:
  vv_place_ptr cenv cx mid s (PlaceR (MemoryPlace id path)) (LocatedValue t p) /\
  runtime_place_typed cx mid (MemoryPlace id path) tv /\
  (!entry ty'. lookup_scopes id mid.scopes = SOME entry /\
     cenv.ce_var_type id = SOME ty' ==> evaluate_type (get_tenv cx) ty' = SOME entry.type) /\
  evaluate_type (get_tenv cx) a = SOME tv /\
  eval_operand p.ptr_operand s = SOME w /\
  local_ptrs_reserved cenv sm /\ wb_frame cenv mid fin sm s it ==>
  place_ptr_rel cenv cx it (PlaceR (MemoryPlace id path)) w (SOME LocMemory) (Type a)
Proof
  simp[vv_place_ptr_def, runtime_place_typed_memory, place_ptr_rel_def] >>
  strip_tac >>
  `tv0 = entry.type` by metis_tac[optionTheory.SOME_11] >>
  `tvk = tv` by metis_tac[mem_path_offset_sound, optionTheory.SOME_11] >>
  `not_fresh_at sm q` by
    (qpat_assum `local_ptrs_reserved _ _`
       (qspecl_then [`id`,`id`,`q`,`sz`,`sz`] mp_tac o cj 2 o
        REWRITE_RULE [local_ptrs_reserved_def]) >> simp[]) >>
  `lookup_var q it = SOME b` by
    (qpat_assum `wb_frame _ _ _ _ _ _`
       (qspecl_then [`q`,`b`] mp_tac o cj 1 o REWRITE_RULE [wb_frame_def]) >> simp[]) >>
  qexistsl [`q`,`sz`,`b`,`t0`,`tv0`,`k`] >> gvs[]
QED

Theorem captured_window_frame[local]:
  vv_at cenv cx a sa sm mid (PlaceR (MemoryPlace id path)) (LocatedValue t p) s /\
  p.ptr_location = LocMemory /\ eval_operand p.ptr_operand s = SOME w /\
  read_result cx (PlaceR (MemoryPlace id path)) mid = (INL v,mid) /\
  evaluate_type (get_tenv cx) a = SOME tv /\
  lookup_scopes id fin.scopes = lookup_scopes id mid.scopes /\
  wb_frame cenv mid fin sm s it /\ ghost_kept_at lo cenv mid sm G1 tn1 s Gi tni ==>
  val_wf tv v /\
  mem_bytes_at (w2n w) (val_footprint tv v) it.vs_memory =
    mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory /\
  (!j. w2n w <= j /\ j < w2n w + val_footprint tv v /\ j IN tni.t_mem ==>
       j IN tn1.t_mem)
Proof
  strip_tac >>
  qpat_x_assum `vv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_at_def] >> strip_tac >> gvs[]
  >- (gvs[wb_frame_def] >>
      `mem_bytes_at b sz it.vs_memory = mem_bytes_at b sz s.vs_memory` by metis_tac[] >>
      conj_tac >- (drule mem_bytes_at_agree_window >> simp[]) >>
      rpt strip_tac >> `b <= j /\ j < b + sz` by decide_tac >>
      qpat_assum `ghost_kept_at _ _ _ _ _ _ _ _ _`
        (qspecl_then [`aid`,`b`,`sz`,`j`] irule o cj 2 o
         REWRITE_RULE [ghost_kept_at_def]) >>
      simp[] >> qexistsl [`aid`,`b`,`sz`] >> simp[] >> first_assum ACCEPT_TAC)
  >- (gvs[local_place_at_def, wb_frame_def] >>
      `mem_bytes_at b sz it.vs_memory = mem_bytes_at b sz s.vs_memory` by
        (fs[locals_kept_def] >> metis_tac[]) >>
      conj_tac >- (drule mem_bytes_at_agree_window >> simp[]) >>
      rpt strip_tac >> `b <= j /\ j < b + sz` by decide_tac >>
      fs[ghost_kept_at_def] >> metis_tac[]) >>
  simp[mem_bytes_at_def] >> decide_tac
QED

Theorem captured_at_frame[local]:
  vv_at cenv cx a sa sm mid raw (LocatedValue t p) s /\
  p.ptr_location = LocMemory /\
  read_result cx raw mid = (INL v,mid) /\ read_result cx raw fin = (INL v,fin) /\
  eval_operand p.ptr_operand it = eval_operand p.ptr_operand s /\
  wb_frame cenv mid fin sm s it /\ local_ptrs_reserved cenv sm /\
  local_ptrs_rel func cenv mid.scopes s /\ sm.cs_next_id <= st2.cs_next_id ==>
  vv_at cenv cx a sa st2 fin raw (LocatedValue t p) it
Proof
  simp[wb_frame_def] >> strip_tac >>
  `MAP FDOM mid.scopes = MAP FDOM fin.scopes` by fs[locals_kept_def] >>
  `!name b sz. local_region cenv fin.scopes it name b sz <=>
                local_region cenv mid.scopes s name b sz` by
    (rpt gen_tac >> eq_tac
     >- (strip_tac >> irule local_region_frame >> metis_tac[])
     >> strip_tac >> irule local_region_frame_fwd >> metis_tac[]) >>
  qpat_x_assum `vv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_at_def] >> strip_tac >> rpt strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >> qexists `w` >> simp[]
  >- (disj1_tac >> qexistsl [`aid`,`b`,`sz`] >>
      `aid < st2.cs_next_id` by decide_tac >> simp[] >> first_assum ACCEPT_TAC) >>
  disj2_tac >> disj1_tac >> qexistsl [`n`,`b`,`sz`] >> simp[]
QED

Theorem captured_ptr_frame[local]:
  ptr_vv_ok cx a raw (LocatedValue t p) mid G1 tn1 s /\
  p.ptr_location = LocMemory /\
  read_result cx raw mid = (INL v,mid) /\ read_result cx raw fin = (INL v,fin) /\
  eval_operand p.ptr_operand s = SOME w /\ eval_operand p.ptr_operand it = SOME w /\
  evaluate_type (get_tenv cx) a = SOME tv /\ val_wf tv v /\
  mem_bytes_at (w2n w) (val_footprint tv v) it.vs_memory =
    mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory /\
  (!j. w2n w <= j /\ j < w2n w + val_footprint tv v /\ j IN tni.t_mem ==>
       j IN tn1.t_mem) /\
  (!x. p.ptr_operand = Var x ==> FLOOKUP Gi x = FLOOKUP G1 x) /\
  op_taint tni p.ptr_operand = op_taint tn1 p.ptr_operand ==>
  ptr_vv_ok cx a raw (LocatedValue t p) fin Gi tni it /\ op_taint tni p.ptr_operand = {}
Proof
  strip_tac >> qpat_x_assum `ptr_vv_ok _ _ _ _ _ _ _ _` mp_tac >>
  simp[ptr_vv_ok_def] >> strip_tac >> simp[] >>
  irule bop_ptr_mem_ok_frame >> qexistsl [`G1`,`s`,`tn1`,`tv`] >> simp[]
QED

Theorem captured_fixed_extent[local]:
  vv_store_bound cx (ArrayT et (Fixed n)) (ArrayT et (Fixed n)) mid raw (LocatedValue t p) s /\
  ptr_buf_ok cenv obj p.ptr_operand G1 s /\ p.ptr_location = LocMemory /\
  eval_operand p.ptr_operand s = SOME w /\
  evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) = SOME (ArrayTV etv (Fixed n)) /\
  lowered_value_type cenv obj = ArrayT et (Fixed n) /\
  type_memory_bytes cenv (ArrayT et (Fixed n)) = type_memory_size (ArrayTV etv (Fixed n)) /\
  s.vs_alloca_next <= it.vs_alloca_next /\ s.vs_alloca_next < dimword (:256) /\
  (!x. p.ptr_operand = Var x ==> FLOOKUP Gi x = FLOOKUP G1 x) ==>
  w2n w + n * type_memory_size etv < dimword (:256) /\
  (0 < n * type_memory_size etv ==>
    w2n w + n * type_memory_size etv <= it.vs_alloca_next /\
    ?x b sz. p.ptr_operand = Var x /\ FLOOKUP Gi x = SOME (b,sz) /\
      b <= w2n w /\ w2n w + n * type_memory_size etv <= b + sz)
Proof
  strip_tac >>
  Cases_on `n * type_memory_size etv = 0`
  >- (pop_assum SUBST1_TAC >> simp[w2n_lt]) >>
  `w2n w + n * type_memory_size etv <= s.vs_alloca_next` by
    (qpat_x_assum `vv_store_bound _ _ _ _ _ _ _` mp_tac >>
     simp[vv_store_bound_def, type_memory_size_def] >> strip_tac >>
     first_x_assum (qspecl_then [`t`,`p.ptr_operand`,`ArrayTV etv (Fixed n)`,`w`] mp_tac) >> simp[]) >>
  conj_tac >- decide_tac >>
  disch_tac >> conj_tac >- decide_tac >>
  qpat_x_assum `ptr_buf_ok _ _ _ _ _` mp_tac >>
  simp[ptr_buf_ok_def, type_memory_size_def] >>
  strip_tac >> qexistsl [`x`,`b`,`sz`] >> simp[]
QED

Theorem array_captured_at_key_mods:
  array_nocopy_cut_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty obj idx et (Fixed n) st0
    (es,s0,G0,tn0) (sa,sm,st2,sb,LocatedValue t p,iop,dst,loc)
    (shadow_sa,shadow_sm,shadow_st2,shadow_sb)
    (gs1,mid,PlaceR (MemoryPlace id path),s,G1,tn1) (gs2,fin,key,it,Gi,tni) /\
  valid_horizon cx st0 H fin.storage_trace /\
  lookup_scopes id fin.scopes = lookup_scopes id mid.scopes /\
  evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) = SOME (ArrayTV etv (Fixed n)) /\
  runtime_place_typed cx mid (MemoryPlace id path) (ArrayTV etv (Fixed n)) /\
  (!v. read_result cx (PlaceR (MemoryPlace id path)) mid = (INL v,mid) ==>
       value_has_type (ArrayTV etv (Fixed n)) v) /\
  (!entry ty'. lookup_scopes id mid.scopes = SOME entry /\
      cenv.ce_var_type id = SOME ty' ==> evaluate_type (get_tenv cx) ty' = SOME entry.type) /\
  post_value_type cenv obj = ArrayT et (Fixed n) /\
  lowered_value_type cenv obj = ArrayT et (Fixed n) /\
  type_memory_bytes cenv (ArrayT et (Fixed n)) = type_memory_size (ArrayTV etv (Fixed n)) /\
  p.ptr_location = LocMemory /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\ (!l. p.ptr_operand <> Label l) ==>
  ?w kvs. eval_operand p.ptr_operand s = SOME w /\ eval_operand p.ptr_operand it = SOME w /\
    read_result cx (PlaceR (MemoryPlace id path)) mid = (INL (ArrayV (SArrayV kvs)),mid) /\
    read_result cx (PlaceR (MemoryPlace id path)) fin = (INL (ArrayV (SArrayV kvs)),fin) /\
    value_has_type (ArrayTV etv (Fixed n)) (ArrayV (SArrayV kvs)) /\
    runtime_place_typed cx fin (MemoryPlace id path) (ArrayTV etv (Fixed n)) /\
    place_ptr_rel cenv cx it (PlaceR (MemoryPlace id path)) w (SOME LocMemory) (Type (ArrayT et (Fixed n))) /\
    ptr_vv_ok cx (ArrayT et (Fixed n)) (PlaceR (MemoryPlace id path)) (LocatedValue t p) fin Gi tni it /\
    op_taint tni p.ptr_operand = {} /\
    vv_at cenv cx (ArrayT et (Fixed n)) sa st2 fin (PlaceR (MemoryPlace id path)) (LocatedValue t p) it /\
    w2n w + n * type_memory_size etv < dimword (:256) /\
    (0 < n * type_memory_size etv ==>
      w2n w + n * type_memory_size etv <= it.vs_alloca_next /\
      ?x b sz. p.ptr_operand = Var x /\ FLOOKUP Gi x = SOME (b,sz) /\
        b <= w2n w /\ w2n w + n * type_memory_size etv <= b + sz)
Proof
  strip_tac >> drule_all_then strip_assume_tac array_nocopy_cut_posts_mods >>
  `local_ptrs_reserved cenv sm /\ sm.cs_next_id <= st2.cs_next_id /\
   s.vs_alloca_next <= it.vs_alloca_next /\
   vv_store_bound cx (ArrayT et (Fixed n)) (ArrayT et (Fixed n)) mid
     (PlaceR (MemoryPlace id path)) (LocatedValue t p) s /\
   ptr_vv_ok cx (ArrayT et (Fixed n)) (PlaceR (MemoryPlace id path)) (LocatedValue t p) mid G1 tn1 s /\
   ptr_buf_ok cenv obj p.ptr_operand G1 s /\ ghost_kept_at lo cenv mid sm G1 tn1 s Gi tni` by
    (qhdtm_x_assum `array_nocopy_cut_mods`
       (strip_assume_tac o REWRITE_RULE [array_nocopy_cut_mods_def]) >> gvs[]) >>
  qhdtm_x_assum `array_nocopy_cut_mods` kall_tac >>
  qhdtm_x_assum `expr_post_mods` (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  qhdtm_x_assum `vv_post_mods` (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  gvs[vv_place_ptr_mods_def] >>
  `?w v. eval_operand p.ptr_operand s = SOME w /\
         read_result cx (PlaceR (MemoryPlace id path)) mid = (INL v,mid)` by
    (qhdtm_x_assum `vv_holds_mods` mp_tac >> simp[vv_holds_mods_def, vv_holds_def] >>
     strip_tac >> qexistsl [`w`,`v`] >> simp[]) >>
  qhdtm_x_assum `vv_holds_mods` kall_tac >>
  `wb_frame cenv mid fin sm s it` by drule_then ACCEPT_TAC expr_post_frame >>
  `eval_operand p.ptr_operand it = SOME w` by
    (irule eval_operand_frame >> conj_tac >- simp[] >> qexistsl [`sm`,`s`] >> fs[wb_frame_def]) >>
  drule_all_then assume_tac captured_read_frame >>
  `value_has_type (ArrayTV etv (Fixed n)) v` by simp[] >>
  `?kvs. v = ArrayV (SArrayV kvs)` by
    (qpat_x_assum `value_has_type _ v` mp_tac >> rpt (pop_assum kall_tac) >>
     Cases_on `v` >> simp[value_has_type_def] >>
     rename1 `ArrayV av` >> Cases_on `av` >> simp[value_has_type_def]) >>
  `runtime_place_typed cx fin (MemoryPlace id path) (ArrayTV etv (Fixed n))` by
    fs[runtime_place_typed_memory] >>
  drule_all_then assume_tac captured_address_frame >>
  drule_all_then strip_assume_tac captured_window_frame >>
  `(!x. p.ptr_operand = Var x ==> FLOOKUP Gi x = FLOOKUP G1 x) /\
   op_taint tni p.ptr_operand = op_taint tn1 p.ptr_operand` by
    (Cases_on `p.ptr_operand` >> fs[ghost_kept_at_def, op_taint_def] >> metis_tac[]) >>
  drule_all_then strip_assume_tac captured_ptr_frame >>
  `local_ptrs_rel func cenv mid.scopes s` by
    (qpat_assum `stmt_state_rel H _ _ _ _ mid s` (mp_tac o MATCH_MP stmt_state_rel_local_ptrs_alloca) >> simp[]) >>
  `eval_operand p.ptr_operand it = eval_operand p.ptr_operand s` by simp[] >>
  drule_all_then assume_tac captured_at_frame >>
  `s.vs_alloca_next < dimword (:256)` by
    (qpat_assum `stmt_state_rel H _ _ _ _ mid s` (mp_tac o MATCH_MP stmt_state_rel_alloca_room) >>
     metis_tac[alloca_room_next_lt]) >>
  drule_all_then strip_assume_tac captured_fixed_extent >>
  qexistsl [`w`,`kvs`] >> simp[]
QED
