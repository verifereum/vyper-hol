(* Frame boundaries for a captured, non-storage array base. *)
Theory exprSimSubscriptArrayFrame
Ancestors
  exprSimSubscriptArraySource exprSimProps exprSimAttributeFields
  loweringPosts valueEncodingProofs valueEncoding exprBopSimProps
  list rich_list finite_map pair vyperState compileEnv exprLoweringProps vyperValue

Theorem immutable_holds_runtime_frame:
  ~cenv.ce_is_ctor /\ immutable_holds cenv cx ty r w es s /\
  es'.immutables = es.immutables /\
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  es'.scopes = es.scopes ==>
  immutable_holds cenv cx ty r w es' s'
Proof
  strip_tac >>
  `FST (read_result cx r es') = FST (read_result cx r es)` by
    (irule read_result_nonstorage_frame >> simp[]) >>
  `SND (read_result cx r es') = es'` by
    (Cases_on `read_result cx r es'` >> drule read_result_state >> simp[]) >>
  gvs[immutable_holds_def] >>
  qexistsl_tac [`name`, `off`, `itv`, `iv`, `k`, `v`] >> simp[] >>
  metis_tac[PAIR, FST, SND]
QED

Theorem locals_kept_dynarray_free_value:
  expr_sim_inv cenv cx env es /\ locals_kept cenv es s s' /\
  local_region cenv es.scopes s n b sz /\
  b <= off /\ off + val_footprint tv v <= b + sz /\
  local_val_at cenv cx n (off - b) tv v /\ val_wf tv v /\ dynarray_free tv ==>
  mem_bytes_at off (val_footprint tv v) s'.vs_memory =
    mem_bytes_at off (val_footprint tv v) s.vs_memory
Proof
  strip_tac >> gvs[locals_kept_def] >> first_x_assum irule >>
  qexistsl_tac [`b`, `n`, `sz`] >> simp[] >> rpt strip_tac >>
  drule_all local_val_at_dynarray_apart >> simp[]
QED

Theorem vv_at_memory_bytes_frame:
  vv_at cenv cx ty sa sb es r (LocatedValue ty p) s /\
  p.ptr_location = LocMemory /\
  read_result cx r es = (INL v,es) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand p.ptr_operand s = SOME w /\
  expr_sim_inv cenv cx env es /\ dynarray_free tv /\
  wb_frame cenv es sb s s' ==>
  mem_bytes_at (w2n w) (val_footprint tv v) s'.vs_memory =
    mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory
Proof
  strip_tac >>
  qpat_x_assum `vv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_at_def] >> strip_tac >> gvs[]
  >- (gvs[wb_frame_def] >>
      `mem_bytes_at b sz s'.vs_memory = mem_bytes_at b sz s.vs_memory` by
        (first_x_assum irule >> simp[] >> metis_tac[]) >>
      drule mem_bytes_at_agree_window >> simp[])
  >- (gvs[wb_frame_def] >> drule_all locals_kept_dynarray_free_value >> simp[]) >>
  simp[mem_bytes_at_def]
QED

Theorem local_region_wb_frame:
  wb_frame cenv es sb s s' /\ local_ptrs_reserved cenv sb /\
  local_ptrs_rel func cenv es.scopes s ==>
  (local_region cenv es.scopes s' n b sz <=> local_region cenv es.scopes s n b sz)
Proof
  strip_tac >> gvs[wb_frame_def] >> eq_tac
  >- (strip_tac >> irule local_region_frame >> conj_tac
      >- metis_tac[] >>
      qexistsl_tac [`sb`, `es.scopes`, `s'`] >> simp[]) >>
  strip_tac >> irule local_region_frame_fwd >>
  qexistsl_tac [`s`, `sb`, `es.scopes`] >> simp[]
QED

Theorem vv_at_located_frame:
  vv_at cenv cx ty sa sb es r (LocatedValue ty p) s /\
  (!w. eval_operand p.ptr_operand s = SOME w ==>
       eval_operand p.ptr_operand s' = SOME w) /\
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  es'.scopes = es.scopes /\ es'.immutables = es.immutables /\
  wb_frame cenv es sb s s' /\ local_ptrs_reserved cenv sb /\
  local_ptrs_rel func cenv es.scopes s /\ sb.cs_next_id <= sc.cs_next_id ==>
  vv_at cenv cx ty sa sc es' r (LocatedValue ty p) s'
Proof
  strip_tac >>
  `FST (read_result cx r es') = FST (read_result cx r es)` by
    (irule read_result_nonstorage_frame >> simp[]) >>
  `!n b sz. local_region cenv es'.scopes s' n b sz <=>
             local_region cenv es.scopes s n b sz` by
    (rpt gen_tac >> simp[] >> irule local_region_wb_frame >> metis_tac[]) >>
  gvs[vv_at_def] >> rpt strip_tac >>
  `read_result cx r es = (INL v,es)` by
    (Cases_on `read_result cx r es` >> gvs[] >> drule read_result_state >> simp[]) >>
  first_x_assum drule_all >> strip_tac >> simp[] >>
  qexists_tac `w` >> simp[] >> gvs[wb_frame_def]
  >- (disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >>
      first_assum ACCEPT_TAC) >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`n`, `b`, `sz`] >> simp[]
QED

Theorem vv_holds_located_nonword_frame:
  vv_holds cenv cx ty r (LocatedValue ty p) es s /\
  vv_at cenv cx ty sa sb es r (LocatedValue ty p) s /\
  (p.ptr_location = LocMemory \/ (~cenv.ce_is_ctor /\ p.ptr_location = LocCode)) /\
  ~is_word_type ty /\
  (p.ptr_location = LocMemory ==>
   !tv. evaluate_type (get_tenv cx) ty = SOME tv ==> dynarray_free tv) /\
  (!w. eval_operand p.ptr_operand s = SOME w ==>
       eval_operand p.ptr_operand s' = SOME w) /\
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  es'.scopes = es.scopes /\ es'.immutables = es.immutables /\
  expr_sim_inv cenv cx env es /\ wb_frame cenv es sb s s' ==>
  vv_holds cenv cx ty r (LocatedValue ty p) es' s'
Proof
  strip_tac
  >- (gvs[vv_holds_def] >>
      `read_result cx r es' = (INL v,es')` by
        (`FST (read_result cx r es') = FST (read_result cx r es)` by
           (irule read_result_nonstorage_frame >> simp[]) >>
         Cases_on `read_result cx r es'` >> gvs[] >>
         drule read_result_state >> simp[]) >>
      qexists_tac `v` >> simp[] >> rpt strip_tac >>
      `val_wf tvt v` by (gvs[vv_at_def] >> metis_tac[]) >>
      `mem_bytes_at (w2n w) (val_footprint tvt v) s'.vs_memory =
       mem_bytes_at (w2n w) (val_footprint tvt v) s.vs_memory` by
        (`dynarray_free tvt` by metis_tac[] >>
         drule_all vv_at_memory_bytes_frame >> simp[]) >>
      irule val_in_memory_footprint_agree >> simp[] >>
      qexists_tac `s.vs_memory` >> simp[]) >>
  gvs[vv_holds_def] >>
  drule_all immutable_holds_runtime_frame >> simp[]
QED

Theorem framed_array_base_transport:
  vv_post ctx func cenv cx obj es sa sb s0 t r (LocatedValue (ArrayT et bd) p) u /\
  expr_post ctx func cenv cx idx t sb sc u t' iv iop v /\
  expr_type obj = ArrayT et bd /\
  ((~cenv.ce_is_ctor /\ p.ptr_location = LocCode) \/
   ((?n. bd = Fixed n) /\
    (!tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv) /\
    p.ptr_location = LocMemory)) /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sb x) /\
  (!l. p.ptr_operand <> Label l) /\
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  t'.scopes = t.scopes /\ t'.immutables = t.immutables /\
  expr_sim_inv cenv cx env t /\ local_ptrs_reserved cenv sb /\
  sb.cs_next_id <= sc.cs_next_id ==>
  vv_holds cenv cx (ArrayT et bd) r (LocatedValue (ArrayT et bd) p) t' v /\
  vv_at cenv cx (ArrayT et bd) sa sc t' r (LocatedValue (ArrayT et bd) p) v
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `wb_frame cenv t sb u v` by
    (gvs[expr_post_def, wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!w. eval_operand p.ptr_operand u = SOME w ==>
       eval_operand p.ptr_operand v = SOME w` by
    (rpt strip_tac >> irule eval_operand_frame >>
     goal_assum (drule_at Any) >> gvs[wb_frame_def] >> metis_tac[]) >>
  `local_ptrs_rel func cenv t.scopes u` by
    gvs[vv_post_def, stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_post_def] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `post_value_type cenv obj = ArrayT et bd` by
    (qpat_x_assum `vv_holds _ _ _ _ _ _ _` mp_tac >>
     simp[Once vv_holds_def] >> strip_tac >> gvs[is_bytestring_type_def]) >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  conj_tac
  >- (irule vv_holds_located_nonword_frame >>
      goal_assum (drule_at Any) >> simp[is_word_type_def] >>
      gvs[evaluate_type_def, AllCaseEqs()] >> metis_tac[dynarray_free_fixed]) >>
  irule vv_at_located_frame >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
