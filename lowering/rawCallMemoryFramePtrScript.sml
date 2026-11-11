(* Exterior-write frames allow arbitrary taint changes inside the written
   window, including copied padding. Robust locals survive because their
   occupied region, not all memory, is unchanged. Historical theorem names
   retain 'clean' for compatibility with existing callers. *)
Theory rawCallMemoryFramePtr
Ancestors
  robustCopyTransportPtr valueEncodingProps bodyPtrDefs pred_set ptrDiscipline
  venomInst finite_map localPtrsProps loweringSlice venomMemProps vyperCallOutcome
  appendStorageGhostPtr exprSimProps decoderGhostFramePtr

Theorem robust_val_clean_write_frame:
  val_wf tv v /\
  (p + val_footprint tv v <= dst \/ dst + LENGTH bytes <= p) /\
  (!i. ~(dst <= i /\ i < dst + LENGTH bytes) ==> (i IN dirty' <=> i IN dirty)) /\
  (!mem. mem_agree_outside dirty s.vs_memory mem ==> val_in_memory tv v p mem) ==>
  !mem. mem_agree_outside dirty'
    (write_memory_with_expansion dst bytes s).vs_memory mem ==>
    val_in_memory tv v p mem
Proof
  rpt strip_tac >> (
  irule robust_val_in_memory_exterior_frame >> simp[] >>
  qexistsl_tac [`s.vs_memory`, `(write_memory_with_expansion dst bytes s).vs_memory`,
    `dirty`, `dirty'`,
    `{i | dst <= i /\ i < dst + LENGTH bytes}`] >>
  simp[] >> rpt strip_tac >>
  irule write_memory_mem_bytes_at_disjoint >> decide_tac)
QED

Theorem oracle_call_memory_taint:
  (inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp ==>
  (step_taint inst s t tn).t_mem =
    tn.t_mem DIFF range_bytes (step_writes inst s t)
Proof
  strip_tac >>
  `new_site_bytes s t = {}` by
    (simp[new_site_bytes_def, EXTENSION, finite_mapTheory.FLOOKUP_DEF] >> metis_tac[]) >>
  simp[step_taint_def, mem_taint_def, written_taint_def] >>
  namedCases_on `inst.inst_operands` ["", "a rest"] >> simp[] >>
  namedCases_on `rest` ["", "b rest2"] >> simp[] >>
  namedCases_on `rest2` ["", "c rest3"] >> simp[] >>
  Cases_on `rest3` >> simp[]
QED

(* Only the memory window and local pointer lookups matter here; oracle
   account updates and pc advancement are deliberately abstracted away. *)
Theorem local_ptrs_rel_clean_write_frame:
  local_ptrs_rel func cenv scopes s /\
  (!name entry p sz. lookup_scopes name scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    lookup_var p u = lookup_var p s) /\
  u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
  u.vs_memory = (write_memory_with_expansion dst bytes s).vs_memory /\
  (!name a len. local_region cenv scopes s name a len ==>
    regions_disjoint dst (LENGTH bytes) a len) ==>
  local_ptrs_rel func cenv scopes u
Proof
  strip_tac >> irule local_ptrs_rel_frame >> qexists_tac `s` >> simp[] >>
  reverse conj_tac >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  rpt strip_tac >> irule val_in_memory_mem_agree >> simp[] >>
  qexistsl_tac [`sz`, `s.vs_memory`] >> simp[] >>
  `local_region cenv scopes s name (w2n w) sz` by
    (simp[loweringStateRelDefsTheory.local_region_def] >> metis_tac[]) >>
  qpat_x_assum `!name a len. local_region _ _ _ _ _ _ ==> _` drule >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> strip_tac >>
  sym_tac >> irule write_memory_mem_bytes_at_disjoint >> simp[]
QED

Theorem immutables_rel_runtime_write_frame:
  immutables_rel cenv addr src F es s /\
  u.vs_data_section = s.vs_data_section /\
  u.vs_memory = (write_memory_with_expansion dst bytes s).vs_memory ==>
  immutables_rel cenv addr src F es u
Proof
  strip_tac >> irule immutables_rel_mem_agree >> qexists_tac `s` >>
  simp[venomMemPropsTheory.LENGTH_write_memory_with_expansion]
QED

Theorem oracle_adoption_locals:
  (SND (adopt_call_outcome rq outcome es)).scopes = es.scopes /\
  (SND (adopt_call_outcome rq outcome es)).immutables = es.immutables
Proof
  Cases_on `rq.cr_static` >> Cases_on `outcome.co_success` >>
  Cases_on `rq.cr_kind = MessageCall` >>
  Cases_on `rq.cr_kind = DelegateMessageCall` >>
  simp[vyperCallOutcomeTheory.adopt_call_outcome_equation]
QED

(* The oracle's record update changes only effects and memory.  Freshness
   discharges local lookup preservation even after writing the status word. *)
Theorem oracle_write_semantic_frame:
  local_ptrs_rel func cenv es.scopes s /\
  immutables_rel cenv addr src F es s /\
  t.vs_vars = s.vs_vars /\ t.vs_allocas = s.vs_allocas /\
  t.vs_alloca_next = s.vs_alloca_next /\
  t.vs_data_section = s.vs_data_section /\
  t.vs_memory = (write_memory_with_expansion dst bytes s).vs_memory /\
  not_scope_ptr cenv es.scopes out /\
  (!name a len. local_region cenv es.scopes s name a len ==>
    regions_disjoint dst (LENGTH bytes) a len) ==>
  local_ptrs_rel func cenv es.scopes t /\
  immutables_rel cenv addr src F es t /\
  local_ptrs_rel func cenv es.scopes
    ((update_var out result t) with vs_inst_idx := pc) /\
  immutables_rel cenv addr src F es
    ((update_var out result t) with vs_inst_idx := pc)
Proof
  strip_tac >> rpt conj_tac
  >- (irule local_ptrs_rel_clean_write_frame >>
      qexistsl_tac [`bytes`, `dst`, `s`] >> simp[venomStateTheory.lookup_var_def] >>
      metis_tac[])
  >- (irule immutables_rel_runtime_write_frame >>
      qexistsl_tac [`bytes`, `dst`, `s`] >> simp[])
  >- (irule local_ptrs_rel_clean_write_frame >>
      qexistsl_tac [`bytes`, `dst`, `s`] >>
      simp[venomStateTheory.update_var_def, venomStateTheory.lookup_var_def,
        finite_mapTheory.FLOOKUP_UPDATE] >>
      rpt strip_tac >> fs[loweringStateRelDefsTheory.not_scope_ptr_def] >> metis_tac[]) >>
  irule immutables_rel_runtime_write_frame >>
  qexistsl_tac [`bytes`, `dst`, `s`] >> simp[venomStateTheory.update_var_def]
QED

Theorem oracle_take_adoption_locals:
  take_call_outcome target calldata value_opt es = (INL (rq,outcome),es1) ==>
  (SND (adopt_call_outcome rq outcome es1)).scopes = es.scopes /\
  (SND (adopt_call_outcome rq outcome es1)).immutables = es.immutables
Proof
  strip_tac >> drule vyperCallOutcomeTheory.take_call_outcome_frame >>
  strip_tac >> simp[oracle_adoption_locals] >>
  fs[vyperStateTheory.evaluation_state_component_equality]
QED

Theorem local_robust_clean_write_frame:
  local_ptrs_rel func cenv scopes s /\
  lookup_scopes name scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME w /\
  (!mem. mem_agree_outside dirty s.vs_memory mem ==>
    val_in_memory entry.type entry.value (w2n w) mem) /\
  (!name a len. local_region cenv scopes s name a len ==>
    regions_disjoint dst (LENGTH bytes) a len) /\
  (!i. ~(dst <= i /\ i < dst + LENGTH bytes) ==> (i IN dirty' <=> i IN dirty)) ==>
  !mem. mem_agree_outside dirty'
    (write_memory_with_expansion dst bytes s).vs_memory mem ==>
    val_in_memory entry.type entry.value (w2n w) mem
Proof
  rpt strip_tac >>
  `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
    (fs[loweringStateRelDefsTheory.local_ptrs_rel_def] >>
     first_x_assum drule_all >> strip_tac >> simp[]) >>
  irule robust_val_clean_write_frame >> simp[] >>
  qexistsl_tac [`bytes`, `dirty`, `dirty'`, `dst`, `s`] >> simp[] >>
  `val_footprint entry.type entry.value <= sz` by
    (drule exprSimPropsTheory.val_footprint_le >> decide_tac) >>
  `local_region cenv scopes s name (w2n w) sz` by
    (simp[loweringStateRelDefsTheory.local_region_def] >> metis_tac[]) >>
  qpat_x_assum `!name a len. local_region _ _ _ _ _ _ ==> _` drule >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem ghost_inv_clean_write_frame:
  ghost_inv d cenv cx es G tn s /\ local_ptrs_rel func cenv es.scopes s /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
    op_taint un (Var x) = op_taint tn (Var x) /\ lookup_var x u = lookup_var x s) /\
  ee.scopes = es.scopes /\
  u.vs_memory = (write_memory_with_expansion dst bytes s).vs_memory /\
  (!i. ~(dst <= i /\ i < dst+LENGTH bytes) ==> (i IN un.t_mem <=> i IN tn.t_mem)) /\
  (!name a len. local_region cenv es.scopes s name a len ==>
    regions_disjoint dst (LENGTH bytes) a len) /\ stor_taint_ok cx un u ==>
  ghost_inv d cenv cx ee H un u
Proof
  strip_tac >> fs[bodyPtrDefsTheory.ghost_inv_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p` by metis_tac[loweringStateRelDefsTheory.local_ptrs_reserved_def] >>
      qpat_x_assum `!name entry p sz. _` drule >> strip_tac >> conj_tac
      >- (irule ptr_covers_old_transport >> goal_assum (drule_at Any) >>
          goal_assum (drule_at Any) >> simp[]) >>
      rpt strip_tac >>
      `lookup_var p s = SOME w` by metis_tac[] >>
      irule local_robust_clean_write_frame >>
      first_assum (irule_at (Pat `local_ptrs_rel _ _ _ _`)) >>
      first_assum (irule_at (Pat `FLOOKUP _ _ = SOME (PtrVar _ _)`)) >>
      qexistsl_tac [`dst`, `un.t_mem`, `tn.t_mem`, `bytes`] >> simp[] >> metis_tac[]) >>
  Cases_on `d` >> fs[bodyPtrDefsTheory.return_buf_ptr_def] >>
  PairCases_on `x` >> gvs[bodyPtrDefsTheory.return_buf_ptr_def] >>
  metis_tac[ptr_covers_old_transport]
QED

Theorem wb_frame_clean_write:
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  u.vs_allocas = s.vs_allocas /\
  u.vs_memory = (write_memory_with_expansion dst bytes s).vs_memory /\
  (!name a len. local_region cenv es.scopes s name a len ==>
    regions_disjoint dst (LENGTH bytes) a len) /\
  (!aid a len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
    regions_disjoint dst (LENGTH bytes) a len) ==>
  wb_frame cenv es es sa s u
Proof
  strip_tac >> simp[loweringPostsTheory.wb_frame_def] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!aid a len. _ /\ FLOOKUP _ _ = SOME _ ==> _` drule_all >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def] >> strip_tac >>
      irule write_memory_mem_bytes_at_disjoint >> simp[]) >>
  irule locals_kept_regions >> rpt strip_tac >>
  qpat_x_assum `!name a len. local_region _ _ _ _ _ _ ==> _` drule >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> strip_tac >>
  irule write_memory_mem_bytes_at_disjoint >> decide_tac
QED

Theorem oracle_call_write_taint:
  (inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL) /\
  source_memory_write_ranges inst s = [(dst,cap)] /\
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp ==>
  (step_taint inst s t tn).t_mem =
    tn.t_mem DIFF {i | dst <= i /\ i < dst + LENGTH (TAKE cap t.vs_returndata)}
Proof
  strip_tac >> (
  `(step_taint inst s t tn).t_mem =
    tn.t_mem DIFF range_bytes (step_writes inst s t)` by
    metis_tac[oracle_call_memory_taint] >>
  simp[ptrDisciplineTheory.step_writes_def, ptrDisciplineTheory.range_bytes_def,
    listTheory.LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF, pred_setTheory.EXTENSION] >>
  Cases_on `cap < LENGTH t.vs_returndata` >>
  Cases_on `cap <= LENGTH t.vs_returndata` >> gvs[] >>
  `cap = LENGTH t.vs_returndata` by decide_tac >> simp[])
QED

Theorem oracle_call_ghost_frame:
  (inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL) /\
  inst.inst_outputs = [out] /\ source_memory_write_ranges inst s = [(dst,cap)] /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_rel func cenv es.scopes s /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> x <> out) /\ ee.scopes = es.scopes /\
  t.vs_vars = s.vs_vars |+ (out,result) /\ t.vs_allocas = s.vs_allocas /\
  t.vs_fmp = s.vs_fmp /\
  t.vs_memory = (write_memory_with_expansion dst (TAKE cap t.vs_returndata) s).vs_memory /\
  (!name a len. local_region cenv es.scopes s name a len ==>
    regions_disjoint dst cap a len) /\
  (!aid a len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
    regions_disjoint dst cap a len) /\
  H = step_prov PG G inst t /\ un = step_taint inst s t tn /\
  stor_taint_ok cx un t ==>
  ghost_inv d cenv cx ee H un (t with vs_inst_idx := pc) /\
  ghost_kept cenv es sa G tn s H un /\
  wb_frame cenv es ee sa s (t with vs_inst_idx := pc)
Proof
  strip_tac >> (
  `!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
    op_taint un (Var x) = op_taint tn (Var x) /\
    lookup_var x (t with vs_inst_idx := pc) = lookup_var x s` by
    (gen_tac >> strip_tac >> conj_tac
     >- (simp[] >> irule step_prov_other_output >> simp[] >> metis_tac[]) >>
     conj_tac
     >- (simp[] >> irule step_taint_other_output >> simp[] >> metis_tac[]) >>
     simp[venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]) >>
  `un.t_mem = tn.t_mem DIFF {i | dst <= i /\ i < dst+LENGTH (TAKE cap t.vs_returndata)}` by
    metis_tac[oracle_call_write_taint] >>
  `(!name a len. local_region cenv es.scopes s name a len ==>
    regions_disjoint dst (LENGTH (TAKE cap t.vs_returndata)) a len) /\
   (!aid a len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
    regions_disjoint dst (LENGTH (TAKE cap t.vs_returndata)) a len)` by
    (`LENGTH (TAKE cap t.vs_returndata) <= cap` by
       (simp[listTheory.LENGTH_TAKE_EQ] >> rw[] >> decide_tac) >>
     conj_tac >> rpt strip_tac >>
     first_x_assum drule_all >> simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  conj_tac
  >- (irule ghost_inv_clean_write_frame >>
      first_assum (irule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
      qexistsl_tac [`sa`, `func`, `dst`, `TAKE cap t.vs_returndata`] >>
      fs[bodyPtrDefsTheory.stor_taint_ok_def] >> metis_tac[]) >>
  conj_tac
  >- (irule ghost_kept_old_transport >> simp[pred_setTheory.SUBSET_DEF] >> metis_tac[]) >>
  `wb_frame cenv es es sa s (t with vs_inst_idx := pc)` suffices_by
    (qpat_x_assum `ee.scopes = _` (fn th => rewrite_tac[th,
       loweringPostsTheory.wb_frame_def, loweringPostsTheory.locals_kept_def,
       loweringPostsTheory.popped_kept_def])) >>
  irule wb_frame_clean_write >>
  simp[venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  qexistsl_tac [`TAKE cap t.vs_returndata`, `dst`] >> simp[] >> metis_tac[])
QED
