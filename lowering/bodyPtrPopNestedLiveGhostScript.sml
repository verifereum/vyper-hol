Theory bodyPtrPopNestedLiveGhost
Ancestors
  bodyPtrPopNestedLivePost bodyPtrDefs assignTuplePtrStoreWord
  augAssignPtrStore localPtrsProps compileEnv loweringStateRelDefs venomState finite_map pred_set
  robustCopyTransportPtr appendStorageGhostPtr

(* A header inside one local cannot affect any other local's representation. *)
Theorem pop_header_other_local_robust:
  ghost_inv d cenv cx es G tn s /\
  local_ptrs_rel func cenv es.scopes s /\
  local_region cenv es.scopes s id locbase cap /\ k+32 <= cap /\
  name <> id /\ lookup_scopes name es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME b ==>
  !mem. mem_agree_outside tn.t_mem (mstore (locbase+k) wd s).vs_memory mem ==>
    val_in_memory entry.type entry.value (w2n b) mem
Proof
  strip_tac >>
  `local_region cenv es.scopes s name (w2n b) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `regions_disjoint locbase cap (w2n b) sz` by
    (fs[local_ptrs_rel_def] >> metis_tac[]) >>
  `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
    (fs[local_ptrs_rel_def] >> metis_tac[]) >>
  `val_footprint entry.type entry.value <= sz` by
    (drule exprSimPropsTheory.val_footprint_le >> decide_tac) >>
  rpt gen_tac >> strip_tac >>
  irule robust_val_in_memory_exterior_frame >> conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`, `(mstore (locbase+k) wd s).vs_memory`,
    `tn.t_mem`, `tn.t_mem`, `{i | locbase+k <= i /\ i < locbase+k+32}`] >>
  simp[] >> conj_tac
  >- (fs[ghost_inv_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
      simp[] >> decide_tac) >>
  fs[regions_disjoint_def] >> decide_tac
QED

Theorem pop_header_locals_robust:
  ghost_inv d cenv cx es G tn s /\
  local_ptrs_rel func cenv es.scopes s /\
  lookup_scopes id es.scopes = SOME old /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var root) cap) /\
  lookup_var root s = SOME b /\
  local_region cenv es.scopes s id (w2n b) cap /\ k+32 <= cap /\
  lookup_scopes id scopes' = SOME (old with <|value := updated; popped := hist|>) /\
  (!name. name <> id ==> lookup_scopes name scopes' = lookup_scopes name es.scopes) /\
  (!mem. mem_agree_outside tn.t_mem (mstore (w2n b+k) wd s).vs_memory mem ==>
    val_in_memory old.type updated (w2n b) mem) ==>
  !name entry p sz. lookup_scopes name scopes' = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    ptr_covers G tn p s sz /\
    !w mem. lookup_var p s = SOME w /\
      mem_agree_outside tn.t_mem (mstore (w2n b+k) wd s).vs_memory mem ==>
      val_in_memory entry.type entry.value (w2n w) mem
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> Cases_on `name = id`
  >- (gvs[] >> fs[ghost_inv_def] >> metis_tac[]) >>
  `lookup_scopes name es.scopes = SOME entry` by metis_tac[] >>
  conj_tac >- (fs[ghost_inv_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> irule pop_header_other_local_robust >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem pop_header_ghost_transport:
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP H x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  (!name entry p sz. lookup_scopes name es'.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    ptr_covers G tn p s sz /\
    !w mem. lookup_var p s = SOME w /\ mem_agree_outside tf.t_mem t.vs_memory mem ==>
      val_in_memory entry.type entry.value (w2n w) mem) /\
  stor_taint_ok cx tf t ==>
  ghost_inv d cenv cx es' H tf t
Proof
  strip_tac >> rewrite_tac[ghost_inv_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
      first_x_assum drule_all >> strip_tac >> conj_tac
      >- (irule ptr_covers_old_transport >> goal_assum (drule_at Any) >>
          goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
      rpt strip_tac >> metis_tac[]) >>
  conj_tac
  >- (Cases_on `d` >> simp[return_buf_ptr_def] >> PairCases_on `x` >>
      fs[ghost_inv_def, return_buf_ptr_def] >>
      irule ptr_covers_old_transport >> goal_assum (drule_at Any) >>
      metis_tac[]) >>
  fs[ghost_inv_def] >> metis_tac[]
QED
