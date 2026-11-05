(* The local clause after a scalar write, independently of the counted edge. *)
Theory assignTuplePtrWordLocals
Ancestors
  assignTuplePtrStoreWord assignTuplePtrStoreFrame bodyPtrDefs robustCopyTransportPtr compileEnv
  valueEncodingProps venomState finite_map pred_set

Theorem local_word_robust_update_ptr:
  ghost_inv d cenv cx es G tn s /\
  local_ptrs_rel func cenv es.scopes s /\
  local_region cenv es.scopes s id dst cap /\ 32 <= cap /\
  (!name entry. lookup_scopes name scopes' = SOME entry ==>
    (name = id ==> entry.type = tv /\ entry.value = v) /\
    (name <> id ==> lookup_scopes name es.scopes = SOME entry)) /\
  (!p sz w. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w ==> w2n w = dst) /\
  (!m. mem_agree_outside (tn.t_mem DIFF {i | dst <= i /\ i < dst+32})
     (mstore dst word s).vs_memory m ==> val_in_memory tv v dst m) ==>
  !name entry p sz.
    lookup_scopes name scopes' = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    ptr_covers G tn p s sz /\
    !w m. lookup_var p s = SOME w /\
      mem_agree_outside (tn.t_mem DIFF {i | dst <= i /\ i < dst+32})
        (mstore dst word s).vs_memory m ==>
      val_in_memory entry.type entry.value (w2n w) m
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `name = id`
  >- suspend "changed" >>
  `lookup_scopes name es.scopes = SOME entry` by metis_tac[] >>
  `ptr_covers G tn p s sz` by metis_tac[ghost_inv_def] >>
  simp[] >> rpt gen_tac >> strip_tac >>
  drule_all local_region_other_footprint_ptr >> strip_tac >>
  irule robust_val_in_memory_exterior_frame >>
  conj_tac >- simp[] >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`s.vs_memory`, `(mstore dst word s).vs_memory`,
    `tn.t_mem`, `tn.t_mem DIFF {i | dst <= i /\ i < dst+32}`] >>
  simp[] >> conj_tac >- metis_tac[ghost_inv_def] >>
  rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> decide_tac
QED

Resume local_word_robust_update_ptr[changed]:
  gvs[local_region_def] >> metis_tac[ghost_inv_def]
QED

Finalise local_word_robust_update_ptr

Theorem ghost_inv_local_word_update_ptr:
  ghost_inv d cenv cx es G tn s /\
  local_ptrs_rel func cenv es.scopes s /\
  local_region cenv es.scopes s id dst cap /\ 32 <= cap /\
  (!name entry. lookup_scopes name es'.scopes = SOME entry ==>
    (name = id ==> entry.type = tv /\ entry.value = v) /\
    (name <> id ==> lookup_scopes name es.scopes = SOME entry)) /\
  (!p sz w. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w ==> w2n w = dst) /\
  (!m. mem_agree_outside (tn.t_mem DIFF {i | dst <= i /\ i < dst+32})
     (mstore dst word s).vs_memory m ==> val_in_memory tv v dst m) /\
  tn'.t_mem = tn.t_mem DIFF {i | dst <= i /\ i < dst+32} /\
  (!p. op_taint tn' (Var p) = op_taint tn (Var p)) /\
  stor_taint_ok cx tn' (mstore dst word s) ==>
  ghost_inv d cenv cx es' G tn' (mstore dst word s)
Proof
  strip_tac >> irule updated_scope_ghost_inv_ptr >>
  reverse conj_tac
  >- (simp[] >> qexistsl_tac [`es`, `s`, `tn`] >>
      simp[lookup_var_def, mstore_def]) >>
  rpt gen_tac >> strip_tac >>
  drule_all local_word_robust_update_ptr >>
  strip_tac >>
  conj_tac
  >- (gvs[ptr_covers_def, lookup_var_def, mstore_def] >> metis_tac[]) >>
  gvs[lookup_var_def, mstore_def] >> metis_tac[]
QED
