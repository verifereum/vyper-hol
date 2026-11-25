(* The slot write changes the result row, which is new at the aggregate anchor. *)
Theory bodyMakeSlotAnchorWriteMods
Ancestors
  bodyStructFieldCutsMods exprSimCopy freshWrites typedMemoryCopy
  loweringPosts loweringStateRelDefs bodyPtrDefs venomMemDefs venomState arithmetic

Theorem make_slot_anchor_write_mods:
  wb_frame ce ebase mid csbase sbase u /\
  ghost_kept_at lo ce ebase csbase Gbase tnbase sbase g1 tt1 /\
  csbase.cs_next_var <= sm.cs_next_var /\ csbase.cs_next_id <= aid /\
  FLOOKUP u.vs_allocas aid = SOME (root,cap) /\ alloca_inv u /\
  (!name a n. local_region ce ebase.scopes sbase name a n ==>
     a+n <= root \/ root+cap <= a) /\
  off + type_memory_size dtv <= cap /\
  struct_store_effects func (sm,g1,tt1,u) (sb,gf,tf,t) (root+off,dtv,v) ==>
  wb_frame ce ebase mid csbase sbase t /\
  ghost_kept_at lo ce ebase csbase Gbase tnbase sbase gf tf
Proof
  strip_tac >>
  fs[wb_frame_def, ghost_kept_at_def, struct_store_effects_def,
     typed_copy_state_frame_def, typed_copy_frame_def] >>
  `t.vs_allocas = u.vs_allocas` by fs[venom_state_component_equality] >>
  `!x. not_fresh_at csbase x ==> not_fresh_at sm x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!old a n. FLOOKUP sbase.vs_allocas old = SOME (a,n) /\
     old < csbase.cs_next_id ==> a+n <= root \/ root+cap <= a` by
    (rpt strip_tac >>
     `old <> aid` by decide_tac >>
     `FLOOKUP u.vs_allocas old = SOME (a,n)` by metis_tac[] >>
     qpat_x_assum `alloca_inv u` mp_tac >>
     simp[alloca_inv_def, allocas_non_overlapping_def] >>
     strip_tac >> first_x_assum (qspecl_then [`old`,`aid`] mp_tac) >> simp[]) >>
  `!a n. a+n <= root \/ root+cap <= a ==>
    mem_bytes_at a n t.vs_memory = mem_bytes_at a n u.vs_memory` by
    (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  rpt conj_tac
  >- metis_tac[]
  >- simp[]
  >- (rpt strip_tac >>
      qpat_assum `!old a n. _ /\ _ ==> a+n <= root \/ _`
        (drule_all_then assume_tac) >>
      qpat_assum `!a n. _ ==> mem_bytes_at a n t.vs_memory = _`
        (drule_then SUBST1_TAC) >>
      qpat_assum `!old a n. _ /\ _ /\ _ ==> mem_bytes_at a n u.vs_memory = _`
        (drule_all_then ACCEPT_TAC))
  >- (irule copy_buffer_locals_kept_frame >>
      qexistsl_tac [`root`,`u`,`cap`] >> simp[] >> conj_tac
      >- (rpt strip_tac >>
          qpat_assum `!name a n. local_region _ _ _ _ _ _ ==> _`
            (drule_then assume_tac) >> decide_tac) >>
      rpt strip_tac >>
      qpat_assum `!a n. _ ==> mem_bytes_at a n t.vs_memory = _` irule >>
      decide_tac)
  >- metis_tac[]
  >- (rpt strip_tac >>
      qpat_assum `!old a n. _ /\ _ ==> a+n <= root \/ _`
        (drule_all_then assume_tac) >>
      `i IN tt1.t_mem` by
        (qpat_assum `!j. _ ==> (j IN tf.t_mem <=> j IN tt1.t_mem)`
           (qspec_then `i` mp_tac) >> simp[] >> decide_tac) >>
      qpat_assum `!old a n i. _ /\ _ /\ _ /\ _ /\ _ /\ _ ==> i IN tnbase.t_mem`
        (drule_all_then ACCEPT_TAC)) >>
  rpt strip_tac >>
  qpat_assum `!name a n. local_region _ _ _ _ _ _ ==> _`
    (drule_then assume_tac) >>
  `i IN tt1.t_mem` by
    (qpat_assum `!j. _ ==> (j IN tf.t_mem <=> j IN tt1.t_mem)`
       (qspec_then `i` mp_tac) >> simp[] >> decide_tac) >>
  qpat_assum `!name a n i. local_region _ _ _ _ _ _ /\ _ ==> i IN tnbase.t_mem`
    (drule_all_then ACCEPT_TAC)
QED
