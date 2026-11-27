(* The reached child preserves the registered row; the slot write only
   replaces its own cell. *)
Theory bodyMakeSlotRangeFramesMods
Ancestors
  bodyMakeElementsContractMods bodyMakeSlotStoreWindowMods bodyStructFieldCutsMods
  bodyPtrMakeArrayMemoryFrame loweringPosts loweringStateRelDefs bodyPtrDefs
  abiDecodeStaticProps representationCleanPtr valueEncodingDefs valueEncoding
  venomState context list pair finite_map arithmetic

val _ = Parse.hide "base";

Theorem make_slot_child_prefix[local]:
  make_elements_prefix_mods base ps off s tn /\ off <= cap /\
  mem_bytes_at base cap u.vs_memory = mem_bytes_at base cap s.vs_memory /\
  (!i. base <= i /\ i < base+cap /\ i IN tt.t_mem ==> i IN tn.t_mem) ==>
  make_elements_prefix_mods base ps off u tt
Proof
  simp[make_elements_prefix_mods_def,EVERY_MEM,FORALL_PROD] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!rt v p n. MEM (rt,v,p,n) ps ==> _`
    (drule_then strip_assume_tac) >> simp[] >>
  rename1 `MEM (rt,v,p,n) ps` >>
  gen_tac >> strip_tac >> irule robust_val_in_memory_shrinking_frame >> simp[] >>
  qexistsl_tac [`tn.t_mem`,`tt.t_mem`,`s.vs_memory`,`u.vs_memory`,`n`] >> simp[] >>
  irule mem_bytes_at_bytewise >> rpt strip_tac >>
  irule mem_bytes_at_eq_byte >> qexistsl_tac [`base`,`cap`] >> simp[] >> decide_tac
QED

Theorem make_slot_range_frames_mods:
  make_elements_prefix_mods base ps off s tn /\
  FLOOKUP s.vs_allocas aid = SOME (base,cap) /\ aid < sa.cs_next_id /\
  (!name b n. local_region ce es.scopes s name b n ==>
    loweringStateRelDefs$regions_disjoint base cap b n) /\
  off + type_memory_size dtv <= cap /\
  wb_frame ce es mid sa s u /\ ghost_kept_at lo ce es sa G tn s g1 tt1 /\
  (~expr_has_effect h ==> pure_frame ce func es sa s u) /\
  struct_store_effects func (sm,g1,tt1,u) (sb,gf,tf,t) (base+off,dtv,v) ==>
  make_elements_prefix_mods base ps off t tf /\
  make_elements_window_mods base cap off (type_memory_size dtv) s t /\
  (~expr_has_effect h ==> make_elements_frame_mods ce func base cap sa es s t)
Proof
  strip_tac >>
  `!name b n. local_region ce es.scopes s name b n ==>
     base+cap <= b \/ b+n <= base` by fs[loweringStateRelDefsTheory.regions_disjoint_def] >>
  qhdtm_x_assum `wb_frame` (strip_assume_tac o REWRITE_RULE[wb_frame_def]) >>
  `make_elements_save_mods s u` by simp[make_elements_save_mods_def] >>
  `mem_bytes_at base cap u.vs_memory = mem_bytes_at base cap s.vs_memory` by
    (qpat_assum `!a b n. _ ==> mem_bytes_at b n _ = _`
       (qspecl_then [`aid`,`base`,`cap`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  `!i. base <= i /\ i < base + cap /\ i IN tt1.t_mem ==> i IN tn.t_mem` by
    (qhdtm_x_assum `ghost_kept_at` (strip_assume_tac o REWRITE_RULE[ghost_kept_at_def]) >>
     rpt strip_tac >>
     qpat_assum `!a b n i. FLOOKUP s.vs_allocas a = SOME (b,n) /\ _ ==> _`
       (qspecl_then [`aid`,`base`,`cap`,`i`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  `make_elements_prefix_mods base ps off u tt1` by
    (irule make_slot_child_prefix >> qexistsl_tac [`cap`,`s`,`tn`] >> simp[] >> decide_tac) >>
  `~expr_has_effect h ==> make_elements_frame_mods ce func base cap sa es s u` by
    (strip_tac >>
     qpat_assum `~expr_has_effect h ==> pure_frame _ _ _ _ _ _`
       (drule_then (strip_assume_tac o REWRITE_RULE[pure_frame_def])) >>
     rewrite_tac[make_elements_frame_mods_def] >> conj_tac
     >- first_assum ACCEPT_TAC >>
     rpt gen_tac >> strip_tac >>
     qpat_assum `!p n. (!i b sz. _ ==> _) ==> mem_bytes_at p n _ = _`
       irule >> first_assum ACCEPT_TAC) >>
  drule_all_then strip_assume_tac make_slot_store_window_mods >> simp[]
QED
