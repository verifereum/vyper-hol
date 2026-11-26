(* Frame the parts of a MakeArray allocation that a single slot does not write. *)
Theory bodyMakeSlotStoreWindowMods
Ancestors
  bodyMakeElementsContractMods bodyStructFieldCutsMods robustCopyTransportPtr
  typedMemoryCopy valueEncodingProps loweringStateRelDefs venomState pred_set list pair

val _ = Parse.hide "base";

Theorem make_slot_store_prefix_mods[local]:
  make_elements_prefix_mods base ps off z tz /\
  typed_copy_frame (base+off) k z.vs_memory t.vs_memory /\
  (!i. ~(base+off <= i /\ i < base+off+k) ==>
       (i IN tf.t_mem <=> i IN tz.t_mem)) ==>
  make_elements_prefix_mods base ps off t tf
Proof
  simp[make_elements_prefix_mods_def, EVERY_MEM, FORALL_PROD] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!rt v p n. MEM (rt,v,p,n) ps ==> _`
    (drule_then strip_assume_tac) >>
  simp[] >> gen_tac >> disch_tac >>
  irule robust_val_in_memory_exterior_frame >> simp[] >>
  qexistsl_tac [`z.vs_memory`, `t.vs_memory`, `tz.t_mem`, `tf.t_mem`,
                `{i | base+off <= i /\ i < base+off+k}`] >>
  simp[] >> rpt conj_tac
  >- (first_assum ACCEPT_TAC)
  >- (fs[typed_copy_frame_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  decide_tac
QED

Theorem make_slot_store_suffix_mods[local]:
  mem_bytes_at base cap z.vs_memory = mem_bytes_at base cap s.vs_memory /\
  typed_copy_frame (base+off) k z.vs_memory t.vs_memory ==>
  make_elements_window_mods base cap off k s t
Proof
  simp[make_elements_window_mods_def, typed_copy_frame_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `mem_bytes_at p n t.vs_memory = mem_bytes_at p n z.vs_memory` by simp[] >>
  `base + (p-base) = p /\ p-base+n <= cap` by decide_tac >>
  `mem_bytes_at (base+(p-base)) n z.vs_memory =
   mem_bytes_at (base+(p-base)) n s.vs_memory` by
    (irule mem_bytes_at_translated_window >> qexists `cap` >> simp[]) >>
  qpat_x_assum `mem_bytes_at (base+(p-base)) n _ = _` mp_tac >>
  qpat_assum `base+(p-base) = p` (fn th => pure_rewrite_tac [th]) >> simp[]
QED

Theorem make_slot_store_frame_mods[local]:
  off+k <= cap /\
  (!name b n. local_region cenv es.scopes s name b n ==>
               loweringStateRelDefs$regions_disjoint base cap b n) /\
  make_elements_frame_mods cenv func base cap sa es s z /\
  typed_copy_frame (base+off) k z.vs_memory t.vs_memory /\
  t.vs_allocas = z.vs_allocas ==>
  make_elements_frame_mods cenv func base cap sa es s t
Proof
  simp[make_elements_frame_mods_def, typed_copy_frame_def] >> strip_tac >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!name b n. local_region _ _ _ _ _ _ ==> regions_disjoint _ _ _ _`
        (drule_then mp_tac) >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def] >> disch_tac >>
      `b+n <= base+off \/ base+off+k <= b` by decide_tac >>
      `mem_bytes_at b n t.vs_memory = mem_bytes_at b n z.vs_memory` by simp[] >>
      simp[] >>
      qpat_assum `!name b n. local_region _ _ _ _ _ _ ==> mem_bytes_at _ _ _ = _`
        (drule_then ACCEPT_TAC)) >>
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  `mem_bytes_at p n t.vs_memory = mem_bytes_at p n z.vs_memory` by
    (first_assum irule >> decide_tac) >>
  simp[] >>
  qpat_assum `!p n. _ ==> mem_bytes_at p n z.vs_memory = mem_bytes_at p n s.vs_memory`
    irule >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem make_slot_store_window_mods:
  off + type_memory_size dtv <= cap /\
  (!name b n. local_region cenv es.scopes s name b n ==>
               loweringStateRelDefs$regions_disjoint base cap b n) /\
  make_elements_save_mods s z /\
  make_elements_prefix_mods base ps off z tz /\
  mem_bytes_at base cap z.vs_memory = mem_bytes_at base cap s.vs_memory /\
  (~expr_has_effect h ==> make_elements_frame_mods cenv func base cap sa es s z) /\
  struct_store_effects func (sc,gz,tz,z) (sb,gf,tf,t) (base+off,dtv,v) ==>
  make_elements_save_mods s t /\
  make_elements_prefix_mods base ps off t tf /\
  (!m. mem_agree_outside tf.t_mem t.vs_memory m ==> val_in_memory dtv v (base+off) m) /\
  make_elements_window_mods base cap off (type_memory_size dtv) s t /\
  (~expr_has_effect h ==> make_elements_frame_mods cenv func base cap sa es s t)
Proof
  simp[struct_store_effects_def] >> strip_tac >>
  qhdtm_x_assum `typed_copy_state_frame`
    (strip_assume_tac o SRULE [typed_copy_state_frame_def, venom_state_component_equality]) >>
  conj_tac >- fs[make_elements_save_mods_def] >>
  conj_tac
  >- (irule make_slot_store_prefix_mods >>
      qexistsl_tac [`type_memory_size dtv`, `tz`, `z`] >> simp[] >>
      first_assum ACCEPT_TAC) >>
  conj_tac >- (irule make_slot_store_suffix_mods >> qexists `z` >> simp[]) >>
  disch_tac >>
  irule make_slot_store_frame_mods >> conj_tac
  >- (first_assum ACCEPT_TAC) >>
  qexistsl_tac [`type_memory_size dtv`, `off`, `z`] >> simp[]
QED
