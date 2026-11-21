(* Restore the immutable memory relation after a root constructor write. *)
Theory immutableDeployAssignMemoryFrame
Ancestors
  immutableDeployAssignSourceFrame immutableDeployAssignFacts exprSimHypsDefs
  compileEnv loweringStateRelDefs valueEncodingProps valueTypingMemoryProps vyperTypeEnv
  vyperTypeInvariants vyperState finite_map placeMemoryPathRebuild
  immutableDeployAssignAdmissible immutableDeployAssignBytes immutableValue loweringSlice
  vyperTypeInitialState alist valueMemoryTransport valueEncodingProofs
  immutableRepSensitivity ctorDeployDeadSectionRel bodyPtrDefs list
  exprSimPopNestedLocalPath vyperPlaceWriteSoundness

Theorem immutable_store_immutables_frame:
  immutables_rel ce cx.txn.target ce.ce_module ce.ce_is_ctor es s /\
  expr_sim_inv ce cx env es /\ ce.ce_is_ctor /\
  FLOOKUP env.bare_globals (ce.ce_module,id) = SOME ty /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  write_place cx (ImmutablePlace ce.ce_module id []) v es = (INL (),es') /\
  immutable_value_admissible tv v /\ val_in_memory tv v off q.vs_memory /\
  immutable_value_bytes_rel tv v
    (mem_bytes_at off (type_memory_size tv) q.vs_memory) /\
  (!a k. regions_disjoint a k off (type_memory_size tv) ==>
    mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) ==>
  immutables_rel ce cx.txn.target ce.ce_module ce.ce_is_ctor es' q
Proof
  strip_tac >>
  `?mods old. ALOOKUP es.immutables cx.txn.target = SOME mods /\
    FLOOKUP (get_source_immutables ce.ce_module mods) id = SOME (tv,old)` by
    (drule_all immutable_assign_source_lookup >> simp[]) >>
  `bare_globals_layout ce.ce_is_ctor ce.ce_module_var_type ce.ce_module_vars
     ce.ce_modules cx env.bare_globals env.bare_global_assignable /\
   env_immutables_consistent env cx es /\ state_well_typed es` by
    fs[expr_sim_inv_def, env_consistent_def] >>
  qpat_x_assum `expr_sim_inv _ _ _ _` kall_tac >>
  `!name. FLOOKUP
    (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
     | SOME imms => get_source_immutables ce.ce_module imms) name =
    if name = id then SOME (tv,v)
    else FLOOKUP (get_source_immutables ce.ce_module mods) name` by
    (gen_tac >> drule_all immutable_root_write_lookup >>
     disch_then (qspec_then `name` mp_tac) >>
     Cases_on `ALOOKUP es'.immutables cx.txn.target` >>
     gvs[get_source_immutables_def]) >>
  fs[immutables_rel_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `name = id`
  >- (gvs[] >> metis_tac[]) >>
  gvs[] >>
  `?ty'. FLOOKUP env.bare_globals (ce.ce_module,name) = SOME ty'` by
    metis_tac[bare_globals_layout_def] >>
  `evaluate_type (get_tenv cx) ty' = SOME tv'` by
    (gvs[env_immutables_consistent_def] >>
     qpat_x_assum `!src id ty tv v. _ /\ _ ==> evaluate_type _ _ = _`
       (drule_all_then assume_tac) >> simp[]) >>
  `regions_disjoint byte_offset (type_memory_size tv') off
      (type_memory_size tv)` by
    (fs[bare_globals_layout_def] >>
     qpat_x_assum `!src id1 id2 ty1 ty2 off1 off2 tv1 tv2. _`
       (drule_all_then assume_tac) >> simp[]) >>
  `val_wf tv' v'` by
    (drule_all state_well_typed_immutables_ALOOKUP >> strip_tac >>
     drule_all imms_well_typed_get_source_immutables >>
     metis_tac[value_has_type_memory_wf]) >>
  `mem_bytes_at byte_offset (type_memory_size tv') q.vs_memory =
   mem_bytes_at byte_offset (type_memory_size tv') s.vs_memory` by metis_tac[] >>
  metis_tac[val_in_memory_mem_agree, arithmeticTheory.LESS_EQ_REFL]
QED

Theorem immutable_value_bytes_rel_replace_path:
  well_formed_type_value itv /\ value_has_type itv old /\
  value_has_type ptv v /\ mem_path_offset itv path = SOME (k,ptv) /\
  assign_subscripts itv old path (Replace v) = INL new /\
  val_in_memory itv old off mem /\
  val_in_memory ptv v (off+k) mem' /\
  (!b n. off <= b /\ b+n <= off+type_memory_size itv /\
    (b+n <= off+k \/ off+k+type_memory_size ptv <= b) ==>
    mem_bytes_at b n mem' = mem_bytes_at b n mem) ==>
  immutable_value_admissible itv new /\
  val_in_memory itv new off mem' /\
  immutable_value_bytes_rel itv new
    (mem_bytes_at off (type_memory_size itv) mem')
Proof
  strip_tac >>
  drule_then strip_assume_tac exprSimPropsTheory.mem_path_offset_sound >>
  `value_has_type itv new` by
    (irule assign_subscripts_type_path_preserves_type >> simp[] >>
     qexistsl [`old`,`path`,`ptv`,`v`] >> simp[]) >>
  `val_in_memory itv new off mem'` by
    (irule typed_memory_replace_path_frame >> simp[] >>
     qexistsl [`old`,`k`,`mem`,`path`,`ptv`,`v`] >>
     `k + off = off + k` by decide_tac >>
     `k + (off + type_memory_size ptv) = off + k + type_memory_size ptv`
       by decide_tac >>
     asm_rewrite_tac[]) >>
  `immutable_value_admissible itv new` by
    (irule typed_immutable_admissible >> simp[]) >>
  simp[immutable_memory_bytes]
QED

Theorem immutable_path_write_source:
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables src imms) id = SOME (itv,old) /\
  write_place cx (ImmutablePlace src id path) v es = (INL (),es') ==>
  ?new. assign_subscripts itv old path (Replace v) = INL new /\
        es' = es with immutables :=
          (cx.txn.target,update_immutable src id itv new imms)::
          ADELKEY cx.txn.target es.immutables
Proof
  strip_tac >>
  Cases_on `assign_subscripts itv old path (Replace v)` >>
  gvs[write_place_def, get_immutables_def, get_address_immutables_def,
       bind_def, return_def, raise_def, lift_option_type_def, lift_sum_def,
       set_immutable_def, set_address_immutables_def, update_immutable_def,
       evaluation_state_component_equality]
QED

Theorem immutable_path_write_immutables_rel:
  immutables_rel ce cx.txn.target src T es s /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables src imms) id = SOME (itv,old) /\
  FLOOKUP ce.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
  well_formed_type_value itv /\ value_has_type itv old /\
  write_place cx (ImmutablePlace src id path) v es = (INL (),es') /\
  mem_path_offset itv path = SOME (k,ptv) /\
  value_has_type ptv v /\ val_in_memory ptv v (off+k) mem' /\
  (!b n. regions_disjoint b n (off+k) (type_memory_size ptv) ==>
    mem_bytes_at b n mem' = mem_bytes_at b n s.vs_memory) /\
  (!name at ot ov.
     name <> id /\
     FLOOKUP ce.ce_module_vars (src,name) = SOME (ImmutableLoc at) /\
     FLOOKUP (get_source_immutables src imms) name = SOME (ot,ov) ==>
     regions_disjoint at (type_memory_size ot) (off+k) (type_memory_size ptv)) ==>
  immutables_rel ce cx.txn.target src T es' (s with vs_memory := mem')
Proof
  strip_tac >> drule_all_then strip_assume_tac immutable_path_write_source >>
  gvs[] >>
  qpat_x_assum `immutables_rel _ _ _ T _ _` mp_tac >>
  simp[immutables_rel_def, update_immutable_def,
       get_source_immutables_set_same, FLOOKUP_UPDATE] >>
  strip_tac >> rpt gen_tac >>
  Cases_on `name = id` >> simp[] >> strip_tac >> gvs[]
  >- (first_x_assum drule_all >> strip_tac >>
      irule immutable_value_bytes_rel_replace_path >>
      rpt (CHANGED_TAC (first_assum (irule_at Any))) >>
      simp[] >>
      rpt strip_tac >>
      qpat_assum `!b n. regions_disjoint _ _ _ _ ==> _` irule >>
      simp[regions_disjoint_def]) >>
  `regions_disjoint byte_offset (type_memory_size tv) (k+off)
      (type_memory_size ptv)` by
    (qpat_assum `!name at ot ov. name <> id /\ _ ==> _`
       (drule_all_then ACCEPT_TAC)) >>
  `mem_bytes_at byte_offset (type_memory_size tv) mem' =
   mem_bytes_at byte_offset (type_memory_size tv) s.vs_memory` by
    (qpat_assum `!b n. regions_disjoint _ _ _ _ ==> _`
       (drule_then ACCEPT_TAC)) >>
  qpat_assum `!name tv v' byte_offset. _ ==> immutable_value_admissible _ _ /\ _`
    (drule_all_then strip_assume_tac) >> simp[] >>
  irule val_in_memory_transport >> simp[immutable_admissible_val_wf] >>
  qexistsl_tac [`s.vs_memory`,`byte_offset`] >> simp[]
QED

Theorem immutable_path_write_live:
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables src imms) id = SOME (itv,old) /\
  value_has_type itv old /\ well_formed_type_value itv /\
  mutable_place_path itv path /\
  evaluate_subscripts itv old path = INL selected ==>
  ?es'. write_place cx (ImmutablePlace src id path) v es = (INL (),es')
Proof
  strip_tac >>
  drule_all assign_subscripts_replace_readback >>
  disch_then (qspec_then `v` strip_assume_tac) >>
  simp[write_place_def,get_immutables_def,get_address_immutables_def,
       bind_def,return_def,lift_option_type_def,lift_sum_def,
       set_immutable_def,set_address_immutables_def]
QED

Theorem immutable_replace_path_robust[local]:
  well_formed_type_value itv /\ value_has_type itv old /\
  value_has_type ptv v /\ mem_path_offset itv path = SOME (k,ptv) /\
  assign_subscripts itv old path (Replace v) = INL new /\
  val_in_memory itv old off sec /\
  off + type_memory_size itv <= LENGTH sec /\
  LENGTH sec' = LENGTH sec /\
  (!m. mem_agree_outside dirty sec' m ==> val_in_memory ptv v (off+k) m) /\
  (!j. off <= j /\ j < off + type_memory_size itv /\
       (j < off+k \/ off+k+type_memory_size ptv <= j) ==>
       EL j sec' = EL j sec /\
       (j IN dirty ==> mem_dead_bytes sec off itv j)) ==>
  !m. mem_agree_outside dirty sec' m ==> val_in_memory itv new off m
Proof
  strip_tac >> rpt strip_tac >>
  qabbrev_tac `restore = GENLIST
      (\j. if off+k <= j /\ j < off+k+type_memory_size ptv then EL j sec
           else if j < LENGTH m then EL j m else 0w) (LENGTH sec)` >>
  `val_in_memory itv old off restore` by
    (irule section_value_memory_frame >> simp[typed_immutable_admissible] >>
     qexists_tac `sec` >> simp[Abbr `restore`] >> rpt strip_tac >>
     `j < LENGTH sec` by decide_tac >> simp[EL_GENLIST] >>
     Cases_on `off+k <= j /\ j < off+k+type_memory_size ptv` >> simp[] >>
     `j < off+k \/ off+k+type_memory_size ptv <= j` by decide_tac >>
     `EL j sec' = EL j sec /\ j NOTIN dirty` by metis_tac[] >>
     fs[mem_agree_outside_def] >>
     first_x_assum drule >> disch_then (mp_tac o AP_TERM “EL 0:byte list -> byte”) >>
     simp[EL_mem_bytes_at]) >>
  MATCH_MP_TAC (Q.SPECL [`path`,`itv`,`old`,`new`,`v`,`off`,
       `restore`,`m`,`k`,`ptv`] typed_memory_replace_path_frame) >>
  `val_in_memory ptv v (off+k) m` by (first_assum irule >> simp[]) >>
  asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >>
  irule LIST_EQ >> simp[LENGTH_mem_bytes_at_proof] >> rpt strip_tac >>
  rename1 `i < n` >>
  `b+i < LENGTH sec` by decide_tac >>
  `~(off+k <= b+i /\ b+i < off+k+type_memory_size ptv)` by decide_tac >>
  simp[EL_mem_bytes_at,Abbr `restore`,EL_GENLIST]
QED

Theorem immutable_replace_path_dirty_dead:
  well_formed_type_value itv /\ value_has_type itv old /\
  value_has_type ptv v /\ mem_path_offset itv path = SOME (k,ptv) /\
  assign_subscripts itv old path (Replace v) = INL new /\
  val_in_memory itv old off sec /\
  off + type_memory_size itv <= LENGTH sec /\
  LENGTH sec' = LENGTH sec /\
  (!m. mem_agree_outside dirty sec' m ==> val_in_memory ptv v (off+k) m) /\
  (!j. off <= j /\ j < off + type_memory_size itv /\
       (j < off+k \/ off+k+type_memory_size ptv <= j) ==>
       EL j sec' = EL j sec /\
       (j IN dirty ==> mem_dead_bytes sec off itv j)) ==>
  !j. off <= j /\ j < off + type_memory_size itv /\ j IN dirty ==>
    mem_dead_bytes sec' off itv j
Proof
  strip_tac >>
  `!m. mem_agree_outside dirty sec' m ==> val_in_memory itv new off m` by
    (MATCH_MP_TAC (Q.INST [`itv` |-> `itv`,`new` |-> `new`,
       `off` |-> `off`,`sec'` |-> `sec'`,`dirty` |-> `dirty`,
       `k` |-> `k`,`old` |-> `old`,`path` |-> `path`,`ptv` |-> `ptv`,
       `sec` |-> `sec`,`v` |-> `v`] immutable_replace_path_robust) >>
     asm_rewrite_tac[]) >>
  `value_has_type itv new` by
    (drule_then strip_assume_tac exprSimPropsTheory.mem_path_offset_sound >>
     irule assign_subscripts_type_path_preserves_type >> simp[] >>
     qexistsl [`old`,`path`,`ptv`,`v`] >> simp[]) >>
  qspecl_then [`itv`,`new`,`off`,`sec'`,`dirty`] mp_tac
    body_assign_immutable_rep_sensitivity >>
  simp[value_has_type_memory_wf] >> rpt strip_tac >>
  first_x_assum (qspec_then `j-off` mp_tac) >>
  `off+(j-off) = j /\ j-off < type_memory_size itv` by decide_tac >>
  simp[]
QED
