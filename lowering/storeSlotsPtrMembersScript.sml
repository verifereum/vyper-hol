(* Counted member-list composition, shared by tuples and structs. *)
Theory storeSlotsPtrMembers
Ancestors
  storeSlotsPtrMemberOffset storeSlotsPtrMemberFrame storeSlotsPtrReadResources
  storeSlotsPtrInterface placeStoreSlots stmtLoweringMono fragExec
  valueTypingMemoryProps valueEncodingDefs valueEncodingProofs vyperTyping vyperTypeDefaults
  context compileEnv venomState ptrDiscipline fragGasPathPtr exprLoweringProps valueEncodingProps valueEncoding vyperValue
  list rich_list arithmetic words finite_map bodyPtrDefs loweringStateRelDefs

Theorem store_slots_members_run_ptr:
  !members tvs vs cenv D ctx PG mo so root slot tr sa sb func s sw dw G tn capacity.
    compile_store_slots_members cenv (Var root) slot members mo so tr sa = ((),sb) /\
    LIST_REL (\(ty,sz) (tv,v). sz = type_memory_size tv /\
      store_slots_ptr_entry cenv D ctx PG ty tv v /\ IS_SOME (encode_value tv v))
      members (ZIP (tvs,vs)) /\
    values_have_types tvs vs /\ mo = 32 * so /\
    ptr_covers G tn root s capacity /\ mo + type_memory_size_list tvs <= capacity /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      tuple_in_memory vs tvs (w2n sw + mo) m) /\
    not_fresh_at sa root /\ (!x. slot = Var x ==> not_fresh_at sa x) /\
    lookup_var root s = SOME sw /\ eval_operand slot s = SOME dw /\ op_taint tn slot = {} /\
    w2n sw + mo + type_memory_size_list tvs < dimword (:256) /\
    w2n dw + so + type_slot_size_list tvs <= dimword (:256) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static ==>
    ?Gf tf u ks.
      gas_path_ptr D 0 ctx func PG G tn s 0 Gf tf (OK u) /\
      store_slots_ptr_frame tr sw dw s tn ks u tf /\
      (!k. MEM k ks <=> ?i writes j. i < LENGTH tvs /\
        encode_value (EL i tvs) (EL i vs) = SOME writes /\
        MEM j (MAP FST writes) /\ k = so + tuple_prefix_slot_size i tvs + j) /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
      u.vs_allocas = s.vs_allocas /\ u.vs_labels = s.vs_labels /\
      u.vs_call_ctx = s.vs_call_ctx /\ ~u.vs_halted /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  Induct_on `members`
  >- (rpt gen_tac >> simp[Once compile_store_slots_def, comp_return_def] >> strip_tac >>
      `LENGTH vs = LENGTH tvs` by metis_tac[values_have_types_length] >>
      `tvs = [] /\ vs = []` by (Cases_on `tvs` >> Cases_on `vs` >> gvs[]) >>
      gvs[] >> qexistsl_tac [`G`, `tn`, `s`, `[]`] >>
      simp[store_slots_ptr_frame_nil] >> irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
  qx_gen_tac `hdmem` >> PairCases_on `hdmem` >>
  Cases_on `tvs` >> Cases_on `vs` >> simp[values_have_types_LIST_REL] >>
  rpt gen_tac >> strip_tac >>
  gvs[Once compile_store_slots_def, comp_bind_def, comp_ignore_bind_def, AllCaseEqs()] >>
  rename1 `store_slots_ptr_entry cenv D ctx PG ty tv v` >>
  rename1 `ZIP (tvs,vs)` >>
  Cases_on `compile_lit_byte_offset (Var root) (32 * so) sa` >>
  rename1 `compile_lit_byte_offset (Var root) (32 * so) sa = (ms,a)` >>
  Cases_on `compile_lit_byte_offset slot so a` >>
  rename1 `compile_lit_byte_offset slot so a = (ds,b)` >>
  Cases_on `compile_store_slots cenv ms ds ty tr b` >>
  rename1 `compile_store_slots cenv ms ds ty tr b = (unit,sc)` >>
  Cases_on `unit` >> gvs[] >> suspend "head"
QED
Resume store_slots_members_run_ptr[head]:
  `ci_mono sa a /\ ci_mono a b /\ ci_mono b sc /\ ci_mono sc sb` by
    metis_tac[ci_mono_compile_lit_byte_offset,
      cj 1 ci_mono_compile_store_slots, cj 2 ci_mono_compile_store_slots, pairTheory.SND] >>
  `fn_has_code sa a func /\ fn_has_code a b func /\
   fn_has_code b sc func /\ fn_has_code sc sb func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans]) >>
  `values_have_types (tv::tvs) (v::vs)` by simp[values_have_types_LIST_REL] >>
  drule store_slots_tuple_child_read_resources >>
  disch_then (qspecl_then [`tn`, `s.vs_memory`, `0`, `32 * so + w2n sw`] mp_tac) >> simp[] >>
  strip_tac >>
  `?writes. encode_value tv v = SOME writes` by metis_tac[optionTheory.IS_SOME_EXISTS] >>
  `32 * so + val_store_size tv v <= capacity /\
   32 * so < dimword (:256) /\
   w2n sw + 32 * so + type_memory_size tv < dimword (:256) /\
   w2n dw + so + type_slot_size tv <= dimword (:256)` by
    (fs[type_memory_size_def, type_slot_size_def, type_memory_size_list_sum] >> decide_tac) >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n sw + 32 * so) m` by metis_tac[ADD_COMM] >>
  drule_all store_slots_member_offset_run_ptr >>
  strip_tac >> suspend "tail"
QED
Resume store_slots_members_run_ptr[tail]:
  `store_slots_ptr_frame tr (sw+n2w (32*so)) (dw+n2w so) s tn ks u tf` by
    (irule store_slots_ptr_frame_pure_prefix >> metis_tac[]) >>
  `store_slots_ptr_frame tr sw dw s tn (MAP ((+) so) ks) u tf` by
    (irule store_slots_ptr_frame_shift >> simp[] >> decide_tac) >>
  `u.vs_memory = s.vs_memory /\ tf.t_mem = tn.t_mem` by
    fs[store_slots_ptr_frame_def] >>
  `lookup_var root u = SOME sw /\ eval_operand slot u = SOME dw /\
   op_taint tf slot = {} /\ ptr_covers Gf tf root u capacity` by
    (Cases_on `slot` >> fs[eval_operand_def, op_taint_def, ptr_covers_def] >> metis_tac[]) >>
  `not_fresh_at sc root /\ (!x. slot = Var x ==> not_fresh_at sc x)` by
    (fs[ci_mono_def, not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `type_memory_size tv DIV 32 = type_slot_size tv` by simp[type_memory_size_slots] >>
  `32 * so + type_memory_size tv = 32 * (so + type_slot_size tv)` by
    simp[type_memory_size_slots, LEFT_ADD_DISTRIB] >>
  `!m. mem_agree_outside tf.t_mem u.vs_memory m ==>
    tuple_in_memory vs tvs (32 * (so + type_slot_size tv) + w2n sw) m` by
    (qpat_x_assum `!tvs vs cenv' D' ctx' PG' so' root' slot' tr' sa' sb' func' s'' sw' dw' G' tn' capacity'. _` kall_tac >>
     gen_tac >> strip_tac >>
     qpat_x_assum `!m. _ ==> tuple_in_memory (v::vs) _ _ _`
       (qspec_then `m` mp_tac) >>
     pure_rewrite_tac[Once val_in_memory_def] >>
     simp_tac (srw_ss()) [LET_THM] >>
     `mem_agree_outside tn.t_mem s.vs_memory m` by metis_tac[] >>
     asm_rewrite_tac[] >> strip_tac >>
     qpat_x_assum `tuple_in_memory vs tvs _ m` mp_tac >>
     `32 * so + w2n sw + type_memory_size tv =
       32 * (so + type_slot_size tv) + w2n sw` by decide_tac >>
     asm_rewrite_tac[]) >>
  qpat_x_assum `compile_store_slots_members _ _ _ members _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  qpat_x_assum `!tvs vs cenv' D' ctx' PG' so' root' slot' tr' sa' sb' func' s'' sw' dw' G' tn' capacity'. _`
    (drule_at (Pat `compile_store_slots_members _ _ _ _ _ _ _ _ = _`)) >>
  suspend "apply_tail"
QED
Resume store_slots_members_run_ptr[apply_tail]:
  disch_then (drule_at (Pat `ptr_covers _ _ _ u capacity`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ func`)) >>
  disch_then (drule_at (Pat `LIST_REL _ members (ZIP (tvs,vs))`)) >>
  disch_then (qspecl_then [`sw`, `dw`] mp_tac) >>
  impl_tac >- (asm_rewrite_tac[values_have_types_LIST_REL] >>
    fs[type_memory_size_def, type_slot_size_def, type_memory_size_list_sum] >> decide_tac) >>
  strip_tac >> suspend "compose"
QED
Resume store_slots_members_run_ptr[compose]:
  qexistsl_tac [`Gf'`, `tf'`, `u'`, `MAP ((+) so) ks ++ ks'`] >>
  conj_tac >- metis_tac[gas_path_ptr_then, ADD_0] >>
  conj_tac >- (irule store_slots_ptr_frame_compose >> metis_tac[]) >>
  reverse conj_tac
  >- (rpt conj_tac >> simp[] >> rpt strip_tac >>
      `not_fresh_at sc x` by (fs[ci_mono_def, not_fresh_at_def] >> decide_tac) >>
      metis_tac[]) >>
  suspend "support"
QED
Resume store_slots_members_run_ptr[support]:
  qpat_x_assum `!k. MEM k ks' <=> _` mp_tac >>
  qpat_x_assum `!j. MEM j ks <=> _` mp_tac >>
  qpat_x_assum `encode_value tv v = SOME writes` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  asm_rewrite_tac[MEM_APPEND] >> eq_tac
  >- (strip_tac
      >- (fs[MEM_MAP] >> qexistsl_tac [`0`, `writes`, `y`] >>
          simp[vyperStateTheory.tuple_prefix_slot_size_def, MEM_MAP] >> metis_tac[]) >>
      qexistsl_tac [`SUC i`, `writes'`, `j`] >>
      simp_tac (srw_ss()) [vyperStateTheory.tuple_prefix_slot_size_def, ADD_ASSOC] >>
      asm_rewrite_tac[] >> decide_tac) >>
  strip_tac >> Cases_on `i`
  >- (fs[vyperStateTheory.tuple_prefix_slot_size_def] >>
      disj1_tac >> simp[MEM_MAP] >> qexists_tac `j` >> simp[ADD_COMM] >> metis_tac[MEM_MAP]) >>
  disj2_tac >> qexistsl_tac [`n`, `writes'`, `j`] >>
  fs[vyperStateTheory.tuple_prefix_slot_size_def] >> decide_tac
QED
Finalise store_slots_members_run_ptr
