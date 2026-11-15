(* Joint composition of sparse aggregate stores. *)
Theory fullStoreSlotsCompositeCases
Ancestors
  fullStoreSlotsMemberStep fullStoreSlotsElementRun fullStoreSlotsMemberFrame
  placeStoreSlots valueEncodingProps context emitHelper exprLoweringProps
  loweringStateRelDefs compileEnv venomState ptrDiscipline venomInst
  finite_map list rich_list arithmetic words stateFrame stmtLoweringMono typedMemoryCopy
  fragExec pair fragGasOriginPtr stmtSimStoreCopy vyperState valueEncodingDefs
  vyperTypeValues valueEncoding vyperValue

Theorem store_slots_head_origin_ptr[local]:
  (!ty tv v. R ty tv v ==> !root slot tr sa sb func s sw dw writes G tn.
    compile_store_slots cenv (Var root) slot ty tr sa = ((),sb) /\
    not_fresh_at sa root /\ (!x. slot = Var x ==> not_fresh_at sa x) /\
    lookup_var root s = SOME sw /\ eval_operand slot s = SOME dw /\
    op_prov G slot = NONE /\ op_taint tn slot = {} /\
    ptr_covers G tn root s (val_store_size tv v) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v (w2n sw) m) /\
    w2n sw + type_memory_size tv < dimword(:256) /\
    w2n dw + type_slot_size tv <= dimword(:256) /\
    encode_value tv v = SOME writes /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    ~s.vs_call_ctx.cc_static /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
    w2n sw + val_store_size tv v <= s.vs_alloca_next ==>
    ?Gf tf u ks.
      (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gf,tf)) /\
      store_copy_normalize s u = FOLDL (\q j. (if tr then tstore else sstore) (dw+n2w j)
        (mload (w2n sw+32*j) s) q) s ks /\
      u.vs_memory = s.vs_memory /\ tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
      (if tr then tf.t_trans else tf.t_stor) = FOLDL (\ta j. key_update ta (dw+n2w j)
        (mem_word_taint tn.t_mem (w2n sw+32*j))) (if tr then tn.t_trans else tn.t_stor) ks /\
      (if tr then tf.t_stor else tf.t_trans) = (if tr then tn.t_stor else tn.t_trans) /\
      (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
      u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
      u.vs_labels = s.vs_labels /\ u.vs_call_ctx = s.vs_call_ctx /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts) /\
  R ty tv v /\
  compile_lit_byte_offset (Var root) mo sa = (src,sb) /\
  compile_lit_byte_offset dst so sb = (slot,sc) /\
  compile_store_slots cenv src slot ty tr sc = ((),sd) /\
  not_fresh_at sa root /\ (!x. dst = Var x ==> not_fresh_at sa x) /\
  lookup_var root s = SOME sw /\ ptr_covers G tn root s capacity /\
  mo + val_store_size tv v <= capacity /\
  eval_operand dst s = SOME dw /\ op_prov G dst = NONE /\ op_taint tn dst = {} /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v (w2n sw+mo) m) /\
  w2n sw+mo+type_memory_size tv < dimword(:256) /\
  w2n dw+so < dimword(:256) /\ w2n dw+so+type_slot_size tv <= dimword(:256) /\
  w2n sw+mo+val_store_size tv v <= s.vs_alloca_next /\
  encode_value tv v = SOME writes /\ fn_has_code sa sd func /\ fn_inst_ids_distinct func /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_call_ctx.cc_static /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?p tp u Gf tf ks.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gf,tf)) /\
    execution_frame p = execution_frame s /\
    tp.t_mem = tn.t_mem /\ tp.t_imm = tn.t_imm /\ tp.t_stor = tn.t_stor /\ tp.t_trans = tn.t_trans /\
    store_copy_normalize p u = FOLDL (\q j. (if tr then tstore else sstore) (dw+n2w so+n2w j)
      (mload (w2n sw+mo+32*j) p) q) p ks /\
    u.vs_memory = p.vs_memory /\ tf.t_mem = tp.t_mem /\ tf.t_imm = tp.t_imm /\
    (if tr then tf.t_trans else tf.t_stor) = FOLDL (\ta j. key_update ta (dw+n2w so+n2w j)
      (mem_word_taint tp.t_mem (w2n sw+mo+32*j))) (if tr then tp.t_trans else tp.t_stor) ks /\
    (if tr then tf.t_stor else tf.t_trans) = (if tr then tp.t_stor else tp.t_trans) /\
    (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    u.vs_labels = s.vs_labels /\ u.vs_call_ctx = s.vs_call_ctx /\
    ~u.vs_halted /\ u.vs_current_bb = sd.cs_current_bb /\ u.vs_inst_idx = LENGTH sd.cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  qpat_assum `!ty tv v. R ty tv v ==> _` (drule_then assume_tac) >>
  irule store_slots_member_step_origin_ptr >>
  rpt (conj_tac >- (first_assum ACCEPT_TAC)) >>
  qexistsl_tac [`capacity`,`cenv`,`dst`,`root`,`sb`,`sc`,`slot`,`src`,`tv`,`ty`,`v`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem store_slots_members_origin_ptr:
  !members tvs vs cenv ctx lo mo so root dst tr sa sb func s sw dw G tn.
  (!ty tv v. R ty tv v ==> !root slot tr sa sb func s sw dw writes G tn.
    compile_store_slots cenv (Var root) slot ty tr sa = ((),sb) /\
    not_fresh_at sa root /\ (!x. slot = Var x ==> not_fresh_at sa x) /\
    lookup_var root s = SOME sw /\ eval_operand slot s = SOME dw /\
    op_prov G slot = NONE /\ op_taint tn slot = {} /\
    ptr_covers G tn root s (val_store_size tv v) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v (w2n sw) m) /\
    w2n sw + type_memory_size tv < dimword(:256) /\
    w2n dw + type_slot_size tv <= dimword(:256) /\
    encode_value tv v = SOME writes /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    ~s.vs_call_ctx.cc_static /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
    w2n sw + val_store_size tv v <= s.vs_alloca_next ==>
    ?Gf tf u ks.
      (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gf,tf)) /\
      store_copy_normalize s u = FOLDL (\q j. (if tr then tstore else sstore) (dw+n2w j)
        (mload (w2n sw+32*j) s) q) s ks /\
      u.vs_memory = s.vs_memory /\ tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
      (if tr then tf.t_trans else tf.t_stor) = FOLDL (\ta j. key_update ta (dw+n2w j)
        (mem_word_taint tn.t_mem (w2n sw+32*j))) (if tr then tn.t_trans else tn.t_stor) ks /\
      (if tr then tf.t_stor else tf.t_trans) = (if tr then tn.t_stor else tn.t_trans) /\
      (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
      u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
      u.vs_labels = s.vs_labels /\ u.vs_call_ctx = s.vs_call_ctx /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts) /\
  compile_store_slots_members cenv (Var root) dst members mo so tr sa = ((),sb) /\
  LIST_REL (\(ty,sz) (tv,v). sz = type_memory_size tv /\ R ty tv v /\ IS_SOME (encode_value tv v) /\
    val_store_size tv v <= type_memory_size tv)
    members (ZIP (tvs,vs)) /\
  LENGTH vs = LENGTH tvs /\ mo = 32*so /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> tuple_in_memory vs tvs (w2n sw+mo) m) /\
  ptr_covers G tn root s (mo+type_memory_size_list tvs) /\
  not_fresh_at sa root /\ (!x. dst = Var x ==> not_fresh_at sa x) /\
  lookup_var root s = SOME sw /\ eval_operand dst s = SOME dw /\
  op_prov G dst = NONE /\ op_taint tn dst = {} /\
  w2n sw+mo+type_memory_size_list tvs < dimword(:256) /\
  w2n dw+so+type_slot_size_list tvs <= dimword(:256) /\
  (!i. i < LENGTH tvs ==> w2n dw+so+tuple_prefix_slot_size i tvs < dimword(:256)) /\
  w2n sw+mo+type_memory_size_list tvs <= s.vs_alloca_next /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ ~s.vs_call_ctx.cc_static /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?Gf tf u ks.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gf,tf)) /\
    store_copy_normalize s u = FOLDL (\q j. (if tr then tstore else sstore) (dw+n2w j)
      (mload (w2n sw+32*j) s) q) s ks /\
    u.vs_memory = s.vs_memory /\ tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
    (if tr then tf.t_trans else tf.t_stor) = FOLDL (\ta j. key_update ta (dw+n2w j)
      (mem_word_taint tn.t_mem (w2n sw+32*j))) (if tr then tn.t_trans else tn.t_stor) ks /\
    (if tr then tf.t_stor else tf.t_trans) = (if tr then tn.t_stor else tn.t_trans) /\
    (!k. MEM k ks <=> ?i writes j. i<LENGTH tvs /\ encode_value (EL i tvs) (EL i vs) = SOME writes /\
      MEM j (MAP FST writes) /\ k = so+tuple_prefix_slot_size i tvs+j) /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    u.vs_labels = s.vs_labels /\ u.vs_call_ctx = s.vs_call_ctx /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  Induct_on `members`
  >- (rpt gen_tac >> simp[Once (cj 2 compile_store_slots_def),comp_return_def] >> strip_tac >>
      `tvs=[] /\ vs=[]` by (Cases_on `tvs` >> Cases_on `vs` >> gvs[]) >>
      gvs[] >> qexistsl [`G`,`tn`,`s`,`[]`] >>
      simp[store_copy_normalize_def,venom_state_component_equality] >>
      rpt gen_tac >> irule (cj 1 gas_origin_ptr_path_rules) >> simp[]) >>
  qx_gen_tac `hdmem` >> PairCases_on `hdmem` >> Cases_on `tvs` >> Cases_on `vs` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  rename1 `R ty tv v` >> rename1 `ZIP (tvs,vs)` >>
  suspend "step"
QED

Resume store_slots_members_origin_ptr[step]:
  qpat_x_assum `compile_store_slots_members _ _ _ (_::_) _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [cj 3 compile_store_slots_def,comp_bind_def,comp_ignore_bind_def] >>
  Cases_on `compile_lit_byte_offset (Var root) (32*so) sa` >>
  rename1 `compile_lit_byte_offset (Var root) (32*so) sa = (src,a)` >>
  Cases_on `compile_lit_byte_offset dst so a` >>
  rename1 `compile_lit_byte_offset dst so a = (slot,b)` >>
  Cases_on `compile_store_slots cenv src slot ty tr b` >>
  rename1 `compile_store_slots cenv src slot ty tr b = (unit,sc)` >>
  Cases_on `unit` >> simp_tac std_ss [] >> disch_tac >> gvs[] >>
  `ci_mono sa a /\ ci_mono a b /\ ci_mono b sc /\ ci_mono sc sb` by
    (qpat_x_assum `!tvs vs cenv ctx lo so root dst tr sa sb func s sw dw G tn. _` kall_tac >>
     qpat_x_assum `!ty tv v. R ty tv v ==> _` kall_tac >>
     metis_tac[ci_mono_compile_lit_byte_offset,cj 1 ci_mono_compile_store_slots,
       cj 2 ci_mono_compile_store_slots,SND]) >>
  `fn_has_code sa sc func /\ fn_has_code sc sb func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split,cs_extends_trans]) >>
  `?writes. encode_value tv v = SOME writes` by metis_tac[optionTheory.IS_SOME_EXISTS] >>
  `w2n dw+so < dimword(:256)` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[tuple_prefix_slot_size_def]) >>
  `32*so + val_store_size tv v <= 32*so+type_memory_size_list (tv::tvs) /\
   w2n sw+32*so+type_memory_size tv < dimword(:256) /\
   w2n dw+so+type_slot_size tv <= dimword(:256) /\
   w2n sw+32*so+val_store_size tv v <= s.vs_alloca_next` by
    (fs[type_memory_size_def,type_slot_size_def] >> decide_tac) >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory tv v (w2n sw+32*so) m` by
    (rpt strip_tac >> first_x_assum drule >> simp_tac (srw_ss()) [Once val_in_memory_def,ADD_COMM,LET_THM]) >>
  suspend "head"
QED

Resume store_slots_members_origin_ptr[head]:
  `?p tp u Gf tf ks.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gf,tf)) /\
    execution_frame p = execution_frame s /\
    tp.t_mem = tn.t_mem /\ tp.t_imm = tn.t_imm /\ tp.t_stor = tn.t_stor /\ tp.t_trans = tn.t_trans /\
    store_copy_normalize p u = FOLDL (\q j. (if tr then tstore else sstore) (dw+n2w so+n2w j)
      (mload (w2n sw+32*so+32*j) p) q) p ks /\
    u.vs_memory = p.vs_memory /\ tf.t_mem = tp.t_mem /\ tf.t_imm = tp.t_imm /\
    (if tr then tf.t_trans else tf.t_stor) = FOLDL (\ta j. key_update ta (dw+n2w so+n2w j)
      (mem_word_taint tp.t_mem (w2n sw+32*so+32*j))) (if tr then tp.t_trans else tp.t_stor) ks /\
    (if tr then tf.t_stor else tf.t_trans) = (if tr then tp.t_stor else tp.t_trans) /\
    (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    u.vs_labels = s.vs_labels /\ u.vs_call_ctx = s.vs_call_ctx /\
    ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\ u.vs_inst_idx = LENGTH sc.cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))` by
    (irule store_slots_head_origin_ptr >>
     simp[] >>
     qexistsl_tac [`R`,`32*so+type_memory_size_list (tv::tvs)`,`cenv`,`dst`,`root`,`a`,`b`,`slot`,`src`,`tv`,`ty`,`v`] >>
     (conj_tac >- (once_rewrite_tac [ADD_COMM] >> first_assum ACCEPT_TAC)) >>
     (conj_tac >- (qpat_x_assum `w2n sw + 32 * so + type_memory_size tv < _` mp_tac >>
       POP_ASSUM_LIST (K ALL_TAC) >> decide_tac)) >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >- (qpat_x_assum `w2n dw + so + type_slot_size tv <= _` mp_tac >>
       POP_ASSUM_LIST (K ALL_TAC) >> decide_tac)) >>
     (conj_tac >- (qpat_x_assum `w2n sw + 32 * so + val_store_size tv v <= _` mp_tac >>
       POP_ASSUM_LIST (K ALL_TAC) >> decide_tac)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "head_frame"
QED

Resume store_slots_members_origin_ptr[head_frame]:
  `store_copy_normalize p u = FOLDL (\q j. (if tr then tstore else sstore) (dw+n2w j)
      (mload (w2n sw+32*j) p) q) p (MAP ((+) so) ks)` by
    (qpat_x_assum `store_copy_normalize p u = _` mp_tac >>
     simp_tac bool_ss [FOLDL_MAP,GSYM word_add_n2w,LEFT_ADD_DISTRIB,
       GSYM WORD_ADD_ASSOC,AC ADD_ASSOC ADD_COMM] >> disch_then SUBST1_TAC >>
     AP_THM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
     simp_tac bool_ss [FUN_EQ_THM] >> rpt gen_tac >>
     simp_tac bool_ss [AC ADD_ASSOC ADD_COMM]) >>
  `(if tr then tf.t_trans else tf.t_stor) = FOLDL (\ta j. key_update ta (dw+n2w j)
      (mem_word_taint tp.t_mem (w2n sw+32*j)))
      (if tr then tp.t_trans else tp.t_stor) (MAP ((+) so) ks)` by
    (qpat_x_assum `(if tr then tf.t_trans else tf.t_stor) = _` mp_tac >>
     simp_tac bool_ss [FOLDL_MAP,GSYM word_add_n2w,LEFT_ADD_DISTRIB,
       GSYM WORD_ADD_ASSOC,AC ADD_ASSOC ADD_COMM] >> disch_then SUBST1_TAC >>
     AP_THM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
     simp_tac bool_ss [FUN_EQ_THM] >> rpt gen_tac >>
     simp_tac bool_ss [AC ADD_ASSOC ADD_COMM]) >>
  drule_all store_slots_frame_pure_prefix >> strip_tac >>
  suspend "tail"
QED

Resume store_slots_members_origin_ptr[tail]:
  `compile_store_slots_members cenv (Var root) dst members
    (32*(so+type_slot_size tv)) (so+type_slot_size tv) tr sc = ((),sb)` by
    (qpat_x_assum `compile_store_slots_members _ _ _ members _ _ _ _ = _` mp_tac >>
     simp_tac std_ss [type_memory_size_slots,LEFT_ADD_DISTRIB]) >>
  `not_fresh_at sc root /\ (!x. dst = Var x ==> not_fresh_at sc x)` by
    (qpat_x_assum `!tvs' vs' cenv' ctx' lo' so' root' dst' tr' sa' sb' func' s'' sw' dw' G' tn'. _` kall_tac >>
     qpat_x_assum `!ty' tv' v'. _` kall_tac >>
     metis_tac[ci_mono_def,cs_extends_trans,freshWritesTheory.not_fresh_at_mono]) >>
  `lookup_var root u = SOME sw /\ eval_operand dst u = SOME dw /\
   op_prov Gf dst = NONE /\ op_taint tf dst = {}` by
    (qpat_x_assum `!tvs' vs' cenv' ctx' lo' so' root' dst' tr' sa' sb' func' s'' sw' dw' G' tn'. _` kall_tac >>
     qpat_x_assum `!ty' tv' v'. _` kall_tac >>
     Cases_on `dst` >> gvs[eval_operand_def,op_prov_def,op_taint_def] >>
     metis_tac[]) >>
  suspend "tail_memory"
QED

Resume store_slots_members_origin_ptr[tail_memory]:
  `ptr_covers Gf tf root u (32*(so+type_slot_size tv)+type_memory_size_list tvs)` by
    (qpat_x_assum `!tvs' vs' cenv' ctx' lo' so' root' dst' tr' sa' sb' func' s'' sw' dw' G' tn'. _` kall_tac >>
     qpat_x_assum `!ty' tv' v'. _` kall_tac >>
     qpat_x_assum `!x. not_fresh_at sa x ==> _` (qspec_then `root` mp_tac) >>
     qpat_x_assum `ptr_covers G tn root s _` mp_tac >>
     qpat_x_assum `not_fresh_at sa root` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp_tac std_ss [bodyPtrDefsTheory.ptr_covers_def,type_memory_size_def,type_memory_size_slots,LEFT_ADD_DISTRIB,ADD_ASSOC] >>
     metis_tac[]) >>
  `!m. mem_agree_outside tf.t_mem u.vs_memory m ==>
    tuple_in_memory vs tvs (32*(so+type_slot_size tv)+w2n sw) m` by
    (rpt strip_tac >>
     qpat_x_assum `!m. _ ==> tuple_in_memory (v::vs) (tv::tvs) _ m` (qspec_then `m` mp_tac) >>
     qpat_x_assum `mem_agree_outside tf.t_mem u.vs_memory m` mp_tac >>
     qpat_x_assum `tf.t_mem = tn.t_mem` mp_tac >>
     qpat_x_assum `u.vs_memory = s.vs_memory` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp_tac std_ss [] >>
     simp_tac list_ss [Once val_in_memory_def,LET_THM] >>
     simp_tac bool_ss [type_memory_size_slots,LEFT_ADD_DISTRIB,AC ADD_ASSOC ADD_COMM]) >>
  suspend "tail_bounds"
QED

Resume store_slots_members_origin_ptr[tail_bounds]:
  `32*(so+type_slot_size tv)+(type_memory_size_list tvs+w2n sw) < dimword(:256) /\
   so+type_slot_size tv+(type_slot_size_list tvs+w2n dw) <= dimword(:256) /\
   32*(so+type_slot_size tv)+(type_memory_size_list tvs+w2n sw) <= u.vs_alloca_next` by
    (qpat_x_assum `32*so + (type_memory_size_list (tv::tvs) + w2n sw) < _` mp_tac >>
     qpat_x_assum `so + (type_slot_size_list (tv::tvs) + w2n dw) <= _` mp_tac >>
     qpat_x_assum `32*so + (type_memory_size_list (tv::tvs) + w2n sw) <= _` mp_tac >>
     qpat_x_assum `u.vs_alloca_next = s.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp_tac std_ss [type_memory_size_def,type_memory_size_slots,type_slot_size_def,LEFT_ADD_DISTRIB] >> decide_tac) >>
  `!i. i < LENGTH tvs ==> so+type_slot_size tv+(w2n dw+tuple_prefix_slot_size i tvs) < dimword(:256)` by
    (gen_tac >> strip_tac >>
     qpat_x_assum `!i. i < SUC (LENGTH tvs) ==> _` (qspec_then `SUC i` mp_tac) >>
     qpat_x_assum `i < LENGTH tvs` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp_tac list_ss [tuple_prefix_slot_size_def] >> decide_tac) >>
  `allocas_from lo u /\ ~u.vs_call_ctx.cc_static` by
    (qpat_x_assum `allocas_from lo s` mp_tac >>
     qpat_x_assum `~s.vs_call_ctx.cc_static` mp_tac >>
     qpat_x_assum `u.vs_allocas = s.vs_allocas` mp_tac >>
     qpat_x_assum `u.vs_alloca_next = s.vs_alloca_next` mp_tac >>
     qpat_x_assum `u.vs_call_ctx = s.vs_call_ctx` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[allocas_from_def]) >>
  qpat_x_assum `!tvs' vs' cenv' ctx' lo' so' root' dst' tr' sa' sb' func' s'' sw' dw' G' tn'. _`
    (drule_at (Pos (el 2))) >>
  disch_then (drule_at (Pos (el 2))) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `~ctx_has_dalloca _`)) >>
  qpat_assum `~ctx_has_dalloca ctx` (fn th => simp_tac bool_ss [th]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >> suspend "tail_append"
QED

Resume store_slots_members_origin_ptr[tail_append]:
  qpat_x_assum `!ty' tv' v'. R ty' tv' v' ==> _` kall_tac >>
  qpat_x_assum `store_copy_normalize u u' = _`
    (assume_tac o REWRITE_RULE [Once ADD_COMM]) >>
  qpat_x_assum `(if tr then tf'.t_trans else tf'.t_stor) = _`
    (assume_tac o REWRITE_RULE [Once ADD_COMM]) >>
  drule_all store_slots_frame_append >> strip_tac >>
  qexistsl [`Gf'`,`tf'`,`u'`,`MAP ((+) so) ks ++ ks'`] >>
  conj_tac >- (rpt gen_tac >>
    qpat_x_assum `!D explicit PG. gas_origin_ptr_path _ (s,G,tn) _ _`
      (qspecl_then [`D`,`explicit`,`PG`] mp_tac) >>
    qpat_x_assum `!D explicit PG. gas_origin_ptr_path _ (u,Gf,tf) _ _`
      (qspecl_then [`D`,`explicit`,`PG`] mp_tac) >>
    POP_ASSUM_LIST (K all_tac) >> metis_tac[gas_origin_ptr_path_append,APPEND]) >>
  suspend "final_posts"
QED

Resume store_slots_members_origin_ptr[final_posts]:
  conj_tac >- (qpat_x_assum `store_copy_normalize s u' = _` mp_tac >>
    POP_ASSUM_LIST (K all_tac) >> simp_tac bool_ss [Once ADD_COMM]) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (qpat_x_assum `(if tr then tf'.t_trans else tf'.t_stor) = _` mp_tac >>
    POP_ASSUM_LIST (K all_tac) >> simp_tac bool_ss [Once ADD_COMM]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "support" >>
  suspend "preservation"
QED

Resume store_slots_members_origin_ptr[preservation]:
  conj_tac >- (
    qpat_x_assum `!x. not_fresh_at sa x ==> _` mp_tac >>
    qpat_x_assum `!x. not_fresh_at sc x ==> _` mp_tac >>
    qpat_x_assum `ci_mono sa a` mp_tac >>
    qpat_x_assum `ci_mono a b` mp_tac >>
    qpat_x_assum `ci_mono b sc` mp_tac >>
    POP_ASSUM_LIST (K all_tac) >>
    metis_tac[ci_mono_def,cs_extends_trans,freshWritesTheory.not_fresh_at_mono]) >>
  simp[]
QED

Resume store_slots_members_origin_ptr[support]:
  qpat_x_assum `!j. MEM j ks <=> _` mp_tac >>
  qpat_x_assum `!k. MEM k ks' <=> _` mp_tac >>
  qpat_x_assum `encode_value tv v = SOME writes` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  simp_tac list_ss [MEM_APPEND,MEM_MAP] >>
  eq_tac >- (
    strip_tac >- (qexistsl [`0`,`writes`,`y`] >>
      simp[tuple_prefix_slot_size_def,ADD_COMM] >> metis_tac[MEM_MAP]) >>
    first_x_assum (drule o iffLR) >> strip_tac >>
    qexistsl [`SUC i`,`writes'`,`j`] >>
    pure_rewrite_tac [EL,HD,TL,tuple_prefix_slot_size_def,ADD_ASSOC,LESS_MONO_EQ] >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- (pure_rewrite_tac [GSYM MEM_MAP] >> first_assum ACCEPT_TAC) >>
    qpat_x_assum `k = _` mp_tac >>
    POP_ASSUM_LIST (K all_tac) >> simp_tac bool_ss [ADD_ASSOC]) >>
  strip_tac >> Cases_on `i`
  >- (rule_assum_tac (PURE_REWRITE_RULE [EL,HD,TL,tuple_prefix_slot_size_def,ADD_0]) >>
      disj1_tac >> qexists_tac `j` >>
      metis_tac[MEM_MAP,ADD_COMM,optionTheory.SOME_11]) >>
  rule_assum_tac (PURE_REWRITE_RULE [EL,HD,TL,tuple_prefix_slot_size_def,LESS_MONO_EQ]) >>
  disj2_tac >> qpat_x_assum `!k. MEM k ks' <=> _` (irule o iffRL) >>
  qexistsl [`n`,`writes'`,`j`] >>
  pure_rewrite_tac [GSYM MEM_MAP] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (simp_tac list_ss [MEM_MAP] >> metis_tac[]) >>
  qpat_x_assum `k = _` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
  simp_tac bool_ss [ADD_ASSOC]
QED

Finalise store_slots_members_origin_ptr
