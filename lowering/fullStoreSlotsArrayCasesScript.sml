(* Dynamic sparse arrays compose the common prefix, element loop and suffix. *)
Theory fullStoreSlotsArrayCases
Ancestors
  fullStoreSlotsArrayFixed fullStoreSlotsArrayPrefix fullStoreSlotsArraySuffix
  fullStoreSlotsMemberFrame fullStoreSlotsElementRun fullStoreSlotsElementLayout stmtSimStoreCopy
  fullStoreSlotsProbe placeStoreSlots context emitHelper emitHelperProps
  exprSimProps vyperTyping vyperValueOperation vyperTypeValues vyperValue
  valueEncodingDefs valueEncodingProps valueEncoding compileEnv loweringStateRelDefs
  stmtLoweringMono exprLoweringProps typedMemoryCopy bodyPtrDefs ptrDiscipline
  venomState venomInst fragExec stateFrame fragGasOriginPtr finite_map list
  rich_list arithmetic words

Theorem store_slots_dynarray_origin_ptr:
  (!v. value_has_type tv v ==> !root slot tr sa sb func s sw dw writes G tn.
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
  compile_store_slots cenv (Var root) dst (ArrayT ty (Dynamic cap)) tr sa = ((),sb) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  type_memory_bytes cenv ty = type_memory_size tv /\ cap < dimword(:256) /\
  well_formed_type_value tv /\ value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  not_fresh_at sa root /\ (!x. dst = Var x ==> not_fresh_at sa x) /\
  lookup_var root s = SOME sw /\ eval_operand dst s = SOME dw /\
  op_prov G dst = NONE /\ op_taint tn dst = {} /\
  ptr_covers G tn root s (val_store_size (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n sw) m) /\
  w2n sw + type_memory_size (ArrayTV tv (Dynamic cap)) < dimword(:256) /\
  w2n dw + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword(:256) /\
  encode_value (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) = SOME writes /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_call_ctx.cc_static /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  w2n sw + val_store_size (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) <= s.vs_alloca_next ==>
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
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  drule_all store_slots_dynarray_resources >> strip_tac >>
  `?len src slot s1 s2 s3 s4.
    emit_op MLOAD [Var root] sa = (len,s1) /\
    emit_op ADD [Var root;Lit 32w] s1 = (src,s2) /\
    emit_op ADD [dst;Lit 1w] s2 = (slot,s3) /\
    compile_copy_elements_to_slots cenv src slot ty len tr s3 = ((),s4) /\
    emit_void (if tr then TSTORE else SSTORE) [dst;len] s4 = ((),sb)` by
    (qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_store_slots_def,is_abi_dynamic_def,is_bytestring_type_def,
       comp_bind_def,comp_ignore_bind_def,comp_return_def,AllCaseEqs()] >>
     ntac 4 (pairarg_tac >> simp[]) >> strip_tac >> Cases_on `_0` >> metis_tac[]) >>
  imp_res_tac typed_copy_emit_op_mono >>
  `ci_mono s3 s4` by
    (mp_tac (cj 3 ci_mono_compile_store_slots) >>
     disch_then (qspecl_then [`cenv`,`src`,`slot`,`ty`,`len`,`tr`,`s3`] mp_tac) >> simp[]) >>
  `ci_mono s4 sb` by
    (mp_tac (Q.SPECL [`if tr then TSTORE else SSTORE`,`[dst;len]`,`s4`]
      ci_mono_emit_void) >> simp[]) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
   fn_has_code s2 s3 func /\ fn_has_code s3 s4 func /\ fn_has_code s4 sb func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split,cs_extends_trans]) >>
  `32 + LENGTH vs * type_memory_size tv <=
     val_store_size (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))` by
    (simp[val_store_size_def,type_memory_size_def] >>
     irule LESS_MONO_MULT >> simp[]) >>
  `w2n sw + 32 < dimword(:256) /\ w2n sw + 32 <= s.vs_alloca_next` by decide_tac >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    mem_word_at (w2n sw) m = n2w (LENGTH vs)` by metis_tac[] >>
  drule_all (Q.INST [`n` |-> `LENGTH vs * type_memory_size tv`,
    `len_nat` |-> `LENGTH vs`] store_slots_dynarray_prefix_origin_ptr) >>
  disch_then (qx_choose_then `lv` (qx_choose_then `out` (qx_choose_then `p`
    (qx_choose_then `Gp` (qx_choose_then `tp` strip_assume_tac))))) >>
  suspend "loop"
QED

Resume store_slots_dynarray_origin_ptr[loop]:
  `w2n (sw+32w) = w2n sw+32` by
    simp[w2n_add_2] >>
  `w2n (dw+1w) <= w2n dw+1` by
    (simp[word_add_def] >> irule MOD_LESS_EQ >> simp[]) >>
  `LENGTH vs < dimword(:256)` by decide_tac >>
  `p.vs_memory = s.vs_memory /\ p.vs_alloca_next = s.vs_alloca_next /\
   ~p.vs_call_ctx.cc_static /\ allocas_from lo p` by
    (fs[execution_frame_def,allocas_from_def] >> metis_tac[]) >>
  qpat_x_assum `src = Var out` SUBST_ALL_TAC >>
  drule_at (Pat `compile_copy_elements_to_slots _ _ _ _ _ _ _ = _`)
    store_slots_elements_origin_ptr >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `~ctx_has_dalloca _`)) >>
  (impl_tac >- (asm_simp_tac bool_ss [] >>
    conj_tac >- (gen_tac >> disch_tac >>
      qpat_x_assum `!v. value_has_type tv v ==> _`
        (qspec_then `EL i vs` mp_tac) >>
      (impl_tac >- fs[all_have_type_EVERY,EVERY_EL]) >>
      asm_simp_tac bool_ss []) >>
    conj_tac >- (gen_tac >> strip_tac >> gvs[]) >> decide_tac)) >>
  disch_then (qx_choose_then `Gq` (qx_choose_then `tq`
    (qx_choose_then `q` (qx_choose_then `ks` strip_assume_tac)))) >>
  suspend "suffix"
QED

Resume store_slots_dynarray_origin_ptr[suffix]:
  qpat_x_assum `!v. value_has_type tv v ==> _` kall_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at s3 x` by
    (fs[ci_mono_def] >> metis_tac[freshWritesTheory.not_fresh_at_mono,cs_extends_trans]) >>
  `eval_operand dst q = SOME dw /\ op_prov Gq dst = NONE /\ op_taint tq dst = {}` by
    (Cases_on `dst` >> gvs[eval_operand_def,op_prov_def,op_taint_def] >> metis_tac[]) >>
  `eval_operand len q = SOME (n2w (LENGTH vs)) /\
   op_prov Gq len = NONE /\ op_taint tq len = {}` by
    (qpat_x_assum `len = Var lv` SUBST_ALL_TAC >>
     fs[eval_operand_def,op_prov_def,op_taint_def]) >>
  `allocas_from lo q /\ ~q.vs_call_ctx.cc_static` by (fs[allocas_from_def,execution_frame_def] >> metis_tac[]) >>
  drule_at (Pat `emit_void _ _ _ = _`) store_slots_length_suffix_origin_ptr >>
  disch_then (drule_at (Pat `eval_operand dst _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand len _ = _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `op_taint _ dst = _`)) >>
  disch_then (drule_at (Pat `op_prov _ dst = _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `~ctx_has_dalloca _`)) >>
  (impl_tac >- (asm_simp_tac bool_ss [])) >>
  disch_then (qx_choose_then `u` (qx_choose_then `tf` strip_assume_tac)) >>
  suspend "frames"
QED

Resume store_slots_dynarray_origin_ptr[frames]:
  qpat_assum `store_copy_normalize p q = _`
    (assume_tac o REWRITE_RULE [Once ADD_COMM]) >>
  qpat_assum `(if tr then tq.t_trans else tq.t_stor) = _`
    (assume_tac o REWRITE_RULE [Once ADD_COMM]) >>
  drule_all (PURE_REWRITE_RULE [MULT_CLAUSES,wordsTheory.n2w_11]
    (Q.INST [`so` |-> `1`] store_slots_frame_shift)) >> strip_tac >>
  qpat_x_assum `store_copy_normalize p q = FOLDL _ p ks` kall_tac >>
  qpat_x_assum `store_copy_normalize p q = FOLDL _ p ks` kall_tac >>
  qpat_x_assum `(if tr then tq.t_trans else tq.t_stor) = FOLDL _ _ ks` kall_tac >>
  qpat_x_assum `(if tr then tq.t_trans else tq.t_stor) = FOLDL _ _ ks` kall_tac >>
  drule_all store_slots_frame_pure_prefix >> strip_tac >>
  suspend "length_frame"
QED

Resume store_slots_dynarray_origin_ptr[length_frame]:
  `mload (w2n sw) q = n2w (LENGTH vs)` by
    (qpat_x_assum `!m. mem_agree_outside tn.t_mem s.vs_memory m ==> mem_word_at _ m = _`
      (qspec_then `s.vs_memory` mp_tac) >>
     simp_tac std_ss [mem_agree_outside_def,mem_word_at_eq_mload] >>
     disch_tac >> gvs[mload_def]) >>
  `mem_word_taint tq.t_mem (w2n sw) = {}` by
    (simp[mem_word_taint_def,pred_setTheory.EXTENSION] >> rpt strip_tac >>
     qpat_x_assum `!i. w2n sw <= i /\ i < w2n sw + 32 ==> _`
       (qspec_then `w2n sw+x` mp_tac) >> simp[] >> decide_tac) >>
  `store_copy_normalize q u = FOLDL (\a j. (if tr then tstore else sstore)
      (dw+n2w j) (mload (w2n sw+32*j) q) a) q [0] /\
   (if tr then tf.t_trans else tf.t_stor) = FOLDL (\ta j. key_update ta (dw+n2w j)
      (mem_word_taint tq.t_mem (w2n sw+32*j)))
      (if tr then tq.t_trans else tq.t_stor) [0]` by
    (conj_tac >- (Cases_on `tr` >>
       simp[store_copy_normalize_def,sstore_def,tstore_def,venom_state_component_equality,WORD_ADD_0]) >>
     simp[WORD_ADD_0] >> gvs[]) >>
  drule_all store_slots_frame_append >> strip_tac >>
  suspend "join"
QED

Resume store_slots_dynarray_origin_ptr[join]:
  qexistsl [`Gq`,`tf`,`u`,`MAP ((+) 1) ks ++ [0]`] >>
  conj_tac >- (rpt gen_tac >>
    irule (REWRITE_RULE [APPEND] (Q.INST [`left` |-> `[]`,`right` |-> `[]`]
      (SPEC_ALL gas_origin_ptr_path_append))) >>
    qexistsl [`Gq`,`q`,`(OK q,Gq,tq)`,`tq`] >> simp[] >>
    irule (REWRITE_RULE [APPEND] (Q.INST [`left` |-> `[]`,`right` |-> `[]`]
      (SPEC_ALL gas_origin_ptr_path_append))) >>
    qexistsl [`Gp`,`p`,`(OK p,Gp,tp)`,`tp`] >> simp[]) >>
  asm_simp_tac bool_ss [] >>
  conj_tac >- suspend "support" >>
  fs[execution_frame_def]
QED

Resume store_slots_dynarray_origin_ptr[support]:
  gen_tac >> drule store_slots_dynarray_encoding_support >>
  disch_then (qspec_then `j` mp_tac) >>
  qpat_x_assum `!k. MEM k ks <=> _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac bool_ss [MEM_APPEND,MEM,MEM_MAP] >>
  metis_tac[ADD_ASSOC]
QED

Finalise store_slots_dynarray_origin_ptr


Theorem store_slots_array_origin_ptr:
  (!v. value_has_type tv v ==> !root slot tr sa sb func s sw dw writes G tn.
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
  compile_store_slots cenv (Var root) dst (ArrayT ty sz) tr sa = ((),sb) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  is_abi_dynamic cenv.ce_struct_fields (ArrayT ty sz) /\
  type_memory_bytes cenv ty = type_memory_size tv /\ (case sz of Fixed n => n | Dynamic n => n) < dimword(:256) /\
  well_formed_type_value tv /\ value_has_type (ArrayTV tv sz) v /\
  not_fresh_at sa root /\ (!x. dst = Var x ==> not_fresh_at sa x) /\
  lookup_var root s = SOME sw /\ eval_operand dst s = SOME dw /\
  op_prov G dst = NONE /\ op_taint tn dst = {} /\
  ptr_covers G tn root s (val_store_size (ArrayTV tv sz) v) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory (ArrayTV tv sz) v (w2n sw) m) /\
  w2n sw + type_memory_size (ArrayTV tv sz) < dimword(:256) /\
  w2n dw + type_slot_size (ArrayTV tv sz) <= dimword(:256) /\
  encode_value (ArrayTV tv sz) v = SOME writes /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_call_ctx.cc_static /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  w2n sw + val_store_size (ArrayTV tv sz) v <= s.vs_alloca_next ==>
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
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> Cases_on `sz`
  >- (`?sparse. v = ArrayV (SArrayV sparse)` by
        (Cases_on `v` >> fs[value_has_type_def] >>
         rename1 `value_has_type _ (ArrayV av)` >> Cases_on `av` >> gvs[value_has_type_def]) >>
      qpat_x_assum `v = _` SUBST_ALL_TAC >> irule store_slots_fixed_array_origin_ptr >>
      asm_simp_tac bool_ss [] >> qexistsl [`cenv`,`dst`,`n`,`root`,`sparse`,`tv`,`ty`] >> asm_simp_tac bool_ss [] >> fs[] >> first_assum MATCH_ACCEPT_TAC) >>
  `?vs. v = ArrayV (DynArrayV vs)` by
    (Cases_on `v` >> fs[value_has_type_def] >>
     rename1 `value_has_type _ (ArrayV av)` >> Cases_on `av` >> gvs[value_has_type_def]) >>
  qpat_x_assum `v = _` SUBST_ALL_TAC >> irule store_slots_dynarray_origin_ptr >>
  asm_simp_tac bool_ss [] >> qexistsl [`n`,`cenv`,`dst`,`root`,`tv`,`ty`,`vs`] >>
  asm_simp_tac bool_ss [] >> fs[] >> first_assum MATCH_ACCEPT_TAC
QED
