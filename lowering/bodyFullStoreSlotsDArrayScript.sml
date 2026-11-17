Theory bodyFullStoreSlotsDArray
Ancestors
  bodyFullStoreSlotsElements bodyFullStoreSlotsAddresses
  bodyFullStoreSlotsOffset bodyFullStoreSlotsTaintStore bodyFullStoreSlotsTaintFold
  typedCopyOriginPtrDynArray fragGasOriginPtrDead placeStoreSlots

(* Promote the canonical clean header read to a horizon-uniform frame. *)
Theorem store_slots_dyn_header_read_uniform[local]:
  emit_op MLOAD [Var xs] a = (Var lv,b) /\
  not_fresh_at a xs /\ lookup_var xs s = SOME sw /\
  ptr_covers G tn xs s 32 /\
  w2n sw + 32 < dimword (:256) /\ w2n sw + 32 <= s.vs_alloca_next /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     mem_word_at (w2n sw) mem = n2w N) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  fn_has_code a b func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    eval_operand (Var lv) t = SOME (n2w N) /\ FLOOKUP Gf lv = NONE /\
    op_taint tf (Var lv) = {} /\ store_copy_normalize s t = s /\
    tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
    t.vs_call_ctx = s.vs_call_ctx /\ allocas_from lo t /\ ~t.vs_halted /\
    t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    (!p. not_fresh_at a p ==>
       lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
       op_taint tf (Var p) = op_taint tn (Var p)) /\
    (!p n. not_fresh_at a p /\ ptr_covers G tn p s n ==>
       ptr_covers Gf tf p t n)
Proof
  strip_tac >> `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by simp[] >>
  drule_all typed_copy_origin_ptr_dyn_read_path >>
  disch_then (qspecl_then [`0`,`0`,`explicit`,`PG`] strip_assume_tac) >>
  qexistsl [`t`,`Gf`,`tnf`] >> simp[] >>
  conj_tac >- (gen_tac >> irule gas_origin_ptr_path_from_no_dead >>
               goal_assum (drule_at Any)) >>
  gvs[typedMemoryCopyTheory.typed_copy_state_frame_def,
      stmtSimStoreCopyTheory.store_copy_normalize_def,
      venomStateTheory.venom_state_component_equality,
      ptrDisciplineTheory.allocas_from_def] >> metis_tac[]
QED

Theorem store_slots_dyn_taint_header_bound[local]:
  !ks X Y (dw:bytes32) sw M.
    Y SUBSET FOLDL (\Z j. key_update Z (dw+1w+n2w j)
      (mem_word_taint M (sw+32+32*j))) X ks ==>
    key_update Y dw {} SUBSET
      FOLDL (\Z j. key_update Z (dw+n2w j)
        (mem_word_taint M (sw+32*j))) X (MAP SUC ks ++ [0])
Proof
  rpt gen_tac >> strip_tac >>
  simp[rich_listTheory.FOLDL_APPEND, wordsTheory.WORD_ADD_0] >>
  irule lowerDloadMaskedStorageTheory.ld_key_update_mono >> simp[] >>
  qpat_x_assum `Y SUBSET _` mp_tac >>
  pure_rewrite_tac[rich_listTheory.FOLDL_MAP] >>
  BETA_TAC >>
  simp_tac bool_ss [wordsTheory.n2w_SUC,
       AC wordsTheory.WORD_ADD_ASSOC wordsTheory.WORD_ADD_COMM,
       AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM,
       arithmeticTheory.MULT_CLAUSES]
QED

Theorem store_slots_dyn_compile_layout[local]:
  acyclic_struct_metadata cenv.ce_struct_fields /\
  compile_store_slots cenv src dst (ArrayT elem (Dynamic n)) tr sa = ((),sb) /\
  fn_has_code sa sb func ==>
  ?cnt data slot s1 s2 sc se.
    emit_op MLOAD [src] sa = (cnt,s1) /\
    emit_op ADD [src; Lit 32w] s1 = (data,s2) /\
    emit_op ADD [dst; Lit 1w] s2 = (slot,sc) /\
    compile_copy_elements_to_slots cenv data slot elem cnt tr sc = ((),se) /\
    emit_void (if tr then TSTORE else SSTORE) [dst;cnt] se = ((),sb) /\
    cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 sc /\
    cs_extends sc se /\ cs_extends se sb /\
    fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
    fn_has_code s2 sc func /\ fn_has_code sc se func /\ fn_has_code se sb func
Proof
  strip_tac >>
  qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` mp_tac >>
  simp[Once contextTheory.compile_store_slots_def,
       compileEnvTheory.is_abi_dynamic_def, compileEnvTheory.is_bytestring_type_def,
       compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.comp_return_def, AllCaseEqs()] >>
  ntac 4 (pairarg_tac >> simp[]) >> strip_tac >>
  rename1 `emit_op MLOAD [src] sa = (cnt,s1)` >>
  rename1 `emit_op ADD [src; Lit 32w] s1 = (data,s2)` >>
  rename1 `emit_op ADD [dst; Lit 1w] s2 = (slot,sc)` >>
  rename1 `emit_void (if tr then TSTORE else SSTORE) [dst;cnt] se = ((),sb)` >>
  Cases_on `_0` >> imp_res_tac typedMemoryCopyTheory.typed_copy_emit_op_mono >>
  `exprLoweringProps$ci_mono sc se` by
    (mp_tac (cj 3 stmtLoweringMonoTheory.ci_mono_compile_store_slots) >>
     disch_then (qspecl_then [`cenv`,`data`,`slot`,`elem`,`cnt`,`tr`,`sc`] mp_tac) >> simp[]) >>
  `exprLoweringProps$ci_mono se sb` by
    (mp_tac (Q.SPECL [`if tr then TSTORE else SSTORE`,`[dst;cnt]`,`se`]
      exprLoweringPropsTheory.ci_mono_emit_void) >> simp[]) >>
  `cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 sc /\
   cs_extends sc se /\ cs_extends se sb` by
    gvs[exprLoweringPropsTheory.ci_mono_def] >>
  simp[] >>
  metis_tac[fragExecTheory.fn_has_code_split, compileEnvTheory.cs_extends_trans]
QED

Theorem store_slots_dyn_data_uniform[local]:
  emit_op ADD [Var x; Lit 32w] a = (data,b) /\
  fn_has_code a b func /\ cs_extends a b /\ not_fresh_at a x /\
  eval_operand (Var x) s = SOME sw /\ op_taint tn (Var x) = {} /\
  ptr_covers G tn x s (32+B) /\ w2n sw+32+B < dimword(:256) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?d q H u.
    data = Var d /\ not_fresh_at b d /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK q,H,u)) /\
    eval_operand data q = SOME (sw+32w) /\ op_taint u data = {} /\
    ptr_covers H u d q B /\ store_copy_normalize s q = s /\
    q.vs_memory = s.vs_memory /\ q.vs_allocas = s.vs_allocas /\
    q.vs_alloca_next = s.vs_alloca_next /\ q.vs_labels = s.vs_labels /\
    q.vs_call_ctx = s.vs_call_ctx /\ allocas_from lo q /\ ~q.vs_halted /\
    q.vs_current_bb = b.cs_current_bb /\
    q.vs_inst_idx = LENGTH b.cs_current_insts /\
    u.t_mem = tn.t_mem /\ u.t_imm = tn.t_imm /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\
    (!p. not_fresh_at a p ==>
      lookup_var p q = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
      op_taint u (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `eval_operand (Lit 32w) s = SOME 32w /\ op_taint tn (Lit 32w) = {}` by
    simp[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`, `w` |-> `x+y`]
    store_address_binop_uniform)) >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_origin_ptr_path _ _ [] (OK q,H,u)` >>
  `ptr_covers H u out q B` by
    (simp[Abbr `H`,Abbr `u`,Abbr `q`] >>
     irule (Q.INST [`off` |-> `32`, `total` |-> `32+B`]
       (SPEC_ALL typedCopyOriginPtrBaseTheory.typed_copy_origin_ptr_offset_covers)) >>
     simp[] >> fs[venomStateTheory.eval_operand_def] >>
     qexists `B+32` >> simp[]) >>
  qexistsl [`out`,`q`,`H`,`u`] >>
  simp[Abbr `q`,venomStateTheory.update_var_def,
       stmtSimStoreCopyTheory.store_copy_normalize_def] >>
  simp[venomStateTheory.venom_state_component_equality]
QED

Theorem store_slots_dyn_addresses_uniform[local]:
  emit_op ADD [Var x; Lit 32w] a = (data,b) /\
  emit_op ADD [dst; Lit 1w] b = (slot,c) /\
  fn_has_code a b func /\ fn_has_code b c func /\
  cs_extends a b /\ cs_extends b c /\ not_fresh_at a x /\
  (!p. dst = Var p ==> not_fresh_at a p) /\
  eval_operand (Var x) s = SOME sw /\ eval_operand dst s = SOME dw /\
  op_taint tn (Var x) = {} /\ op_taint tn dst = {} /\
  ptr_covers G tn x s (32+B) /\ w2n sw+32+B < dimword(:256) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?d q H u.
    data = Var d /\ not_fresh_at c d /\
    (!p. slot = Var p ==> not_fresh_at c p) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK q,H,u)) /\
    eval_operand data q = SOME (sw+32w) /\ op_taint u data = {} /\
    ptr_covers H u d q B /\
    eval_operand slot q = SOME (dw+1w) /\ op_taint u slot = {} /\
    store_copy_normalize s q = s /\
    q.vs_memory = s.vs_memory /\ q.vs_allocas = s.vs_allocas /\
    q.vs_alloca_next = s.vs_alloca_next /\ q.vs_labels = s.vs_labels /\
    q.vs_call_ctx = s.vs_call_ctx /\ allocas_from lo q /\ ~q.vs_halted /\
    q.vs_current_bb = c.cs_current_bb /\
    q.vs_inst_idx = LENGTH c.cs_current_insts /\
    u.t_mem = tn.t_mem /\ u.t_imm = tn.t_imm /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\
    (!p. not_fresh_at a p ==>
      lookup_var p q = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
      op_taint u (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all store_slots_dyn_data_uniform >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `!p. not_fresh_at a p ==> not_fresh_at b p` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists `a` >>
     metis_tac[typedMemoryCopyTheory.typed_copy_emit_op_mono,
       exprLoweringPropsTheory.ci_mono_def]) >>
  `eval_operand dst q = SOME dw /\ op_taint u dst = {}` by
    (Cases_on `dst` >> fs[venomStateTheory.eval_operand_def,
       ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  `eval_operand (Lit 1w) q = SOME 1w /\ op_taint u (Lit 1w) = {}` by
    simp[venomStateTheory.eval_operand_def,ptrDisciplineTheory.op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`, `w` |-> `x+y`]
    store_address_binop_uniform)) >>
  disch_then (qspecl_then [`explicit`,`PG`,`H`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_origin_ptr_path _ (q,_,_) [] (OK r,J,v)` >>
  `ptr_covers J v d r B` by
    (irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >> metis_tac[]) >>
  `not_fresh_at c d` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists `b` >>
     metis_tac[typedMemoryCopyTheory.typed_copy_emit_op_mono,
       exprLoweringPropsTheory.ci_mono_def]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK r,J,v)` by
    (gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl [`H`,`q`,`u`] >> simp[]) >>
  `eval_operand data r = SOME (sw+32w) /\ op_taint v data = {}` by
    gvs[venomStateTheory.eval_operand_def] >>
  `r.vs_memory = s.vs_memory /\ r.vs_allocas = s.vs_allocas /\
   r.vs_alloca_next = s.vs_alloca_next /\ r.vs_labels = s.vs_labels /\
   r.vs_call_ctx = s.vs_call_ctx /\ ~r.vs_halted /\
   r.vs_current_bb = c.cs_current_bb /\
   r.vs_inst_idx = LENGTH c.cs_current_insts` by
    simp[Abbr `r`,venomStateTheory.update_var_def] >>
  qexistsl [`d`,`r`,`J`,`v`] >> simp[] >>
  conj_tac >- simp[Abbr `r`,venomStateTheory.eval_operand_def,
    venomStateTheory.lookup_var_def,venomStateTheory.update_var_def,
    finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[Abbr `r`]
QED

Theorem store_slots_dyn_prefix_uniform[local]:
  emit_op MLOAD [Var x] a = (Var lv,b) /\
  emit_op ADD [Var x; Lit 32w] b = (data,c) /\
  emit_op ADD [dst; Lit 1w] c = (slot,e) /\
  fn_has_code a b func /\ fn_has_code b c func /\ fn_has_code c e func /\
  cs_extends a b /\ cs_extends b c /\ cs_extends c e /\
  not_fresh_at a x /\ (!p. dst = Var p ==> not_fresh_at a p) /\
  eval_operand (Var x) s = SOME sw /\ eval_operand dst s = SOME dw /\
  op_taint tn (Var x) = {} /\ op_taint tn dst = {} /\
  ptr_covers G tn x s (32+B) /\ w2n sw+32+B < dimword(:256) /\
  w2n sw+32+B <= s.vs_alloca_next /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     mem_word_at (w2n sw) mem = n2w N) /\
  fn_inst_ids_distinct func /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?d q H u.
    data = Var d /\ not_fresh_at e d /\ not_fresh_at e lv /\
    (!p. slot = Var p ==> not_fresh_at e p) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK q,H,u)) /\
    eval_operand (Var lv) q = SOME (n2w N) /\ FLOOKUP H lv = NONE /\
    op_taint u (Var lv) = {} /\
    eval_operand data q = SOME (sw+32w) /\ op_taint u data = {} /\
    ptr_covers H u d q B /\
    eval_operand slot q = SOME (dw+1w) /\ op_taint u slot = {} /\
    eval_operand dst q = SOME dw /\ op_taint u dst = {} /\
    store_copy_normalize s q = s /\
    q.vs_memory = s.vs_memory /\ q.vs_allocas = s.vs_allocas /\
    q.vs_alloca_next = s.vs_alloca_next /\ q.vs_labels = s.vs_labels /\
    q.vs_call_ctx = s.vs_call_ctx /\ allocas_from lo q /\ lo <= q.vs_alloca_next /\
    ~q.vs_halted /\ q.vs_current_bb = e.cs_current_bb /\
    q.vs_inst_idx = LENGTH e.cs_current_insts /\
    u.t_mem = tn.t_mem /\ u.t_imm = tn.t_imm /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\
    (!p. not_fresh_at a p ==>
      lookup_var p q = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
      op_taint u (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `lookup_var x s = SOME sw /\ ptr_covers G tn x s 32 /\
   w2n sw+32 < dimword(:256) /\ w2n sw+32 <= s.vs_alloca_next` by
    (conj_tac >- gvs[venomStateTheory.eval_operand_def] >>
     simp[] >> irule reasonCopySourcePtrTheory.ptr_covers_mono >>
     qexists `32+B` >> simp[]) >>
  drule_all store_slots_dyn_header_read_uniform >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `!p. not_fresh_at a p ==> not_fresh_at b p` by
    metis_tac[typedMemoryCopyTheory.typed_copy_emit_op_mono,
      exprLoweringPropsTheory.ci_mono_def, freshWritesTheory.not_fresh_at_mono] >>
  `not_fresh_at b lv` by
    (qpat_assum `emit_op MLOAD _ _ = _`
       (mp_then Any mp_tac emitHelperPropsTheory.emitted_insts_emit_op) >>
     gvs[loweringStateRelDefsTheory.not_fresh_at_def]) >>
  `eval_operand (Var x) t = SOME sw /\ op_taint tf (Var x) = {} /\
   eval_operand dst t = SOME dw /\ op_taint tf dst = {} /\
   ptr_covers Gf tf x t (32+B)` by
    (Cases_on `dst` >> fs[venomStateTheory.eval_operand_def,
      ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  `not_fresh_at b x /\ (!p. dst = Var p ==> not_fresh_at b p)` by
    metis_tac[] >>
  drule_all store_slots_dyn_addresses_uniform >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `not_fresh_at e lv` by
    metis_tac[typedMemoryCopyTheory.typed_copy_emit_op_mono,
      exprLoweringPropsTheory.ci_mono_def, freshWritesTheory.not_fresh_at_mono] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK q,H,u)` by
    (gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl [`Gf`,`t`,`tf`] >> simp[]) >>
  qexistsl [`d`,`q`,`H`,`u`] >> simp[] >>
  `store_copy_normalize s q = s` by
    (qpat_x_assum `store_copy_normalize t q = t` mp_tac >>
     qpat_x_assum `store_copy_normalize s t = s` mp_tac >>
     simp[stmtSimStoreCopyTheory.store_copy_normalize_def,
       venomStateTheory.venom_state_component_equality]) >>
  Cases_on `dst` >> gvs[venomStateTheory.eval_operand_def,
    ptrDisciplineTheory.op_taint_def]
QED

val dyn_child = ``
 !ty tv v src dst tr sa sb s sw dw tn G writes func ctx lo explicit PG.
  type_rank cenv.ce_struct_fields ty < type_rank cenv.ce_struct_fields (ArrayT elem (Dynamic n)) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !rt. evaluate_type tenv fty = SOME rt ==>
              sz = type_memory_size rt) fields) /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\
  compile_store_slots cenv src dst ty tr sa = ((),sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  op_taint tn src = {} /\ op_taint tn dst = {} /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory tv v (w2n sw) mem) /\
  (type_memory_size tv <> 0 ==>
     ?x. src = Var x /\ ptr_covers G tn x s (type_memory_size tv)) /\
  w2n sw + type_memory_size tv < dimword (:256) /\
  w2n dw + type_slot_size tv <= dimword (:256) /\
  (type_memory_size tv = 0 \/
   w2n sw + type_memory_size tv <= s.vs_alloca_next) /\
  encode_value tv v = SOME writes /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_call_ctx.cc_static /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t ks Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK t,Gf,tnf)) /\
    store_copy_normalize s t =
      FOLDL (\q j. (if tr then tstore else sstore) (dw+n2w j)
         (mload (w2n sw+32*j) s) q) s ks /\
    (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
    (!x. not_fresh_at sa x ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tnf (Var x) = op_taint tn (Var x)) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
    (if tr then tnf.t_stor = tn.t_stor else tnf.t_trans = tn.t_trans) /\
    (if tr then tnf.t_trans else tnf.t_stor) SUBSET
      FOLDL (\X j. key_update X (dw+n2w j)
         (mem_word_taint tn.t_mem (w2n sw+32*j)))
        (if tr then tn.t_trans else tn.t_stor) ks /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts``;

Theorem compile_store_slots_dynarray_origin_ptr_path:
 !cenv tenv elem n. (^dyn_child) ==>
 !tv v src dst tr sa sb s sw dw tn G writes func ctx lo explicit PG.
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !rt. evaluate_type tenv fty = SOME rt ==>
              sz = type_memory_size rt) fields) /\
  evaluate_type tenv (ArrayT elem (Dynamic n)) = SOME tv /\ value_has_type tv v /\
  compile_store_slots cenv src dst (ArrayT elem (Dynamic n)) tr sa = ((),sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  op_taint tn src = {} /\ op_taint tn dst = {} /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory tv v (w2n sw) mem) /\
  (type_memory_size tv <> 0 ==>
     ?x. src = Var x /\ ptr_covers G tn x s (type_memory_size tv)) /\
  w2n sw + type_memory_size tv < dimword (:256) /\
  w2n dw + type_slot_size tv <= dimword (:256) /\
  (type_memory_size tv = 0 \/
   w2n sw + type_memory_size tv <= s.vs_alloca_next) /\
  encode_value tv v = SOME writes /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_call_ctx.cc_static /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t ks Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK t,Gf,tnf)) /\
    store_copy_normalize s t =
      FOLDL (\q j. (if tr then tstore else sstore) (dw+n2w j)
         (mload (w2n sw+32*j) s) q) s ks /\
    (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
    (!x. not_fresh_at sa x ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tnf (Var x) = op_taint tn (Var x)) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
    (if tr then tnf.t_stor = tn.t_stor else tnf.t_trans = tn.t_trans) /\
    (if tr then tnf.t_trans else tnf.t_stor) SUBSET
      FOLDL (\X j. key_update X (dw+n2w j)
         (mem_word_taint tn.t_mem (w2n sw+32*j)))
        (if tr then tn.t_trans else tn.t_stor) ks /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> disch_then (mk_asm "child") >> rpt gen_tac >> strip_tac >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(),
      valueEncodingTheory.type_memory_size_def] >>
  rename1 `evaluate_type tenv elem = SOME etv` >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
  rename1 `value_has_type (ArrayTV etv (Dynamic n)) (ArrayV av)` >>
  Cases_on `av` >> gvs[vyperTypingTheory.value_has_type_def] >>
  drule_all store_slots_dyn_compile_layout >> strip_tac >>
  qpat_assum `emit_op MLOAD _ _ = _`
    (mp_then Any strip_assume_tac emitHelperPropsTheory.emitted_insts_emit_op) >>
  gvs[] >>
  `not_fresh_at sa x /\ (!p. dst = Var p ==> not_fresh_at sa p)` by
    metis_tac[] >>
  `ptr_covers G tn x s (32+n*type_memory_size etv) /\
   w2n sw+32+n*type_memory_size etv < dimword(:256) /\
   w2n sw+32+n*type_memory_size etv <= s.vs_alloca_next` by
    metis_tac[arithmeticTheory.ADD_COMM, arithmeticTheory.ADD_ASSOC] >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     mem_word_at (w2n sw) mem = n2w (LENGTH l)` by
    metis_tac[valueEncodingPropsTheory.val_in_memory_dynarray] >>
  drule_all store_slots_dyn_prefix_uniform >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  mp_tac compile_copy_elements_to_slots_origin_ptr_path_conditional >>
  (impl_tac >- (rpt (pop_assum kall_tac) >> conj_tac
    >- (rpt gen_tac >> strip_tac >>
        drule_all store_slots_addresses_origin_ptr_path >> simp[]) >>
    rpt gen_tac >> strip_tac >> irule store_slots_taint_fold_mono >> simp[])) >>
  disch_then (qspecl_then [`cenv`,`tenv`,`elem`,`etv`] mp_tac) >>
  (impl_tac >- (rpt gen_tac >> strip_tac >>
    asm "child" (qspec_then `elem` irule) >>
    simp[typedCopyDomainTheory.type_rank_def] >> metis_tac[])) >>
  disch_then (mk_asm "elements") >> suspend "payload"
QED

Resume compile_store_slots_dynarray_origin_ptr_path[payload]:
  `type_memory_bytes cenv elem = type_memory_size etv` by
    (irule typedMemoryCopyTheory.typed_copy_memory_size >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `!i. i < LENGTH l ==>
     value_has_type etv (EL i l) /\ IS_SOME (encode_value etv (EL i l)) /\
     !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
       val_in_memory etv (EL i l)
         (w2n sw+32+i*type_memory_size etv) mem` by
    (gen_tac >> strip_tac >> conj_tac
     >- gvs[vyperTypingTheory.all_have_type_EVERY, listTheory.EVERY_EL] >>
     conj_tac
     >- (irule store_slots_dyn_element_encoded >>
         simp[] >> qexists_tac `1` >>
         qpat_x_assum `encode_value (ArrayTV _ _) _ = _` mp_tac >>
         simp[Once vyperStorageTheory.encode_value_def, AllCaseEqs()] >>
         metis_tac[]) >>
     gen_tac >> strip_tac >>
     qpat_x_assum `!mem. _ ==> val_in_memory (ArrayTV _ _) _ _ _`
       drule >>
     simp[valueEncodingPropsTheory.val_in_memory_dynarray] >> strip_tac >>
     drule_all exprSimAggregateEncodingTheory.elems_in_memory_EL >> simp[]) >>
  `LENGTH l * type_memory_size etv <= n * type_memory_size etv /\
   LENGTH l * type_slot_size etv <= n * type_slot_size etv /\
   LENGTH l <= LENGTH l * type_slot_size etv /\
   0 < n * type_slot_size etv` by simp[] >>
  `w2n sw+32+LENGTH l*type_memory_size etv < dimword(:256) /\
   w2n dw+1+LENGTH l*type_slot_size etv <= dimword(:256) /\
   LENGTH l < dimword(:256) /\ w2n dw+1 < dimword(:256)` by
    (qpat_x_assum `type_slot_size (ArrayTV _ _) + _ <= _` mp_tac >>
     pure_rewrite_tac[vyperValueTheory.type_slot_size_def] >>
     rpt strip_tac >> decide_tac) >>
  `w2n (sw+32w) = w2n sw+32 /\ w2n (dw+1w) = w2n dw+1` by
    (gvs[wordsTheory.word_add_def, wordsTheory.dimword_def]) >>
  suspend "execute_payload"
QED

Resume compile_store_slots_dynarray_origin_ptr_path[execute_payload]:
  asm_x "elements" (qspecl_then [`\i. EL i l`,`LENGTH l`,`data`,`slot`,
    `Var (STRING #"%" (toString sa.cs_next_var))`,`tr`,`sc`,`se`,`func`,
    `q`,`sw+32w`,`dw+1w`,`u`,`H`,`ctx`,`lo`,`explicit`,`PG`] mp_tac) >>
  (impl_tac >- (asm_x "child" kall_tac >>
    simp[ptrDisciplineTheory.op_prov_def] >>
    conj_tac >- metis_tac[] >>
    conj_tac >- (qpat_x_assum `!i. i < LENGTH l ==> value_has_type _ _ /\ _` mp_tac >>
      rpt (pop_assum kall_tac) >>
      simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
    conj_tac >- metis_tac[] >>
    qpat_x_assum `ptr_covers H u d q _` mp_tac >>
    qpat_x_assum `LENGTH l * type_memory_size etv <= _` mp_tac >>
    rpt (pop_assum kall_tac) >>
    simp[bodyPtrDefsTheory.ptr_covers_def] >> rpt strip_tac >>
    qexistsl_tac [`w`,`b`,`sz'`] >> simp[] >>
    `LENGTH l * type_memory_size etv <= n * type_memory_size etv` by simp[] >>
    decide_tac)) >>
  strip_tac >> suspend "header"
QED

Resume compile_store_slots_dynarray_origin_ptr_path[header]:
  `cs_extends sa sc` by metis_tac[compileEnvTheory.cs_extends_trans] >>
  `!p. dst = Var p ==> not_fresh_at sc p` by
    (qpat_x_assum `!p. dst = Var p ==> not_fresh_at sa p` mp_tac >>
     qpat_x_assum `emit_op MLOAD _ _ = _` mp_tac >>
     qpat_x_assum `emit_op ADD _ s1 = _` mp_tac >>
     qpat_x_assum `emit_op ADD _ s2 = _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     imp_res_tac typedMemoryCopyTheory.typed_copy_emit_op_mono >>
     fs[exprLoweringPropsTheory.ci_mono_def] >>
     irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >>
     simp[] >> decide_tac) >>
  `eval_operand dst t = SOME dw /\ op_taint tnf dst = {}` by
    (Cases_on `dst` >> gvs[venomStateTheory.eval_operand_def,
       ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  `eval_operand (Var (STRING #"%" (toString sa.cs_next_var))) t =
     SOME (n2w (LENGTH l)) /\
   op_taint tnf (Var (STRING #"%" (toString sa.cs_next_var))) = {}` by
    (gvs[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  `allocas_from lo t` by
    (fs[ptrDisciplineTheory.allocas_from_def] >> metis_tac[]) >>
  `~t.vs_call_ctx.cc_static` by metis_tac[] >>
  drule_all storage_tainted_word_store_origin_ptr >>
  disch_then (qspecl_then [`explicit`,`PG`,`Gf`] assume_tac) >>
  suspend "join"
QED

Resume compile_store_slots_dynarray_origin_ptr_path[join]:
  qmatch_asmsub_abbrev_tac `OK fin,Gf,ft` >>
  qexistsl_tac [`fin`,`MAP SUC ks ++ [0]`,`Gf`,`ft`] >>
  conj_tac
  >- (gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
      qexistsl_tac [`Gf`,`t`,`tnf`] >> simp[] >>
      irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
      qexistsl_tac [`H`,`q`,`u`] >> simp[]) >>
  conj_tac
  >- (`store_copy_normalize s fin =
        FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
          (mload (w2n sw + 32*j) s) q) s (MAP SUC ks ++ [0])`
        suffices_by simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
      irule placeStoreSlotsTheory.store_slots_dyn_fold_header >>
      conj_tac >- decide_tac >>
      qexistsl_tac [`q`,`t`] >> simp[] >>
      `mload (w2n sw) s = n2w (LENGTH l)` by
        (qpat_x_assum `!mem. mem_agree_outside _ _ mem ==> mem_word_at _ mem = _`
          (qspec_then `s.vs_memory` mp_tac) >>
         simp[bodyPtrDefsTheory.mem_agree_outside_def, valueEncodingPropsTheory.mem_word_at_eq_mload]) >>
      Cases_on `tr` >>
      simp[Abbr `fin`, stmtSimStoreCopyTheory.store_copy_normalize_def,
        venomStateTheory.sstore_def, venomStateTheory.tstore_def,
        venomStateTheory.venom_state_component_equality]) >>
  conj_tac
  >- (drule placeStoreSlotsTheory.store_slots_dynarray_encoding_support >>
      disch_then (fn th => rewrite_tac[th]) >>
      simp_tac (srw_ss()) [listTheory.MEM_APPEND, listTheory.MEM_MAP] >>
      qpat_x_assum `!k. MEM k ks <=> _` (fn th => rewrite_tac[th]) >>
      POP_ASSUM_LIST (K all_tac) >>
      simp_tac (srw_ss()) [listTheory.MEM_MAP, arithmeticTheory.ADD1,
        AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
      gen_tac >> eq_tac >> strip_tac >> gvs[]
      >- (rename1 `MEM pair writes` >>
          qexistsl_tac [`i`,`writes`,`FST pair`] >> simp[] >> metis_tac[])
      >- (qexists_tac `FST y + i * type_slot_size etv` >>
          conj_tac >- decide_tac >>
          qexistsl_tac [`i`,`ew`,`FST y`] >> simp[] >> metis_tac[])) >>
  suspend "frames"
QED

Resume compile_store_slots_dynarray_origin_ptr_path[frames]:
  `!p. not_fresh_at sa p ==> not_fresh_at sc p` by
    (qpat_x_assum `emit_op MLOAD _ _ = _` mp_tac >>
     qpat_x_assum `emit_op ADD _ s1 = _` mp_tac >>
     qpat_x_assum `emit_op ADD _ s2 = _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     imp_res_tac typedMemoryCopyTheory.typed_copy_emit_op_mono >>
     fs[exprLoweringPropsTheory.ci_mono_def] >>
     irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >>
     simp[] >> decide_tac) >>
  conj_tac
  >- (gen_tac >> strip_tac >>
      `not_fresh_at sc x'` by metis_tac[] >>
      qpat_x_assum `!x. not_fresh_at sc x ==> _`
        (qspec_then `x'` mp_tac) >>
      qpat_x_assum `!p. not_fresh_at sa p ==> lookup_var _ _ = _ /\ _`
        (qspec_then `x'` mp_tac) >>
      simp[] >> rpt strip_tac >> Cases_on `tr` >>
      gvs[Abbr `fin`, Abbr `ft`, venomStateTheory.sstore_def,
        venomStateTheory.tstore_def, venomStateTheory.lookup_var_def,
        ptrDisciplineTheory.op_taint_def]) >>
  `sb.cs_current_bb = se.cs_current_bb` by
    (drule exprLoweringPropsTheory.emit_void_same_blocks >>
     simp[exprLoweringPropsTheory.same_blocks_def]) >>
  `key_update (if tr then tnf.t_trans else tnf.t_stor) dw {} SUBSET
    FOLDL (\X j. key_update X (dw+n2w j)
      (mem_word_taint tn.t_mem (w2n sw+32*j)))
      (if tr then tn.t_trans else tn.t_stor) (MAP SUC ks ++ [0])` by
    (irule store_slots_dyn_taint_header_bound >>
     qpat_x_assum `(if tr then tnf.t_trans else tnf.t_stor) SUBSET _` mp_tac >>
     simp[] >>
     simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  Cases_on `tr` >>
  gvs[Abbr `fin`, Abbr `ft`, venomStateTheory.sstore_def,
    venomStateTheory.tstore_def]
QED

Finalise compile_store_slots_dynarray_origin_ptr_path
