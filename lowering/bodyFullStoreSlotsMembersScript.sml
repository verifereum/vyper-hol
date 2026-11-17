Theory bodyFullStoreSlotsMembers
Ancestors
  bodyFullStoreSlotsOffset bodyFullStoreSlotsTaintFold bodyFullStoreSlotsElements placeStoreSlots
  typedCopyOriginPtrBase typedMemoryCopy bodyFullStoreSlotsRetired
  fragGasOriginPtrLoop emitHelperProps emitHelper compileEnv
  ptrDiscipline venomState venomExecSemantics venomInst codegenRel
  contextCodegenRel memSafeRun finite_map pred_set list words arithmetic
  context stmtLowering fragGasCopyLoop stmtSimStoreCopy fragGasOriginPtr exprSimCopy

(* Expanded lower-rank hypothesis; no new logical predicate. *)
val members_child = ``
 !ty tv v.
 type_rank cenv.ce_struct_fields ty < n ==>
 !src dst tr sa sb s sw dw tn G writes func ctx lo explicit PG.
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
  w2n sw + type_memory_size tv < dimword(:256) /\
  w2n dw + type_slot_size tv <= dimword(:256) /\
  (type_memory_size tv = 0 \/ w2n sw + type_memory_size tv <= s.vs_alloca_next) /\
  encode_value tv v = SOME writes /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_call_ctx.cc_static /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t ks Gf tf.
   (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (s,G,tn) [] (OK t,Gf,tf)) /\
   store_copy_normalize s t =
     FOLDL (\q j. (if tr then tstore else sstore) (dw+n2w j)
       (mload (w2n sw+32*j) s) q) s ks /\
   (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
   (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
     FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
   tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
   (if tr then tf.t_stor = tn.t_stor else tf.t_trans = tn.t_trans) /\
   (if tr then tf.t_trans else tf.t_stor) SUBSET
     FOLDL (\X j. key_update X (dw+n2w j)
       (mem_word_taint tn.t_mem (w2n sw+32*j)))
       (if tr then tn.t_trans else tn.t_stor) ks /\
   t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
   t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
   t.vs_call_ctx = s.vs_call_ctx /\ ~t.vs_halted /\
   t.vs_current_bb = sb.cs_current_bb /\
   t.vs_inst_idx = LENGTH sb.cs_current_insts``;

val members_result = ``
 ?t ks Gf tf.
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK t,Gf,tf)) /\
  store_copy_normalize s t =
    FOLDL (\q j. (if tr then tstore else sstore) (dw+n2w j)
      (mload (w2n (sw:256 word)+32*j) s) q) s ks /\
  (!k. MEM k ks <=> ?i writes j. i < LENGTH tvs /\
    encode_value (EL i tvs) (EL i vs) = SOME writes /\
    MEM j (MAP FST writes) /\ k = so+tuple_prefix_slot_size i tvs+j) /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
  (if tr then tf.t_stor = tn.t_stor else tf.t_trans = tn.t_trans) /\
  (if tr then tf.t_trans else tf.t_stor) SUBSET
    FOLDL (\X j. key_update X (dw+n2w j)
      (mem_word_taint tn.t_mem (w2n sw+32*j)))
      (if tr then tn.t_trans else tn.t_stor) ks /\
  t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
  t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
  t.vs_call_ctx = s.vs_call_ctx /\ ~t.vs_halted /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts``;

val members_case = ``
 !tvs vs mo so src slot tr sa sb func s sw dw tn G ctx lo explicit PG.
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !rt. evaluate_type tenv fty = SOME rt ==>
      sz = type_memory_size rt) fields) /\
  compile_store_slots_members cenv src slot members mo so tr sa = ((),sb) /\
  LIST_REL (\(ty,sz) (tv,v). sz = type_memory_size tv /\
    type_rank cenv.ce_struct_fields ty < n /\
    evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\
    IS_SOME (encode_value tv v)) members (ZIP (tvs,vs)) /\
  LENGTH vs = LENGTH tvs /\ mo = 32*so /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    tuple_in_memory vs tvs (w2n sw+mo) mem) /\
  (!x. src = Var x \/ slot = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
  op_taint tn src = {} /\ op_taint tn slot = {} /\
  (type_memory_size_list tvs <> 0 ==> ?x. src = Var x /\
    ptr_covers G tn x s (mo+type_memory_size_list tvs)) /\
  w2n sw+mo+type_memory_size_list tvs < dimword(:256) /\
  w2n dw+so+type_slot_size_list tvs <= dimword(:256) /\
  (type_memory_size_list tvs = 0 \/
    w2n sw+mo+type_memory_size_list tvs <= s.vs_alloca_next) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_call_ctx.cc_static /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ^members_result``;

val members_goal = ``!members. ^members_case``;

Theorem members_sparse_support_cons[local]:
 encode_value tv v = SOME writes /\
 (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
 (!k. MEM k tailks <=> ?i ws j. i < LENGTH tvs /\
   encode_value (EL i tvs) (EL i vs) = SOME ws /\
   MEM j (MAP FST ws) /\
   k = j+(so+type_slot_size tv+tuple_prefix_slot_size i tvs)) ==>
 !k. MEM k (MAP (\j. so+j) ks ++ tailks) <=>
   ?i ws j. i < SUC (LENGTH tvs) /\
   encode_value (EL i (tv::tvs)) (EL i (v::vs)) = SOME ws /\
   MEM j (MAP FST ws) /\
   k = j+(so+tuple_prefix_slot_size i (tv::tvs))
Proof
 strip_tac >> gen_tac >> simp[MEM_APPEND, MEM_MAP] >> eq_tac
 >- (strip_tac
     >- (qexistsl [`0`,`writes`,`j`] >>
         fs[vyperStateTheory.tuple_prefix_slot_size_def] >> metis_tac[ADD_COMM]) >>
     qexistsl [`SUC i`,`ws`,`j`] >>
     pure_rewrite_tac[EL, TL, vyperStateTheory.tuple_prefix_slot_size_def,
       prim_recTheory.LESS_MONO_EQ] >>
     simpLib.ASM_SIMP_TAC bool_ss [ADD_ASSOC] >> metis_tac[]) >>
 strip_tac >> Cases_on `i`
 >- (gvs[vyperStateTheory.tuple_prefix_slot_size_def] >> metis_tac[ADD_COMM]) >>
 rename1 `SUC ni < SUC (LENGTH tvs)` >>
 disj2_tac >> qexistsl [`ni`,`ws`,`j`] >>
 RULE_ASSUM_TAC (PURE_REWRITE_RULE [EL, TL,
   vyperStateTheory.tuple_prefix_slot_size_def, prim_recTheory.LESS_MONO_EQ]) >>
 simpLib.ASM_SIMP_TAC bool_ss [ADD_ASSOC] >> metis_tac[]
QED

Theorem members_head_memory_entry[local]:
 (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
   tuple_in_memory (v::vs) (tv::tvs) (32*so+w2n sw) mem) /\
 t.vs_memory = s.vs_memory /\ tt.t_mem = tn.t_mem /\
 32*so+(type_memory_size_list (tv::tvs)+w2n sw) < dimword(:256) /\
 so+(type_slot_size_list (tv::tvs)+w2n dw) <= dimword(:256) ==>
 w2n (sw+n2w (32*so):256 word) = w2n sw+32*so /\
 (!mem. mem_agree_outside tt.t_mem t.vs_memory mem ==>
   val_in_memory tv v (w2n (sw+n2w (32*so))) mem) /\
 w2n (sw+n2w (32*so)) + type_memory_size tv < dimword(:256) /\
 w2n (dw+n2w so:256 word) + type_slot_size tv <= dimword(:256)
Proof
 strip_tac >>
 `type_memory_size_list (tv::tvs) = type_memory_size tv + type_memory_size_list tvs /\
  type_slot_size_list (tv::tvs) = type_slot_size tv + type_slot_size_list tvs` by
   simp[Once valueEncodingTheory.type_memory_size_def,
     Once vyperValueTheory.type_slot_size_def] >>
 `32*so < dimword(:256) /\ w2n sw+32*so < dimword(:256)` by decide_tac >>
 `w2n (sw+n2w (32*so):256 word) = w2n sw+32*so` by
   (`w2n (n2w (32*so):256 word) = 32*so` by simp[] >>
    simp[wordsTheory.w2n_add_2]) >>
 asm_rewrite_tac [] >> conj_tac
 >- (rpt strip_tac >>
     `mem_agree_outside tn.t_mem s.vs_memory mem` by metis_tac[] >>
     qpat_x_assum `!mem. _ ==> tuple_in_memory _ _ _ _` drule >>
     pure_once_rewrite_tac[valueEncodingDefsTheory.val_in_memory_def] >> simp[]) >>
 `w2n (dw+n2w so:256 word) <= w2n dw+so` by
   (pure_rewrite_tac[wordsTheory.word_add_def, wordsTheory.w2n_n2w] >>
    irule LESS_EQ_TRANS >> qexists_tac `w2n dw + so MOD dimword(:256)` >>
    conj_tac >- simp[MOD_LESS_EQ] >> simp[MOD_LESS_EQ]) >>
 decide_tac
QED

Theorem members_tail_memory_entry[local]:
 (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
   tuple_in_memory (v::vs) (tv::tvs) (32*so+w2n sw) mem) /\
 t.vs_memory = s.vs_memory /\ tt.t_mem = tn.t_mem /\
 (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
   FLOOKUP H x = FLOOKUP G x /\ op_taint tt (Var x) = op_taint tn (Var x)) /\
 (!x. src = Var x ==> not_fresh_at sa x) /\
 (type_memory_size_list (tv::tvs) <> 0 ==> ?x. src = Var x /\
   ptr_covers G tn x s (32*so+type_memory_size_list (tv::tvs))) ==>
 (!mem. mem_agree_outside tt.t_mem t.vs_memory mem ==>
   tuple_in_memory vs tvs (w2n sw+32*(so+type_slot_size tv)) mem) /\
 (type_memory_size_list tvs <> 0 ==> ?x. src = Var x /\
   ptr_covers H tt x t (32*(so+type_slot_size tv)+type_memory_size_list tvs))
Proof
 strip_tac >>
 `type_memory_size tv = 32 * type_slot_size tv` by
   simp[valueEncodingPropsTheory.type_memory_size_slots] >>
 conj_tac
 >- (rpt strip_tac >>
     `mem_agree_outside tn.t_mem s.vs_memory mem` by metis_tac[] >>
     qpat_x_assum `!mem. _ ==> tuple_in_memory (v::vs) _ _ _` drule >>
     pure_once_rewrite_tac[valueEncodingDefsTheory.val_in_memory_def] >>
     simp[NoAsms] >> strip_tac >>
     `w2n sw+32*(so+type_slot_size tv) = 32*so+w2n sw+type_memory_size tv` by decide_tac >>
     gvs[]) >>
 strip_tac >>
 `type_memory_size_list (tv::tvs) <> 0` by
   simp[Once valueEncodingTheory.type_memory_size_def] >>
 first_x_assum drule >> strip_tac >> qexists_tac `x` >>
 `not_fresh_at sa x` by metis_tac[] >>
 `32*(so+type_slot_size tv)+type_memory_size_list tvs =
   32*so+type_memory_size_list (tv::tvs)` by
   (simp[NoAsms, Once valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
 fs[bodyPtrDefsTheory.ptr_covers_def]
QED

Theorem members_head_offset_covers[local]:
 compile_lit_byte_offset src (32*so) sa = (ms,a) /\
 eval_operand src s = SOME sw /\
 (type_memory_size_list (tv::tvs) <> 0 ==> ?x. src = Var x /\
   ptr_covers G tn x s (32*so+type_memory_size_list (tv::tvs))) /\
 32*so+(type_memory_size_list (tv::tvs)+w2n sw) < dimword(:256) /\
 eval_operand ms u1 = SOME (sw+n2w (32*so)) /\
 op_prov G1 ms = op_prov G src /\ op_taint t1 ms = {} /\
 copy_old_operand a ms /\
 (!x. not_fresh_at a x ==> lookup_var x u2 = lookup_var x u1 /\
   FLOOKUP G2 x = FLOOKUP G1 x /\ op_taint t2 (Var x) = op_taint t1 (Var x)) /\
 u2.vs_allocas = u1.vs_allocas /\ u2.vs_alloca_next = u1.vs_alloca_next ==>
 (type_memory_size tv <> 0 ==> ?x. ms = Var x /\
   ptr_covers G2 t2 x u2 (type_memory_size tv))
Proof
 strip_tac >> strip_tac >>
 `type_memory_size_list (tv::tvs) <> 0` by
   simp[Once valueEncodingTheory.type_memory_size_def] >>
 first_x_assum drule >> strip_tac >>
 `lookup_var x s = SOME sw` by fs[eval_operand_def] >>
 `32*so+type_memory_size tv <= 32*so+type_memory_size_list (tv::tvs) /\
  w2n sw+32*so < dimword(:256)` by
   fs[Once valueEncodingTheory.type_memory_size_def] >>
 qpat_x_assum `src = Var x` SUBST_ALL_TAC >>
 drule_all ifexp_runtime_offset_covers >> strip_tac >>
 qexists_tac `q` >> simp[] >>
 fs[copy_old_operand_def, bodyPtrDefsTheory.ptr_covers_def]
QED

Theorem members_sparse_runtime_cons[local]:
 store_copy_normalize s a = s /\ a.vs_memory = s.vs_memory /\
 u.vs_memory = s.vs_memory /\
 w2n (sw+n2w (32*so):256 word) = w2n sw+32*so /\
 store_copy_normalize a u =
   FOLDL (\q j. (if tr then tstore else sstore) ((dw+n2w so)+n2w j)
     (mload (w2n (sw+n2w (32*so))+32*j) a) q) a ks /\
 store_copy_normalize u t =
   FOLDL (\q j. (if tr then tstore else sstore) (dw+n2w j)
     (mload (32*j+w2n sw) u) q) u tailks ==>
 store_copy_normalize s t =
   FOLDL (\q j. (if tr then tstore else sstore) (dw+n2w j)
     (mload (w2n sw+32*j) s) q) s (MAP (\j. so+j) ks ++ tailks)
Proof
 strip_tac >>
 `store_copy_normalize s u =
   FOLDL (\q j. (if tr then tstore else sstore) (dw+n2w j)
     (mload (w2n sw+32*j) s) q) s (MAP (\j. so+j) ks)` by
   (qpat_x_assum `store_copy_normalize a u = _`
      (mp_tac o AP_TERM ``store_copy_normalize s``) >>
    simp[store_slots_normalize_compose, store_slots_normalize_fold,
      rich_listTheory.FOLDL_MAP] >>
    pure_rewrite_tac[mload_def, LEFT_ADD_DISTRIB, GSYM wordsTheory.word_add_n2w] >>
    simpLib.ASM_SIMP_TAC bool_ss
      [AC ADD_ASSOC ADD_COMM,
       AC wordsTheory.WORD_ADD_ASSOC wordsTheory.WORD_ADD_COMM]) >>
 irule store_slots_fold_compose >> qexists `u` >>
 simpLib.ASM_SIMP_TAC bool_ss [AC ADD_ASSOC ADD_COMM]
QED

Theorem members_tail_run[local]:
 ^members_case ==> !s u H tt.
 acyclic_struct_metadata cenv.ce_struct_fields /\
 sfields_tenv_consistent cenv.ce_struct_fields tenv /\
 (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
   ALL_DISTINCT (MAP FST fields) /\
   EVERY (\(fname,fty,sz). !rt. evaluate_type tenv fty = SOME rt ==>
     sz = type_memory_size rt) fields) /\
 compile_store_slots_members cenv src slot members (32*so+type_memory_size tv)
   (so+type_memory_size tv DIV 32) tr sc = ((),sb) /\
 LIST_REL (\(ty,sz) (tv,v). sz = type_memory_size tv /\
   type_rank cenv.ce_struct_fields ty < n /\
   evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\
   IS_SOME (encode_value tv v)) members (ZIP (tvs,vs)) /\
 LENGTH vs = LENGTH tvs /\
 (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
   tuple_in_memory (v::vs) (tv::tvs) (32*so+w2n sw) mem) /\
 (!x. src = Var x \/ slot = Var x ==> not_fresh_at sa x) /\
 eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
 op_taint tn src = {} /\ op_taint tn slot = {} /\
 (type_memory_size_list (tv::tvs) <> 0 ==> ?x. src = Var x /\
   ptr_covers G tn x s (32*so+type_memory_size_list (tv::tvs))) /\
 32*so+(type_memory_size_list (tv::tvs)+w2n sw) < dimword(:256) /\
 so+(type_slot_size_list (tv::tvs)+w2n dw) <= dimword(:256) /\
 (type_memory_size_list (tv::tvs) = 0 \/
   32*so+(type_memory_size_list (tv::tvs)+w2n sw) <= s.vs_alloca_next) /\
 fn_has_code sc sb func /\ fn_inst_ids_distinct func /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
 allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~s.vs_call_ctx.cc_static /\
 sa.cs_next_var <= sc.cs_next_var /\
 (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
   FLOOKUP H x = FLOOKUP G x /\ op_taint tt (Var x) = op_taint tn (Var x)) /\
 tt.t_mem = tn.t_mem /\ u.vs_memory = s.vs_memory /\
 u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
 u.vs_labels = s.vs_labels /\ u.vs_call_ctx = s.vs_call_ctx /\ ~u.vs_halted /\
 u.vs_current_bb = sc.cs_current_bb /\ u.vs_inst_idx = LENGTH sc.cs_current_insts ==>
 (\s G tn sa so. ^members_result) u H tt sc (so+type_slot_size tv)
Proof
 disch_then (mk_asm "tail") >> rpt gen_tac >>
 disch_then (map_every assume_tac o CONJUNCTS) >> BETA_TAC >>
 `type_memory_size tv = 32 * type_slot_size tv /\
  type_memory_size tv DIV 32 = type_slot_size tv` by
   simp[valueEncodingPropsTheory.type_memory_size_slots] >>
 `compile_store_slots_members cenv src slot members
    (32*(so+type_slot_size tv)) (so+type_slot_size tv) tr sc = ((),sb)` by
   (pure_rewrite_tac [LEFT_ADD_DISTRIB] >>
    qpat_x_assum `compile_store_slots_members _ _ _ _ _ _ _ _ = _` mp_tac >> simp[]) >>
 `(!x. src = Var x \/ slot = Var x ==> not_fresh_at sc x)` by
   (asm_x "tail" kall_tac >>
    fs[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
 `eval_operand src u = SOME sw /\ eval_operand slot u = SOME dw /\
  op_taint tt src = {} /\ op_taint tt slot = {}` by
   (Cases_on `src` >> Cases_on `slot` >> fs[eval_operand_def, op_taint_def]) >>
 `(!mem. mem_agree_outside tt.t_mem u.vs_memory mem ==>
    tuple_in_memory vs tvs (w2n sw+32*(so+type_slot_size tv)) mem) /\
  (type_memory_size_list tvs <> 0 ==> ?x. src = Var x /\
    ptr_covers H tt x u (32*(so+type_slot_size tv)+type_memory_size_list tvs))` by
   (irule members_tail_memory_entry >> qexistsl [`G`,`s`,`sa`,`tn`,`v`] >>
    asm_x "tail" kall_tac >> metis_tac[]) >>
 `allocas_from lo u` by
   (qpat_assum `allocas_from lo s` mp_tac >>
    pure_rewrite_tac[allocas_from_def] >> asm_rewrite_tac[]) >>
 asm_x "tail" (qspecl_then [`tvs`,`vs`,`32*(so+type_slot_size tv)`,
   `so+type_slot_size tv`,`src`,`slot`,`tr`,`sc`,`sb`,`func`,`u`,
   `sw`,`dw`,`tt`,`H`,`ctx`,`lo`,`explicit`,`PG`] mp_tac) >>
 impl_tac
 >- (`type_memory_size_list (tv::tvs) = type_memory_size tv + type_memory_size_list tvs /\
      type_slot_size_list (tv::tvs) = type_slot_size tv + type_slot_size_list tvs` by
       simp[NoAsms, Once valueEncodingTheory.type_memory_size_def,
         Once vyperValueTheory.type_slot_size_def] >>
     `32*(so+type_slot_size tv)+(type_memory_size_list tvs+w2n sw) < dimword(:256) /\
      (so+type_slot_size tv)+(type_slot_size_list tvs+w2n dw) <= dimword(:256) /\
      (type_memory_size_list tvs = 0 \/
       32*(so+type_slot_size tv)+(type_memory_size_list tvs+w2n sw) <= u.vs_alloca_next)` by
       (fs[] >> decide_tac) >> gvs[] >> metis_tac[ADD_COMM]) >>
 simp[]
QED

val members_head_post = ``
 encode_value tv v = SOME writes /\
 (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,H,tt) [] (OK t,Gf,tf)) /\
 store_copy_normalize u t =
   FOLDL (\q j. (if tr then tstore else sstore) (dw+n2w so+n2w j)
     (mload (w2n ((sw:256 word)+n2w (32*so))+32*j) u) q) u ks /\
 (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
 (!x. not_fresh_at b x ==> lookup_var x t = lookup_var x u /\
   FLOOKUP Gf x = FLOOKUP H x /\ op_taint tf (Var x) = op_taint tt (Var x)) /\
 tf.t_mem = tt.t_mem /\ tf.t_imm = tt.t_imm /\
 (if tr then tf.t_stor = tt.t_stor else tf.t_trans = tt.t_trans) /\
 (if tr then tf.t_trans else tf.t_stor) SUBSET
   FOLDL (\X j. key_update X (dw+n2w so+n2w j)
     (mem_word_taint tt.t_mem (w2n (sw+n2w (32*so))+32*j)))
     (if tr then tt.t_trans else tt.t_stor) ks /\
 t.vs_memory = u.vs_memory /\ t.vs_allocas = u.vs_allocas /\
 t.vs_alloca_next = u.vs_alloca_next /\ t.vs_labels = u.vs_labels /\
 t.vs_call_ctx = u.vs_call_ctx /\ ~t.vs_halted /\
 t.vs_current_bb = sc.cs_current_bb /\ t.vs_inst_idx = LENGTH sc.cs_current_insts``;

Theorem members_head_run[local]:
 ^members_child ==> !u H tt.
 acyclic_struct_metadata cenv.ce_struct_fields /\
 sfields_tenv_consistent cenv.ce_struct_fields tenv /\
 (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
   ALL_DISTINCT (MAP FST fields) /\
   EVERY (\(fname,fty,sz). !rt. evaluate_type tenv fty = SOME rt ==>
     sz = type_memory_size rt) fields) /\
 type_rank cenv.ce_struct_fields ty < n /\ evaluate_type tenv ty = SOME tv /\
 value_has_type tv v /\ IS_SOME (encode_value tv v) /\
 compile_store_slots cenv ms ds ty tr b = ((),sc) /\
 (!x. ms = Var x \/ ds = Var x ==> not_fresh_at b x) /\
 eval_operand ms u = SOME (sw+n2w (32*so)) /\
 eval_operand ds u = SOME (dw+n2w so) /\ op_taint tt ms = {} /\ op_taint tt ds = {} /\
 (!mem. mem_agree_outside tt.t_mem u.vs_memory mem ==>
   val_in_memory tv v (w2n (sw+n2w (32*so))) mem) /\
 (type_memory_size tv <> 0 ==> ?x. ms = Var x /\ ptr_covers H tt x u (type_memory_size tv)) /\
 w2n (sw+n2w (32*so)) = w2n sw+32*so /\
 w2n (sw+n2w (32*so))+type_memory_size tv < dimword(:256) /\
 w2n (dw+n2w so)+type_slot_size tv <= dimword(:256) /\
 (type_memory_size_list (tv::tvs) = 0 \/
  32*so+(type_memory_size_list (tv::tvs)+w2n sw) <= u.vs_alloca_next) /\
 fn_has_code b sc func /\ fn_inst_ids_distinct func /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
 allocas_from lo u /\ lo <= u.vs_alloca_next /\ ~u.vs_call_ctx.cc_static /\ ~u.vs_halted /\
 u.vs_current_bb = b.cs_current_bb /\ u.vs_inst_idx = LENGTH b.cs_current_insts ==>
 ?t ks Gf tf writes. ^members_head_post
Proof
 disch_then (mk_asm "child") >> rpt gen_tac >>
 disch_then (map_every assume_tac o CONJUNCTS) >>
 Cases_on `encode_value tv v` >- fs[] >>
 rename1 `encode_value tv v = SOME writes` >>
 asm_x "child" drule >> disch_then (qspecl_then [`tv`,`v`] mp_tac) >>
 disch_then (drule_at (Pos (el 6))) >> disch_then (qspec_then `u` mp_tac) >>
 disch_then (drule_at (Pat `eval_operand ms _ = _`)) >>
 disch_then (drule_at (Pat `op_taint _ ms = _`)) >>
 disch_then (drule_at (Pat `eval_operand ds _ = _`)) >>
 disch_then (drule_at (Pat `encode_value _ _ = _`)) >>
 disch_then (drule_at (Pat `fn_has_code b sc _`)) >>
 disch_then (qspecl_then [`H`,`ctx`,`lo`,`explicit`,`PG`] mp_tac) >>
 impl_tac
 >- (`type_memory_size_list (tv::tvs) = type_memory_size tv+type_memory_size_list tvs` by
       simp[NoAsms, Once valueEncodingTheory.type_memory_size_def] >>
     fs[] >> metis_tac[]) >>
 strip_tac >> qexistsl [`t`,`ks`,`Gf`,`tf`,`writes`] >> simp[]
QED

Theorem members_offsets_run[local]:
 compile_lit_byte_offset src (32*so) sa = (ms,a) /\
 compile_lit_byte_offset slot so a = (ds,b) /\
 sa.cs_next_var <= a.cs_next_var /\ a.cs_next_var <= b.cs_next_var /\
 (!x. src = Var x \/ slot = Var x ==> not_fresh_at sa x) /\
 eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
 op_taint tn src = {} /\ op_taint tn slot = {} /\
 (type_memory_size_list (tv::tvs) <> 0 ==> ?x. src = Var x /\
   ptr_covers G tn x s (32*so+type_memory_size_list (tv::tvs))) /\
 32*so+(type_memory_size_list (tv::tvs)+w2n sw) < dimword(:256) /\
 (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ fn_has_code sa a func /\ fn_has_code a b func /\
 ~s.vs_halted /\ allocas_from lo s /\
 s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
 ?u2 Gf' tf'.
 (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u2,Gf',tf')) /\
 eval_operand ms u2 = SOME (sw+n2w (32*so)) /\
 eval_operand ds u2 = SOME (dw+n2w so) /\
 copy_old_operand b ms /\ copy_old_operand b ds /\ op_taint tf' ms = {} /\ op_taint tf' ds = {} /\
 (type_memory_size tv <> 0 ==> ?x. ms = Var x /\ ptr_covers Gf' tf' x u2 (type_memory_size tv)) /\
 tf'.t_mem = tn.t_mem /\ tf'.t_stor = tn.t_stor /\ tf'.t_trans = tn.t_trans /\ tf'.t_imm = tn.t_imm /\
 (!x. not_fresh_at sa x ==> lookup_var x u2 = lookup_var x s /\
   FLOOKUP Gf' x = FLOOKUP G x /\ op_taint tf' (Var x) = op_taint tn (Var x)) /\
 u2.vs_memory = s.vs_memory /\ u2.vs_allocas = s.vs_allocas /\
 u2.vs_alloca_next = s.vs_alloca_next /\ u2.vs_labels = s.vs_labels /\
 u2.vs_call_ctx = s.vs_call_ctx /\ ~u2.vs_halted /\
 u2.vs_current_bb = b.cs_current_bb /\ u2.vs_inst_idx = LENGTH b.cs_current_insts /\
 store_copy_normalize s u2 = s
Proof
 disch_then (map_every assume_tac o CONJUNCTS) >>
 `copy_old_operand sa src` by fs[copy_old_operand_def] >>
 drule_all compile_lit_byte_offset_origin_ptr_path >>
 disch_then (qspecl_then [`explicit`,`PG`,`G`] strip_assume_tac) >>
 rename1 `eval_operand ms u1 = SOME (sw+n2w (32*so))` >>
 `copy_old_operand a slot` by
   (fs[copy_old_operand_def, loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
 `eval_operand slot u1 = SOME dw /\ op_taint tf slot = {}` by
   (Cases_on `slot` >> fs[eval_operand_def, op_taint_def]) >>
 `allocas_from lo u1` by
   (qpat_assum `allocas_from lo s` mp_tac >> pure_rewrite_tac[allocas_from_def] >> asm_rewrite_tac[]) >>
 drule_all (Q.SPEC `slot` compile_lit_byte_offset_origin_ptr_path) >>
 disch_then (qspecl_then [`explicit`,`PG`,`Gf`] strip_assume_tac) >>
 rename1 `eval_operand ds u2 = SOME (dw+n2w so)` >>
 `(type_memory_size tv <> 0 ==> ?x. ms = Var x /\ ptr_covers Gf' tf' x u2 (type_memory_size tv))` by
   (MATCH_MP_TAC (Q.INST [`G1` |-> `Gf`, `t1` |-> `tf`] members_head_offset_covers) >> simp[]) >>
 `eval_operand ms u2 = SOME (sw+n2w (32*so)) /\ op_taint tf' ms = {}` by
   (Cases_on `ms` >> fs[copy_old_operand_def, eval_operand_def, op_taint_def]) >>
 `store_copy_normalize s u2 = s` by
   (qpat_assum `store_copy_normalize u1 u2 = u1` (mp_tac o AP_TERM ``store_copy_normalize s``) >>
    simp[NoAsms, store_copy_normalize_def] >>
    qpat_assum `store_copy_normalize s u1 = s` mp_tac >> simp[NoAsms, store_copy_normalize_def]) >>
 qexistsl [`u2`,`Gf'`,`tf'`] >>
 conj_tac >- metis_tac[gas_origin_ptr_path_trans] >>
 simpLib.ASM_SIMP_TAC bool_ss [] >>
 conj_tac
 >- (fs[copy_old_operand_def, loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
 rpt strip_tac >> metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]
QED

Theorem members_cons_finish[local]:
 (!ks X Y (k:256 word) b M. X SUBSET Y ==>
   FOLDL (\Z i. key_update Z (k+n2w i) (mem_word_taint M (b+32*i))) X ks SUBSET
   FOLDL (\Z i. key_update Z (k+n2w i) (mem_word_taint M (b+32*i))) Y ks) ==>
 ^members_head_post /\
 (\s G tn sa so. ^members_result) t Gf tf sc (so+type_slot_size tv) /\
 (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,H,tt)) /\
 store_copy_normalize s u = s /\
 w2n (sw+n2w (32*so)) = w2n sw+32*so /\
 sa.cs_next_var <= b.cs_next_var /\ b.cs_next_var <= sc.cs_next_var /\
 (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
   FLOOKUP H x = FLOOKUP G x /\ op_taint tt (Var x) = op_taint tn (Var x)) /\
 tt.t_mem = tn.t_mem /\ tt.t_imm = tn.t_imm /\
 tt.t_stor = tn.t_stor /\ tt.t_trans = tn.t_trans /\
 u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
 u.vs_alloca_next = s.vs_alloca_next /\ u.vs_labels = s.vs_labels /\
 u.vs_call_ctx = s.vs_call_ctx ==>
 (\tvs vs. ^members_result) (tv::tvs) (v::vs)
Proof
 disch_then (mk_asm "mono") >> BETA_TAC >>
 disch_then (map_every assume_tac o CONJUNCTS) >>
 qpat_x_assum `?t ks Gf tf. _`
   (qx_choose_then `endstate` (qx_choose_then `tailks`
    (qx_choose_then `ghost_end` (qx_choose_then `ta_end` strip_assume_tac)))) >>
 `store_copy_normalize s endstate =
    FOLDL (\q j. (if tr then tstore else sstore) (dw+n2w j)
      (mload (w2n sw+32*j) s) q) s (MAP (\j. so+j) ks ++ tailks)` by
   (irule members_sparse_runtime_cons >> conj_tac >- first_assum ACCEPT_TAC >>
    qexistsl [`u`,`t`] >> simpLib.ASM_SIMP_TAC bool_ss [AC ADD_ASSOC ADD_COMM]) >>
 `!k. MEM k (MAP (\j. so+j) ks ++ tailks) <=>
    ?i ws j. i < SUC (LENGTH tvs) /\
      encode_value (EL i (tv::tvs)) (EL i (v::vs)) = SOME ws /\ MEM j (MAP FST ws) /\
      k = j+(so+tuple_prefix_slot_size i (tv::tvs))` by
   (irule members_sparse_support_cons >> conj_tac
    >- (qpat_assum `!k. MEM k tailks <=> _` mp_tac >>
        simpLib.SIMP_TAC bool_ss [AC ADD_ASSOC ADD_COMM]) >> qexists `writes` >> simp[]) >>
 `(if tr then tf.t_trans else tf.t_stor) SUBSET
    FOLDL (\X j. key_update X (dw+n2w j) (mem_word_taint tn.t_mem (w2n sw+32*j)))
      (if tr then tn.t_trans else tn.t_stor) (MAP (\j. so+j) ks)` by
   (qpat_x_assum `(if tr then tf.t_trans else tf.t_stor) SUBSET _` mp_tac >>
    simpLib.ASM_SIMP_TAC bool_ss [store_slots_taint_shift]) >>
 `(if tr then ta_end.t_trans else ta_end.t_stor) SUBSET
    FOLDL (\X j. key_update X (dw+n2w j) (mem_word_taint tn.t_mem (w2n sw+32*j)))
      (if tr then tn.t_trans else tn.t_stor) (MAP (\j. so+j) ks ++ tailks)` by
   (irule (SRULE [] (Q.INST [`off` |-> `0`] store_slots_child_bank_bound)) >>
    conj_tac >- asm "mono" ACCEPT_TAC >> qexists `(if tr then tf.t_trans else tf.t_stor)` >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qpat_x_assum `(if tr then ta_end.t_trans else ta_end.t_stor) SUBSET _` mp_tac >>
    simpLib.ASM_SIMP_TAC bool_ss [wordsTheory.WORD_ADD_0, AC ADD_ASSOC ADD_COMM]) >>
 qexistsl [`endstate`,`MAP (\j. so+j) ks ++ tailks`,`ghost_end`,`ta_end`] >>
 conj_tac >- (gen_tac >> metis_tac[gas_origin_ptr_path_trans]) >>
 simpLib.ASM_SIMP_TAC bool_ss [listTheory.LENGTH, AC ADD_ASSOC ADD_COMM] >>
 conj_tac >- (rpt strip_tac >> metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]) >>
 Cases_on `tr` >> metis_tac[]
QED

val members_cons_entry = ``
 acyclic_struct_metadata cenv.ce_struct_fields /\
 sfields_tenv_consistent cenv.ce_struct_fields tenv /\
 (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
   ALL_DISTINCT (MAP FST fields) /\
   EVERY (\(fname,fty,sz). !rt. evaluate_type tenv fty = SOME rt ==>
     sz = type_memory_size rt) fields) /\
 type_rank cenv.ce_struct_fields ty < n /\ evaluate_type tenv ty = SOME tv /\
 value_has_type tv v /\ IS_SOME (encode_value tv v) /\
 compile_store_slots_members cenv src slot members (32*so+type_memory_size tv)
   (so+type_memory_size tv DIV 32) tr sc = ((),sb) /\
 LIST_REL (\(ty,sz) (tv,v). sz = type_memory_size tv /\
   type_rank cenv.ce_struct_fields ty < n /\
   evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\
   IS_SOME (encode_value tv v)) members (ZIP (tvs,vs)) /\
 LENGTH vs = LENGTH tvs /\
 (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
   tuple_in_memory (v::vs) (tv::tvs) (32*so+w2n sw) mem) /\
 (!x. src = Var x \/ slot = Var x ==> not_fresh_at sa x) /\
 eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
 op_taint tn src = {} /\ op_taint tn slot = {} /\
 (type_memory_size_list (tv::tvs) <> 0 ==> ?x. src = Var x /\
   ptr_covers G tn x s (32*so+type_memory_size_list (tv::tvs))) /\
 32*so+(type_memory_size_list (tv::tvs)+w2n sw) < dimword(:256) /\
 so+(type_slot_size_list (tv::tvs)+w2n dw) <= dimword(:256) /\
 (type_memory_size_list (tv::tvs) = 0 \/
   32*so+(type_memory_size_list (tv::tvs)+w2n sw) <= s.vs_alloca_next) /\
 fn_inst_ids_distinct func /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
 allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~s.vs_call_ctx.cc_static /\
 ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
 s.vs_inst_idx = LENGTH sa.cs_current_insts /\
 compile_lit_byte_offset src (32*so) sa = (ms,a) /\
 compile_lit_byte_offset slot so a = (ds,b) /\
 compile_store_slots cenv ms ds ty tr b = ((),sc) /\
 sa.cs_next_var <= a.cs_next_var /\ a.cs_next_var <= b.cs_next_var /\
 b.cs_next_var <= sc.cs_next_var /\
 fn_has_code sa a func /\ fn_has_code a b func /\
 fn_has_code b sc func /\ fn_has_code sc sb func``;

Theorem members_cons_run[local]:
 (!ks X Y (k:256 word) b M. X SUBSET Y ==>
   FOLDL (\Z i. key_update Z (k+n2w i) (mem_word_taint M (b+32*i))) X ks SUBSET
   FOLDL (\Z i. key_update Z (k+n2w i) (mem_word_taint M (b+32*i))) Y ks) ==>
 ^members_child ==> ^members_case ==> !s. ^members_cons_entry ==>
 (\tvs vs. ^members_result) (tv::tvs) (v::vs)
Proof
 disch_then (mk_asm "mono") >> disch_then (mk_asm "child") >>
 disch_then (mk_asm "tail") >> gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 drule_all members_offsets_run >>
 disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
 `w2n (sw+n2w (32*so)) = w2n sw+32*so /\
  (!mem. mem_agree_outside tf'.t_mem u2.vs_memory mem ==>
    val_in_memory tv v (w2n (sw+n2w (32*so))) mem) /\
  w2n (sw+n2w (32*so)) + type_memory_size tv < dimword(:256) /\
  w2n (dw+n2w so) + type_slot_size tv <= dimword(:256)` by
   (irule members_head_memory_entry >> qexistsl [`s`,`tn`,`tvs`,`vs`] >>
    asm_x "child" kall_tac >> asm_x "mono" kall_tac >> asm_x "tail" kall_tac >> metis_tac[]) >>
 `(!x. ms = Var x \/ ds = Var x ==> not_fresh_at b x)` by
   (asm_x "child" kall_tac >> asm_x "mono" kall_tac >> asm_x "tail" kall_tac >>
    fs[copy_old_operand_def, loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
 `allocas_from lo u2` by (qpat_assum `allocas_from lo s` mp_tac >>
    pure_rewrite_tac[allocas_from_def] >> asm_rewrite_tac[]) >>
 asm "child" (mp_tac o MATCH_MP members_head_run) >>
 disch_then (qspecl_then [`u2`,`Gf'`,`tf'`] mp_tac) >>
 impl_tac >- (asm_x "child" kall_tac >> asm_x "mono" kall_tac >> asm_x "tail" kall_tac >>
    simpLib.ASM_SIMP_TAC bool_ss [] >> metis_tac[]) >>
 disch_then (qx_choose_then `t` (qx_choose_then `ks` (qx_choose_then `Gf''`
   (qx_choose_then `tf''` (qx_choose_then `writes` strip_assume_tac))))) >>
 `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP Gf'' x = FLOOKUP G x /\ op_taint tf'' (Var x) = op_taint tn (Var x)` by
   (asm_x "child" kall_tac >> asm_x "mono" kall_tac >> asm_x "tail" kall_tac >>
    fs[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
 asm_x "tail" (mp_tac o MATCH_MP members_tail_run) >>
 disch_then (qspecl_then [`s`,`t`,`Gf''`,`tf''`] mp_tac) >>
 impl_tac >- (asm_x "child" kall_tac >> asm_x "mono" kall_tac >>
    simpLib.ASM_SIMP_TAC bool_ss [] >> metis_tac[LESS_EQ_TRANS]) >>
 disch_then assume_tac >> BETA_TAC >>
 simpLib.SIMP_TAC bool_ss [listTheory.LENGTH, AC ADD_ASSOC ADD_COMM] >>
 asm_x "mono" (irule o SIMP_RULE bool_ss [listTheory.LENGTH, AC ADD_ASSOC ADD_COMM] o MATCH_MP members_cons_finish) >>
 conj_tac >- first_assum ACCEPT_TAC >>
 qexistsl [`Gf''`,`Gf'`,`b`,`ks`,`sc`,`t`,`tf''`,`tf'`,`u2`,`writes`] >>
 asm_x "child" kall_tac >> simpLib.ASM_SIMP_TAC bool_ss [AC ADD_ASSOC ADD_COMM] >>
 conj_tac >- (qpat_x_assum `(\s G tn sa so. _) _ _ _ _ _` mp_tac >>
    simpLib.ASM_SIMP_TAC bool_ss [AC ADD_ASSOC ADD_COMM]) >>
 conj_tac >- decide_tac >>
 qpat_x_assum `(if tr then tf''.t_trans else tf''.t_stor) SUBSET _` mp_tac >>
 simpLib.ASM_SIMP_TAC bool_ss [AC ADD_ASSOC ADD_COMM]
QED

Theorem compile_store_slots_members_origin_ptr_path_conditional:
 (!ks X Y (k:256 word) b M. X SUBSET Y ==>
   FOLDL (\Z i. key_update Z (k+n2w i) (mem_word_taint M (b+32*i))) X ks SUBSET
   FOLDL (\Z i. key_update Z (k+n2w i) (mem_word_taint M (b+32*i))) Y ks) ==>
 !cenv tenv n. ^members_child ==> ^members_goal
Proof
 disch_then (mk_asm "mono") >> rpt gen_tac >> disch_then (mk_asm "child") >>
 Induct_on `members`
 >- (rpt gen_tac >> strip_tac >>
     `tvs = [] /\ vs = []` by
       (Cases_on `tvs` >> Cases_on `vs` >> gvs[]) >>
     gvs[Once compile_store_slots_def, comp_return_def] >>
     qexistsl [`s`,`[]`,`G`,`tn`] >>
     simp[gas_origin_ptr_path_rules, store_copy_normalize_def,
       venom_state_component_equality]) >>
 qpat_x_assum `!tvs vs mo so src slot tr sa sb func s sw dw tn G ctx lo explicit PG. _`
   (mk_asm "tail") >>
 qx_gen_tac `hdmem` >> PairCases_on `hdmem` >>
 Cases_on `tvs` >> Cases_on `vs` >> simp[] >>
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 gnvs[Once compile_store_slots_def, comp_bind_def, comp_ignore_bind_def,
   AllCaseEqs()] >>
 rename1 `evaluate_type tenv ty = SOME tv` >>
 rename1 `value_has_type tv v` >> rename1 `ZIP (tvs,vs)` >>
 Cases_on `compile_lit_byte_offset src (32*so) sa` >>
 rename1 `compile_lit_byte_offset src (32*so) sa = (ms,a)` >>
 Cases_on `compile_lit_byte_offset slot so a` >>
 rename1 `compile_lit_byte_offset slot so a = (ds,b)` >>
 Cases_on `compile_store_slots cenv ms ds ty tr b` >>
 rename1 `compile_store_slots cenv ms ds ty tr b = (u,sc)` >>
 Cases_on `u` >> gnvs[] >>
 `exprLoweringProps$ci_mono sa a /\ exprLoweringProps$ci_mono a b /\
  exprLoweringProps$ci_mono b sc /\ exprLoweringProps$ci_mono sc sb` by
   (asm_x "child" kall_tac >> asm_x "mono" kall_tac >>
    asm_x "tail" kall_tac >>
    metis_tac[exprLoweringPropsTheory.ci_mono_compile_lit_byte_offset,
      cj 1 stmtLoweringMonoTheory.ci_mono_compile_store_slots,
      cj 2 stmtLoweringMonoTheory.ci_mono_compile_store_slots, pairTheory.SND]) >>
 imp_res_tac (iffLR exprLoweringPropsTheory.ci_mono_def) >>
 `fn_has_code sa a func /\ fn_has_code a b func /\
  fn_has_code b sc func /\ fn_has_code sc sb func` by
   (asm_x "child" kall_tac >> asm_x "mono" kall_tac >> asm_x "tail" kall_tac >>
    metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans]) >>
 simpLib.SIMP_TAC bool_ss [AC ADD_ASSOC ADD_COMM] >>
 asm_x "mono" (mp_tac o MATCH_MP members_cons_run) >>
 disch_then (fn th => asm_x "child" (mp_tac o MATCH_MP th)) >>
 disch_then (fn th => asm_x "tail" (mp_tac o MATCH_MP th)) >>
 disch_then (irule o SIMP_RULE bool_ss [listTheory.LENGTH, AC ADD_ASSOC ADD_COMM] o BETA_RULE) >>
 rule_assum_tac (SIMP_RULE bool_ss [AC ADD_ASSOC ADD_COMM]) >>
 simpLib.ASM_SIMP_TAC bool_ss [] >> metis_tac[]
QED
