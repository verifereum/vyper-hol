(* Common live-word endpoint for dense and bytestring entry branches. *)
Theory fullStoreSlotsLeafCases
Ancestors
  fullStoreSlotsWordLoop fullStoreSlotsBytes fullStoreDense
  fullStoreSlotsMemberFrame placeStoreSlots stmtSimStoreCopy
  placeStoreCopyPath context emitHelper emitHelperProps exprLoweringProps
  loweringStateRelDefs codegenRel ptrDiscipline bodyPtrDefs compileEnv unitTransformDefs
  venomState venomInst venomExecSemantics fragExec stateFrame
  finite_map pred_set list rich_list arithmetic words
  vyperValue vyperTyping exprSimProps valueEncodingDefs vyperStorageCoverage
  fullAssignCopyFacts valueEncoding valueEncodingProps

Theorem store_slots_copy_prefix_fold:
  w2n (sw:bytes32)+32*n < dimword(:256) ==>
  store_copy_prefix (if tr then LocTransient else LocStorage) sw dw s n =
    FOLDL (\q j. (if tr then tstore else sstore) (dw+n2w j)
      (mload (w2n sw+32*j) s) q) s (GENLIST I n)
Proof
  strip_tac >> simp[store_copy_prefix_def, COUNT_LIST_GENLIST] >>
  irule FOLDL_CONG >> simp[] >> rpt strip_tac >>
  rename1 `MEM j (GENLIST I n)` >>
  `j < n` by gvs[MEM_GENLIST] >>
  `w2n (sw+n2w j*32w) = w2n sw+32*j` by
    (rewrite_tac[word_mul_n2w] >> simp[w2n_add_2] >> decide_tac) >>
  Cases_on `tr` >> simp[]
QED

Theorem store_slots_live_word_loop:
  compile_word_copy_loop_op (Var root) slot cnt LocMemory
    (if tr then LocTransient else LocStorage) F sa = (z,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  ~s.vs_call_ctx.cc_static /\ not_fresh_at sa root /\
  (!y. slot=Var y \/ cnt=Var y ==> not_fresh_at sa y) /\
  lookup_var root s=SOME sw /\ ptr_covers G tn root s (32*n) /\
  eval_operand slot s=SOME dw /\ op_taint tn slot={} /\
  eval_operand cnt s=SOME (n2w n) /\ op_taint tn cnt={} /\ op_prov G cnt=NONE /\
  n<dimword(:256) /\ w2n sw+32*n<dimword(:256) /\
  w2n sw+32*n<=s.vs_alloca_next /\ ~s.vs_halted /\
  s.vs_current_bb=sa.cs_current_bb /\ s.vs_inst_idx=LENGTH sa.cs_current_insts ==>
  ?Gf tf u.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tf)) /\
    store_copy_normalize s u =
      FOLDL (\q k. (if tr then tstore else sstore) (dw+n2w k)
        (mload (w2n sw+32*k) s) q) s (GENLIST I n) /\
    u.vs_memory=s.vs_memory /\ tf.t_mem=tn.t_mem /\ tf.t_imm=tn.t_imm /\
    (if tr then tf.t_trans else tf.t_stor) =
      FOLDL (\ta k. key_update ta (dw+n2w k)
        (mem_word_taint tn.t_mem (w2n sw+32*k)))
        (if tr then tn.t_trans else tn.t_stor) (GENLIST I n) /\
    (if tr then tf.t_stor else tf.t_trans)=(if tr then tn.t_stor else tn.t_trans) /\
    (!p. not_fresh_at sa p ==> lookup_var p u=lookup_var p s /\
      FLOOKUP Gf p=FLOOKUP G p /\ op_taint tf (Var p)=op_taint tn (Var p)) /\
    u.vs_allocas=s.vs_allocas /\ u.vs_alloca_next=s.vs_alloca_next /\
    u.vs_labels=s.vs_labels /\ u.vs_call_ctx=s.vs_call_ctx /\
    ~u.vs_halted /\ u.vs_current_bb=sb.cs_current_bb /\
    u.vs_inst_idx=LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  drule_at (Pat `compile_word_copy_loop_op _ _ _ _ _ _ _ = _`)
    memory_copy_loop_op_origin_ptr_exact >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `~ctx_has_dalloca _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand slot _ = _`)) >>
  disch_then (qspec_then `dw` mp_tac) >>
  (impl_tac >- (Cases_on `tr` >> simp[] >> metis_tac[])) >> strip_tac >>
  drule place_store_copy_frame_observations >> strip_tac >>
  drule bodyMemAssignTopCopyPathsTheory.topcopy_frame_frontier >> strip_tac >>
  qexistsl [`Gf`,`tnf`,`t`] >> simp[] >>
  `store_copy_prefix (if tr then LocTransient else LocStorage) sw dw s n =
    FOLDL (\q k. (if tr then tstore else sstore) (dw+n2w k)
      (mload (w2n sw+32*k) s) q) s (GENLIST I n)` by
    (irule store_slots_copy_prefix_fold >> simp[]) >>
  Cases_on `tr` >>
  gvs[store_copy_frame_def, exprSimPtrTopLevelStorageCopyTheory.toplevel_copy_source_taint_def]
QED

Theorem store_slots_dense_words:
  ~is_abi_dynamic cenv.ce_struct_fields ty /\
  n=type_memory_bytes cenv ty DIV 32 /\
  compile_store_slots cenv (Var root) slot ty tr sa=((),sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  ~s.vs_call_ctx.cc_static /\ not_fresh_at sa root /\
  (!y. slot=Var y ==> not_fresh_at sa y) /\
  lookup_var root s=SOME sw /\ ptr_covers G tn root s (32*n) /\
  eval_operand slot s=SOME dw /\ op_taint tn slot={} /\
  n<dimword(:256) /\ w2n sw+32*n<dimword(:256) /\
  w2n sw+32*n<=s.vs_alloca_next /\ ~s.vs_halted /\
  s.vs_current_bb=sa.cs_current_bb /\ s.vs_inst_idx=LENGTH sa.cs_current_insts ==>
  ?Gf tf u.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tf)) /\
    store_copy_normalize s u =
      FOLDL (\q k. (if tr then tstore else sstore) (dw+n2w k)
        (mload (w2n sw+32*k) s) q) s (GENLIST I n) /\
    u.vs_memory=s.vs_memory /\ tf.t_mem=tn.t_mem /\ tf.t_imm=tn.t_imm /\
    (if tr then tf.t_trans else tf.t_stor) =
      FOLDL (\ta k. key_update ta (dw+n2w k)
        (mem_word_taint tn.t_mem (w2n sw+32*k)))
        (if tr then tn.t_trans else tn.t_stor) (GENLIST I n) /\
    (if tr then tf.t_stor else tf.t_trans)=(if tr then tn.t_stor else tn.t_trans) /\
    (!p. not_fresh_at sa p ==> lookup_var p u=lookup_var p s /\
      FLOOKUP Gf p=FLOOKUP G p /\ op_taint tf (Var p)=op_taint tn (Var p)) /\
    u.vs_allocas=s.vs_allocas /\ u.vs_alloca_next=s.vs_alloca_next /\
    u.vs_labels=s.vs_labels /\ u.vs_call_ctx=s.vs_call_ctx /\
    ~u.vs_halted /\ u.vs_current_bb=sb.cs_current_bb /\
    u.vs_inst_idx=LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_slots_def] >>
  Cases_on `n=1`
  >- suspend "single" >>
  `type_memory_bytes cenv ty DIV 32 <> 1` by metis_tac[] >>
  Cases_on `tr` >>
  simp[compile_memory_to_storage_def, compile_memory_to_transient_def,
    comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `compile_word_copy_loop _ _ _ _ _ _ _ = _` mp_tac >>
  rewrite_tac[compile_word_copy_loop_def] >> strip_tac
  >- (drule_at (Pat `compile_word_copy_loop_op _ _ _ _ _ _ _ = _`)
        (SRULE [] (Q.INST [`tr` |-> `T`] store_slots_live_word_loop)) >>
      disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
      disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
      disch_then (drule_at (Pat `eval_operand slot _ = _`)) >>
      simp[eval_operand_def, op_taint_def, op_prov_def] >>
      (impl_tac >- (simp[] >> decide_tac)) >>
      strip_tac >> gvs[]) >>
  drule_at (Pat `compile_word_copy_loop_op _ _ _ _ _ _ _ = _`)
    (SRULE [] (Q.INST [`tr` |-> `F`] store_slots_live_word_loop)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand slot _ = _`)) >>
  simp[eval_operand_def, op_taint_def, op_prov_def] >>
  (impl_tac >- (simp[] >> decide_tac)) >> strip_tac >> gvs[]
QED

Resume store_slots_dense_words[single]:
  `type_memory_bytes cenv ty DIV 32 = 1` by metis_tac[] >>
  simp[] >> strip_tac >> gvs[] >>
  drule_all dense_single_compiled_origin_ptr_uniform >> strip_tac >>
  drule place_store_copy_frame_observations >> strip_tac >>
  qexistsl [`Gf`,`tnf`,`t`] >>
  Cases_on `tr` >>
  gvs[store_copy_frame_def, store_copy_prefix_def,
    exprSimPtrTopLevelStorageCopyTheory.toplevel_copy_source_taint_def,
    EVAL ``COUNT_LIST 1``, WORD_ADD_0, WORD_MULT_CLAUSES, store_copy_normalize_def]
QED

Finalise store_slots_dense_words

Theorem store_slots_bytes_words:
  is_abi_dynamic cenv.ce_struct_fields ty /\ is_bytestring_type ty /\
  n=1+word_size len /\
  compile_store_slots cenv (Var root) slot ty tr sa=((),sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  ~s.vs_call_ctx.cc_static /\ not_fresh_at sa root /\
  (!y. slot=Var y ==> not_fresh_at sa y) /\
  lookup_var root s=SOME sw /\ ptr_covers G tn root s (32*n) /\
  eval_operand slot s=SOME dw /\ op_taint tn slot={} /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    mem_word_at (w2n sw) m = n2w len) /\
  len+63<dimword(:256) /\ n<dimword(:256) /\
  w2n sw+32*n<dimword(:256) /\ w2n sw+32*n<=s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb=sa.cs_current_bb /\
  s.vs_inst_idx=LENGTH sa.cs_current_insts ==>
  ?Gf tf u.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tf)) /\
    store_copy_normalize s u =
      FOLDL (\q k. (if tr then tstore else sstore) (dw+n2w k)
        (mload (w2n sw+32*k) s) q) s (GENLIST I n) /\
    u.vs_memory=s.vs_memory /\ tf.t_mem=tn.t_mem /\ tf.t_imm=tn.t_imm /\
    (if tr then tf.t_trans else tf.t_stor) =
      FOLDL (\ta k. key_update ta (dw+n2w k)
        (mem_word_taint tn.t_mem (w2n sw+32*k)))
        (if tr then tn.t_trans else tn.t_stor) (GENLIST I n) /\
    (if tr then tf.t_stor else tf.t_trans)=(if tr then tn.t_stor else tn.t_trans) /\
    (!p. not_fresh_at sa p ==> lookup_var p u=lookup_var p s /\
      FLOOKUP Gf p=FLOOKUP G p /\ op_taint tf (Var p)=op_taint tn (Var p)) /\
    u.vs_allocas=s.vs_allocas /\ u.vs_alloca_next=s.vs_alloca_next /\
    u.vs_labels=s.vs_labels /\ u.vs_call_ctx=s.vs_call_ctx /\
    ~u.vs_halted /\ u.vs_current_bb=sb.cs_current_bb /\
    u.vs_inst_idx=LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_slots_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `compile_bytestring_word_count (Var root) sa = (cnt,sm)` >>
  Cases_on `compile_word_copy_loop_op (Var root) slot cnt LocMemory
    (if tr then LocTransient else LocStorage) F sm` >> gvs[] >>
  rename1 `fn_has_code sa sb func` >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
   (!p. cnt=Var p ==> not_fresh_at sm p)` by
    (qpat_x_assum `compile_bytestring_word_count _ _ = _` mp_tac >>
     simp[compile_bytestring_word_count_def, emit_op_def, emit_inst_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
     simp[cs_extends_def, IS_PREFIX_APPEND, not_fresh_at_def]) >>
  `cs_extends sm sb` by
    (mp_tac ci_mono_compile_word_copy_loop_op >>
     disch_then (qspecl_then [`Var root`,`slot`,`cnt`,`LocMemory`,
       `if tr then LocTransient else LocStorage`,`F`,`sm`] mp_tac) >>
     simp[ci_mono_def]) >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_at (Pat `compile_bytestring_word_count _ _ = _`)
    store_slots_bytestring_count_origin_ptr >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code sa sm _`)) >>
  disch_then (drule_at (Pat `lookup_var root s = _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `~ctx_has_dalloca _`)) >>
  disch_then (qspec_then `len` mp_tac) >>
  (impl_tac >- (simp[] >> decide_tac)) >> strip_tac >>
  suspend "loop"
QED

Resume store_slots_bytes_words[loop]:
  `execution_frame u = execution_frame s` by
    (qpat_x_assum `u with <|vs_vars := _; vs_inst_idx := _|> = s` mp_tac >>
     simp[venom_state_component_equality, execution_frame_def]) >>
  `u.vs_memory=s.vs_memory /\ u.vs_allocas=s.vs_allocas /\
   u.vs_alloca_next=s.vs_alloca_next /\ u.vs_call_ctx=s.vs_call_ctx /\
   u.vs_labels=s.vs_labels` by
    gvs[execution_frame_def, venom_state_component_equality] >>
  `not_fresh_at sm root /\
   (!y. slot=Var y \/ cnt=Var y ==> not_fresh_at sm y)` by
    (gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `lookup_var root u=SOME sw /\ eval_operand slot u=SOME dw /\
   op_taint tf slot={}` by
    (conj_tac >- metis_tac[] >> Cases_on `slot` >>
     gvs[eval_operand_def, op_taint_def] >> metis_tac[]) >>
  `allocas_from lo u` by
    (qpat_x_assum `allocas_from lo s` mp_tac >> simp[allocas_from_def]) >>
  drule_at (Pat `compile_word_copy_loop_op _ _ _ _ _ _ _ = _`)
    store_slots_live_word_loop >>
  disch_then (drule_at (Pat `ptr_covers Gf tf root u _`)) >>
  disch_then (drule_at (Pat `fn_has_code sm sb _`)) >>
  disch_then (drule_at (Pat `eval_operand slot u = _`)) >>
  disch_then (drule_at (Pat `lookup_var root u = _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `~ctx_has_dalloca _`)) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  suspend "post"
QED

Resume store_slots_bytes_words[post]:
  `store_copy_normalize s u = s` by
    gvs[store_copy_normalize_def, venom_state_component_equality] >>
  qpat_x_assum `store_copy_normalize u u' = _`
    (mp_tac o AP_TERM ``store_copy_normalize s``) >>
  simp[store_slots_normalize_fold, store_slots_normalize_compose,
    mload_def] >> strip_tac >>
  qexistsl [`Gf'`,`tf'`,`u'`] >> conj_tac
  >- (rpt gen_tac >>
      qpat_assum `!D explicit PG. gas_origin_ptr_path _ (s,G,tn) [] _`
        (qspecl_then [`D`,`explicit`,`PG`]
          (mp_then Any mp_tac fragGasOriginPtrTheory.gas_origin_ptr_path_append)) >>
      simp[] >> disch_then irule >> simp[]) >>
  simp[] >> rpt strip_tac >>
  `not_fresh_at sm p` by
    (gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  metis_tac[]
QED

Finalise store_slots_bytes_words

Theorem store_slots_bytes_robust_header:
  (tv = BaseTV (BytesT (Dynamic cap)) \/ tv = BaseTV (StringT cap)) /\
  value_has_type tv v /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v off m) ==>
  ?len. val_store_size tv v = 32 * (1 + word_size len) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      mem_word_at off m = n2w len)
Proof
  strip_tac >> Cases_on `v` >>
  gvs[value_has_type_def, val_store_size_def, val_in_memory_def] >>
  metis_tac[LEFT_ADD_DISTRIB, MULT_COMM, MULT_RIGHT_1]
QED

Theorem store_slots_leaf_origin_ptr:
  ((~is_abi_dynamic cenv.ce_struct_fields ty /\ ~vyper_is_dynamic tenv ty) \/
   (is_abi_dynamic cenv.ce_struct_fields ty /\ is_bytestring_type ty)) /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  compile_store_slots cenv (Var root) slot ty tr sa = ((),sb) /\
  not_fresh_at sa root /\ (!x. slot=Var x ==> not_fresh_at sa x) /\
  lookup_var root s=SOME sw /\ eval_operand slot s=SOME dw /\
  op_prov G slot=NONE /\ op_taint tn slot={} /\
  ptr_covers G tn root s (val_store_size tv v) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n sw) m) /\
  w2n sw+type_memory_size tv<dimword(:256) /\
  w2n dw+type_slot_size tv<=dimword(:256) /\
  encode_value tv v=SOME writes /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb=sa.cs_current_bb /\
  s.vs_inst_idx=LENGTH sa.cs_current_insts /\
  ~s.vs_call_ctx.cc_static /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  w2n sw+val_store_size tv v<=s.vs_alloca_next ==>
  ?Gf tf u ks.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tf)) /\
    store_copy_normalize s u =
      FOLDL (\q k. (if tr then tstore else sstore) (dw+n2w k)
        (mload (w2n sw+32*k) s) q) s ks /\
    u.vs_memory=s.vs_memory /\ tf.t_mem=tn.t_mem /\ tf.t_imm=tn.t_imm /\
    (if tr then tf.t_trans else tf.t_stor) =
      FOLDL (\ta k. key_update ta (dw+n2w k)
        (mem_word_taint tn.t_mem (w2n sw+32*k)))
        (if tr then tn.t_trans else tn.t_stor) ks /\
    (if tr then tf.t_stor else tf.t_trans)=(if tr then tn.t_stor else tn.t_trans) /\
    (!k. MEM k ks <=> MEM k (MAP FST writes)) /\
    (!x. not_fresh_at sa x ==> lookup_var x u=lookup_var x s /\
      FLOOKUP Gf x=FLOOKUP G x /\ op_taint tf (Var x)=op_taint tn (Var x)) /\
    u.vs_allocas=s.vs_allocas /\ u.vs_alloca_next=s.vs_alloca_next /\
    u.vs_labels=s.vs_labels /\ u.vs_call_ctx=s.vs_call_ctx /\
    ~u.vs_halted /\ u.vs_current_bb=sb.cs_current_bb /\
    u.vs_inst_idx=LENGTH sb.cs_current_insts
Proof
  strip_tac
  >- suspend "dense"
  >> suspend "bytes"
QED

Resume store_slots_leaf_origin_ptr[dense]:
  `~is_bytestring_type ty` by
    (Cases_on `ty` >> gvs[is_bytestring_type_def, is_abi_dynamic_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[is_bytestring_type_def, is_abi_dynamic_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[is_bytestring_type_def, is_abi_dynamic_def]) >>
  `val_store_size tv v=type_memory_size tv` by
    metis_tac[fullAssignCopyFactsTheory.topcopy_val_store_size] >>
  `type_memory_size tv=32*type_slot_size tv` by simp[type_memory_size_slots] >>
  `ptr_covers G tn root s (32*type_slot_size tv)` by metis_tac[] >>
  drule_at (Pat `compile_store_slots _ _ _ _ _ _ = _`) store_slots_dense_words >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (drule_at (Pat `~ctx_has_dalloca _`)) >>
  (impl_tac >- (simp[] >> decide_tac)) >> strip_tac >>
  qexistsl [`Gf`,`tf`,`u`,`GENLIST I (type_slot_size tv)`] >> simp[] >>
  gen_tac >> eq_tac
  >- (simp[MEM_GENLIST] >> strip_tac >>
      irule encode_value_live_written >> metis_tac[]) >>
  simp[MEM_GENLIST] >> strip_tac >>
  drule (CONJUNCT1 vyperEncodeDecodeTheory.encode_writes_bounded) >>
  simp[]
QED

Resume store_slots_leaf_origin_ptr[bytes]:
  `?cap. tv=BaseTV (BytesT (Dynamic cap)) \/ tv=BaseTV (StringT cap)` by
    (Cases_on `ty` >> gvs[is_bytestring_type_def, evaluate_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[is_bytestring_type_def, evaluate_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[is_bytestring_type_def, evaluate_type_def]) >>
  drule_at (Pat `value_has_type _ _`) store_slots_bytes_robust_header >>
  disch_then (qspecl_then [`tn`,`s`,`w2n sw`,`cap`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `val_in_memory tv v (w2n sw) s.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  drule_at (Pat `val_in_memory _ _ _ _`) store_slots_bytes_footprint >>
  disch_then (qspecl_then [`writes`,`cap`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `val_store_size tv v <= type_memory_size tv` by
    (Cases_on `v` >>
     gvs[value_has_type_def, val_store_size_def, type_memory_size_def] >>
     qpat_x_assum `LENGTH _ <= cap` (mp_tac o MATCH_MP word_size_monotone) >>
     decide_tac) >>
  `len < dimword(:256)` by
    (qspec_then `len` mp_tac le_word_size_mul >> decide_tac) >>
  `mem_word_at (w2n sw) s.vs_memory = n2w len` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `L < dimword(:256)` by decide_tac >>
  `len = L` by
    (qpat_x_assum `mem_word_at _ _ = n2w L` mp_tac >>
     simp[Once EQ_SYM_EQ, n2w_11]) >> gvs[] >>
  drule_at (Pat `compile_store_slots _ _ _ _ _ _ = _`) store_slots_bytes_words >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (drule_at (Pat `~ctx_has_dalloca _`)) >>
  disch_then (qspec_then `L` mp_tac) >>
  (impl_tac >- (simp[] >> decide_tac)) >> strip_tac >>
  qexistsl [`Gf`,`tf`,`u`,`GENLIST I (1+word_size L)`] >>
  simp[MEM_GENLIST] >>
  pure_once_rewrite_tac [ADD_COMM] >> simp[]
QED

Finalise store_slots_leaf_origin_ptr
