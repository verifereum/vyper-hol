(* Common live-word endpoint for dense and bytestring entry branches. *)
Theory fullStoreSlotsLeafCases
Ancestors
  fullStoreSlotsWordLoop fullStoreSlotsBytes fullStoreDense
  fullStoreSlotsMemberFrame placeStoreSlots stmtSimStoreCopy
  placeStoreCopyPath context emitHelper emitHelperProps exprLoweringProps
  loweringStateRelDefs codegenRel ptrDiscipline bodyPtrDefs compileEnv unitTransformDefs
  venomState venomInst venomExecSemantics
  finite_map pred_set list rich_list arithmetic words

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
