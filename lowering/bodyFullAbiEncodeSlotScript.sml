(* Actual tuple staging: ADD followed by a store, copy, or empty copy. *)
Theory bodyFullAbiEncodeSlot
Ancestors
  bodyFullAbiEncodeOffset bodyFullAbiEncodeStore bodyFullAbiEncodeCopy
  fragGasOriginPtrLoop fragExecPtr
  abiTupleProps bodyPtrMakeArrayPrimitiveInstall bodyPtrMakeArrayWordStore
  assignBasePtrCleanStore exprLoweringProps emitHelperProps fragExec
  assignTuplePtrStoreWord assignTuplePtrCopyEndpoint typedCopyPtr robustCopyTransportPtr contextCodegenRel unitTransformDefs memSafeRun
  ptrDiscipline instMemFrontier codegenRel wordLoadStorePtr
  arithmetic finite_map pred_set words list rich_list compileEnv context emitHelper
  localPtrsProps bodyPtrDefs ghostPcTransportPtr abiAllocationHistory loweringStateRelDefs exprSimProps valueEncodingProps valueEncoding valueEncodingDefs venomState venomExecSemantics venomInst

Theorem abi_encode_tuple_slot_origin:
  !a b ce root off op ty tv v s bw G tn total lo explicit ctx func PG
    d cx es origin G0 tn0 s0.
  compile_abi_tuple_slot ce (Var root) off op ty a = ((),b) /\
  fn_has_code a b func /\ fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ lookup_var root s = SOME bw /\
  ptr_covers G tn root s total /\ not_fresh_at a root /\
  off + type_memory_bytes ce ty <= total /\
  w2n bw + off < dimword(:256) /\
  w2n bw + off + type_memory_bytes ce ty < dimword(:256) /\
  lo <= w2n bw + off /\
  (type_memory_bytes ce ty = 0 \/
   w2n bw + off + type_memory_bytes ce ty <= s.vs_alloca_next) /\
  abi_tuple_input ce ty tv v op s /\
  (!x. op = Var x ==> not_fresh_at a x) /\
  (if is_word_type ty then op_taint tn op = {} else
    ?xs sw. op = Var xs /\ lookup_var xs s = SOME sw /\
      ptr_covers G tn xs s (type_memory_bytes ce ty) /\
      w2n sw + type_memory_bytes ce ty < dimword(:256) /\
      (type_memory_bytes ce ty = 0 \/
       w2n sw + type_memory_bytes ce ty <= s.vs_alloca_next) /\
      (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        val_in_memory tv v (w2n sw) mem)) /\
  local_ptrs_rel func ce es.scopes s /\
  (!name x sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at a x) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at a x) /\
  (!x. not_fresh_at origin x ==> not_fresh_at a x) /\
  (!name z k. local_region ce es.scopes s name z k ==>
    regions_disjoint (w2n bw + off) (type_memory_bytes ce ty) z k) /\
  (!aid z k. FLOOKUP s0.vs_allocas aid = SOME (z,k) /\ aid < origin.cs_next_id ==>
    regions_disjoint (w2n bw + off) (type_memory_bytes ce ty) z k) /\
  (!name z k. local_region ce es.scopes s0 name z k ==>
    regions_disjoint (w2n bw + off) (type_memory_bytes ce ty) z k) ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
    (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
      val_in_memory tv v (w2n bw + off) mem) /\
    (!D. ghost_inv_at D lo d ce cx es G tn s ==>
      ghost_inv_at D lo d ce cx es Gf tnf t) /\
    (ghost_kept_at lo ce es origin G0 tn0 s0 G tn ==>
      ghost_kept_at lo ce es origin G0 tn0 s0 Gf tnf) /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!code. abi_alloca_history code s ==> abi_alloca_history code t) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!i. ~(w2n bw+off <= i /\ i < w2n bw+off+type_memory_bytes ce ty) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!x. not_fresh_at a x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
    (!oldop. (!x. oldop = Var x ==> not_fresh_at a x) ==>
      eval_operand oldop t = eval_operand oldop s /\
      op_taint tnf oldop = op_taint tn oldop /\ op_prov Gf oldop = op_prov G oldop)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_abi_tuple_slot _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_abi_tuple_slot_def, comp_bind_def] >> pairarg_tac >>
  simp[] >> strip_tac >>
  rename1 `emit_op ADD [Var root;Lit (n2w off)] a = (dst,mid)` >>
  `cs_extends a mid /\ cs_extends mid b` by suspend "extends" >>
  `fn_has_code a mid func /\ fn_has_code mid b func` by
    metis_tac[fn_has_code_split] >>
  drule_all abi_encode_owned_offset_origin >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  rename1 `lookup_var q addressed = SOME (n2w (w2n bw+off))` >>
  `!x. not_fresh_at a x ==> x <> q` by suspend "fresh" >>
  `local_ptrs_rel func ce es.scopes addressed /\
   (!name z k. local_region ce es.scopes addressed name z k ==>
     regions_disjoint (w2n bw+off) (type_memory_bytes ce ty) z k)` by suspend "locals" >>
  `(!D. ghost_inv_at D lo d ce cx es G tn s ==>
      ghost_inv_at D lo d ce cx es G' tn' addressed) /\
   (ghost_kept_at lo ce es origin G0 tn0 s0 G tn ==>
      ghost_kept_at lo ce es origin G0 tn0 s0 G' tn')` by suspend "entry_frame" >>
  Cases_on `is_word_type ty` >- suspend "word" >>
  Cases_on `type_memory_bytes ce ty = 0` >- suspend "zero" >>
  suspend "copy"
QED

Resume abi_encode_tuple_slot_origin[extends]:
  conj_tac
  >- (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
      simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def,
        cs_extends_def, IS_PREFIX_APPEND] >> strip_tac >> gvs[] >>
      qexists_tac `[]` >> simp[] >> metis_tac[]) >>
  Cases_on `is_word_type ty` >> Cases_on `type_memory_bytes ce ty` >>
  gvs[compile_copy_memory_def, comp_return_def, emit_void_def, comp_bind_def,
    fresh_id_def, emit_def, comp_ignore_bind_def, cs_extends_def, IS_PREFIX_APPEND]
QED
Resume abi_encode_tuple_slot_origin[fresh]:
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def,
    not_fresh_at_def]
QED
Resume abi_encode_tuple_slot_origin[locals]:
  `!x. (!name sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) sz) ==> x <> q)` by
    metis_tac[] >>
  `!name z k. local_region ce es.scopes addressed name z k <=>
    local_region ce es.scopes s name z k` by
    (simp[local_region_def] >> metis_tac[]) >>
  conj_tac >- (gvs[local_ptrs_rel_def, local_backed_def] >> metis_tac[]) >>
  metis_tac[]
QED
Resume abi_encode_tuple_slot_origin[entry_frame]:
  metis_tac[]
QED
Resume abi_encode_tuple_slot_origin[word]:
  fs[abi_tuple_input_def] >>
  `eval_operand op addressed = SOME (typed_val_to_w256 tv v) /\ op_taint tn' op = {}` by
    metis_tac[] >>
  `emit_void MSTORE [Var q;op] mid = ((),b)` by metis_tac[] >>
  drule_all emit_void_fetch_boundary >> strip_tac >>
  qabbrev_tac `i = mk_inst mid.cs_next_id MSTORE [Var q;op] []` >>
  qabbrev_tac `u = mstore (w2n bw+off) (typed_val_to_w256 tv v) addressed` >>
  qabbrev_tac `tf = step_taint i addressed u tn'` >>
  `tf.t_var = tn'.t_var /\ tf.t_stor = tn'.t_stor /\ tf.t_trans = tn'.t_trans /\
   tf.t_mem = tn'.t_mem DIFF {j | w2n bw+off <= j /\ j < w2n bw+off+32}` by
    suspend "word_taint" >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (addressed,G',tn') []
    (OK (u with vs_inst_idx := SUC addressed.vs_inst_idx),G',tf)` by suspend "word_path" >>
  `(!D. ghost_inv_at D lo d ce cx es G tn s ==>
      ghost_inv_at D lo d ce cx es G' tf (u with vs_inst_idx := SUC addressed.vs_inst_idx)) /\
   (ghost_kept_at lo ce es origin G0 tn0 s0 G tn ==>
      ghost_kept_at lo ce es origin G0 tn0 s0 G' tf)` by suspend "word_frame" >>
  `!mem. mem_agree_outside tf.t_mem u.vs_memory mem ==>
      val_in_memory tv v (w2n bw+off) mem` by suspend "word_robust" >>
  qexistsl_tac [`u with vs_inst_idx := SUC addressed.vs_inst_idx`, `G'`, `tf`] >>
  conj_tac >- (gen_tac >> irule gas_origin_ptr_path_trans >> metis_tac[]) >>
  suspend "word_post"
QED
Resume abi_encode_tuple_slot_origin[zero]:
  fs[compile_copy_memory_def, comp_return_def] >>
  `val_wf tv v /\ val_footprint tv v <= 0` by
    (gvs[abi_tuple_input_def] >> drule val_footprint_le >> decide_tac) >>
  `!mem. mem_agree_outside tn'.t_mem addressed.vs_memory mem ==>
    val_in_memory tv v (w2n bw+off) mem` by
    (rpt strip_tac >> irule robust_val_in_memory_copy_transport >>
     conj_tac >- gvs[] >>
     qexistsl_tac [`s.vs_memory`, `s.vs_memory`, `0`, `w2n sw`, `tn.t_mem`, `tn.t_mem`] >>
     gvs[mem_bytes_at_def]) >>
  qexistsl_tac [`addressed`, `G'`, `tn'`] >> simp[] >>
  metis_tac[ADD_COMM]
QED
Resume abi_encode_tuple_slot_origin[copy]:
  fs[] >>
  `emit_void MCOPY [Var q;Var xs;Lit (n2w (type_memory_bytes ce ty))] mid = ((),b)` by
    (Cases_on `type_memory_bytes ce ty` >> gvs[compile_copy_memory_def]) >>
  drule_all emit_void_fetch_boundary >> strip_tac >>
  `lookup_var xs addressed = SOME sw /\ ptr_covers G' tn' xs addressed (type_memory_bytes ce ty)` by
    (`xs <> q` by metis_tac[] >>
     `lookup_var xs addressed = lookup_var xs s /\ FLOOKUP G' xs = FLOOKUP G xs /\
       op_taint tn' (Var xs) = op_taint tn (Var xs)` by metis_tac[] >>
     conj_tac >- metis_tac[] >>
     qpat_x_assum `ptr_covers G tn xs s _` mp_tac >>
     simp[NoAsms, ptr_covers_def] >> metis_tac[]) >>
  qabbrev_tac `i = mk_inst mid.cs_next_id MCOPY [Var q;Var xs;Lit (n2w (type_memory_bytes ce ty))] []` >>
  qabbrev_tac `u = mcopy (w2n bw+off) (w2n sw) (type_memory_bytes ce ty) addressed` >>
  qabbrev_tac `tf = step_taint i addressed u tn'` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (addressed,G',tn') []
    (OK (u with vs_inst_idx := SUC addressed.vs_inst_idx),G',tf)` by suspend "copy_path" >>
  qexistsl_tac [`u with vs_inst_idx := SUC addressed.vs_inst_idx`, `G'`, `tf`] >>
  conj_tac >- (gen_tac >> irule gas_origin_ptr_path_trans >> metis_tac[]) >>
  suspend "copy_post"
QED
Resume abi_encode_tuple_slot_origin[word_taint]:
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`, `G'`, `mid.cs_next_id`] mp_tac) >>
  simp[Abbr `tf`, Abbr `u`, Abbr `i`] >> metis_tac[]
QED
Resume abi_encode_tuple_slot_origin[word_path]:
  gen_tac >> simp[NoAsms, Abbr `tf`, Abbr `i`, Abbr `u`] >>
  `off + w2n bw = w2n (n2w (off + w2n bw):bytes32)` by
    (simp[] >> decide_tac) >>
  pop_assum SUBST1_TAC >> irule abi_encode_mstore_origin_path >>
  gvs[allocas_from_def, inst_dload_in_section_def, inst_mem_below_frontier_def,
    mk_inst_def, eval_operand_def] >>
  gvs[source_memory_read_ranges_def, source_memory_write_ranges_def,
      fixed_source_write_range_def, eval_operand_def, lookup_var_def, update_var_def] >>
  metis_tac[]
QED
Resume abi_encode_tuple_slot_origin[word_frame]:
  conj_tac
  >- (rpt strip_tac >>
      simp[NoAsms, Abbr `tf`, Abbr `i`, Abbr `u`] >>
      `off+w2n bw = w2n (n2w (off+w2n bw):bytes32)` by (simp[] >> decide_tac) >>
      pop_assum SUBST1_TAC >> irule (cj 1 abi_encode_mstore_frame_at) >>
      simp[] >>
      `ghost_kept_at lo ce es origin G' tn' addressed G' tn'` by simp[ghost_kept_at_def] >>
      metis_tac[]) >>
  strip_tac >>
  `ghost_kept_at lo ce es origin G0 tn0 s0 G' tn'` by metis_tac[] >>
  qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ G' tn'` mp_tac >>
  simp[NoAsms, ghost_kept_at_def] >> strip_tac >>
  fs[op_taint_def] >> metis_tac[IN_DIFF]
QED
Resume abi_encode_tuple_slot_origin[word_robust]:
  rpt strip_tac >> irule val_in_memory_clean_footprint_ptr >>
  conj_tac >- simp[] >> qexistsl_tac [`tf.t_mem`, `u.vs_memory`] >>
  reverse conj_tac >- (simp[Abbr `u`] >> metis_tac[abi_tuple_word_mstore]) >>
  rpt strip_tac >>
  `val_footprint tv v <= 32` by metis_tac[val_footprint_le] >>
  gvs[]
QED
Resume abi_encode_tuple_slot_origin[word_post]:
  conj_tac >- gvs[] >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  `tf.t_imm = tn.t_imm` by
    simp[Abbr `tf`, Abbr `i`, step_taint_def, imm_taint_def, mk_inst_def] >>
  `!j. ~(w2n bw+off <= j /\ j < w2n bw+off+32) ==>
    mem_bytes_at j 1 u.vs_memory = mem_bytes_at j 1 s.vs_memory /\
    (j IN tf.t_mem <=> j IN tn.t_mem)` by
    (gen_tac >> disch_tac >> conj_tac
     >- (simp[NoAsms, Abbr `u`] >>
         irule EQ_TRANS >> qexists_tac `mem_bytes_at j 1 addressed.vs_memory` >>
         conj_tac >- (irule mstore_mem_bytes_at_disjoint >> decide_tac) >> simp[]) >>
     gvs[]) >>
  `!oldop. op_taint tf oldop = op_taint tn' oldop` by
    (Cases >> simp[op_taint_def]) >>
  `!x. not_fresh_at a x ==> lookup_var x addressed = lookup_var x s /\
    FLOOKUP G' x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    metis_tac[] >>
  gvs[Abbr `u`, mstore_def, write_memory_with_expansion_def,
    abi_alloca_history_def, lookup_var_def] >> metis_tac[]
QED
Resume abi_encode_tuple_slot_origin[copy_path]:
  gen_tac >> simp[NoAsms, Abbr `tf`, Abbr `i`, Abbr `u`] >>
  `off + w2n bw = w2n (n2w (off + w2n bw):bytes32)` by
    (simp[] >> decide_tac) >>
  `type_memory_bytes ce ty = w2n (n2w (type_memory_bytes ce ty):bytes32)` by
    (simp[] >> decide_tac) >>
  ntac 2 (pop_assum SUBST1_TAC) >> irule abi_encode_mcopy_origin_path >>
  gvs[allocas_from_def, inst_dload_in_section_def, inst_mem_below_frontier_def,
    mk_inst_def, eval_operand_def] >>
  gvs[source_memory_read_ranges_def, source_memory_write_ranges_def,
      fixed_source_write_range_def, sized_source_write_range_def, op_taint_def,
      eval_operand_def, lookup_var_def, update_var_def] >>
  metis_tac[]
QED
Resume abi_encode_tuple_slot_origin[copy_post]:
  `val_wf tv v /\ val_footprint tv v <= type_memory_bytes ce ty` by
    (fs[abi_tuple_input_def] >> metis_tac[val_footprint_le]) >>
  `!mem. mem_agree_outside tn'.t_mem addressed.vs_memory mem ==>
    val_in_memory tv v (w2n sw) mem` by gvs[] >>
  `tf.t_var = tn'.t_var /\ tf.t_stor = tn'.t_stor /\ tf.t_trans = tn'.t_trans /\
    (!j. ~(w2n bw+off <= j /\ j < w2n bw+off+type_memory_bytes ce ty) ==>
      (j IN tf.t_mem <=> j IN tn'.t_mem))` by suspend "copy_taint" >>
  conj_tac >- suspend "copy_robust" >>
  conj_tac >- suspend "copy_inv" >>
  conj_tac >- suspend "copy_kept" >>
  suspend "copy_fields"
QED
Resume abi_encode_tuple_slot_origin[copy_taint]:
  `eval_operand (Var q) addressed = SOME (n2w (w2n bw+off)) /\
   eval_operand (Var xs) addressed = SOME sw /\
   eval_operand (Lit (n2w (type_memory_bytes ce ty))) addressed =
     SOME (n2w (type_memory_bytes ce ty))` by simp[eval_operand_def] >>
  qpat_assum `eval_operand (Var q) _ = _` (mp_then Any mp_tac mcopy_operand_ghost_frame) >>
  disch_then (fn th => qpat_assum `eval_operand (Var xs) _ = _` (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `eval_operand (Lit _) _ = _` (mp_then Any mp_tac th)) >>
  disch_then (qspecl_then [`PG`, `G'`, `tn'`, `mid.cs_next_id`] mp_tac) >>
  simp[Abbr `tf`, Abbr `i`, Abbr `u`] >> rpt strip_tac >> gvs[] >>
  eq_tac >> rpt strip_tac >> gvs[] >> decide_tac
QED
Resume abi_encode_tuple_slot_origin[copy_robust]:
  rpt strip_tac >> simp[NoAsms, Abbr `tf`, Abbr `i`, Abbr `u`] >>
  `off+w2n bw = w2n (n2w (off+w2n bw):bytes32)` by (simp[] >> decide_tac) >>
  `type_memory_bytes ce ty = w2n (n2w (type_memory_bytes ce ty):bytes32)` by
    (simp[] >> decide_tac) >>
  ntac 2 (pop_assum SUBST1_TAC) >> pure_rewrite_tac[n2w_w2n] >>
  irule mcopy_staged_robust_ptr >> conj_tac >- simp[] >>
  qexists_tac `sw` >> qexists_tac `Lit (n2w (type_memory_bytes ce ty))` >>
  qexists_tac `Var q` >> qexists_tac `mid.cs_next_id` >>
  qexists_tac `n2w (type_memory_bytes ce ty)` >> qexists_tac `addressed` >>
  qexists_tac `Var xs` >> qexists_tac `tn'` >>
  gvs[eval_operand_def]
QED
Resume abi_encode_tuple_slot_origin[copy_inv]:
  rpt strip_tac >> simp[NoAsms, Abbr `tf`, Abbr `i`, Abbr `u`] >>
  `off+w2n bw = w2n (n2w (off+w2n bw):bytes32)` by (simp[] >> decide_tac) >>
  `type_memory_bytes ce ty = w2n (n2w (type_memory_bytes ce ty):bytes32)` by
    (simp[] >> decide_tac) >>
  ntac 2 (pop_assum SUBST1_TAC) >> pure_rewrite_tac[n2w_w2n] >>
  irule (cj 1 abi_encode_mcopy_frame_at) >>
  simp[eval_operand_def] >>
  gvs[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`G'`, `origin with cs_next_id := 0`,
    `update_var q (bw+n2w off) s with vs_inst_idx := LENGTH mid.cs_current_insts`, `tn'`] >>
  simp[ghost_kept_at_def] >> metis_tac[]
QED
Resume abi_encode_tuple_slot_origin[copy_kept]:
  strip_tac >>
  `ghost_kept_at lo ce es origin G0 tn0 s0 G' tn'` by metis_tac[] >>
  qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ G' tn'` mp_tac >>
  rewrite_tac[ghost_kept_at_def] >> strip_tac >>
  conj_tac >- (fs[op_taint_def] >> metis_tac[]) >>
  conj_tac
  >- (map_every qx_gen_tac [`aid1`, `z`, `k`, `j`] >> strip_tac >>
      `regions_disjoint (w2n bw+off) (type_memory_bytes ce ty) z k` by metis_tac[ADD_COMM] >>
      `~(w2n bw+off <= j /\ j < w2n bw+off+type_memory_bytes ce ty)` by
        (qpat_x_assum `regions_disjoint (w2n bw+off) _ z k` mp_tac >>
         rewrite_tac[regions_disjoint_def] >> decide_tac) >>
      `j IN tn'.t_mem` by metis_tac[] >> metis_tac[]) >>
  conj_tac
  >- (map_every qx_gen_tac [`name`, `z`, `k`, `j`] >> strip_tac >>
      `regions_disjoint (w2n bw+off) (type_memory_bytes ce ty) z k` by metis_tac[ADD_COMM] >>
      `~(w2n bw+off <= j /\ j < w2n bw+off+type_memory_bytes ce ty)` by
        (qpat_x_assum `regions_disjoint (w2n bw+off) _ z k` mp_tac >>
         rewrite_tac[regions_disjoint_def] >> decide_tac) >>
      `j IN tn'.t_mem` by metis_tac[] >> metis_tac[]) >>
  qx_gen_tac `j` >> strip_tac >>
  `~(w2n bw+off <= j /\ j < w2n bw+off+type_memory_bytes ce ty)` by decide_tac >>
  metis_tac[]
QED
Resume abi_encode_tuple_slot_origin[copy_fields]:
  `tf.t_imm = tn.t_imm` by
    simp[Abbr `tf`, Abbr `i`, step_taint_def, imm_taint_def, mk_inst_def] >>
  `!j. ~(w2n bw+off <= j /\ j < w2n bw+off+type_memory_bytes ce ty) ==>
    mem_bytes_at j 1 u.vs_memory = mem_bytes_at j 1 s.vs_memory /\
    (j IN tf.t_mem <=> j IN tn.t_mem)` by
    (gen_tac >> disch_tac >> conj_tac
     >- (simp[NoAsms, Abbr `u`] >>
         irule EQ_TRANS >> qexists_tac `mem_bytes_at j 1 addressed.vs_memory` >>
         conj_tac >- (irule mcopy_mem_bytes_at_disjoint >> decide_tac) >> simp[]) >>
     gvs[]) >>
  `!oldop. op_taint tf oldop = op_taint tn' oldop` by
    (Cases >> simp[op_taint_def]) >>
  `!x. not_fresh_at a x ==> lookup_var x addressed = lookup_var x s /\
    FLOOKUP G' x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    metis_tac[] >>
  gvs[Abbr `u`, mcopy_def, write_memory_with_expansion_def,
    abi_alloca_history_def, lookup_var_def] >>
  conj_tac >- metis_tac[] >>
  Cases >> simp[eval_operand_def, lookup_var_def] >> metis_tac[]
QED
Finalise abi_encode_tuple_slot_origin
