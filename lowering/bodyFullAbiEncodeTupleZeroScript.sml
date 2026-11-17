(* Zero-capacity slots do not inspect their source operand. *)
Theory bodyFullAbiEncodeTupleZero
Ancestors
  bodyFullAbiEncodeSlot bodyFullAbiEncodeTuple bodyFullAbiEncodeOffset
  abiTupleProps exprLoweringProps
  exprSimBufferEmpty valueEncoding valueEncodingDefs vyperValue
  exprLowering compileEnv context emitHelper fragExec ptrDiscipline
  venomState venomExecSemantics loweringStateRelDefs exprSimProps
  arithmetic finite_map pred_set words list

Theorem zero_kvs_memory[local]:
  (!v. val_wf tv v ==> !p mem. val_in_memory tv v p mem) ==>
  !kvs n. kvs_val_wf kvs tv n ==> !p mem. kvs_in_memory kvs p tv mem
Proof
  strip_tac >> Induct >> simp[val_wf_def, val_in_memory_def] >>
  Cases_on `h` >> simp[val_wf_def, val_in_memory_def] >> metis_tac[]
QED

Theorem zero_bound_kvs[local]:
  kvs_val_wf kvs tv 0 ==> kvs = []
Proof
  Cases_on `kvs` >> simp[val_wf_def] >> Cases_on `h` >> simp[val_wf_def]
QED

Theorem zero_wf_memory_mutual[local]:
  (!tv. !v. type_memory_size tv = 0 /\ val_wf tv v ==>
    !p mem. val_in_memory tv v p mem) /\
  (!ts. !vs. type_memory_size_list ts = 0 /\ tuple_val_wf vs ts ==>
    !p mem. tuple_in_memory vs ts p mem) /\
  (!fs. !vs. type_memory_size_fields fs = 0 /\ fields_val_wf vs fs ==>
    !p mem. fields_in_memory vs fs p mem)
Proof
  ho_match_mp_tac type_memory_size_ind >> simp[type_memory_size_def] >>
  conj_tac
  >- (Cases >> simp[val_wf_def, val_in_memory_def, type_memory_size_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >> simp[val_wf_def]) >>
  conj_tac
  >- (gen_tac >> strip_tac >> Cases >>
      simp[val_wf_def, val_in_memory_def, type_memory_size_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >>
      simp[val_wf_def, val_in_memory_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
      `type_memory_size (ArrayTV tv (Fixed n)) = 0` by
        fs[type_memory_size_def] >>
      Cases_on `v` >> gvs[val_wf_def, val_in_memory_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >>
      gvs[val_wf_def, val_in_memory_def]
      >- (drule zero_bound_kvs >> simp[val_in_memory_def]) >>
      drule zero_kvs_memory >> disch_then drule >>
      strip_tac >> simp[] >> rpt strip_tac >> irule default_memory_zero_bytes >>
      simp[mem_bytes_at_def]) >>
  conj_tac
  >- (gen_tac >> strip_tac >> Cases >>
      simp[val_wf_def, val_in_memory_def, type_memory_size_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >>
      simp[val_wf_def, val_in_memory_def] >> metis_tac[]) >>
  conj_tac
  >- (Cases >> simp[val_wf_def, val_in_memory_def]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> Cases >>
      simp[val_wf_def, val_in_memory_def] >> metis_tac[]) >>
  conj_tac
  >- (Cases >> simp[val_wf_def, val_in_memory_def] >>
      Cases_on `h` >> simp[val_wf_def, val_in_memory_def]) >>
  rpt gen_tac >> strip_tac >> Cases >>
  simp[val_wf_def, val_in_memory_def] >>
  Cases_on `h` >> simp[val_wf_def, val_in_memory_def] >> metis_tac[]
QED

Theorem abi_encode_tuple_slot_zero_origin:
  !a b ce root off op ty tv v s bw G tn total lo explicit ctx func PG
    d cx es origin G0 tn0 s0.
  compile_abi_tuple_slot ce (Var root) off op ty a = ((),b) /\
  ~is_word_type ty /\ type_memory_bytes ce ty = 0 /\
  val_wf tv v /\ type_memory_size tv = 0 /\
  fn_has_code a b func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\ allocas_from lo s /\
  lookup_var root s = SOME bw /\ ptr_covers G tn root s total /\
  off <= total /\ w2n bw + off < dimword(:256) /\
  (!name x sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at a x) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at a x) /\
  (!x. not_fresh_at origin x ==> not_fresh_at a x) ==>
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
    (!i. mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!x. not_fresh_at a x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
    (!oldop. (!x. oldop = Var x ==> not_fresh_at a x) ==>
      eval_operand oldop t = eval_operand oldop s /\
      op_taint tnf oldop = op_taint tn oldop /\ op_prov Gf oldop = op_prov G oldop)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_abi_tuple_slot _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_abi_tuple_slot_def, comp_bind_def, compile_copy_memory_def,
    comp_return_def] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `off + 0 <= total' /\ w2n bw + off < dimword(:256)` by decide_tac >>
  drule_all (Q.INST [`n` |-> `0`] (SPEC_ALL abi_encode_owned_offset_origin)) >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  `!x. not_fresh_at a x ==> x <> q` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_var_def, fresh_id_def, emit_def, not_fresh_at_def]) >>
  qexistsl_tac [`t`, `G'`, `tn'`] >>
  simp[] >> metis_tac[zero_wf_memory_mutual]
QED

(* Changing an ignored zero-copy operand does not change compiler output. *)
Theorem zero_slot_operand_cong[local]:
  ~is_word_type ty /\ type_memory_bytes ce ty = 0 ==>
  compile_abi_tuple_slot ce buf off op ty =
  compile_abi_tuple_slot ce buf off op' ty
Proof
  strip_tac >> simp[FUN_EQ_THM, compile_abi_tuple_slot_def,
    compile_copy_memory_def, comp_bind_def]
QED

Theorem zero_tuple_operand_cong[local]:
  !xs off a.
  compile_store_abi_tuple ce buf off
    (MAP (\(op,ty). ((if ~is_word_type ty /\ type_memory_bytes ce ty = 0
       then Var root else op),ty)) xs) a =
  compile_store_abi_tuple ce buf off xs a
Proof
  Induct >> simp[compile_store_abi_tuple_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  Cases_on `~is_word_type h1 /\ type_memory_bytes ce h1 = 0` >>
  gvs[compile_store_abi_tuple_def, compile_copy_memory_def, comp_bind_def,
    comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> Cases_on `is_word_type h1` >> gvs[]
QED

Theorem abi_encode_tuple_staging_zero_safe:
  !a b ce root ops tys tvs vs total s bw G tn lo explicit ctx func PG
    d cx es origin G0 tn0 s0.
  compile_store_abi_tuple ce (Var root) 0 (ZIP (ops,tys)) a = ((),b) /\
  LENGTH ops = LENGTH tys /\ LENGTH tvs = LENGTH tys /\ LENGTH vs = LENGTH tys /\
  total = abi_tuple_bytes ce (ZIP (ops,tys)) /\
  fn_has_code a b func /\ fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ lookup_var root s = SOME bw /\
  ptr_covers G tn root s total /\ not_fresh_at a root /\
  w2n bw + total < dimword(:256) /\ lo <= w2n bw /\
  (total = 0 \/ w2n bw + total <= s.vs_alloca_next) /\
  (!i. i < LENGTH tys ==>
    val_wf (EL i tvs) (EL i vs) /\
    type_memory_size (EL i tvs) = type_memory_bytes ce (EL i tys) /\
    type_memory_bytes ce (EL i tys) < dimword(:256) /\
    (if ~is_word_type (EL i tys) /\ type_memory_bytes ce (EL i tys) = 0 then T else
      abi_tuple_input ce (EL i tys) (EL i tvs) (EL i vs) (EL i ops) s /\
      (!x. EL i ops = Var x ==> not_fresh_at a x) /\
      (if is_word_type (EL i tys) then op_taint tn (EL i ops) = {} else
        ?x w. EL i ops = Var x /\ lookup_var x s = SOME w /\
          ptr_covers G tn x s (type_memory_bytes ce (EL i tys)) /\
          w2n w + type_memory_bytes ce (EL i tys) < dimword(:256) /\
          w2n w + type_memory_bytes ce (EL i tys) <= s.vs_alloca_next /\
          (val_footprint (EL i tvs) (EL i vs) = 0 \/
           regions_disjoint (w2n bw) total (w2n w)
             (val_footprint (EL i tvs) (EL i vs))) /\
          (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
            val_in_memory (EL i tvs) (EL i vs) (w2n w) mem)))) /\
  local_ptrs_rel func ce es.scopes s /\
  (!name x sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at a x) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at a x) /\
  (!x. not_fresh_at origin x ==> not_fresh_at a x) /\
  (!name z k. local_region ce es.scopes s name z k ==>
    regions_disjoint (w2n bw) total z k) /\
  (!aid z k. FLOOKUP s0.vs_allocas aid = SOME (z,k) /\ aid < origin.cs_next_id ==>
    regions_disjoint (w2n bw) total z k) /\
  (!name z k. local_region ce es.scopes s0 name z k ==>
    regions_disjoint (w2n bw) total z k) ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
    (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
      val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) (w2n bw) mem) /\
    lookup_var root t = SOME bw /\ ptr_covers Gf tnf root t total /\
    local_ptrs_rel func ce es.scopes t /\
    (!D. ghost_inv_at D lo d ce cx es G tn s ==>
      ghost_inv_at D lo d ce cx es Gf tnf t) /\
    (ghost_kept_at lo ce es origin G0 tn0 s0 G tn ==>
      ghost_kept_at lo ce es origin G0 tn0 s0 Gf tnf) /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!code. abi_alloca_history code s ==> abi_alloca_history code t) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!i. ~(w2n bw <= i /\ i < w2n bw + total) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!x. not_fresh_at a x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
    (!oldop. (!x. oldop = Var x ==> not_fresh_at a x) ==>
      eval_operand oldop t = eval_operand oldop s /\
      op_taint tnf oldop = op_taint tn oldop /\ op_prov Gf oldop = op_prov G oldop)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `zs = MAP (\(op,ty).
    if ~is_word_type ty /\ type_memory_bytes ce ty = 0 then Var root else op)
    (ZIP (ops,tys))` >>
  `LENGTH zs = LENGTH tys` by simp[Abbr `zs`] >>
  `!i. i < LENGTH tys ==> EL i zs =
    (if ~is_word_type (EL i tys) /\ type_memory_bytes ce (EL i tys) = 0
     then Var root else EL i ops)` by
    (rpt strip_tac >> simp[Abbr `zs`, EL_MAP, EL_ZIP]) >>
  `ZIP (zs,tys) = MAP (\(op,ty).
    ((if ~is_word_type ty /\ type_memory_bytes ce ty = 0 then Var root else op),ty))
    (ZIP (ops,tys))` by suspend "zip" >>
  `compile_store_abi_tuple ce (Var root) 0 (ZIP (zs,tys)) a = ((),b)` by
    metis_tac[zero_tuple_operand_cong] >>
  `abi_tuple_bytes ce (ZIP (zs,tys)) = abi_tuple_bytes ce (ZIP (ops,tys))` by
    suspend "bytes" >>
  irule abi_encode_tuple_staging_full >>
  asm_rewrite_tac[] >> qexistsl_tac [`zs`, `tys`] >> asm_rewrite_tac[] >>
  conj_tac >- suspend "fresh" >>
  conj_tac >- suspend "input" >>
  suspend "resource"
QED
Resume abi_encode_tuple_staging_zero_safe[zip]:
  irule LIST_EQ >> simp[] >> rpt strip_tac >> simp[EL_ZIP, EL_MAP]
QED
Resume abi_encode_tuple_staging_zero_safe[bytes]:
  simp[abiTupleEncodeMemoryTheory.abi_tuple_encode_bytes_zip]
QED
Resume abi_encode_tuple_staging_zero_safe[fresh]:
  rpt strip_tac >>
  qpat_x_assum `!i. i < LENGTH tys ==> val_wf _ _ /\ _`
    (qspec_then `i` mp_tac) >>
  Cases_on `~is_word_type (EL i tys) /\ type_memory_bytes ce (EL i tys) = 0` >>
  gvs[] >> metis_tac[]
QED
Resume abi_encode_tuple_staging_zero_safe[input]:
  rpt strip_tac >>
  qpat_x_assum `!i. i < LENGTH tys ==> val_wf _ _ /\ _`
    (qspec_then `i` mp_tac) >>
  Cases_on `~is_word_type (EL i tys) /\ type_memory_bytes ce (EL i tys) = 0` >>
  gvs[] >> strip_tac >>
  gvs[abi_tuple_input_def, eval_operand_def] >>
  imp_res_tac val_footprint_le >>
  simp[regions_disjoint_def] >>
  metis_tac[zero_wf_memory_mutual]
QED
Resume abi_encode_tuple_staging_zero_safe[resource]:
  rpt strip_tac >>
  qpat_x_assum `!i. i < LENGTH tys ==> val_wf _ _ /\ _`
    (qspec_then `i` mp_tac) >>
  Cases_on `~is_word_type (EL i tys) /\ type_memory_bytes ce (EL i tys) = 0` >>
  gvs[] >> strip_tac >> gvs[] >> simp[zero_wf_memory_mutual]
  >- (irule reasonCopySourcePtrTheory.ptr_covers_mono >>
      goal_assum (drule_at Any) >> simp[]) >>
  Cases_on `is_word_type (EL i tys)` >> gvs[] >> metis_tac[]
QED
Finalise abi_encode_tuple_staging_zero_safe
