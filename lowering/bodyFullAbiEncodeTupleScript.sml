(* Post-allocation tuple staging. Argument evaluation and allocation are
   separate callers; this theory never transports a pre-horizon execution. *)
Theory bodyFullAbiEncodeTuple
Ancestors
  bodyFullAbiEncodeSlot bodyFullAbiEncodeTupleStage
  bodyFullAbiEncodeTupleResources assignTuplePtrCopyLen
  typedCopyTuplePtr logValueFramePtr typedCopyRobustTransportPtr
  bodyPtrSubscriptMemoryRebuild
  compileEnv context emitHelperProps exprLoweringProps fragGasOriginPtrLoop
  abiTupleEncodeSlot
  externalEntryShape exprLowering fragExec emitHelper
  abiTupleProps bodyPtrDefs robustCopyTransportPtr valueEncodingProps
  valueEncodingDefs venomExecSemantics venomState ptrDiscipline exprSimProps
  localPtrsProps loweringStateRelDefs abiDecodeStaticProps
  arithmetic list rich_list pair finite_map pred_set words

(* A later slot preserves a live source resource if its write interval
   misses the represented footprint. Coverage is transported independently
   of the bytes, so no cleanliness of capacity padding is required. *)
Theorem abi_encode_tuple_resource_frame[local]:
  abi_tuple_input ce ty tv v op s /\
  (!x. op = Var x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)) /\
  eval_operand op t = eval_operand op s /\
  (!i. i NOTIN writes ==> mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
  (if is_word_type ty then op_taint tn op = {} else
    ?x w. op = Var x /\ lookup_var x s = SOME w /\
      ptr_covers G tn x s (type_memory_bytes ce ty) /\
      (!i. w2n w <= i /\ i < w2n w + val_footprint tv v ==> i NOTIN writes) /\
      (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        val_in_memory tv v (w2n w) mem)) ==>
  abi_tuple_input ce ty tv v op t /\
  (if is_word_type ty then op_taint tn' op = {} else
    ?x w. op = Var x /\ lookup_var x t = SOME w /\
      ptr_covers G' tn' x t (type_memory_bytes ce ty) /\
      (!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
        val_in_memory tv v (w2n w) mem))
Proof
  strip_tac >> Cases_on `is_word_type ty`
  >- (gvs[abi_tuple_input_def] >> Cases_on `op` >> gvs[op_taint_def]) >>
  fs[] >>
  `val_wf tv v` by gvs[abi_tuple_input_def] >>
  `!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
    val_in_memory tv v (w2n w) mem` by
    (rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
     conj_tac >- simp[] >>
     qexistsl_tac [`s.vs_memory`, `t.vs_memory`, `tn.t_mem`, `tn'.t_mem`, `writes`] >>
     simp[] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  conj_tac
  >- (gvs[abi_tuple_input_def, eval_operand_def] >>
      metis_tac[mem_agree_outside_def]) >>
  reverse conj_tac >- simp[] >>
  irule ptr_covers_lookup_frame >> goal_assum (drule_at Any) >> simp[]
QED

Theorem abi_encode_tuple_head_resource[local]:
  abi_tuple_input ce ty tv v op s /\
  (!x. op = Var x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)) /\
  eval_operand op t = eval_operand op s /\
  t.vs_alloca_next = s.vs_alloca_next /\
  (!i. ~(addr <= i /\ i < addr + capacity) ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
  off + type_memory_bytes ce ty <= capacity /\
  (~is_word_type ty ==> !w. eval_operand op s = SOME w ==>
    (val_footprint tv v = 0 \/
     loweringStateRelDefs$regions_disjoint addr capacity (w2n w) (val_footprint tv v))) /\
  (if is_word_type ty then op_taint tn op = {} else
    ?x w. op = Var x /\ lookup_var x s = SOME w /\
      ptr_covers G tn x s (type_memory_bytes ce ty) /\
      w2n w + type_memory_bytes ce ty < dimword(:256) /\
      (type_memory_bytes ce ty = 0 \/
       w2n w + type_memory_bytes ce ty <= s.vs_alloca_next) /\
      (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        val_in_memory tv v (w2n w) mem)) ==>
  abi_tuple_input ce ty tv v op t /\
  (if is_word_type ty then op_taint tn' op = {} else
    ?x w. op = Var x /\ lookup_var x t = SOME w /\
      ptr_covers G' tn' x t (type_memory_bytes ce ty) /\
      w2n w + type_memory_bytes ce ty < dimword(:256) /\
      (type_memory_bytes ce ty = 0 \/
       w2n w + type_memory_bytes ce ty <= t.vs_alloca_next) /\
      (!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
        val_in_memory tv v (w2n w) mem))
Proof
  strip_tac >>
  `abi_tuple_input ce ty tv v op t /\
    (if is_word_type ty then op_taint tn' op = {} else
      ?x w. op = Var x /\ lookup_var x t = SOME w /\
        ptr_covers G' tn' x t (type_memory_bytes ce ty) /\
        (!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
          val_in_memory tv v (w2n w) mem))` by
    (irule abi_encode_tuple_resource_frame >>
     qexistsl_tac [`G`, `s`, `tn`, `{i | addr <= i /\ i < addr + capacity}`] >>
     simp[] >> Cases_on `is_word_type ty` >> gvs[] >>
     `val_footprint tv v = 0 \/
      loweringStateRelDefs$regions_disjoint addr capacity (w2n w) (val_footprint tv v)` by
       (first_x_assum irule >> simp[eval_operand_def]) >>
     gvs[loweringStateRelDefsTheory.regions_disjoint_def] >>
     rpt strip_tac >> decide_tac) >>
  Cases_on `is_word_type ty` >> gvs[]
QED

Theorem abi_encode_tuple_local_frame[local]:
  local_ptrs_rel func ce scopes s /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  (!name x sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) sz) ==>
    lookup_var x t = lookup_var x s) /\
  (!name z k. local_region ce scopes s name z k ==> regions_disjoint p n z k) /\
  (!i. ~(p <= i /\ i < p+n) ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory) ==>
  local_ptrs_rel func ce scopes t /\
  (!name z k. local_region ce scopes t name z k <=> local_region ce scopes s name z k) /\
  (!lo. allocas_from lo t <=> allocas_from lo s)
Proof
  strip_tac >> reverse conj_tac
  >- (conj_tac
      >- (rpt gen_tac >> irule local_region_lookup_cong >> metis_tac[]) >>
      simp[allocas_from_def]) >>
  irule local_ptrs_rel_mem_agree >> qexists_tac `s` >> simp[]
  >> reverse conj_tac >- (conj_tac >- metis_tac[] >> metis_tac[optionTheory.NOT_SOME_NONE]) >>
  rpt strip_tac >> irule mem_bytes_at_bytewise >> rpt strip_tac >>
  sym_tac >> first_x_assum irule >>
  `regions_disjoint p n b sz` by metis_tac[] >>
  fs[regions_disjoint_def] >> decide_tac
QED

Theorem abi_encode_tuple_prefix_extend[local]:
  LENGTH tvs = LENGTH vs /\ (k:num) < LENGTH tvs /\
  (!i. i <= k ==> val_wf (EL i tvs) (EL i vs)) /\
  (!i m. i < k /\ mem_agree_outside tn mem m ==>
    val_in_memory (EL i tvs) (EL i vs)
      ((addr:num) + SUM (MAP type_memory_size (TAKE i tvs))) m) /\
  (!j. ~(addr + SUM (MAP type_memory_size (TAKE k tvs)) <= j /\
          j < addr + SUM (MAP type_memory_size (TAKE k tvs)) +
            type_memory_size (EL k tvs)) ==>
    mem_bytes_at j 1 mem' = mem_bytes_at j 1 mem /\
    (j IN tn' <=> j IN tn)) /\
  (!m. mem_agree_outside tn' mem' m ==>
    val_in_memory (EL k tvs) (EL k vs)
      (addr + SUM (MAP type_memory_size (TAKE k tvs))) m) ==>
  !i m. i < SUC k /\ mem_agree_outside tn' mem' m ==>
    val_in_memory (EL i tvs) (EL i vs)
      (addr + SUM (MAP type_memory_size (TAKE i tvs))) m
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> Cases_on `i = k`
  >- gvs[] >>
  `i < k` by decide_tac >>
  `SUM (MAP type_memory_size (TAKE i tvs)) + type_memory_size (EL i tvs) <=
    SUM (MAP type_memory_size (TAKE k tvs))` by
    (irule sum_take_element_before >> simp[]) >>
  irule robust_representation_exterior_frame >>
  conj_tac >- (first_x_assum irule >> decide_tac) >>
  qexistsl_tac [`addr + SUM (MAP type_memory_size (TAKE k tvs))`,
    `mem`, `mem'`, `type_memory_size (EL k tvs)`, `tn`, `tn'`] >>
  simp[] >> metis_tac[]
QED

Theorem abi_encode_tuple_step_layout[local]:
  compile_store_abi_tuple ce buf off ((op,ty)::rest) st = ((),b) /\
  compile_abi_tuple_slot ce buf off op ty st = ((),mid) /\
  cs_extends a st /\ fn_has_code a b func ==>
  compile_store_abi_tuple ce buf (off + type_memory_bytes ce ty) rest mid = ((),b) /\
  cs_extends st mid /\ cs_extends mid b /\ cs_extends a mid /\
  fn_has_code st mid func
Proof
  strip_tac >>
  `compile_store_abi_tuple ce buf off ((op,ty)::rest) st =
    (do compile_abi_tuple_slot ce buf off op ty;
        compile_store_abi_tuple ce buf (off + type_memory_bytes ce ty) rest od) st` by
    (simp[NoAsms, compile_store_abi_tuple_def, compile_abi_tuple_slot_def,
      comp_bind_def, comp_ignore_bind_def] >>
     Cases_on `emit_op ADD [buf; Lit (n2w off)] st` >> simp[]) >>
  `compile_store_abi_tuple ce buf (off + type_memory_bytes ce ty) rest mid = ((),b)` by
    gvs[comp_bind_def, comp_ignore_bind_def] >>
  `cs_extends mid b` by
    (mp_tac (Q.SPECL [`ce`, `buf`, `off + type_memory_bytes ce ty`, `rest`, `mid`, `K T`]
      compile_store_abi_tuple_labels) >> simp[]) >>
  `cs_extends st mid` by suspend "slot_extends" >>
  metis_tac[cs_extends_trans, fn_has_code_split]
QED
Resume abi_encode_tuple_step_layout[slot_extends]:
  qpat_x_assum `compile_abi_tuple_slot _ _ _ _ _ _ = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[compile_abi_tuple_slot_def, comp_bind_def] >> pairarg_tac >>
  Cases_on `is_word_type ty` >> Cases_on `type_memory_bytes ce ty` >>
  simp[emit_op_def, emit_void_def, compile_copy_memory_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_var_def, fresh_id_def, emit_def] >> strip_tac >>
  gvs[emit_op_def, comp_bind_def, comp_return_def, fresh_var_def,
    fresh_id_def, emit_def, comp_ignore_bind_def] >>
  simp[cs_extends_def, IS_PREFIX_APPEND] >> qexists_tac `[]` >> simp[]
QED
Finalise abi_encode_tuple_step_layout

(* The entry is the physical endpoint of argument compilation and fresh
   tuple allocation. Live source footprints exclude the tuple destination;
   source capacity bounds justify reads independently of this separation. *)
Theorem abi_encode_tuple_staging_full:
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
    abi_tuple_input ce (EL i tys) (EL i tvs) (EL i vs) (EL i ops) s /\
    type_memory_bytes ce (EL i tys) < dimword(:256) /\
    (~is_word_type (EL i tys) ==> !w. eval_operand (EL i ops) s = SOME w ==>
      (val_footprint (EL i tvs) (EL i vs) = 0 \/
       loweringStateRelDefs$regions_disjoint (w2n bw) total (w2n w)
         (val_footprint (EL i tvs) (EL i vs))))) /\
  (!i x. i < LENGTH ops /\ EL i ops = Var x ==> not_fresh_at a x) /\
  (!i. i < LENGTH tys ==>
    if is_word_type (EL i tys) then op_taint tn (EL i ops) = {} else
    ?x w. EL i ops = Var x /\ lookup_var x s = SOME w /\
      ptr_covers G tn x s (type_memory_bytes ce (EL i tys)) /\
      w2n w + type_memory_bytes ce (EL i tys) < dimword(:256) /\
      (type_memory_bytes ce (EL i tys) = 0 \/
       w2n w + type_memory_bytes ce (EL i tys) <= s.vs_alloca_next) /\
      (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        val_in_memory (EL i tvs) (EL i vs) (w2n w) mem)) /\
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
  rename1 `ptr_covers G tn root s capacity` >>
  `!i. i < LENGTH tys ==>
    abi_tuple_input ce (EL i tys) (EL i tvs) (EL i vs) (EL i ops) s /\
    type_memory_size (EL i tvs) = type_memory_bytes ce (EL i tys) /\
    val_wf (EL i tvs) (EL i vs) /\
    (~is_word_type (EL i tys) ==> !w. eval_operand (EL i ops) s = SOME w ==>
      (val_footprint (EL i tvs) (EL i vs) = 0 \/
       loweringStateRelDefs$regions_disjoint (w2n bw) capacity (w2n w)
         (val_footprint (EL i tvs) (EL i vs))))` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!i. i < LENGTH tys ==> abi_tuple_input _ _ _ _ _ _ /\ _`
       (qspec_then `i` mp_tac) >>
     simp[] >> strip_tac >> gvs[abi_tuple_input_def]) >>
  qabbrev_tac `P = \done rest off st (t,g,u).
    done ++ rest = ZIP (ops,tys) /\
    off = SUM (MAP type_memory_size (TAKE (LENGTH done) tvs)) /\
    off = abi_tuple_bytes ce done /\
    compile_store_abi_tuple ce (Var root) off rest st = ((),b) /\
    cs_extends a st /\ a.cs_next_var <= st.cs_next_var /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,g,u)) /\
    (!i mem. i < LENGTH done /\ mem_agree_outside u.t_mem t.vs_memory mem ==>
      val_in_memory (EL i tvs) (EL i vs)
        (w2n bw + SUM (MAP type_memory_size (TAKE i tvs))) mem) /\
    lookup_var root t = SOME bw /\ ptr_covers g u root t capacity /\
    local_ptrs_rel func ce es.scopes t /\
    (!name z k. local_region ce es.scopes t name z k <=>
      local_region ce es.scopes s name z k) /\
    (!D. ghost_inv_at D lo d ce cx es G tn s ==>
      ghost_inv_at D lo d ce cx es g u t) /\
    (ghost_kept_at lo ce es origin G0 tn0 s0 G tn ==>
      ghost_kept_at lo ce es origin G0 tn0 s0 g u) /\
    ~t.vs_halted /\ t.vs_current_bb = st.cs_current_bb /\
    t.vs_inst_idx = LENGTH st.cs_current_insts /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!code. abi_alloca_history code s ==> abi_alloca_history code t) /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!j. ~(w2n bw <= j /\ j < w2n bw + capacity) ==>
      mem_bytes_at j 1 t.vs_memory = mem_bytes_at j 1 s.vs_memory /\
      (j IN u.t_mem <=> j IN tn.t_mem)) /\
    (!x. not_fresh_at a x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP g x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    (!oldop. (!x. oldop = Var x ==> not_fresh_at a x) ==>
      eval_operand oldop t = eval_operand oldop s /\
      op_taint u oldop = op_taint tn oldop /\ op_prov g oldop = op_prov G oldop)` >>
  `P [] (ZIP (ops,tys)) 0 a (s,G,tn)` by suspend "initial" >>
  `!done rest off st mid r op ty.
    compile_abi_tuple_slot ce (Var root) off op ty st = ((),mid) /\
    P done ((op,ty)::rest) off st r ==>
    ?z. P (done ++ [(op,ty)]) rest (off + type_memory_bytes ce ty) mid z`
    by suspend "step" >>
  `?z. (\aa rr bb zz. T) a (s,G,tn) b z /\
      P ([] ++ ZIP (ops,tys)) []
      (0 + abi_tuple_bytes ce (ZIP (ops,tys))) b z` by
    (irule abi_encode_owned_tuple_stage >> simp[] >> metis_tac[]) >>
  suspend "assemble"
QED

Resume abi_encode_tuple_staging_full[initial]:
  simp[Abbr `P`, abi_tuple_bytes_def, cs_extends_def] >>
  conj_tac
  >- (gen_tac >> irule (cj 1 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >> simp[]) >>
  qpat_x_assum `ptr_covers G tn root s capacity` mp_tac >>
  asm_rewrite_tac[abi_tuple_bytes_def]
QED
Resume abi_encode_tuple_staging_full[step]:
  rpt gen_tac >> PairCases_on `r` >>
  simp[Abbr `P`] >> strip_tac >>
  `LENGTH done < LENGTH tys /\
   EL (LENGTH done) ops = op /\ EL (LENGTH done) tys = ty` by
    (`LENGTH done + SUC (LENGTH rest) = LENGTH tys` by
       (qpat_x_assum `_ = ZIP (ops,tys)` (mp_tac o Q.AP_TERM `LENGTH`) >>
        simp[]) >>
     `LENGTH done < LENGTH tys` by decide_tac >>
     `EL (LENGTH done) (ZIP (ops,tys)) = (op,ty)` by
       (qpat_x_assum `_ = ZIP (ops,tys)` (fn th => rewrite_tac[GSYM th]) >>
        simp[EL_APPEND_EQN]) >>
     qpat_x_assum `EL _ (ZIP _) = _` mp_tac >> simp[EL_ZIP]) >>
  `off + type_memory_bytes ce ty <= capacity` by
    (qpat_x_assum `_ = ZIP (ops,tys)` (mp_tac o Q.AP_TERM `abi_tuple_bytes ce`) >>
     simp[abi_tuple_bytes_def, MAP_APPEND, SUM_APPEND] >>
     qpat_x_assum `off = abi_tuple_bytes ce done` mp_tac >>
     qpat_x_assum `capacity = abi_tuple_bytes ce _` mp_tac >>
     simp[abi_tuple_bytes_def] >> decide_tac) >>
  drule_all abi_encode_tuple_step_layout >> strip_tac >>
  `abi_tuple_input ce ty (EL (LENGTH done) tvs) (EL (LENGTH done) vs) op s /\
   type_memory_size (EL (LENGTH done) tvs) = type_memory_bytes ce ty /\
   val_wf (EL (LENGTH done) tvs) (EL (LENGTH done) vs) /\
   (~is_word_type ty ==> !w. eval_operand op s = SOME w ==>
     (val_footprint (EL (LENGTH done) tvs) (EL (LENGTH done) vs) = 0 \/
      loweringStateRelDefs$regions_disjoint (w2n bw) capacity (w2n w)
        (val_footprint (EL (LENGTH done) tvs) (EL (LENGTH done) vs))))` by
    (qpat_x_assum `!i. i < LENGTH tys ==> abi_tuple_input _ _ _ _ _ _ /\ type_memory_size _ = _ /\ _`
       (qspec_then `LENGTH done` mp_tac) >> simp[] >> metis_tac[]) >>
  `!x. op = Var x ==> not_fresh_at a x` by
    (rpt strip_tac >> qpat_x_assum `!i x. _ ==> not_fresh_at a x` irule >>
     qexists_tac `LENGTH done` >> simp[]) >>
  `abi_tuple_input ce ty (EL (LENGTH done) tvs) (EL (LENGTH done) vs) op r0 /\
   (if is_word_type ty then op_taint r2 op = {} else
     ?x w. op = Var x /\ lookup_var x r0 = SOME w /\
       ptr_covers r1 r2 x r0 (type_memory_bytes ce ty) /\
       w2n w + type_memory_bytes ce ty < dimword(:256) /\
       (type_memory_bytes ce ty = 0 \/
        w2n w + type_memory_bytes ce ty <= r0.vs_alloca_next) /\
       (!mem. mem_agree_outside r2.t_mem r0.vs_memory mem ==>
         val_in_memory (EL (LENGTH done) tvs) (EL (LENGTH done) vs) (w2n w) mem))` by
    (irule abi_encode_tuple_head_resource >>
     qexistsl_tac [`G`, `w2n bw`, `capacity`, `off`, `s`, `tn`] >> simp[] >>
     conj_tac >- metis_tac[] >>
     qpat_x_assum `!i. i < LENGTH tys ==> if _ then _ else _`
       (qspec_then `LENGTH done` mp_tac) >> simp[]) >>
  `st.cs_next_var <= mid.cs_next_var` by
    (drule abi_tuple_encode_slot_shape >> simp[]) >>
  `!x. not_fresh_at a x ==> not_fresh_at st x` by
    (qpat_x_assum `a.cs_next_var <= st.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `allocas_from lo r0 /\ lo <= r0.vs_alloca_next /\
   w2n bw + off < dimword(:256) /\
   w2n bw + off + type_memory_bytes ce ty < dimword(:256) /\
   lo <= w2n bw + off /\
   (type_memory_bytes ce ty = 0 \/
    w2n bw + off + type_memory_bytes ce ty <= r0.vs_alloca_next)` by
    (simp[allocas_from_def] >>
     qpat_x_assum `allocas_from lo s` mp_tac >>
     simp[allocas_from_def] >> decide_tac) >>
  `(!name z k. local_region ce es.scopes r0 name z k ==>
      regions_disjoint (w2n bw + off) (type_memory_bytes ce ty) z k) /\
   (!aid z k. FLOOKUP s0.vs_allocas aid = SOME (z,k) /\ aid < origin.cs_next_id ==>
      regions_disjoint (w2n bw + off) (type_memory_bytes ce ty) z k) /\
   (!name z k. local_region ce es.scopes s0 name z k ==>
      regions_disjoint (w2n bw + off) (type_memory_bytes ce ty) z k)` by
    (rpt conj_tac >> rpt gen_tac >> strip_tac >>
     `regions_disjoint (w2n bw) capacity z k` by metis_tac[] >>
     qpat_x_assum `regions_disjoint (w2n bw) capacity z k` mp_tac >>
     simp[regions_disjoint_def] >> decide_tac) >>
  `not_fresh_at st root /\ (!x. op = Var x ==> not_fresh_at st x) /\
   (!name x sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
   (!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at st x) /\
   (!x. not_fresh_at origin x ==> not_fresh_at st x)` by metis_tac[] >>
  `ptr_covers r1 r2 root r0 capacity` by
    (qpat_x_assum `capacity = _` (fn th => rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
  drule abi_encode_tuple_slot_origin >>
  disch_then (qspecl_then [`EL (LENGTH done) tvs`, `EL (LENGTH done) vs`] mp_tac) >>
  disch_then (drule_at (Pat `abi_tuple_input _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `lookup_var root r0 = SOME _`)) >>
  disch_then (drule_at (Pat `local_ptrs_rel _ _ _ r0`)) >>
  disch_then (qspecl_then [`bw`, `lo`, `explicit`, `ctx`, `PG`] mp_tac) >>
  disch_then (qspecl_then [`d`, `cx`, `origin`] mp_tac) >>
  disch_then (qspecl_then [`G0`, `tn0`, `s0`] mp_tac) >>
  (impl_tac >- suspend "slot_entry") >> strip_tac >>
  qexists_tac `(t,Gf,tnf)` >>
  suspend "slot_post"
QED
Resume abi_encode_tuple_staging_full[assemble]:
  PairCases_on `z` >>
  qpat_x_assum `P _ [] _ _ _` mp_tac >>
  simp[Abbr `P`] >> strip_tac >>
  `!mem. mem_agree_outside z2.t_mem z0.vs_memory mem ==>
    val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) (w2n bw) mem` by
    (rpt strip_tac >> simp[val_in_memory_tuple] >>
     irule tuple_in_memory_from_elements >> simp[] >>
     rpt strip_tac >> first_x_assum irule >> simp[]) >>
  qexistsl_tac [`z0`, `z1`, `z2`] >> asm_rewrite_tac[] >>
  qpat_x_assum `abi_tuple_bytes ce _ = _` (fn th => rewrite_tac[GSYM th]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  once_rewrite_tac[ADD_COMM] >> first_assum ACCEPT_TAC
QED
Resume abi_encode_tuple_staging_full[slot_entry]:
  markerLib.RESUME_TAC >> asm_rewrite_tac[]
QED
Resume abi_encode_tuple_staging_full[slot_post]:
  markerLib.RESUME_TAC >>
  CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
  asm_rewrite_tac[] >>
  (conj_tac >- suspend "offset_take" >>
  conj_tac >- (qpat_x_assum `off = abi_tuple_bytes ce done` mp_tac >>
    simp[abi_tuple_bytes_def, MAP_APPEND, SUM_APPEND]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- decide_tac >>
  conj_tac >- metis_tac[gas_origin_ptr_path_trans] >>
  conj_tac >- suspend "prefix_post" >>
  conj_tac >- metis_tac[] >>
  conj_tac >- suspend "coverage_post" >>
  conj_tac >- suspend "locals_post" >>
  conj_tac >- suspend "regions_post" >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- suspend "exterior_post" >>
  conj_tac >- metis_tac[] >>
  metis_tac[])
QED
Resume abi_encode_tuple_staging_full[offset_take]:
  markerLib.RESUME_TAC >>
  `LENGTH done < LENGTH tvs` by decide_tac >>
  `TAKE (LENGTH done + 1) tvs =
    SNOC (EL (LENGTH done) tvs) (TAKE (LENGTH done) tvs)` by
    metis_tac[TAKE_SUC_BY_TAKE, ADD1] >>
  asm_rewrite_tac[MAP_SNOC, SUM_SNOC]
QED
Resume abi_encode_tuple_staging_full[prefix_post]:
  markerLib.RESUME_TAC >>
  rewrite_tac[GSYM ADD1] >>
  once_rewrite_tac[ADD_COMM] >>
  ho_match_mp_tac (Q.INST [`mem` |-> `r0.vs_memory`, `tn` |-> `r2.t_mem`]
    abi_encode_tuple_prefix_extend) >>
  asm_rewrite_tac[] >>
  (conj_tac >- (rpt strip_tac >>
    `i < LENGTH tys` by decide_tac >>
    qpat_x_assum `!i. i < LENGTH tys ==> abi_tuple_input _ _ _ _ _ _ /\ type_memory_size _ = _ /\ _`
      (qspec_then `i` mp_tac) >> simp[]) >>
  conj_tac >- (rpt strip_tac >> once_rewrite_tac[ADD_COMM] >>
    first_x_assum irule >> asm_rewrite_tac[]) >>
  conj_tac >- (rpt strip_tac >>
    qpat_x_assum `!i. ~(_ <= i /\ _) ==> _` (qspec_then `j` mp_tac) >>
    qpat_x_assum `~(_ <= j /\ _)` mp_tac >>
    qpat_x_assum `off = SUM _` (fn th => pure_rewrite_tac[GSYM th]) >>
    metis_tac[]) >>
  rpt strip_tac >>
  qpat_x_assum `off = SUM _` (fn th => pure_rewrite_tac[GSYM th]) >>
  first_x_assum irule >> asm_rewrite_tac[])
QED
Resume abi_encode_tuple_staging_full[coverage_post]:
  markerLib.RESUME_TAC >>
  irule ptr_covers_lookup_frame >>
  qexistsl_tac [`r1`, `r0`, `r2`] >>
  metis_tac[]
QED
Resume abi_encode_tuple_staging_full[locals_post]:
  markerLib.RESUME_TAC >>
  irule (cj 1 abi_encode_tuple_local_frame) >>
  qexistsl_tac [`type_memory_bytes ce ty`, `w2n bw + off`, `r0`] >>
  asm_rewrite_tac[] >> metis_tac[]
QED
Resume abi_encode_tuple_staging_full[regions_post]:
  markerLib.RESUME_TAC >>
  `!name z k. local_region ce es.scopes t name z k <=>
    local_region ce es.scopes r0 name z k` by
    (ho_match_mp_tac (Q.INST [`func` |-> `func`,
       `n` |-> `type_memory_bytes ce ty`, `p` |-> `w2n (bw:256 word) + off`]
       (cj 2 abi_encode_tuple_local_frame)) >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  metis_tac[]
QED
Resume abi_encode_tuple_staging_full[exterior_post]:
  markerLib.RESUME_TAC >> gen_tac >> disch_tac >>
  `~(w2n bw + off <= j /\
      j < w2n bw + off + type_memory_bytes ce ty)` by
    (qpat_x_assum `capacity = _` mp_tac >> decide_tac) >>
  qpat_x_assum `!i. ~(_ <= i /\ _) ==> _`
    (qspec_then `j` mp_tac) >>
  qpat_x_assum `!j. ~(_ <= j) \/ _ ==> _`
    (qspec_then `j` mp_tac) >>
  asm_rewrite_tac[] >> metis_tac[]
QED
Finalise abi_encode_tuple_staging_full
