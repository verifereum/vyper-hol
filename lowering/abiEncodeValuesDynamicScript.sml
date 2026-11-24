Theory abiEncodeValuesDynamic
Ancestors
  abiEncodeValuesPhases abiEncodeValuesSource abiEncoderWindow abiEncoderAdmissible
  abiEncoderWindowJointPhases abiEncoderWindowPhase
  abiEncoderRegisteredEffect abiEncoderWindowContract abiEncoderChildCode
  exprSimAbiEncodeExecFrame bodyFullAbiEncodeOriginFloor
  fragGasOriginPtrLoop fragExec freshWrites exprLoweringProps compileEnv loweringStateRelDefs
  assignTuplePtrCopyLen allocaSiteResource ptrDiscipline
  valueEncodingProps valueEncodingDefs venomState venomMemDefs
  words finite_map list arithmetic pred_set
  vyperABI vyperValue vyperTyping contractABI

(* Once the child has encoded its tail, the suffix writes only the head
   offset and the cursor. In particular it keeps the new tail readable. *)
Theorem abi_encode_values_dynamic_suffix_run:
  abi_encode_child_suffix (Var head) (Var cursor) offset len st = (out,en) /\
  fn_has_code st en func /\
  eval_operand (Var head) s = SOME (n2w head_addr) /\
  eval_operand (Var cursor) s = SOME (n2w slot) /\
  eval_operand offset s = SOME (n2w off) /\
  eval_operand len s = SOME (n2w (LENGTH bytes)) /\
  (!x. Var head = Var x \/ Var cursor = Var x \/ offset = Var x \/
       len = Var x ==> not_fresh_at st x) /\
  ptr_covers G tn head s 32 /\ ptr_covers G tn cursor s 32 /\
  op_taint tn offset = {} /\ op_taint tn len = {} /\
  FLOOKUP s.vs_allocas site = SOME (slot,32) /\
  head_addr + 32 <= s.vs_alloca_next /\ slot + 32 <= s.vs_alloca_next /\
  venomMemDefs$regions_disjoint (head_addr,32) (slot,32) /\
  venomMemDefs$regions_disjoint (tail,LENGTH bytes) (head_addr,32) /\
  venomMemDefs$regions_disjoint (tail,LENGTH bytes) (slot,32) /\
  mem_bytes_at tail (LENGTH bytes) s.vs_memory = bytes /\
  (!i. tail <= i /\ i < tail + LENGTH bytes ==> i NOTIN tn.t_mem) /\
  alloca_inv s /\ alloca_room ctx func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t G' tn'.
    run_inst_seq (emitted_insts st en) s = OK (t with vs_inst_idx := s.vs_inst_idx) /\
    mem_word_at head_addr t.vs_memory = n2w off /\
    mem_word_at slot t.vs_memory = n2w (off + LENGTH bytes) /\
    mem_bytes_at tail (LENGTH bytes) t.vs_memory = bytes /\
    (!i. (head_addr <= i /\ i < head_addr + 32) \/
         (slot <= i /\ i < slot + 32) \/
         (tail <= i /\ i < tail + LENGTH bytes) ==> i NOTIN tn'.t_mem) /\
    window_phase ctx func st en {site} [(head_addr,32)] s t /\
    abi_encode_exec_frame func s t /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem DIFF
      ({i | head_addr <= i /\ i < head_addr + 32} UNION
       {i | slot <= i /\ i < slot + 32}) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')
Proof
  strip_tac >>
  drule_all window_child_suffix_joint >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`t`,`G'`,`tn'`] strip_assume_tac)) >>
  `mem_bytes_at tail (LENGTH bytes) t.vs_memory = bytes` by
    (Cases_on `bytes = []` >- simp[mem_bytes_at_def] >>
     `0 < LENGTH (bytes:word8 list)` by simp[LENGTH_NON_NIL] >>
     qpat_assum `t.vs_memory = _` (fn th => PURE_REWRITE_TAC [th]) >>
     fs[venomMemDefsTheory.regions_disjoint_def] >>
     asm_simp_tac bool_ss [mstore_mem_bytes_at_disjoint]) >>
  qexistsl_tac [`t`,`G'`,`tn'`] >> asm_rewrite_tac[] >>
  simp[pred_setTheory.IN_DIFF, pred_setTheory.GSPECIFICATION] >> metis_tac[]
QED

Theorem abi_encode_values_dynamic_suffix:
  abi_encode_child_suffix (Var head) (Var cursor) offset len st = (out,en) /\
  fn_has_code st en func /\
  eval_operand (Var head) s = SOME (n2w head_addr) /\
  eval_operand (Var cursor) s = SOME (n2w slot) /\
  eval_operand offset s = SOME (n2w off) /\
  eval_operand len s = SOME (n2w (LENGTH bytes)) /\
  (!x. Var head = Var x \/ Var cursor = Var x \/ offset = Var x \/
       len = Var x ==> not_fresh_at st x) /\
  ptr_covers G tn head s 32 /\ ptr_covers G tn cursor s 32 /\
  op_taint tn offset = {} /\ op_taint tn len = {} /\
  FLOOKUP s.vs_allocas site = SOME (slot,32) /\
  head_addr + 32 <= s.vs_alloca_next /\ slot + 32 <= s.vs_alloca_next /\
  venomMemDefs$regions_disjoint (head_addr,32) (slot,32) /\
  venomMemDefs$regions_disjoint (tail,LENGTH bytes) (head_addr,32) /\
  venomMemDefs$regions_disjoint (tail,LENGTH bytes) (slot,32) /\
  mem_bytes_at tail (LENGTH bytes) s.vs_memory = bytes /\
  (!i. tail <= i /\ i < tail + LENGTH bytes ==> i NOTIN tn.t_mem) /\
  alloca_inv s /\ alloca_room ctx func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t G' tn'.
    mem_word_at head_addr t.vs_memory = n2w off /\
    mem_word_at slot t.vs_memory = n2w (off + LENGTH bytes) /\
    mem_bytes_at tail (LENGTH bytes) t.vs_memory = bytes /\
    (!i. (head_addr <= i /\ i < head_addr + 32) \/
         (slot <= i /\ i < slot + 32) \/
         (tail <= i /\ i < tail + LENGTH bytes) ==> i NOTIN tn'.t_mem) /\
    window_phase ctx func st en {site} [(head_addr,32)] s t /\
    abi_encode_exec_frame func s t /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem DIFF
      ({i | head_addr <= i /\ i < head_addr + 32} UNION
       {i | slot <= i /\ i < slot + 32}) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')
Proof
  strip_tac >> drule_all abi_encode_values_dynamic_suffix_run >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`t`,`G'`,`tn'`] strip_assume_tac)) >>
  qexistsl_tac [`t`,`G'`,`tn'`] >> asm_rewrite_tac[]
QED

Theorem abi_encode_dynamic_suffix_taint[local]:
  (i < h \/ h + 32 <= i) /\ (i < slot \/ slot + 32 <= i) ==>
  (i IN (m DIFF ({j | h <= j /\ j < h + 32} UNION
                 {j | slot <= j /\ j < slot + 32})) <=> i IN m)
Proof
  simp_tac (srw_ss()) [IN_DIFF] >>
  strip_tac >>
  `~(h <= i /\ i < h+32) /\ ~(slot <= i /\ i < slot+32)` by decide_tac >>
  metis_tac[]
QED

(* The source-window callback supplies an optional side post on its own
   terminal state. The post is independent of the horizon/dead set. *)
Definition abi_encode_values_source_side_def:
  abi_encode_values_source_side Side lo explicit ctx func PG <=>
  !dst src ei st out en bs sb cap s d G tn.
    compile_abi_encode_to_buf dst src ei st = (out,en) /\
    abi_encoder_admissible ei /\
    (?ct rv. enc ct rv = bs /\
      !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        abi_encoder_window_input ei ct rv sb cap mem) /\
    eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
    op_taint tn src = {} /\ op_taint tn dst = {} /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
    fn_has_code st en func /\ fn_inst_ids_distinct func /\
    alloca_inv s /\ alloca_room ctx func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
      s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
    (0 < cap ==> sb + cap <= s.vs_alloca_next /\
      venomMemDefs$regions_disjoint (sb,cap) (d,LENGTH bs) /\
      ?p. src = Var p /\ ptr_covers G tn p s cap) /\
    d + LENGTH bs <= s.vs_alloca_next /\
    (0 < LENGTH bs ==> ?p. dst = Var p /\ ptr_covers G tn p s (LENGTH bs)) /\
    (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id IN frag_ids st en /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
      sz = 32 /\ (0 < cap ==> venomMemDefs$regions_disjoint (sb,cap) (b,sz)) /\
      venomMemDefs$regions_disjoint (d,LENGTH bs) (b,sz)) /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?t G' tn'.
      mem_bytes_at d (LENGTH bs) t.vs_memory = bs /\
      eval_operand out t = SOME (n2w (LENGTH bs)) /\
      window_phase ctx func st en (window_alloca_sites func (frag_ids st en))
        [(d,LENGTH bs)] s t /\ abi_encode_exec_frame func s t /\
      op_taint tn' out = {} /\ (!x. out = Var x ==> not_fresh_at en x) /\
      (!i. d <= i /\ i < d + LENGTH bs ==> i NOTIN tn'.t_mem) /\
      (!x. not_fresh_at st x ==>
        FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
      (!i. (i < d \/ d + LENGTH bs <= i) /\
        (!id b sz. id IN window_alloca_sites func (frag_ids st en) /\
          FLOOKUP t.vs_allocas id = SOME (b,sz) ==> i < b \/ b + sz <= i) ==>
        (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
      tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
      Side st en s t
End

Theorem abi_encode_values_source_side_trivial:
  abi_encode_values_source_side (\a b s t. T) lo explicit ctx func PG
Proof
  simp_tac bool_ss [abi_encode_values_source_side_def] >>
  rpt gen_tac >> MATCH_ACCEPT_TAC abi_encode_values_source_window_input
QED

(* The suffix callback uses the normalized ordinary execution selected by
   window_child_suffix_joint. It does not choose a second successor. *)
Definition abi_encode_values_suffix_join_def:
  abi_encode_values_suffix_join Child Row func <=>
    !st mid en s u t head cursor off len out ids writes ctx.
      abi_encode_child_suffix head cursor off len mid = (out,en) /\
      fn_has_code mid en func /\ ci_mono st mid /\
      ~u.vs_halted /\ u.vs_current_bb = mid.cs_current_bb /\
      u.vs_inst_idx = LENGTH mid.cs_current_insts /\
      window_phase ctx func mid en ids writes u t /\
      run_inst_seq (emitted_insts mid en) u = OK (t with vs_inst_idx := u.vs_inst_idx) /\
      Child st mid s u ==> Row st en s t
End

Theorem abi_encode_values_suffix_join_trivial:
  abi_encode_values_suffix_join (\a b s t. T) (\a b s t. T) func
Proof
  simp[abi_encode_values_suffix_join_def]
QED

(* Encode from the materialized member without allocating a source tuple.
   The window input's ABI type and value need only encode to the same bytes. *)
Theorem abi_encode_values_dynamic_body_input_side:
  abi_encode_values_source_side Child lo explicit ctx func PG /\
  abi_encode_values_suffix_join Child Row func /\
  compile_abi_encode_to_buf (Var dest) src ei st = (len,mid) /\
  abi_encode_child_suffix (Var head) (Var cursor) offset len mid = (len,en) /\
  abi_encoder_admissible ei /\
  (?ct rv. enc ct rv = bs /\
    !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      abi_encoder_window_input ei ct rv sb cap mem) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand (Var dest) s = SOME (n2w tail) /\
  eval_operand (Var head) s = SOME (n2w head_addr) /\
  eval_operand (Var cursor) s = SOME (n2w slot) /\ eval_operand offset s = SOME (n2w off) /\
  op_taint tn src = {} /\ op_taint tn (Var dest) = {} /\ op_taint tn offset = {} /\
  (!x. src = Var x \/ Var dest = Var x \/ Var head = Var x \/
       Var cursor = Var x \/ offset = Var x ==> not_fresh_at st x) /\
  ptr_covers G tn head s 32 /\ ptr_covers G tn cursor s 32 /\
  ptr_covers G tn dest s (LENGTH bs) /\
  fn_has_code st mid func /\ fn_has_code mid en func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
  (0 < cap ==> sb + cap <= s.vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,cap) (tail,LENGTH bs) /\
    ?p. src = Var p /\ ptr_covers G tn p s cap) /\
  tail + LENGTH bs <= s.vs_alloca_next /\ head_addr + 32 <= s.vs_alloca_next /\
  slot + 32 <= s.vs_alloca_next /\ FLOOKUP s.vs_allocas site = SOME (slot,32) /\
  venomMemDefs$regions_disjoint (head_addr,32) (slot,32) /\
  venomMemDefs$regions_disjoint (tail,LENGTH bs) (head_addr,32) /\
  venomMemDefs$regions_disjoint (tail,LENGTH bs) (slot,32) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st mid /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ (0 < cap ==> venomMemDefs$regions_disjoint (sb,cap) (b,sz)) /\
    venomMemDefs$regions_disjoint (tail,LENGTH bs) (b,sz)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t G' tn'.
    mem_word_at head_addr t.vs_memory = n2w off /\
    mem_word_at slot t.vs_memory = n2w (off + LENGTH bs) /\
    mem_bytes_at tail (LENGTH bs) t.vs_memory = bs /\
    (!i. (head_addr <= i /\ i < head_addr + 32) \/
         (slot <= i /\ i < slot + 32) \/
         (tail <= i /\ i < tail + LENGTH bs) ==> i NOTIN tn'.t_mem) /\
    window_phase ctx func st en (site INSERT window_alloca_sites func (frag_ids st mid))
      [(head_addr,32);(tail,LENGTH bs)] s t /\ abi_encode_exec_frame func s t /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!i. (i < head_addr \/ head_addr + 32 <= i) /\ (i < tail \/ tail + LENGTH bs <= i) /\
      (!id b sz. id IN (site INSERT window_alloca_sites func (frag_ids st mid)) /\
        FLOOKUP t.vs_allocas id = SOME (b,sz) ==> i < b \/ b+sz <= i) ==>
      (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    Row st en s t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `(!x. src = Var x \/ Var dest = Var x ==> not_fresh_at st x) /\
   (0 < LENGTH bs ==> ?p. Var dest = Var p /\ ptr_covers G tn p s (LENGTH bs))` by metis_tac[] >>
  qpat_x_assum `abi_encode_values_source_side Child _ _ _ _ _`
    (mp_tac o Q.INST [`dst` |-> `Var dest`, `d` |-> `tail`, `en` |-> `mid`, `out` |-> `len`] o
     SPEC_ALL o REWRITE_RULE [abi_encode_values_source_side_def]) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
  disch_then (qx_choose_then `u` (qx_choose_then `Gu` (qx_choose_then `tu` strip_assume_tac))) >>
  `st.cs_next_var <= mid.cs_next_var` by
    metis_tac[ci_mono_def, cj 2 ci_mono_compile_abi_encode, pairTheory.SND] >>
  `not_fresh_at st head /\ not_fresh_at st cursor /\
    (!x. offset = Var x ==> not_fresh_at st x)` by metis_tac[] >>
  `(!x. Var head = Var x \/ Var cursor = Var x \/ offset = Var x \/
        len = Var x ==> not_fresh_at mid x)` by metis_tac[not_fresh_at_mono] >>
  `eval_operand (Var head) u = SOME (n2w head_addr) /\ ptr_covers Gu tu head u 32` by
    (irule abi_encode_values_pointer_frame >>
     qpat_assum `window_phase ctx func st mid _ _ s u` (irule_at Any) >>
     qexistsl_tac [`tn`,`G`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `eval_operand (Var cursor) u = SOME (n2w slot) /\ ptr_covers Gu tu cursor u 32` by
    (irule abi_encode_values_pointer_frame >>
     qpat_assum `window_phase ctx func st mid _ _ s u` (irule_at Any) >>
     qexistsl_tac [`tn`,`G`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `eval_operand offset u = SOME (n2w off) /\ op_taint tu offset = {}` by
    (conj_tac >- metis_tac[window_phase_operand] >>
     Cases_on `offset`
     >- simp_tac (srw_ss()) [op_taint_def]
     >- (qpat_assum `!x. not_fresh_at st x ==> FLOOKUP Gu x = _ /\ _`
           (qspec_then `s'` mp_tac) >>
         impl_tac >- metis_tac[] >>
         disch_then (fn th => PURE_ONCE_REWRITE_TAC [cj 2 th]) >>
         first_assum ACCEPT_TAC)
     >> simp_tac (srw_ss()) [op_taint_def]) >>
  drule window_phase_resources >> strip_tac >>
  drule window_phase_control >> strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by metis_tac[window_exec_frame_alloca_budget] >>
  `FLOOKUP u.vs_allocas site = SOME (slot,32)` by
    metis_tac[window_phase_effect, abi_encoder_registered_effect_allocated] >>
  `head_addr + 32 <= u.vs_alloca_next /\ slot + 32 <= u.vs_alloca_next` by
    (qpat_assum `window_alloca_growth s u`
       (assume_tac o CONJUNCT1 o REWRITE_RULE [window_alloca_growth_def]) >>
     decide_tac) >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by
    metis_tac[abi_encode_origin_path_allocas_from] >>
  mp_tac (Q.INST [`st` |-> `mid`, `s` |-> `u`, `G` |-> `Gu`, `tn` |-> `tu`,
    `bytes` |-> `bs`, `out` |-> `len`] abi_encode_values_dynamic_suffix_run) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `t` (qx_choose_then `G'` (qx_choose_then `tn'` strip_assume_tac))) >>
  `Row st en s t` by
    (`ci_mono st mid` by metis_tac[cj 2 ci_mono_compile_abi_encode, pairTheory.SND] >>
     qpat_x_assum `abi_encode_values_suffix_join _ _ _`
       (strip_assume_tac o REWRITE_RULE [abi_encode_values_suffix_join_def]) >>
     first_x_assum irule >> metis_tac[]) >>
  `window_phase ctx func st en (site INSERT window_alloca_sites func (frag_ids st mid))
    [(head_addr,32);(tail,LENGTH bs)] s t` by
    (irule window_phase_chain >>
     qexistsl_tac [`window_alloca_sites func (frag_ids st mid)`,`[(tail,LENGTH bs)]`,
                  `mid`,`{site}`,`[(head_addr,32)]`,`u`] >>
     simp[SUBSET_DEF] >> metis_tac[]) >>
  `!i. (i < head_addr \/ head_addr + 32 <= i) /\ (i < tail \/ tail + LENGTH bs <= i) /\
    (!id b sz. id IN (site INSERT window_alloca_sites func (frag_ids st mid)) /\
        FLOOKUP t.vs_allocas id = SOME (b,sz) ==> i < b \/ b+sz <= i) ==>
    (i IN tn'.t_mem <=> i IN tn.t_mem)` by
    (gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
     `!id b sz. id IN window_alloca_sites func (frag_ids st mid) /\
      FLOOKUP u.vs_allocas id = SOME (b,sz) ==> i < b \/ b+sz <= i` by
        metis_tac[window_phase_effect, abi_encoder_registered_effect_allocated, IN_INSERT] >>
     `i < slot \/ slot + 32 <= i` by
        metis_tac[window_phase_effect, abi_encoder_registered_effect_allocated, IN_INSERT] >>
     `i IN tu.t_mem <=> i IN tn.t_mem` by metis_tac[] >>
     `i IN tn'.t_mem <=> i IN tu.t_mem` by
       (qpat_assum `tn'.t_mem = _ DIFF _` (fn th =>
         PURE_REWRITE_TAC [th]) >>
        irule abi_encode_dynamic_suffix_taint >> asm_rewrite_tac[]) >>
     qpat_assum `i IN tn'.t_mem <=> i IN tu.t_mem` (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
     first_assum ACCEPT_TAC) >>
  qexistsl_tac [`t`,`G'`,`tn'`] >> asm_rewrite_tac[] >>
  rpt conj_tac >> metis_tac[abi_encode_exec_frame_trans, not_fresh_at_mono, gas_origin_ptr_path_trans]
QED

Theorem abi_encode_values_dynamic_body_input:
  compile_abi_encode_to_buf (Var dest) src ei st = (len,mid) /\
  abi_encode_child_suffix (Var head) (Var cursor) offset len mid = (len,en) /\
  abi_encoder_admissible ei /\
  (?ct rv. enc ct rv = bs /\
    !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      abi_encoder_window_input ei ct rv sb cap mem) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand (Var dest) s = SOME (n2w tail) /\
  eval_operand (Var head) s = SOME (n2w head_addr) /\
  eval_operand (Var cursor) s = SOME (n2w slot) /\ eval_operand offset s = SOME (n2w off) /\
  op_taint tn src = {} /\ op_taint tn (Var dest) = {} /\ op_taint tn offset = {} /\
  (!x. src = Var x \/ Var dest = Var x \/ Var head = Var x \/
       Var cursor = Var x \/ offset = Var x ==> not_fresh_at st x) /\
  ptr_covers G tn head s 32 /\ ptr_covers G tn cursor s 32 /\
  ptr_covers G tn dest s (LENGTH bs) /\
  fn_has_code st mid func /\ fn_has_code mid en func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
  (0 < cap ==> sb + cap <= s.vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,cap) (tail,LENGTH bs) /\
    ?p. src = Var p /\ ptr_covers G tn p s cap) /\
  tail + LENGTH bs <= s.vs_alloca_next /\ head_addr + 32 <= s.vs_alloca_next /\
  slot + 32 <= s.vs_alloca_next /\ FLOOKUP s.vs_allocas site = SOME (slot,32) /\
  venomMemDefs$regions_disjoint (head_addr,32) (slot,32) /\
  venomMemDefs$regions_disjoint (tail,LENGTH bs) (head_addr,32) /\
  venomMemDefs$regions_disjoint (tail,LENGTH bs) (slot,32) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st mid /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ (0 < cap ==> venomMemDefs$regions_disjoint (sb,cap) (b,sz)) /\
    venomMemDefs$regions_disjoint (tail,LENGTH bs) (b,sz)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t G' tn'.
    mem_word_at head_addr t.vs_memory = n2w off /\
    mem_word_at slot t.vs_memory = n2w (off + LENGTH bs) /\
    mem_bytes_at tail (LENGTH bs) t.vs_memory = bs /\
    (!i. (head_addr <= i /\ i < head_addr + 32) \/
         (slot <= i /\ i < slot + 32) \/
         (tail <= i /\ i < tail + LENGTH bs) ==> i NOTIN tn'.t_mem) /\
    window_phase ctx func st en (site INSERT window_alloca_sites func (frag_ids st mid))
      [(head_addr,32);(tail,LENGTH bs)] s t /\ abi_encode_exec_frame func s t /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!i. (i < head_addr \/ head_addr + 32 <= i) /\ (i < tail \/ tail + LENGTH bs <= i) /\
      (!id b sz. id IN (site INSERT window_alloca_sites func (frag_ids st mid)) /\
        FLOOKUP t.vs_allocas id = SOME (b,sz) ==> i < b \/ b+sz <= i) ==>
      (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')
Proof
  MATCH_ACCEPT_TAC (SIMP_RULE bool_ss
    [abi_encode_values_source_side_trivial, abi_encode_values_suffix_join_def]
    (Q.INST [`Child` |-> `\a b s t. T`, `Row` |-> `\a b s t. T`]
      abi_encode_values_dynamic_body_input_side))
QED

Theorem abi_encode_values_dynamic_body:
  compile_abi_encode_to_buf (Var dest) src ei st = (len,mid) /\
  abi_encode_child_suffix (Var head) (Var cursor) offset len mid = (len,en) /\
  abi_enc_plan env ty ei /\ evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v sb mem) /\
  bs = enc (vyper_to_abi_type env ty) av /\ cap = val_footprint tv v /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand (Var dest) s = SOME (n2w tail) /\
  eval_operand (Var head) s = SOME (n2w head_addr) /\
  eval_operand (Var cursor) s = SOME (n2w slot) /\ eval_operand offset s = SOME (n2w off) /\
  op_taint tn src = {} /\ op_taint tn (Var dest) = {} /\ op_taint tn offset = {} /\
  (!x. src = Var x \/ Var dest = Var x \/ Var head = Var x \/
       Var cursor = Var x \/ offset = Var x ==> not_fresh_at st x) /\
  ptr_covers G tn head s 32 /\ ptr_covers G tn cursor s 32 /\
  ptr_covers G tn dest s (LENGTH bs) /\
  fn_has_code st mid func /\ fn_has_code mid en func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
  (0 < cap ==> sb + cap <= s.vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,cap) (tail,LENGTH bs) /\
    ?p. src = Var p /\ ptr_covers G tn p s cap) /\
  tail + LENGTH bs <= s.vs_alloca_next /\ head_addr + 32 <= s.vs_alloca_next /\
  slot + 32 <= s.vs_alloca_next /\ FLOOKUP s.vs_allocas site = SOME (slot,32) /\
  venomMemDefs$regions_disjoint (head_addr,32) (slot,32) /\
  venomMemDefs$regions_disjoint (tail,LENGTH bs) (head_addr,32) /\
  venomMemDefs$regions_disjoint (tail,LENGTH bs) (slot,32) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st mid /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ (0 < cap ==> venomMemDefs$regions_disjoint (sb,cap) (b,sz)) /\
    venomMemDefs$regions_disjoint (tail,LENGTH bs) (b,sz)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t G' tn'.
    mem_word_at head_addr t.vs_memory = n2w off /\
    mem_word_at slot t.vs_memory = n2w (off + LENGTH bs) /\
    mem_bytes_at tail (LENGTH bs) t.vs_memory = bs /\
    (!i. (head_addr <= i /\ i < head_addr + 32) \/
         (slot <= i /\ i < slot + 32) \/
         (tail <= i /\ i < tail + LENGTH bs) ==> i NOTIN tn'.t_mem) /\
    window_phase ctx func st en (site INSERT window_alloca_sites func (frag_ids st mid))
      [(head_addr,32);(tail,LENGTH bs)] s t /\ abi_encode_exec_frame func s t /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!i. (i < head_addr \/ head_addr + 32 <= i) /\ (i < tail \/ tail + LENGTH bs <= i) /\
      (!id b sz. id IN (site INSERT window_alloca_sites func (frag_ids st mid)) /\
        FLOOKUP t.vs_allocas id = SOME (b,sz) ==> i < b \/ b+sz <= i) ==>
      (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_values_plan_window_input >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  mp_tac abi_encode_values_dynamic_body_input >>
  impl_tac >-
    (qpat_x_assum `bs = _` SUBST_ALL_TAC >>
     qpat_x_assum `cap = _` SUBST_ALL_TAC >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED
