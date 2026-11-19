(* Nonempty external-call packing: the tuple is already staged in memory. *)
Theory bodyFullExtCallEncodeTail
Ancestors
  abiEncoderWindowJoint abiEncoderSourceRobust abiEncoderSourceInvoke
  abiEncoderWindowContract abiEncoderRegisteredEffect abiEncoderCounters
  entryDecodeStructure reasonCopySourcePtr assignTuplePtrCopyLen
  exprSimAbiEncodeExecFrame exprSimAbiEncodeSemantic exprSimAbiEncodeStateTransport
  exprSimAbiEncodeSiteResources
  abiEncoderProps abiAllocationHistory bodyFullAttributeAdd bodyFullPathHistory
  allocaHistory localPtrsProps allocaSiteResource memoryReadProps
  fragGasOriginPtrLoop fragGasOriginPtr loweringShapeRules loweringShapeDefs
  exprLoweringProps fragExec logAbiPrefixPtr
  bodyPtrDefs ptrDiscipline ptrSafeRun compileEnv emitHelper
  venomInst venomState venomMemDefs contractABI valueEncoding vyperABI
  words arithmetic list pred_set finite_map

(* Arithmetic changes only the result variable and the instruction index. *)
Theorem extcall_tail_add[local]:
  !k p. emit_op ADD [left; Lit (n2w k)] a = (out,b) /\ fn_has_code a b func /\
  eval_operand left s = SOME (n2w p) /\ op_taint tn left = {} /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  !G PG. ?q t G' tn'. out = Var q /\ not_fresh_at b q /\
    lookup_var q t = SOME (n2w (p + k)) /\ op_taint tn' out = {} /\
    FLOOKUP G' q = op_prov G left /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_memory = s.vs_memory /\ t.vs_labels = s.vs_labels /\
    abi_encode_exec_frame func s t /\
    (!ids outs. abi_encoder_registered_effect ids outs s t) /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at a x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> drule emit_op_facts >> strip_tac >>
  `out' = STRING #"%" (toString a.cs_next_var)` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_var_def, fresh_id_def, emit_def] >>
  qabbrev_tac `inst = mk_inst a.cs_next_id ADD [left; Lit (n2w k)] [out']` >>
  qabbrev_tac `u = update_var out' (n2w (p + k)) s` >>
  qabbrev_tac `v = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G1 = step_prov PG G inst u` >>
  qabbrev_tac `tn1 = step_taint inst s u tn` >>
  `out = Var out' /\
   (!D l explicit. allocas_from l s ==>
      gas_origin_ptr_path (D,l,explicit,ctx,func,PG) (s,G,tn) []
        (OK v,G1,tn1)) /\
   FLOOKUP G1 out' = op_prov G left /\ op_taint tn1 out = {} /\
   tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
   tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
   (!x. x <> out' ==> FLOOKUP G1 x = FLOOKUP G x /\
     op_taint tn1 (Var x) = op_taint tn (Var x))` by
    (irule attribute_add_full_frame >>
     simp[Abbr `inst`, Abbr `u`, Abbr `v`, Abbr `G1`, Abbr `tn1`, word_add_n2w] >>
     qexists_tac `n2w k` >> simp[word_add_n2w] >>
     qexistsl [`a`, `b`] >> simp[]) >>
  qexistsl [`out'`, `v`, `G1`, `tn1`] >>
  simp[Abbr `v`, Abbr `u`, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       abi_encode_exec_frame_def, abi_encode_semantic_obs_def,
       pending_alloca_size_def, abi_encoder_registered_effect_def] >>
  rpt strip_tac >> metis_tac[]
QED

(* Compiler IDs distinguish reused encoder slots from the two registered buffers. *)
Theorem extcall_encoder_reused_window[local]:
  compile_abi_encode_to_buf dst src ei a = (out,b) /\
  cs_extends a b /\ fn_has_code a b fn /\ fn_inst_ids_distinct fn /\
  (!i w r sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
    i.inst_id IN frag_ids a b /\ i.inst_operands = [Lit w] /\
    FLOOKUP s.vs_allocas i.inst_id = SOME (r,sz) ==> sz = w2n w) /\
  alloca_inv s /\
  FLOOKUP s.vs_allocas shared = SOME (p,capacity) /\
  FLOOKUP s.vs_allocas source = SOME (q,source_capacity) /\
  shared < a.cs_next_id /\ source < a.cs_next_id /\
  32 + n <= capacity /\ cap <= source_capacity ==>
  !inst r sz.
    MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids a b /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (r,sz) ==>
    sz = 32 /\
    (0 < cap ==> venomMemDefs$regions_disjoint (q,cap) (r,sz)) /\
    venomMemDefs$regions_disjoint (p+32,n) (r,sz)
Proof
  rpt strip_tac
  >- (`inst.inst_operands = [Lit 32w]` by
        (irule abi_encode_caller_body_literal >>
         metis_tac[abi_encode_frag_code_members,
                   venomInstIdsPropsTheory.fn_inst_ids_distinct_all_distinct]) >>
      first_x_assum (qspecl_then [`inst`, `32w`, `r`, `sz`] mp_tac) >>
      simp[dimword_def])
  >- (`source <> inst.inst_id` by fs[frag_ids_def] >>
      `venomMemDefs$regions_disjoint (q,source_capacity) (r,sz)` by
        metis_tac[alloca_site_registered_disjoint] >>
      fs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac)
  >- (`shared <> inst.inst_id` by fs[frag_ids_def] >>
      `venomMemDefs$regions_disjoint (p,capacity) (r,sz)` by
        metis_tac[alloca_site_registered_disjoint] >>
      fs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac)
QED

Theorem extcall_encoder_selector_frame[local]:
  window_strong_result ctx fn a b out at av (p+32) s t /\
  shared < a.cs_next_id /\ 32 <= capacity /\
  FLOOKUP s.vs_allocas shared = SOME (p,capacity) ==>
  (!id r sz. id IN window_alloca_sites fn (frag_ids a b) /\
    FLOOKUP t.vs_allocas id = SOME (r,sz) ==>
    venomMemDefs$regions_disjoint (p+28,4) (r,sz)) /\
  read_memory (p+28) 4 t = read_memory (p+28) 4 s
Proof
  strip_tac >> drule window_strong_result_effect >> strip_tac >>
  `alloca_inv t` by
    metis_tac[window_strong_result_public, abi_encoder_window_result_resources] >>
  `FLOOKUP t.vs_allocas shared = SOME (p,capacity)` by
    metis_tac[abi_encoder_registered_effect_allocated] >>
  conj_asm1_tac
  >- (rpt strip_tac >>
      `shared <> id` by fs[window_alloca_sites_def, frag_ids_def] >>
      `venomMemDefs$regions_disjoint (p,capacity) (r,sz)` by
        metis_tac[alloca_site_registered_disjoint] >>
      fs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  simp[read_memory_eq_mem_bytes_at] >>
  irule abi_encoder_window_effect_bytes >>
  goal_assum (drule_at Any) >>
  qexists_tac `[(p+32,LENGTH (contractABI$enc at av))]` >>
  simp[venomMemDefsTheory.regions_disjoint_def]
QED

(* The registered shared buffer protects the selector at the same endpoint
   that the encoder returns the actual payload length. *)
Theorem extcall_encoder_window[local]:
  compile_abi_encode_to_buf (Var dst) (Var src) ei a = (alen,b) /\
  cs_extends a b /\ fn_has_code a b fn /\ fn_inst_ids_distinct fn /\
  (!i w r sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
    i.inst_id IN frag_ids a b /\ i.inst_operands = [Lit w] /\
    FLOOKUP s.vs_allocas i.inst_id = SOME (r,sz) ==> sz = w2n w) /\
  alloca_inv s /\ alloca_room ctx fn s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  FLOOKUP s.vs_allocas shared = SOME (p,capacity) /\
  FLOOKUP s.vs_allocas source = SOME (q,source_capacity) /\
  shared <> source /\ shared < a.cs_next_id /\ source < a.cs_next_id /\
  32 + LENGTH (contractABI$enc at av) <= capacity /\ cap <= source_capacity /\
  lookup_var src s = SOME (n2w q) /\ lookup_var dst s = SOME (n2w (p+32)) /\
  not_fresh_at a src /\ not_fresh_at a dst /\
  ptr_covers G tn src s cap /\ ptr_covers G tn dst s (LENGTH (contractABI$enc at av)) /\
  abi_encoder_admissible ei /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     abi_encoder_window_input ei at av q cap mem) /\
  (!i. p+28 <= i /\ i < p+32 ==> i NOTIN tn.t_mem) ==>
  ?t G' tn'.
    window_strong_result ctx fn a b alen at av (p+32) s t /\
    abi_encode_exec_frame fn s t /\
    op_taint tn' alen = {} /\
    (!x. alen = Var x ==> not_fresh_at b x) /\
    (!x. not_fresh_at a x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,G',tn')) /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\
    (!i. (i < p+32 \/ p+32 + LENGTH (contractABI$enc at av) <= i) /\
         (!id r sz. id IN window_alloca_sites fn (frag_ids a b) /\
           FLOOKUP t.vs_allocas id = SOME (r,sz) ==> i < r \/ r+sz <= i) ==>
         (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    read_memory (p+28) (4 + LENGTH (contractABI$enc at av)) t =
      read_memory (p+28) 4 s ++ contractABI$enc at av /\
    (!i. p+28 <= i /\ i < p+32 + LENGTH (contractABI$enc at av) ==> i NOTIN tn'.t_mem)
Proof
  strip_tac >>
  `p + capacity <= s.vs_alloca_next /\ q + source_capacity <= s.vs_alloca_next` by
    metis_tac[alloca_site_registered_below] >>
  `venomMemDefs$regions_disjoint (q,cap) (p+32,LENGTH (contractABI$enc at av))` by
    (`venomMemDefs$regions_disjoint (q,source_capacity) (p,capacity)` by
       metis_tac[alloca_site_registered_disjoint] >>
     fs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `q+cap <= s.vs_alloca_next /\ p+32+LENGTH (contractABI$enc at av) <= s.vs_alloca_next` by
    decide_tac >>
  `!inst r sz. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
     inst.inst_id IN frag_ids a b /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (r,sz) ==>
     sz = 32 /\ (0 < cap ==> venomMemDefs$regions_disjoint (q,cap) (r,sz)) /\
     venomMemDefs$regions_disjoint (p+32,LENGTH (contractABI$enc at av)) (r,sz)` by
    (match_mp_tac (GEN_ALL extcall_encoder_reused_window) >>
     goal_assum (drule_at (Pat `FLOOKUP s.vs_allocas _ = SOME (p,_)`)) >>
     goal_assum (drule_at (Pat `FLOOKUP s.vs_allocas _ = SOME (q,_)`)) >>
     metis_tac[]) >>
  `eval_operand (Var dst) s = SOME (n2w (p+32)) /\
   eval_operand (Var src) s = SOME (n2w q) /\
   op_taint tn (Var src) = {} /\ op_taint tn (Var dst) = {}` by
    (simp[eval_operand_def] >>
     rpt conj_tac >> qpat_assum `ptr_covers G tn _ s _` (K ALL_TAC) >>
     metis_tac[ptr_covers_def]) >>
  `!x. Var src = Var x \/ Var dst = Var x ==> not_fresh_at a x` by
    (simp[] >> (metis_tac[])) >>
  `(0 < cap ==> q + cap <= s.vs_alloca_next /\
     venomMemDefs$regions_disjoint (q,cap) (p+32,LENGTH (contractABI$enc at av)) /\
     ?x. Var src = Var x /\ ptr_covers G tn x s cap) /\
   (0 < LENGTH (contractABI$enc at av) ==> ?x. Var dst = Var x /\
     ptr_covers G tn x s (LENGTH (contractABI$enc at av)))` by metis_tac[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp` by simp[] >>
  drule_all compile_abi_encode_to_buf_window_joint >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  `32 <= capacity` by decide_tac >>
  drule_all extcall_encoder_selector_frame >> strip_tac >>
  drule window_strong_result_public >> strip_tac >>
  drule abi_encoder_window_result_output >> strip_tac >>
  drule_then (strip_assume_tac o PURE_REWRITE_RULE [window_alloca_growth_def])
    window_strong_result_growth >>
  drule window_strong_result_effect >> strip_tac >>
  qexistsl [`t`, `G'`, `tn'`] >>
  asm_rewrite_tac[] >>
  conj_tac
  >- (rewrite_tac[allocas_from_def] >> rpt strip_tac >>
      Cases_on `FLOOKUP s.vs_allocas aid`
      >- (`s.vs_alloca_next <= b'` by metis_tac[] >> decide_tac) >>
      `x = (b',sz)` by metis_tac[abi_encoder_registered_effect_allocated, optionTheory.SOME_11] >>
      metis_tac[allocas_from_def]) >>
  conj_tac >- decide_tac >>
  conj_tac
  >- (once_rewrite_tac[read_memory_split] >>
      simp[read_memory_eq_mem_bytes_at, ADD_ASSOC]) >>
  rpt strip_tac >> Cases_on `p+32 <= i`
  >- metis_tac[] >>
  `!id r sz. id IN window_alloca_sites fn (frag_ids a b) /\
     FLOOKUP t.vs_allocas id = SOME (r,sz) ==> i < r \/ r+sz <= i` by
    (rpt strip_tac >>
     `sz = 32` by metis_tac[window_strong_result_sizes] >>
     `venomMemDefs$regions_disjoint (p+28,4) (r,sz)` by metis_tac[] >>
     qpat_x_assum `venomMemDefs$regions_disjoint (p+28,4) _` mp_tac >>
     rewrite_tac[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `i < p+32` by decide_tac >>
  metis_tac[]
QED

(* A covered offset within the shared buffer, before or after encoding. *)
Theorem extcall_tail_offset[local]:
  emit_op ADD [Var root;Lit (n2w k)] a = (dst,b) /\
  fn_has_code a b fn /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  lookup_var root s = SOME (n2w p) /\
  ptr_covers G tn root s capacity /\ k+n <= capacity /\
  p+k < dimword (:256) ==>
  !explicit PG. ?x t G' tn'. dst = Var x /\
    lookup_var x t = SOME (n2w (p+k)) /\ ptr_covers G' tn' x t n /\
    not_fresh_at b x /\ a.cs_next_var <= b.cs_next_var /\
    a.cs_next_id <= b.cs_next_id /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_memory = s.vs_memory /\ t.vs_labels = s.vs_labels /\
    abi_encode_exec_frame fn s t /\
    (!ids outs. abi_encoder_registered_effect ids outs s t) /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!y. not_fresh_at a y ==>
      lookup_var y t = lookup_var y s /\ FLOOKUP G' y = FLOOKUP G y /\
      op_taint tn' (Var y) = op_taint tn (Var y))
Proof
  strip_tac >>
  rpt gen_tac >>
  `eval_operand (Var root) s = SOME (n2w p) /\ op_taint tn (Var root) = {}` by
    (rewrite_tac[eval_operand_def] >> metis_tac[ptr_covers_def]) >>
  drule_all extcall_tail_add >>
  disch_then (qspecl_then [`G`, `PG`] (qx_choose_then `x` (qx_choose_then `t`
    (qx_choose_then `G'` (qx_choose_then `tn'` strip_assume_tac))))) >>
  drule emit_op_facts >> strip_tac >>
  `a.cs_next_id <= b.cs_next_id` by
    (drule emit_op_next_id >> decide_tac) >>
  `ptr_covers G tn root s (k+n)` by metis_tac[ptr_covers_mono] >>
  `p < dimword (:256)` by decide_tac >>
  `w2n (n2w p : 256 word) = p` by simp[w2n_n2w, LESS_MOD] >>
  `FLOOKUP G' x = FLOOKUP G root` by gs[op_prov_def] >>
  `ptr_covers G' tn' x t n` by
    (irule ptr_covers_offset_transport >>
     conj_tac >- metis_tac[] >>
     qexistsl [`G`, `k`, `root`, `s`, `tn`, `n2w p`] >>
     asm_rewrite_tac[word_add_n2w]) >>
  `out = x` by metis_tac[operand_11] >>
  qexistsl [`x`, `t`, `G'`, `tn'`] >> asm_rewrite_tac[] >> decide_tac
QED

(* The typed tuple is in the registered source allocation at offset zero.
   The byte count below is the actual encoding length, not its capacity. *)
Theorem extcall_packed_tuple_tail_local_sizes:
  emit_op ADD [Var root;Lit 32w] a = (dst,b) /\
  compile_abi_encode_to_buf dst (Var src) ei b = (alen,c) /\
  emit_op ADD [alen;Lit 4w] c = (len,d) /\
  emit_op ADD [Var root;Lit 28w] d = (off,e) /\
  fn_has_code a b fn /\ fn_has_code b c fn /\ cs_extends b c /\
  fn_has_code c d fn /\ fn_has_code d e fn /\ fn_inst_ids_distinct fn /\
  (!i w r sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
    i.inst_id IN frag_ids b c /\ i.inst_operands = [Lit w] /\
    FLOOKUP s.vs_allocas i.inst_id = SOME (r,sz) ==> sz = w2n w) /\
  alloca_inv s /\ alloca_room ctx fn s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  FLOOKUP s.vs_allocas shared = SOME (p,capacity) /\
  FLOOKUP s.vs_allocas source = SOME (q,source_capacity) /\
  shared <> source /\ shared < a.cs_next_id /\ source < a.cs_next_id /\
  lookup_var root s = SOME (n2w p) /\ lookup_var src s = SOME (n2w q) /\
  not_fresh_at a root /\ not_fresh_at a src /\
  ptr_covers G tn root s capacity /\ ptr_covers G tn src s (val_footprint tv v) /\
  val_footprint tv v <= source_capacity /\
  abi_enc_plan env ty ei /\ evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v q mem) /\
  32 + vyper_abi_size_bound env ty <= capacity /\
  bytes = contractABI$enc (vyper_to_abi_type env ty) av /\
  read_memory (p+28) 4 s = selector /\
  (!i. p+28 <= i /\ i < p+32 ==> i NOTIN tn.t_mem) ==>
  !explicit PG. ?x y t G' tn'.
    off = Var x /\ len = Var y /\ not_fresh_at e x /\ not_fresh_at e y /\
    lookup_var x t = SOME (n2w (p+28)) /\
    lookup_var y t = SOME (n2w (4 + LENGTH bytes)) /\ op_taint tn' len = {} /\
    ptr_covers G' tn' x t (4 + LENGTH bytes) /\ ptr_covers G' tn' root t capacity /\
    4 + LENGTH bytes < dimword (:256) /\ p+28 < dimword (:256) /\
    read_memory (p+28) (4 + LENGTH bytes) t = selector ++ bytes /\
    (!i. p+28 <= i /\ i < p+32 + LENGTH bytes ==> i NOTIN tn'.t_mem) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,G',tn')) /\
    ~t.vs_halted /\ t.vs_current_bb = e.cs_current_bb /\
    t.vs_inst_idx = LENGTH e.cs_current_insts /\ t.vs_labels = s.vs_labels /\
    alloca_inv t /\ alloca_room ctx fn t /\ allocas_from lo t /\ lo <= t.vs_alloca_next /\
    abi_encode_exec_frame fn s t /\
    abi_encoder_registered_effect (window_alloca_sites fn (frag_ids b c))
      [(p+32,LENGTH bytes)] s t /\
    (!i. (i < p+32 \/ p+32 + LENGTH bytes <= i) /\
         (!id r sz. id IN window_alloca_sites fn (frag_ids b c) /\
           FLOOKUP t.vs_allocas id = SOME (r,sz) ==> i < r \/ r+sz <= i) ==>
         (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!z. not_fresh_at a z ==>
         FLOOKUP G' z = FLOOKUP G z /\ op_taint tn' (Var z) = op_taint tn (Var z) /\
         (!w. lookup_var z s = SOME w ==> lookup_var z t = SOME w))
Proof
  strip_tac >> rpt gen_tac >>
  drule_all abi_encoder_source_window_robust >>
  disch_then (qx_choose_then `ct` (qx_choose_then `rv` strip_assume_tac)) >>
  `contractABI$enc ct rv = bytes` by metis_tac[] >>
  `32 + LENGTH (contractABI$enc ct rv) <= capacity` by decide_tac >>
  `p + capacity <= s.vs_alloca_next` by metis_tac[alloca_site_registered_below] >>
  `s.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  `p+32 < dimword (:256)` by decide_tac >>
  drule_all extcall_tail_offset >>
  disch_then (qspecl_then [`explicit`, `PG`]
    (qx_choose_then `dest` (qx_choose_then `s1`
      (qx_choose_then `G1` (qx_choose_then `tn1` strip_assume_tac))))) >>
  `!i w r sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
    i.inst_id IN frag_ids b c /\ i.inst_operands = [Lit w] /\
    FLOOKUP s1.vs_allocas i.inst_id = SOME (r,sz) ==> sz = w2n w` by
    (qpat_assum `!i w r sz. _ ==> sz = w2n w` mp_tac >> asm_rewrite_tac[]) >>
  `alloca_room ctx fn s1` by metis_tac[alloca_room_fields] >>
  `alloca_inv s1 /\ allocas_from lo s1` by
    ((qpat_assum `alloca_inv s` mp_tac >> qpat_assum `allocas_from lo s` mp_tac >>
     asm_rewrite_tac[alloca_inv_def, allocas_non_overlapping_def,
                     alloca_next_valid_def, allocas_from_def] >> (metis_tac[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def, allocas_from_def]))) >>
  `shared < b.cs_next_id /\ source < b.cs_next_id` by decide_tac >>
  `not_fresh_at b src` by metis_tac[not_fresh_at_mono] >>
  `lookup_var src s1 = SOME (n2w q) /\
   FLOOKUP G1 src = FLOOKUP G src /\ op_taint tn1 (Var src) = op_taint tn (Var src)` by
    metis_tac[] >>
  `ptr_covers G1 tn1 src s1 (val_footprint tv v)` by
    metis_tac[ptr_covers_lookup_frame] >>
  `abi_encoder_admissible ei` by metis_tac[abi_enc_plan_admissible] >>
  `!mem. mem_agree_outside tn1.t_mem s1.vs_memory mem ==>
     abi_encoder_window_input ei ct rv q (val_footprint tv v) mem` by asm_rewrite_tac[] >>
  `FLOOKUP s1.vs_allocas shared = SOME (p,capacity) /\
   FLOOKUP s1.vs_allocas source = SOME (q,source_capacity) /\ lo <= s1.vs_alloca_next /\
   (!i. p+28 <= i /\ i < p+32 ==> i NOTIN tn1.t_mem) /\
   compile_abi_encode_to_buf (Var dest) (Var src) ei b = (alen,c)` by
    (asm_rewrite_tac[] >> metis_tac[]) >>
  drule_all extcall_encoder_window >>
  disch_then (qspecl_then [`explicit`, `PG`]
    (qx_choose_then `s2` (qx_choose_then `G2` (qx_choose_then `tn2` strip_assume_tac)))) >>
  suspend "finish_adds"
QED

Resume extcall_packed_tuple_tail_local_sizes[finish_adds]:
  drule window_strong_result_public >> strip_tac >>
  drule abi_encoder_window_result_control >> strip_tac >>
  drule abi_encoder_window_result_output >> strip_tac >>
  drule abi_encoder_window_result_resources >> strip_tac >>
  drule window_strong_result_labels >> strip_tac >>
  drule window_strong_result_effect >> strip_tac >>
  `eval_operand alen s2 = SOME (n2w (LENGTH bytes))` by metis_tac[] >>
  `c.cs_next_var <= d.cs_next_var` by
    (qpat_assum `emit_op ADD _ c = _` (mp_then Any mp_tac emit_op_facts) >>
     strip_tac >> decide_tac) >>
  `b.cs_next_var <= c.cs_next_var` by metis_tac[abi_encoder_counters] >>
  `a.cs_next_var <= c.cs_next_var /\ a.cs_next_var <= d.cs_next_var` by decide_tac >>
  `not_fresh_at b root /\ not_fresh_at c root /\ not_fresh_at d root` by
    metis_tac[not_fresh_at_mono] >>
  `!z. not_fresh_at a z ==>
        FLOOKUP G2 z = FLOOKUP G z /\ op_taint tn2 (Var z) = op_taint tn (Var z) /\
        (!w. lookup_var z s = SOME w ==> lookup_var z s2 = SOME w)` by
    (rpt strip_tac >>
     `not_fresh_at b z` by metis_tac[not_fresh_at_mono] >>
     metis_tac[abi_encoder_window_result_vars]) >>
  `lookup_var root s2 = SOME (n2w p) /\ FLOOKUP G2 root = FLOOKUP G root /\
   op_taint tn2 (Var root) = op_taint tn (Var root)` by metis_tac[] >>
  `ptr_covers G2 tn2 root s2 capacity` by metis_tac[ptr_covers_lookup_frame] >>
  drule_all (Q.SPEC `4` extcall_tail_add) >>
  disch_then (qspecl_then [`G2`, `PG`]
    (qx_choose_then `y` (qx_choose_then `s3`
      (qx_choose_then `G3` (qx_choose_then `tn3` strip_assume_tac))))) >>
  `lookup_var root s3 = lookup_var root s2 /\
   FLOOKUP G3 root = FLOOKUP G2 root /\ op_taint tn3 (Var root) = op_taint tn2 (Var root)` by
    (qpat_assum `!z. not_fresh_at c z ==> lookup_var z s3 = _ /\ _` (qspec_then `root` mp_tac) >>
     metis_tac[]) >>
  `ptr_covers G3 tn3 root s3 capacity` by metis_tac[ptr_covers_lookup_frame] >>
  `lookup_var root s3 = SOME (n2w p)` by metis_tac[] >>
  `allocas_from lo s3` by
    (qpat_assum `allocas_from lo s2` (mp_tac o REWRITE_RULE [allocas_from_def]) >>
     asm_rewrite_tac[allocas_from_def]) >>
  `32 + LENGTH bytes <= capacity` by metis_tac[] >>
  `28 + (4 + LENGTH bytes) <= capacity /\ p+28 < dimword (:256) /\
   4 + LENGTH bytes < dimword (:256)` by decide_tac >>
  qpat_x_assum `emit_op ADD _ a = _` kall_tac >>
  drule_all extcall_tail_offset >>
  disch_then (qspecl_then [`explicit`, `PG`]
    (qx_choose_then `x` (qx_choose_then `s4`
      (qx_choose_then `G4` (qx_choose_then `tn4` strip_assume_tac))))) >>
  suspend "compose_tail"
QED

Resume extcall_packed_tuple_tail_local_sizes[compose_tail]:
  `not_fresh_at e y` by metis_tac[not_fresh_at_mono] >>
  `ptr_covers G4 tn4 root s4 capacity` by
    (qpat_assum `!z. not_fresh_at d z ==> lookup_var z s4 = _ /\ _`
       (qspec_then `root` strip_assume_tac) >>
     metis_tac[ptr_covers_lookup_frame]) >>
  `alloca_inv s4 /\ alloca_room ctx fn s4` by
    metis_tac[alloca_inv_fields, alloca_room_fields] >>
  `allocas_from lo s4` by
    (qpat_assum `allocas_from lo s2` (mp_tac o REWRITE_RULE [allocas_from_def]) >>
     asm_rewrite_tac[allocas_from_def]) >>
  `abi_encode_exec_frame fn s s4` by metis_tac[abi_encode_exec_frame_trans] >>
  `abi_encoder_registered_effect (window_alloca_sites fn (frag_ids b c))
     [(p+32,LENGTH bytes)] s s4` by metis_tac[abi_encoder_registered_effect_trans] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK s4,G4,tn4)` by
    metis_tac[gas_origin_ptr_path_append, APPEND] >>
  `lookup_var y s4 = SOME (n2w (4 + LENGTH bytes)) /\ op_taint tn4 len = {}` by
    (qpat_assum `!z. not_fresh_at d z ==> lookup_var z s4 = _ /\ _`
       (qspec_then `y` strip_assume_tac) >>
     metis_tac[ADD_COMM]) >>
  `read_memory (p+28) (4 + LENGTH bytes) s4 = selector ++ bytes` by
    (qpat_assum `read_memory _ _ s2 = _`
       (mp_tac o REWRITE_RULE [read_memory_eq_mem_bytes_at]) >>
     qpat_assum `read_memory _ _ s = _`
       (mp_tac o REWRITE_RULE [read_memory_eq_mem_bytes_at]) >>
     asm_rewrite_tac[read_memory_eq_mem_bytes_at] >> metis_tac[]) >>
  qexistsl [`x`, `y`, `s4`, `G4`, `tn4`] >>
  asm_rewrite_tac[] >>
  rpt conj_tac
  >- (qpat_assum `!i. p+28 <= i /\ i < p+32 + LENGTH (contractABI$enc ct rv) ==> _` mp_tac >>
      asm_rewrite_tac[] >> metis_tac[])
  >- (qpat_assum `!i. (_ \/ _) /\ _ ==> (i IN tn2.t_mem <=> _)` mp_tac >>
      asm_rewrite_tac[] >> metis_tac[]) >>
  rpt strip_tac >>
  `not_fresh_at c z /\ not_fresh_at d z` by metis_tac[not_fresh_at_mono] >>
  metis_tac[]
QED

Finalise extcall_packed_tuple_tail_local_sizes

(* Inverse history is one way to provide the encoder's local size facts. *)
Theorem extcall_packed_tuple_tail:
  emit_op ADD [Var root;Lit 32w] a = (dst,b) /\
  compile_abi_encode_to_buf dst (Var src) ei b = (alen,c) /\
  emit_op ADD [alen;Lit 4w] c = (len,d) /\
  emit_op ADD [Var root;Lit 28w] d = (off,e) /\
  fn_has_code a b fn /\ fn_has_code b c fn /\ cs_extends b c /\
  fn_has_code c d fn /\ fn_has_code d e fn /\ fn_inst_ids_distinct fn /\
  abi_alloca_history (fn_insts fn) s /\ alloca_inv s /\ alloca_room ctx fn s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  FLOOKUP s.vs_allocas shared = SOME (p,capacity) /\
  FLOOKUP s.vs_allocas source = SOME (q,source_capacity) /\
  shared <> source /\ shared < a.cs_next_id /\ source < a.cs_next_id /\
  lookup_var root s = SOME (n2w p) /\ lookup_var src s = SOME (n2w q) /\
  not_fresh_at a root /\ not_fresh_at a src /\
  ptr_covers G tn root s capacity /\ ptr_covers G tn src s (val_footprint tv v) /\
  val_footprint tv v <= source_capacity /\
  abi_enc_plan env ty ei /\ evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v q mem) /\
  32 + vyper_abi_size_bound env ty <= capacity /\
  bytes = contractABI$enc (vyper_to_abi_type env ty) av /\
  read_memory (p+28) 4 s = selector /\
  (!i. p+28 <= i /\ i < p+32 ==> i NOTIN tn.t_mem) ==>
  !explicit PG. ?x y t G' tn'.
    off = Var x /\ len = Var y /\ not_fresh_at e x /\ not_fresh_at e y /\
    lookup_var x t = SOME (n2w (p+28)) /\
    lookup_var y t = SOME (n2w (4 + LENGTH bytes)) /\ op_taint tn' len = {} /\
    ptr_covers G' tn' x t (4 + LENGTH bytes) /\ ptr_covers G' tn' root t capacity /\
    4 + LENGTH bytes < dimword (:256) /\ p+28 < dimword (:256) /\
    read_memory (p+28) (4 + LENGTH bytes) t = selector ++ bytes /\
    (!i. p+28 <= i /\ i < p+32 + LENGTH bytes ==> i NOTIN tn'.t_mem) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,G',tn')) /\
    ~t.vs_halted /\ t.vs_current_bb = e.cs_current_bb /\
    t.vs_inst_idx = LENGTH e.cs_current_insts /\ t.vs_labels = s.vs_labels /\
    alloca_inv t /\ alloca_room ctx fn t /\ allocas_from lo t /\ lo <= t.vs_alloca_next /\
    abi_encode_exec_frame fn s t /\
    abi_encoder_registered_effect (window_alloca_sites fn (frag_ids b c))
      [(p+32,LENGTH bytes)] s t /\
    (!i. (i < p+32 \/ p+32 + LENGTH bytes <= i) /\
         (!id r sz. id IN window_alloca_sites fn (frag_ids b c) /\
           FLOOKUP t.vs_allocas id = SOME (r,sz) ==> i < r \/ r+sz <= i) ==>
         (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!z. not_fresh_at a z ==>
         FLOOKUP G' z = FLOOKUP G z /\ op_taint tn' (Var z) = op_taint tn (Var z) /\
         (!w. lookup_var z s = SOME w ==> lookup_var z t = SOME w))
Proof
  strip_tac >>
  `!i w r sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
    i.inst_id IN frag_ids b c /\ i.inst_operands = [Lit w] /\
    FLOOKUP s.vs_allocas i.inst_id = SOME (r,sz) ==> sz = w2n w` by
    (rpt strip_tac >> drule_all abi_alloca_history_function_size >> simp[]) >>
  drule_all extcall_packed_tuple_tail_local_sizes >> simp[]
QED
