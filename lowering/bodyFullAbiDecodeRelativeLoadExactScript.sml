Theory bodyFullAbiDecodeRelativeLoadExact
Ancestors
  bodyFullGhostFrame bodyFullUnwrapRun assignTuplePtrLoadStep
  stateFrame compileEnv loweringStateRelDefs bodyFullAbiDecodeAge
  abiDecoderWordTyped externalEntryShape entryDecoderHistoryFrame
  allocaHistory freshWrites abiDecodePtrMemberFrame ptrDiscipline exprSimCopy bodyPtrDefs
  emitHelper codegenRel ptrSafeRun
  bodyLiteralBufferMemory fragExecMem instSeqPtrLo abiEncoder emitHelperProps
  abiDecodePtrRead fragGasSeqPtr fragGasOriginPtrLoop
  exprLoweringProps list rich_list venomExecSemantics venomInst words venomState

(* The address/load prefix reads only inside the supplied input frontier.
   This is a memory-safety boundary, independent of ghost horizons. *)
Theorem abi_decode_relative_load_mem_lower:
  compile_abi_dec_addr (Var src) pos sa = (addr,sb) /\
  emit_op MLOAD [addr] sb = (v,sc) /\
  lookup_var src s = SOME b /\ eval_operand pos s = SOME (n2w p) /\
  p+32 <= h /\ w2n b+h < dimword (:256) /\
  w2n b+h <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sc) s
Proof
  strip_tac >>
  `emit_op ADD [Var src;pos] sa = (addr,sb)` by
    gvs[compile_abi_dec_addr_def] >>
  drule emitted_insts_emit_op >> strip_tac >>
  qpat_assum `emit_op MLOAD _ _ = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  `emitted_insts sa sc = emitted_insts sa sb ++ emitted_insts sb sc` by
    (irule emitted_insts_append >> conj_tac >> asm_rewrite_tac[]) >>
  simp[run_inst_seq_mem_ok_def] >>
  conj_tac
  >- (irule instMemFrontierTheory.below_frontier_no_ranges >> simp[mk_inst_def]) >>
  `step_inst_base (mk_inst sa.cs_next_id ADD [Var src;pos]
    [STRING #"%" (toString sa.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var)) (b+n2w p) s)` by
    (irule step_ADD >> simp[eval_operand_def]) >>
  simp[] >>
  simp[instMemFrontierTheory.below_frontier_MLOAD, eval_operand_def,
       lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  conj_tac
  >- (`w2n (b+n2w p) = w2n b+p` by
        (irule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> decide_tac) >>
      decide_tac) >>
  BasicProvers.TOP_CASE_TAC >> simp[]
QED

(* These are finite instruction certificates, not a transport of the old
   expression judgment.  Deterministic instruction ghosts select one endpoint
   before the horizon-dependent dead masks are introduced. *)
Theorem abi_decode_relative_load_joint_lower:
  compile_abi_dec_addr (Var src) pos sa = (addr,sb) /\
  emit_op MLOAD [addr] sb = (v,sc) /\
  fn_has_code sa sc fn /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  abi_decode_ptr_window G tn s src b h /\
  eval_operand pos s = SOME (n2w p) /\ op_taint tn pos = {} /\
  p+32 <= h /\ w2n b+h < dimword (:256) /\
  w2n b+h <= s.vs_alloca_next /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  ?out t Gf tnf.
    v = Var out /\ not_fresh_at sc out /\
    run_inst_seq (emitted_insts sa sc) s =
      OK (t with vs_inst_idx := s.vs_inst_idx) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
       (s,G,tn) [] (OK t,Gf,tnf)) /\
    (!D. inst_seq_ptr D lo ctx fn PG G tn
       (emitted_insts sa sc) s Gf tnf) /\
    lookup_var out t = SOME (mload (w2n b+p) s) /\
    op_prov Gf v = NONE /\ op_taint tnf v = {} /\
    ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
    t.vs_inst_idx = LENGTH sc.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (fresh_vars_wrt sa s ==> fresh_vars_wrt sc t) /\
    (!x. not_fresh_at sa x ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  drule_all (abi_decode_ptr_relative_load |> Q.INST [`D` |-> `ARB`, `PG` |-> `PG`]) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`out`, `t`, `G'`, `tn'`] >>
  asm_rewrite_tac[] >>
  `!D. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sc) s G' tn'` by
    (gen_tac >>
     drule_all (abi_decode_ptr_relative_load |> Q.INST [`D` |-> `D`, `PG` |-> `PG`]) >>
     disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
     qpat_assum `inst_seq_ptr ARB _ _ _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac inst_seq_ptr_ghost_unique) >>
     disch_then drule >> simp[] >> strip_tac >> gvs[]) >>
  `!D. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sc) s G' tn'` by
    (gen_tac >> irule inst_seq_ptr_zero_to_lo >>
     simp[] >> qexists_tac `D` >> simp[]) >>
  `emit_op ADD [Var src;pos] sa = (addr,sb)` by
    gvs[compile_abi_dec_addr_def] >>
  `inst_extends sa sb /\ inst_extends sb sc` by
    metis_tac[inst_extends_emit_op] >>
  `inst_extends sa sc` by metis_tac[inst_extends_trans] >>
  `sc.cs_current_bb = sa.cs_current_bb` by
    gvs[inst_extends_def] >>
  drule emitted_insts_emit_op >> strip_tac >>
  qpat_assum `emit_op MLOAD _ _ = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  `emitted_insts sa sc = emitted_insts sa sb ++ emitted_insts sb sc` by
    (irule emitted_insts_append >> conj_tac >> asm_rewrite_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
       i.inst_opcode <> GAS) (emitted_insts sa sc)` by
    simp[mk_inst_def, is_terminator_def] >>
  `(ctx_has_dalloca ctx ==>
    !pre i post u. emitted_insts sa sc = pre ++ i::post /\
      run_inst_seq pre s = OK u ==> unitTransformDefs$dalloca_no_wrap i u)` by
    (rpt strip_tac >> irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
     `MEM i (emitted_insts sa sc)` by simp[MEM_APPEND] >>
     fs[MEM_APPEND, mk_inst_def] >> gvs[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sc) s` by
    (irule abi_decode_relative_load_mem_lower >>
     qexistsl_tac [`addr`, `b`, `h`, `p`, `pos`, `sb`, `src`, `v`] >>
     simp[] >> gvs[abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_def]) >>
  simp[] >> gen_tac >>
  qpat_x_assum `inst_seq_ptr ARB _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `!D. inst_seq_ptr D 0 _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `!D. inst_seq_ptr D lo _ _ _ _ _ _ _ _ _`
    (qspec_then `D` assume_tac) >>
  drule_all emitted_origin_ptr_path >>
  disch_then (qspec_then `explicit` mp_tac) >>
  `((t with vs_inst_idx := s.vs_inst_idx) with
       vs_inst_idx := LENGTH sc.cs_current_insts) = t` by
    simp[venom_state_component_equality] >>
  asm_rewrite_tac[]
QED

(* Load and clamp expose this concrete scalar frame.  Transport semantic
   and horizon ghosts together, without inspecting either gas judgment. *)
Theorem abi_decode_scalar_joint_frame_lower:
  state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
  local_ptrs_reserved ce sa /\ origin.cs_next_var <= sa.cs_next_var /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)) /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
  tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  (!H. V H ==> stmt_state_rel H ctx fn ce cx es s /\
    ghost_inv_at (DF H) lo delta ce cx es G tn s /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn) ==>
  (!H. V H ==> stmt_state_rel H ctx fn ce cx es t /\
    ghost_inv_at (DF H) lo delta ce cx es G' tn' t /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G' tn')
Proof
  strip_tac >>
  `t = (s with vs_inst_idx := t.vs_inst_idx) with vs_vars := t.vs_vars` by
    metis_tac[state_frame_eq_reconstruct] >>
  rpt strip_tac
  >- (irule stmt_state_rel_old_vars_frame_ptr >> metis_tac[])
  >- (irule ghost_inv_at_exterior_frame >>
      qexistsl_tac [`G`, `es`, `s`, `sa`, `tn`] >>
      qpat_x_assum `t = _` (fn th => once_rewrite_tac[th]) >>
      simp[lookup_var_def] >> metis_tac[lookup_var_def])
  >> irule ghost_kept_at_clean_suffix >> qexistsl_tac [`G`, `tn`] >>
  simp[] >> reverse conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  `not_fresh_at sa x` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  metis_tac[]
QED

(* Identical owned-state quotation to LeafCases. *)
val owned_decoder_state = ``\st s G tn.
  alloca_history fn s /\ lo <= s.vs_alloca_next /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  abi_decode_ptr_window G tn s input input_word (LENGTH input_bytes) /\
  mem_bytes_at (w2n input_word) (LENGTH input_bytes) s.vs_memory = input_bytes /\
  w2n input_word + LENGTH input_bytes <= s.vs_alloca_next /\
  FLOOKUP s.vs_allocas output_id = SOME (output_base,output_cap) /\
  lookup_var output s = SOME (n2w output_base) /\
  ptr_covers G tn output s output_cap /\
  output_base + output_cap < dimword (:256) /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
      aid < origin.cs_next_id ==> off+sz <= s.vs_alloca_next) /\
  (!name b sz. local_region ce es0.scopes s0 name b sz ==>
      b+sz <= s.vs_alloca_next) /\
  EVERY (\(aid,p,b,k,bytes).
    aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) /\
    lookup_var p s = SOME (n2w b) /\ ptr_covers G tn p s k /\
    op_taint tn (Var p) = {} /\ k = LENGTH bytes /\
    mem_bytes_at b k s.vs_memory = bytes /\ b+k <= s.vs_alloca_next) live /\
  EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) s.vs_memory = bytes) protected /\
  (!H. V H ==> stmt_state_rel H ctx fn ce cx es s /\
    ghost_inv_at (DF H) lo delta ce cx es G tn s /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn) /\
  (?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [output] /\ inst.inst_id = output_id) /\
  not_local_ptr ce es.scopes output /\ lo <= output_base /\
  (!name b k. local_region ce es.scopes s name b k ==>
    output_base+output_cap <= b \/ b+k <= output_base) /\
  output_id < st.cs_next_id /\ not_fresh_at st output /\
  origin.cs_next_var <= st.cs_next_var /\
  EVERY (\(aid,p,b,k,bytes). not_fresh_at st p) live``;

Theorem abi_decode_owned_scalar_frame_with_history_lower:
  alloca_history fn t /\
  (^owned_decoder_state) sa s G tn /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  not_fresh_at sa input /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
  (!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)) /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
  tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm ==>
  (^owned_decoder_state) sb t G' tn'
Proof
  strip_tac >>
  `t = (s with vs_inst_idx := t.vs_inst_idx) with vs_vars := t.vs_vars` by
    metis_tac[state_frame_eq_reconstruct] >>
  fs[] >>
  `!H. V H ==> stmt_state_rel H ctx fn ce cx es t /\
    ghost_inv_at (DF H) lo delta ce cx es G' tn' t /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G' tn'` by
    (ho_match_mp_tac abi_decode_scalar_joint_frame_lower >>
     simp[state_frame_def] >> metis_tac[]) >>
  `abi_decode_ptr_window G' tn' t input input_word (LENGTH input_bytes)` by
    (irule abi_decode_ptr_window_frame >> qexistsl_tac [`G`, `s`, `tn`] >> simp[]) >>
  `!p k. not_fresh_at sa p /\ ptr_covers G tn p s k ==>
     ptr_covers G' tn' p t k` by
    (simp[ptr_covers_def] >> metis_tac[]) >>
  `!name b k. local_region ce es.scopes t name b k <=>
      local_region ce es.scopes s name b k` by
    (rpt gen_tac >> irule exprSimCopyTheory.copy_buffer_local_region_frame >>
     qexists_tac `sa` >> simp[]) >>
  `not_fresh_at sb output` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `EVERY (\(aid,p,b,k,bytes). not_fresh_at sb p) live` by
    metis_tac[bodyFullAbiDecodeAgeTheory.abi_decode_live_age_mono] >>
  `EVERY (\(aid,p,b,k,bytes).
    aid < sb.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,k) /\
    lookup_var p t = SOME (n2w b) /\ ptr_covers G' tn' p t k /\
    op_taint tn' (Var p) = {} /\ k = LENGTH bytes /\
    mem_bytes_at b k t.vs_memory = bytes /\ b+k <= t.vs_alloca_next) live` by
    (fs[EVERY_MEM] >> qx_gen_tac `e` >> strip_tac >>
     PairCases_on `e` >> gvs[] >>
     qpat_x_assum `!e. MEM e live ==> (\(aid,p,b,k,bytes). not_fresh_at sa p) e`
       (qspec_then `(e0,e1,e2,e3,e4)` mp_tac) >>
     qpat_x_assum `!e. MEM e live ==> (\(aid,p,b,k,bytes). aid < sa.cs_next_id /\ _) e`
       (qspec_then `(e0,e1,e2,e3,e4)` mp_tac) >>
     simp[] >> rpt strip_tac >> gvs[] >>
     metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem abi_decode_no_alloca_endpoint_history_lower:
  fn_has_code sa sb fn /\ sb.cs_current_bb = sa.cs_current_bb /\
  isPREFIX sa.cs_current_insts sb.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb) /\
  alloca_history fn s /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  t.vs_allocas = s.vs_allocas ==> alloca_history fn t
Proof
  strip_tac >>
  drule_all entry_straight_line_code_slice >> strip_tac >>
  rewrite_tac[alloca_history_def] >> conj_tac
  >- metis_tac[alloca_history_def] >>
  rpt strip_tac >>
  rename1 `get_instruction bb2 k = SOME inst` >>
  `bb2 = bb` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `bb2 = bb` SUBST_ALL_TAC >>
  Cases_on `k < s.vs_inst_idx`
  >- metis_tac[alloca_history_def] >>
  `k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst` by
    (qpat_x_assum `get_instruction bb k = _` mp_tac >> rw[get_instruction_def]) >>
  `LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts +
     LENGTH (emitted_insts sa sb)` by
    gvs[emitted_insts_def, IS_PREFIX_APPEND] >>
  `k - s.vs_inst_idx + s.vs_inst_idx = k /\
   k - s.vs_inst_idx < LENGTH (emitted_insts sa sb)` by decide_tac >>
  `EL (k - s.vs_inst_idx) (DROP s.vs_inst_idx bb.bb_instructions) = inst` by
    (qspecl_then [`k - s.vs_inst_idx`, `s.vs_inst_idx`, `bb.bb_instructions`]
       mp_tac EL_DROP >> simp[]) >>
  `EL (k - s.vs_inst_idx) (emitted_insts sa sb) = inst` by
    (qpat_x_assum `EL _ (DROP _ _) = _` mp_tac >>
     asm_rewrite_tac[] >> simp[EL_APPEND_EQN]) >>
  `MEM inst (emitted_insts sa sb)` by metis_tac[EL_MEM] >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem abi_decode_owned_relative_load_exact:
  compile_abi_dec_addr (Var input) pos sa = (addr,sb) /\
  emit_op MLOAD [addr] sb = (v,sc) /\
  fn_has_code sa sc fn /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (^owned_decoder_state) sa s G tn /\
  not_fresh_at sa input /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  eval_operand pos s = SOME (n2w p) /\ op_taint tn pos = {} /\
  p+32 <= LENGTH input_bytes /\
  w2n input_word+LENGTH input_bytes < dimword (:256) /\
  allocas_from lo s ==>
  ?out t Gf tnf.
    v = Var out /\ not_fresh_at sc out /\
    (?u. run_inst_seq (emitted_insts sa sc) s = OK u /\
         t = u with vs_inst_idx := LENGTH sc.cs_current_insts) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
       (s,G,tn) [] (OK t,Gf,tnf)) /\
    eval_operand v t = SOME (mload (w2n input_word+p) s) /\
    op_prov Gf v = NONE /\ op_taint tnf v = {} /\
    ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
    t.vs_inst_idx = LENGTH sc.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
    tnf.t_mem = tn.t_mem /\
    (^owned_decoder_state) sc t Gf tnf /\
    (!x. not_fresh_at sa x ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `abi_decode_ptr_window G tn s input input_word (LENGTH input_bytes) /\
   lo <= s.vs_alloca_next /\
   w2n input_word+LENGTH input_bytes <= s.vs_alloca_next /\
   alloca_history fn s` by fs[] >>
  drule_all abi_decode_relative_load_joint_lower >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  `emit_op ADD [Var input;pos] sa = (addr,sb)` by
    gvs[compile_abi_dec_addr_def] >>
  qpat_assum `emit_op ADD _ _ = _`
    (strip_assume_tac o MATCH_MP loweringShapeRulesTheory.emit_op_facts) >>
  qpat_assum `emit_op MLOAD _ _ = _`
    (strip_assume_tac o MATCH_MP loweringShapeRulesTheory.emit_op_facts) >>
  `inst_extends sa sc` by metis_tac[inst_extends_trans, inst_extends_emit_op] >>
  `isPREFIX sa.cs_current_insts sc.cs_current_insts` by
    metis_tac[inst_extends_def, IS_PREFIX_APPEND] >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sc)` by
    (qpat_assum `emit_op MLOAD _ _ = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     qpat_assum `emit_op ADD _ _ = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     `emitted_insts sa sc = emitted_insts sa sb ++ emitted_insts sb sc` by
       (irule emitted_insts_append >> metis_tac[]) >> simp[mk_inst_def]) >>
  `alloca_history fn t` by
    (irule abi_decode_no_alloca_endpoint_history_lower >> metis_tac[]) >>
  `sa.cs_next_id <= sc.cs_next_id` by
    (qpat_assum `emit_op ADD _ _ = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     qpat_assum `emit_op MLOAD _ _ = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >> simp[]) >>
  `(^owned_decoder_state) sc t Gf tnf` by
    (irule abi_decode_owned_scalar_frame_with_history_lower >>
     conj_tac >- asm_rewrite_tac[] >>
     qexistsl_tac [`G`, `s`, `sa`, `tn`] >> asm_rewrite_tac[] >>
     simp[]) >>
  `t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels` by
    (qpat_assum `state_frame t = _` mp_tac >> simp[state_frame_def]) >>
  `eval_operand v t = SOME (mload (w2n input_word+p) s)` by
    (qpat_assum `v = Var out` (fn th => rewrite_tac[th]) >>
     rewrite_tac[eval_operand_def] >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`out`, `t`, `Gf`, `tnf`] >>
  qpat_x_assum `v = Var out` SUBST_ALL_TAC >>
  asm_rewrite_tac[] >>
  qexists_tac `t with vs_inst_idx := s.vs_inst_idx` >>
  simp[venom_state_component_equality]
QED
