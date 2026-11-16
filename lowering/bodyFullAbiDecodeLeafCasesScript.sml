Theory bodyFullAbiDecodeLeafCases
Ancestors
  bodyFullGhostFrame bodyFullUnwrapRun assignTuplePtrLoadStep
  stateFrame compileEnv loweringStateRelDefs bodyFullAbiDecodeAge
  abiDecoderWordTyped exprSimAbiDecodeChildBounds externalEntryShape
  entryDecoderHistoryFrame abiDecodeClampShape
  allocaHistory freshWrites abiDecodePtrMemberFrame ptrDiscipline exprSimCopy bodyPtrDefs
  bodyFullAbiDecodeOutputOwnership bodyFullAbiDecodeCopyFrame
  bodyFullAbiDecodeDecoderFrame bodyFullAbiDecodeMotiveProbe
  bodyFullAbiDecodeStoreContents typedCopyOriginPtrDynArray
  emitHelper codegenRel ptrSafeRun
  bodyLiteralBufferMemory fragExecMem instSeqPtrLo abiEncoder emitHelperProps
  abiDecodePtrRead fragGasSeqPtr fragGasOriginPtrLoop
  exprLoweringProps list rich_list venomExecSemantics venomInst words venomState

(* The address/load prefix reads only inside the supplied input frontier.
   This is a memory-safety boundary, independent of ghost horizons. *)
Theorem abi_decode_relative_load_mem[local]:
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
Theorem abi_decode_relative_load_joint[local]:
  compile_abi_dec_addr (Var src) pos sa = (addr,sb) /\
  emit_op MLOAD [addr] sb = (v,sc) /\
  fn_has_code sa sc fn /\ ~ctx_has_dalloca ctx /\
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
  `run_inst_seq_mem_ok (emitted_insts sa sc) s` by
    (irule abi_decode_relative_load_mem >>
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
Theorem abi_decode_scalar_joint_frame:
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

(* NEW owned interface: the original MotiveProbe quotations are unchanged. *)
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

Theorem abi_decode_owned_scalar_frame_with_history:
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
    (ho_match_mp_tac abi_decode_scalar_joint_frame >>
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

val owned_decoder_pre = ``\start finish dst src opc base_op hi d write_start size s G tn.
  opc = MLOAD /\ fn_has_code start finish fn /\ fn_inst_ids_distinct fn /\
  ~ctx_has_dalloca ctx /\ local_ptrs_reserved ce start /\ (?H. V H) /\
  w2n input_word+LENGTH input_bytes < dimword (:256) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\
  eval_operand dst s = SOME (n2w d) /\
  (?p. dst = Var p /\ ptr_covers G tn p s (write_start-d+size) /\
       FLOOKUP G p = SOME (output_base,output_cap)) /\
  base_op = Var input /\
  (?off h. eval_operand src s = SOME (n2w off) /\
     eval_operand hi s = SOME (n2w h) /\ off <= h /\ h <= LENGTH input_bytes) /\
  op_prov G src = NONE /\ op_prov G hi = NONE /\
  op_taint tn dst = {} /\ op_taint tn src = {} /\
  op_taint tn base_op = {} /\ op_taint tn hi = {} /\
  abi_decoder_operand_live start.cs_next_var dst /\
  abi_decoder_operand_live start.cs_next_var src /\
  abi_decoder_operand_live start.cs_next_var base_op /\
  abi_decoder_operand_live start.cs_next_var hi /\
  output_base <= d /\ d <= write_start /\ write_start+size <= output_base+output_cap /\
  (w2n input_word+LENGTH input_bytes <= write_start \/
    write_start+size <= w2n input_word) /\
  EVERY (\(aid,p,b,k,bytes). aid < start.cs_next_id /\
    (b+k <= write_start \/ write_start+size <= b)) live /\
  EVERY (\(a,bytes). a+LENGTH bytes <= write_start \/ write_start+size <= a) protected /\
  (^owned_decoder_state) start s G tn``;

val owned_decoder_post = ``\start finish s G tn.
  ?r G' tn'.
    (!H. V H ==> gas_origin_ptr_path
      (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (r,G',tn')) /\
    ((?t. r = OK t /\ ~t.vs_halted /\
       t.vs_current_bb = finish.cs_current_bb /\
       t.vs_inst_idx = LENGTH finish.cs_current_insts /\
       (^owned_decoder_state) finish t G' tn' /\
       (!x. not_fresh_at start x ==>
         lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x))) \/
     (?t. r = Abort Revert_abort t))``;

val owned_to_buf_motive = ``\dst src opc base_op hi info.
  !env sf ty tv live protected start finish s G tn d.
    abi_decoder_coherent ce env sf ty tv /\
    info = type_to_abi_dec_info sf ce ty /\
    (?off h. eval_operand src s = SOME (n2w off) /\
       eval_operand hi s = SOME (n2w h) /\
       off + abi_member_head_size (vyper_to_abi_type env ty) <= h /\
       h <= LENGTH input_bytes) /\
    compile_abi_decode_to_buf dst src opc base_op hi info start = ((),finish) /\
    (^owned_decoder_pre) start finish dst src opc base_op hi d d
      (type_memory_size tv) s G tn ==>
    (^owned_decoder_post) start finish s G tn``;

(* Exact universal finite clamp boundary; no runtime-success assumption. *)
val clamp_boundary = ``!value clamp sa sb fn ctx s w G tn lo explicit PG.
  compile_abi_clamp_basetype value clamp sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand value s = SOME w /\ op_prov G value = NONE /\
  op_taint tn value = {} /\ abi_decoder_operand_live sa.cs_next_var value /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  ?r Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (r,Gf,tnf)) /\
    ((?t. r = Abort Revert_abort t) \/
     (?t. r = OK t /\ ~t.vs_halted /\
       t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts /\
       eval_operand value t = SOME w /\
       op_prov Gf value = NONE /\ op_taint tnf value = {} /\
       t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
       state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
       tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
       tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
       (!x. not_fresh_at sa x ==>
          lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
          op_taint tnf (Var x) = op_taint tn (Var x))))``;

Theorem abi_decode_no_alloca_endpoint_history:
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

Theorem abi_decode_owned_relative_load:
  compile_abi_dec_addr (Var input) pos sa = (addr,sb) /\
  emit_op MLOAD [addr] sb = (v,sc) /\
  fn_has_code sa sc fn /\ ~ctx_has_dalloca ctx /\
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
  drule_all abi_decode_relative_load_joint >>
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
    (irule abi_decode_no_alloca_endpoint_history >> metis_tac[]) >>
  `sa.cs_next_id <= sc.cs_next_id` by
    (qpat_assum `emit_op ADD _ _ = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     qpat_assum `emit_op MLOAD _ _ = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >> simp[]) >>
  `(^owned_decoder_state) sc t Gf tnf` by
    (irule abi_decode_owned_scalar_frame_with_history >>
     conj_tac >- asm_rewrite_tac[] >>
     qexistsl_tac [`G`, `s`, `sa`, `tn`] >> asm_rewrite_tac[] >>
     simp[]) >>
  `t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels` by
    (qpat_assum `state_frame t = _` mp_tac >> simp[state_frame_def]) >>
  qexistsl_tac [`out`, `t`, `Gf`, `tnf`] >>
  asm_rewrite_tac[] >> simp[eval_operand_def] >>
  metis_tac[operand_11, arithmeticTheory.ADD_COMM]
QED

Theorem abi_decode_owned_clamp_conditional[local]:
  (^clamp_boundary) ==>
  compile_abi_clamp_basetype value clamp sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand value s = SOME w /\ op_prov G value = NONE /\
  op_taint tn value = {} /\ abi_decoder_operand_live sa.cs_next_var value /\
  allocas_from lo s /\ (^owned_decoder_state) sa s G tn /\
  not_fresh_at sa input /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?r Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
       (s,G,tn) [] (r,Gf,tnf)) /\
    ((?t. r = Abort Revert_abort t) \/
     (?t. r = OK t /\ ~t.vs_halted /\
       t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts /\
       eval_operand value t = SOME w /\
       op_prov Gf value = NONE /\ op_taint tnf value = {} /\
       (^owned_decoder_state) sb t Gf tnf /\
       (!x. not_fresh_at sa x ==>
          lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
          op_taint tnf (Var x) = op_taint tn (Var x))))
Proof
  strip_tac >> strip_tac >>
  `lo <= s.vs_alloca_next` by fs[] >>
  qpat_x_assum `!value clamp sa sb fn ctx s w G tn lo explicit PG. _` drule_all >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac)
  >- (qexistsl_tac [`r`, `Gf`, `tnf`] >> asm_rewrite_tac[] >> metis_tac[]) >>
  `?B. bop_scalar_seq {} UNIV (emitted_insts sa sb) B /\
     sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
     same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var` by
    (drule abi_decode_clamp_scalar >>
     disch_then (qspecl_then [`{}`, `UNIV`] mp_tac) >> simp[] >> metis_tac[]) >>
  `!code R A B. bop_scalar_seq R A code B ==>
     EVERY (\i. i.inst_opcode <> ALLOCA) code` by
    (POP_ASSUM_LIST (K all_tac) >> Induct >>
     simp[Once bodyPtrBopScalarSeqTheory.bop_scalar_seq_def] >>
     rpt strip_tac >> gvs[mk_inst_def] >> metis_tac[]) >>
  `alloca_history fn s` by fs[] >>
  `alloca_history fn t` by
    (irule abi_decode_no_alloca_endpoint_history >>
     qexistsl_tac [`s`, `sa`, `sb`] >>
     simp[] >> metis_tac[same_blocks_def, IS_PREFIX_APPEND]) >>
  `sa.cs_next_id <= sb.cs_next_id` by
    (mp_tac (Q.SPECL [`value`, `clamp`, `sa`]
       exprLoweringPropsTheory.ci_mono_compile_abi_clamp_basetype) >>
     asm_rewrite_tac[pairTheory.SND] >> simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `(^owned_decoder_state) sb t Gf tnf` by
    (irule abi_decode_owned_scalar_frame_with_history >>
     conj_tac >- asm_rewrite_tac[] >>
     qexistsl_tac [`G`, `s`, `sa`, `tn`] >> asm_rewrite_tac[] >> simp[]) >>
  qexistsl_tac [`r`, `Gf`, `tnf`] >> asm_rewrite_tac[] >>
  disj2_tac >> qexists_tac `t` >> asm_rewrite_tac[]
QED

Theorem abi_decode_owned_store_joint:
  emit_void MSTORE [Var dst;value] sa = ((),sb) /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (^owned_decoder_state) sa s G tn /\ (?H. V H) /\
  local_ptrs_reserved ce sa /\ not_fresh_at sa input /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  lookup_var dst s = SOME (n2w a) /\ ptr_covers G tn dst s 32 /\
  eval_operand value s = SOME w /\ op_taint tn value = {} /\
  output_base <= a /\ a+32 <= output_base+output_cap /\
  a+32 <= s.vs_alloca_next /\
  (w2n input_word + LENGTH input_bytes <= a \/ a+32 <= w2n input_word) /\
  EVERY (\(aid,p,b,k,bytes). b+k <= a \/ a+32 <= b) live /\
  EVERY (\(b,bytes). b+LENGTH bytes <= a \/ a+32 <= b) protected ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (^owned_decoder_state) sb t Gf tnf /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  BETA_TAC >> strip_tac >> (
  `a < dimword (:256)` by decide_tac >>
  qabbrev_tac `store_inst = mk_inst sa.cs_next_id MSTORE [Var dst;value] []` >>
  qabbrev_tac `u = mstore a w s` >>
  qabbrev_tac `Gf = step_prov PG G store_inst u` >>
  qabbrev_tac `tnf = step_taint store_inst s u tn` >>
  `local_ptrs_rel fn ce es.scopes s` by metis_tac[stmt_state_rel_def, state_rel_def] >>
  `lo <= a /\ (!name b k. local_region ce es.scopes s name b k ==>
    a+32 <= b \/ b+k <= a)` by
    (conj_tac >- decide_tac >> rpt strip_tac >>
     qpat_x_assum `!name b k. local_region _ _ _ _ _ _ ==> _` drule >> decide_tac) >>
  `!H. V H ==> stmt_state_rel H ctx fn ce cx es u /\
    ghost_inv_at (DF H) lo delta ce cx es Gf tnf u /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 Gf tnf` by
    (gen_tac >> strip_tac >>
     `ghost_inv_at (DF H') lo delta ce cx es G tn s /\
      ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn` by metis_tac[] >>
     `w2n (n2w a : 256 word) = a` by simp[] >>
     `FLOOKUP s.vs_allocas inst.inst_id = SOME (output_base,output_cap) /\
      (!H. V H ==> stmt_state_rel H ctx fn ce cx es s)` by metis_tac[] >>
     Q.SUBGOAL_THEN `w2n input_word + LENGTH input_bytes <= a \/ a+32 <= w2n input_word` assume_tac
     >- metis_tac[] >>
     qpat_assum `w2n (n2w a : 256 word) = a` (fn th =>
       drule_all (REWRITE_RULE [th]
         (abi_decode_output_write_frame_joint |> Q.INST [`a` |-> `addr`]
          |> Q.INST [`addr` |-> `n2w a`])) ) >>
     simp[] >>
     disch_then (qspecl_then [`sa.cs_next_id`, `PG`] mp_tac) >>
     simp[Abbr `u`, Abbr `Gf`, Abbr `tnf`, Abbr `store_inst`] >> metis_tac[]) >>
  `emit_inst MSTORE [Var dst;value] [] sa = ((),sb)` by
    gvs[emit_void_def, emit_inst_def] >>
  `step_inst_base store_inst s = OK u` by
    simp[Abbr `store_inst`, Abbr `u`, step_inst_base_opcode_eqs,
      mk_inst_def, exec_write2_def, eval_operand_def] >>
  `inst_mem_below_frontier store_inst s /\ inst_dload_in_section store_inst s` by
    simp[Abbr `store_inst`, unitTransformDefsTheory.inst_mem_below_frontier_def,
      memSafeRunTheory.inst_dload_in_section_def, mk_inst_def,
      contextCodegenRelTheory.source_memory_read_ranges_def,
      source_memory_write_ranges_def, fixed_source_write_range_def, eval_operand_def] >>
  `allocas_from lo s` by metis_tac[ghost_inv_at_def] >>
  `!D. ptr_inst_ok D lo 0 ctx fn G tn store_inst s` by
    (gen_tac >>
     `step_inst 0 ctx store_inst s = OK u` by
       (qpat_x_assum `step_inst_base store_inst s = _` (SUBST1_TAC o SYM) >>
        simp[step_inst_non_invoke, Abbr `store_inst`, mk_inst_def]) >>
     `u.vs_requests = s.vs_requests` by
       simp[Abbr `u`, mstore_def, write_memory_with_expansion_def] >>
     gvs[ptr_covers_def] >> simp[ptr_inst_ok_def] >> rpt conj_tac
     >- (simp[Abbr `store_inst`, access_ok_def, mk_inst_def,
          source_memory_write_ranges_def, fixed_source_write_range_def,
          contextCodegenRelTheory.source_memory_read_ranges_def, eval_operand_def,
          memLocDefsTheory.mem_write_ops_def, memLocDefsTheory.mem_read_ops_def] >>
         rpt strip_tac >> gvs[] >> metis_tac[])
     >- (simp[Abbr `store_inst`, taint_ok_def, mk_inst_def,
          contextCodegenRelTheory.source_memory_read_ranges_def] >>
         rpt strip_tac >> gvs[op_taint_def])) >>
  qabbrev_tac `t = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
     (s,G,tn) [] (OK t,Gf,tnf)` by
    (gen_tac >>
     mp_tac (Q.INST [`opc` |-> `MSTORE`, `args` |-> `[Var dst;value]`,
       `outs` |-> `[]`, `func` |-> `fn`] typed_copy_emit_inst_origin_ptr_path) >>
     simp[Abbr `t`, Abbr `Gf`, Abbr `tnf`, Abbr `store_inst`, is_terminator_def]) >>
  drule emit_inst_extends >> strip_tac >>
  drule emitted_insts_emit_inst >> strip_tac >>
  `~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
   t.vs_inst_idx = LENGTH sb.cs_current_insts /\ t.vs_allocas = s.vs_allocas` by
    simp[Abbr `t`, Abbr `u`, mstore_def, write_memory_with_expansion_def] >>
  `alloca_history fn t` by
    (irule abi_decode_no_alloca_endpoint_history >>
     qexistsl_tac [`s`, `sa`, `sb`] >>
     simp[Abbr `store_inst`, mk_inst_def, IS_PREFIX_APPEND]) >>
  `!H. V H ==> stmt_state_rel H ctx fn ce cx es t /\
    ghost_inv_at (DF H) lo delta ce cx es Gf tnf t /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 Gf tnf` by
    (ho_match_mp_tac (abi_decode_scalar_joint_frame |>
       Q.INST [`s` |-> `u`, `G` |-> `Gf`, `tn` |-> `tnf`]) >>
     simp[Abbr `t`, state_frame_def, lookup_var_def] >> metis_tac[]) >>
  `Gf = G /\ tnf.t_var = tn.t_var /\
   tnf.t_mem = tn.t_mem DIFF {i | a <= i /\ i < a+32}` by
    (mp_tac (wordLoadStorePtrTheory.mstore_ghost_frame |> Q.SPECL
      [`PG`, `G`, `tn`, `s`, `sa.cs_next_id`, `dst`, `value`, `n2w a`, `w`]) >>
     simp[Abbr `Gf`, Abbr `tnf`, Abbr `store_inst`, Abbr `u`]) >>
  `!p. lookup_var p t = lookup_var p s` by
    simp[Abbr `t`, Abbr `u`, mstore_def, write_memory_with_expansion_def, lookup_var_def] >>
  `!p k. ptr_covers Gf tnf p t k = ptr_covers G tn p s k` by
    simp[ptr_covers_def, op_taint_def, Abbr `t`, Abbr `u`, mstore_def,
      write_memory_with_expansion_def, lookup_var_def] >>
  `t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_memory = (mstore a w s).vs_memory` by
    simp[Abbr `t`, Abbr `u`, mstore_def, write_memory_with_expansion_def] >>
  `!b k. b+k <= a \/ a+32 <= b ==>
    mem_bytes_at b k t.vs_memory = mem_bytes_at b k s.vs_memory` by
    metis_tac[valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint] >>
  `!name b k. local_region ce es.scopes t name b k =
     local_region ce es.scopes s name b k` by
    (rpt gen_tac >> irule copy_buffer_local_region_frame >>
     qexists_tac `sa` >> simp[]) >>
  `abi_decode_ptr_window Gf tnf t input input_word (LENGTH input_bytes)` by
    (gvs[abi_decode_ptr_window_def] >> simp[abi_decode_ptr_window_def] >>
     metis_tac[]) >>
  qexistsl_tac [`t`, `Gf`, `tnf`] >> asm_rewrite_tac[] >>
  simp[op_taint_def] >>
  `u.vs_memory = t.vs_memory` by simp[Abbr `t`] >>
  `!p. not_fresh_at sb p = not_fresh_at sa p` by simp[not_fresh_at_def] >>
  rpt conj_tac
  >- metis_tac[]
  >- (rule_assum_tac (REWRITE_RULE [EVERY_MEM]) >>
      pure_rewrite_tac[EVERY_MEM] >> rpt strip_tac >>
      PairCases_on `e` >> pure_rewrite_tac[pairTheory.UNCURRY_DEF] >>
      qpat_x_assum `!e. MEM e live ==> (\(aid,p,b,k,bytes). aid < sa.cs_next_id /\ _) e`
        (qspec_then `(e0,e1,e2,e3,e4)` mp_tac) >>
      qpat_x_assum `!e. MEM e live ==> (\(aid,p,b,k,bytes). b+k <= a \/ _) e`
        (qspec_then `(e0,e1,e2,e3,e4)` mp_tac) >>
      simp_tac (srw_ss()) [] >> rpt strip_tac >>
      qpat_x_assum `MEM _ live ==> _ /\ _` (drule_then strip_assume_tac) >>
      qpat_x_assum `MEM _ live ==> _ \/ _` (drule_then assume_tac) >>
      `e0 < sa.cs_next_id + 1` by decide_tac >>
      qpat_x_assum `op_taint tn (Var e1) = {}`
        (mp_tac o REWRITE_RULE [op_taint_def]) >>
      simp_tac (srw_ss()) [] >> metis_tac[])
  >- (rule_assum_tac (REWRITE_RULE [EVERY_MEM]) >>
      pure_rewrite_tac[EVERY_MEM] >> rpt strip_tac >>
      PairCases_on `e` >>
      qpat_x_assum `!e. MEM e protected ==> (\(a,bytes). mem_bytes_at a _ _ = _) e`
        (qspec_then `(e0,e1)` mp_tac) >>
      qpat_x_assum `!e. MEM e protected ==> (\(b,bytes). b+LENGTH bytes <= a \/ _) e`
        (qspec_then `(e0,e1)` mp_tac) >>
      simp_tac (srw_ss()) [] >> rpt strip_tac >> metis_tac[])
  >- metis_tac[]
  >- metis_tac[]
  >> qpat_x_assum `!p. not_fresh_at sb p = _`
       (fn th => pure_rewrite_tac[th]) >> asm_rewrite_tac[])
QED

Theorem abi_decode_word_case_joint_conditional:
  (^clamp_boundary) ==>
  !dst src opc base_op hi clamp.
    (^owned_to_buf_motive) dst src opc base_op hi (DecPrimWord clamp)
Proof
  strip_tac >> rpt gen_tac >>
  CONV_TAC (RATOR_CONV (RATOR_CONV (RATOR_CONV (RATOR_CONV (RATOR_CONV BETA_CONV))))) >>
  CONV_TAC (RATOR_CONV (RATOR_CONV (RATOR_CONV (RATOR_CONV BETA_CONV)))) >>
  CONV_TAC (RATOR_CONV (RATOR_CONV (RATOR_CONV BETA_CONV))) >>
  CONV_TAC (RATOR_CONV (RATOR_CONV BETA_CONV)) >>
  CONV_TAC (RATOR_CONV BETA_CONV) >> CONV_TAC BETA_CONV >>
  rpt gen_tac >> qabbrev_tac `OS = (^owned_decoder_state)` >>
  BETA_TAC >> strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_abi_decode_to_buf_def, compile_abi_decode_static_def,
       comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> strip_tac >>
  `type_memory_bytes ce ty = 32` by
    metis_tac[abi_decoder_primitive_cases] >>
  `type_memory_size tv = 32 /\
   abi_member_head_size (vyper_to_abi_type env ty) = 32` by
    (drule abiDecoderCoherenceTheory.abi_decoder_coherent_header >>
     simp[abiDecoderCoherenceTheory.abi_decoder_header_def] >>
     metis_tac[abi_decode_scalar_member_head]) >>
  rename1 `compile_abi_clamp_basetype val_op clamp cs'' = (ignored,clamped)` >>
  `ignored = ()` by (Cases_on `ignored` >> simp[]) >>
  `cs_extends start cs' /\ cs_extends cs' cs'' /\
   cs_extends cs'' clamped /\ cs_extends clamped finish'` by
    metis_tac[compile_abi_dec_addr_labels, emit_op_labels,
      compile_abi_clamp_basetype_labels, emit_void_labels, pairTheory.SND] >>
  `cs_extends start cs'' /\ cs_extends cs'' finish'` by
    metis_tac[cs_extends_trans] >>
  `fn_has_code start cs'' fn` by metis_tac[fragExecTheory.fn_has_code_split] >>
  `off + 32 <= LENGTH input_bytes` by decide_tac >>
  `allocas_from lo s /\ origin.cs_next_var <= start.cs_next_var` by
    (fs[Abbr `OS`] >> metis_tac[ghost_inv_at_def]) >>
  `not_fresh_at start input` by
    (gvs[abiDecoderReentryTheory.abi_decoder_operand_live_def,
         abiDecoderReentryTheory.abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at start x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at start x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  qpat_assum `Abbrev (OS = _)` (fn th =>
    drule_all (PURE_REWRITE_RULE [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]
      abi_decode_owned_relative_load)) >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  `emit_op ADD [Var input;src] start = (src_addr,cs')` by
    gvs[compile_abi_dec_addr_def] >>
  qpat_assum `emit_op ADD _ _ = _`
    (strip_assume_tac o MATCH_MP loweringShapeRulesTheory.emit_op_facts) >>
  qpat_assum `emit_op MLOAD _ _ = _`
    (strip_assume_tac o MATCH_MP loweringShapeRulesTheory.emit_op_facts) >>
  `start.cs_next_var <= cs''.cs_next_var` by decide_tac >>
  `not_fresh_at cs'' input /\ local_ptrs_reserved ce cs'' /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cs'' x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cs'' x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono, local_ptrs_reserved_next_var] >>
  `abi_decoder_operand_live cs''.cs_next_var val_op` by
    metis_tac[abiDecoderReentryTheory.abi_decoder_operand_live_emit] >>
  `allocas_from lo t` by (fs[Abbr `OS`] >> metis_tac[ghost_inv_at_def]) >>
  `fn_has_code cs'' clamped fn` by metis_tac[fragExecTheory.fn_has_code_split] >>
  qpat_x_assum `ignored = ()` SUBST_ALL_TAC >>
  qpat_assum `Abbrev (OS = _)` (fn th =>
    drule_all (PURE_REWRITE_RULE [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]
      abi_decode_owned_clamp_conditional)) >>
  disch_then (qspecl_then [`explicit`, `PG`] mp_tac) >>
  (strip_tac
   >- (qexistsl [`r`, `Gf'`, `tnf'`] >> conj_tac
       >- metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans]
       >> metis_tac[]) >>
   `start.cs_next_var <= clamped.cs_next_var /\
    cs''.cs_next_var <= clamped.cs_next_var` by
     (mp_tac (Q.SPECL [`val_op`, `clamp`, `cs''`]
        exprLoweringPropsTheory.ci_mono_compile_abi_clamp_basetype) >>
      asm_rewrite_tac[pairTheory.SND] >>
      simp[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
   `not_fresh_at start p` by
     gvs[abiDecoderReentryTheory.abi_decoder_operand_live_def,
         abiDecoderReentryTheory.abi_decoder_older_vars_def, not_fresh_at_def] >>
   `not_fresh_at cs'' p` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
   `local_ptrs_reserved ce clamped /\ not_fresh_at clamped input /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at clamped x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at clamped x)` by
     metis_tac[freshWritesTheory.not_fresh_at_mono, local_ptrs_reserved_next_var] >>
   `lookup_var p t' = SOME (n2w d) /\
    ptr_covers Gf' tnf' p t' 32` by
     (qpat_assum `!x. not_fresh_at start x ==> _`
        (qspec_then `p` mp_tac) >>
      qpat_assum `!x. not_fresh_at cs'' x ==> _`
        (qspec_then `p` mp_tac) >>
      simp[] >> rpt strip_tac >>
      qpat_x_assum `ptr_covers G tn p s _` mp_tac >>
      qpat_x_assum `eval_operand dst s = _` mp_tac >>
      asm_rewrite_tac[eval_operand_def, ptr_covers_def] >>
      rpt strip_tac >> gvs[]) >>
   `alloca_inv t' /\
    FLOOKUP t'.vs_allocas output_id = SOME (output_base,output_cap)` by
     (fs[Abbr `OS`] >> metis_tac[stmt_state_rel_def]) >>
   `d+32 <= t'.vs_alloca_next` by
     (fs[venomMemDefsTheory.alloca_inv_def,
         venomMemDefsTheory.alloca_next_valid_def] >>
      first_x_assum (drule_then assume_tac) >> decide_tac) >>
   `fn_has_code clamped finish' fn` by
     metis_tac[fragExecTheory.fn_has_code_split] >>
   `EVERY (\(aid,p,b,k,bytes). b+k <= d \/ d+32 <= b) live` by
     (pure_rewrite_tac[EVERY_MEM] >> rpt strip_tac >> PairCases_on `e` >>
      qpat_x_assum `EVERY (\(aid,p,b,k,bytes). aid < _ /\ _) live`
        (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
      disch_then (qspec_then `(e0,e1,e2,e3,e4)` mp_tac) >> simp[]) >>
   `(?H. V H) /\ d+32 <= output_base+output_cap /\
    (w2n input_word + LENGTH input_bytes <= d \/ d+32 <= w2n input_word) /\
    EVERY (\(b,bytes). b+LENGTH bytes <= d \/ d+32 <= b) protected` by
     (asm_rewrite_tac[] >> metis_tac[]) >>
   qpat_assum `Abbrev (OS = _)` (fn th =>
     drule_at (Pat `OS clamped t' Gf' tnf'`)
       (PURE_REWRITE_RULE [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]
       abi_decode_owned_store_joint)) >>
   disch_then drule >>
   disch_then (qspecl_then [`mload (w2n input_word + off) s`,
     `explicit`, `d`, `PG`] mp_tac) >>
   (impl_tac >- (asm_rewrite_tac[] >> metis_tac[])) >>
   disch_then (qx_choose_then `u` (qx_choose_then `Gu`
     (qx_choose_then `tnu` strip_assume_tac))) >>
   (qexistsl [`OK u`, `Gu`, `tnu`] >> conj_tac
    >- metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans] >>
    disj1_tac >> qexists_tac `u` >> asm_rewrite_tac[] >>
    rpt strip_tac >>
    `not_fresh_at clamped x /\ not_fresh_at cs'' x` by
      metis_tac[freshWritesTheory.not_fresh_at_mono] >>
    metis_tac[]))
QED
