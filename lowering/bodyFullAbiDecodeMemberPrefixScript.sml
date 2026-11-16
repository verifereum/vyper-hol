Theory bodyFullAbiDecodeMemberPrefix
Ancestors
  gasOriginPtrLabels bodyFullAbiDecodeInterface bodyFullAbiDecodeFiniteGuard
  bodyFullAbiDecodeLeafCases abiDecodePtrPrims abiDecodePtrHead abiDecodePtrBytesTail
  instSeqPtrLo fragGasSeqPtr fragGasOriginPtrLoop fragExecMem abiDecoderCoherence
  abiDecoderMemberInfos abiDecoderReentry vyperABI valueEncoding
  bodyPtrTypeBuiltinsBounds loweringStateRelDefs loweringShapeRules
  emitHelper compileEnv emitHelperProps exprLowering exprLoweringProps
  abiEncoder venomExecSemantics venomInst venomState words list rich_list finite_map

(* The first ADD selects the bounded head slot, not the dynamic child.
   Its liveness frame does not require global fresh_vars_wrt. *)
Theorem abi_decode_member_slot_run[local]:
  emit_op ADD [src;Lit (n2w ao)] sa = (pos,sb) /\
  eval_operand src s = SOME (n2w off) /\
  off+ao+head_size <= h /\ h < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand pos t = SOME (n2w (off+ao)) /\
    off+ao < dimword (:256) /\ off+ao+head_size <= h /\
    (!old. abi_decoder_operand_live sa.cs_next_var old ==>
       eval_operand old t = eval_operand old s) /\
    t with vs_vars := s.vs_vars = s
Proof
  strip_tac >>
  drule_all buffer_emit_add_run >> strip_tac >>
  qexists_tac `update_var (STRING #"%" (toString sa.cs_next_var))
    (n2w off + n2w ao) s` >>
  asm_rewrite_tac[] >>
  `pos = Var (STRING #"%" (toString sa.cs_next_var))` by
    gvs[emit_op_def, fresh_var_def, fresh_id_def, emit_def,
        comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  simp[eval_operand_update_var, word_add_n2w] >>
  conj_tac >-
    (rpt strip_tac >> irule eval_operand_update_old >>
     qexists_tac `sa` >>
     conj_tac >-
       (rpt strip_tac >> gvs[abi_decoder_operand_live_def,
          abi_decoder_older_vars_def, not_fresh_at_def]) >> simp[]) >>
  simp[update_var_def]
QED

(* Alpha-identical to the existing owned interface, not a HOL definition. *)
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
  EVERY (\(aid:num,p:string,b:num,k:num,bytes:word8 list). not_fresh_at st p) live``;

Theorem abi_decode_member_slot_joint[local]:
  emit_op ADD [src;Lit (n2w ao)] sa = (pos,sb) /\
  eval_operand src s = SOME (n2w off) /\
  off+ao+head_size <= h /\ h < dimword (:256) /\
  op_prov G src = NONE /\ op_taint tn src = {} /\
  ~ctx_has_dalloca ctx /\ fn_has_code sa sb fn /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  allocas_from lo s /\ (^owned_decoder_state) sa s G tn /\
  not_fresh_at sa input /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?u Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
       (s,G,tn) [] (OK u,Gf,tnf)) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (^owned_decoder_state) sb u Gf tnf /\
    eval_operand pos u = SOME (n2w (off+ao)) /\
    op_prov Gf pos = NONE /\ op_taint tnf pos = {} /\
    off+ao < dimword (:256) /\ off+ao+head_size <= h /\
    (!x. not_fresh_at sa x ==>
       lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_decode_member_slot_run >> strip_tac >>
  `bop_scalar_seq {x | not_fresh_at sa x} {src;Lit (n2w ao)}
     (emitted_insts sa sb) (pos INSERT {src;Lit (n2w ao)})` by
    (irule bodyPtrBopScalarCompileTheory.bop_scalar_seq_emit_op >>
     conj_tac >- simp[] >> qexistsl_tac [`ADD`, `[src;Lit (n2w ao)]`] >> simp[]) >>
  `!op. op IN {src;Lit (n2w ao)} ==>
      op_prov G op = NONE /\ op_taint tn op = {}` by
    (pure_rewrite_tac[pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY] >>
     rpt strip_tac >> gvs[] >>
     simp[ptrDisciplineTheory.op_prov_def, ptrDisciplineTheory.op_taint_def]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `inst_extends sa sb` by metis_tac[inst_extends_emit_op] >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb)` by
    simp[mk_inst_def] >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id` by
    (drule emit_op_facts >> simp[]) >>
  drule_all (BETA_RULE abi_decode_scalar_guard_success_joint) >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`u`, `Gf`, `tnf`] >> asm_rewrite_tac[] >>
  qpat_x_assum `u = _` (fn th => rewrite_tac[th]) >>
  gvs[eval_operand_def, lookup_var_def]
QED

(* The dynamic offset is unconstrained.  The actual-position ADD is allowed
   to wrap, in which case the emitted underflow guard rejects. *)
Theorem abi_decode_member_actual_run[local]:
  emit_op ADD [src;offset] sa = (actual,sm) /\
  abi_decode_ge_guard actual src sm = ((),sb) /\
  eval_operand src s = SOME sw /\ eval_operand offset s = SOME ow /\
  abi_decoder_operand_live sa.cs_next_var src ==>
  (?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t) \/
  (?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand actual t = SOME (sw+ow) /\ w2n sw <= w2n (sw+ow))
Proof
  simp[abiDecoderGuardTheory.abi_decode_ge_guard_def,
       comp_bind_def, comp_ignore_bind_def, emit_op_def, emit_void_def,
       fresh_var_def, fresh_id_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  `!n w u. sa.cs_next_var <= n ==>
    eval_operand src (update_var (STRING #"%" (toString n)) w u) =
      eval_operand src u` by
    (rpt strip_tac >> irule eval_operand_update_old >>
     qexists_tac `sa` >> conj_tac >-
       (rpt strip_tac >> gvs[abi_decoder_operand_live_def,
          abi_decoder_older_vars_def, not_fresh_at_def]) >> simp[]) >>
  `!x w u. eval_operand (Var x) (update_var x w u) = SOME w` by
    simp[eval_operand_update_var] >>
  simp_tac (srw_ss()) [emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp_tac (srw_ss()) [DROP_LENGTH_APPEND] >>
  simp[Once run_inst_seq_def, mk_inst_def, Once step_inst_base_def,
       exec_pure2_def] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def,
       exec_pure2_def, eval_operand_update_var] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def,
       exec_pure1_def, eval_operand_update_var] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def,
       eval_operand_update_var] >>
  Cases_on `w2n (sw+ow) < w2n sw` >- simp[] >>
  disj2_tac >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, exec_pure2_def] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def,
       exec_pure2_def, exec_pure1_def] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def,
       exec_pure2_def, exec_pure1_def] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def,
       exec_pure2_def, exec_pure1_def] >>
  simp[run_inst_seq_def] >>
  simp[eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, ASCIInumbersTheory.toString_inj]
QED

Theorem abi_decode_member_actual_joint:
  emit_op ADD [src;offset] sa = (actual,sm) /\
  abi_decode_ge_guard actual src sm = ((),sb) /\
  eval_operand src s = SOME sw /\ eval_operand offset s = SOME ow /\
  abi_decoder_operand_live sa.cs_next_var src /\
  op_prov G src = NONE /\ op_prov G offset = NONE /\
  op_taint tn src = {} /\ op_taint tn offset = {} /\
  ~ctx_has_dalloca ctx /\ fn_has_code sa sb fn /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  allocas_from lo s /\ (^owned_decoder_state) sa s G tn /\
  not_fresh_at sa input /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  (?t Gf tnf. !D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s,G,tn) [] (Abort Revert_abort t,Gf,tnf)) \/
  (?u Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK u,Gf,tnf)) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (^owned_decoder_state) sb u Gf tnf /\
    eval_operand actual u = SOME (sw+ow) /\ w2n sw <= w2n (sw+ow) /\
    op_prov Gf actual = NONE /\ op_taint tnf actual = {} /\
    (!x. not_fresh_at sa x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)))
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `?B. bop_scalar_seq {x | not_fresh_at sa x} {src;offset}
     (emitted_insts sa sb) B /\ actual IN B` by
    (irule abi_decode_position_suffix_scalar >>
     conj_tac >- simp[] >>
     qexistsl_tac [`Lit 1w`, `sm`, `offset`, `src`] >> simp[]) >>
  pop_assum strip_assume_tac >>
  `!op. op IN {src;offset} ==>
      op_prov G op = NONE /\ op_taint tn op = {}` by
    (pure_rewrite_tac[pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY] >>
     rpt strip_tac >> gvs[]) >>
  `inst_extends sa sb /\ sb.cs_current_bb = sa.cs_current_bb /\
   sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
   EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb)` by
    (qpat_x_assum `abi_decode_ge_guard _ _ _ = _` mp_tac >>
     qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[abiDecoderGuardTheory.abi_decode_ge_guard_def,
       comp_bind_def, comp_ignore_bind_def, emit_op_def, emit_void_def,
       fresh_var_def, fresh_id_def, emit_def, comp_return_def] >>
     rpt strip_tac >> gvs[] >>
     simp_tac (srw_ss()) [inst_extends_def, emitted_insts_def] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC] >>
     simp_tac (srw_ss()) [DROP_LENGTH_APPEND, mk_inst_def]) >>
  drule_all abi_decode_member_actual_run >> strip_tac
  >- (disj1_tac >> drule_all abi_decode_scalar_guard_abort_joint >>
      disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
      qexistsl_tac [`t with vs_inst_idx := j`, `Gf`, `tnf`] >> asm_rewrite_tac[]) >>
  disj2_tac >> drule_all (BETA_RULE abi_decode_scalar_guard_success_joint) >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`u`, `Gf`, `tnf`] >> asm_rewrite_tac[] >>
  qpat_x_assum `u = _` (fn th => rewrite_tac[th]) >>
  gvs[eval_operand_def, lookup_var_def]
QED

(* Destination selection is pointer arithmetic, not a scalar certificate. *)
Theorem abi_decode_member_destination_joint[local]:
  emit_op ADD [Var dst;pos] sa = (Var out,sb) /\
  ptr_covers G tn dst s cap /\ lookup_var dst s = SOME b /\
  eval_operand pos s = SOME (n2w q) /\
  op_taint tn (Var dst) = {} /\ op_taint tn pos = {} /\
  ~ctx_has_dalloca ctx /\ q+k <= cap /\ w2n b+cap < dimword(:256) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    ptr_covers Gf tnf out t k /\ lookup_var out t = SOME (b+n2w q) /\
    FLOOKUP Gf out = FLOOKUP G dst /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  drule_all (abi_decode_ptr_output_address |> Q.INST [`D` |-> `ARB`, `PG` |-> `PG`]) >>
  disch_then (qspecl_then [`fn`, `PG`] mp_tac) >>
  simp_tac (srw_ss()) [LET_THM] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `ptr_covers Gf tnf out u k` >>
  qabbrev_tac `t = u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `FLOOKUP Gf out = FLOOKUP G dst` by
    (qpat_x_assum `ptr_covers G tn dst s cap` mp_tac >>
     simp[bodyPtrDefsTheory.ptr_covers_def] >> strip_tac >>
     simp[Abbr `Gf`, ptrDisciplineTheory.step_prov_def,
          ptrDisciplineTheory.set_prov_def, ptrDisciplineTheory.out_prov_def,
          ptrDisciplineTheory.first_prov_def, ptrDisciplineTheory.op_prov_def,
          mk_inst_def, FLOOKUP_UPDATE]) >>
  qexistsl_tac [`t`, `Gf`, `tnf`] >>
  reverse conj_tac >-
    (drule emit_op_facts >> strip_tac >>
     simp[Abbr `t`, Abbr `u`, update_var_def]) >>
  `!D. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf` by
    (gen_tac >>
     drule_all (abi_decode_ptr_output_address |> Q.INST [`D` |-> `D`, `PG` |-> `PG`]) >>
     disch_then (qspecl_then [`fn`, `PG`, `D`] mp_tac) >>
     simp[LET_THM, Abbr `Gf`, Abbr `tnf`, Abbr `u`]) >>
  `!D. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s Gf tnf` by
    (gen_tac >> irule inst_seq_ptr_zero_to_lo >>
     simp[] >> qexists_tac `D` >> simp[]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `inst_extends sa sb` by metis_tac[inst_extends_emit_op] >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule emit_op_facts >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    simp[mk_inst_def, is_terminator_def] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (simp[run_inst_seq_mem_ok_def, instMemFrontierTheory.below_frontier_no_ranges,
          mk_inst_def] >> BasicProvers.TOP_CASE_TAC >> simp[]) >>
  gen_tac >>
  qpat_x_assum `inst_seq_ptr ARB _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `!D. inst_seq_ptr D 0 _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `!D. inst_seq_ptr D lo _ _ _ _ _ _ _ _ _`
    (qspec_then `D` assume_tac) >>
  drule_all emitted_origin_ptr_path >>
  disch_then (qspec_then `explicit` mp_tac) >>
  simp[Abbr `t`, Abbr `u`]
QED

Theorem abi_decode_member_destination_owned:
  emit_op ADD [Var dst;pos] sa = (Var out,sb) /\
  ptr_covers G tn dst s cap /\ lookup_var dst s = SOME b /\
  eval_operand pos s = SOME (n2w q) /\
  op_taint tn (Var dst) = {} /\ op_taint tn pos = {} /\
  ~ctx_has_dalloca ctx /\ q+k <= cap /\ w2n b+cap < dimword(:256) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  allocas_from lo s /\ (^owned_decoder_state) sa s G tn /\
  not_fresh_at sa input /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    ptr_covers Gf tnf out t k /\ lookup_var out t = SOME (b+n2w q) /\
    FLOOKUP Gf out = FLOOKUP G dst /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (^owned_decoder_state) sb t Gf tnf /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `lo <= s.vs_alloca_next /\ alloca_history fn s` by fs[] >>
  drule_all abi_decode_member_destination_joint >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  drule emit_op_facts >> strip_tac >>
  `sa.cs_next_id <= sb.cs_next_id` by
    (drule emitted_insts_emit_op >> simp[]) >>
  `isPREFIX sa.cs_current_insts sb.cs_current_insts` by
    metis_tac[IS_PREFIX_APPEND] >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb)` by
    (drule emitted_insts_emit_op >> simp[mk_inst_def]) >>
  `alloca_history fn t` by
    (irule abi_decode_no_alloca_endpoint_history >> metis_tac[]) >>
  `(^owned_decoder_state) sb t Gf tnf` by
    (irule abi_decode_owned_scalar_frame_with_history >>
     conj_tac >- asm_rewrite_tac[] >>
     qexistsl_tac [`G`, `s`, `sa`, `tn`] >> asm_rewrite_tac[] >>
     simp[] >> metis_tac[]) >>
  pop_assum (assume_tac o BETA_RULE) >>
  qexistsl_tac [`t`, `Gf`, `tnf`] >> asm_rewrite_tac[]
QED

(* Alpha-identical entry quotations from the shared interface. *)
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

val guarded_decoder_pre = ``\start finish dst src opc base_op hi d write_start size s G tn.
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
     eval_operand hi s = SOME (n2w h) /\ off < dimword (:256) /\
     h <= LENGTH input_bytes) /\ hi <> Lit 0w /\
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

val guarded_to_buf_entry = ``\dst src opc base_op hi info env sf ty tv live protected start finish s G tn d.
    abi_decoder_coherent ce env sf ty tv /\
    info = type_to_abi_dec_info sf ce ty /\
    (?off h. eval_operand src s = SOME (n2w off) /\
       eval_operand hi s = SOME (n2w h) /\ off < dimword (:256) /\
       h <= LENGTH input_bytes /\
       ((?clamp. info = DecPrimWord clamp) ==>
         off + abi_member_head_size (vyper_to_abi_type env ty) <= h)) /\
    compile_abi_decode_to_buf dst src opc base_op hi info start = ((),finish) /\
    (^guarded_decoder_pre) start finish dst src opc base_op hi d d
      (type_memory_size tv) s G tn``;

val bounded_member_entry = ``\dst src opc base_op hi elems ao vo env sf pretys pretvs tys tvs live protected start finish s G tn d.
    LIST_REL (abi_decoder_coherent ce env sf) (pretys++tys) (pretvs++tvs) /\
    LENGTH pretys = LENGTH pretvs /\
    elems = abi_decoder_member_infos sf ce tys /\
    ao = SUM (MAP (abi_embedded_static_size ce.ce_struct_fields) pretys) /\
    vo = SUM (MAP (type_memory_bytes ce) pretys) /\
    hi <> Lit 0w /\
    (?off h. eval_operand src s = SOME (n2w off) /\
      eval_operand hi s = SOME (n2w h) /\
      off+ao+SUM (MAP (abi_embedded_static_size ce.ce_struct_fields) tys) <= h /\
      h <= LENGTH input_bytes) /\
    compile_abi_decode_complex_elems dst src opc base_op hi elems ao vo start =
      ((),finish) /\
    eval_operand dst s = SOME (n2w d) /\
    (^owned_decoder_pre) start finish dst src opc base_op hi d (d+vo)
      (SUM (MAP (type_memory_bytes ce) tys)) s G tn``;

Theorem abi_decode_member_select_joint[local]:
  !finish.
  (^bounded_member_entry) dst src opc base_op hi elems ao vo env sf
    pretys pretvs (ty::tys) (tv::tvs) live protected start finish s G tn d /\
  compile_getelemptr_abi src
    (dec_info_needs_offset (type_to_abi_dec_info sf ce ty)) ao opc base_op hi
    start = (elem_src,select_end) /\ fn_has_code start select_end fn ==>
  ((?rstate Gr tnr. !D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (Abort Revert_abort rstate,Gr,tnr)) \/
   (?u Gu tnu q h.
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK u,Gu,tnu)) /\
      ~u.vs_halted /\ u.vs_current_bb = select_end.cs_current_bb /\
      u.vs_inst_idx = LENGTH select_end.cs_current_insts /\
      (^owned_decoder_state) select_end u Gu tnu /\
      eval_operand elem_src u = SOME (n2w q) /\ q < dimword(:256) /\
      eval_operand hi u = SOME (n2w h) /\ h <= LENGTH input_bytes /\
      op_prov Gu elem_src = NONE /\ op_taint tnu elem_src = {} /\
      ((?clamp. type_to_abi_dec_info sf ce ty = DecPrimWord clamp) ==>
        q + abi_member_head_size (vyper_to_abi_type env ty) <= h) /\
      (!x. not_fresh_at start x ==>
        lookup_var x u = lookup_var x s /\ FLOOKUP Gu x = FLOOKUP G x /\
        op_taint tnu (Var x) = op_taint tn (Var x))))
Proof
  gen_tac >> BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `allocas_from lo s` by
    (qpat_x_assum `?H. V H` strip_assume_tac >>
     qpat_x_assum `!H. V H ==> _` drule >>
     simp[bodyPtrDefsTheory.ghost_inv_at_def] >> metis_tac[]) >>
  `not_fresh_at start input` by
    gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at start x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at start x)` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  qpat_x_assum `?off h. _ /\ _ /\ off+ao+_ <= h /\ _` strip_assume_tac >>
  `h < dimword(:256)` by decide_tac >>
  `off+ao+abi_embedded_static_size ce.ce_struct_fields ty <= h` by
    (qpat_x_assum `off+ao+_ <= h` mp_tac >> simp[MAP,SUM]) >>
  qpat_x_assum `compile_getelemptr_abi _ _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [compile_getelemptr_abi_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >>
  first_assum (fn th => CONV_TAC (LAND_CONV (REWRITE_CONV [th]))) >>
  simp_tac std_ss [] >>
  reverse (Cases_on `dec_info_needs_offset (type_to_abi_dec_info sf ce ty)`) >-
    (asm_simp_tac bool_ss [comp_return_def, pairTheory.PAIR_EQ] >>
     disch_then (map_every SUBST_ALL_TAC o CONJUNCTS) >>
     drule_all (BETA_RULE abi_decode_member_slot_joint) >>
     disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
     `u.vs_labels = s.vs_labels` by
       metis_tac[gas_origin_ptr_path_preserves_labels] >>
     `eval_operand hi u = SOME (n2w h)` by
       (`!x. hi = Var x ==> not_fresh_at start x` by
          (qpat_x_assum `abi_decoder_operand_live _ hi` mp_tac >>
           POP_ASSUM_LIST (K all_tac) >> Cases_on `hi` >>
           simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
             not_fresh_at_def]) >>
        qpat_x_assum `eval_operand hi s = _` mp_tac >>
        qpat_x_assum `!x. hi = Var x ==> _` mp_tac >>
        qpat_x_assum `!x. not_fresh_at start x ==> _` mp_tac >>
        qpat_x_assum `u.vs_labels = s.vs_labels` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> Cases_on `hi` >>
        simp[eval_operand_def] >> metis_tac[]) >>
     `abi_decoder_coherent ce env sf ty tv` by
       (qpat_x_assum `LIST_REL _ _ _` mp_tac >>
        simp[LIST_REL_APPEND_EQ]) >>
     `abi_embedded_static_size ce.ce_struct_fields ty =
       abi_member_head_size (vyper_to_abi_type env ty)` by
       metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
     disj2_tac >> qexistsl_tac [`u`,`Gf`,`tnf`,`off+ao`,`h`] >>
     asm_rewrite_tac[] >> strip_tac >> decide_tac) >>
  asm_simp_tac bool_ss [comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >>
  first_assum (fn th => CONV_TAC (LAND_CONV (REWRITE_CONV [th]))) >>
  simp_tac std_ss [] >>
  pairarg_tac >>
  first_assum (fn th => CONV_TAC (LAND_CONV (REWRITE_CONV [th]))) >>
  simp_tac std_ss [] >>
  pairarg_tac >>
  first_assum (fn th => CONV_TAC (LAND_CONV (REWRITE_CONV [th]))) >>
  simp_tac std_ss [] >>
  pure_rewrite_tac [GSYM (REWRITE_RULE [comp_bind_def, comp_ignore_bind_def]
    abiDecoderGuardTheory.abi_decode_ge_guard_def)] >>
  pairarg_tac >>
  first_assum (fn th => CONV_TAC (LAND_CONV (REWRITE_CONV [th]))) >>
  simp_tac std_ss [comp_return_def] >>
  disch_then (map_every SUBST_ALL_TAC o CONJUNCTS) >>
  rename1 `emit_op ADD [src; Lit (n2w ao)] start = (head_ptr,slot_end)` >>
  rename1 `compile_abi_dec_addr (Var input) head_ptr slot_end = (head_addr,addr_end)` >>
  rename1 `emit_op MLOAD [head_addr] addr_end = (offset_val,load_end)` >>
  rename1 `emit_op ADD [src;offset_val] load_end = (elem_src,actual_end)` >>
  `abi_decode_ge_guard elem_src src actual_end = ((),select_end)` by
    (simp_tac std_ss [abiDecoderGuardTheory.abi_decode_ge_guard_def,
       comp_bind_def, comp_ignore_bind_def, LET_THM] >>
     simp[]) >>
  `cs_extends start slot_end /\ cs_extends slot_end addr_end /\
   cs_extends addr_end load_end /\ cs_extends load_end actual_end /\
   cs_extends actual_end select_end` by
    (qpat_x_assum `abi_decode_ge_guard _ _ _ = _` mp_tac >>
     qpat_x_assum `emit_op ADD [src;offset_val] _ = _` mp_tac >>
     qpat_x_assum `emit_op MLOAD _ _ = _` mp_tac >>
     qpat_x_assum `compile_abi_dec_addr _ _ _ = _` mp_tac >>
     qpat_x_assum `emit_op ADD [src;Lit _] _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[exprSimAccountsTheory.emit_op_extends_next_var,
       externalEntryShapeTheory.compile_abi_dec_addr_labels,
       exprSimConvertTheory.straight_fresh_extends,
       abiDecodePtrPositionTheory.abi_decode_ge_guard_straight_fresh,
       pairTheory.SND]) >>
  `fn_has_code start slot_end fn` by
    metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans] >>
  drule_all (BETA_RULE abi_decode_member_slot_joint) >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `fn_has_code slot_end load_end fn` by
    metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans] >>
  `start.cs_next_var <= slot_end.cs_next_var` by
    (qpat_x_assum `emit_op ADD [src;Lit _] start = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[exprSimAccountsTheory.emit_op_extends_next_var, pairTheory.SND]) >>
  `not_fresh_at slot_end input /\ local_ptrs_reserved ce slot_end /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at slot_end x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at slot_end x)` by
    (qpat_x_assum `start.cs_next_var <= slot_end.cs_next_var` mp_tac >>
     qpat_x_assum `not_fresh_at start input` mp_tac >>
     qpat_x_assum `local_ptrs_reserved ce start` mp_tac >>
     qpat_x_assum `!x sz. ce.ce_return_buf = _ ==> not_fresh_at start x` mp_tac >>
     qpat_x_assum `!x sz. ce.ce_return_pc = _ ==> not_fresh_at start x` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[not_fresh_at_def, local_ptrs_reserved_next_var,
       arithmeticTheory.LESS_EQ_TRANS]) >>
  `allocas_from lo u` by
    (qpat_x_assum `?H. V H` strip_assume_tac >>
     qpat_x_assum `!H. V H ==> _` drule >>
     simp[bodyPtrDefsTheory.ghost_inv_at_def] >> metis_tac[]) >>
  `abi_decoder_coherent ce env sf ty tv` by
    (qpat_x_assum `LIST_REL _ _ _` mp_tac >> simp[LIST_REL_APPEND_EQ]) >>
  `off+ao+32 <= LENGTH input_bytes` by
    (drule abi_decoder_coherent_header >>
     drule abiDecoderDynamicTheory.abi_decoder_coherent_dynamic >>
     qpat_x_assum `dec_info_needs_offset _` mp_tac >>
     simp[abiDecoderOffsetTheory.abi_decoder_needs_offset_iff,
       abi_decoder_header_def, abiDecodeRangesTheory.abi_member_head_size_def] >> rpt strip_tac >> decide_tac) >>
  `(^owned_decoder_state) slot_end u Gf tnf` by
    (BETA_TAC >> asm_rewrite_tac[] >> metis_tac[]) >>
  pop_assum (assume_tac o BETA_RULE) >>
  `?out t Gl tnl.
    offset_val = Var out /\ not_fresh_at load_end out /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (u,Gf,tnf) [] (OK t,Gl,tnl)) /\
    eval_operand offset_val t = SOME (mload (w2n input_word+(off+ao)) u) /\
    op_prov Gl offset_val = NONE /\ op_taint tnl offset_val = {} /\
    ~t.vs_halted /\ t.vs_current_bb = load_end.cs_current_bb /\
    t.vs_inst_idx = LENGTH load_end.cs_current_insts /\
    t.vs_memory = u.vs_memory /\ t.vs_allocas = u.vs_allocas /\
    t.vs_alloca_next = u.vs_alloca_next /\ t.vs_labels = u.vs_labels /\
    tnl.t_mem = tnf.t_mem /\
    (^owned_decoder_state) load_end t Gl tnl /\
    (!x. not_fresh_at slot_end x ==>
      lookup_var x t = lookup_var x u /\ FLOOKUP Gl x = FLOOKUP Gf x /\
      op_taint tnl (Var x) = op_taint tnf (Var x))` by
    (BETA_TAC >> irule (BETA_RULE abi_decode_owned_relative_load) >>
     asm_rewrite_tac[] >>
     qexistsl_tac [`head_addr`,`head_ptr`,`addr_end`] >> asm_rewrite_tac[]) >>
  `slot_end.cs_next_var <= load_end.cs_next_var` by
    (qpat_x_assum `compile_abi_dec_addr _ _ _ = _` mp_tac >>
     qpat_x_assum `emit_op MLOAD _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[compile_abi_dec_addr_def] >>
     rpt strip_tac >> metis_tac[exprSimAccountsTheory.emit_op_extends_next_var,
       arithmeticTheory.LESS_EQ_TRANS, pairTheory.SND]) >>
  `!x. not_fresh_at start x ==> not_fresh_at slot_end x` by
    (simp[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `t.vs_labels = s.vs_labels` by
    metis_tac[gas_origin_ptr_path_preserves_labels] >>
  `!op. abi_decoder_operand_live start.cs_next_var op ==>
    eval_operand op t = eval_operand op s /\
    op_prov Gl op = op_prov G op /\ op_taint tnl op = op_taint tn op` by
    (qpat_x_assum `!x. not_fresh_at start x ==> lookup_var x u = _ /\ _` mp_tac >>
     qpat_x_assum `!x. not_fresh_at slot_end x ==> lookup_var x t = _ /\ _` mp_tac >>
     qpat_x_assum `!x. not_fresh_at start x ==> not_fresh_at slot_end x` mp_tac >>
     qpat_x_assum `t.vs_labels = s.vs_labels` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> Cases_on `op` >>
     gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       eval_operand_def, ptrDisciplineTheory.op_prov_def,
       ptrDisciplineTheory.op_taint_def, GSYM not_fresh_at_def] >> metis_tac[]) >>
  `eval_operand src t = SOME (n2w off) /\ op_prov Gl src = NONE /\
   op_taint tnl src = {}` by metis_tac[] >>
  `abi_decoder_operand_live load_end.cs_next_var src` by
    (qpat_x_assum `abi_decoder_operand_live start.cs_next_var src` mp_tac >>
     qpat_x_assum `start.cs_next_var <= slot_end.cs_next_var` mp_tac >>
     qpat_x_assum `slot_end.cs_next_var <= load_end.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `src` >>
     simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `fn_has_code load_end select_end fn` by
    metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans] >>
  `not_fresh_at load_end input /\ local_ptrs_reserved ce load_end /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at load_end x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at load_end x)` by
    (qpat_x_assum `slot_end.cs_next_var <= load_end.cs_next_var` mp_tac >>
     qpat_x_assum `not_fresh_at slot_end input` mp_tac >>
     qpat_x_assum `local_ptrs_reserved ce slot_end` mp_tac >>
     qpat_x_assum `!x sz. ce.ce_return_buf = _ ==> not_fresh_at slot_end x` mp_tac >>
     qpat_x_assum `!x sz. ce.ce_return_pc = _ ==> not_fresh_at slot_end x` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[not_fresh_at_def, local_ptrs_reserved_next_var,
       arithmeticTheory.LESS_EQ_TRANS]) >>
  `allocas_from lo t` by
    (qpat_x_assum `?H. V H` strip_assume_tac >>
     qpat_x_assum `(^owned_decoder_state) load_end t Gl tnl` mp_tac >>
     BETA_TAC >> strip_tac >>
     qpat_x_assum `!H. V H ==> _` drule >>
     simp[bodyPtrDefsTheory.ghost_inv_at_def] >> metis_tac[]) >>
  qpat_x_assum `(^owned_decoder_state) load_end t Gl tnl`
    (assume_tac o BETA_RULE) >>
  `(?z Gz tnz. !D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
     (t,Gl,tnl) [] (Abort Revert_abort z,Gz,tnz)) \/
   (?z Gz tnz.
     (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (t,Gl,tnl) [] (OK z,Gz,tnz)) /\
     ~z.vs_halted /\ z.vs_current_bb = select_end.cs_current_bb /\
     z.vs_inst_idx = LENGTH select_end.cs_current_insts /\
     (^owned_decoder_state) select_end z Gz tnz /\
     eval_operand elem_src z = SOME (n2w off+mload (w2n input_word+(off+ao)) u) /\
     w2n (n2w off:bytes32) <= w2n (n2w off+mload (w2n input_word+(off+ao)) u) /\
     op_prov Gz elem_src = NONE /\ op_taint tnz elem_src = {} /\
     (!x. not_fresh_at load_end x ==>
       lookup_var x z = lookup_var x t /\ FLOOKUP Gz x = FLOOKUP Gl x /\
       op_taint tnz (Var x) = op_taint tnl (Var x)))` by
    (BETA_TAC >> irule (BETA_RULE abi_decode_member_actual_joint) >>
     asm_rewrite_tac[] >>
     qexistsl_tac [`offset_val`,`actual_end`,`src`] >> asm_rewrite_tac[])
  >- (disj1_tac >> qexistsl_tac [`z`,`Gz`,`tnz`] >>
      qpat_x_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _` mp_tac >>
      qpat_x_assum `!D. gas_origin_ptr_path _ (u,Gf,tnf) _ _` mp_tac >>
      qpat_x_assum `!D. gas_origin_ptr_path _ (t,Gl,tnl) _ _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >>
      metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK z,Gz,tnz)` by
    (qpat_x_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _` mp_tac >>
     qpat_x_assum `!D. gas_origin_ptr_path _ (u,Gf,tnf) _ _` mp_tac >>
     qpat_x_assum `!D. gas_origin_ptr_path _ (t,Gl,tnl) _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans]) >>
  `!x. not_fresh_at start x ==>
    lookup_var x z = lookup_var x s /\ FLOOKUP Gz x = FLOOKUP G x /\
    op_taint tnz (Var x) = op_taint tn (Var x)` by
    (qpat_x_assum `!x. not_fresh_at start x ==> lookup_var x u = _ /\ _` mp_tac >>
     qpat_x_assum `!x. not_fresh_at slot_end x ==> lookup_var x t = _ /\ _` mp_tac >>
     qpat_x_assum `!x. not_fresh_at load_end x ==> lookup_var x z = _ /\ _` mp_tac >>
     qpat_x_assum `start.cs_next_var <= slot_end.cs_next_var` mp_tac >>
     qpat_x_assum `slot_end.cs_next_var <= load_end.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  `z.vs_labels = s.vs_labels` by metis_tac[gas_origin_ptr_path_preserves_labels] >>
  `eval_operand hi z = SOME (n2w h)` by
    (qpat_x_assum `eval_operand hi s = _` mp_tac >>
     qpat_x_assum `abi_decoder_operand_live _ hi` mp_tac >>
     qpat_x_assum `!x. not_fresh_at start x ==> lookup_var x z = _ /\ _` mp_tac >>
     qpat_x_assum `z.vs_labels = s.vs_labels` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `hi` >>
     simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       not_fresh_at_def, eval_operand_def] >> metis_tac[]) >>
  disj2_tac >> qexistsl_tac [`z`,`Gz`,`tnz`,
    `w2n (n2w off+mload (w2n input_word+(off+ao)) u:bytes32)`,`h`] >>
  asm_rewrite_tac[wordsTheory.n2w_w2n, wordsTheory.w2n_lt] >>
  qpat_x_assum `(^owned_decoder_state) select_end z Gz tnz`
    (assume_tac o BETA_RULE) >>
  BETA_TAC >> asm_rewrite_tac[] >>
  strip_tac >> gvs[abiEncoderTheory.dec_info_needs_offset_def]
QED

Theorem abi_decode_member_tail_frame[local]:
  !finish Gt.
  (^bounded_member_entry) dst src opc base_op hi elems ao vo env sf
    pretys pretvs (ty::tys) (tv::tvs) live protected start finish s G tn d /\
  cs_extends start tail_start /\
  start.cs_next_var <= tail_start.cs_next_var /\
  start.cs_next_id <= tail_start.cs_next_id /\
  compile_abi_decode_complex_elems dst src opc base_op hi
    (abi_decoder_member_infos sf ce tys)
    (ao+abi_embedded_static_size ce.ce_struct_fields ty)
    (vo+type_memory_bytes ce ty) tail_start = ((),finish) /\
  ~t.vs_halted /\ t.vs_current_bb = tail_start.cs_current_bb /\
  t.vs_inst_idx = LENGTH tail_start.cs_current_insts /\
  (^owned_decoder_state) tail_start t Gt tnt /\
  t.vs_labels = s.vs_labels /\
  (!x. not_fresh_at start x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP Gt x = FLOOKUP G x /\
    op_taint tnt (Var x) = op_taint tn (Var x)) ==>
  (^bounded_member_entry) dst src opc base_op hi
    (abi_decoder_member_infos sf ce tys)
    (ao+abi_embedded_static_size ce.ce_struct_fields ty)
    (vo+type_memory_bytes ce ty) env sf (pretys++[ty]) (pretvs++[tv])
    tys tvs live protected tail_start finish t Gt tnt d
Proof
  gen_tac >> qx_gen_tac `gfinal` >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!op. abi_decoder_operand_live start.cs_next_var op ==>
    eval_operand op t = eval_operand op s /\
    op_prov gfinal op = op_prov G op /\ op_taint tnt op = op_taint tn op` by
    (qpat_x_assum `!x. not_fresh_at start x ==> _` mp_tac >>
     qpat_x_assum `t.vs_labels = s.vs_labels` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp_tac (srw_ss()) [not_fresh_at_def, ptrDisciplineTheory.op_taint_def] >>
     rpt strip_tac >> Cases_on `op` >>
     gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       eval_operand_def, ptrDisciplineTheory.op_prov_def,
       ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  `!op. abi_decoder_operand_live start.cs_next_var op ==>
    abi_decoder_operand_live tail_start.cs_next_var op` by
    (Cases >> simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     rpt strip_tac >> gvs[not_fresh_at_def] >> decide_tac) >>
  `local_ptrs_reserved ce tail_start` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `cs_extends tail_start finish'` by
    (qpat_x_assum `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ tail_start = _`
       (mp_tac o AP_TERM ``SND : unit # compile_state -> compile_state``) >>
     simp_tac std_ss [] >> disch_then (SUBST1_TAC o SYM) >>
     metis_tac[cj 2 externalEntryShapeTheory.compile_abi_decode_labels]) >>
  `fn_has_code tail_start finish' fn` by metis_tac[fragExecTheory.fn_has_code_split] >>
  simp[MAP_APPEND, SUM_APPEND, APPEND_ASSOC] >>
  (conj_tac >- (pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> asm_rewrite_tac[])) >>
  (conj_tac >-
    (qpat_x_assum `?off h. _ /\ _ /\ off+ao+_ <= h /\ _` mp_tac >>
     qpat_x_assum `ao = _` mp_tac >> rpt (pop_assum kall_tac) >>
     simp_tac (srw_ss()) [MAP, SUM] >> rpt strip_tac >>
     qexistsl_tac [`off`,`h`] >> simp[] >> decide_tac)) >>
  (conj_tac >-
    (qpat_x_assum `?p. dst = Var p /\ _` strip_assume_tac >>
     qexists_tac `p` >> gvs[] >>
     `not_fresh_at start p` by
       gvs[not_fresh_at_def, abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     fs[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM])) >>
  simp[] >>
  qpat_x_assum `vo = _` mp_tac >>
  qpat_x_assum `d + vo + _ <= output_base + output_cap` mp_tac >>
  qpat_x_assum `w2n input_word + LENGTH input_bytes <= d+vo \/ _` mp_tac >>
  qpat_x_assum `EVERY (\(aid,p,b,k,bytes). aid < start.cs_next_id /\ (b+k <= d+vo \/ _)) live` mp_tac >>
  qpat_x_assum `EVERY (\(a,bytes). a+LENGTH bytes <= d+vo \/ _) protected` mp_tac >>
  qpat_x_assum `start.cs_next_id <= tail_start.cs_next_id` mp_tac >>
  qpat_x_assum `!aid off sz. _ ==> off+sz <= t.vs_alloca_next` mp_tac >>
  qpat_x_assum `!name b sz. _ ==> b+sz <= t.vs_alloca_next` mp_tac >>
  qpat_x_assum `!name b k. local_region ce es.scopes t name b k ==> _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  simp_tac (srw_ss()) [MAP, SUM, EVERY_MEM] >>
  rpt strip_tac >>
  gvs[] >>
  FIRST [decide_tac, metis_tac[],
    (PairCases_on `e` >> gvs[] >>
     first_x_assum drule >> simp_tac (srw_ss()) [] >>
     rpt strip_tac >> decide_tac)]
QED

Theorem abi_decode_member_prefix_joint:
  !finish. (^bounded_member_entry) dst src opc base_op hi elems ao vo env sf
    pretys pretvs (ty::tys) (tv::tvs) live protected start finish s G tn d ==>
  ?elem_src elem_dst select_end head_start tail_start.
    compile_getelemptr_abi src
      (dec_info_needs_offset (type_to_abi_dec_info sf ce ty)) ao opc base_op hi
      start = (elem_src,select_end) /\
    emit_op ADD [dst;Lit (n2w vo)] select_end = (elem_dst,head_start) /\
    compile_abi_decode_to_buf elem_dst elem_src opc base_op hi
      (type_to_abi_dec_info sf ce ty) head_start = ((),tail_start) /\
    compile_abi_decode_complex_elems dst src opc base_op hi
      (abi_decoder_member_infos sf ce tys)
      (ao+abi_embedded_static_size ce.ce_struct_fields ty)
      (vo+type_memory_bytes ce ty) tail_start = ((),finish) /\
    ((?rstate Gr tnr. !D. gas_origin_ptr_path
        (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (Abort Revert_abort rstate,Gr,tnr)) \/
     (?u Gu tnu.
       (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
         (s,G,tn) [] (OK u,Gu,tnu)) /\
       (^guarded_to_buf_entry) elem_dst elem_src opc base_op hi
         (type_to_abi_dec_info sf ce ty) env sf ty tv live protected
         head_start tail_start u Gu tnu (d+vo) /\
       start.cs_next_var <= head_start.cs_next_var /\
       (!x. not_fresh_at start x ==>
         lookup_var x u = lookup_var x s /\ FLOOKUP Gu x = FLOOKUP G x /\
         op_taint tnu (Var x) = op_taint tn (Var x)) /\
       (!t Gt tnt.
         (!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
           (u,Gu,tnu) [] (OK t,Gt,tnt)) /\
         ~t.vs_halted /\ t.vs_current_bb = tail_start.cs_current_bb /\
         t.vs_inst_idx = LENGTH tail_start.cs_current_insts /\
         (^owned_decoder_state) tail_start t Gt tnt /\
         (!x. not_fresh_at head_start x ==>
           lookup_var x t = lookup_var x u /\ FLOOKUP Gt x = FLOOKUP Gu x /\
           op_taint tnt (Var x) = op_taint tnu (Var x)) ==>
         (^bounded_member_entry) dst src opc base_op hi
           (abi_decoder_member_infos sf ce tys)
           (ao+abi_embedded_static_size ce.ce_struct_fields ty)
           (vo+type_memory_bytes ce ty) env sf (pretys++[ty]) (pretvs++[tv])
           tys tvs live protected tail_start finish t Gt tnt d /\
         (!x. not_fresh_at start x ==>
           lookup_var x t = lookup_var x s /\ FLOOKUP Gt x = FLOOKUP G x /\
           op_taint tnt (Var x) = op_taint tn (Var x)))))
Proof
  gen_tac >> BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `(^bounded_member_entry) dst src opc base_op hi elems ao vo env sf
    pretys pretvs (ty::tys) (tv::tvs) live protected start finish' s G tn d` by
    (BETA_TAC >> asm_rewrite_tac[]) >>
  qpat_x_assum `elems = _` SUBST_ALL_TAC >>
  qpat_assum `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_decoder_member_infos_def, MAP] >>
  rewrite_tac [Once compile_abi_decode_to_buf_def] >>
  simp_tac bool_ss [comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> first_assum (fn th => CONV_TAC (LAND_CONV (REWRITE_CONV [th]))) >>
  simp_tac std_ss [] >>
  pairarg_tac >> first_assum (fn th => CONV_TAC (LAND_CONV (REWRITE_CONV [th]))) >>
  simp_tac std_ss [] >>
  pairarg_tac >> first_assum (fn th => CONV_TAC (LAND_CONV (REWRITE_CONV [th]))) >>
  simp_tac std_ss [] >>
  strip_tac >>
  rename1 `compile_getelemptr_abi _ _ _ _ _ _ _ = (elem_src,select_end)` >>
  rename1 `emit_op ADD _ select_end = (elem_dst,head_start)` >>
  rename1 `compile_abi_decode_to_buf elem_dst elem_src _ _ _ _ head_start = (head_result,tail_start)` >>
  Cases_on `head_result` >>
  qexistsl_tac [`elem_src`,`elem_dst`,`select_end`,`head_start`,`tail_start`] >>
  (conj_tac >- asm_rewrite_tac[]) >>
  (conj_tac >- asm_rewrite_tac[]) >>
  (conj_tac >- asm_rewrite_tac[]) >>
  (conj_tac >- asm_rewrite_tac[abi_decoder_member_infos_def]) >>
  `cs_extends start select_end` by
    (qpat_x_assum `compile_getelemptr_abi _ _ _ _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[externalEntryShapeTheory.compile_getelemptr_abi_labels, pairTheory.SND]) >>
  `cs_extends select_end head_start` by
    (qpat_x_assum `emit_op ADD _ select_end = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[exprSimAccountsTheory.emit_op_extends_next_var]) >>
  `cs_extends head_start tail_start /\ cs_extends tail_start finish'` by
    (qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ head_start = _` mp_tac >>
     qpat_x_assum `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ tail_start = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[externalEntryShapeTheory.compile_abi_decode_labels, pairTheory.SND]) >>
  `fn_has_code start select_end fn /\ fn_has_code select_end head_start fn /\
   fn_has_code head_start tail_start fn` by
    metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans] >>
  qpat_x_assum `(^bounded_member_entry) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  disch_then (fn th => assume_tac th >> mp_tac th) >>
  disch_then (mp_then (Pos hd) mp_tac abi_decode_member_select_joint) >>
  disch_then (qspecl_then [`select_end`,`explicit`,`elem_src`,`PG`] mp_tac) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then strip_assume_tac
  >- (disj1_tac >> qexistsl_tac [`rstate`,`Gr`,`tnr`] >> asm_rewrite_tac[]) >>
  rename1 `eval_operand elem_src selected = SOME (n2w q)` >>
  rename1 `(^owned_decoder_state) select_end selected Gs tns` >>
  `start.cs_next_var <= select_end.cs_next_var /\
   select_end.cs_next_var <= head_start.cs_next_var` by
    (conj_tac
     >- (qpat_x_assum `compile_getelemptr_abi _ _ _ _ _ _ _ = _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         strip_tac >> drule abiDecoderReentryPointerTheory.abi_decoder_member_pointer_counters >>
         simp[]) >>
     qpat_x_assum `emit_op ADD _ select_end = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[exprSimAccountsTheory.emit_op_extends_next_var]) >>
  `local_ptrs_reserved ce select_end` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `start` >> asm_rewrite_tac[]) >>
  `selected.vs_labels = s.vs_labels` by
    (qpat_x_assum `!D. gas_origin_ptr_path _ _ [] (OK selected,_,_)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[gas_origin_ptr_path_preserves_labels]) >>
  `!op. abi_decoder_operand_live start.cs_next_var op ==>
    eval_operand op selected = eval_operand op s /\
    op_prov Gs op = op_prov G op /\ op_taint tns op = op_taint tn op` by
    (qpat_x_assum `!x. not_fresh_at start x ==> lookup_var x selected = _ /\ _` mp_tac >>
     qpat_x_assum `selected.vs_labels = s.vs_labels` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> Cases_on `op` >>
     gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       eval_operand_def, ptrDisciplineTheory.op_prov_def,
       ptrDisciplineTheory.op_taint_def, GSYM not_fresh_at_def]) >>
  `abi_decoder_coherent ce env sf ty tv` by
    (qpat_x_assum `LIST_REL _ _ _` mp_tac >>
     simp[LIST_REL_APPEND_EQ, LIST_REL_CONS1]) >>
  `type_memory_bytes ce ty = type_memory_size tv` by
    (drule abi_decoder_coherent_header >> simp[abi_decoder_header_def]) >>
  qpat_x_assum `?p. dst = Var p /\ _` strip_assume_tac >>
  qpat_x_assum `dst = Var p` SUBST_ALL_TAC >>
  `?out. elem_dst = Var out` by
    (qpat_x_assum `emit_op ADD _ select_end = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[emit_op_facts]) >>
  qpat_x_assum `elem_dst = Var out` SUBST_ALL_TAC >>
  `not_fresh_at start p` by
    (qpat_x_assum `abi_decoder_operand_live start.cs_next_var (Var p)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `lookup_var p selected = SOME (n2w d) /\
   op_taint tns (Var p) = {}` by
    (simp[GSYM eval_operand_def] >> metis_tac[]) >>
  `ptr_covers Gs tns p selected
     (vo + SUM (MAP (type_memory_bytes ce) (ty::tys)))` by
    (qpat_x_assum `ptr_covers G tn p s _` mp_tac >>
     qpat_x_assum `!x. not_fresh_at start x ==> lookup_var x selected = _ /\ _` mp_tac >>
     qpat_x_assum `not_fresh_at start p` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[]) >>
  `vo + type_memory_size tv <= vo + SUM (MAP (type_memory_bytes ce) (ty::tys)) /\
   w2n (n2w d : bytes32) + (vo + SUM (MAP (type_memory_bytes ce) (ty::tys))) < dimword (:256)` by
    (qpat_x_assum `d+vo+_ <= output_base+output_cap` mp_tac >>
     qpat_x_assum `output_base+output_cap < dimword (:256)` mp_tac >>
     qpat_x_assum `type_memory_bytes ce ty = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[MAP, SUM] >> rpt strip_tac >>
     `d < dimword (:256)` by decide_tac >> simp[w2n_n2w] >> decide_tac) >>
  `not_fresh_at select_end input` by
    (qpat_x_assum `base_op = Var input` mp_tac >>
     qpat_x_assum `abi_decoder_operand_live start.cs_next_var base_op` mp_tac >>
     qpat_x_assum `start.cs_next_var <= select_end.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
     rpt strip_tac >> gvs[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `allocas_from lo selected` by
    (qpat_x_assum `(^owned_decoder_state) select_end selected Gs tns`
       (assume_tac o BETA_RULE) >>
     qpat_x_assum `?H. V H` mp_tac >>
     pop_assum mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp[bodyPtrDefsTheory.ghost_inv_at_def] >> metis_tac[]) >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at select_end x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at select_end x)` by
    (qpat_x_assum `!x sz. ce.ce_return_buf = _ ==> _` mp_tac >>
     qpat_x_assum `!x sz. ce.ce_return_pc = _ ==> _` mp_tac >>
     qpat_x_assum `origin.cs_next_var <= start.cs_next_var` mp_tac >>
     qpat_x_assum `start.cs_next_var <= select_end.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `?u Gu tnu.
     (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
       (selected,Gs,tns) [] (OK u,Gu,tnu)) /\
     ptr_covers Gu tnu out u (type_memory_size tv) /\
     lookup_var out u = SOME (n2w d+n2w vo) /\
     FLOOKUP Gu out = FLOOKUP Gs p /\
     ~u.vs_halted /\ u.vs_current_bb = head_start.cs_current_bb /\
     u.vs_inst_idx = LENGTH head_start.cs_current_insts /\
     (^owned_decoder_state) head_start u Gu tnu /\
     (!x. not_fresh_at select_end x ==>
       lookup_var x u = lookup_var x selected /\ FLOOKUP Gu x = FLOOKUP Gs x /\
       op_taint tnu (Var x) = op_taint tns (Var x))` by
    (BETA_TAC >> irule (BETA_RULE abi_decode_member_destination_owned) >>
     qpat_assum `(^owned_decoder_state) select_end selected Gs tns`
       (assume_tac o BETA_RULE) >>
     asm_rewrite_tac[] >>
     conj_tac >-
       (qexists_tac `Lit (n2w vo)` >>
        simp[eval_operand_def, ptrDisciplineTheory.op_taint_def]) >>
     qexists_tac `vo + SUM (MAP (type_memory_bytes ce) (ty::tys))` >>
     simp[]) >>
  pop_assum strip_assume_tac >>
  `u.vs_labels = selected.vs_labels` by
    (qpat_x_assum `!D. gas_origin_ptr_path _ (selected,_,_) [] (OK u,_,_)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[gas_origin_ptr_path_preserves_labels]) >>
  `!op. abi_decoder_operand_live select_end.cs_next_var op ==>
    eval_operand op u = eval_operand op selected /\
    op_prov Gu op = op_prov Gs op /\ op_taint tnu op = op_taint tns op` by
    (qpat_x_assum `!x. not_fresh_at select_end x ==> lookup_var x u = _ /\ _` mp_tac >>
     qpat_x_assum `u.vs_labels = selected.vs_labels` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> Cases_on `op` >>
     gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       eval_operand_def, ptrDisciplineTheory.op_prov_def,
       ptrDisciplineTheory.op_taint_def, GSYM not_fresh_at_def]) >>
  `abi_decoder_operand_live select_end.cs_next_var elem_src` by
    (qpat_x_assum `compile_getelemptr_abi _ _ _ _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[abiDecoderReentryPointerTheory.abi_decoder_member_pointer_counters]) >>
  `abi_decoder_operand_live select_end.cs_next_var hi /\
   abi_decoder_operand_live select_end.cs_next_var (Var input)` by
    (qpat_x_assum `base_op = Var input` mp_tac >>
     qpat_x_assum `abi_decoder_operand_live start.cs_next_var base_op` mp_tac >>
     qpat_x_assum `abi_decoder_operand_live start.cs_next_var hi` mp_tac >>
     qpat_x_assum `start.cs_next_var <= select_end.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[abi_decoder_operand_live_mono]) >>
  `FLOOKUP Gu out = SOME (output_base,output_cap)` by
    (qpat_x_assum `FLOOKUP Gu out = _` mp_tac >>
     qpat_x_assum `FLOOKUP G p = SOME _` mp_tac >>
     qpat_x_assum `not_fresh_at start p` mp_tac >>
     qpat_x_assum `!x. not_fresh_at start x ==> lookup_var x selected = _ /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  disj2_tac >> qexistsl_tac [`u`,`Gu`,`tnu`] >>
  (conj_tac >-
    (qpat_x_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK selected,_,_)` mp_tac >>
     qpat_x_assum `!D. gas_origin_ptr_path _ (selected,_,_) [] (OK u,_,_)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[gas_origin_ptr_path_trans])) >>
  (conj_tac >-
    (BETA_TAC >>
     qpat_assum `(^owned_decoder_state) head_start u Gu tnu`
       (assume_tac o BETA_RULE) >>
     asm_rewrite_tac[eval_operand_def, GSYM word_add_n2w] >>
     (conj_tac >-
       (qexistsl_tac [`q`,`h`] >>
        qpat_x_assum `!op. abi_decoder_operand_live select_end.cs_next_var op ==> _` mp_tac >>
        qpat_x_assum `abi_decoder_operand_live select_end.cs_next_var elem_src` mp_tac >>
        qpat_x_assum `abi_decoder_operand_live select_end.cs_next_var hi` mp_tac >>
        qpat_x_assum `eval_operand elem_src selected = _` mp_tac >>
        qpat_x_assum `eval_operand hi selected = _` mp_tac >>
        qpat_x_assum `q < dimword (:256)` mp_tac >>
        qpat_x_assum `h <= LENGTH input_bytes` mp_tac >>
        qpat_x_assum `(?clamp. _ = DecPrimWord clamp) ==> _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> metis_tac[])) >>
     (conj_tac >-
       (irule local_ptrs_reserved_next_var >> qexists_tac `select_end` >> simp[])) >>
     simp[] >>
     (conj_tac >-
       (qexistsl_tac [`q`,`h`] >> simp[])) >>
     (conj_tac >-
       (qpat_x_assum `ptr_covers Gu tnu out u _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        simp[bodyPtrDefsTheory.ptr_covers_def])) >>
     (conj_tac >-
       (qpat_x_assum `!op. abi_decoder_operand_live start.cs_next_var op ==> _` mp_tac >>
        qpat_x_assum `abi_decoder_operand_live start.cs_next_var base_op` mp_tac >>
        qpat_x_assum `op_taint tn base_op = {}` mp_tac >>
        qpat_x_assum `base_op = Var input` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> metis_tac[])) >>
     (conj_tac >-
       (qpat_x_assum `emit_op ADD _ select_end = _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        strip_tac >> drule loweringShapeRulesTheory.emit_op_facts >>
        simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
          GSYM not_fresh_at_def])) >>
     (conj_tac >-
       (qpat_x_assum `abi_decoder_operand_live select_end.cs_next_var elem_src` mp_tac >>
        qpat_x_assum `select_end.cs_next_var <= head_start.cs_next_var` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> metis_tac[abi_decoder_operand_live_mono])) >>
     (conj_tac >-
       (qpat_x_assum `abi_decoder_operand_live select_end.cs_next_var (Var input)` mp_tac >>
        qpat_x_assum `select_end.cs_next_var <= head_start.cs_next_var` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> metis_tac[abi_decoder_operand_live_mono])) >>
     (conj_tac >-
       (qpat_x_assum `abi_decoder_operand_live select_end.cs_next_var hi` mp_tac >>
        qpat_x_assum `select_end.cs_next_var <= head_start.cs_next_var` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> metis_tac[abi_decoder_operand_live_mono])) >>
     qpat_x_assum `EVERY (\(aid,p,b,k,bytes). aid < start.cs_next_id /\ (b + k <= d + vo \/ _)) live` mp_tac >>
     qpat_x_assum `EVERY (\(a,bytes). a + LENGTH bytes <= d + vo \/ _) protected` mp_tac >>
     qpat_x_assum `vo = _` mp_tac >>
     qpat_x_assum `type_memory_bytes ce ty = type_memory_size tv` mp_tac >>
     qpat_x_assum `alloca_history fn u /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[EVERY_MEM, pairTheory.FORALL_PROD] >>
     rpt strip_tac >> res_tac >> gvs[] >> decide_tac)) >>
  (conj_tac >- decide_tac) >>
  (conj_tac >-
    (qpat_x_assum `!x. not_fresh_at start x ==> lookup_var x selected = _ /\ _` mp_tac >>
     qpat_x_assum `!x. not_fresh_at select_end x ==> lookup_var x u = _ /\ _` mp_tac >>
     qpat_x_assum `start.cs_next_var <= select_end.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[not_fresh_at_def, arithmeticTheory.LE_TRANS])) >>
  rpt gen_tac >> disch_then strip_assume_tac >>
  `t.vs_labels = u.vs_labels` by
    (qpat_x_assum `!H. V H ==> gas_origin_ptr_path _ _ [] (OK t,_,_)` mp_tac >>
     qpat_x_assum `?H. V H` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[gas_origin_ptr_path_preserves_labels]) >>
  `!x. not_fresh_at start x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP Gt' x = FLOOKUP G x /\
    op_taint tnt (Var x) = op_taint tn (Var x)` by
    (qpat_x_assum `!x. not_fresh_at head_start x ==> lookup_var x t = _ /\ _` mp_tac >>
     qpat_x_assum `!x. not_fresh_at select_end x ==> lookup_var x u = _ /\ _` mp_tac >>
     qpat_x_assum `!x. not_fresh_at start x ==> lookup_var x selected = _ /\ _` mp_tac >>
     qpat_x_assum `start.cs_next_var <= select_end.cs_next_var` mp_tac >>
     qpat_x_assum `select_end.cs_next_var <= head_start.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[not_fresh_at_def, arithmeticTheory.LE_TRANS]) >>
  `!op. abi_decoder_operand_live start.cs_next_var op ==>
    eval_operand op t = eval_operand op s /\
    op_prov Gt' op = op_prov G op /\ op_taint tnt op = op_taint tn op` by
    (qpat_x_assum `!x. not_fresh_at start x ==> lookup_var x t = _ /\ _` mp_tac >>
     qpat_x_assum `t.vs_labels = u.vs_labels` mp_tac >>
     qpat_x_assum `u.vs_labels = selected.vs_labels` mp_tac >>
     qpat_x_assum `selected.vs_labels = s.vs_labels` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> Cases_on `op` >>
     gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       eval_operand_def, ptrDisciplineTheory.op_prov_def,
       ptrDisciplineTheory.op_taint_def, GSYM not_fresh_at_def]) >>
  BETA_TAC >>
  reverse conj_tac >- simp[] >>
  asm_rewrite_tac[MAP_APPEND, SUM_APPEND, LIST_REL_APPEND_EQ,
    APPEND_ASSOC, APPEND, MAP, SUM, LENGTH_APPEND, LENGTH] >>
  `eval_operand src t = eval_operand src s /\
   eval_operand hi t = eval_operand hi s /\
   eval_operand (Var p) t = eval_operand (Var p) s /\
   op_prov Gt' src = op_prov G src /\ op_prov Gt' hi = op_prov G hi /\
   op_taint tnt src = op_taint tn src /\ op_taint tnt hi = op_taint tn hi /\
   op_taint tnt (Var p) = op_taint tn (Var p) /\
   op_taint tnt base_op = op_taint tn base_op` by
    (qpat_x_assum `!op. abi_decoder_operand_live start.cs_next_var op ==> eval_operand op t = _ /\ _` mp_tac >>
     map_every (fn q => qpat_x_assum q mp_tac)
       [`abi_decoder_operand_live start.cs_next_var src`,
        `abi_decoder_operand_live start.cs_next_var hi`,
        `abi_decoder_operand_live start.cs_next_var (Var p)`,
        `abi_decoder_operand_live start.cs_next_var base_op`] >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  asm_rewrite_tac[GSYM APPEND_ASSOC, APPEND, arithmeticTheory.ADD_CLAUSES] >>
  (conj_tac >-
    (qpat_x_assum `?off h. eval_operand src s = _ /\ eval_operand hi s = _ /\ off + ao + _ <= h /\ _` mp_tac >>
     qpat_x_assum `ao = _` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >> qexistsl_tac [`off`,`h`] >>
     gvs[MAP, SUM] >> decide_tac)) >>
  (conj_tac >-
    (qpat_x_assum `fn_has_code start finish' fn` mp_tac >>
     qpat_x_assum `cs_extends start select_end` mp_tac >>
     qpat_x_assum `cs_extends select_end head_start` mp_tac >>
     qpat_x_assum `cs_extends head_start tail_start` mp_tac >>
     qpat_x_assum `cs_extends tail_start finish'` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans])) >>
  `head_start.cs_next_var <= tail_start.cs_next_var` by
    (qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ head_start = _` mp_tac >>
     qspecl_then [`Var out`,`elem_src`,`opc`,`base_op`,`hi`,
       `type_to_abi_dec_info sf ce ty`,`head_start`] mp_tac (cj 1 ci_mono_compile_abi_decode) >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[ci_mono_def]) >>
  `start.cs_next_var <= tail_start.cs_next_var` by decide_tac >>
  (conj_tac >-
    (irule local_ptrs_reserved_next_var >> qexists_tac `start` >> simp[])) >>
  (conj_tac >-
    (qexists_tac `p` >> simp[] >>
     qpat_x_assum `!x. not_fresh_at start x ==> lookup_var x t = _ /\ _` mp_tac >>
     qpat_x_assum `not_fresh_at start p` mp_tac >>
     qpat_x_assum `ptr_covers G tn p s _` mp_tac >>
     qpat_x_assum `FLOOKUP G p = SOME _` mp_tac >>
     qpat_x_assum `vo = _` mp_tac >>
     qpat_x_assum `type_memory_bytes ce ty = type_memory_size tv` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[bodyPtrDefsTheory.ptr_covers_def, MAP, SUM] >> metis_tac[])) >>
  (conj_tac >- metis_tac[]) >>
  (conj_tac >- metis_tac[abi_decoder_operand_live_mono]) >>
  (conj_tac >- metis_tac[abi_decoder_operand_live_mono]) >>
  (conj_tac >- metis_tac[abi_decoder_operand_live_mono]) >>
  (conj_tac >- metis_tac[abi_decoder_operand_live_mono]) >>
  `!H. V H ==> ghost_kept_at lo ce es0 origin G0 tn0 s0 Gt' tnt` by
    (qpat_x_assum `!H. V H ==> stmt_state_rel _ _ _ _ _ _ t /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  asm_rewrite_tac[] >>
  qpat_x_assum `EVERY (\(aid,p,b,k,bytes). aid < tail_start.cs_next_id /\ FLOOKUP t.vs_allocas aid = _ /\ _) live` mp_tac >>
  qpat_x_assum `EVERY (\(aid,p,b,k,bytes). aid < start.cs_next_id /\ (b + k <= d + vo \/ _)) live` mp_tac >>
  qpat_x_assum `EVERY (\(a,bytes). a + LENGTH bytes <= d + vo \/ _) protected` mp_tac >>
  qpat_x_assum `d + vo + SUM _ <= output_base + output_cap` mp_tac >>
  qpat_x_assum `w2n input_word + LENGTH input_bytes <= d + vo \/ _` mp_tac >>
  qpat_x_assum `vo = _` mp_tac >>
  qpat_x_assum `type_memory_bytes ce ty = type_memory_size tv` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[EVERY_MEM, pairTheory.FORALL_PROD, MAP, SUM] >>
  rpt strip_tac >> res_tac >> gvs[] >> decide_tac
QED
