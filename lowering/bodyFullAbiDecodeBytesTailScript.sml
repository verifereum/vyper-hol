Theory bodyFullAbiDecodeBytesTail
Ancestors
  bodyFullAbiDecodeLeafCases bodyFullAbiDecodeCopyFrame
  bodyFullAbiDecodeOwnedCopy bodyFullAbiDecodeTailAdd bodyFullAbiDecodeFiniteGuard
  bodyPtrBopScalarCompile gasOriginPtrLabels contractABI vyperTypeABI
  allocaHistory abiDecodePtrMemberFrame bodyPtrDefs bodyFullGhostFrame
  loweringStateRelDefs
  abiDecoderBytesPhases abiDecoderBytesRuntime abiDecodePtrBytesTail
  bodyFullAbiDecodeAge bodyPtrBopScalarOutcome bodyPtrBopScalarSeq
  instSeqPtrLo freshWrites exprLoweringProps emitHelperProps
  ptrDiscipline fragGasSeqPtr fragGasOriginPtrDead fragGasOriginPtrLoop stateFrame fragExecMem
  emitHelper compileEnv venomState venomExecSemantics venomInst
  words arithmetic list rich_list finite_map pred_set

(* The actual tail entry supplies operand age, not global SSA freshness. *)
Theorem abi_decode_tail_round_run[local]:
  emit_op ADD [cnt;Lit 31w] sa = (up,c1) /\
  emit_op NOT [Lit 31w] c1 = (mask,c2) /\
  emit_op AND [up;mask] c2 = (rounded,sb) /\
  eval_operand cnt s = SOME (n2w c) /\ c+31 < dimword(:256) /\
  abi_decoder_operand_live sa.cs_next_var cnt ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand rounded t = SOME (n2w (32*((c+31) DIV 32)))
Proof
  simp[emit_op_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >> strip_tac >> gvs[] >>
  simp_tac (srw_ss()) [emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp_tac (srw_ss()) [DROP_LENGTH_APPEND] >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure1_def, exec_pure2_def, eval_operand_def,
       lookup_var_update_var, eval_operand_update_other,
       ASCIInumbersTheory.toString_inj, abi_decode_bytes_round_word]
QED

Theorem abi_decode_tail_round_joint[local]:
  emit_op ADD [cnt;Lit 31w] sa = (up,c1) /\
  emit_op NOT [Lit 31w] c1 = (mask,c2) /\
  emit_op AND [up;mask] c2 = (rounded,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand cnt s = SOME (n2w c) /\ c+31 < dimword(:256) /\
  abi_decoder_operand_live sa.cs_next_var cnt /\
  op_prov G cnt = NONE /\ op_taint tn cnt = {} /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand rounded t = SOME (n2w (32*((c+31) DIV 32))) /\
    op_prov Gf rounded = NONE /\ op_taint tnf rounded = {} /\
    state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all abi_decode_tail_round_run >> strip_tac >>
  `bop_scalar_seq {x | not_fresh_at sa x} {cnt;Lit 31w}
    (emitted_insts sa sb) (rounded INSERT mask INSERT up INSERT {cnt;Lit 31w})` by
    (irule abi_decode_bytes_round_scalar >> simp[] >> metis_tac[]) >>
  `!op. op IN {cnt;Lit 31w} ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    (rpt strip_tac >> gvs[op_prov_def, op_taint_def]) >>
  drule_all (bop_scalar_seq_run |> Q.INST [`D` |-> `<|d_stor := K (K {});
    d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`]) >>
  disch_then (qspecl_then [`fn`, `PG`] strip_assume_tac) >>
  `inst_seq_ptr <|d_stor := K (K {}); d_trans := K (K {});
    d_imm := K {}; d_ret := K {}|> lo ctx fn PG G tn
    (emitted_insts sa sb) s G' tn'` by
    (irule inst_seq_ptr_zero_to_lo >> simp[] >>
     qexists_tac `<|d_stor := K (K {}); d_trans := K (K {});
       d_imm := K {}; d_ret := K {}|>` >> simp[]) >>
  qpat_x_assum `inst_seq_ptr _ 0 _ _ _ _ _ _ _ _ _` kall_tac >>
  `inst_extends sa c1 /\ inst_extends c1 c2 /\ inst_extends c2 sb` by
    metis_tac[inst_extends_emit_op] >>
  `inst_extends sa sb` by metis_tac[inst_extends_trans] >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (map_every (fn pat => qpat_assum pat
      (mp_then Any strip_assume_tac loweringShapeRulesTheory.emit_op_facts))
      [`emit_op ADD _ sa = _`, `emit_op NOT _ c1 = _`, `emit_op AND _ c2 = _`] >>
     metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
     i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    metis_tac[bop_scalar_seq_opcodes] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    metis_tac[bop_scalar_seq_mem_ok] >>
  drule_all emitted_origin_ptr_path >>
  disch_then (qspec_then `explicit` assume_tac) >>
  drule_all bop_scalar_seq_runtime_frame >> strip_tac >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sb.cs_current_insts`, `G'`, `tn'`] >>
  conj_tac >- (gen_tac >> irule gas_origin_ptr_path_from_no_dead >> asm_rewrite_tac[]) >>
  `eval_operand rounded (t with vs_inst_idx := LENGTH sb.cs_current_insts) =
    eval_operand rounded t` by
    (Cases_on `rounded` >> simp[NoAsms, eval_operand_def, lookup_var_def]) >>
  simp[] >>
  qpat_x_assum `t = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
  simp[state_frame_def, lookup_var_def, op_taint_def] >> metis_tac[]
QED

(* Identical syntactic owned-state interface; no new logical definition. *)
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

Theorem abi_decode_bytes_tail_owned_joint:
  abi_decode_bytes_runtime_tail (Var dst) (Var ar) cnt sa = ((),sb) /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (^owned_decoder_state) sa s G tn /\ (?H. V H) /\
  local_ptrs_reserved ce sa /\ not_fresh_at sa input /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  not_fresh_at sa dst /\ not_fresh_at sa ar /\
  abi_decoder_operand_live sa.cs_next_var cnt /\
  eval_operand cnt s = SOME (n2w c) /\ op_prov G cnt = NONE /\ op_taint tn cnt = {} /\
  c <= n /\ n+31 < dimword (:256) /\
  lookup_var dst s = SOME (n2w d) /\ ptr_covers G tn dst s (32+32*((n+31) DIV 32)) /\
  FLOOKUP G dst = SOME (output_base,output_cap) /\ op_taint tn (Var dst) = {} /\
  abi_decode_ptr_window G tn s ar (n2w a) (32+c) /\ op_taint tn (Var ar) = {} /\
  w2n input_word <= a /\ a+32+c <= w2n input_word+LENGTH input_bytes /\
  w2n input_word+LENGTH input_bytes < dimword (:256) /\
  output_base <= d /\ d+32+32*((n+31) DIV 32) <= output_base+output_cap /\
  (w2n input_word+LENGTH input_bytes <= d \/
    d+32+32*((n+31) DIV 32) <= w2n input_word) /\
  EVERY (\(aid,p,b,k,bytes). b+k <= d \/ d+32+32*((n+31) DIV 32) <= b) live /\
  EVERY (\(b,bytes). b+LENGTH bytes <= d \/ d+32+32*((n+31) DIV 32) <= b) protected ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (^owned_decoder_state) sb t Gf tnf /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `emit_op ADD [cnt;Lit 31w] sa` >> rename1 `emit_op ADD [cnt;Lit 31w] sa = (up,c1)` >>
  Cases_on `emit_op NOT [Lit 31w] c1` >> rename1 `emit_op NOT [Lit 31w] c1 = (mask,c2)` >>
  Cases_on `emit_op AND [up;mask] c2` >> rename1 `emit_op AND [up;mask] c2 = (rounded,c3)` >>
  Cases_on `emit_op ADD [Var dst;rounded] c3` >> rename1 `emit_op ADD [Var dst;rounded] c3 = (last,c4)` >>
  Cases_on `emit_void MSTORE [last;Lit 0w] c4` >> rename1 `emit_void MSTORE [last;Lit 0w] c4 = (unit,c5)` >>
  Cases_on `emit_op ADD [Lit 32w;cnt] c5` >> rename1 `emit_op ADD [Lit 32w;cnt] c5 = (copysz,c6)` >>
  Cases_on `unit` >>
  qpat_x_assum `abi_decode_bytes_runtime_tail _ _ _ _ = _` mp_tac >>
  simp[abi_decode_bytes_runtime_tail_def, comp_bind_def, comp_ignore_bind_def] >> strip_tac >>
  `cs_extends sa c1 /\ cs_extends c1 c2 /\ cs_extends c2 c3 /\
   cs_extends c3 c4 /\ cs_extends c4 c5 /\ cs_extends c5 c6 /\ cs_extends c6 sb` by
    (imp_res_tac loweringShapeRulesTheory.emit_op_facts >>
     fs[emit_void_def, GSYM emit_inst_def] >> imp_res_tac emit_inst_extends >>
     rpt conj_tac >> irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
  `cs_extends sa c3 /\ cs_extends c3 sb /\ cs_extends c4 sb /\
   cs_extends c5 sb` by metis_tac[cs_extends_trans] >>
  map_every (fn args =>
    (qspecl_then args mp_tac fragExecTheory.fn_has_code_split >> simp[] >> strip_tac))
    [[`sa`,`c3`,`sb`,`fn`], [`c3`,`c4`,`sb`,`fn`],
     [`c4`,`c5`,`sb`,`fn`], [`c5`,`c6`,`sb`,`fn`]] >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by
    (fs[] >> metis_tac[ghost_inv_at_def]) >>
  `c+31 < dimword (:256)` by decide_tac >>
  drule_all abi_decode_tail_round_joint >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  `sa.cs_next_var <= c3.cs_next_var /\ sa.cs_next_id <= c3.cs_next_id /\
   c3.cs_current_bb = sa.cs_current_bb /\
   isPREFIX sa.cs_current_insts c3.cs_current_insts` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`emit_op AND _ c2 = _`, `emit_op NOT _ c1 = _`, `emit_op ADD _ sa = _`] >>
     rpt (pop_assum kall_tac) >>
     simp[emit_op_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt strip_tac >> gvs[] >> simp[IS_PREFIX_APPEND, APPEND_ASSOC]) >>
  `t.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `state_frame t = _` mp_tac >> simp[state_frame_def]) >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa c3)` by
    (`bop_scalar_seq {x | not_fresh_at sa x} {cnt;Lit 31w}
       (emitted_insts sa c3) (rounded INSERT mask INSERT up INSERT {cnt;Lit 31w})` by
       (irule abi_decode_bytes_round_scalar >> simp[] >> metis_tac[]) >>
     drule bop_scalar_seq_memory_checks >> simp[EVERY_MEM] >> metis_tac[]) >>
  `alloca_history fn t` by
    (irule abi_decode_no_alloca_endpoint_history >>
     qexistsl_tac [`s`, `sa`, `c3`] >> fs[]) >>
  `(^owned_decoder_state) c3 t Gf tnf` by
    (irule abi_decode_owned_scalar_frame_with_history >>
     conj_tac >- simp[] >> qexistsl_tac [`G`, `s`, `sa`, `tn`] >> simp[] >>
     qpat_x_assum `state_frame t = _` mp_tac >> simp[state_frame_def]) >>
  `local_ptrs_reserved ce c3 /\ not_fresh_at c3 input /\
   not_fresh_at c3 dst /\ not_fresh_at c3 ar /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at c3 x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at c3 x)` by
    metis_tac[local_ptrs_reserved_next_var, not_fresh_at_mono] >>
  `abi_decoder_operand_live c3.cs_next_var rounded` by
    (irule abiDecoderReentryTheory.abi_decoder_operand_live_emit >> metis_tac[]) >>
  `lookup_var dst t = SOME (n2w d) /\
   FLOOKUP Gf dst = SOME (output_base,output_cap) /\ op_taint tnf (Var dst) = {}` by
    metis_tac[] >>
  `32*((c+31) DIV 32) <= 32*((n+31) DIV 32)` by
    (`(c+31) DIV 32 <= (n+31) DIV 32` by (irule DIV_LE_MONOTONE >> simp[]) >> decide_tac) >>
  `d+32*((c+31) DIV 32)+32 <= output_base+output_cap /\
   output_base+output_cap < dimword (:256)` by (fs[] >> decide_tac) >>
  drule_all (abi_decode_tail_ptr_add_joint |> Q.INST [`len` |-> `32`]) >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  `output_base+output_cap <= t'.vs_alloca_next` by
    (`alloca_inv t' /\ FLOOKUP t'.vs_allocas output_id = SOME (output_base,output_cap)` by
       (fs[] >> metis_tac[stmt_state_rel_def]) >>
     qpat_assum `alloca_inv t'` mp_tac >>
     qpat_assum `FLOOKUP t'.vs_allocas output_id = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >>
     metis_tac[]) >>
  `local_ptrs_reserved ce c4 /\ not_fresh_at c4 input /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at c4 x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at c4 x)` by
    (`c3.cs_next_var <= c4.cs_next_var` by
       (qpat_assum `emit_op ADD _ c3 = _` mp_tac >>
        rpt (pop_assum kall_tac) >> strip_tac >>
        drule loweringShapeRulesTheory.emit_op_facts >> strip_tac >> simp[]) >>
     metis_tac[local_ptrs_reserved_next_var, not_fresh_at_mono]) >>
  `lookup_var r t' = SOME (n2w (d+32*((c+31) DIV 32))) /\
   eval_operand (Lit 0w) t' = SOME 0w /\ op_taint tnf' (Lit 0w) = {}` by
    (simp[NoAsms, eval_operand_def, op_taint_def] >>
     qpat_assum `eval_operand last t' = _` mp_tac >>
     qpat_assum `last = Var r` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[eval_operand_def]) >>
  `output_base <= d+32*((c+31) DIV 32) /\
   d+32*((c+31) DIV 32)+32 <= t'.vs_alloca_next /\
   (w2n input_word+LENGTH input_bytes <= d+32*((c+31) DIV 32) \/
    d+32*((c+31) DIV 32)+32 <= w2n input_word)` by decide_tac >>
  `EVERY (\(aid,p,b,k,bytes). b+k <= d+32*((c+31) DIV 32) \/
     d+32*((c+31) DIV 32)+32 <= b) live /\
   EVERY (\(b,bytes). b+LENGTH bytes <= d+32*((c+31) DIV 32) \/
     d+32*((c+31) DIV 32)+32 <= b) protected` by
    (qpat_assum `EVERY (\(aid,p,b,k,bytes). b+k <= d \/ _) live` mp_tac >>
     qpat_assum `EVERY (\(b,bytes). b+LENGTH bytes <= d \/ _) protected` mp_tac >>
     qpat_assum `32*((c+31) DIV 32) <= 32*((n+31) DIV 32)` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[EVERY_MEM, pairTheory.FORALL_PROD] >> rpt strip_tac >>
     res_tac >> decide_tac) >>
  qpat_assum `last = Var r` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  mp_tac (abi_decode_owned_store_joint |> SPEC_ALL |> Q.INST
    [`sa` |-> `c4`, `sb` |-> `c5`, `s` |-> `t'`, `G` |-> `Gf'`,
     `tn` |-> `tnf'`, `dst` |-> `r`, `value` |-> `Lit 0w`,
     `a` |-> `d+32*((c+31) DIV 32)`, `w` |-> `0w`]) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `ts` (qx_choose_then `Gs`
    (qx_choose_then `tns` (map_every assume_tac o CONJUNCTS)))) >>
  `sa.cs_next_var <= c4.cs_next_var /\ c4.cs_next_var <= c5.cs_next_var` by
    (qpat_assum `emit_op ADD _ c3 = _` mp_tac >>
     qpat_assum `emit_void MSTORE _ c4 = _` mp_tac >>
     qpat_assum `sa.cs_next_var <= c3.cs_next_var` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
       emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt strip_tac >> gvs[]) >>
  `abi_decoder_operand_live c5.cs_next_var cnt` by
    (irule abiDecoderReentryTheory.abi_decoder_operand_live_mono >>
     qexists_tac `sa.cs_next_var` >> simp[]) >>
  `ts.vs_labels = s.vs_labels` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _` mp_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (t,Gf,tnf) _ _` mp_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (t',Gf',tnf') _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     metis_tac[gas_origin_ptr_path_preserves_labels]) >>
  `eval_operand cnt ts = SOME (n2w c) /\ op_prov Gs cnt = NONE /\
   op_taint tns cnt = {}` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`ts.vs_labels = s.vs_labels`,
        `abi_decoder_operand_live sa.cs_next_var cnt`,
        `eval_operand cnt s = _`, `op_prov G cnt = _`, `op_taint tn cnt = _`,
        `!x. not_fresh_at sa x ==> _`,
        `!x. not_fresh_at c3 x ==> _`,
        `!x. not_fresh_at c4 x ==> _`,
        `sa.cs_next_var <= c3.cs_next_var`, `sa.cs_next_var <= c4.cs_next_var`] >>
     rpt (pop_assum kall_tac) >> Cases_on `cnt` >>
     simp[abiDecoderReentryTheory.abi_decoder_operand_live_def,
       abiDecoderReentryTheory.abi_decoder_older_vars_def,
       op_prov_def, op_taint_def, eval_operand_def] >>
     rpt strip_tac >> gvs[not_fresh_at_def] >> metis_tac[]) >>
  `?raw. run_inst_seq (emitted_insts c5 c6) ts = OK raw /\
    eval_operand copysz raw = SOME (n2w (32+c))` by
    (qpat_assum `emit_op ADD _ c5 = _` mp_tac >>
     qpat_assum `eval_operand cnt ts = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[emit_op_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >> rpt strip_tac >> gvs[] >>
     simp[emitted_insts_def, DROP_LENGTH_APPEND, run_inst_seq_def,
       step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       eval_operand_def, lookup_var_update_var, wordsTheory.word_add_n2w]) >>
  suspend "size_success"
QED

Resume abi_decode_bytes_tail_owned_joint[size_success]:
  markerLib.RESUME_TAC >>
  `bop_scalar_seq {x | not_fresh_at c5 x} {Lit 32w;cnt}
     (emitted_insts c5 c6) (copysz INSERT {Lit 32w;cnt})` by
    (irule bop_scalar_seq_emit_op >> conj_tac >- simp[] >>
     qexistsl_tac [`ADD`, `[Lit 32w;cnt]`] >> simp[]) >>
  `!op. op IN {Lit 32w;cnt} ==> op_prov Gs op = NONE /\ op_taint tns op = {}` by
    (qpat_assum `op_prov Gs cnt = _` mp_tac >>
     qpat_assum `op_taint tns cnt = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[IN_INSERT, NOT_IN_EMPTY] >> rpt strip_tac >>
     gvs[op_prov_def, op_taint_def]) >>
  `inst_extends c5 c6 /\ c6.cs_current_bb = c5.cs_current_bb /\
   c5.cs_next_var <= c6.cs_next_var /\ c5.cs_next_id <= c6.cs_next_id /\
   EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts c5 c6)` by
    (qpat_assum `emit_op ADD _ c5 = _` mp_tac >> rpt (pop_assum kall_tac) >>
     strip_tac >> drule loweringShapeRulesTheory.emit_op_facts >> strip_tac >>
     drule emitted_insts_emit_op >> strip_tac >>
     simp[mk_inst_def] >> metis_tac[inst_extends_emit_op]) >>
  `local_ptrs_reserved ce c5 /\ not_fresh_at c5 input /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at c5 x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at c5 x)` by
    metis_tac[local_ptrs_reserved_next_var, not_fresh_at_mono] >>
  `allocas_from lo ts` by
    (qpat_assum `(^owned_decoder_state) c5 ts Gs tns` mp_tac >>
     qpat_assum `?H. V H` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[] >> rpt strip_tac >>
     qpat_x_assum `!H. V H ==> _` drule >>
     simp[ghost_inv_at_def]) >>
  mp_tac (abi_decode_scalar_guard_success_joint |> SPEC_ALL |> Q.INST
    [`sa` |-> `c5`, `sb` |-> `c6`, `s` |-> `ts`, `G` |-> `Gs`,
     `tn` |-> `tns`, `t` |-> `raw`, `A` |-> `{Lit 32w;cnt}`,
     `B` |-> `copysz INSERT {Lit 32w;cnt}`]) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `tc` (qx_choose_then `Gc`
    (qx_choose_then `tnc` (map_every assume_tac o CONJUNCTS)))) >>
  `eval_operand copysz tc = SOME (n2w (32+c)) /\
   op_taint tnc copysz = {}` by
    (qpat_assum `tc = _` mp_tac >>
     qpat_assum `eval_operand copysz raw = _` mp_tac >>
     qpat_assum `!op. op IN copysz INSERT _ ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >> ntac 3 strip_tac >>
     conj_tac >- (gvs[] >> Cases_on `copysz` >> gvs[eval_operand_def, lookup_var_def]) >>
     first_x_assum (qspec_then `copysz` mp_tac) >> simp[]) >>
  suspend "copy"
QED

Resume abi_decode_bytes_tail_owned_joint[copy]:
  markerLib.RESUME_TAC >>
  `sa.cs_next_var <= c5.cs_next_var /\ sa.cs_next_var <= c6.cs_next_var` by decide_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x tc = lookup_var x s /\
    FLOOKUP Gc x = FLOOKUP G x /\ op_taint tnc (Var x) = op_taint tn (Var x)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`!x. not_fresh_at sa x ==> _`, `!x. not_fresh_at c3 x ==> _`,
       `!x. not_fresh_at c4 x ==> _`, `!x. not_fresh_at c5 x ==> _`,
       `sa.cs_next_var <= c3.cs_next_var`, `sa.cs_next_var <= c4.cs_next_var`,
       `sa.cs_next_var <= c5.cs_next_var`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     `not_fresh_at c3 x /\ not_fresh_at c4 x /\ not_fresh_at c5 x` by
       metis_tac[not_fresh_at_mono] >> metis_tac[]) >>
  `local_ptrs_reserved ce c6 /\ not_fresh_at c6 input /\
   not_fresh_at c6 dst /\ not_fresh_at c6 ar /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at c6 x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at c6 x)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`local_ptrs_reserved ce sa`, `not_fresh_at sa input`,
       `not_fresh_at sa dst`, `not_fresh_at sa ar`,
       `!x sz. ce.ce_return_buf = _ ==> not_fresh_at sa x`,
       `!x sz. ce.ce_return_pc = _ ==> not_fresh_at sa x`,
       `sa.cs_next_var <= c6.cs_next_var`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     metis_tac[local_ptrs_reserved_next_var, not_fresh_at_mono]) >>
  `abi_decoder_operand_live c6.cs_next_var copysz` by
    metis_tac[abiDecoderReentryTheory.abi_decoder_operand_live_emit] >>
  `lookup_var dst tc = SOME (n2w d) /\ lookup_var ar tc = SOME (n2w a) /\
   FLOOKUP Gc dst = SOME (output_base,output_cap) /\
   op_taint tnc (Var dst) = {} /\ op_taint tnc (Var ar) = {}` by
    (qpat_assum `!x. not_fresh_at sa x ==> lookup_var x tc = _ /\ _` mp_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`lookup_var dst s = _`, `FLOOKUP G dst = _`, `op_taint tn (Var dst) = _`,
        `abi_decode_ptr_window G tn s ar _ _`, `op_taint tn (Var ar) = _`,
        `not_fresh_at sa dst`, `not_fresh_at sa ar`] >>
     rpt (pop_assum kall_tac) >> simp[abi_decode_ptr_window_def] >>
     rpt strip_tac >> metis_tac[]) >>
  `c <= 32*((n+31) DIV 32)` by
    (qpat_assum `c <= n` mp_tac >> rpt (pop_assum kall_tac) >>
     mp_tac (arithmeticTheory.DIVISION |> Q.SPEC `32`) >>
     rewrite_tac [DECIDE ``0 < 32``] >>
     disch_then (qspec_then `n+31` strip_assume_tac) >> strip_tac >> decide_tac) >>
  `abi_decode_ptr_window Gc tnc tc input input_word (LENGTH input_bytes) /\
   w2n input_word + LENGTH input_bytes <= tc.vs_alloca_next /\
   output_base + output_cap <= tc.vs_alloca_next` by
    (qpat_assum `(^owned_decoder_state) c6 tc Gc tnc` mp_tac >>
     qpat_assum `?H. V H` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[] >> rpt strip_tac >>
     `alloca_inv tc` by metis_tac[stmt_state_rel_def] >>
     gvs[venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >>
     metis_tac[]) >>
  `a < dimword (:256) /\ d < dimword (:256) /\ 32+c < dimword (:256) /\
   d+(32+c) <= output_base+output_cap /\
   d+(32+c) <= tc.vs_alloca_next /\ a+(32+c) <= tc.vs_alloca_next` by decide_tac >>
  `ptr_covers Gc tnc dst tc (32+c)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`lookup_var dst tc = _`, `FLOOKUP Gc dst = _`, `op_taint tnc (Var dst) = _`,
       `output_base <= d`, `d + (32+c) <= output_base+output_cap`, `d < dimword (:256)`] >>
     rpt (pop_assum kall_tac) >> simp[ptr_covers_def, w2n_n2w, LESS_MOD]) >>
  `ptr_covers Gc tnc ar tc (32+c)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`abi_decode_ptr_window G tn s ar _ _`,
       `!x. not_fresh_at sa x ==> lookup_var x tc = _ /\ _`, `not_fresh_at sa ar`] >>
     rpt (pop_assum kall_tac) >> simp[abi_decode_ptr_window_def, ptr_covers_def] >>
     rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `!i. a <= i /\ i < a+(32+c) ==> i NOTIN tnc.t_mem` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`abi_decode_ptr_window Gc tnc tc input _ _`, `w2n input_word <= a`,
       `a+32+c <= w2n input_word+LENGTH input_bytes`] >>
     rpt (pop_assum kall_tac) >> simp[abi_decode_ptr_window_def] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `(w2n input_word+LENGTH input_bytes <= d \/ d+(32+c) <= w2n input_word) /\
   EVERY (\(aid,p,b,k,bytes). b+k <= d \/ d+(32+c) <= b) live /\
   EVERY (\(b,bytes). b+LENGTH bytes <= d \/ d+(32+c) <= b) protected` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`w2n input_word+LENGTH input_bytes <= d \/ _`,
       `EVERY (\(aid,p,b,k,bytes). b+k <= d \/ _) live`,
       `EVERY (\(b,bytes). b+LENGTH bytes <= d \/ _) protected`,
       `c <= 32*((n+31) DIV 32)`] >>
     rpt (pop_assum kall_tac) >> simp[EVERY_MEM, pairTheory.FORALL_PROD] >>
     rpt strip_tac >> res_tac >> decide_tac) >>
  mp_tac (abi_decode_owned_mcopy_joint |> SPEC_ALL |> Q.INST
    [`sa` |-> `c6`, `s` |-> `tc`, `G` |-> `Gc`, `tn` |-> `tnc`,
     `src` |-> `ar`, `count_op` |-> `copysz`, `b` |-> `d`, `n` |-> `32+c`]) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choose_then `tb` (qx_choose_then `Gb`
    (qx_choose_then `tnb` (map_every assume_tac o CONJUNCTS)))) >>
  suspend "assemble"
QED

Resume abi_decode_bytes_tail_owned_joint[assemble]:
  markerLib.RESUME_TAC >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s,G,tn) [] (OK tb,Gb,tnb)` by
    (gen_tac >>
     irule gas_origin_ptr_path_trans >> qexistsl [`Gf`, `t`, `tnf`] >>
     (conj_tac >- simp[]) >>
     irule gas_origin_ptr_path_trans >> qexistsl [`Gf'`, `t'`, `tnf'`] >>
     (conj_tac >- simp[]) >>
     irule gas_origin_ptr_path_trans >> qexistsl [`Gs`, `ts`, `tns`] >>
     (conj_tac >- simp[]) >>
     irule gas_origin_ptr_path_trans >> qexistsl [`Gc`, `tc`, `tnc`] >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x tb = lookup_var x s /\
    FLOOKUP Gb x = FLOOKUP G x /\ op_taint tnb (Var x) = op_taint tn (Var x)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`!x. not_fresh_at sa x ==> lookup_var x tc = _ /\ _`,
       `!x. not_fresh_at c6 x ==> _`, `sa.cs_next_var <= c6.cs_next_var`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     `not_fresh_at c6 x` by metis_tac[not_fresh_at_mono] >> metis_tac[]) >>
  qexistsl [`tb`, `Gb`, `tnb`] >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`(^owned_decoder_state) sb tb Gb tnb`,
     `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK tb,Gb,tnb)`,
     `!x. not_fresh_at sa x ==> lookup_var x tb = _ /\ _`,
     `~tb.vs_halted`, `tb.vs_current_bb = sb.cs_current_bb`,
     `tb.vs_inst_idx = LENGTH sb.cs_current_insts`] >>
  rpt (pop_assum kall_tac) >> simp[] >> metis_tac[]
QED

Finalise abi_decode_bytes_tail_owned_joint
