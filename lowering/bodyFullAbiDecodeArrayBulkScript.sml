Theory bodyFullAbiDecodeArrayBulk
Ancestors
  exprSimWordBuiltins[qualified,ignore_grammar]
  bodyFullAbiDecodeInterface bodyFullAbiDecodeFiniteGuard
  bodyFullAbiDecodeTailAdd bodyFullAbiDecodeOwnedCopy abiDecoderBulk
  bodyPtrBopScalarCompile bodyPtrBopScalarOutcome bodyPtrBopScalarSeq
  abiDecodePtrMemberFrame abiDecoderReentry loweringShapeRules
  exprSimAccounts externalEntryShape freshWrites emitHelperProps
  abiEncoder compileEnv emitHelper venomState venomExecSemantics venomInst
  ptrDiscipline words arithmetic list rich_list finite_map pred_set pair
  loweringStateRelDefs exprLoweringProps bodyFullAbiDecodeFiniteObserved fragExec
  bodyPtrDefs fragGasOriginPtr ghostPcTransportPtr

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

(* Only the two scalar instructions of the bulk suffix. *)

Theorem abi_decode_bulk_scalar_code[local]:
  emit_op MUL [cnt;Lit (n2w msz)] sa = (copy_sz,sm) /\
  emit_op ADD [src;Lit 32w] sm = (data,sb) ==>
  bop_scalar_seq {x | not_fresh_at sa x}
    (cnt INSERT src INSERT {op | ?w. op = Lit w})
    (emitted_insts sa sb)
    (data INSERT copy_sz INSERT cnt INSERT src INSERT {op | ?w. op = Lit w}) /\
  EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb) /\
  inst_extends sa sb /\ cs_extends sa sb /\
  sb.cs_current_bb = sa.cs_current_bb /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id
Proof
  strip_tac >>
  drule (Q.SPEC `MUL` emitted_insts_emit_op) >> strip_tac >>
  drule (Q.SPEC `ADD` emitted_insts_emit_op) >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> simp[]) >>
  conj_tac
  >- (asm_rewrite_tac[] >> irule bop_scalar_seq_append >>
      qexists_tac `copy_sz INSERT cnt INSERT src INSERT {op | ?w. op = Lit w}` >>
      simp[] >> conj_tac >> irule bop_scalar_seq_single >>
      simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj]) >>
  `sm.cs_blocks = sa.cs_blocks /\ sm.cs_current_bb = sa.cs_current_bb /\
   sb.cs_blocks = sm.cs_blocks /\ sb.cs_current_bb = sm.cs_current_bb` by
    metis_tac[emit_op_facts] >>
  simp[mk_inst_def, inst_extends_def, cs_extends_def, IS_PREFIX_APPEND, APPEND_ASSOC]
QED

Theorem abi_decode_bulk_scalar_observed[local]:
  emit_op MUL [cnt;Lit (n2w msz)] sa = (copy_sz,sm) /\
  emit_op ADD [src;Lit 32w] sm = (data,sb) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  !obs. fn_has_code sa sb obs ==>
    gas_path ctx obs s 0 (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  drule (Q.SPEC `MUL` emitted_insts_emit_op) >> strip_tac >>
  drule (Q.SPEC `ADD` emitted_insts_emit_op) >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> simp[]) >>
  `sb.cs_current_bb = sa.cs_current_bb` by metis_tac[emit_op_facts] >>
  mp_tac (Q.INST [`code` |-> `emitted_insts sa sb`]
            abi_decode_finite_success_observed) >>
  simp[mk_inst_def, is_terminator_def, APPEND_ASSOC]
QED

Theorem abi_decode_bulk_add_observed[local]:
  emit_op ADD [x;y] sa = (Var r,sb) /\
  eval_operand x s = SOME (n2w a) /\ eval_operand y s = SOME (n2w k) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  t = (update_var r (n2w (a+k)) s) with vs_inst_idx := SUC s.vs_inst_idx ==>
  !obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (OK t)
Proof
  strip_tac >> rpt strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  gvs[] >>
  drule (Q.INST [`w` |-> `n2w (a+k):256 word`] emit_op_zero_path) >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       word_add_n2w, is_terminator_def]
QED

Theorem abi_decode_bulk_mcopy_observed[local]:
  emit_void MCOPY [dst;src;cnt] sa = ((),sb) /\
  eval_operand dst s = SOME (n2w b) /\ eval_operand src s = SOME (n2w a) /\
  eval_operand cnt s = SOME (n2w n) /\
  a < dimword (:256) /\ b < dimword (:256) /\ n < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  t = (mcopy b a n s) with vs_inst_idx := SUC s.vs_inst_idx ==>
  !obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (OK t)
Proof
  strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `emit_inst MCOPY [dst;src;cnt] [] sa = ((),sb)` by
    gvs[emit_void_def, emit_inst_def] >>
  `sb.cs_current_bb = sa.cs_current_bb` by metis_tac[emitted_insts_emit_inst] >>
  mp_tac (Q.INST [`code` |-> `[mk_inst sa.cs_next_id MCOPY [dst;src;cnt] []]`,
                  `t` |-> `mcopy b a n s`] abi_decode_finite_success_observed) >>
  simp[mk_inst_def, is_terminator_def, run_inst_seq_def,
       step_inst_base_opcode_eqs, w2n_n2w, LESS_MOD, ADD1]
QED

Theorem abi_decode_bulk_payload_cut[local]:
  abi_decode_bulk_payload dst src cnt msz MLOAD (Var input) sa = ((),sf) ==>
  ?sm sb sc sd copy_sz data source dest.
    emit_op MUL [cnt;Lit (n2w msz)] sa = (copy_sz,sm) /\
    emit_op ADD [src;Lit 32w] sm = (data,sb) /\
    emit_op ADD [Var input;data] sb = (source,sc) /\
    emit_op ADD [dst;Lit 32w] sc = (dest,sd) /\
    emit_void MCOPY [dest;source;copy_sz] sd = ((),sf) /\
    cs_extends sa sb /\ cs_extends sb sc /\ cs_extends sc sd /\ cs_extends sd sf /\
    sa.cs_next_var <= sb.cs_next_var /\ sb.cs_next_var <= sc.cs_next_var /\
    sc.cs_next_var <= sd.cs_next_var /\ sd.cs_next_var <= sf.cs_next_var
Proof
  simp[abi_decode_bulk_payload_def, compile_abi_dec_addr_def, comp_bind_def,
       abiDecoderCompositionTheory.abi_decode_copy_opcode_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  ntac 3 (pairarg_tac >> gvs[]) >>
  rename1 `emit_void MCOPY _ sd = ((),sf)` >>
  imp_res_tac emit_op_extends_next_var >>
  drule emitted_insts_emit_void >> strip_tac >>
  conj_tac >- metis_tac[cs_extends_trans] >>
  `cs_extends sd sf` by
    (qspecl_then [`MCOPY`, `[dst_data;src_addr;copy_sz]`, `sd`, `K T`]
       mp_tac externalEntryShapeTheory.emit_void_labels >> simp[]) >>
  simp[] >> decide_tac
QED

Theorem abi_decode_array_bulk_scalar_run[local]:
  emit_op MUL [cnt;Lit (n2w msz)] sa = (copy_sz,sm) /\
  emit_op ADD [src;Lit 32w] sm = (data,sb) /\
  eval_operand cnt s = SOME (n2w n) /\ eval_operand src s = SOME (n2w off) /\
  abi_decoder_operand_live sa.cs_next_var src ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand copy_sz t = SOME (n2w (n*msz)) /\
    eval_operand data t = SOME (n2w (off+32))
Proof
  simp[emit_op_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  `eval_operand src
     (update_var (STRING #"%" (toString sa.cs_next_var)) (n2w (n*msz)) s) =
   eval_operand src s` by
    (irule exprSimWordBuiltinsTheory.eval_operand_update_not_fresh >>
     qexists_tac `sa` >> simp[] >> rpt strip_tac >>
     gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  simp_tac (srw_ss()) [emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp_tac (srw_ss()) [DROP_LENGTH_APPEND] >>
  gvs[MULT_COMM] >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure2_def, eval_operand_def, lookup_var_update_var,
       ASCIInumbersTheory.toString_inj, word_mul_n2w, word_add_n2w,
       MULT_COMM]
QED

Theorem abi_decode_array_bulk_scalar_joint[local]:
  emit_op MUL [cnt;Lit (n2w msz)] sa = (copy_sz,sm) /\
  emit_op ADD [src;Lit 32w] sm = (data,sb) /\
  eval_operand cnt s = SOME (n2w n) /\ eval_operand src s = SOME (n2w off) /\
  abi_decoder_operand_live sa.cs_next_var src /\
  op_prov G cnt = NONE /\ op_prov G src = NONE /\
  op_taint tn cnt = {} /\ op_taint tn src = {} /\
  ~ctx_has_dalloca ctx /\ fn_has_code sa sb fn /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (^owned_decoder_state) sa s G tn /\ (?H. V H) /\
  not_fresh_at sa input /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?u Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
           (s,G,tn) [] (OK u,Gf,tnf)) /\
    (!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (OK u)) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (^owned_decoder_state) sb u Gf tnf /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\
    eval_operand copy_sz u = SOME (n2w (n*msz)) /\
    eval_operand data u = SOME (n2w (off+32)) /\
    op_prov Gf data = NONE /\ op_taint tnf data = {} /\
    op_taint tnf copy_sz = {} /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  BETA_TAC >> strip_tac >>
  drule_all abi_decode_bulk_scalar_code >> strip_tac >>
  drule_all abi_decode_array_bulk_scalar_run >> strip_tac >>
  `!op. op IN (cnt INSERT src INSERT {op | ?w. op = Lit w}) ==>
    op_prov G op = NONE /\ op_taint tn op = {}` by
    (simp[] >> rpt strip_tac >> gvs[op_prov_def, op_taint_def]) >>
  `allocas_from lo s` by metis_tac[ghost_inv_at_def] >>
  mp_tac (Q.INST [
    `A` |-> `cnt INSERT src INSERT {op | ?w. op = Lit w}`,
    `B` |-> `data INSERT copy_sz INSERT cnt INSERT src INSERT {op | ?w. op = Lit w}`]
    (BETA_RULE abi_decode_scalar_guard_success_joint)) >>
  (impl_tac >- (asm_rewrite_tac[] >> qexists_tac `inst` >> asm_rewrite_tac[])) >>
  strip_tac >>
  `!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (OK u)` by
    (qpat_assum `u = t with vs_inst_idx := _` (fn th => once_rewrite_tac[th]) >>
     mp_tac abi_decode_bulk_scalar_observed >> asm_rewrite_tac[]) >>
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
   u.vs_alloca_next = s.vs_alloca_next` by
    (drule_all bodyPtrBopScalarOutcomeTheory.bop_scalar_seq_runtime_frame >> strip_tac >>
     qpat_assum `u = t with vs_inst_idx := _` (fn th => once_rewrite_tac[th]) >>
     qpat_assum `t = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `eval_operand copy_sz u = SOME (n2w (n*msz)) /\
   eval_operand data u = SOME (n2w (off+32))` by
    (qpat_assum `u = t with vs_inst_idx := _` (fn th => once_rewrite_tac[th]) >>
     simp[ghostPcTransportPtrTheory.eval_operand_inst_idx]) >>
  qpat_assum `!op. op IN data INSERT copy_sz INSERT _ ==> _`
    (fn th => map_every (fn opnd =>
      qspec_then opnd (strip_assume_tac o SIMP_RULE (srw_ss()) []) th)
      [`data`, `copy_sz`]) >>
  qexistsl_tac [`u`, `Gf`, `tnf`] >>
  asm_rewrite_tac[] >> qexists_tac `inst` >> asm_rewrite_tac[]
QED
