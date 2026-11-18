Theory bodyFullAbiDecodeGuardReadJoint
Ancestors
  bodyFullAbiDecodeGuardReadObserved
  bodyFullAbiDecodeLeafCases bodyFullAbiDecodeFiniteGuard bodyFullAbiDecodeScalarNoAlloca
  bodyFullAbiDecodeAge bodyFullAbiDecodeBytesArithmetic bodyFullAbiDecodeClampMemory
  abiDecoderBytesBound abiDecoderBytesPhases abiDecoderRange abiDecoderGuards
  abiDecodePtrPrims abiDecodePtrBytesMember bodyPtrBopScalarCompile bodyPtrBopScalarOutcome
  gasOriginPtrLabels ptrDiscipline freshWrites exprLoweringProps emitHelperProps
  abiEncoder compileEnv emitHelper venomState venomExecSemantics venomInst
  words arithmetic list rich_list finite_map pred_set

Theorem abi_decode_bytes_head_run[local]:
  abi_decode_bytes_head src hi sa = (head,sb) /\ hi <> Lit 0w /\
  eval_operand src s = SOME (n2w off) /\
  eval_operand hi s = SOME (n2w h) /\
  off < dimword(:256) /\ h < dimword(:256) /\
  abi_decoder_operand_live sa.cs_next_var src /\
  abi_decoder_operand_live sa.cs_next_var hi ==>
  (?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
       eval_operand head t = SOME (n2w (off+32)) /\
       off <= w2n (n2w (off+32):bytes32) /\
       w2n (n2w (off+32):bytes32) <= w2n (n2w h:bytes32)) \/
  (?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  MATCH_ACCEPT_TAC bodyFullAbiDecodeGuardReadObservedTheory.abi_decode_bytes_head_run
QED

Theorem abi_decode_bytes_count_run[local]:
  emit_op GT [cnt;Lit (n2w n)] sa = (many,c1) /\
  emit_op ISZERO [many] c1 = (ok,c2) /\
  emit_void ASSERT [ok] c2 = ((),sb) /\
  eval_operand cnt s = SOME (n2w c) /\
  c < dimword(:256) /\ n < dimword(:256) /\
  abi_decoder_operand_live sa.cs_next_var cnt ==>
  (?t. run_inst_seq (emitted_insts sa sb) s = OK t /\ c <= n) \/
  (?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  MATCH_ACCEPT_TAC bodyFullAbiDecodeGuardReadObservedTheory.abi_decode_bytes_count_run
QED

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

(* Keep canonical scalar witnesses while assembling owned and emitted frames. *)
Theorem abi_decode_bytes_scalar_frame_joint:
  bop_scalar_seq {x | not_fresh_at sa x} A (emitted_insts sa sb) B /\
  (!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  ~ctx_has_dalloca ctx /\ fn_has_code sa sb fn /\ inst_extends sa sb /\
  sb.cs_current_bb = sa.cs_current_bb /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb) /\
  allocas_from lo s /\ (^owned_decoder_state) sa s G tn /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  not_fresh_at sa input /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?u Gf tnf.
    u = t with vs_inst_idx := LENGTH sb.cs_current_insts /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
       (s,G,tn) [] (OK u,Gf,tnf)) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (^owned_decoder_state) sb u Gf tnf /\
    u.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\ allocas_from lo u /\
    (!op. op IN B ==> op_prov Gf op = NONE /\ op_taint tnf op = {}) /\
    (!x. not_fresh_at sa x ==>
       lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  MATCH_ACCEPT_TAC bodyFullAbiDecodeGuardReadObservedTheory.abi_decode_bytes_scalar_frame_joint
QED

Theorem abi_decode_bytes_head_joint:
  abi_decode_bytes_head src hi sa = (head,sb) /\ hi <> Lit 0w /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (^owned_decoder_state) sa s G tn /\ allocas_from lo s /\
  not_fresh_at sa input /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  eval_operand src s = SOME (n2w off) /\
  eval_operand hi s = SOME (n2w h) /\
  off < dimword(:256) /\ h < dimword(:256) /\
  abi_decoder_operand_live sa.cs_next_var src /\
  abi_decoder_operand_live sa.cs_next_var hi /\
  op_prov G src = NONE /\ op_taint tn src = {} /\
  op_prov G hi = NONE /\ op_taint tn hi = {} ==>
  (?t Gf tnf. (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (^owned_decoder_state) sb t Gf tnf /\ off+32 <= h /\
    eval_operand head t = SOME (n2w (off+32)) /\
    op_prov Gf head = NONE /\ op_taint tnf head = {} /\
    t.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\ allocas_from lo t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x))) \/
  (?t Gf tnf. !D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (Abort Revert_abort t,Gf,tnf))
Proof
  strip_tac >>
  drule_all bodyFullAbiDecodeGuardReadObservedTheory.abi_decode_bytes_head_joint_observed >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac)
  >- (disj1_tac >> qexistsl_tac [`t`, `Gf`, `tnf`] >> asm_rewrite_tac[]) >>
  disj2_tac >> qexistsl_tac [`t`, `Gf`, `tnf`] >> asm_rewrite_tac[]
QED

Theorem abi_decode_bytes_count_joint:
  abi_decode_le_guard cnt (Lit (n2w n)) sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (^owned_decoder_state) sa s G tn /\ allocas_from lo s /\
  not_fresh_at sa input /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  eval_operand cnt s = SOME (n2w c) /\
  c < dimword(:256) /\ n < dimword(:256) /\
  abi_decoder_operand_live sa.cs_next_var cnt /\
  op_prov G cnt = NONE /\ op_taint tn cnt = {} ==>
  (?t Gf tnf. (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (^owned_decoder_state) sb t Gf tnf /\ c <= n /\
    t.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\ allocas_from lo t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x))) \/
  (?t Gf tnf. !D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (Abort Revert_abort t,Gf,tnf))
Proof
  strip_tac >>
  drule_all bodyFullAbiDecodeGuardReadObservedTheory.abi_decode_bytes_count_joint_observed >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac)
  >- (disj1_tac >> qexistsl_tac [`t`, `Gf`, `tnf`] >> asm_rewrite_tac[]) >>
  disj2_tac >> qexistsl_tac [`t`, `Gf`, `tnf`] >> asm_rewrite_tac[]
QED

(* Retain the canonical load's fresh address certificate at its actual endpoint. *)
Theorem abi_decode_bytes_owned_load_frame_joint:
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
  ?out ar t Gf tnf.
    v = Var out /\ not_fresh_at sc out /\
    addr = Var ar /\ not_fresh_at sc ar /\
    abi_decode_ptr_window Gf tnf t ar
      (input_word+n2w p) (LENGTH input_bytes-p) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
       (s,G,tn) [] (OK t,Gf,tnf)) /\
    eval_operand v t = SOME (mload (w2n input_word+p) s) /\
    op_prov Gf v = NONE /\ op_taint tnf v = {} /\
    ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
    t.vs_inst_idx = LENGTH sc.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\ allocas_from lo t /\
    (^owned_decoder_state) sc t Gf tnf /\
    (!x. not_fresh_at sa x ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  drule_all bodyFullAbiDecodeGuardReadObservedTheory.abi_decode_bytes_owned_load_frame_joint_observed >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`out`, `ar`, `t`, `Gf`, `tnf`] >> asm_rewrite_tac[]
QED
