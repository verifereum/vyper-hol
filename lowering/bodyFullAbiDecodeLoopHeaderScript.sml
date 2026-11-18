Theory bodyFullAbiDecodeLoopHeader
Ancestors
  bodyFullAbiDecodeLoopHeaderExact
  bodyFullAbiDecodeInterface bodyFullAbiDecodeLeafCases
  bodyFullAbiDecodeFiniteGuard assignBasePtrBytesPrefix
  typedCopyOriginPtrBase typedMemoryCopy bodyPtrMakeArrayEmission bodyFullShared bodyPtrDefs
  allocaFootprint gasOriginPtrLabels instSeqPtrLo fragGasOriginPtrDead
  fragGasOriginPtrLoop fragGasCopyLoop stmtReasonLitFragMemory fragExec
  stateFrame emitHelperProps loweringShapeRules
  compileEnv emitHelper venomInst venomExecSemantics venomState
  words list finite_map exprLoweringProps freshWrites rich_list loweringStateRelDefs

(* Alpha-identical owned state quotation, not a HOL definition. *)
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

(* The loop counter is a protected, clean one-word pointer read. *)
Theorem abi_decode_loop_counter_load:
  emit_op MLOAD [Var counter] sa = (Var out,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ allocas_from lo s /\
  ptr_covers G tn counter s 32 /\ lookup_var counter s = SOME a /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
  w2n a+32 <= s.vs_alloca_next /\
  (^owned_decoder_state) sa s G tn /\
  not_fresh_at sa input /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
       (s,G,tn) [] (OK t,Gf,tnf)) /\
    eval_operand (Var out) t = SOME (mload (w2n a) s) /\
    op_prov Gf (Var out) = NONE /\ op_taint tnf (Var out) = {} /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (^owned_decoder_state) sb t Gf tnf /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
    tnf.t_mem = tn.t_mem /\
    (!x. not_fresh_at sa x ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all abi_decode_loop_counter_load_exact >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >> asm_rewrite_tac[]
QED

(* Control transfer changes only the cursor, not owned resources. *)
Theorem abi_decode_loop_owned_jump[local]:
  (^owned_decoder_state) st s G tn ==>
  (^owned_decoder_state) st (jump_to lbl s) G tn
Proof
  ACCEPT_TAC abi_decode_loop_owned_jump_exact
QED

Theorem abi_decode_loop_owned_branch[local]:
  emit_op LT [Var counter; length] sa = (lt,sb) /\
  emit_op ISZERO [lt] sb = (done,sc) /\
  emit_inst JNZ [done; Label exit; Label body_lbl] [] sc = ((),sd) /\
  lookup_var counter s = SOME (n2w j) /\
  eval_operand length s = SOME (n2w n) /\ j <= n /\ n < dimword (:256) /\
  FLOOKUP G counter = NONE /\ op_prov G length = NONE /\
  op_taint tn (Var counter) = {} /\ op_taint tn length = {} /\
  fn_has_code sa sd fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  (^owned_decoder_state) sa s G tn /\
  not_fresh_at sa input /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    (^owned_decoder_state) sd t Gf tnf /\
    ~t.vs_halted /\ t.vs_inst_idx = 0 /\
    t.vs_current_bb = (if j = n then exit else body_lbl) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
    tnf.t_mem = tn.t_mem /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all abi_decode_loop_owned_branch_exact >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >> asm_rewrite_tac[]
QED

(* The concrete header segments select one endpoint before any horizon. *)
Theorem abi_decode_loop_header_joint:
  emit_op MLOAD [Var counter] sa = (Var idx,sb) /\
  compile_abi_dec_addr (Var input) src sb = (addr,sc) /\
  emit_op MLOAD [addr] sc = (count_op,sd) /\
  emit_op LT [Var idx;count_op] sd = (lt,se) /\
  emit_op ISZERO [lt] se = (done,sf) /\
  emit_inst JNZ [done;Label exit_lbl;Label body_lbl] [] sf = ((),sg) /\
  fn_has_code sa sb fn /\ fn_has_code sb sd fn /\ fn_has_code sd sg fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ sa.cs_current_insts = [] /\
  s.vs_inst_idx = 0 /\ allocas_from lo s /\
  (^owned_decoder_state) sa s G tn /\
  not_fresh_at sa input /\ not_fresh_at sa counter /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. hi = Var x ==> not_fresh_at sa x) /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  lookup_var counter s = SOME (n2w cell) /\ ptr_covers G tn counter s 32 /\
  mem_word_at cell s.vs_memory = n2w j /\
  (!i. cell <= i /\ i < cell+32 ==> i NOTIN tn.t_mem) /\
  cell+32 <= s.vs_alloca_next /\ cell < dimword (:256) /\
  eval_operand src s = SOME (n2w srcoff) /\ op_taint tn src = {} /\
  eval_operand hi s = SOME (n2w h) /\
  srcoff+32+n*asz <= h /\ h <= LENGTH input_bytes /\
  w2n input_word+LENGTH input_bytes < dimword (:256) /\
  mem_word_at (w2n input_word+srcoff) s.vs_memory = n2w n /\
  j <= n /\ n < dimword (:256) ==>
  ?t Gf tnf.
    (!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    (^owned_decoder_state) sg t Gf tnf /\
    ~t.vs_halted /\ t.vs_inst_idx = 0 /\
    t.vs_current_bb = (if j = n then exit_lbl else body_lbl) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
    tnf.t_mem = tn.t_mem /\
    eval_operand src t = SOME (n2w srcoff) /\
    eval_operand hi t = SOME (n2w h) /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all abi_decode_loop_header_joint_exact >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >> asm_rewrite_tac[]
QED
