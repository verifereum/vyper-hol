Theory bodyFullAbiDecodeLoopDestination
Ancestors
  bodyFullAbiDecodeLeafCases bodyFullAbiDecodeMemberPrefix decoderArraySetupPtr
  calldataDynOwned bodyPtrBopScalarOutcome stateFrame freshWrites
  abiDecodePtrBytesTail instSeqPtrLo fragGasSeqPtr fragExecMem abiDecodePtrHead
  loweringShapeRules fragGasOriginPtrLoop bodyFullAbiDecodeLoopDestinationExact
  allocaFootprint emitHelperProps exprLoweringProps abiDecoderIndexedAddress
  codegenRel ptrDiscipline decoderNavigationPtr decoderGhostFramePtr fragExec
  abiDecoderReentry loweringStateRelDefs compileEnv emitHelper
  venomInst venomExecSemantics venomState words list rich_list finite_map arithmetic

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

Theorem abi_decode_loop_destination_joint:
  abi_decode_indexed_address (Var dst) idx msz sa = (child_dst,sb) /\
  lookup_var dst s = SOME (n2w d) /\ eval_operand idx s = SOME (n2w j) /\
  abi_decoder_operand_live sa.cs_next_var (Var dst) /\
  abi_decoder_operand_live sa.cs_next_var idx /\
  ptr_covers G tn dst s (32+n*msz) /\
  FLOOKUP G dst = SOME (output_base,output_cap) /\
  output_base <= d /\ d+32+n*msz <= output_base+output_cap /\ j<n /\
  op_prov G idx = NONE /\ op_taint tn idx = {} /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (^owned_decoder_state) sa s G tn /\
  not_fresh_at sa input /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?u Gu tnu child.
    child_dst = Var child /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK u,Gu,tnu)) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (^owned_decoder_state) sb u Gu tnu /\
    eval_operand child_dst u = SOME (n2w (d+32+j*msz)) /\
    ptr_covers Gu tnu child u msz /\
    FLOOKUP Gu child = SOME (output_base,output_cap) /\
    op_taint tnu child_dst = {} /\
    abi_decoder_operand_live sb.cs_next_var child_dst /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\ u.vs_labels = s.vs_labels /\
    tnu.t_mem = tn.t_mem /\
    (!x. not_fresh_at sa x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP Gu x = FLOOKUP G x /\
      op_taint tnu (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  drule_all bodyFullAbiDecodeLoopDestinationExactTheory.abi_decode_loop_destination_joint_exact >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`u`, `Gu`, `tnu`, `child`] >> asm_rewrite_tac[]
QED
