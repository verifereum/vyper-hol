Theory bodyFullAbiDecodeCallerPrefixJoint
Ancestors
  bodyFullAbiDecodeInterface bodyFullAbiDecodeLeafCases
  bodyFullAbiDecodeFiniteObserved assignTuplePtrCopyLen abiDecodePtrRead
  abiBuiltinDecodeSetup abiBuiltinDecodeHeader abiBuiltinLengthGuard
  abiDecodePtrMemberFrame assignTuplePtrLoadStep instSeqPtrLo
  fragGasOriginPtrLoop fragGasSeqPtr bodyFullUnwrapRun
  emitHelperProps exprLoweringProps loweringStateRelDefs
  stateFrame allocaHistory fragExecMem instMemFrontier
  compileEnv emitHelper freshWrites ptrDiscipline
  venomExecSemantics venomInst venomState words arithmetic finite_map list rich_list

val caller_setup_pre = ``\data min_size max_size outsz st ready ops s G tn b data_var d.
  abi_builtin_decode_setup data min_size max_size outsz st = (ops,ready) /\
  fn_has_code st ready fn /\ fn_inst_ids_distinct fn /\ ~ctx_has_dalloca ctx /\
  local_ptrs_reserved ce st /\ origin.cs_next_var <= st.cs_next_var /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\ (?H. V H) /\
  alloca_history fn s /\ lo <= s.vs_alloca_next /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
    aid < origin.cs_next_id ==> off+sz <= s.vs_alloca_next) /\
  (!name a sz. local_region ce es0.scopes s0 name a sz ==>
    a+sz <= s.vs_alloca_next) /\
  (!H. V H ==> stmt_state_rel H ctx fn ce cx es s /\
    ghost_inv_at (DF H) lo delta ce cx es G tn s /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn) /\
  data = Var data_var /\ eval_operand data s = SOME (n2w b) /\
  op_taint tn data = {} /\ abi_decoder_operand_live st.cs_next_var data /\
  abi_decode_ptr_window G tn s data_var (n2w b) (32+LENGTH input_bytes) /\
  mload b s = n2w (LENGTH input_bytes) /\
  mem_bytes_at (b+32) (LENGTH input_bytes) s.vs_memory = input_bytes /\
  b+32+LENGTH input_bytes <= s.vs_alloca_next /\
  b+32+LENGTH input_bytes < dimword (:256) /\
  min_size <= max_size /\ max_size < dimword (:256) /\
  outsz < dimword (:256) /\ d+outsz < dimword (:256) /\
  (b+32+LENGTH input_bytes <= d \/ d+outsz <= b+32) /\
  ((FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) = NONE /\
      d = s.vs_alloca_next) \/
   FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) =
     SOME (d,outsz))``;

Theorem abi_decode_caller_prefix_joint:
  (^caller_setup_pre) data min_size max_size outsz st ready ops s G tn b data_var d /\
  emit_op MLOAD [data] st = (len,sa) /\
  emit_op ADD [data; Lit 32w] sa = (src,sb) ==>
  ?u Gp tnp.
    (!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK u,Gp,tnp)) /\
    (!obs. fn_has_code st sb obs ==> gas_path ctx obs s 0 (OK u)) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (?input. src = Var input /\
      abi_decode_ptr_window Gp tnp u input (n2w (b+32)) (LENGTH input_bytes)) /\
    eval_operand len u = SOME (n2w (LENGTH input_bytes)) /\
    op_prov Gp len = NONE /\ op_taint tnp len = {} /\ op_taint tnp src = {} /\
    abi_decoder_operand_live sb.cs_next_var len /\
    abi_decoder_operand_live sb.cs_next_var src /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\
    state_frame u = state_frame (s with vs_inst_idx := u.vs_inst_idx) /\
    tnp.t_mem = tn.t_mem /\ tnp.t_stor = tn.t_stor /\
    tnp.t_trans = tn.t_trans /\ tnp.t_imm = tn.t_imm /\ alloca_history fn u /\
    (!x. not_fresh_at st x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP Gp x = FLOOKUP G x /\ op_taint tnp (Var x) = op_taint tn (Var x)) /\
    (!H. V H ==> stmt_state_rel H ctx fn ce cx es u /\
      ghost_inv_at (DF H) lo delta ce cx es Gp tnp u /\
      ghost_kept_at lo ce es0 origin G0 tn0 s0 Gp tnp)
Proof
  BETA_TAC >> strip_tac >>
  `cs_extends st sa /\ cs_extends sa sb /\
   st.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sb.cs_next_var` by
    metis_tac[emit_op_extends_next_var] >>
  `?lv. len = Var lv` by metis_tac[emitted_insts_emit_op] >>
  `b < dimword (:256)` by decide_tac >>
  `ptr_covers G tn data_var s 32 /\ lookup_var data_var s = SOME (n2w b) /\
   (!i. w2n (n2w b:256 word) <= i /\ i < w2n (n2w b:256 word)+32 ==>
      i NOTIN tn.t_mem)` by
    (gvs[abi_decode_ptr_window_def, ptr_covers_def] >> rpt strip_tac >>
     first_x_assum irule >> simp[] >> decide_tac) >>
  drule_all (emit_mload_clean_normalized_ptr |> Q.INST [`D` |-> `ARB`]) >>
  disch_then (qspecl_then [`PG`, `fn`] strip_assume_tac) >>
  FAIL_TAC "mload witnesses"
QED
