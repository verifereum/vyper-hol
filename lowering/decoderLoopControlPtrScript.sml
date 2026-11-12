(* Concrete pointer-safe control edges of the calldata decoder loop. *)
Theory decoderLoopControlPtr
Ancestors decoderLoopHeaderCorePtr decoderLoopBackedgeCorePtr abiDecoderContract instIdxIndep ghostPcTransportPtr memLocDefs bodyPtrDefs decoderGhostFramePtr decoderProtectedScratchPtr typedCopyPtr abiDecoderExecution abiDecoderFrame
  entryDispatchPtr typedCopyArrayPtr ptrSafeRun ptrDiscipline
  codegenRel emitHelperProps contextCodegenRel exprLoweringProps
  venomExecSemantics venomState venomInst finite_map pred_set words list arithmetic

Theorem decoder_index_backedge_ptr:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv nv (Var q) hdr /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\ q <> nv /\
  ptr_covers G tn q s 32 /\ lookup_var q s = SOME (n2w slot) /\
  slot + 32 < dimword (:256) /\
  eval_operand (Var iv) s = SOME (n2w j) /\
  op_taint tn (Var iv) = {} /\ op_prov G (Var iv) = NONE /\
  j < ncount /\ ncount < dimword (:256) /\ DISJOINT P tn.t_mem /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  lookup_block hdr fn.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 ==>
  ?H u t.
    t = jump_to hdr (mstore slot (n2w (SUC j)) (update_var nv (n2w (SUC j)) s)) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_initial_fmp = s.vs_initial_fmp /\
    t.vs_fmp = s.vs_fmp /\ ptr_covers H u q t 32 /\
    mload slot t = n2w (SUC j) /\
    DISJOINT {a | slot <= a /\ a < slot + 32} u.t_mem /\
    DISJOINT P u.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\
    (!x. x <> nv ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    op_taint u (Var nv) = {} /\ op_prov H (Var nv) = NONE /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> drule_all decoder_index_backedge_ptr_core >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >> qexistsl_tac [`H`, `u`, `t`] >> simp[]
QED

Theorem decoder_index_header_ptr:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions =
    abi_decode_header_insts id (Var q) src CALLDATALOAD iv cv cmp done body_lbl exit_lbl /\
  s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  ALL_DISTINCT [q;iv;cv;cmp;done] /\ src <> Var iv /\
  ptr_covers G tn q s 32 /\ lookup_var q s = SOME (n2w slot) /\
  slot + 32 < dimword (:256) /\ mload slot s = n2w j /\
  DISJOINT {a | slot <= a /\ a < slot + 32} tn.t_mem /\
  eval_operand src s = SOME srcaddr /\ op_taint tn src = {} /\
  abi_decode_load CALLDATALOAD srcaddr s = n2w ncount /\
  j <= ncount /\ ncount < dimword (:256) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  lookup_block body_lbl fn.fn_blocks = SOME body_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\
  lookup_block exit_lbl fn.fn_blocks = SOME exit_bb /\
  phi_prefix_length exit_bb.bb_instructions = 0 ==>
  ?H u t.
    t = jump_to (if j < ncount then body_lbl else exit_lbl)
          (abi_decode_header_state iv cv cmp done j ncount s) /\
    t.vs_allocas = s.vs_allocas /\
    t.vs_initial_fmp = s.vs_initial_fmp /\ t.vs_fmp = s.vs_fmp /\
    ptr_covers H u q t 32 /\ mload slot t = n2w j /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\
    (!x. ~MEM x [iv;cv;cmp;done] ==>
       lookup_var x t = lookup_var x s /\
       FLOOKUP H x = FLOOKUP G x /\
       op_taint u (Var x) = op_taint tn (Var x)) /\
    (!x. MEM x [iv;cv;cmp;done] ==>
       op_taint u (Var x) = {} /\ op_prov H (Var x) = NONE) /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
       !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> drule_all decoder_index_header_ptr_core >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`H`, `u`, `t`] >> simp[]
QED
