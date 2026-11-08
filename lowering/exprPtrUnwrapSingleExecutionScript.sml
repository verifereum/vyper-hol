(* Attach the two checked slot-copy instructions to their compiled cursor. *)
Theory exprPtrUnwrapSingleExecution
Ancestors
  exprPtrUnwrapSingleSegment exprPtrUnwrapFrames ghostPcTransportPtr
  fragGasSeqPtr fragExec exprLoweringProps slotCopyExecution bodyPtrDefs
  venomState venomInst ptrDiscipline ptrSafeRun list rich_list arithmetic

Theorem unwrap_single_slot_execution:
  (load = SLOAD \/ load = TLOAD) /\
  same_blocks sa sb /\ isPREFIX sa.cs_current_insts sb.cs_current_insts /\
  fn_has_code sa sb fn /\
  emitted_insts sa sb =
    [mk_inst id load [src] [out]; mk_inst (id+1) MSTORE [Var root;Var out] []] /\
  eval_operand src s = SOME key /\ op_taint tn src = {} /\ root <> out /\
  ptr_covers G tn root s 32 /\ lookup_var root s = SOME addr /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?Gf tnf t.
    gas_path_ptr D lo ctx fn PG G tn s 0 Gf tnf (OK t) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t = (mstore (w2n addr) (slot_copy_word load s key)
      (update_var out (slot_copy_word load s key) s)
        with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    tnf.t_mem =
      (tn.t_mem DIFF {j | w2n addr <= j /\ j < w2n addr+32}) UNION
        {w2n addr+k | k IN key_taint
          (if load=SLOAD then tn.t_stor else tn.t_trans) key} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!x. x <> out ==> FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tnf (Var x) = op_taint tn (Var x)) /\
    (!x k. x <> out /\ ptr_covers G tn x s k ==> ptr_covers Gf tnf x t k)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule_all copy_single_slot_segment >>
  disch_then (qspecl_then [`id`, `fn`, `PG`, `D`] strip_assume_tac) >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[same_blocks_def, fn_has_code_def, IS_PREFIX_APPEND] >>
     gvs[emitted_insts_def] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
     gvs[DROP_LENGTH_APPEND]) >>
  `LENGTH sa.cs_current_insts + 2 = LENGTH sb.cs_current_insts` by
    (`LENGTH (emitted_insts sa sb) = 2` by simp[] >>
     gvs[emitted_insts_def, IS_PREFIX_APPEND, DROP_LENGTH_APPEND]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    [mk_inst id load [src] [out]; mk_inst (id+1) MSTORE [Var root;Var out] []]` by
    (gvs[mk_inst_def, is_terminator_def]) >>
  `isPREFIX [mk_inst id load [src] [out];
     mk_inst (id+1) MSTORE [Var root;Var out] []]
     (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
  drule_all run_inst_seq_gas_path_ptr >>
  simp[mk_inst_def] >> strip_tac >>
  qexistsl [`Gf`, `tnf`] >>
  asm_rewrite_tac[] >>
  gvs[same_blocks_def, mstore_def, update_var_def]
QED
