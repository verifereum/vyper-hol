Theory abiDecodePtrMember
Ancestors
  abiDecodePtrSelectionFrame abiDecodePtrWord abiDecodePtrBytesFramed
  abiDecodePtrBytesTail abiDecodePtrMemberFrame assignTuplePtrLoadStep
  bodyPtrDefs ptrDiscipline emitHelper emitHelperProps exprLoweringProps
  compileEnv freshWrites abiEncoderWindowLookup venomExecSemantics venomState
  venomInst finite_map words arithmetic list stateFrame

(* Destination setup is a pointer ADD, not part of scalar head selection.
   Keep its frame and coverage on the same replay witnesses. *)
Theorem abi_decode_member_destination_ptr:
  emit_op ADD [Var dst;Lit (n2w q)] sa = (Var out,sb) /\
  ptr_covers G tn dst s cap /\ lookup_var dst s = SOME b /\
  ~ctx_has_dalloca ctx /\ q+k <= cap /\ w2n b+cap < dimword(:256) /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ghost_inv ret cenv cx es G tn s /\ stmt_state_rel ctx func cenv cx es s /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?t H tm.
    run_inst_seq (emitted_insts sa sb) s = OK (t with vs_inst_idx := s.vs_inst_idx) /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s H tm /\
    ptr_covers H tm out t k /\ lookup_var out t = SOME (b+n2w q) /\
    not_fresh_at sb out /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\ t.vs_memory = s.vs_memory /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)) /\
    ghost_inv ret cenv cx es H tm t /\ stmt_state_rel ctx func cenv cx es t /\
    (fresh_vars_wrt sa s ==> fresh_vars_wrt sb t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `eval_operand (Lit (n2w q)) s = SOME (n2w q) /\
   op_taint tn (Lit (n2w q)) = {} /\ op_taint tn (Var dst) = {}` by
    fs[eval_operand_def, op_taint_def, ptr_covers_def] >>
  drule_all abi_decode_ptr_output_address >>
  disch_then (qspecl_then [`func`, `PG`, `D`] mp_tac) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `inst_seq_ptr D 0 ctx func PG G tn
    (emitted_insts sa sb) s H tm` >>
  qmatch_asmsub_abbrev_tac `ptr_covers H tm out t k` >>
  `state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
   t.vs_memory = s.vs_memory /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient /\ t.vs_call_ctx = s.vs_call_ctx` by
    simp[Abbr `t`, state_frame_def, update_var_def] >>
  `ghost_inv ret cenv cx es H tm t` by
    (irule ghost_inv_old_vars_frame_ptr >>
     goal_assum (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
     qexists_tac `sa` >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es t` by
    (irule stmt_state_rel_old_vars_frame_ptr >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
     qexists_tac `sa` >> fs[Abbr `t`, update_var_def]) >>
  `not_fresh_at sb out` by
    (drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
     simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj]) >>
  qexistsl [`t`, `H`, `tm`] >> asm_rewrite_tac[] >> strip_tac >>
  `fresh_vars_wrt sb s` by
    (irule fresh_vars_wrt_mono >> qexists_tac `sa` >>
     drule emitted_insts_emit_op >> simp[]) >>
  simp[Abbr `t`, fresh_vars_wrt_def] >>
  fs[fresh_vars_wrt_def, not_fresh_at_def] >> metis_tac[]
QED
