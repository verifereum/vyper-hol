Theory abiDecodePtrMember
Ancestors
  abiDecodePtrSelectionFrame abiDecodePtrWord abiDecodePtrBytesFramed
  abiDecodePtrBytesTail abiDecodePtrMemberFrame assignTuplePtrLoadStep
  bodyPtrDefs ptrDiscipline emitHelper emitHelperProps exprLoweringProps
  compileEnv freshWrites abiEncoderWindowLookup venomExecSemantics venomState
  venomInst finite_map words arithmetic list stateFrame pred_set
  bodyPtrBopScalarCompile bodyPtrBopScalarSeq bodyPtrBopScalarOutcome
  abiEncoder abiDecodePtrHead abiDecodePtrPosition abiEncoderWindowSequence

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

(* The static branch has no input read, so it needs no header window. *)
Theorem abi_decode_static_selection_framed:
  compile_getelemptr_abi pos F off MLOAD (Var src) hi sa = (v,sb) /\
  (!x. pos = Var x ==> not_fresh_at sa x) /\
  eval_operand pos s = SOME z /\ op_prov G pos = NONE /\ op_taint tn pos = {} /\
  ~ctx_has_dalloca ctx /\ run_inst_seq (emitted_insts sa sb) s = OK u /\
  ghost_inv ret cenv cx es G tn s /\ stmt_state_rel ctx func cenv cx es s /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?out H tf. v = Var out /\ not_fresh_at sb out /\
    lookup_var out u = SOME (z+n2w off) /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s H tf /\
    op_prov H v = NONE /\ op_taint tf v = {} /\
    state_frame u = state_frame s /\ u.vs_memory = s.vs_memory /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    ghost_inv ret cenv cx es H tf u /\ stmt_state_rel ctx func cenv cx es u /\
    (fresh_vars_wrt sa s ==> fresh_vars_wrt sb u)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `emit_op ADD [pos;Lit (n2w off)] sa = (v,sb)` by
    (Cases_on `emit_op ADD [pos;Lit (n2w off)] sa` >>
     fs[compile_getelemptr_abi_def, comp_bind_def, comp_return_def]) >>
  `bop_scalar_seq {x | not_fresh_at sa x} {pos;Lit (n2w off)}
    (emitted_insts sa sb) (v INSERT {pos;Lit (n2w off)})` by
    (irule bop_scalar_seq_emit_op >> simp[] >>
     qexistsl [`ADD`, `[pos;Lit (n2w off)]`] >> simp[]) >>
  `!op. op IN {pos;Lit (n2w off)} ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    (simp[] >> rpt strip_tac >> gvs[op_prov_def, op_taint_def]) >>
  drule_all bop_scalar_seq_run >>
  disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
  drule_all bop_scalar_seq_runtime_frame >> strip_tac >>
  mp_tac (Q.INST [`hi` |-> `Lit 0w`, `mid` |-> `sb`,
    `offset` |-> `Lit (n2w off)`, `w` |-> `n2w off`]
    abi_decode_position_suffix_result) >>
  simp_tac bool_ss [] >>
  (impl_tac >- simp[eval_operand_def]) >> strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
    FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)` by
    (fs[lookup_var_def, op_taint_def] >> metis_tac[]) >>
  `u.vs_memory = s.vs_memory /\ u.vs_accounts = s.vs_accounts /\
   u.vs_transient = s.vs_transient /\ u.vs_call_ctx = s.vs_call_ctx /\
   state_frame u = state_frame s /\ u.vs_inst_idx = s.vs_inst_idx` by
    (qpat_x_assum `u = s with vs_vars := _` SUBST1_TAC >> simp[state_frame_def]) >>
  `ghost_inv ret cenv cx es G' tn' u` by
    (irule ghost_inv_old_vars_frame_ptr >>
     goal_assum (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
     qexists_tac `sa` >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es u` by
    (irule stmt_state_rel_old_vars_frame_ptr >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
     qexists_tac `sa` >>
     conj_tac >- simp[] >> conj_tac
     >- (qpat_x_assum `u = s with vs_vars := _` SUBST1_TAC >> simp[state_frame_def]) >>
     simp[]) >>
  qpat_x_assum `u = s with vs_vars := _` kall_tac >>
  qexistsl [`out`, `G'`, `tn'`] >> asm_rewrite_tac[] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> strip_tac >>
  irule abi_window_seq_fresh >>
  goal_assum (drule_at (Pat `run_inst_seq _ _ = _`)) >>
  qexists_tac `sb` >> simp[] >> conj_tac
  >- (drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
      simp[mk_inst_def, not_fresh_at_def, ASCIInumbersTheory.toString_inj]) >>
  irule fresh_vars_wrt_mono >> qexists_tac `sa` >>
  drule emitted_insts_emit_op >> simp[]
QED
