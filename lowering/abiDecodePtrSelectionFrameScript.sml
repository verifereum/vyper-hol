Theory abiDecodePtrSelectionFrame
Ancestors
  abiDecodePtrHead abiDecodePtrBytesRuntimeFrame abiDecoderGuard abiEncoder
  emitHelper emitHelperProps exprLoweringProps compileEnv freshWrites
  abiEncoderWindowLookup venomExecSemantics venomState venomInst
  words arithmetic list rich_list finite_map assignTuplePtrLoadStep
  abiDecodePtrMemberFrame bodyPtrDefs ptrDiscipline stateFrame

(* Syntax, not offset arithmetic, supplies freshness for the next decoder. *)
Theorem abi_decode_selection_shape:
  compile_getelemptr_abi pos T off MLOAD (Var src) hi sa = (v,sb) ==>
  inst_extends sa sb /\ same_blocks sa sb /\
  sa.cs_next_var <= sb.cs_next_var /\
  EVERY (\i. (fresh_write_op i.inst_opcode \/ i.inst_opcode = MLOAD) /\
    EVERY (not_fresh_at sb) i.inst_outputs) (emitted_insts sa sb)
Proof
  Cases_on `hi = Lit 0w` >>
  simp[compile_getelemptr_abi_def, compile_abi_dec_addr_def,
       abi_decode_ge_guard_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
  rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[inst_extends_def, same_blocks_def, emitted_insts_def,
       DROP_LENGTH_APPEND] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, fresh_write_op_def] >>
  simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj]
QED

Theorem abi_decode_selection_runtime_fresh:
  compile_getelemptr_abi pos T off MLOAD (Var src) hi sa = (v,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK u /\ fresh_vars_wrt sa s ==>
  fresh_vars_wrt sb u
Proof
  strip_tac >> drule abi_decode_selection_shape >> strip_tac >>
  `fresh_vars_wrt sb s` by
    (irule fresh_vars_wrt_mono >> qexists_tac `sa` >> simp[]) >>
  irule abi_window_seq_fresh >>
  qexistsl_tac [`sb`, `emitted_insts sa sb`, `s`] >> simp[] >>
  fs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >> strip_tac >>
  gvs[fresh_write_op_simple]
QED

(* Keep the replay's ghosts and all its frame facts on the same witnesses. *)
Theorem abi_decode_selection_success_framed:
  compile_getelemptr_abi pos T off MLOAD (Var src) hi sa = (v,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  abi_decode_ptr_window G tn s src b h /\ not_fresh_at sa src /\
  (!x. pos = Var x ==> not_fresh_at sa x) /\
  eval_operand pos s = SOME z /\ op_prov G pos = NONE /\ op_taint tn pos = {} /\
  p = w2n (z + n2w off) /\ p+32 <= h /\ w2n b+h < dimword(:256) /\
  run_inst_seq (emitted_insts sa sb) s = OK u /\
  ghost_inv ret cenv cx es G tn s /\ stmt_state_rel ctx func cenv cx es s /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?out H tf. v = Var out /\ not_fresh_at sb out /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s H tf /\
    gas_path_ptr D 0 ctx func PG G tn s 0 H tf
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    lookup_var out u = SOME (z + mload (w2n b+p) s) /\
    op_prov H v = NONE /\ op_taint tf v = {} /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    state_frame u = state_frame s /\ u.vs_memory = s.vs_memory /\
    u.vs_allocas = s.vs_allocas /\ u.vs_accounts = s.vs_accounts /\
    u.vs_transient = s.vs_transient /\ u.vs_call_ctx = s.vs_call_ctx /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    ghost_inv ret cenv cx es H tf u /\ stmt_state_rel ctx func cenv cx es u /\
    abi_decode_ptr_window H tf u src b h /\
    (!x k. not_fresh_at sa x /\ ptr_covers G tn x s k ==> ptr_covers H tf x u k) /\
    (fresh_vars_wrt sa s ==> fresh_vars_wrt sb u)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_decode_getelemptr_success_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s H tf` >>
  `ghost_inv ret cenv cx es H tf u` by
    (irule ghost_inv_old_vars_frame_ptr >>
     goal_assum (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
     qexists_tac `sa` >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es u` by
    (irule stmt_state_rel_old_vars_frame_ptr >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
     qexists_tac `sa` >> fs[state_frame_def, venom_state_component_equality]) >>
  `abi_decode_ptr_window H tf u src b h` by
    (irule abi_decode_ptr_window_frame >>
     goal_assum (drule_at (Pat `abi_decode_ptr_window _ _ _ _ _ _`)) >> simp[]) >>
  `!x k. not_fresh_at sa x /\ ptr_covers G tn x s k ==> ptr_covers H tf x u k` by
    (rpt strip_tac >> fs[ptr_covers_def] >> metis_tac[]) >>
  qexistsl_tac [`out`, `H`, `tf`] >> simp[] >>
  conj_tac
  >- (qpat_x_assum `state_frame u = state_frame s` mp_tac >>
      simp[state_frame_def, venom_state_component_equality]) >>
  strip_tac >> irule abi_decode_selection_runtime_fresh >>
  goal_assum (drule_at (Pat `compile_getelemptr_abi _ _ _ _ _ _ _ = _`)) >>
  qexists_tac `s` >> simp[]
QED
