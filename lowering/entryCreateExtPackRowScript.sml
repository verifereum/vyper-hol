(* Confinement at the actual execution cursors of an ABI packing row. *)
Theory entryCreateExtPackRow
Ancestors
  entryCreateAdminSequence abiEncodeValuesPhases bodyFullAbiEncodeOffset
  entryCreateFocusSpec entryCreateCompletedCut
  bodyPtrMakeArrayEmission emitHelperProps fragExec exprLoweringProps abiEncoderProps
  abiEncoderWindowPhase exprSimAbiEncodeExecFrame fragGasOriginPtr ptrDiscipline
  venomExecSemantics venomState venomInst words finite_map arithmetic

(* The head address is the first actual ADD of either kind of row.  The
   concrete state equation used by its ghost producer determines the edge. *)
Theorem abi_pack_head_add_scope:
  emit_op ADD [Var dst;Lit (n2w off)] a = (Var head,b) /\
  fn_has_code a b func /\ ~s.vs_halted /\ create_operand_at a s /\
  lookup_var dst s = SOME bw ==>
  create_operand_full_scope a b explicit ctx func s []
    (OK (update_var head (bw + n2w off) s with
         vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `s.vs_current_bb = a.cs_current_bb /\
   s.vs_inst_idx = LENGTH a.cs_current_insts` by fs[create_operand_at_def] >>
  drule_all emit_op_fetch_boundary >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `run_inst_seq (emitted_insts a b) s =
   OK (update_var head (bw + n2w off) s)` by
    gvs[run_inst_seq_def, mk_inst_def, step_inst_base_opcode_eqs,
         exec_pure2_def, eval_operand_def] >>
  qpat_assum `SUC s.vs_inst_idx = LENGTH b.cs_current_insts`
    (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
  irule create_admin_sequence_scope >>
  simp[frag_ids_def, mk_inst_def, is_terminator_def] >>
  metis_tac[]
QED

Theorem abi_encode_values_head_address_scoped:
  emit_op ADD [Var dst;Lit (n2w off)] st = (head,en) /\
  eval_operand (Var dst) s = SOME (n2w b) /\ ptr_covers G tn dst s cap /\
  off + n <= cap /\ b + cap <= s.vs_alloca_next /\ fn_has_code st en func /\
  alloca_inv s /\ alloca_room ctx func s /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ create_operand_at st s ==>
  ?p t G' tn'.
    head = Var p /\ not_fresh_at en p /\ ptr_covers G' tn' p t n /\
    eval_operand head t = SOME (n2w (b+off)) /\
    window_phase ctx func st en {} [] s t /\ abi_encode_exec_frame func s t /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\ t.vs_memory = s.vs_memory /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    create_operand_full_scope st en explicit ctx func s [] (OK t)
Proof
  strip_tac >>
  `s.vs_current_bb = st.cs_current_bb /\
   s.vs_inst_idx = LENGTH st.cs_current_insts` by fs[create_operand_at_def] >>
  drule_all abi_encode_values_head_address_endpoint >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`p`,`t`,`G'`,`tn'`] strip_assume_tac)) >>
  `lookup_var dst s = SOME (n2w b)` by fs[eval_operand_def] >>
  `create_operand_full_scope st en explicit ctx func s [] (OK t)` by
    (qpat_assum `t = _` SUBST1_TAC >> irule abi_pack_head_add_scope >> metis_tac[]) >>
  qexistsl_tac [`p`,`t`,`G'`,`tn'`] >> asm_rewrite_tac[]
QED
