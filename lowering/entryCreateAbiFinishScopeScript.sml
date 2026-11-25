Theory entryCreateAbiFinishScope
Ancestors
  abiEncodeValuesFinish abiEncodeValuesLayout abiEncoderWindowPhase
  entryCreateAdminSequence entryCreateFocusSpec exprSimAbiEncodeExecFrame
  exprLoweringProps emitHelperProps abiEncoderProps fragExec emitHelper
  fragGasOriginPtr bodyPtrDefs ptrDiscipline compileEnv
  valueEncodingDefs contractABI venomState venomInst words finite_map pred_set list

(* The bytes, size and confined path all refer to the same cursor load. *)
Theorem create_abi_cursor_finish_confined:
  emit_op MLOAD [Var cursor] st = (out,en) /\
  eval_operand (Var cursor) s = SOME (n2w slot) /\ ptr_covers G tn cursor s 32 /\
  slot + 32 <= s.vs_alloca_next /\ mem_word_at slot s.vs_memory = n2w (hl + tl) /\
  (!i. slot <= i /\ i < slot + 32 ==> i NOTIN tn.t_mem) /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  LIST_REL abi_encoder_layout_valid tys vs /\
  hl = head_lengths tys 0 /\ tl = LENGTH (FLAT (abi_tuple_tails tys vs)) /\
  abi_encoder_tuple_prefix hl tys vs d s.vs_memory /\
  (!i. d <= i /\ i < d + hl ==> i NOTIN tn.t_mem) /\
  (!i. d + hl <= i /\ i < d + hl + tl ==> i NOTIN tn.t_mem) /\
  bytes = enc (Tuple tys) (ListV vs) ==>
  ?t G' tn'.
    create_operand_full_scope st en explicit ctx func s [] (OK t) /\
    eval_operand out t = SOME (n2w (LENGTH bytes)) /\ op_taint tn' out = {} /\
    (!x. out = Var x ==> not_fresh_at en x) /\
    mem_bytes_at d (LENGTH bytes) t.vs_memory = bytes /\
    (!i. d <= i /\ i < d + LENGTH bytes ==> i NOTIN tn'.t_mem) /\
    window_phase ctx func st en {} [] s t /\ abi_encode_exec_frame func s t /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\ t.vs_memory = s.vs_memory /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')
Proof
  strip_tac >> drule_all abi_encode_values_finish_run >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`t`,`G'`,`tn'`] strip_assume_tac)) >>
  qexistsl_tac [`t`,`G'`,`tn'`] >> conj_tac
  >- (`t.vs_inst_idx = LENGTH en.cs_current_insts` by
        metis_tac[window_phase_control] >>
      `create_operand_full_scope st en explicit ctx func s []
        (OK ((t with vs_inst_idx := s.vs_inst_idx) with
             vs_inst_idx := LENGTH en.cs_current_insts))` suffices_by
        (`(t with vs_inst_idx := LENGTH en.cs_current_insts) = t` by
           simp[venom_state_component_equality] >> simp[]) >>
      drule emitted_insts_emit_op >> strip_tac >>
      drule emit_op_same_blocks >> strip_tac >>
      irule create_admin_sequence_scope >>
      fs[create_operand_at_def, same_blocks_def, frag_ids_def, mk_inst_def,
         is_terminator_def]) >>
  asm_rewrite_tac[]
QED
