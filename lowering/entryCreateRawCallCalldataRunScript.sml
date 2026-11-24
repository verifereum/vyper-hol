(* Keep the copy's scoped traversal at the joint producer's physical landing. *)
Theory entryCreateRawCallCalldataRun
Ancestors
  bodyFullRawCallCalldataCopy entryCreateAdminSequence dallocaCalldata
  entryCreateFocusSpec builtinSystem abiEncoderProps venomInst words pred_set
  fragExec fragGasOriginPtr compileEnv bodySim contextRawReachable
  unitTransformDefs venomState ptrDiscipline finite_map arithmetic
  memSafeRun venomExecSemantics

Theorem raw_call_calldata_copy_selected:
  compile_msg_data_to_memory sa = ((dp,dl),sb) /\
  fn_has_code sa sb func /\ body_inv tops ctx cenv cx /\
  MEM func ctx.ctx_functions /\ ctx_has_dalloca ctx /\
  gas_origin_ptr_path (D0,lo,explicit0,ctx,func,PG)
    (s0,G0,tn0) marks (OK s,G,tn) /\
  (!fn inst v. contextRawReachable$frag_reachable ctx func s0 fn inst v ==>
     dalloca_fmp_headroom inst v) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ allocas_below_fmp s /\
  w2n s.vs_initial_fmp <= w2n s.vs_fmp /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) ==>
  ?t G' tn' p.
    (!explicit. create_operand_full_scope sa sb explicit ctx func s [] (OK t)) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    dp = Var p /\ eval_operand dp t = SOME s.vs_fmp /\
    eval_operand dl t = SOME (n2w (LENGTH s.vs_call_ctx.cc_calldata)) /\
    ptr_covers G' tn' p t (LENGTH s.vs_call_ctx.cc_calldata) /\
    op_taint tn' dl = {} /\ op_taint tn' dp = {} /\ op_prov G' dl = NONE /\
    read_memory (w2n s.vs_fmp) (LENGTH s.vs_call_ctx.cc_calldata) t =
      s.vs_call_ctx.cc_calldata /\
    w2n t.vs_fmp = w2n s.vs_fmp + venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata) /\
    t.vs_memory =
      (write_memory_with_expansion (w2n s.vs_fmp) s.vs_call_ctx.cc_calldata s).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx;
              vs_memory := s.vs_memory; vs_fmp := s.vs_fmp|>) = s /\
    tn'.t_mem =
      (tn.t_mem UNION {i | w2n s.vs_fmp <= i /\ i < w2n t.vs_fmp})
        DIFF {i | w2n s.vs_fmp <= i /\
                    i < w2n s.vs_fmp + LENGTH s.vs_call_ctx.cc_calldata} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ allocas_below_fmp t
Proof
  disch_then (fn pre => strip_assume_tac pre >>
    strip_assume_tac (MATCH_MP calldata_memory_joint_run_with_seq pre)) >>
  qpat_x_assum `compile_msg_data_to_memory _ = _`
    (fn code => strip_assume_tac (MATCH_MP calldata_memory_placement code) >>
                strip_assume_tac (MATCH_MP calldata_memory_insts code)) >>
  `!explicit. create_operand_full_scope sa sb explicit ctx func s [] (OK t)` by
    (gen_tac >>
     `create_operand_full_scope sa sb explicit ctx func s []
         (OK ((t with vs_inst_idx := s.vs_inst_idx) with
              vs_inst_idx := LENGTH sb.cs_current_insts))` by
       (irule create_admin_sequence_scope >>
        simp[create_operand_at_def, frag_ids_def, mk_inst_def, is_terminator_def] >>
        decide_tac) >>
     `((t with vs_inst_idx := s.vs_inst_idx) with
         vs_inst_idx := LENGTH sb.cs_current_insts) = t` by
       simp[venom_state_component_equality] >>
     pop_assum (fn norm => qpat_assum `create_operand_full_scope _ _ _ _ _ _ _ _`
       (ACCEPT_TAC o PURE_REWRITE_RULE [norm]))) >>
  qexistsl_tac [`t`,`G'`,`tn'`,`p`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
