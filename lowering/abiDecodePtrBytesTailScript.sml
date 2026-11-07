(* Pointer certificates for the exact runtime bytes tail. *)
Theory abiDecodePtrBytesTail
Ancestors
  abiDecoderBytesRuntime abiDecoderRange abiDecodeStaticProps abiDecodePtrRead abiDecodePtrNormalized
  bodyPtrBopScalarCompile bodyPtrBopScalarSeq bodyPtrBopScalarOutcome
  abiDecodePtrMemberFrame assignTuplePtrCopyLen
  emitHelperProps exprLoweringProps compileEnv emitHelper freshWrites
  venomState venomExecSemantics venomInst ptrDiscipline typedCopyPtr bodyPtrDefs
  list pred_set finite_map words arithmetic

(* Rounding is scalar even though the following address ADD is not. *)
Theorem abi_decode_bytes_round_scalar:
  emit_op ADD [cnt;Lit 31w] sa = (up,c1) /\
  emit_op NOT [Lit 31w] c1 = (mask,c2) /\
  emit_op AND [up;mask] c2 = (rounded,sb) /\
  cnt IN A /\ Lit 31w IN A /\
  (!x. x IN R ==> not_fresh_at sa x) ==>
  bop_scalar_seq R A (emitted_insts sa sb)
    (rounded INSERT mask INSERT up INSERT A)
Proof
  strip_tac >>
  `!x. x IN R ==> not_fresh_at c1 x` by
    (qpat_assum `emit_op ADD _ sa = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     fs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `!x. x IN R ==> not_fresh_at c2 x` by
    (qpat_assum `emit_op NOT _ _ = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     fs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `bop_scalar_seq R A (emitted_insts sa c1) (up INSERT A)` by
    (irule bop_scalar_seq_emit_op >> simp[] >>
     qexistsl_tac [`ADD`, `[cnt;Lit 31w]`] >> simp[]) >>
  `bop_scalar_seq R (up INSERT A) (emitted_insts c1 c2)
     (mask INSERT up INSERT A)` by
    (irule bop_scalar_seq_emit_op >> simp[] >>
     qexistsl_tac [`NOT`, `[Lit 31w]`] >> simp[]) >>
  `bop_scalar_seq R (mask INSERT up INSERT A) (emitted_insts c2 sb)
     (rounded INSERT mask INSERT up INSERT A)` by
    (irule bop_scalar_seq_emit_op >> simp[] >>
     qexistsl_tac [`AND`, `[up;mask]`] >> simp[]) >>
  imp_res_tac emit_op_extends >>
  `emitted_insts sa c2 = emitted_insts sa c1 ++ emitted_insts c1 c2` by
    (irule emitted_insts_append >> simp[]) >>
  `emitted_insts sa sb = emitted_insts sa c2 ++ emitted_insts c2 sb` by
    (irule emitted_insts_append >> simp[APPEND_ASSOC]) >>
  simp[] >> irule bop_scalar_seq_append >>
  qexists_tac `mask INSERT up INSERT A` >> simp[] >>
  irule bop_scalar_seq_append >> qexists_tac `up INSERT A` >> simp[]
QED

Theorem abi_decode_bytes_round_sequence:
  emit_op ADD [cnt;Lit 31w] sa = (up,c1) /\
  emit_op NOT [Lit 31w] c1 = (mask,c2) /\
  emit_op AND [up;mask] c2 = (rounded,sb) /\
  eval_operand cnt s = SOME (n2w c) /\
  c+31 < dimword(:256) /\ fresh_vars_wrt sa s ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand rounded t = SOME (n2w (32*((c+31) DIV 32))) /\
    fresh_vars_wrt sb t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section
Proof
  strip_tac >>
  `eval_operand (Lit 31w) s = SOME 31w` by simp[eval_operand_def] >>
  drule_all emit_op_ADD_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa c1) s = OK s1` >>
  `eval_operand (Lit 31w) s1 = SOME 31w` by simp[eval_operand_def] >>
  drule_all emit_op_NOT_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `eval_operand up s2 = SOME ((n2w c:bytes32)+31w)` by metis_tac[] >>
  drule_all emit_op_AND_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 sb) s2 = OK t` >>
  rpt (qpat_x_assum `!a. a < LENGTH _ ==> _` kall_tac) >>
  rpt (qpat_x_assum `LENGTH _.vs_memory = _` kall_tac) >>
  rpt (qpat_x_assum `same_blocks _ _` kall_tac) >>
  drule_all (abi_decode_pure_emit_frame |> Q.INST [`opc` |-> `ADD`] |> SRULE []) >>
  strip_tac >>
  drule_all abi_decode_NOT_emit_frame >> strip_tac >>
  drule_all abi_decode_AND_emit_frame >> strip_tac >>
  imp_res_tac inst_extends_emit_op >>
  ntac 2 (drule_all abi_decode_sequence_chain >> strip_tac) >>
  qexists_tac `t` >> simp[abi_decode_bytes_round_word] >> metis_tac[]
QED


Theorem abi_decode_bytes_round_ptr:
  emit_op ADD [cnt;Lit 31w] sa = (up,c1) /\
  emit_op NOT [Lit 31w] c1 = (mask,c2) /\
  emit_op AND [up;mask] c2 = (rounded,sb) /\
  eval_operand cnt s = SOME (n2w c) /\
  c+31 < dimword(:256) /\ fresh_vars_wrt sa s /\
  op_prov G cnt = NONE /\ op_taint tn cnt = {} /\ ~ctx_has_dalloca ctx /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. x IN R ==> not_fresh_at sa x) ==>
  ?t G' tn'.
    run_inst_seq (emitted_insts sa sb) s =
      OK (t with vs_inst_idx := s.vs_inst_idx) /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s G' tn' /\
    eval_operand rounded t = SOME (n2w (32*((c+31) DIV 32))) /\
    op_prov G' rounded = NONE /\ op_taint tn' rounded = {} /\
    fresh_vars_wrt sb t /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := LENGTH sb.cs_current_insts|> /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x IN R ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >> drule_all abi_decode_bytes_round_sequence >> strip_tac >>
  `bop_scalar_seq R {cnt;Lit 31w} (emitted_insts sa sb)
    (rounded INSERT mask INSERT up INSERT {cnt;Lit 31w})` by
    (irule abi_decode_bytes_round_scalar >> simp[] >> metis_tac[]) >>
  `!op. op IN {cnt;Lit 31w} ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    (simp[] >> rpt strip_tac >> gvs[op_prov_def,op_taint_def]) >>
  drule_all bop_scalar_seq_run >>
  disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
  drule_all bop_scalar_seq_runtime_frame >> strip_tac >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sb.cs_current_insts`, `G'`, `tn'`] >>
  `t.vs_inst_idx = s.vs_inst_idx` by
    (qpat_assum `t = s with vs_vars := _`
       (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `fresh_vars_wrt sb (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (qpat_x_assum `fresh_vars_wrt sb t` mp_tac >>
     simp[fresh_vars_wrt_def, lookup_var_def]) >>
  `eval_operand rounded (t with vs_inst_idx := LENGTH sb.cs_current_insts) =
     eval_operand rounded t` by
    (Cases_on `rounded` >> simp[NoAsms,eval_operand_def,lookup_var_def]) >>
  `op_prov G' rounded = NONE /\ op_taint tn' rounded = {}` by
    (qpat_x_assum `!op. op IN rounded INSERT _ ==> _`
       (qspec_then `rounded` mp_tac) >> simp[]) >>
  `t with vs_inst_idx := LENGTH sb.cs_current_insts =
     s with <|vs_vars := t.vs_vars; vs_inst_idx := LENGTH sb.cs_current_insts|>` by
    (qpat_assum `t = s with vs_vars := _`
       (fn th => once_rewrite_tac[th]) >> simp[NoAsms]) >>
  simp[] >> conj_tac
  >- (qpat_assum `t = s with vs_vars := _`
        (fn th => once_rewrite_tac[th]) >> simp[venom_state_component_equality]) >>
  rpt strip_tac >> simp[lookup_var_def] >>
  first_x_assum irule >> simp[]
QED

(* Address formation needs coverage, not initialization of the output buffer. *)
Theorem abi_decode_ptr_output_address_covers:
  ptr_covers G tn dst s cap /\ lookup_var dst s = SOME b /\
  q+k <= cap /\ w2n b+cap < dimword(:256) ==>
  ptr_covers
    (step_prov PG G (mk_inst id ADD [Var dst;pos] [out])
      (update_var out (b+n2w q) s))
    (step_taint (mk_inst id ADD [Var dst;pos] [out]) s
      (update_var out (b+n2w q) s) tn)
    out (update_var out (b+n2w q) s with vs_inst_idx := idx) k
Proof
  strip_tac >>
  `w2n (b+n2w q) = w2n b+q` by
    (irule w2n_add_n2w_lt >> decide_tac) >>
  fs[ptr_covers_def] >>
  simp[ptr_covers_def, copy_len_binop_ghost_frame,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       op_prov_def, mk_inst_def, FLOOKUP_UPDATE] >>
  qexistsl_tac [`b'`, `sz'`] >> simp[] >> decide_tac
QED
