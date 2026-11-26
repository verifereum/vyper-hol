(* The observed head-address ADD does not write the payload or the cursor. *)
Theory bodyExtStaticHeadAddressMods
Ancestors
  abiEncodeValuesPhases abiEncodeValuesPrefixFrame abiEncodeValuesRun
  abiEncoderWindowPhase abiEncoderRegisteredEffect abiEncoderWindowContract
  exprSimAbiEncodeExecFrame exprLoweringProps fragGasOriginPtr fragExec
  bodyPtrDefs ptrDiscipline compileEnv context emitHelper venomInst venomState
  finite_map list pred_set words pair

Theorem ext_static_head_address_mods:
  emit_op ADD [Var dst;Lit (n2w off)] st = (head,en) /\
  eval_operand (Var dst) s = SOME (n2w b) /\ ptr_covers G tn dst s cap /\
  off + n <= cap /\ b + cap <= s.vs_alloca_next /\ fn_has_code st en func /\
  alloca_inv s /\ alloca_room ctx func s /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encode_values_prefix_at ats avs hl b cursor loc slot i st s G tn ==>
  ?p t G' tn'.
    head = Var p /\ not_fresh_at en p /\ ptr_covers G' tn' p t n /\
    eval_operand head t = SOME (n2w (b+off)) /\ op_taint tn' head = {} /\
    abi_encode_values_prefix_at ats avs hl b cursor loc slot i en t G' tn' /\
    ci_mono st en /\ window_phase ctx func st en {} [] s t /\
    abi_encode_exec_frame func s t /\
    (!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==>
           lookup_var x t = SOME w) /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ci_mono st en` by
    (qspec_then `st` mp_tac (Q.SPECL [`ADD`,`[Var dst;Lit (n2w off)]`] ci_mono_emit_op) >>
     simp[]) >>
  mp_tac abi_encode_values_head_address >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`p`,`t`,`G'`,`tn'`]
    (map_every assume_tac o CONJUNCTS)) >>
  `abi_encode_values_prefix_at ats avs hl b cursor loc slot i en t G' tn'` by
    (irule abi_encode_values_prefix_arith >>
     qpat_assum `window_phase ctx func st en {} [] s t` (irule_at Any) >>
     qpat_assum `abi_encode_values_prefix_at _ _ _ _ _ _ _ _ st s G tn`
       (irule_at Any) >> asm_rewrite_tac[]) >>
  `op_taint tn' head = {}` by
    (qpat_assum `ptr_covers G' tn' p t n`
       (mp_tac o REWRITE_RULE [ptr_covers_def]) >> simp[]) >>
  `t.vs_allocas = s.vs_allocas` by
    (drule window_phase_effect >>
     simp[abi_encoder_registered_effect_def] >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     simp[FLOOKUP_EXT,FUN_EQ_THM]) >>
  `!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==>
     lookup_var x t = SOME w` by
    (drule window_phase_vars >> simp[]) >>
  qexistsl [`p`,`t`,`G'`,`tn'`] >> asm_rewrite_tac[]
QED
