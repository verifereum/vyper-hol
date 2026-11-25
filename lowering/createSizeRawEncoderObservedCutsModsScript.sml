Theory createSizeRawEncoderObservedCutsMods
Ancestors
  createSizePrefixReplay createCtorObservedSilence createMarkedPath
  bodyPtrMakeArrayEmission bodyPtrMakeArrayPrimitiveInstall
  context compileEnv fragExec fragGasOrigin gasEvents venomExecSemantics
  venomInst venomInstProofs1 venomState arithmetic relation pair list words

(* Read both marks and the next PC from the actual observed successor. *)
Theorem raw_observed_straight_edge[local]:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  gas_origin_edge F explicit ctx func s ms (OK t) ==>
  ms = [] /\ t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = SUC s.vs_inst_idx
Proof
  rw[gas_origin_edge_def] >>
  Cases_on `step_inst_base i s` >>
  gvs[step_inst_non_invoke,exit_result_def,Once gas_events_step_def] >>
  drule_all step_inst_base_preserves_all >> simp[]
QED

Theorem raw_observed_encoder_silence[local]:
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  create_expr_prefix a b explicit ctx func s ms t /\
  (t.vs_current_bb,t.vs_inst_idx) = (b.cs_current_bb,LENGTH b.cs_current_insts) /\
  gas_origin_path T explicit ctx func s [] (OK t) ==>
  ms = []
Proof
  simp[create_expr_prefix_marked] >> strip_tac >>
  irule ctor_observed_cut_silent >>
  qexistsl [`ctx`,`(b.cs_current_bb,LENGTH b.cs_current_insts)`,`explicit`,`func`,`t`,`s`] >>
  simp[] >> qpat_x_assum `RTC _ _ _` mp_tac >> match_mp_tac RTC_MONOTONE >>
  simp[FORALL_PROD,create_marked_edge_def,create_prefix_step_def,PULL_EXISTS]
QED

Theorem raw_encoder_observed_cuts_mods:
  0 < N /\ se = C N /\ s = St N /\
  (!i. i < N ==>
    ((St (SUC i)).vs_current_bb,(St (SUC i)).vs_inst_idx) =
    ((C (SUC i)).cs_current_bb,LENGTH (C (SUC i)).cs_current_insts)) /\
  compile_alloc_buffer capacity se = (buf,a) /\ fn_has_code se a func /\
  compile_copy_memory_dynamic buf.buf_operand (Var src) (Var len) a = ((),b) /\
  fn_has_code a b func /\ emit_op ADD [buf.buf_operand;Var len] b = (dst_op,st) /\
  fn_has_code b st func /\
  gas_origin_edge F explicit ctx func s am (OK su) /\
  gas_origin_edge F explicit ctx func su bm (OK sv) /\
  gas_origin_edge F explicit ctx func sv cm (OK u) /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  create_expr_prefix st en explicit ctx func u encmarks t /\
  (t.vs_current_bb,t.vs_inst_idx) = (en.cs_current_bb,LENGTH en.cs_current_insts) ==>
  am = [] /\ bm = [] /\ cm = [] /\
  (su.vs_current_bb,su.vs_inst_idx) = (a.cs_current_bb,LENGTH a.cs_current_insts) /\
  (sv.vs_current_bb,sv.vs_inst_idx) = (b.cs_current_bb,LENGTH b.cs_current_insts) /\
  (u.vs_current_bb,u.vs_inst_idx) = (st.cs_current_bb,LENGTH st.cs_current_insts) /\
  (gas_origin_path T explicit ctx func u [] (OK t) ==> encmarks = [])
Proof
  strip_tac >>
  `s.vs_current_bb = se.cs_current_bb /\ s.vs_inst_idx = LENGTH se.cs_current_insts` by
    (`PRE N < N /\ SUC (PRE N) = N` by decide_tac >>
     qpat_assum `!i. i < N ==> _` (qspec_then `PRE N` mp_tac) >> simp[]) >>
  `am = [] /\ su.vs_current_bb = a.cs_current_bb /\ su.vs_inst_idx = LENGTH a.cs_current_insts` by
    (`?tmp. emit_op ALLOCA [Lit (n2w capacity)] se = (tmp,a)` by
       (Cases_on `emit_op ALLOCA [Lit (n2w capacity)] se` >>
        fs[compile_alloc_buffer_def,comp_bind_def,comp_return_def]) >>
     pop_assum strip_assume_tac >>
     drule_all (Q.INST [`opc` |-> `ALLOCA`] emit_op_fetch_boundary) >> strip_tac >>
     drule_all (SIMP_RULE (srw_ss()) [is_terminator_def]
       (Q.INST [`i` |-> `mk_inst id ALLOCA ops outs`] raw_observed_straight_edge)) >> simp[]) >>
  `bm = [] /\ sv.vs_current_bb = b.cs_current_bb /\ sv.vs_inst_idx = LENGTH b.cs_current_insts` by
    (`emit_void MCOPY [buf.buf_operand;Var src;Var len] a = ((),b)` by
       fs[compile_copy_memory_dynamic_def] >>
     drule_all emit_void_fetch_boundary >> strip_tac >>
     `?bb. lookup_block su.vs_current_bb func.fn_blocks = SOME bb /\
           get_instruction bb su.vs_inst_idx = SOME
             (mk_inst a.cs_next_id MCOPY [buf.buf_operand;Var src;Var len] [])` by fs[] >>
     pop_assum strip_assume_tac >>
     drule_all (SIMP_RULE (srw_ss()) [is_terminator_def]
       (Q.INST [`i` |-> `mk_inst id MCOPY ops outs`] raw_observed_straight_edge)) >>
     strip_tac >>
     qpat_assum `b.cs_current_bb = _` SUBST1_TAC >>
     qpat_assum `LENGTH b.cs_current_insts = _` SUBST1_TAC >>
     qpat_assum `sv.vs_current_bb = _` SUBST1_TAC >>
     qpat_assum `sv.vs_inst_idx = _` SUBST1_TAC >>
     qpat_assum `su.vs_current_bb = _` SUBST1_TAC >>
     qpat_assum `su.vs_inst_idx = _` SUBST1_TAC >>
     simp[]) >>
  `cm = [] /\ u.vs_current_bb = st.cs_current_bb /\ u.vs_inst_idx = LENGTH st.cs_current_insts` by
    (drule_all (Q.INST [`opc` |-> `ADD`] emit_op_fetch_boundary) >> strip_tac >>
     drule_all (SIMP_RULE (srw_ss()) [is_terminator_def]
       (Q.INST [`i` |-> `mk_inst id ADD ops outs`] raw_observed_straight_edge)) >> simp[]) >>
  simp[] >> strip_tac >> drule_all raw_observed_encoder_silence >> simp[]
QED
