(* Concrete pointer checks for RawLog's fixed-data continuation. *)
Theory bodyFullRawLogFixedTailPath
Ancestors
  bodyFullRawLogFixedBoundary rawLogPtrInst bodyPtrDefs ptrDiscipline
  ptrSafeRun venomState venomInst venomExecSemantics words list
  rawLogCoreFrame fragGasSeqPtr wordLoadStorePtr exprPtrUnwrapCopyEdges
  instMemFrontier emitHelper compileEnv fragExecMem fragExec
  venomMemDefs valueEncodingProps rich_list finite_map arithmetic venomStepProps venomInstProofs

Theorem raw_log_fixed_log_inst_ok:
  LENGTH topics < dimword (:256) /\
  eval_operand pop s = SOME off /\
  eval_operands topics s = SOME vals /\
  (?p b sz. pop = Var p /\ FLOOKUP G p = SOME (b,sz) /\
    b <= w2n off /\ w2n off + 32 <= b + sz) /\
  EVERY (\op. op_taint tn op = {}) topics /\
  op_taint tn pop = {} /\
  (!i. w2n off <= i /\ i < w2n off + 32 ==> i NOTIN tn.t_mem) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  stor_taint_ok_at D tn s /\
  step_inst_base
    (mk_inst id LOG (Lit (n2w (LENGTH topics)) :: REVERSE topics ++ [Lit 32w;pop]) []) s = OK t ==>
  ptr_inst_ok D lo fuel ctx fn G tn
    (mk_inst id LOG (Lit (n2w (LENGTH topics)) :: REVERSE topics ++ [Lit 32w;pop]) []) s
Proof
  strip_tac >>
  `access_ok 0 G fn
    (mk_inst id LOG (Lit (n2w (LENGTH topics)) :: REVERSE topics ++ [Lit 32w;pop]) []) s` by
    (irule log_access_ok >> simp[eval_operand_def, dimword_def] >> metis_tac[]) >>
  `access_ok lo G fn
    (mk_inst id LOG (Lit (n2w (LENGTH topics)) :: REVERSE topics ++ [Lit 32w;pop]) []) s` by
    (gvs[access_ok_def] >> rpt strip_tac >> metis_tac[arithmeticTheory.ADD_EQ_0]) >>
  `taint_ok fn tn
    (mk_inst id LOG (Lit (n2w (LENGTH topics)) :: REVERSE topics ++ [Lit 32w;pop]) []) s` by
    (irule log_taint_ok >> simp[eval_operand_def, op_taint_def, dimword_def] >> metis_tac[]) >>
  gvs[ptr_inst_ok_def, stor_taint_ok_at_def, mk_inst_def, step_inst_non_invoke]
QED

Theorem raw_log_fixed_store_step:
  emit_void MSTORE [Var p;data_op] sm = ((),s1) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;Var p]) [] s1 = ((),sb) /\
  eval_operand (Var p) s = SOME w /\ eval_operand data_op s = SOME word /\
  ptr_covers G tn p s 32 /\ op_taint tn data_op = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  let i = mk_inst id MSTORE [Var p;data_op] [];
      t = mstore (w2n w) word s;
      tf = step_taint i s t tn
  in
    step_inst_base i s = OK t /\ ptr_inst_ok D lo 0 ctx func G tn i s /\
    step_prov PG G i t = G /\
    tf.t_var = tn.t_var /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    tf.t_mem = tn.t_mem DIFF {j | w2n w <= j /\ j < w2n w + 32} /\
    ptr_covers G tf p t 32 /\
    EVERY (\op. op_taint tf op = {}) ops = EVERY (\op. op_taint tn op = {}) ops /\
    (!j. w2n w <= j /\ j < w2n w+32 ==> j NOTIN tf.t_mem) /\
    allocas_from lo t /\ stor_taint_ok_at D tn s = stor_taint_ok_at D tf t
Proof
  strip_tac >> simp_tac bool_ss [LET_THM] >>
  `lookup_var p s = SOME w` by gvs[eval_operand_def] >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`,`G`,`id`] strip_assume_tac) >>
  simp[] >> conj_tac
  >- simp[mk_inst_def, step_inst_base_opcode_eqs, exec_write2_def, eval_operand_def] >>
  conj_tac >- (irule ptr_inst_ok_mstore_tainted >> simp[]) >>
  ` (step_taint (mk_inst id MSTORE [Var p;data_op] []) s
      (mstore (w2n w) word s) tn).t_imm = tn.t_imm` by
    simp[step_taint_def, mk_inst_def, imm_taint_def] >>
  gvs[ptr_covers_def, mstore_def, lookup_var_def, allocas_from_def,
       stor_taint_ok_at_def, op_taint_def] >> metis_tac[]
QED

Theorem raw_log_fixed_sequence_path:
  emit_void MSTORE [pop;data_op] sm = ((),s1) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;pop]) [] s1 = ((),sb) /\
  fn_has_code sm sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (let i = mk_inst sm.cs_next_id MSTORE [pop;data_op] [];
       j = mk_inst s1.cs_next_id LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;pop]) []
   in step_inst_base i s = OK t /\
      step_inst_base j (t with vs_inst_idx := SUC s.vs_inst_idx) = OK v /\
      inst_mem_below_frontier i s /\ inst_dload_in_section i s /\
      ptr_inst_ok D lo 0 ctx func G tn i s /\
      inst_mem_below_frontier j (t with vs_inst_idx := SUC s.vs_inst_idx) /\
      inst_dload_in_section j (t with vs_inst_idx := SUC s.vs_inst_idx) /\
      ptr_inst_ok D lo 0 ctx func
        (step_prov PG G i t) (step_taint i s t tn) j (t with vs_inst_idx := SUC s.vs_inst_idx) /\
      step_prov PG (step_prov PG G i t) j v = G1 /\
      step_taint j (t with vs_inst_idx := SUC s.vs_inst_idx) v (step_taint i s t tn) = tn1) ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (v with vs_inst_idx := LENGTH sb.cs_current_insts),G1,tn1) /\
  (v with vs_inst_idx := LENGTH sb.cs_current_insts).vs_current_bb = sb.cs_current_bb
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `step_inst_base i s = OK t` >>
  qmatch_asmsub_abbrev_tac `step_inst_base j _ = OK v` >>
  `sb.cs_current_bb = sm.cs_current_bb /\
   sb.cs_current_insts = sm.cs_current_insts ++ [i;j]` by
    (gvs[emit_void_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, fresh_id_def, emit_def, Abbr `i`, Abbr `j`]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX sb.cs_current_insts bb.bb_instructions` by
    (gvs[fn_has_code_def] >> metis_tac[]) >>
  `get_instruction bb s.vs_inst_idx = SOME i /\
   get_instruction bb (SUC s.vs_inst_idx) = SOME j` by
    (gvs[IS_PREFIX_APPEND, get_instruction_def, EL_APPEND_EQN] >> simp[]) >>
  `step_inst 0 ctx i s = OK t` by
    simp[step_inst_non_invoke, Abbr `i`, mk_inst_def] >>
  `~is_terminator i.inst_opcode` by simp[Abbr `i`, mk_inst_def, is_terminator_def] >>
  drule_all step_preserves_control_flow >> strip_tac >>
  `~t.vs_halted` by metis_tac[step_preserves_halted] >>
  `step_inst 0 ctx j (t with vs_inst_idx := SUC s.vs_inst_idx) = OK v` by
    simp[step_inst_non_invoke, Abbr `j`, mk_inst_def] >>
  `~is_terminator j.inst_opcode` by simp[Abbr `j`, mk_inst_def, is_terminator_def] >>
  `v.vs_current_bb = s.vs_current_bb` by
    (drule_at (Pat `step_inst _ _ j _ = _`) step_preserves_control_flow >> simp[]) >>
  `i.inst_opcode <> INVOKE /\ j.inst_opcode <> INVOKE` by
    simp[Abbr `i`, Abbr `j`, mk_inst_def] >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (t with vs_inst_idx := SUC s.vs_inst_idx),step_prov PG G i t,step_taint i s t tn)` by
    (drule_all straight_line_origin_ptr_edge >>
     simp[Abbr `i`, mk_inst_def]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
     (t with vs_inst_idx := SUC s.vs_inst_idx,step_prov PG G i t,step_taint i s t tn) []
     (OK (v with vs_inst_idx := SUC (SUC s.vs_inst_idx)),G1,tn1)` by
    (`j.inst_opcode <> GAS` by simp[Abbr `j`, mk_inst_def] >>
     gvs[] >> drule_at (Pat `step_inst_base j _ = _`) straight_line_origin_ptr_edge >>
     simp[] >> disch_then drule_all >> simp[]) >>
  `~v.vs_halted` by
    (drule_at (Pat `step_inst _ _ j _ = _`) step_preserves_halted >> simp[]) >>
  `LENGTH sb.cs_current_insts = SUC (SUC s.vs_inst_idx)` by simp[] >>
  simp[] >>
  irule (SRULE [] (Q.INST [`left` |-> `[]`, `right` |-> `[]`]
    (SPEC_ALL (cj 2 fragGasOriginPtrTheory.gas_origin_ptr_path_rules)))) >>
  goal_assum (drule_at Any) >>
  irule (SRULE [] (Q.INST [`left` |-> `[]`, `right` |-> `[]`]
    (SPEC_ALL (cj 2 fragGasOriginPtrTheory.gas_origin_ptr_path_rules)))) >>
  goal_assum (drule_at Any) >>
  simp[] >> irule (cj 1 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >> simp[]
QED
