Theory bodyPtrSignedConvertBool
Ancestors
  bodyPtrSignedConvertIszero exprLowering exprLoweringProps emitHelperProps
  fragGasSeqPtr compileEnv loweringStateRelDefs ASCIInumbers rich_list ptrDiscipline finite_map venomState venomInst

Theorem convert_bool_code:
  compile_type_convert x ConvToBool sa = (out,sb) ==>
  ?a b.
    out = Var b /\
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id ISZERO [x] [a];
       mk_inst (sa.cs_next_id+1) ISZERO [Var a] [b]] /\
    a <> b /\
    (!p. not_fresh_at sa p ==> p <> a /\ p <> b) /\
    sb.cs_next_var = sa.cs_next_var+2 /\
    sb.cs_current_bb = sa.cs_current_bb /\
    LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts+2
Proof
  simp[compile_type_convert_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> gvs[] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  imp_res_tac emit_op_extends >>
  gvs[same_blocks_def, not_fresh_at_def, toString_inj] >>
  qexists_tac `STRING #"%" (toString sa.cs_next_var)` >> simp[toString_inj]
QED

Theorem iszero_pair_certificate:
  op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq [mk_inst id ISZERO [x] [a];
                mk_inst (id+1) ISZERO [Var a] [b]] s = OK t ==>
  ?H th.
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id ISZERO [x] [a];
       mk_inst (id+1) ISZERO [Var a] [b]] s H th /\
    H = DRESTRICT (DRESTRICT G (COMPL {a})) (COMPL {b}) /\
    th = tn with t_var := tn.t_var |+ (a,{}) |+ (b,{}) /\
    op_prov H (Var b) = NONE /\ op_taint th (Var b) = {}
Proof
  strip_tac >>
  gvs[run_inst_seq_def, AllCaseEqs()] >>
  rename1 `step_inst_base (mk_inst id ISZERO [x] [a]) s = OK u` >>
  qpat_assum `step_inst_base (mk_inst id _ _ _) _ = _`
    (mp_then Any strip_assume_tac iszero_run_shape) >> gvs[] >>
  drule iszero_run_shape >> strip_tac >> gvs[] >>
  simp[op_prov_def, FLOOKUP_DRESTRICT, op_taint_def, FLOOKUP_UPDATE] >>
  simp[inst_seq_ptr_def] >>
  conj_tac
  >- (irule iszero_ptr_inst_ok >> simp[allocas_from_def] >>
      goal_assum (drule_at Any)) >>
  simp[iszero_ghost_update] >>
  `step_inst_base (mk_inst (id+1) ISZERO [Var a] [b])
    (update_var a (bool_to_word (w = 0w)) s with vs_inst_idx := SUC s.vs_inst_idx) =
    OK (update_var b (bool_to_word (w' = 0w))
      (update_var a (bool_to_word (w = 0w)) s with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule step_ISZERO >> simp[eval_operand_def, lookup_var_def, update_var_def] >>
     gvs[eval_operand_def, lookup_var_def, update_var_def]) >>
  conj_tac
  >- (irule iszero_ptr_inst_ok >> simp[allocas_from_def, op_taint_def, FLOOKUP_UPDATE] >>
      goal_assum (drule_at Any)) >>
  simp[] >>
  drule iszero_ghost_update >> strip_tac >> simp[] >>
  qpat_assum `step_inst_base (mk_inst id _ _ _) _ = _`
    (mp_then Any strip_assume_tac iszero_ghost_update) >>
  simp[DRESTRICT_DRESTRICT]
QED

Theorem convert_bool_fixed_certificate:
  compile_type_convert x ConvToBool sa = (out,sb) /\
  op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H th. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th /\
    op_prov H out = NONE /\ op_taint th out = {} /\
    (!p. not_fresh_at sa p ==>
      FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >> drule convert_bool_code >> strip_tac >> gvs[] >>
  drule_all iszero_pair_certificate >>
  disch_then (qspecl_then [`fn`,`PG`,`G`,`D`] strip_assume_tac) >>
  qexistsl_tac [`H`,`th`] >> simp[] >>
  gvs[op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> simp[] >> metis_tac[]
QED

Theorem iszero_pair_runtime_frame:
  run_inst_seq [mk_inst id ISZERO [x] [a];
                mk_inst (id+1) ISZERO [Var a] [b]] s = OK t ==>
  (t with vs_vars := s.vs_vars) = s /\
  (!p. p <> a /\ p <> b ==> lookup_var p t = lookup_var p s)
Proof
  strip_tac >> gvs[run_inst_seq_def, AllCaseEqs()] >>
  qpat_assum `step_inst_base (mk_inst id _ _ _) _ = _`
    (mp_then Any strip_assume_tac iszero_run_shape) >> gvs[] >>
  drule iszero_run_shape >> strip_tac >> gvs[] >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem convert_bool_runtime_frame:
  compile_type_convert x ConvToBool sa = (out,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  (t with vs_vars := s.vs_vars) = s /\
  (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s)
Proof
  strip_tac >> drule convert_bool_code >> strip_tac >> gvs[] >>
  drule iszero_pair_runtime_frame >> strip_tac >> simp[] >>
  metis_tac[]
QED

Theorem convert_bool_counted_certificate:
  compile_type_convert x ConvToBool sa = (out,sb) /\
  op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?H th.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
    op_prov H out = NONE /\ op_taint th out = {} /\
    (!p. not_fresh_at sa p ==>
      FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >> drule_all convert_bool_fixed_certificate >>
  disch_then (qspecl_then [`fn`,`PG`,`G`,`D`] strip_assume_tac) >>
  qexistsl_tac [`H`,`th`] >> simp[] >>
  drule convert_bool_code >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb)` by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >>
  simp[mk_inst_def]
QED
