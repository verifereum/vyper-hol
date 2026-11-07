Theory bodyPtrBopInLiteralTyped
Ancestors exprSimBopInLiteralWord bodyPtrBopInLiteralSource bodyPtrBopInLiteralSuffix
  exprSimPtrProps wordArgsPtr exprSimWordArgs typedWordArgsPostPtr
  gasSummaryComposePtr varsExt freshWrites instIdxIndep list
  bodyPtrBopInScalarTransport exprSimBopInLiteralWord
  finite_map venomState fragExec venomInst venomExecSemantics bodyPtrBopInLiteralRun

(* Encoding is used only at this boundary: the path below states source
   membership rather than membership of the encoded machine words. *)
Theorem literal_typed_scalar_path:
  (bop = In \/ bop = NotIn) /\
  (if bop = In then compile_list_membership_in needle xs
   else compile_list_membership_notin needle xs) sm = (dst,sb) /\
  is_word_type et /\ evaluate_type (get_tenv cx) et = SOME tv /\
  value_has_type tv v /\ EVERY (value_has_type tv) vs /\
  LIST_REL (\x v. eval_operand x s = SOME (typed_val_to_w256 tv v)) xs vs /\
  eval_operand needle s = SOME (typed_val_to_w256 tv v) /\
  fresh_vars_wrt sm s /\
  op_prov G needle = NONE /\ op_taint tn needle = {} /\
  EVERY (\x. op_prov G x = NONE /\ op_taint tn x = {}) xs /\
  ~ctx_has_dalloca ctx /\ fn_has_code sm sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u t G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    t = (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    (u with vs_vars := s.vs_vars) = s /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand dst t = SOME (bool_to_word (if bop = In then MEM v vs else ~MEM v vs)) /\
    fresh_vars_wrt sb t /\ op_prov G' dst = NONE /\ op_taint tn' dst = {} /\
    (tn' with t_var := tn.t_var) = tn /\
    (!p. not_fresh_at sm p ==> FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p)) /\
    (!x v. eval_operand x s = SOME v ==> eval_operand x t = SOME v)
Proof
  strip_tac >>
  `LIST_REL (\x w. eval_operand x s = SOME w) xs (MAP (typed_val_to_w256 tv) vs)` by
    simp[LIST_REL_MAP2] >>
  drule_all literal_typed_encoding_MEM >> disch_tac >>
  Cases_on `bop = In` >> gvs[]
  >- (drule_all literal_in_path >>
      disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
      gvs[eval_op_inst_idx] >> qexistsl_tac [`u`,`G'`,`tn'`] >> simp[]) >>
  drule_all literal_notin_path >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  gvs[eval_op_inst_idx] >> qexistsl_tac [`u`,`G'`,`tn'`] >> simp[]
QED

Theorem scalar_drop_fresh_path:
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  EVERY (\i. MEM i.inst_opcode [EQ; OR; AND; ISZERO] /\
    (LENGTH i.inst_operands = 1 \/ LENGTH i.inst_operands = 2) /\
    LENGTH i.inst_outputs = 1) (emitted_insts sa sb) /\
  writes_fresh sa (emitted_insts sa sb) /\
  ~ctx_has_dalloca ctx /\ fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) (drop_fresh sa s) = OK u /\
  eval_operand dst u = SOME w /\
  (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
    (drop_fresh sa s with vs_inst_idx := k) G' tn') ==>
  ?t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand dst t = SOME w /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s)
Proof
  strip_tac >>
  `EVERY (\i. MEM i.inst_opcode [EQ; OR; AND; ISZERO])
    (emitted_insts sa sb)` by (gvs[EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (irule membership_scalar_nonterminators >> simp[]) >>
  `!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
    (s with vs_inst_idx := k) G' tn'` by
    (gen_tac >> irule scalar_sequence_check_vars_ext >>
     conj_tac >- simp[] >> conj_tac >- simp[] >>
     qexists_tac `drop_fresh sa s with vs_inst_idx := k` >>
     conj_tac >- simp[run_inst_seq_inst_idx, exec_result_map_def] >>
     conj_tac >- simp[vars_ext_def, drop_fresh_def, DRESTRICT_SUBMAP,
                       venom_state_component_equality] >> simp[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
    ~is_ext_call_op i.inst_opcode) (emitted_insts sa sb)` by
    (gvs[EVERY_MEM] >> rpt strip_tac >> res_tac >>
     gvs[is_terminator_def, is_ext_call_op_def]) >>
  `?u1. run_inst_seq (emitted_insts sa sb) s = OK u1 /\ vars_ext u u1` by
    (`vars_ext (drop_fresh sa s) s` by simp[vars_ext_drop_fresh] >>
     drule_all run_inst_seq_vars_ext >>
     simp[vars_ext_result_def]) >>
  drule_all membership_scalar_run_path >> strip_tac >>
  drule_all run_inst_seq_writes_fresh >> strip_tac >>
  qexists_tac `u1 with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[eval_op_inst_idx, lookup_var_def] >>
  conj_tac >- gvs[venom_state_component_equality] >>
  gvs[vars_ext_def] >>
  drule eval_operand_vars_ext >>
  disch_then (qspec_then `dst` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem literal_typed_clean_run:
  (bop = In \/ bop = NotIn) /\
  (if bop = In then compile_list_membership_in needle xs
   else compile_list_membership_notin needle xs) sm = (dst,sb) /\
  is_word_type et /\ evaluate_type (get_tenv cx) et = SOME tv /\
  value_has_type tv v /\ EVERY (value_has_type tv) vs /\
  LIST_REL (\x v. eval_operand x s = SOME (typed_val_to_w256 tv v)) xs vs /\
  eval_operand needle s = SOME (typed_val_to_w256 tv v) /\
  EVERY (\x. !p. x = Var p ==> not_fresh_at sm p) (needle::xs) /\
  op_prov G needle = NONE /\ op_taint tn needle = {} /\
  EVERY (\x. op_prov G x = NONE /\ op_taint tn x = {}) xs /\
  ~ctx_has_dalloca ctx ==>
  ?u G' tn'.
    run_inst_seq (emitted_insts sm sb) (drop_fresh sm s) = OK u /\
    eval_operand dst u = SOME (bool_to_word (if bop = In then MEM v vs else ~MEM v vs)) /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sm sb)
      (drop_fresh sm s with vs_inst_idx := k) G' tn') /\
    op_prov G' dst = NONE /\ op_taint tn' dst = {} /\
    (tn' with t_var := tn.t_var) = tn /\
    (!p. not_fresh_at sm p ==> FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `fresh_vars_wrt sm (drop_fresh sm s)` by simp[fresh_vars_wrt_drop_fresh] >>
  `LIST_REL (\x v. eval_operand x (drop_fresh sm s) = SOME (typed_val_to_w256 tv v)) xs vs` by
    (irule (iffRL literal_typed_operands_drop_fresh) >> gvs[]) >>
  `eval_operand needle (drop_fresh sm s) = SOME (typed_val_to_w256 tv v)` by
    (gvs[] >> drule eval_operand_drop_fresh >> simp[]) >>
  `LIST_REL (\x w. eval_operand x (drop_fresh sm s) = SOME w)
    xs (MAP (typed_val_to_w256 tv) vs)` by simp[LIST_REL_MAP2] >>
  drule_all literal_typed_encoding_MEM >> disch_tac >>
  Cases_on `bop = In` >> gvs[]
  >- (drule_all bodyPtrBopInLiteralRunTheory.literal_in_run >> strip_tac >>
      drule_all literal_in_uniform >>
      disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
      qexistsl_tac [`tt`,`G'`,`tn'`] >> simp[]) >>
  drule_all bodyPtrBopInLiteralRunTheory.literal_notin_run >> strip_tac >>
  drule_all literal_notin_uniform >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`tt`,`G'`,`tn'`] >> simp[]
QED

Theorem literal_typed_scalar_path_arbitrary:
  (bop = In \/ bop = NotIn) /\
  (if bop = In then compile_list_membership_in needle xs
   else compile_list_membership_notin needle xs) sm = (dst,sb) /\
  is_word_type et /\ evaluate_type (get_tenv cx) et = SOME tv /\
  value_has_type tv v /\ EVERY (value_has_type tv) vs /\
  LIST_REL (\x v. eval_operand x s = SOME (typed_val_to_w256 tv v)) xs vs /\
  eval_operand needle s = SOME (typed_val_to_w256 tv v) /\
  EVERY (\x. !p. x = Var p ==> not_fresh_at sm p) (needle::xs) /\
  op_prov G needle = NONE /\ op_taint tn needle = {} /\
  EVERY (\x. op_prov G x = NONE /\ op_taint tn x = {}) xs /\
  ~ctx_has_dalloca ctx /\ fn_has_code sm sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u t G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    t = (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    (u with vs_vars := s.vs_vars) = s /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand dst t = SOME (bool_to_word (if bop = In then MEM v vs else ~MEM v vs)) /\
    op_prov G' dst = NONE /\ op_taint tn' dst = {} /\
    (tn' with t_var := tn.t_var) = tn /\
    (!p. not_fresh_at sm p ==> FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p)) /\
    (!p. not_fresh_at sm p ==> lookup_var p t = lookup_var p s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all literal_typed_clean_run >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  `sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
    same_blocks sm sb /\
    EVERY (\i. MEM i.inst_opcode [EQ; OR; AND; ISZERO] /\
      (LENGTH i.inst_operands = 1 \/ LENGTH i.inst_operands = 2) /\
      LENGTH i.inst_outputs = 1) (emitted_insts sm sb)` by
    (Cases_on `bop = In` >> gvs[]
     >- (drule literal_in_code_shape >> simp[]) >>
     drule literal_notin_code_shape >> simp[]) >>
  `writes_fresh sm (emitted_insts sm sb)` by
    (mp_tac (Q.SPECL [`xs`,`needle`] literal_membership_straight) >>
     simp[straight_fresh_def] >> strip_tac >>
     Cases_on `bop = In` >> gvs[] >> metis_tac[]) >>
  drule_all scalar_drop_fresh_path >> strip_tac >>
  qexistsl_tac [`t with vs_inst_idx := s.vs_inst_idx`,`t`,`G'`,`tn'`] >>
  simp[] >> gvs[venom_state_component_equality]
QED
