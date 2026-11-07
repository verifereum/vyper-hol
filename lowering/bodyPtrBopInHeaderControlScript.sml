(* Runtime dynamic-header capacity check: source bounds make ASSERT succeed.
   All three emitted instructions are retained in the checked path. *)
Theory bodyPtrBopInHeaderControl
Ancestors bodyPtrBopInHeaderLoad bodyPtrBopInLiteralSuffix bodyPtrBopInHeaderCode
  bodyPtrBopInLoopLayout exprSendPtr exprLoweringProps
  venomExecSemantics venomInst venomState fragGasPathPtr fragGasSeqPtr
  ptrSafeRun ptrDiscipline stmtAppendStorageRunPtr words finite_map arithmetic

Theorem membership_gt_step:
  eval_operand left s = SOME a /\ eval_operand right s = SOME b ==>
  step_inst_base (mk_inst id GT [left;right] [out]) s =
    OK (update_var out (bool_to_word (w2n a > w2n b)) s)
Proof
  strip_tac >> PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[mk_inst_def, instruction_accessors,
    instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def]
QED

Theorem membership_positioned_scalar_path:
  MEM opc [EQ; OR; AND; ISZERO; GT] /\
  (LENGTH ops = 1 \/ LENGTH ops = 2) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc ops [out]) /\
  (!op. MEM op ops ==> op_taint tn op = {} /\ op_prov G op = NONE) /\
  step_inst_base (mk_inst id opc ops [out]) s = OK (update_var out w s) ==>
  ?G'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G'
      (tn with t_var := tn.t_var |+ (out,{}))
      (OK (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx)) /\
    FLOOKUP G' out = NONE /\
    (!x. x <> out ==> FLOOKUP G' x = FLOOKUP G x)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id opc ops [out]) s` by
    (irule membership_scalar_check >> simp[update_var_def]) >>
  `~is_terminator (mk_inst id opc ops [out]).inst_opcode /\
   (mk_inst id opc ops [out]).inst_opcode <> INVOKE` by
    gvs[mk_inst_def, is_terminator_def] >>
  drule_all straight_line_ptr_edge >>
  disch_then (qspec_then `PG` mp_tac) >> strip_tac >>
  `step_taint (mk_inst id opc ops [out]) s (update_var out w s) tn =
     tn with t_var := tn.t_var |+ (out,{})` by
    (irule membership_scalar_ghost_frame >> simp[]) >>
  qexists_tac `step_prov PG G (mk_inst id opc ops [out]) (update_var out w s)` >>
  conj_tac
  >- (gvs[mk_inst_def] >> drule (cj 2 gas_path_ptr_rules) >>
      disch_then (qspec_then `0` mp_tac) >> simp[] >>
      disch_then irule >> simp[update_var_def, cj 1 gas_path_ptr_rules]) >>
  conj_tac >- (irule membership_scalar_provenance >> simp[]) >>
  simp[scalar_step_old_prov]
QED

Theorem membership_capacity_gt_path:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id GT [len;Lit (n2w cap)] [out]) /\
  eval_operand len s = SOME (n2w n) /\ n <= cap /\ cap < dimword(:256) /\
  op_taint tn len = {} /\ op_prov G len = NONE ==>
  ?G'. gas_path_ptr D 0 ctx fn PG G tn s 0 G'
      (tn with t_var := tn.t_var |+ (out,{}))
      (OK (update_var out 0w s with vs_inst_idx := SUC s.vs_inst_idx)) /\
    FLOOKUP G' out = NONE /\
    (!x. x <> out ==> FLOOKUP G' x = FLOOKUP G x)
Proof
  strip_tac >>
  `n < dimword(:256)` by decide_tac >>
  `step_inst_base (mk_inst id GT [len;Lit (n2w cap)] [out]) s =
     OK (update_var out 0w s)` by
    (drule membership_gt_step >>
     disch_then (qspec_then `Lit (n2w cap)` mp_tac) >>
     simp[eval_operand_def, w2n_n2w, LESS_MOD, GREATER_DEF, bool_to_word_def]) >>
  drule_at (Pat `get_instruction _ _ = _`) membership_positioned_scalar_path >>
  disch_then (qspec_then `0w` irule) >>
  simp[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[op_taint_def, op_prov_def]
QED

Theorem membership_capacity_iszero_path:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ISZERO [Var flag] [out]) /\
  lookup_var flag s = SOME 0w /\ FLOOKUP G flag = NONE /\
  op_taint tn (Var flag) = {} ==>
  ?G'. gas_path_ptr D 0 ctx fn PG G tn s 0 G'
      (tn with t_var := tn.t_var |+ (out,{}))
      (OK (update_var out 1w s with vs_inst_idx := SUC s.vs_inst_idx)) /\
    FLOOKUP G' out = NONE /\
    (!x. x <> out ==> FLOOKUP G' x = FLOOKUP G x)
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ISZERO [Var flag] [out]) s =
     OK (update_var out 1w s)` by
    (mp_tac (Q.INST [`a` |-> `0w`, `arg` |-> `Var flag`] membership_iszero_step) >>
     simp[eval_operand_def, bool_to_word_def]) >>
  drule_at (Pat `get_instruction _ _ = _`) membership_positioned_scalar_path >>
  disch_then (qspec_then `1w` irule) >>
  fs[op_taint_def, op_prov_def]
QED

Theorem membership_capacity_path:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id GT [len;Lit (n2w cap)] [flag]) /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst id1 ISZERO [Var flag] [valid]) /\
  get_instruction bb (s.vs_inst_idx+2) = SOME (mk_inst id2 ASSERT [Var valid] []) /\
  eval_operand len s = SOME (n2w n) /\ n <= cap /\ cap < dimword(:256) /\
  op_taint tn len = {} /\ op_prov G len = NONE ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    t = (update_var valid 1w (update_var flag 0w s)
      with vs_inst_idx := s.vs_inst_idx+3) /\
    tn' = (tn with t_var := tn.t_var |+ (flag,{}) |+ (valid,{})) /\
    FLOOKUP G' valid = NONE /\
    (!x. x <> flag /\ x <> valid ==> FLOOKUP G' x = FLOOKUP G x)
Proof
  strip_tac >> drule_all membership_capacity_gt_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr _ _ _ _ _ _ _ _ _ _ tn1 (OK s1)` >>
  `~s1.vs_halted /\ lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s1.vs_inst_idx = SOME (mk_inst id1 ISZERO [Var flag] [valid]) /\
   lookup_var flag s1 = SOME 0w /\ op_taint tn1 (Var flag) = {}` by
    simp[Abbr `s1`, Abbr `tn1`, update_var_def, lookup_var_def,
         FLOOKUP_UPDATE, op_taint_def] >>
  drule_all membership_capacity_iszero_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr _ _ _ _ _ _ _ s1 _ _ tn2 (OK s2)` >>
  `~s2.vs_halted /\ lookup_block s2.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s2.vs_inst_idx = SOME (mk_inst id2 ASSERT [Var valid] []) /\
   eval_operand (Var valid) s2 = SOME 1w /\ op_taint tn2 (Var valid) = {}` by
    (simp[Abbr `s2`, Abbr `s1`, Abbr `tn2`, update_var_def, lookup_var_def,
         FLOOKUP_UPDATE, op_taint_def, eval_operand_def, ADD1]) >>
  `1w <> (0w:bytes32)` by simp[] >>
  drule_all assert_ok_path_ptr >> simp[] >>
  disch_then (qspecl_then [`PG`, `G''`, `D`] assume_tac) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G'' tn2
     (OK (s2 with vs_inst_idx := SUC s2.vs_inst_idx))` by
    (metis_tac[gas_path_ptr_then, ADD_CLAUSES]) >>
  qexists_tac `G''` >>
  fs[Abbr `s2`, Abbr `s1`, Abbr `tn2`, Abbr `tn1`, update_var_def, ADD1] >>
  metis_tac[]
QED

(* Composition boundary. Its load premise is supplied by HeaderLoad's
   source-justified memory/slot/code paths, not by erased execution. *)
Theorem membership_loaded_header_capacity_path:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ n <= cap /\ cap < dimword(:256) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb (s.vs_inst_idx+1) =
    SOME (mk_inst id GT [Var hdr;Lit (n2w cap)] [flag]) /\
  get_instruction bb (s.vs_inst_idx+2) =
    SOME (mk_inst id1 ISZERO [Var flag] [valid]) /\
  get_instruction bb (s.vs_inst_idx+3) =
    SOME (mk_inst id2 ASSERT [Var valid] []) /\
  gas_path_ptr D 0 ctx fn PG G tn s 0 G1
    (tn with t_var := tn.t_var |+ (hdr,{}))
    (OK (update_var hdr (n2w n) s with vs_inst_idx := SUC s.vs_inst_idx)) /\
  FLOOKUP G1 hdr = NONE /\
  (!x. x <> hdr ==> FLOOKUP G1 x = FLOOKUP G x) ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    t = (update_var valid 1w (update_var flag 0w (update_var hdr (n2w n) s))
      with vs_inst_idx := s.vs_inst_idx+4) /\
    tn' = (tn with t_var := tn.t_var |+ (hdr,{}) |+ (flag,{}) |+ (valid,{})) /\
    FLOOKUP G' valid = NONE /\
    (!x. x <> flag /\ x <> valid ==> FLOOKUP G' x = FLOOKUP G1 x)
Proof
  strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr _ _ _ _ _ _ _ _ _ _ tn1 (OK s1)` >>
  `~s1.vs_halted /\ lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s1.vs_inst_idx = SOME (mk_inst id GT [Var hdr;Lit (n2w cap)] [flag]) /\
   get_instruction bb (SUC s1.vs_inst_idx) = SOME (mk_inst id1 ISZERO [Var flag] [valid]) /\
   get_instruction bb (s1.vs_inst_idx+2) = SOME (mk_inst id2 ASSERT [Var valid] []) /\
   eval_operand (Var hdr) s1 = SOME (n2w n) /\
   op_taint tn1 (Var hdr) = {} /\ op_prov G1 (Var hdr) = NONE` by
    simp[Abbr `s1`, Abbr `tn1`, update_var_def, eval_operand_def,
      lookup_var_def, FLOOKUP_UPDATE, op_taint_def, op_prov_def, ADD1] >>
  drule_all membership_capacity_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t)` by
    (metis_tac[gas_path_ptr_then, ADD_CLAUSES]) >>
  qexistsl_tac [`G'`, `tn'`, `t`] >> simp[] >>
  fs[Abbr `s1`, Abbr `tn1`, update_var_def, ADD1] >> metis_tac[]
QED

Theorem membership_generated_header_capacity_path:
  (do len <- compile_ptr_load F imm loc arr;
      flag <- emit_op GT [len;Lit (n2w cap)];
      valid <- emit_op ISZERO [flag];
      emit_inst ASSERT [valid] [];
      comp_return len od) sa = (len,sb) /\ fn_has_code sa sb fn /\
  hdr = "%" ++ toString sa.cs_next_var /\
  flag = "%" ++ toString (sa.cs_next_var+1) /\
  valid = "%" ++ toString (sa.cs_next_var+2) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ n <= cap /\ cap < dimword(:256) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  gas_path_ptr D 0 ctx fn PG G tn s 0 G1
    (tn with t_var := tn.t_var |+ (hdr,{}))
    (OK (update_var hdr (n2w n) s with vs_inst_idx := SUC s.vs_inst_idx)) /\
  FLOOKUP G1 hdr = NONE /\
  (!x. x <> hdr ==> FLOOKUP G1 x = FLOOKUP G x) ==>
  len = Var hdr /\
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    t = (update_var valid 1w (update_var flag 0w (update_var hdr (n2w n) s))
      with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    tn' = (tn with t_var := tn.t_var |+ (hdr,{}) |+ (flag,{}) |+ (valid,{})) /\
    FLOOKUP G' valid = NONE /\
    (!x. x <> flag /\ x <> valid ==> FLOOKUP G' x = FLOOKUP G1 x)
Proof
  strip_tac >> drule_all membership_runtime_header_code >> strip_tac >>
  drule (SRULE [] (GEN_ALL membership_runtime_header_layout)) >> strip_tac >>
  fs[] >> simp[] >>
  drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`)
    membership_loaded_header_capacity_path >>
  simp[] >> disch_then irule >> fs[] >>
  conj_tac >- (qexistsl_tac [`cap`, `sa.cs_next_id+1`] >> simp[]) >>
  conj_tac >- (qexists_tac `sa.cs_next_id+3` >> simp[]) >>
  qexists_tac `sa.cs_next_id+2` >> simp[]
QED

Theorem membership_header_result_clean:
  t = (update_var valid 1w (update_var flag 0w (update_var hdr (n2w n) s))
    with vs_inst_idx := pc) /\
  tn' = (tn with t_var := tn.t_var |+ (hdr,{}) |+ (flag,{}) |+ (valid,{})) /\
  FLOOKUP G1 hdr = NONE /\
  (!x. x <> flag /\ x <> valid ==> FLOOKUP G' x = FLOOKUP G1 x) /\
  hdr <> flag /\ hdr <> valid /\ ~s.vs_halted ==>
  eval_operand (Var hdr) t = SOME (n2w n) /\
  op_prov G' (Var hdr) = NONE /\ op_taint tn' (Var hdr) = {} /\
  ~t.vs_halted
Proof
  strip_tac >>
  simp[eval_operand_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, op_taint_def, op_prov_def]
QED
