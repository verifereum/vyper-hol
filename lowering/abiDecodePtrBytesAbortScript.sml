Theory abiDecodePtrBytesAbort
Ancestors
  abiDecodePtrBytesMember abiDecodePtrBytesSuccess abiDecodePtrScalarAbort
  abiDecodePtrContinuation abiDecodePtrScalarFrame abiDecodePtrBytesPrefixLive
  instSeqComposePtr fragExec instIdxIndep rich_list assignTuplePtrCopyLen stateFrame
  abiDecodePtrRead abiDecodePtrMemberFrame
  bodyPtrBopScalarSeq bodyPtrBopScalarOutcome
  abiDecoderBytesBound abiDecoderContract abiDecoderGuard abiDecoderBytesRuntime
  assignTuplePtrLocalBytesCopy emitHelperProps exprLoweringProps
  abiEncoder compileEnv context bodyPtrDefs ptrDiscipline
  venomExecSemantics venomState venomInst words arithmetic list finite_map pred_set

Theorem abi_decode_bytes_member_abort_ptr:
  compile_abi_decode_to_buf (Var dst) pos MLOAD (Var src) hi
    (DecBytestring n) sa = ((),sb) /\ hi <> Lit 0w /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\ fresh_vars_wrt sa s /\
  abi_decode_ptr_window G tn s src b h /\
  lookup_var dst s = SOME d /\ ptr_covers G tn dst s cap /\
  eval_operand pos s = SOME (n2w p) /\ eval_operand hi s = SOME (n2w h) /\
  op_prov G pos = NONE /\ op_prov G hi = NONE /\
  op_taint tn pos = {} /\ op_taint tn hi = {} /\
  p < dimword(:256) /\ n+31 < dimword(:256) /\
  32+contractABI$ceil32 n <= cap /\ w2n d+cap < dimword(:256) /\
  w2n b+h < dimword(:256) /\
  (w2n b+h <= w2n d \/ w2n d+cap <= w2n b) /\
  run_inst_seq (emitted_insts sa sb) s = Abort a u ==>
  ?Gf tnf.
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s Gf tnf /\
    (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx;
              vs_halted := s.vs_halted; vs_returndata := s.vs_returndata|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule abi_decode_bytes_member_phases >> simp[] >> strip_tac >>
  drule_all abi_decode_bytes_prefix_protected >> strip_tac >>
  `inst_extends c1 sb` by metis_tac[inst_extends_trans] >>
  `emitted_insts sa sb = emitted_insts sa c1 ++ emitted_insts c1 sb` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `?B. bop_scalar_seq {x | not_fresh_at sa x}
    ({pos;hi} UNION IMAGE Lit UNIV) (emitted_insts sa c1) B /\
    ({pos;hi} UNION IMAGE Lit UNIV) SUBSET B /\ head IN B` by
    (irule abi_decode_bytes_head_scalar >> simp[] >> metis_tac[]) >>
  `!op. op IN {pos;hi} UNION IMAGE Lit UNIV ==>
    op_prov G op = NONE /\ op_taint tn op = {}` by
    (simp[IN_UNION, IN_IMAGE] >> rpt strip_tac >> gvs[op_prov_def, op_taint_def]) >>
  Cases_on `?v. run_inst_seq (emitted_insts sa c1) s = OK v`
  >- suspend "after_head" >>
  `run_inst_seq (emitted_insts sa c1) s = Abort a u` by
    (gvs[run_inst_seq_append_err]) >>
  drule_all scalar_seq_abort_replay_ptr >>
  disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
  drule_all scalar_seq_abort_runtime_frame >> strip_tac >>
  suspend "head_join"
QED

Resume abi_decode_bytes_member_abort_ptr[head_join]:
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa c1)` by
    metis_tac[EVERY_APPEND] >>
  `inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s G' tn'` by
    (qpat_assum `emitted_insts sa sb = _` (fn th => pure_rewrite_tac[th]) >>
     irule inst_seq_ptr_abort_append >> metis_tac[]) >>
  qexistsl_tac [`G'`, `tn'`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qpat_assum `(u with <|vs_vars := _; vs_halted := _; vs_returndata := _|>) = s` mp_tac >>
     qpat_assum `s.vs_inst_idx = _` mp_tac >>
     qpat_assum `~s.vs_halted` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[venom_state_component_equality]) >>
  simp[] >> rpt strip_tac >> fs[lookup_var_def, op_taint_def] >> metis_tac[]
QED

Resume abi_decode_bytes_member_abort_ptr[after_head]:
  qpat_x_assum `?v. run_inst_seq (emitted_insts sa c1) s = OK v`
    (qx_choose_then `sh` assume_tac) >>
  `h < dimword(:256)` by decide_tac >>
  `p+32 <= h` by
    (drule_all abi_decode_bytes_head_success_bound >> simp[]) >>
  drule_all abi_decode_bytes_head_sequence >> strip_tac >>
  rename1 `eval_operand head vh = SOME (n2w (p+32))` >>
  `vh = sh` by gvs[] >> qpat_x_assum `vh = sh` SUBST_ALL_TAC >>
  drule_all (abi_decode_scalar_success_frame |> Q.INST
    [`j` |-> `LENGTH c1.cs_current_insts`]) >>
  disch_then (qspecl_then [`func`, `c1`, `PG`, `D`] strip_assume_tac) >>
  qabbrev_tac `s1 = sh with vs_inst_idx := LENGTH c1.cs_current_insts` >>
  `abi_decode_ptr_window H tm s1 src b h` by
    (simp[Abbr `s1`] >> first_assum irule >> simp[]) >>
  `~s1.vs_halted /\ s1.vs_current_bb = c1.cs_current_bb /\
   s1.vs_inst_idx = LENGTH c1.cs_current_insts` by
    (simp_tac (srw_ss()) [Abbr `s1`] >>
     qpat_assum `sh = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
     fs[same_blocks_def]) >>
  `eval_operand pos s1 = SOME (n2w p) /\ op_taint tm pos = {}` by
    (fs[Abbr `s1`, SUBSET_DEF] >>
     simp[eval_operand_def, lookup_var_def] >>
     Cases_on `pos` >> gvs[eval_operand_def, lookup_var_def]) >>
  `cs_extends sa c1 /\ cs_extends c1 sb /\
   cs_extends c1 c3 /\ cs_extends c3 sb /\
   cs_extends c1 c2 /\ cs_extends c2 c3` by
    (`inst_extends c1 c3 /\ inst_extends c3 sb /\ same_blocks c1 sb /\
      same_blocks c3 sb /\ same_blocks c1 c3` by
       (fs[same_blocks_def] >> metis_tac[inst_extends_trans]) >>
     fs[cs_extends_def, same_blocks_def, inst_extends_def] >> simp[IS_PREFIX_APPEND]) >>
  `fn_has_code c1 sb func` by
    (drule_all fn_has_code_split >> simp[]) >>
  `fn_has_code c1 c3 func` by
    (drule_all fn_has_code_split >> simp[]) >>
  drule_all (abi_decode_ptr_relative_load |> Q.INST
    [`G` |-> `H`, `tn` |-> `tm`, `s` |-> `s1`, `D` |-> `D`, `PG` |-> `PG`]) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  suspend "after_load"
QED

Resume abi_decode_bytes_member_abort_ptr[after_load]:
  `inst_extends c1 c3 /\ inst_extends sa c3 /\ inst_extends c3 sb` by
    metis_tac[inst_extends_trans] >>
  `c1.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa c1 /\
   c3.cs_current_insts = c1.cs_current_insts ++ emitted_insts c1 c3` by
    fs[inst_extends_def] >>
  `emitted_insts c1 sb = emitted_insts c1 c3 ++ emitted_insts c3 sb` by
    (irule emitted_insts_append >> asm_rewrite_tac[GSYM inst_extends_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa c1) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c1 c3)` by
    metis_tac[EVERY_APPEND] >>
  `run_inst_seq (emitted_insts sa c1) s =
    OK (s1 with vs_inst_idx := s.vs_inst_idx)` by
    (qpat_assum `run_inst_seq (emitted_insts sa c1) s = OK sh` mp_tac >>
     qpat_assum `sh = s with vs_vars := _` mp_tac >>
     qunabbrev_tac `s1` >> POP_ASSUM_LIST (K ALL_TAC) >>
     rpt strip_tac >> gvs[venom_state_component_equality]) >>
  drule_all emitted_insts_join_normalized_ptr >> strip_tac >>
  suspend "count_entry"
QED

Resume abi_decode_bytes_member_abort_ptr[count_entry]:
  `fresh_vars_wrt c1 s1 /\ fresh_vars_wrt c3 t` by
    fs[Abbr `s1`, fresh_vars_wrt_def] >>
  `fn_has_code c3 sb func` by
    metis_tac[fn_has_code_split] >>
  `inst_extends c4 sb` by metis_tac[inst_extends_trans] >>
  `emitted_insts c3 sb = emitted_insts c3 c4 ++ emitted_insts c4 sb /\
   emitted_insts sa sb = emitted_insts sa c3 ++ emitted_insts c3 sb` by
    (conj_tac >> irule emitted_insts_append >>
     asm_rewrite_tac[GSYM inst_extends_def]) >>
  `?C. bop_scalar_seq {x | not_fresh_at c3 x}
    ({cnt} UNION IMAGE Lit UNIV) (emitted_insts c3 c4) C /\
    ({cnt} UNION IMAGE Lit UNIV) SUBSET C` by
    (irule abi_decode_le_guard_scalar >> simp[] >> metis_tac[]) >>
  `!op. op IN {cnt} UNION IMAGE Lit UNIV ==>
    op_prov G' op = NONE /\ op_taint tn' op = {}` by
    (simp_tac (srw_ss()) [IN_UNION, IN_SING, IN_IMAGE, IN_UNIV] >>
     gen_tac >> disch_then DISJ_CASES_TAC
     >- (qpat_x_assum `op = cnt` SUBST1_TAC >> asm_rewrite_tac[]) >>
     pop_assum (qx_choose_then `w` SUBST1_TAC) >>
     simp[op_prov_def, op_taint_def]) >>
  Cases_on `?v. run_inst_seq (emitted_insts c3 c4) t = OK v`
  >- suspend "count_success" >>
  suspend "count_abort"
QED

Resume abi_decode_bytes_member_abort_ptr[count_success]:
  qpat_x_assum `?v. run_inst_seq (emitted_insts c3 c4) t = OK v`
    (qx_choose_then `sl` assume_tac) >>
  drule_all abi_decode_scalar_success_frame >>
  disch_then (qspecl_then [`LENGTH c4.cs_current_insts`, `func`, `PG`, `D`]
    strip_assume_tac) >>
  qabbrev_tac `s4 = sl with vs_inst_idx := LENGTH c4.cs_current_insts` >>
  `c4.cs_current_insts = c3.cs_current_insts ++ emitted_insts c3 c4 /\
   sb.cs_current_insts = c4.cs_current_insts ++ emitted_insts c4 sb` by
    asm_rewrite_tac[GSYM inst_extends_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c3 c4) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c4 sb)` by
    metis_tac[EVERY_APPEND] >>
  `run_inst_seq (emitted_insts c3 c4) t = OK (s4 with vs_inst_idx := t.vs_inst_idx)` by
    (qpat_assum `sl = t with vs_vars := _` mp_tac >>
     qpat_assum `run_inst_seq (emitted_insts c3 c4) t = OK sl` mp_tac >>
     qunabbrev_tac `s4` >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[venom_state_component_equality]) >>
  suspend "payload_entry"
QED

Resume abi_decode_bytes_member_abort_ptr[payload_entry]:
  `s4.vs_inst_idx = LENGTH c4.cs_current_insts` by simp[Abbr `s4`] >>
  qpat_assum `run_inst_seq (emitted_insts sa c3) s = _`
    (mp_then (Pat `run_inst_seq xs s = _`) mp_tac emitted_insts_join_normalized_ptr) >>
  disch_then drule_all >> strip_tac >>
  suspend "payload_setup"
QED

Resume abi_decode_bytes_member_abort_ptr[payload_setup]:
  `inst_extends sa c4` by metis_tac[inst_extends_trans] >>
  `emitted_insts sa sb = emitted_insts sa c4 ++ emitted_insts c4 sb` by
    (irule emitted_insts_append >> asm_rewrite_tac[GSYM inst_extends_def]) >>
  `run_inst_seq (emitted_insts c4 sb) s4 =
    Abort a (u with vs_inst_idx := s4.vs_inst_idx)` by
    (irule abi_decode_run_continue_abort_normalized >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`s`, `emitted_insts sa c4`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `emitted_insts sa sb = emitted_insts sa c4 ++ _`
       (fn th => pure_once_rewrite_tac[GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  suspend "payload_guard"
QED

Resume abi_decode_bytes_member_abort_ptr[payload_guard]:
  `?E. bop_scalar_seq {x | not_fresh_at c4 x}
    {head;cnt;hi} (emitted_insts c4 c5) E /\ {head;cnt;hi} SUBSET E` by
    (irule (abi_decode_bytes_payload_scalar |> Q.INST
       [`A` |-> `{head;cnt;hi}`, `R` |-> `{x | not_fresh_at c4 x}`]) >>
     simp_tac (srw_ss()) [IN_GSPEC] >> metis_tac[]) >>
  suspend "payload_clean"
QED

Resume abi_decode_bytes_member_abort_ptr[payload_clean]:
  `!x. head = Var x ==> not_fresh_at c1 x` by
    (gen_tac >> disch_tac >>
     `abiDecoderReentry$abi_decoder_operand_live c1.cs_next_var head` by
       (irule abiDecoderReentryTheory.abi_decoder_operand_live_fresh >>
        qexistsl_tac [`sh`, `n2w (p+32)`] >> asm_rewrite_tac[]) >>
     pop_assum mp_tac >>
     asm_simp_tac (srw_ss()) [abiDecoderReentryTheory.abi_decoder_operand_live_def,
       abiDecoderReentryTheory.abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `!x. hi = Var x ==> not_fresh_at c1 x` by
    (gen_tac >> disch_tac >>
     `abiDecoderReentry$abi_decoder_operand_live c1.cs_next_var hi` by
       (irule abiDecoderReentryTheory.abi_decoder_operand_live_fresh >>
        qexistsl_tac [`sh`, `n2w h`] >> conj_tac
        >- (qpat_assum `!op w. eval_operand op s = SOME w ==> _` irule >>
            first_assum MATCH_ACCEPT_TAC) >>
        first_assum MATCH_ACCEPT_TAC) >>
     pop_assum mp_tac >>
     asm_simp_tac (srw_ss()) [abiDecoderReentryTheory.abi_decoder_operand_live_def,
       abiDecoderReentryTheory.abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `t.vs_labels = s1.vs_labels` by
    (qpat_assum `state_frame t = _` mp_tac >>
     simp_tac (srw_ss()) [state_frame_def, venom_state_component_equality]) >>
  `!op. (!x. op = Var x ==> not_fresh_at c1 x) ==>
    eval_operand op t = eval_operand op s1 /\
    op_prov G' op = op_prov H op /\ op_taint tn' op = op_taint tm op` by
    (gen_tac >> disch_tac >> irule abi_decode_scalar_protected_operand >>
     simp[] >> qexists_tac `{x | not_fresh_at c1 x}` >> simp[]) >>
  suspend "payload_transport"
QED

Resume abi_decode_bytes_member_abort_ptr[payload_transport]:
  `op_prov G' head = NONE /\ op_taint tn' head = {} /\
   op_prov G' hi = NONE /\ op_taint tn' hi = {}` by
    (qpat_assum `!op. (!x. op = Var x ==> not_fresh_at c1 x) ==> _`
       (qspec_then `head` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     qpat_assum `!op. (!x. op = Var x ==> not_fresh_at c1 x) ==> _`
       (qspec_then `hi` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     rpt conj_tac >> metis_tac[SUBSET_DEF, IN_UNION, IN_INSERT]) >>
  `!op. op IN {head;cnt;hi} ==> op_prov G' op = NONE /\ op_taint tn' op = {}` by
    (simp_tac (srw_ss()) [IN_INSERT, NOT_IN_EMPTY] >> metis_tac[]) >>
  `!op. op IN {head;cnt;hi} ==> !x. op = Var x ==> not_fresh_at c3 x` by
    (qpat_assum `!x. head = Var x ==> _` mp_tac >>
     qpat_assum `!x. hi = Var x ==> _` mp_tac >>
     qpat_assum `!x. not_fresh_at c1 x ==> not_fresh_at c3 x` mp_tac >>
     qpat_assum `cnt = Var out` mp_tac >>
     qpat_assum `not_fresh_at c3 out` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac (srw_ss()) [IN_INSERT, NOT_IN_EMPTY] >>
     rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `!op. op IN {head;cnt;hi} ==> op_prov H' op = NONE /\ op_taint tm' op = {}` by
    (ho_match_mp_tac (abi_decode_scalar_clean_set_transport |> Q.INST
       [`G` |-> `G'`, `tn` |-> `tn'`, `R` |-> `{x | not_fresh_at c3 x}`]) >>
     conj_tac >- first_assum MATCH_ACCEPT_TAC >>
     conj_tac >-
       (qpat_assum `!op. op IN {head;cnt;hi} ==> !x. _` mp_tac >>
        simp_tac (srw_ss()) [IN_GSPEC]) >>
     gen_tac >> disch_tac >>
     qpat_assum `!op. (!x. op = Var x ==> x IN {x | not_fresh_at c3 x}) ==> _`
       (qspec_then `op` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> simp[]) >>
  suspend "payload_split"
QED

Resume abi_decode_bytes_member_abort_ptr[payload_split]:
  `inst_extends c5 sb /\ inst_extends c4 sb` by metis_tac[inst_extends_trans] >>
  `emitted_insts c4 sb = emitted_insts c4 c5 ++ emitted_insts c5 sb` by
    (irule emitted_insts_append >> asm_rewrite_tac[GSYM inst_extends_def]) >>
  Cases_on `?v. run_inst_seq (emitted_insts c4 c5) s4 = OK v`
  >- suspend "payload_success" >>
  `run_inst_seq (emitted_insts c4 c5) s4 =
    Abort a (u with vs_inst_idx := s4.vs_inst_idx)` by
    (qpat_x_assum `run_inst_seq (emitted_insts c4 sb) s4 = _` mp_tac >>
     qpat_assum `emitted_insts c4 sb = _` (fn th => pure_once_rewrite_tac[th]) >>
     `!v. run_inst_seq (emitted_insts c4 c5) s4 <> OK v` by
       (qpat_x_assum `~(?v. run_inst_seq (emitted_insts c4 c5) s4 = OK v)` mp_tac >>
        pure_rewrite_tac[NOT_EXISTS_THM] >> simp_tac bool_ss []) >>
     drule run_inst_seq_append_err >>
     disch_then (qspec_then `emitted_insts c5 sb` (fn th => pure_rewrite_tac[th])) >>
     simp_tac bool_ss []) >>
  drule_all scalar_seq_abort_replay_ptr >>
  disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
  drule_all scalar_seq_abort_runtime_frame >> strip_tac >>
  suspend "payload_abort_join"
QED

Resume abi_decode_bytes_member_abort_ptr[payload_success]:
  `eval_operand head s1 = SOME (n2w (p+32)) /\
   eval_operand hi s1 = SOME (n2w h)` by
    (`eval_operand hi sh = SOME (n2w h)` by
       (qpat_assum `!op w. eval_operand op s = SOME w ==> _` irule >>
        first_assum MATCH_ACCEPT_TAC) >>
     simp_tac (srw_ss()) [Abbr `s1`, eval_operand_def, lookup_var_def] >>
     qpat_assum `eval_operand head sh = _` mp_tac >>
     qpat_assum `eval_operand hi sh = _` mp_tac >>
     simp_tac (srw_ss()) [eval_operand_def, lookup_var_def]) >>
  `eval_operand head t = SOME (n2w (p+32)) /\
   eval_operand hi t = SOME (n2w h)` by
    (qpat_assum `!op. (!x. op = Var x ==> not_fresh_at c1 x) ==> _`
       (qspec_then `head` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     qpat_assum `!op. (!x. op = Var x ==> not_fresh_at c1 x) ==> _`
       (qspec_then `hi` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     conj_tac >> metis_tac[]) >>
  `eval_operand cnt t = SOME (mload (w2n b+p) s)` by
    (`w2n (b+n2w p) = w2n b+p` by
       (irule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> decide_tac) >>
     fs[eval_operand_def, Abbr `s1`, mload_def]) >>
  `w2n (mload (w2n b+p) s) <= n` by
    (`eval_operand (Lit (n2w n)) t = SOME (n2w n)` by simp[eval_operand_def] >>
     drule_all abi_decode_le_guard_success_bound >> simp[w2n_n2w]) >>
  `eval_operand (Lit (n2w n)) t = SOME (n2w n)` by simp[eval_operand_def] >>
  `w2n (mload (w2n b+p) s) <= w2n (n2w n:bytes32)` by fs[w2n_n2w] >>
  drule_all abi_decode_le_guard_sequence >> strip_tac >>
  suspend "payload_success_values"
QED

Resume abi_decode_bytes_member_abort_ptr[payload_success_values]:
  rename1 `fresh_vars_wrt c4 v4` >>
  `v4 = sl` by
    (qpat_assum `run_inst_seq (emitted_insts c3 c4) t = OK v4` mp_tac >>
     qpat_assum `run_inst_seq (emitted_insts c3 c4) t = OK sl` mp_tac >>
     simp[]) >> qpat_x_assum `v4 = sl` SUBST_ALL_TAC >>
  `fresh_vars_wrt c4 s4` by
    (qpat_assum `fresh_vars_wrt c4 sl` mp_tac >>
     simp_tac (srw_ss()) [Abbr `s4`, fresh_vars_wrt_def]) >>
  `!op w. eval_operand op t = SOME w ==> eval_operand op s4 = SOME w` by
    (rpt gen_tac >> disch_tac >>
     `eval_operand op sl = SOME w` by
       (qpat_assum `!op w. eval_operand op t = SOME w ==> _` irule >>
        first_assum ACCEPT_TAC) >>
     simp_tac (srw_ss()) [Abbr `s4`, eval_operand_def, lookup_var_def] >>
     pop_assum mp_tac >> simp_tac (srw_ss()) [eval_operand_def, lookup_var_def]) >>
  `eval_operand head s4 = SOME (n2w (p+32)) /\
   eval_operand cnt s4 = SOME (mload (w2n b+p) s) /\
   eval_operand hi s4 = SOME (n2w h)` by metis_tac[] >>
  qpat_x_assum `?v. run_inst_seq (emitted_insts c4 c5) s4 = OK v`
    (qx_choose_then `sp` assume_tac) >>
  `p+32+w2n (mload (w2n b+p) s) <= h` by
    (drule_all abi_decode_bytes_payload_success_bound >> simp[w2n_n2w]) >>
  suspend "tail_success"
QED

Resume abi_decode_bytes_member_abort_ptr[tail_success]:
  `eval_operand cnt s4 = SOME (n2w (w2n (mload (w2n b+p) s)))` by
    simp[n2w_w2n] >>
  drule abi_decode_bytes_payload_guard_sequence >>
  disch_then (qspecl_then [`s4`, `p+32`, `w2n (mload (w2n b+p) s)`] mp_tac) >>
  (impl_tac >-
    (conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (disj2_tac >> qexists_tac `h` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC)) >> strip_tac >>
  rename1 `fresh_vars_wrt c5 v5` >>
  `v5 = sp` by gvs[] >> qpat_x_assum `v5 = sp` SUBST_ALL_TAC >>
  suspend "tail_operands"
QED

Resume abi_decode_bytes_member_abort_ptr[tail_operands]:
  cheat
QED

Resume abi_decode_bytes_member_abort_ptr[payload_abort_join]:
  `c5.cs_current_insts = c4.cs_current_insts ++ emitted_insts c4 c5 /\
   sb.cs_current_insts = c5.cs_current_insts ++ emitted_insts c5 sb` by
    asm_rewrite_tac[GSYM inst_extends_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c4 c5)` by
    metis_tac[EVERY_APPEND] >>
  drule_all abi_decode_compile_abort_suffix_ptr >> strip_tac >>
  `inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s G'' tn''` by
    (irule (cj 2 abi_decode_compile_continue_abort_ptr) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`H'`, `a`, `c4`, `s4`, `tm'`,
       `u with vs_inst_idx := s4.vs_inst_idx`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "payload_abort_frame"
QED

Resume abi_decode_bytes_member_abort_ptr[payload_abort_frame]:
  qexistsl_tac [`G''`, `tn''`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qpat_assum `state_frame t = _` mp_tac >>
     qpat_assum `(u with <|vs_vars := _; vs_halted := _; vs_returndata := _; vs_inst_idx := _|>) = s4` mp_tac >>
     qpat_assum `sh = s with vs_vars := _` mp_tac >>
     qpat_assum `sl = t with vs_vars := _` mp_tac >>
     qpat_assum `Abbrev (s1 = _)` mp_tac >>
     qpat_assum `Abbrev (s4 = _)` mp_tac >>
     qpat_assum `s.vs_inst_idx = _` mp_tac >>
     qpat_assum `~s.vs_halted` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[markerTheory.Abbrev_def, state_frame_def, venom_state_component_equality]) >>
  reverse conj_tac >- metis_tac[] >>
  gen_tac >> strip_tac >>
  `not_fresh_at c1 x /\ not_fresh_at c3 x /\ not_fresh_at c4 x` by metis_tac[] >>
  fs[IN_GSPEC_IFF, lookup_var_def, op_taint_def] >> metis_tac[]
QED

Resume abi_decode_bytes_member_abort_ptr[count_abort]:
  `c3.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa c3 /\
   sb.cs_current_insts = c3.cs_current_insts ++ emitted_insts c3 sb` by
    fs[inst_extends_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c3 sb)` by
    metis_tac[EVERY_APPEND] >>
  `run_inst_seq (emitted_insts c3 sb) t =
    Abort a (u with vs_inst_idx := t.vs_inst_idx)` by
    (irule abi_decode_run_continue_abort_normalized >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`s`, `emitted_insts sa c3`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `emitted_insts sa sb = emitted_insts sa c3 ++ _`
       (fn th => pure_once_rewrite_tac[GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  `run_inst_seq (emitted_insts c3 c4) t =
    Abort a (u with vs_inst_idx := t.vs_inst_idx)` by
    (qpat_x_assum `run_inst_seq (emitted_insts c3 sb) t = _` mp_tac >>
     qpat_assum `emitted_insts c3 sb = _` (fn th => pure_once_rewrite_tac[th]) >>
     `!v. run_inst_seq (emitted_insts c3 c4) t <> OK v` by
       (qpat_x_assum `~(?v. run_inst_seq (emitted_insts c3 c4) t = OK v)` mp_tac >>
        pure_rewrite_tac[NOT_EXISTS_THM] >> simp_tac bool_ss []) >>
     drule run_inst_seq_append_err >>
     disch_then (qspec_then `emitted_insts c4 sb` (fn th => pure_rewrite_tac[th])) >>
     simp_tac bool_ss []) >>
  drule_all scalar_seq_abort_replay_ptr >>
  disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
  drule_all scalar_seq_abort_runtime_frame >> strip_tac >>
  suspend "count_abort_join"
QED

Resume abi_decode_bytes_member_abort_ptr[count_abort_join]:
  `c4.cs_current_insts = c3.cs_current_insts ++ emitted_insts c3 c4 /\
   sb.cs_current_insts = c4.cs_current_insts ++ emitted_insts c4 sb` by
    asm_rewrite_tac[GSYM inst_extends_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c3 c4)` by
    metis_tac[EVERY_APPEND] >>
  drule_all abi_decode_compile_abort_suffix_ptr >> strip_tac >>
  `inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s G'' tn''` by
    (irule (cj 2 abi_decode_compile_continue_abort_ptr) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`G'`, `a`, `c3`, `t`, `tn'`,
       `u with vs_inst_idx := t.vs_inst_idx`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "count_abort_frame"
QED

Resume abi_decode_bytes_member_abort_ptr[count_abort_frame]:
  qexistsl_tac [`G''`, `tn''`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qpat_assum `state_frame t = _` mp_tac >>
     qpat_assum `(u with <|vs_vars := _; vs_halted := _; vs_returndata := _; vs_inst_idx := _|>) = t` mp_tac >>
     qpat_assum `sh = s with vs_vars := _` mp_tac >>
     qpat_assum `Abbrev (s1 = _)` mp_tac >>
     qpat_assum `s.vs_inst_idx = _` mp_tac >>
     qpat_assum `~s.vs_halted` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[markerTheory.Abbrev_def, state_frame_def, venom_state_component_equality]) >>
  reverse conj_tac >- metis_tac[] >>
  gen_tac >> strip_tac >>
  `not_fresh_at c1 x /\ not_fresh_at c3 x` by metis_tac[] >>
  fs[IN_GSPEC_IFF, lookup_var_def, op_taint_def] >> metis_tac[]
QED

Finalise abi_decode_bytes_member_abort_ptr
