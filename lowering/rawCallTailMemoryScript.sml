(* Counted memory execution of the allocation, call and finish policies. *)
Theory rawCallTailMemory
Ancestors
  rawCallAllocatedOracleMemory rawCallResultPathMemory rawCallFinishPathMemory
  rawCallFinishPostMemory exprSimRawCall exprSimRawCallCalldata exprSafeOperand localPtrsProps
  exprSimProps exprLoweringProps exprSimMemDefs fragGasPathMem builtinSystem
  emitHelperProps fragExec compileEnv loweringPosts venomState venomExecSemantics
  vyperTypeSystem valueEncoding words finite_map list
Libs
  monadsyntax

Theorem raw_call_outbuf_tail_mem:
  compile_raw_call_outbuf cap sa = ((ov,op),sm) /\
  compile_raw_call_finish to_op dp dl gas_op val_op
    (if stat then StaticCall else RegularCall) cap flags.rcf_revert_on_failure ov op sm = (result,sb) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ci_mono initial sa /\ wb_frame cenv initial_es initial s0 s /\
  stmt_state_rel ctx func cenv cx initial_es s0 /\ local_ptrs_reserved cenv initial /\
  MAP FDOM initial_es.scopes = MAP FDOM es.scopes /\
  eval_operand gas_op s = SOME gas /\ eval_operand to_op s = SOME aw /\
  eval_operand dp s = SOME ao /\ eval_operand dl s = SOME az /\ eval_operand val_op s = SOME val_word /\
  safe_operand sa to_op /\ safe_operand sa dp /\ safe_operand sa dl /\
  safe_operand sa gas_op /\ safe_operand sa val_op /\
  w2w aw = target /\
  w2n (if stat then 0w else val_word) = (case value_opt of NONE => 0 | SOME n => n) /\
  stat = IS_NONE value_opt /\
  take_call_outcome target (read_memory (w2n ao) (w2n az) s) value_opt es = (INL (rq,outcome),es1) /\
  MAP FDOM es.scopes = MAP FDOM (SND (adopt_call_outcome rq outcome es1)).scopes /\
  cap < dimword (:256) /\ LENGTH outcome.co_returnData < dimword (:256) /\
  (0 < cap ==> 64 + ((cap + 31) DIV 32) * 32 < dimword (:256)) /\
  flags.rcf_max_outsize = cap /\ expr_type e = raw_call_return_type flags /\
  lowered_value_type cenv e = expr_type e /\
  (0 < cap ==> evaluate_type (get_tenv cx) (expr_type e) =
    SOME (if flags.rcf_revert_on_failure then BaseTV (BytesT (Dynamic cap))
      else TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic cap))])) /\
  (w2n az = 0 \/ w2n ao + w2n az <= s.vs_alloca_next) /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r. gas_path_mem ctx func s 0 r /\
    ((?u. r = OK u /\ alloca_history func u /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (flags.rcf_revert_on_failure ==> outcome.co_success) /\
      vv_post ctx func cenv cx e initial_es initial sb s0
        (SND (adopt_call_outcome rq outcome es1))
        (Value (if flags.rcf_revert_on_failure then
          if cap = 0 then NoneV else BytesV (TAKE cap outcome.co_returnData)
         else if cap = 0 then BoolV outcome.co_success
         else ArrayV (TupleV [BoolV outcome.co_success;BytesV (TAKE cap outcome.co_returnData)])))
        (if cap = 0 then StackValue ann result
         else LocatedValue (expr_type e) (mk_ptr result LocMemory)) u /\
      vv_store_bound cx (expr_type e) (lowered_value_type cenv e)
        (SND (adopt_call_outcome rq outcome es1))
        (Value (if flags.rcf_revert_on_failure then
          if cap = 0 then NoneV else BytesV (TAKE cap outcome.co_returnData)
         else if cap = 0 then BoolV outcome.co_success
         else ArrayV (TupleV [BoolV outcome.co_success;BytesV (TAKE cap outcome.co_returnData)])))
        (if cap = 0 then StackValue ann result
         else LocatedValue (expr_type e) (mk_ptr result LocMemory)) u) \/
     (?u. flags.rcf_revert_on_failure /\ ~outcome.co_success /\
       r = Abort Revert_abort u /\ u.vs_returndata = outcome.co_returnData))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ci_mono sa sm` by metis_tac[ci_mono_compile_raw_call_outbuf, pairTheory.SND] >>
  `ci_mono sm sb` by metis_tac[ci_mono_compile_raw_call_finish, pairTheory.SND] >>
  `cs_extends sa sm /\ cs_extends sm sb` by fs[ci_mono_def] >>
  drule_all fn_has_code_split >> strip_tac >>
  Cases_on `emit_op (if stat then STATICCALL else CALL)
    (if stat then [gas_op;to_op;dp;dl;op;Lit (n2w cap)]
     else [gas_op;to_op;val_op;dp;dl;op;Lit (n2w cap)]) sm` >>
  rename1 `emit_op _ _ sm = (ok,sc)` >>
  `ci_mono sm sc` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `cs_extends sm sc` by fs[ci_mono_def] >>
  `cs_extends sc sb` by suspend "call_metadata" >>
  `fn_has_code sm sc func /\ fn_has_code sc sb func` by
    metis_tac[fn_has_code_split] >>
  `0 < cap ==> ((cap+31) DIV 32)*32+32 < dimword (:256)` by
    (strip_tac >> qpat_x_assum `0 < cap ==> 64 + _ < _` drule >> decide_tac) >>
  drule_all raw_call_allocated_oracle_mem >>
  disch_then (qx_choose_then `t` (qx_choose_then `w` (map_every assume_tac o CONJUNCTS))) >>
  Cases_on `flags.rcf_revert_on_failure`
  >- suspend "revert" >>
  suspend "nonrevert"
QED

Resume raw_call_outbuf_tail_mem[call_metadata]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `w2n az = 0 \/ _` kall_tac >>
  Cases_on `flags.rcf_revert_on_failure`
  >- (fs[] >> drule raw_call_finish_revert_compile >>
      simp[arithmeticTheory.GREATER_DEF] >> strip_tac >>
      rename1 `fresh_label "call_failed" ce = (fl,s2)` >>
      `ce = sc` by (Cases_on `stat` >> gvs[]) >> gvs[] >>
      rename1 `fresh_label "call_failed" sc = _` >>
      `ci_mono sc s2 /\ ci_mono s2 s3 /\ ci_mono s3 s4 /\
       ci_mono s4 s5 /\ ci_mono s5 s6 /\ ci_mono s6 s7 /\
       ci_mono s7 s8 /\ ci_mono s8 s9 /\ ci_mono s9 s10` by
        (rpt conj_tac >> metis_tac[ci_mono_fresh_label, ci_mono_emit_inst,
          ci_mono_new_block, ci_mono_emit_op, ci_mono_compile_alloc_buffer,
          ci_mono_emit_void, pairTheory.SND]) >>
      `cs_extends s10 sb` by
        (Cases_on `0 < flags.rcf_max_outsize` >> fs[comp_return_def]
         >- (drule raw_call_success_code >> strip_tac >>
             irule cs_extends_same_block >>
             fs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND]) >>
         simp[cs_extends_refl]) >>
      fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  fs[] >> drule raw_call_nonrevert_finish_code >> simp[] >> strip_tac >>
  `sc' = sc` by (Cases_on `stat` >> gvs[]) >> gvs[] >>
  Cases_on `0 < flags.rcf_max_outsize`
  >- (drule_at (Pat `0 < _`) raw_call_nonrevert_suffix_code >>
      fs[arithmeticTheory.GREATER_DEF] >>
      disch_then drule >> strip_tac >> metis_tac[cs_extends_trans]) >>
  fs[arithmeticTheory.GREATER_DEF, comp_return_def] >> simp[cs_extends_refl]
QED

Resume raw_call_outbuf_tail_mem[revert]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `w2n az = 0 \/ _` kall_tac >>
  `local_ptrs_reserved cenv sc` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[ci_mono_def]) >>
  `alloca_inv t` by fs[stmt_state_rel_def] >>
  gvs[] >>
  qpat_assum `compile_raw_call_finish _ _ _ _ _ _ _ T _ _ _ = _`
    (mp_then Any mp_tac raw_call_revert_finish_path_mem) >>
  disch_then (drule_at (Pat `emit_op _ _ _ = _`)) >>
  disch_then (qspec_then `outcome.co_success` mp_tac) >>
  disch_then (drule_at (Pat `alloca_history func t`)) >>
  disch_then (qspecl_then [`ctx`,`w`] mp_tac) >>
  (impl_tac >- suspend "revert_entry") >>
  strip_tac >> suspend "revert_result"
QED

Resume raw_call_outbuf_tail_mem[nonrevert]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `w2n az = 0 \/ _` kall_tac >>
  `local_ptrs_reserved cenv sc` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[ci_mono_def]) >>
  `initial.cs_next_var <= sc.cs_next_var` by (fs[ci_mono_def] >> decide_tac) >>
  fs[] >> drule raw_call_nonrevert_finish_code >> simp[] >> strip_tac >>
  `sc' = sc /\ ok' = ok` by (Cases_on `stat` >> gvs[]) >> gvs[] >>
  Cases_on `0 < flags.rcf_max_outsize`
  >- suspend "tuple" >>
  fs[arithmeticTheory.GREATER_DEF, comp_return_def] >>
  `flags.rcf_max_outsize = 0` by decide_tac >>
  `expr_type e = BaseT BoolT` by
    fs[raw_call_return_type_def] >>
  `expr_val_rel cx (BaseT BoolT) (BoolV outcome.co_success) result t` by
    (simp[expr_val_rel_def, vyperValueTheory.evaluate_type_def,
       is_word_type_def, typed_val_to_w256_def, val_to_w256_def] >>
     Cases_on `outcome.co_success` >> simp[bool_to_word_def]) >>
  metis_tac[raw_call_zero_finish_post_mem]
QED

Resume raw_call_outbuf_tail_mem[tuple]:
  markerLib.RESUME_TAC >>
  fs[arithmeticTheory.GREATER_DEF, raw_call_return_type_def] >>
  qpat_assum `expr_type e = _`
    (mp_then (Pat `expr_type _ = _`) mp_tac raw_call_nonrevert_positive_path_mem) >>
  simp[arithmeticTheory.GREATER_DEF, arithmeticTheory.MULT_COMM] >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ t`)) >>
  disch_then (drule_at (Pat `wb_frame _ _ _ _ t`)) >>
  disch_then (drule_at (Pat `do _ od _ = (_,_)`)) >>
  disch_then (drule_at (Pat `MEM _ (fn_insts _)`)) >>
  disch_then (drule_at (Pat `eval_operand ov t = _`)) >>
  disch_then (qspec_then `outcome.co_success` mp_tac) >>
  disch_then (drule_at (Pat `alloc.inst_outputs = _`)) >>
  disch_then (drule_at (Pat `safe_operand sc ok`)) >>
  (impl_tac >- (simp[] >> Cases_on `outcome.co_success` >> simp[bool_to_word_def])) >>
  strip_tac >>
  rename1 `run_inst_seq _ t = OK u` >>
  qexists_tac `OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)` >>
  conj_tac >- (drule_all gas_path_mem_then >> simp[]) >>
  gvs[]
QED

Resume raw_call_outbuf_tail_mem[revert_entry]:
  simp[] >>
  conj_tac >- (Cases_on `outcome.co_success` >> simp[bool_to_word_def]) >>
  strip_tac >>
  fs[safe_operand_def] >>
  fs[venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >>
  first_x_assum drule >> simp[] >> decide_tac
QED

Resume raw_call_outbuf_tail_mem[revert_result]:
  markerLib.RESUME_TAC
  >- (qexists_tac `Abort Revert_abort u` >> gvs[] >>
      drule_all gas_path_mem_then >> simp[]) >>
  suspend "revert_normal"
QED

Resume raw_call_outbuf_tail_mem[revert_normal]:
  markerLib.RESUME_TAC >>
  `initial.cs_next_var <= sc.cs_next_var` by (fs[ci_mono_def] >> decide_tac) >>
  Cases_on `0 < flags.rcf_max_outsize`
  >- suspend "revert_bytes" >>
  gvs[] >>
  `stmt_state_rel ctx func cenv cx (SND (adopt_call_outcome rq outcome es1)) u` by
    (irule raw_call_finish_state_rel_aged >>
     qexistsl_tac [`0w`,`0`,`0w`,`sc`,`t`] >> simp[]) >>
  `wb_frame cenv initial_es initial s0 u` by
    (irule raw_call_finish_frame_aged >>
     qexistsl_tac [`0w`,`0`,`0w`,`sc`,`t`] >> simp[]) >>
  `flags.rcf_max_outsize = 0` by decide_tac >>
  qexists_tac `OK u` >>
  conj_tac >- (drule_all gas_path_mem_then >> simp[]) >>
  simp[] >>
  `expr_type e = NoneT` by fs[raw_call_return_type_def] >>
  metis_tac[raw_call_zero_finish_post_mem]
QED

Resume raw_call_outbuf_tail_mem[revert_bytes]:
  fs[] >>
  `!name lb lsz. local_region cenv (SND (adopt_call_outcome rq outcome es1)).scopes t name lb lsz ==>
    w2n w + (32*((flags.rcf_max_outsize+31) DIV 32)+32) <= lb \/ lb+lsz <= w2n w` by
    (rpt strip_tac >>
     `regions_disjoint (w2n w) (32*((flags.rcf_max_outsize+31) DIV 32)+32) lb lsz`
       suffices_by simp[compileEnvTheory.regions_disjoint_def] >>
     irule local_ptrs_rel_alloca_disjoint >>
     goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >>
     goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
     fs[stmt_state_rel_def, state_rel_def]) >>
  `stmt_state_rel ctx func cenv cx (SND (adopt_call_outcome rq outcome es1)) u` by
    (irule (INST_TYPE [alpha |-> ``:256``] raw_call_finish_state_rel_aged) >>
     qexistsl_tac [`w`,`flags.rcf_max_outsize`,
       `n2w (MIN (LENGTH outcome.co_returnData) flags.rcf_max_outsize)`,`sc`,`t`] >>
     simp[] >> qexistsl_tac [`alloc`,`w2n w`,
       `32*((flags.rcf_max_outsize+31) DIV 32)+32`] >> gvs[] >> metis_tac[]) >>
  `wb_frame cenv initial_es initial s0 u` by
    (irule (INST_TYPE [alpha |-> ``:256``] raw_call_finish_frame_aged) >>
     qexistsl_tac [`w`,`flags.rcf_max_outsize`,
       `n2w (MIN (LENGTH outcome.co_returnData) flags.rcf_max_outsize)`,`sc`,`t`] >>
     simp[] >> conj_tac
     >- (rpt strip_tac >>
         qpat_assum `!aid b sz. _ /\ FLOOKUP t.vs_allocas aid = _ ==> _`
           (drule_all_then strip_assume_tac) >> fs[regions_disjoint_def] >> decide_tac) >>
     rpt strip_tac >>
     qpat_assum `!name b sz. local_region cenv initial_es.scopes s0 name b sz ==> _`
       (drule_all_then strip_assume_tac) >> fs[regions_disjoint_def] >> decide_tac) >>
  suspend "revert_bytes_post"
QED

Resume raw_call_outbuf_tail_mem[revert_bytes_post]:
  `expr_type e = BaseT (BytesT (Dynamic flags.rcf_max_outsize))` by
    fs[raw_call_return_type_def] >>
  `u.vs_allocas = t.vs_allocas` by
    (qpat_assum `raw_call_finish_view u = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[raw_call_finish_view_def, venom_state_component_equality, mstore_def]) >>
  `eval_operand ov u = SOME w` by metis_tac[] >>
  `!name lb lsz. local_region cenv (SND (adopt_call_outcome rq outcome es1)).scopes u name lb lsz ==>
    w2n w + (32*((flags.rcf_max_outsize+31) DIV 32)+32) <= lb \/ lb+lsz <= w2n w` by
    (rpt strip_tac >>
     `regions_disjoint (w2n w) (32*((flags.rcf_max_outsize+31) DIV 32)+32) lb lsz`
       suffices_by simp[regions_disjoint_def] >>
     irule local_ptrs_rel_alloca_disjoint >>
     goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >>
     goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
     fs[stmt_state_rel_def, state_rel_def]) >>
  qexists_tac `OK u` >>
  conj_tac >- (drule_all gas_path_mem_then >> simp[]) >>
  simp[] >>
  `vv_post ctx func cenv cx e initial_es initial sb s0
     (SND (adopt_call_outcome rq outcome es1))
     (Value (BytesV (TAKE flags.rcf_max_outsize outcome.co_returnData)))
     (LocatedValue (expr_type e) (mk_ptr ov LocMemory)) u /\
   vv_store_bound cx (expr_type e) (lowered_value_type cenv e)
     (SND (adopt_call_outcome rq outcome es1))
     (Value (BytesV (TAKE flags.rcf_max_outsize outcome.co_returnData)))
     (LocatedValue (expr_type e) (mk_ptr ov LocMemory)) u`
    suffices_by gvs[] >>
  irule raw_call_bytes_finish_post_mem >> simp[NoAsms] >> simp[] >>
  gvs[] >>
  qexistsl_tac [`sa.cs_next_id`,`w2n w`,
    `32*((flags.rcf_max_outsize+31) DIV 32)`,`t`] >>
  gvs[] >> conj_tac
  >- (drule_all raw_call_outbuf_positive_id_growth >> fs[ci_mono_def] >> decide_tac) >>
  conj_tac >- metis_tac[] >>
  qspec_then `flags.rcf_max_outsize` mp_tac valueTypingMemoryPropsTheory.word_size_capacity >>
  simp[vfmConstantsTheory.word_size_def]
QED

Finalise raw_call_outbuf_tail_mem
