(* The compiled length word is stored at one endpoint for every dead mask. *)
Theory bodyFullRawCallLength
Ancestors
  rawCallBufferPtr rawCallShapePtr rawCallFinishCodePtr fragGasCopyLoop
  instSeqComposePtr fragGasSeqPtr fragGasOriginPtr fragGasOriginPtrDead
  fragExecMem fragExecPtr fragExec instIdxIndep
  ptrSafetyTransport ptrDiscipline bodyPtrDefs ghostPcTransportPtr
  exprLoweringProps emitHelperProps loweringShapeRules compileEnv builtinSimple
  emitHelper context venomExecSemantics venomInst venomState venomMemProps
  valueEncodingDefs valueEncoding words list rich_list finite_map pred_set
  arithmetic gasEvents gasCount instMemFrontier memSafeRun freshWrites
  ssaOperandFrame
Libs monadsyntax pairLib

Theorem raw_call_length_store_origin_ptr:
  !sa sb n p capacity a s G tn lo explicit ctx func PG.
  (do rds <- emit_op RETURNDATASIZE [];
      cmp <- emit_op LT [rds;Lit (n2w n)];
      cap <- compile_select cmp rds (Lit (n2w n));
      emit_void MSTORE [Var p;cap] od) sa = ((),sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ allocas_from lo s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa p /\ lookup_var p s = SOME a /\
  ptr_covers G tn p s capacity /\ 32 <= capacity /\
  w2n a + 32 <= s.vs_alloca_next /\
  n < dimword (:256) /\ LENGTH s.vs_returndata < dimword (:256) /\
  mem_bytes_at (w2n a+32) (LENGTH (TAKE n s.vs_returndata)) s.vs_memory =
    TAKE n s.vs_returndata /\
  (!i. w2n a+32 <= i /\
       i < w2n a+32+LENGTH (TAKE n s.vs_returndata) ==> i NOTIN tn.t_mem)
  ==>
  ?z_raw z J un.
    run_inst_seq (emitted_insts sa sb) s = OK z_raw /\
    z = z_raw with vs_inst_idx := LENGTH sb.cs_current_insts /\
    z = (mstore (w2n a) (n2w (MIN (LENGTH s.vs_returndata) n)) s)
      with <|vs_vars := z.vs_vars; vs_inst_idx := LENGTH sb.cs_current_insts|> /\
    z.vs_current_bb = sb.cs_current_bb /\
    ptr_covers J un p z capacity /\
    un.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32} /\
    un.t_stor = tn.t_stor /\ un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x z = lookup_var x s /\ FLOOKUP J x = FLOOKUP G x /\
      op_taint un (Var x) = op_taint tn (Var x)) /\
    (!mem. mem_agree_outside un.t_mem z.vs_memory mem ==>
      val_in_memory (BaseTV (BytesT (Dynamic n)))
        (BytesV (TAKE n s.vs_returndata)) (w2n a) mem) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts sa sb) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK z,J,un))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `?rds s1 cmp s2 cap s3.
    emit_op RETURNDATASIZE [] sa = (rds,s1) /\
    emit_op LT [rds;Lit (n2w n)] s1 = (cmp,s2) /\
    compile_select cmp rds (Lit (n2w n)) s2 = (cap,s3) /\
    emit_void MSTORE [Var p;cap] s3 = ((),sb)` by
    (qpat_x_assum `(do _ <- _; _ od) sa = ((),sb)` mp_tac >>
     simp[comp_bind_def,comp_ignore_bind_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  qpat_assum `emit_op RETURNDATASIZE [] sa = (rds,s1)`
    (mp_then (Pat `emit_op _ _ _ = _`) mp_tac emit_op_facts) >>
  disch_then (qx_choose_then `rz` strip_assume_tac) >>
  qpat_x_assum `rds = Var rz` SUBST_ALL_TAC >>
  qpat_assum `emit_op LT _ s1 = (cmp,s2)`
    (mp_then (Pat `emit_op _ _ _ = _`) mp_tac emit_op_facts) >>
  disch_then (qx_choose_then `cmpx` strip_assume_tac) >>
  qpat_x_assum `cmp = Var cmpx` SUBST_ALL_TAC >>
  `ci_mono sa s1 /\ ci_mono s1 s2 /\
   ci_mono s2 s3 /\ ci_mono s3 sb` by
    metis_tac[ci_mono_emit_op,ci_mono_compile_select,ci_mono_emit_void,
      pairTheory.SND] >>
  `p <> rz /\ p <> cmpx /\ rz <> cmpx /\ not_fresh_at s2 p /\
   not_fresh_at s2 rz` by
    (fs[ci_mono_def] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `emitted_insts sa s1 = [mk_inst sa.cs_next_id RETURNDATASIZE [] [rz]] /\
   emitted_insts s1 s2 = [mk_inst s1.cs_next_id LT [Var rz;Lit (n2w n)] [cmpx]] /\
   emitted_insts s3 sb = [mk_inst s3.cs_next_id MSTORE [Var p;cap] []]` by
    (conj_tac
     >- (qpat_assum `emit_op RETURNDATASIZE [] sa = _`
           (mp_then Any mp_tac emitted_insts_emit_op) >> simp[]) >>
     conj_tac
     >- (qpat_assum `emit_op LT _ s1 = _`
           (mp_then Any mp_tac emitted_insts_emit_op) >> simp[]) >>
     qpat_assum `emit_void MSTORE _ s3 = _`
       (mp_then Any mp_tac emitted_insts_emit_void) >> simp[]) >>
  suspend "execute"
QED

Resume raw_call_length_store_origin_ptr[execute]:
  qabbrev_tac `i_rds = mk_inst sa.cs_next_id RETURNDATASIZE [] [rz]` >>
  qabbrev_tac `t_rds = update_var rz (n2w (LENGTH s.vs_returndata)) s` >>
  qabbrev_tac `G_rds = step_prov PG G i_rds t_rds` >>
  qabbrev_tac `tn_rds = step_taint i_rds s t_rds tn` >>
  `step_inst_base i_rds s = OK t_rds` by
    simp[Abbr `i_rds`,Abbr `t_rds`,raw_call_returndatasize_step_base] >>
  `G_rds = DRESTRICT G (COMPL {rz}) /\
   tn_rds = tn with t_var := tn.t_var |+ (rz,{})` by
    simp[Abbr `G_rds`,Abbr `tn_rds`,Abbr `i_rds`,Abbr `t_rds`,
      raw_call_returndatasize_step_taint,step_prov_def,set_prov_def,
      out_prov_def,mk_inst_def] >>
  qabbrev_tac `i_cmp = mk_inst s1.cs_next_id LT [Var rz;Lit (n2w n)] [cmpx]` >>
  qabbrev_tac `t_cmp = update_var cmpx
    (bool_to_word (LENGTH s.vs_returndata < n)) t_rds` >>
  qabbrev_tac `G_cmp = step_prov PG G_rds i_cmp t_cmp` >>
  qabbrev_tac `tn_cmp = step_taint i_cmp t_rds t_cmp tn_rds` >>
  `eval_operand (Var rz) t_rds = SOME (n2w (LENGTH s.vs_returndata)) /\
   eval_operand (Lit (n2w n)) t_rds = SOME (n2w n)` by
    simp[Abbr `t_rds`,eval_operand_def,lookup_var_def,update_var_def,
      FLOOKUP_UPDATE] >>
  `step_inst_base i_cmp t_rds = OK t_cmp` by
    simp[Abbr `i_cmp`,Abbr `t_cmp`,step_inst_base_opcode_eqs,
      mk_inst_def,exec_pure2_def,wordsTheory.w2n_n2w,
      arithmeticTheory.LESS_MOD] >>
  `G_cmp = DRESTRICT G_rds (COMPL {cmpx}) /\
   tn_cmp = tn_rds with t_var := tn_rds.t_var |+ (cmpx,{})` by
    simp[Abbr `G_cmp`,Abbr `tn_cmp`,Abbr `i_cmp`,Abbr `t_cmp`,
      raw_call_length_binop_step_ghost] >>
  `eval_operand (Var cmpx) t_cmp =
     SOME (bool_to_word (LENGTH s.vs_returndata < n)) /\
   eval_operand (Var rz) t_cmp = SOME (n2w (LENGTH s.vs_returndata)) /\
   eval_operand (Lit (n2w n)) t_cmp = SOME (n2w n)` by
    simp[Abbr `t_cmp`,Abbr `t_rds`,eval_operand_def,lookup_var_def,
      update_var_def,FLOOKUP_UPDATE] >>
  mp_tac (Q.INST [`condop` |-> `Var cmpx`,`tp` |-> `Var rz`,
    `ep` |-> `Lit (n2w n)`,`sa` |-> `s2`,`sb` |-> `s3`,`op` |-> `cap`,
    `s` |-> `t_cmp`,`b` |-> `LENGTH s.vs_returndata < n`,
    `tv` |-> `n2w (LENGTH s.vs_returndata)`,`ev` |-> `n2w n`]
    raw_call_select_run_code) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `t_sel` strip_assume_tac) >>
  `eval_operand cap t_sel = SOME (n2w (MIN (LENGTH s.vs_returndata) n))` by
    (Cases_on `LENGTH s.vs_returndata < n` >> fs[arithmeticTheory.MIN_DEF]) >>
  qpat_assum `compile_select _ _ _ s2 = (cap,s3)`
    (mp_then (Pat `compile_select _ _ _ _ = _`) mp_tac raw_call_select_state_frame) >>
  disch_then (qspec_then `t_sel` mp_tac) >>
  disch_then (qspec_then `t_cmp` mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  `lookup_var p t_cmp = SOME a` by
    (qpat_assum `lookup_var p s = SOME a`
       (mp_tac o REWRITE_RULE [lookup_var_def]) >>
     simp[Abbr `t_cmp`,Abbr `t_rds`,lookup_var_def,update_var_def,FLOOKUP_UPDATE]) >>
  `lookup_var p t_sel = SOME a` by metis_tac[] >>
  qabbrev_tac `i_store = mk_inst s3.cs_next_id MSTORE [Var p;cap] []` >>
  qabbrev_tac `z_raw = mstore (w2n a)
    (n2w (MIN (LENGTH s.vs_returndata) n)) t_sel` >>
  `step_inst_base i_store t_sel = OK z_raw` by
    simp[Abbr `i_store`,Abbr `z_raw`,step_inst_base_opcode_eqs,
      mk_inst_def,exec_write2_def,eval_operand_def] >>
  suspend "ghosts"
QED

Resume raw_call_length_store_origin_ptr[ghosts]:
  qabbrev_tac `D0 = <|d_stor := K (K {}); d_trans := K (K {});
    d_imm := K {}; d_ret := K {}|>` >>
  mp_tac (Q.INST [`condop` |-> `Var cmpx`,`tp` |-> `Var rz`,
    `ep` |-> `Lit (n2w n)`,`sa` |-> `s2`,`sb` |-> `s3`,`op` |-> `cap`,
    `s` |-> `t_cmp with vs_inst_idx := s.vs_inst_idx+2`,
    `G` |-> `G_cmp`,`tn` |-> `tn_cmp`,`D` |-> `D0`,
    `ctx` |-> `ctx`,`func` |-> `func`,`PG` |-> `PG`,
    `cv` |-> `bool_to_word (LENGTH s.vs_returndata < n)`,
    `tv` |-> `n2w (LENGTH s.vs_returndata)`,`ev` |-> `n2w n`]
    raw_call_select_checked_code) >>
  impl_tac >-
    simp[op_prov_def,op_taint_def,FLOOKUP_DRESTRICT,FLOOKUP_UPDATE] >>
  disch_then (qx_choosel_then [`G_sel`,`tn_sel`] strip_assume_tac) >>
  `FLOOKUP G_sel p = FLOOKUP G p /\
   op_taint tn_sel (Var p) = op_taint tn (Var p)` by
    (qpat_assum `!x. not_fresh_at s2 x ==> _` (qspec_then `p` mp_tac) >>
     simp[op_taint_def,FLOOKUP_DRESTRICT,FLOOKUP_UPDATE]) >>
  `ptr_covers G_sel tn_sel p t_sel capacity` by
    (qpat_assum `ptr_covers G tn p s capacity`
       (strip_assume_tac o REWRITE_RULE [ptr_covers_def]) >>
     rename1 `FLOOKUP G p = SOME (b0,sz0)` >>
     rewrite_tac[ptr_covers_def] >> conj_tac >- simp[] >>
     qexistsl_tac [`a`,`b0`,`sz0`] >> gvs[]) >>
  qabbrev_tac `un = tn_sel with t_mem :=
    tn_sel.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32}` >>
  `step_taint i_store t_sel z_raw tn_sel = un /\
   step_prov PG G_sel i_store z_raw = G_sel` by
    simp[Abbr `i_store`,Abbr `z_raw`,Abbr `un`,
      raw_call_mstore_clean_effect,step_prov_def,set_prov_def,mk_inst_def,
      DRESTRICT_UNIV] >>
  suspend "sequence"
QED

Resume raw_call_length_store_origin_ptr[sequence]:
  qpat_assum `compile_select _ _ _ s2 = (cap,s3)`
    (mp_then (Pat `compile_select _ _ _ _ = _`) mp_tac raw_call_select_code) >>
  disch_then (qx_choosel_then [`delta`,`mask`,`out`] strip_assume_tac) >>
  qpat_assum `emit_void MSTORE _ s3 = ((),sb)`
    (mp_then Any mp_tac emit_void_extends) >> strip_tac >>
  `same_blocks sa sb` by fs[same_blocks_def] >>
  `sb.cs_current_insts = sa.cs_current_insts ++
    ([i_rds;i_cmp] ++ emitted_insts s2 s3 ++ [i_store])` by
    simp[Abbr `i_store`,APPEND_ASSOC] >>
  `emitted_insts sa sb =
    [i_rds;i_cmp] ++ emitted_insts s2 s3 ++ [i_store]` by
    (qpat_assum `sb.cs_current_insts = sa.cs_current_insts ++ _`
       (fn th => PURE_REWRITE_TAC [emitted_insts_def,th,DROP_LENGTH_APPEND]) >>
     REFL_TAC) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    simp[Abbr `i_rds`,Abbr `i_cmp`,Abbr `i_store`,mk_inst_def,is_terminator_def] >>
  `run_inst_seq [i_rds;i_cmp] s = OK t_cmp` by simp[run_inst_seq_def] >>
  `run_inst_seq ([i_rds;i_cmp] ++ emitted_insts s2 s3) s = OK t_sel` by
    (qpat_assum `run_inst_seq [i_rds;i_cmp] s = OK t_cmp`
       (fn th => ONCE_REWRITE_TAC [MATCH_MP run_inst_seq_append th]) >>
     first_assum ACCEPT_TAC) >>
  `run_inst_seq (emitted_insts sa sb) s = OK z_raw` by
    (qpat_assum `emitted_insts sa sb = _`
       (fn th => ONCE_REWRITE_TAC [th]) >>
     PURE_REWRITE_TAC [GSYM APPEND_ASSOC] >>
     qpat_assum `run_inst_seq [i_rds;i_cmp] s = OK t_cmp`
       (fn th => ONCE_REWRITE_TAC [MATCH_MP run_inst_seq_append th]) >>
     qpat_assum `run_inst_seq (emitted_insts s2 s3) t_cmp = OK t_sel`
       (fn th => ONCE_REWRITE_TAC [MATCH_MP run_inst_seq_append th]) >>
     asm_rewrite_tac[run_inst_seq_def] >> simp[]) >>
  `~is_terminator i_cmp.inst_opcode` by
    simp[Abbr `i_cmp`,mk_inst_def,is_terminator_def] >>
  `step_inst_base i_cmp (t_rds with vs_inst_idx := SUC s.vs_inst_idx) =
    OK (t_cmp with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[step_inst_inst_idx_indep,exec_result_map_def] >>
  `inst_seq_ptr D0 0 ctx func PG G tn [i_rds;i_cmp] s G_cmp tn_cmp` by
    (simp[Once inst_seq_ptr_def] >> conj_tac
     >- simp[Abbr `i_rds`,ptr_inst_ok_returndatasize] >>
     simp[] >> simp[Once inst_seq_ptr_def] >> conj_tac
     >- (simp[Abbr `i_cmp`] >> irule ptr_inst_ok_raw_call_length_binop >>
         simp[op_prov_def,op_taint_def,FLOOKUP_DRESTRICT,FLOOKUP_UPDATE]) >>
     simp[inst_seq_ptr_def,step_inst_inst_idx_indep,exec_result_map_def,
       Abbr `G_cmp`,Abbr `tn_cmp`,Abbr `i_cmp`,Abbr `t_cmp`,
       raw_call_length_binop_step_ghost]) >>
  suspend "store_ptr"
QED

Resume raw_call_length_store_origin_ptr[store_ptr]:
  `ptr_covers G_sel tn_sel p t_sel 32` by
    (qpat_assum `ptr_covers G_sel tn_sel p t_sel capacity` mp_tac >>
     qpat_assum `32 <= capacity` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     strip_tac >> rewrite_tac[ptr_covers_def] >> strip_tac >>
     rename1 `lookup_var p t_sel = SOME wp` >>
     rename1 `FLOOKUP G_sel p = SOME (b0,sz0)` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`wp`,`b0`,`sz0`] >> simp[] >> decide_tac) >>
  `~is_terminator i_store.inst_opcode` by
    simp[Abbr `i_store`,mk_inst_def,is_terminator_def] >>
  `!k. inst_seq_ptr D0 0 ctx func PG G_sel tn_sel [i_store]
    (t_sel with vs_inst_idx := k) G_sel un` by
    (gen_tac >> simp[Once inst_seq_ptr_def] >> conj_tac
     >- (qpat_assum `Abbrev (i_store = _)`
           (fn th => PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
         irule ptr_inst_ok_mstore >> rpt conj_tac >>
         simp_tac (srw_ss()) [] >> first_assum ACCEPT_TAC) >>
     simp[step_inst_inst_idx_indep,exec_result_map_def,inst_seq_ptr_def]) >>
  `run_inst_seq (emitted_insts s2 s3)
    (t_cmp with vs_inst_idx := s.vs_inst_idx+2) =
    OK (t_sel with vs_inst_idx := s.vs_inst_idx+2)` by
    (qspecl_then [`emitted_insts s2 s3`,`t_cmp`,`s.vs_inst_idx+2`]
       mp_tac run_inst_seq_inst_idx >>
     impl_tac >- simp[mk_inst_def,is_terminator_def] >>
     disch_then (fn th => ONCE_REWRITE_TAC [th]) >>
     qpat_assum `run_inst_seq (emitted_insts s2 s3) t_cmp = OK t_sel`
       (fn th => ONCE_REWRITE_TAC [th]) >> simp[exec_result_map_def]) >>
  `inst_seq_ptr D0 0 ctx func PG G_cmp tn_cmp
    (emitted_insts s2 s3 ++ [i_store])
    (t_cmp with vs_inst_idx := s.vs_inst_idx+2) G_sel un` by
    (irule inst_seq_ptr_append >> conj_tac
     >- simp[mk_inst_def,is_terminator_def] >>
     qexistsl_tac [`G_sel`,`t_sel with vs_inst_idx := s.vs_inst_idx+2`,`tn_sel`] >>
     rpt conj_tac >> simp_tac (srw_ss()) [] >> first_assum ACCEPT_TAC) >>
  `inst_seq_ptr D0 0 ctx func PG G tn (emitted_insts sa sb) s G_sel un` by
    (qpat_assum `emitted_insts sa sb = _`
       (fn th => ONCE_REWRITE_TAC [th]) >>
     PURE_REWRITE_TAC [GSYM APPEND_ASSOC] >>
     irule inst_seq_ptr_append_ok >> conj_tac
     >- simp[Abbr `i_rds`,Abbr `i_cmp`,mk_inst_def,is_terminator_def] >>
     qexistsl_tac [`G_cmp`,`t_cmp`,`tn_cmp`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     simp_tac (srw_ss()) [] >> first_assum ACCEPT_TAC) >>
  suspend "memory"
QED

Resume raw_call_length_store_origin_ptr[memory]:
  `t_sel = s with vs_vars := t_sel.vs_vars` by
    (qpat_assum `t_sel = t_cmp with vs_vars := _`
       (fn th => ONCE_REWRITE_TAC [th]) >>
     simp[Abbr `t_cmp`,Abbr `t_rds`,update_var_def]) >>
  `t_sel.vs_alloca_next = s.vs_alloca_next /\
   t_sel.vs_current_bb = s.vs_current_bb /\
   t_sel.vs_memory = s.vs_memory` by
    (qpat_assum `t_sel = s with vs_vars := _`
       (fn th => ONCE_REWRITE_TAC [th]) >> simp[]) >>
  `z_raw = (mstore (w2n a) (n2w (MIN (LENGTH s.vs_returndata) n)) s)
    with vs_vars := t_sel.vs_vars` by
    (simp_tac bool_ss [Abbr `z_raw`] >>
     qpat_assum `t_sel = s with vs_vars := _`
       (fn th => ONCE_REWRITE_TAC [th]) >> simp[mstore_reset_vars]) >>
  `!u. run_inst_seq_mem_ok ([i_rds;i_cmp] ++ emitted_insts s2 s3) u` by
    (gen_tac >> irule run_inst_seq_mem_ok_every >>
     simp[Abbr `i_rds`,Abbr `i_cmp`,mk_inst_def,
       unitTransformDefsTheory.inst_mem_below_frontier_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def,inst_dload_in_section_def]) >>
  `run_inst_seq_mem_ok [i_store] t_sel` by
    simp[run_inst_seq_mem_ok_last,Abbr `i_store`,below_frontier_MSTORE,
      inst_dload_in_section_def,mk_inst_def,eval_operand_def] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (qpat_assum `emitted_insts sa sb = _`
       (fn th => ONCE_REWRITE_TAC [th]) >>
     irule run_inst_seq_mem_ok_append >> conj_tac >- simp[] >>
     qpat_assum `!u. run_inst_seq_mem_ok _ u`
       (qspec_then `s` ACCEPT_TAC)) >>
  qabbrev_tac `z = z_raw with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `ptr_covers G_sel un p z capacity` by
    (qpat_assum `ptr_covers G_sel tn_sel p t_sel capacity`
       (mp_tac o REWRITE_RULE [ptr_covers_def]) >>
     simp_tac (srw_ss()) [ptr_covers_def,Abbr `z`,Abbr `z_raw`,Abbr `un`,
       op_taint_def,lookup_var_def,mstore_vars]) >>
  `un.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32} /\
   un.t_stor = tn.t_stor /\ un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm` by
    simp[Abbr `un`] >>
  `LENGTH (TAKE n s.vs_returndata) = MIN (LENGTH s.vs_returndata) n` by
    (rw[LENGTH_TAKE_EQ,MIN_DEF] >> decide_tac) >>
  `z.vs_memory =
    (mstore (w2n a) (n2w (MIN (LENGTH s.vs_returndata) n)) s).vs_memory` by
    (simp_tac bool_ss [Abbr `z`] >>
     qpat_assum `z_raw = _ with vs_vars := _`
       (fn th => ONCE_REWRITE_TAC [th]) >> simp[]) >>
  `!mem. mem_agree_outside un.t_mem z.vs_memory mem ==>
    val_in_memory (BaseTV (BytesT (Dynamic n)))
      (BytesV (TAKE n s.vs_returndata)) (w2n a) mem` by
    (rpt strip_tac >> irule bytes_length_store_robust >>
     conj_tac >- (simp[] >> rw[MIN_DEF] >> decide_tac) >>
     qexistsl_tac [`tn.t_mem`,`s`] >>
     asm_rewrite_tac[] >>
     qpat_assum `un.t_mem = tn.t_mem DIFF _` (fn dirty_th =>
       qpat_assum `z.vs_memory = _` (fn memory_th =>
         qpat_assum `mem_agree_outside un.t_mem z.vs_memory mem`
           (ACCEPT_TAC o REWRITE_RULE [dirty_th,memory_th])))) >>
  suspend "finish"
QED

Resume raw_call_length_store_origin_ptr[finish]:
  `!x. not_fresh_at sa x ==>
    not_fresh_at s2 x /\ x <> rz /\ x <> cmpx` by
    (rpt strip_tac >> fs[ci_mono_def] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `!x. not_fresh_at sa x ==>
    lookup_var x z = lookup_var x s /\ FLOOKUP G_sel x = FLOOKUP G x /\
    op_taint un (Var x) = op_taint tn (Var x)` by
    (gen_tac >> strip_tac >>
     `not_fresh_at s2 x /\ x <> rz /\ x <> cmpx` by simp[] >>
     `lookup_var x t_sel = lookup_var x s` by
       simp[Abbr `t_cmp`,Abbr `t_rds`,lookup_var_def,update_var_def,FLOOKUP_UPDATE] >>
     `lookup_var x z = lookup_var x t_sel` by
       simp_tac (srw_ss()) [Abbr `z`,Abbr `z_raw`,lookup_var_def,mstore_vars] >>
     `FLOOKUP G_sel x = FLOOKUP G x /\
      op_taint tn_sel (Var x) = op_taint tn (Var x)` by
       (qpat_assum `!x. not_fresh_at s2 x ==> FLOOKUP _ _ = _ /\ _`
          (qspec_then `x` mp_tac) >>
        simp[op_taint_def,FLOOKUP_DRESTRICT,FLOOKUP_UPDATE]) >>
     `op_taint un (Var x) = op_taint tn_sel (Var x)` by
       simp_tac (srw_ss()) [Abbr `un`,op_taint_def] >> simp[]) >>
  `z = (mstore (w2n a) (n2w (MIN (LENGTH s.vs_returndata) n)) s)
    with <|vs_vars := z.vs_vars; vs_inst_idx := LENGTH sb.cs_current_insts|>` by
    simp[Abbr `z`,mstore_vars] >>
  `z.vs_current_bb = sb.cs_current_bb` by
    (simp[Abbr `z`,Abbr `z_raw`,mstore_def,write_memory_with_expansion_def] >>
     fs[same_blocks_def]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `fn_has_code sa sb func`
       (strip_assume_tac o REWRITE_RULE [fragExecTheory.fn_has_code_def]) >>
     rename1 `lookup_block sb.cs_current_bb func.fn_blocks = SOME bb0` >>
     qpat_assum `isPREFIX sb.cs_current_insts bb0.bb_instructions`
       (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
     rename1 `bb0.bb_instructions = sb.cs_current_insts ++ extra` >>
     qexists_tac `bb0` >> conj_tac
     >- (qpat_assum `s.vs_current_bb = sa.cs_current_bb`
           (fn th => PURE_REWRITE_TAC [th]) >>
         qpat_assum `same_blocks sa sb`
           (fn th => PURE_REWRITE_TAC
             [GSYM (CONJUNCT2 (REWRITE_RULE [same_blocks_def] th))]) >>
         first_assum ACCEPT_TAC) >>
     simp[IS_PREFIX_APPEND] >>
     qexists_tac `extra` >>
     rewrite_tac[GSYM APPEND_ASSOC,DROP_LENGTH_APPEND] >> simp[]) >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) =
    LENGTH sb.cs_current_insts` by simp[] >>
  `gas_origin_ptr_path (D0,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK z,G_sel,un) /\ allocas_from lo z_raw` by
    (simp_tac bool_ss [Abbr `z`] >>
     qpat_assum `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = _`
       (fn th => ONCE_REWRITE_TAC [GSYM th]) >>
     irule run_inst_seq_origin_ptr_lift >>
     rpt conj_tac >> FIRST
       [first_assum ACCEPT_TAC,
        qexists_tac `bb` >> conj_tac >> first_assum ACCEPT_TAC]) >>
  `z = z_raw with vs_inst_idx := LENGTH sb.cs_current_insts` by
    simp_tac bool_ss [Abbr `z`] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK z,G_sel,un)` by
    (gen_tac >> irule gas_origin_ptr_path_from_no_dead >>
     qpat_assum `gas_origin_ptr_path (D0,_,_,_,_,_) _ _ _` mp_tac >>
     simp_tac (srw_ss()) [Abbr `D0`]) >>
  qexistsl_tac [`z_raw`,`z`,`G_sel`,`un`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise raw_call_length_store_origin_ptr
