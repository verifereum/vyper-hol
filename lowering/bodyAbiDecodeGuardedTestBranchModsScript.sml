Theory bodyAbiDecodeGuardedTestBranchMods
Ancestors
  bodyFullAbiDecodeLoopHeaderExact bodyFullAbiDecodeRelativeLoadExact
  bodyFullAbiDecodeFiniteObserved typedCopyOriginPtrBase typedMemoryCopy
  bodyPtrMakeArrayEmission stmtSimProps emitHelperProps exprLoweringProps
  stateFrame fragExec fragGasPath venomInst venomState words list
  compileEnv emitHelper loweringShapeRules venomExecSemantics finite_map

local
  val template = abi_decode_loop_owned_branch_exact
  val (entry, post) = dest_imp (concl template)
  val (results, body) = strip_exists post
  val owned_state = #1 (strip_comb (find_term (fn tm =>
    let val (head,args) = strip_comb tm
    in is_abs head andalso length args = 4 end) body))
  val effects = ``tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
                    tnf.t_imm = tn.t_imm``
  val tm = mk_imp (entry, list_mk_exists (results,
    list_mk_conj (strip_conj body @ strip_conj effects)))
in
  val owned_decoder_state = owned_state
  val branch_frame_statement = list_mk_forall (free_vars tm, rhs (concl (DEPTH_CONV BETA_CONV tm)))
end

(* Replay the emitted LT and ISZERO up to the JNZ, then take that jump.
   Normalizing the comparison cursor does not change the jump's result. *)
Theorem observe_test_branch[local]:
  emit_op LT [Var counter; length] sa = (Var x,sb) /\
  emit_op ISZERO [Var x] sb = (Var y,sc) /\
  emit_inst JNZ [Var y; Label exit; Label body_lbl] [] sc = ((),sd) /\
  lookup_var counter s = SOME (n2w j) /\
  eval_operand length s = SOME (n2w n) /\ j <= n /\ n < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ fn_has_code sa sd obs ==>
  gas_path ctx obs s 0 (OK (jump_to (if j = n then exit else body_lbl)
    (update_var y (if j = n then 1w else 0w)
      (update_var x (if j < n then 1w else 0w) s))))
Proof
  strip_tac >>
  `cs_extends sa sb /\ cs_extends sb sc /\ cs_extends sc sd` by
    metis_tac[typed_copy_emit_op_mono, ci_mono_def, cs_extends_emit_inst] >>
  `fn_has_code sa sc obs /\ fn_has_code sc sd obs` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  qabbrev_tac `code = [mk_inst sa.cs_next_id LT [Var counter; length] [x];
                       mk_inst sb.cs_next_id ISZERO [Var x] [y]]` >>
  `sc.cs_current_bb = sa.cs_current_bb /\
   sc.cs_current_insts = sa.cs_current_insts ++ code` by
    gvs[Abbr `code`, emit_op_eq, APPEND_ASSOC] >>
  `sd.cs_blocks = sc.cs_blocks /\ sd.cs_current_bb = sc.cs_current_bb /\
   sd.cs_current_insts = sc.cs_current_insts ++
     [mk_inst sc.cs_next_id JNZ [Var y; Label exit; Label body_lbl] []]` by
    gvs[emit_inst_eq] >>
  `j < dimword (:256)` by decide_tac >>
  qabbrev_tac `v = update_var x (if j < n then 1w else 0w) s` >>
  `step_inst_base (mk_inst sa.cs_next_id LT [Var counter; length] [x]) s = OK v` by
    (`eval_operand (Var counter) s = SOME (n2w j)` by simp[eval_operand_def] >>
     mp_tac (Q.SPECL [`Var counter`, `length`, `n2w j`, `n2w n`,
                       `sa.cs_next_id`, `x`, `s`] step_LT) >>
     Cases_on `j < n` >>
     simp[Abbr `v`, w2n_n2w, arithmeticTheory.LESS_MOD, bool_to_word_def]) >>
  qabbrev_tac `u = update_var y (if j = n then 1w else 0w) v` >>
  `step_inst_base (mk_inst sb.cs_next_id ISZERO [Var x] [y]) v = OK u` by
    (`eval_operand (Var x) v = SOME (if j < n then 1w else 0w)` by
       simp[Abbr `v`, eval_operand_def, lookup_var_update_var] >>
     drule step_ISZERO >>
     disch_then (qspecl_then [`sb.cs_next_id`,`y`] mp_tac) >>
     Cases_on `j < n` >> gvs[Abbr `u`, bool_to_word_def]) >>
  `run_inst_seq code s = OK u` by simp[run_inst_seq_def, Abbr `code`] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
   LENGTH (FILTER (\i. i.inst_opcode = GAS) code) = 0` by
    simp[Abbr `code`, mk_inst_def, is_terminator_def] >>
  qabbrev_tac `q = u with vs_inst_idx := LENGTH sc.cs_current_insts` >>
  `gas_path ctx obs s 0 (OK q)` by
    (drule_all abi_decode_finite_success_observed >>
     disch_then (qspec_then `ctx` mp_tac) >> simp[Abbr `q`]) >>
  `gas_path ctx obs q 0 (OK (jump_to (if j = n then exit else body_lbl) q))` by
    (irule assert_jnz_zero_path >>
     conj_tac >- simp[Abbr `q`, Abbr `u`, Abbr `v`, update_var_def] >>
     qexistsl_tac [`Var y`,`sc`,`sd`] >>
     simp[Abbr `q`, Abbr `u`, Abbr `v`, eval_operand_def,
          lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `jump_to (if j = n then exit else body_lbl) q =
   jump_to (if j = n then exit else body_lbl) u` by simp[Abbr `q`, jump_to_def] >>
  `gas_path ctx obs s 0 (OK (jump_to (if j = n then exit else body_lbl) q))` by
    metis_tac[gas_path_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SIMP_RULE (srw_ss()) []] >>
  gvs[Abbr `u`, Abbr `v`]
QED

Theorem abi_decode_loop_owned_branch_frame_mods:
  ^branch_frame_statement
Proof
  rpt gen_tac >> strip_tac >>
  drule_all (typed_copy_origin_ptr_header_branch_path |> Q.GEN `D`) >>
  disch_then assume_tac >>
  first_assum (qspecl_then [`explicit`, `PG`,
    `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`]
    strip_assume_tac) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
       (s,G,tn) [] (OK t,Gf,tnf)` by
    (gen_tac >> first_x_assum (qspecl_then [`explicit`,`PG`,`D`] mp_tac) >>
     rpt strip_tac >> gvs[]) >>
  `sa.cs_next_var <= sb.cs_next_var /\
   sa.cs_next_var <= sd.cs_next_var /\ sa.cs_next_id <= sd.cs_next_id` by
    gvs[emit_op_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
        fresh_var_def, fresh_id_def, emit_def, comp_return_def] >>
  `!p. not_fresh_at sa p ==> p <> x /\ p <> y` by
    metis_tac[emit_op_old_var_separate, arithmeticTheory.LESS_EQ_REFL] >>
  qabbrev_tac `u = update_var y (if j = n then 1w else 0w)
      (update_var x (if j < n then 1w else 0w) s)` >>
  `t = jump_to (if j = n then exit else body_lbl) u` by simp[Abbr `u`] >>
  `alloca_history fn u` by
    (irule allocaHistoryTheory.alloca_history_frame >>
     qexists_tac `s` >> fs[Abbr `u`, update_var_def]) >>
  `state_frame u = state_frame (s with vs_inst_idx := u.vs_inst_idx)` by
    simp[Abbr `u`, update_var_def, state_frame_def] >>
  `!p. not_fresh_at sa p ==>
    lookup_var p u = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
    op_taint tnf (Var p) = op_taint tn (Var p)` by
    (simp[Abbr `u`, lookup_var_update_var] >> metis_tac[]) >>
  `(^owned_decoder_state) sd u Gf tnf` by
    (BETA_TAC >> irule (BETA_RULE abi_decode_owned_scalar_frame_with_history_lower) >>
     conj_tac >- (qexists_tac `inst` >> asm_rewrite_tac[]) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl_tac [`G`,`s`,`sa`,`tn`] >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC) >>
  `(^owned_decoder_state) sd t Gf tnf` by
    (qpat_assum `t = jump_to _ u` SUBST1_TAC >>
     irule abi_decode_loop_owned_jump_exact >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `(^owned_decoder_state) sd t Gf tnf` (assume_tac o BETA_RULE) >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >>
  conj_tac >-
    (qpat_x_assum `fn_has_code sa sd fn` kall_tac >>
     rpt strip_tac >>
     qpat_assum `lt = Var x` SUBST_ALL_TAC >>
     qpat_assum `done = Var y` SUBST_ALL_TAC >>
     drule_all observe_test_branch >> simp[Abbr `u`]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_labels = s.vs_labels` by
    simp[Abbr `u`, jump_to_def, update_var_def] >>
  `!p. not_fresh_at sa p ==>
    lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
    op_taint tnf (Var p) = op_taint tn (Var p)` by
    metis_tac[] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC
QED
