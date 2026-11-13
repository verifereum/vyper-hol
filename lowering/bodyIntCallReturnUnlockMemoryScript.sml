(* Memory return resources at the exact optional-release boundary. *)
Theory bodyIntCallReturnUnlockMemory
Ancestors
  bodyIntCallJointContract stmtSimReturnWiden ctorReturnFrame
  exprLoweringProps loweringPosts compileEnv loweringStateRelDefs exprSimStorageCopy
  stmtSimReturn venomState venomExecSemantics vyperState bodySim
  intCallReturnMem placeMemoryCopyEffect bodyIntCallSharpReturn

Theorem intcall_memory_unlock_exit_frame:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  fp.jc_rb = SOME (bw,cap) /\ fp.jc_root_ce.ce_returns_count = 0 /\
  copy_static t = copy_static s /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  (!off len. off + len <= w2n bw \/ w2n bw + cap <= off ==>
    mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) /\
  (!op. fp.jc_reserved op ==> eval_operand op t = eval_operand op s) /\
  val_in_memory fp.jc_ret_tv v (w2n bw) t.vs_memory ==>
  intcall_stmt_exit fp (INR (ReturnException v)) es
    (IntRet <|iret_values := []; iret_adopt_fmp := NONE|>
      (return_unlock_state fp.jc_root_ce t))
Proof
  strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx
     (es with scopes := []) s` by
    (fs[intcall_joint_res_def, intcall_expr_res_def, stmt_state_rel_def] >>
     conj_tac >- metis_tac[state_rel_scopes_nil] >>
     fs[immutable_alloca_sep_def, immutable_decl_sep_def, local_region_def, lookup_scopes_def] >>
     metis_tac[]) >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx
     (es with scopes := []) t` by
    (irule typed_return_empty_state_frame >>
     qexistsl_tac [`w2n bw`, `s`, `cap`] >>
     simp[arithmeticTheory.ADD_COMM] >>
     reverse conj_tac >- (fs[intcall_joint_res_def, intcall_expr_res_def] >> metis_tac[]) >>
     rpt strip_tac >>
     `eval_operand (Var x) t = eval_operand (Var x) s` by
       (first_x_assum irule >> fs[intcall_frame_ok_def, intcall_joint_res_def, intcall_expr_res_def,
         same_frame_def, compile_env_component_equality]) >>
     fs[eval_operand_def]) >>
  `state_rel fp.jc_func fp.jc_root_ce fp.jc_cx
     (es with scopes := []) t` by
    (irule (SRULE [] (Q.INST [`es` |-> `es with scopes := []`]
       constructor_exit_state_rel)) >> qexists_tac `ce` >>
     fs[intcall_joint_res_def, intcall_expr_res_def, stmt_state_rel_def]) >>
  simp[intcall_stmt_exit_def] >> disj2_tac >> conj_tac
  >- (simp[intret_q_def] >> qexists_tac `t` >>
      simp[result_rel_def, intret_vals_match_def, state_rel_gas_obs]) >>
  simp[eval_operand_return_unlock] >> conj_tac
  >- (rpt strip_tac >>
      `regions_disjoint a k (w2n bw) cap` by
        (fs[intcall_frame_ok_def] >> metis_tac[]) >>
      fs[regions_disjoint_def, intcall_joint_res_def, intcall_expr_res_def]) >>
  fs[intcall_joint_res_def, intcall_expr_res_def]
QED

(* Copies may traverse blocks, unlike the straight-line load frame. *)
Theorem return_unlock_control_frame:
  !ce s prev bb.
    (return_unlock_state ce s) with <|vs_prev_bb := prev; vs_current_bb := bb|> =
    return_unlock_state ce (s with <|vs_prev_bb := prev; vs_current_bb := bb|>)
Proof
  rpt gen_tac >> qabbrev_tac `info = ce.ce_nonreentrant` >> PairCases_on `info` >>
  Cases_on `info0` >> Cases_on `info2` >> Cases_on `info3` >>
  simp[return_unlock_state_def, tstore_def, sstore_def]
QED

Theorem copy_static_unlock_witness:
  copy_static t = copy_static (return_unlock_state ce s) /\
  LENGTH (return_unlock_insts ce id) <= t.vs_inst_idx ==>
  ?u. t = return_unlock_state ce u /\ copy_static u = copy_static s /\
      u.vs_memory = t.vs_memory /\ u.vs_vars = t.vs_vars
Proof
  strip_tac >>
  qexists_tac `s with <|vs_prev_bb := t.vs_prev_bb;
    vs_current_bb := t.vs_current_bb; vs_vars := t.vs_vars;
    vs_memory := t.vs_memory;
    vs_inst_idx := t.vs_inst_idx - LENGTH (return_unlock_insts ce id)|>` >>
  simp[copy_static_def] >>
  qspec_then `ce` (qspec_then `s` (qspecl_then [`t.vs_prev_bb`, `t.vs_current_bb`] mp_tac))
    return_unlock_control_frame >>
  drule return_unlock_memory_frame >>
  disch_then (qspecl_then [`s with <|vs_prev_bb := t.vs_prev_bb;
      vs_current_bb := t.vs_current_bb|>`, `t.vs_vars`, `t.vs_memory`] mp_tac) >>
  simp[] >> rpt strip_tac >>
  qpat_x_assum `_ with <|vs_memory := _; vs_vars := _; vs_inst_idx := _|> = _`
    (SUBST1_TAC o SYM) >>
  qpat_x_assum `_ with <|vs_prev_bb := _; vs_current_bb := _|> = _`
    (SUBST1_TAC o SYM) >>
  fs[copy_static_def, venom_state_component_equality]
QED
