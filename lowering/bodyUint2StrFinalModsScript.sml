Theory bodyUint2StrFinalMods
Ancestors
  bodyFullBuiltinUint2StrBlocks exprSimUint2Str bodyPtrDefs
  fragGasOriginPtrLoop fragGasSeqPtr bodyFullUnwrapSlotPost bodyFullUnwrapRun
  bodyFullHashKeccakFixed memSafeRun ptrDiscipline allocasBelowFmpUpdatesProps
  bodyMemBiUint2StrBlocks exprLoweringProps loweringStateRelDefs arithmetic
  venomState venomMemDefs venomInst finite_map pred_set list words

(* The real pointer floor applies to the path, not the ordinary ghost.
   The single store clears the header's taint; it cannot add taint below lo. *)
Theorem u2s_final_joint_mods:
  valid_horizon cx st0 H0 es.storage_trace /\
  not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!r len. cenv.ce_return_buf = SOME (PtrVar (Var r) len) ==> not_fresh_at a r) /\
  (!r len. cenv.ce_return_pc = SOME (PtrVar (Var r) len) ==> not_fresh_at a r) /\
  fn_inst_ids_distinct fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [q] /\
  not_local_ptr cenv es.scopes q /\ n+32 <= sz /\
  b+sz < dimword(:256) /\ lo <= b /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  u2s_digits a b n X 0 str s /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    u2s_safe H ctx fn cenv cx es a (Var p) b sz inst sr s /\
    ghost_inv_at (DF H) 0 d cenv cx es G tn s) /\
  ghost_kept_at lo cenv es a G0 tn0 s0 G tn /\
  FLOOKUP G p = SOME (b,sz) /\ op_taint tn (Var p) = {} /\
  FLOOKUP G (u2s_var a 1) = NONE /\ op_taint tn (Var (u2s_var a 1)) = {} /\
  (!j. b+n+32-LENGTH str <= j /\ j < b+n+32 ==> j NOTIN tn.t_mem) /\
  ~s.vs_halted /\
  lookup_block (u2s_label a 4) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 4; bb_instructions := u2s_final a (Var p) n|> /\
  s.vs_current_bb = u2s_label a 4 /\ s.vs_inst_idx = 0 ==>
  ?t G' tn'.
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,G',tn')) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      u2s_safe H ctx fn cenv cx es a (Var p) b sz inst sr t /\
      ghost_inv_at (DF H) 0 d cenv cx es G' tn' t) /\
    ghost_kept_at lo cenv es a G0 tn0 s0 G' tn' /\
    eval_operand (Var (u2s_var a 2)) t = SOME (n2w (b+n-LENGTH str)) /\
    val_in_memory ty (StringV str) (b+n-LENGTH str) t.vs_memory /\
    FLOOKUP G' (u2s_var a 2) = SOME (b,sz) /\
    op_taint tn' (Var (u2s_var a 2)) = {} /\
    (!j. b+n-LENGTH str <= j /\ j < b+n+32 ==> j NOTIN tn'.t_mem) /\
    (!i. i < lo /\ i IN tn'.t_mem ==> i IN tn.t_mem) /\
    t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0 /\ ~t.vs_halted
Proof
  strip_tac >>
  `u2s_safe H0 ctx fn cenv cx es a (Var p) b sz inst sr s` by metis_tac[] >>
  drule u2s_final_result >> simp[] >> disch_then drule_all >>
  disch_then (qspec_then `ty` strip_assume_tac) >>
  rename1 `run_inst_seq (TAKE 4 (u2s_final a (Var p) n)) s = OK t` >>
  `lookup_var p s = SOME (n2w b)` by fs[u2s_safe_def, eval_operand_def] >>
  `LENGTH str <= n /\ lookup_var (u2s_var a 1) s = SOME (n2w (LENGTH str))` by
    fs[u2s_digits_def] >>
  drule_all u2s_final_pointer_sequence >>
  disch_then (qspecl_then [`fn`, `PG`] strip_assume_tac) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
       u2s_safe H ctx fn cenv cx es a (Var p) b sz inst sr t` by
    (rpt strip_tac >>
     `u2s_safe H ctx fn cenv cx es a (Var p) b sz inst sr s` by metis_tac[] >>
     drule u2s_final_result >> simp[] >> disch_then drule_all >>
     disch_then (qspec_then `ty` strip_assume_tac) >> gvs[]) >>
  `t.vs_allocas = s.vs_allocas` by
    (fs[u2s_safe_def,u2s_frame_def] >>
     qpat_assum `t with <|vs_memory := _; vs_vars := _; vs_prev_bb := _;
                          vs_current_bb := _; vs_inst_idx := _|> = sr`
       (mp_tac o Q.AP_TERM `\z. z.vs_allocas`) >>
     qpat_assum `s with <|vs_memory := _; vs_vars := _; vs_prev_bb := _;
                          vs_current_bb := _; vs_inst_idx := _|> = sr`
       (mp_tac o Q.AP_TERM `\z. z.vs_allocas`) >> simp[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (jump_to (u2s_label a 5) t),G',tn')` by suspend "path" >>
  qexistsl_tac [`jump_to (u2s_label a 5) t`, `G'`, `tn'`] >>
  conj_tac >- simp[] >>
  conj_tac >- suspend "ghost" >>
  suspend "observations"
QED

Resume u2s_final_joint_mods[path]:
  `run_inst_seq_mem_ok (TAKE 4 (u2s_final a (Var p) n)) s` by
    (irule u2s_final_mem_ok >> fs[u2s_safe_def, eval_operand_def] >>
     `b+sz <= s.vs_alloca_next` by
       (fs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
     simp[word_add_n2w, GSYM n2w_sub, w2n_n2w] >> decide_tac) >>
  gen_tac >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (t with vs_inst_idx := 4),G',tn')` by
    (`lookup_block s.vs_current_bb fn.fn_blocks =
       SOME <|bb_label := u2s_label a 4; bb_instructions := u2s_final a (Var p) n|>` by simp[] >>
     drule_at (Pat `lookup_block _ _ = SOME _`) run_inst_seq_gas_origin_ptr_path >>
     disch_then (drule_at (Pat `run_inst_seq _ _ = OK _`)) >>
     `inst_seq_ptr D lo ctx fn PG G tn (TAKE 4 (u2s_final a (Var p) n)) s G' tn'` by simp[] >>
     disch_then (drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)) >>
     disch_then (qspec_then `explicit` mp_tac) >>
     simp[u2s_final_def, u2s_inst_def, mk_inst_def, is_terminator_def] >>
     impl_tac
     >- (rpt strip_tac >> irule dalloca_no_wrap_non_dalloca >>
         qpat_x_assum `_ = pre ++ [i] ++ post`
           (mp_tac o Q.AP_TERM `EVERY (\j. j.inst_opcode <> DALLOCA)`) >>
         simp[EVERY_APPEND]) >>
     simp[]) >>
  `stmt_state_rel H0 ctx fn cenv cx es t` by fs[u2s_safe_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp (t with vs_inst_idx := 4)` by
    (simp[allocas_below_fmp_updates] >>
     qpat_assum `stmt_state_rel H0 _ _ _ _ _ t`
       (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp)) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (t with vs_inst_idx := 4,G',tn') [] (OK (jump_to (u2s_label a 5) t),G',tn')` by
    (`jump_to (u2s_label a 5) (t with vs_inst_idx := 4) =
      jump_to (u2s_label a 5) t` by simp[jump_to_def] >>
     pop_assum (fn th => once_rewrite_tac [GSYM th]) >>
     irule jmp_origin_ptr_path >>
     simp[u2s_final_def,u2s_inst_def,mk_inst_def,get_instruction_def,allocas_from_def] >>
     fs[allocas_from_def]) >>
  metis_tac[gas_origin_ptr_path_trans]
QED

Resume u2s_final_joint_mods[ghost]:
  rpt strip_tac >- metis_tac[u2s_safe_jump] >>
  `ghost_inv_at (DF H) 0 d cenv cx es G tn s` by metis_tac[] >>
  irule unwrap_slot_copy_ghost_inv_at >>
  conj_tac
  >- (fs[u2s_safe_def,u2s_frame_def,venom_state_component_equality,
         ghost_inv_at_def,jump_to_def] >> metis_tac[]) >>
  conj_tac >- simp[allocas_from_def] >>
  conj_tac
  >- fs[ghost_inv_at_def,stor_taint_ok_at_def,u2s_safe_def,
        u2s_frame_def,venom_state_component_equality,jump_to_def] >>
  qexistsl_tac [`G`,`fn`,`sz`,`s`,`a`,`b`,`tn`] >>
  fs[u2s_safe_def,u2s_frame_def,jump_to_def,lookup_var_def,stmt_state_rel_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[ADD_COMM] >>
  fs[state_rel_def] >> rpt strip_tac >> decide_tac
QED

Resume u2s_final_joint_mods[observations]:
  conj_tac
  >- (irule ghost_kept_at_clean_suffix >>
      qexistsl_tac [`G`, `tn`] >> simp[SUBSET_DEF]) >>
  fs[jump_to_def,eval_operand_def,lookup_var_def] >>
  rpt strip_tac >>
  Cases_on `b+n+32-LENGTH str <= j`
  >- (disj1_tac >> first_x_assum irule >> decide_tac) >>
  decide_tac
QED

Finalise u2s_final_joint_mods
