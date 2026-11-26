(* The zero block on the actual allocation-floor path, with the linked
   caller's zero-floor ghost and a separate low-memory taint observation. *)
Theory bodyUint2StrZeroMods
Ancestors
  bodyFullBuiltinUint2StrBlocks bodyMemBiUint2StrBlocks exprSimUint2Str
  bodyPtrDefs bodyFullUnwrapRun bodyFullUnwrapSlotFrame bodyFullHashKeccakFixed
  fragGasSeqPtr fragGasOriginPtrLoop exprLoweringProps venomInst venomState
  venomMemDefs loweringStateRelDefs ptrDiscipline words finite_map list pred_set

Theorem u2s_zero_joint_mods:
  valid_horizon cx st0 H0 es.storage_trace /\
  not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!r len. cenv.ce_return_buf = SOME (PtrVar (Var r) len) ==> not_fresh_at a r) /\
  (!r len. cenv.ce_return_pc = SOME (PtrVar (Var r) len) ==> not_fresh_at a r) /\
  fn_inst_ids_distinct fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [q] /\
  not_local_ptr cenv es.scopes q /\ 1 <= n /\ n+32 <= sz /\
  b+sz < dimword(:256) /\ lo <= b /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       u2s_safe H ctx fn cenv cx es a (Var p) b sz inst sr s /\
       ghost_inv_at (DF H) 0 d cenv cx es G tn s) /\
  ghost_kept_at lo cenv es a G0 tn0 s0 G tn /\
  FLOOKUP G p = SOME (b,sz) /\ op_taint tn (Var p) = {} /\
  ~s.vs_halted /\
  lookup_block (u2s_label a 3) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 3; bb_instructions := u2s_zero a (Var p) n|> /\
  s.vs_current_bb = u2s_label a 3 /\ s.vs_inst_idx = 0 ==>
  ?t G' tn'.
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,G',tn')) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
       u2s_safe H ctx fn cenv cx es a (Var p) b sz inst sr t /\
       ghost_inv_at (DF H) 0 d cenv cx es G' tn' t) /\
    ghost_kept_at lo cenv es a G0 tn0 s0 G' tn' /\
    eval_operand (Var (u2s_var a 2)) t = SOME (n2w (b+n-1)) /\
    val_in_memory ty (StringV "0") (b+n-1) t.vs_memory /\
    FLOOKUP G' (u2s_var a 2) = SOME (b,sz) /\
    op_taint tn' (Var (u2s_var a 2)) = {} /\
    (!j. b+n-1 <= j /\ j < b+n+32 ==> j NOTIN tn'.t_mem) /\
    t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    (!i. i < lo /\ i IN tn'.t_mem ==> i IN tn.t_mem)
Proof
  strip_tac >>
  `u2s_safe H0 ctx fn cenv cx es a (Var p) b sz inst sr s` by metis_tac[] >>
  drule u2s_zero_result >> simp[] >> disch_then drule_all >>
  disch_then (qspec_then `ty` strip_assume_tac) >>
  rename1 `run_inst_seq (TAKE 6 (u2s_zero a (Var p) n)) s = OK t` >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
       u2s_safe H ctx fn cenv cx es a (Var p) b sz inst sr t` by
    (rpt strip_tac >>
     `u2s_safe H ctx fn cenv cx es a (Var p) b sz inst sr s` by metis_tac[] >>
     drule u2s_zero_result >> simp[] >> disch_then drule_all >> strip_tac >> gvs[]) >>
  `lookup_var p s = SOME (n2w b)` by fs[u2s_safe_def, eval_operand_def] >>
  drule_all u2s_zero_pointer_sequence >>
  disch_then (qspecl_then [`fn`, `PG`] strip_assume_tac) >>
  `tn'.t_mem SUBSET tn.t_mem` by simp[SUBSET_DEF] >>
  qexistsl_tac [`jump_to (u2s_label a 5) t`, `G'`, `tn'`] >>
  conj_tac >- suspend "path" >>
  conj_tac >- suspend "ghost" >>
  conj_tac
  >- (irule ghost_kept_at_clean_suffix >> qexistsl_tac [`G`, `tn`] >> simp[]) >>
  fs[jump_to_def, eval_operand_def, lookup_var_def, SUBSET_DEF] >>
  rpt strip_tac >> decide_tac
QED

Resume u2s_zero_joint_mods[path]:
  `run_inst_seq_mem_ok (TAKE 6 (u2s_zero a (Var p) n)) s` by
    (irule u2s_zero_mem_ok >>
     fs[u2s_safe_def, eval_operand_def] >>
     `b+sz <= s.vs_alloca_next` by
       (fs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
     simp[word_add_n2w, GSYM n2w_sub, w2n_n2w] >> decide_tac) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
          (OK (t with vs_inst_idx := 6),G',tn')` by
    (gen_tac >> qspecl_then [`TAKE 6 (u2s_zero a (Var p) n)`, `s`, `t`]
       mp_tac run_inst_seq_gas_origin_ptr_path >>
     disch_then (qspecl_then [`G`, `tn`, `G'`, `tn'`] mp_tac) >>
     disch_then (qspecl_then [`ctx`, `fn`,
       `<|bb_label := u2s_label a 3; bb_instructions := u2s_zero a (Var p) n|>`] mp_tac) >>
     simp[u2s_zero_def, u2s_inst_def, mk_inst_def, is_terminator_def] >>
     impl_tac
     >- (rpt strip_tac >> irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
         qpat_x_assum `_ = pre ++ [i] ++ post`
           (mp_tac o Q.AP_TERM `EVERY (\j. j.inst_opcode <> DALLOCA)`) >>
         simp[EVERY_APPEND]) >>
     simp[]) >>
  `t.vs_allocas = s.vs_allocas` by
    (fs[u2s_safe_def, u2s_frame_def] >>
     ntac 2 (qpat_x_assum `_ = sr` (mp_tac o Q.AP_TERM `\z. z.vs_allocas`)) >>
     simp[]) >>
  `stmt_state_rel H0 ctx fn cenv cx es t` by fs[u2s_safe_def] >>
  drule bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >> strip_tac >>
  rpt strip_tac >> irule gas_origin_ptr_path_trans >>
  qexistsl_tac [`G'`, `t with vs_inst_idx := 6`, `tn'`] >> simp[] >>
  `jump_to (u2s_label a 5) (t with vs_inst_idx := 6) =
   jump_to (u2s_label a 5) t` by simp[jump_to_def] >>
  pop_assum (fn th => once_rewrite_tac [GSYM th]) >>
  `allocas_from lo (t with vs_inst_idx := 6)` by
    (qpat_assum `allocas_from lo s` mp_tac >>
     pure_rewrite_tac[allocas_from_def] >> simp[]) >>
  irule jmp_origin_ptr_path >>
  simp[u2s_zero_def, u2s_inst_def, mk_inst_def, get_instruction_def,
       allocasBelowFmpUpdatesPropsTheory.allocas_below_fmp_updates]
QED

Resume u2s_zero_joint_mods[ghost]:
  rpt strip_tac
  >- metis_tac[u2s_safe_jump] >>
  `ghost_inv_at (DF H) 0 d cenv cx es G tn s` by metis_tac[] >>
  irule unwrap_slot_copy_ghost_inv_at_mono >>
  simp[allocas_from_def] >>
  conj_tac
  >- fs[ghost_inv_at_def, stor_taint_ok_at_def, u2s_safe_def,
        u2s_frame_def, venom_state_component_equality, jump_to_def] >>
  qexistsl_tac [`G`, `fn`, `sz`, `s`, `a`, `b`, `tn`] >>
  fs[u2s_safe_def, u2s_frame_def, jump_to_def, lookup_var_def, stmt_state_rel_def, SUBSET_DEF] >>
  conj_tac >- (qpat_assum `!name lb lsz. local_region cenv es.scopes s name lb lsz ==> _` ACCEPT_TAC) >>
  conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
  qpat_assum `state_rel H0 fn cenv cx es s` (mp_tac o REWRITE_RULE [state_rel_def]) >> simp[]
QED

Finalise u2s_zero_joint_mods
