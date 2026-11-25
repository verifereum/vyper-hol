(* The fixed-byte SHA suffix at the reached argument's horizon. *)
Theory bodyShaFixedMachineMods
Ancestors
  bodyFullHashShaFixedSuccess bodyFullHashShaFixedAbort
  bodyMemBiSha256Compose bodyMethodIdScratchFrameMods bodyFullPostsMods
  bodyFullShadowBodyInv fragGasSeqMem fragGasSeqPtr venomState venomInst
  loweringStateRelDefs loweringPosts vyperCallOutcome words list
  instSeqPtrLo exprSimHash exprSimWordArgs exprOperandVar exprLoweringProps
  vyperValue vyperTyping vyperTypeSystem builtinHashing freshWrites
  bodyPtrDefs fragExec rich_list pred_set compileEnv

Theorem sha_fixed_ptr_restore[local]:
  ghost_inv_at_mods D lo d cenv cx mid G tn s /\
  inst_seq_ptr D 0 ctx func PG G tn code s Gf tf ==>
  inst_seq_ptr D lo ctx func PG G tn code s Gf tf
Proof
  strip_tac >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by
    fs[ghost_inv_at_mods_def] >>
  irule inst_seq_ptr_zero_to_lo >> simp[] >> qexists_tac `D` >> simp[]
QED

Theorem sha_fixed_machine_mods:
  expr_type e = BaseT (BytesT (Fixed m)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Fixed m))) /\
  value_has_type (BaseTV (BytesT (Fixed m))) (BytesV bs) /\
  expr_post_mods (H:(bool # bytes32 # type_value) list # num list)
    ctx func cenv cx e es sa sm s0 mid (BytesV bs) x s /\
  ptr_val_ok cx (post_value_type cenv e) (BytesV bs) x G tn s /\
  expr_store_bound cx (expr_type e) (BytesV bs) x s /\
  ghost_inv_at_mods (DF H) lo d cenv cx mid G tn s /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_sha256_bytesm x m sm = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (!v k. cenv.ce_return_buf = SOME (PtrVar (Var v) k) ==> not_fresh_at sa v) /\
  (!v k. cenv.ce_return_pc = SOME (PtrVar (Var v) k) ==> not_fresh_at sa v) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  run_inst_seq_mem_ok (emitted_insts sm sb) s /\
  ?r Gf tf. run_inst_seq (emitted_insts sm sb) s = r /\
    inst_seq_ptr (DF H) lo ctx func PG G tn (emitted_insts sm sb) s Gf tf /\
    if (?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success) then
      ?z outcome rest. r = OK z /\
        s.vs_outcomes = outcome::rest /\ outcome.co_success /\
        eval_operand op z = SOME (SHA_256_bytes bs) /\
        ghost_inv_at (DF H) 0 d cenv cx (mid with outcomes := SOME rest) Gf tf
          (z with vs_inst_idx := s.vs_inst_idx+7) /\
        ghost_kept_at 0 cenv mid sm G tn s Gf tf /\
        op_taint tf op = {} /\ op_prov Gf op = NONE /\
        stmt_state_rel H ctx func cenv cx
          (SND (take_call_outcome NONE 2w bs NONE mid)) z /\
        (!v. not_fresh_at sm v ==> lookup_var v z = lookup_var v s) /\
        pure_frame cenv func mid sm s z
    else
      ?z. r = Abort (if s.vs_outcomes = [] then ExHalt_abort else Revert_abort) z
Proof
  strip_tac >>
  qhdtm_x_assum `expr_post_mods`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  `m <= 32` by
    (qpat_x_assum `evaluate_type _ _ = _` mp_tac >>
     simp[vyperValueTheory.evaluate_type_def, AllCaseEqs()]) >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Fixed m)))` by
    simp[vyperValueTheory.evaluate_type_def] >>
  drule_all_then strip_assume_tac hash_fixed_post_view >>
  drule_then assume_tac expr_post_state >>
  drule_then (drule_then assume_tac) compile_lower_value_var >>
  drule_then strip_assume_tac (cj 2 compile_expr_grows) >>
  `local_ptrs_reserved cenv sm` by (irule local_ptrs_reserved_next_var >>
    qexists_tac `sa` >> simp[]) >>
  `(!v k. cenv.ce_return_buf = SOME (PtrVar (Var v) k) ==> not_fresh_at sm v) /\
   (!v k. cenv.ce_return_pc = SOME (PtrVar (Var v) k) ==> not_fresh_at sm v)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  drule_all_then strip_assume_tac (SRULE [] (Q.INST [`sha` |-> `T`] hash_fixed_alloca_code)) >>
  `op_taint tn x = {}` by fs[ptr_val_ok_def] >>
  `ghost_inv_at (DF H) 0 d cenv cx mid G tn s` by
    (drule_then ACCEPT_TAC method_id_ghost_at_zero) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (`sb.cs_current_bb = sm.cs_current_bb /\
      sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb` by
       (qpat_assum `compile_sha256_bytesm _ _ _ = _` mp_tac >>
        rpt (pop_assum kall_tac) >> metis_tac[hash_buffer_suffix_shape, same_blocks_def]) >>
     qpat_x_assum `fn_has_code sm sb func` mp_tac >> simp[fn_has_code_def] >>
     strip_tac >> qexists_tac `bb` >>
     fs[IS_PREFIX_APPEND] >> pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
     simp[IS_PREFIX_APPEND]) >>
  conj_tac
  >- (`is_bytes_or_string_type (expr_type e)` by simp[is_bytes_or_string_type_def] >>
      ` (if is_bytestring_type (expr_type e) then compile_sha256_bytes x sm
         else case expr_type e of
           BaseT (BytesT (Fixed n)) => compile_sha256_bytesm x n sm
         | _ => compile_sha256_word x sm) = (op,sb)` by simp[is_bytestring_type_def] >>
      drule_all_then ACCEPT_TAC sha256_typed_suffix_mem_ok) >>
  Cases_on `?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success`
  >- (qpat_assum `?outcome rest. _` strip_assume_tac >>
      `TAKE m (word_to_bytes_be w) = bs` by
        (qpat_x_assum `TAKE (LENGTH bs) _ = bs` mp_tac >> simp[]) >>
      drule_all sha_fixed_success_frame_at >>
      disch_then (qspec_then `PG` strip_assume_tac) >>
      qpat_x_assum `LENGTH bs = m` (SUBST_ALL_TAC o SYM) >>
      drule_all_then strip_assume_tac compile_sha256_bytesm_frame >>
      `t' = t` by
        (qpat_x_assum `run_inst_seq _ _ = OK t'` mp_tac >> simp[]) >>
      qpat_x_assum `t' = t` SUBST_ALL_TAC >>
      qexistsl_tac [`OK t`, `Gf`, `tf`] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- (drule_all_then ACCEPT_TAC sha_fixed_ptr_restore) >>
      qpat_x_assum `s.vs_inst_idx = _` kall_tac >> asm_rewrite_tac[] >>
      qexistsl_tac [`t`, `outcome`, `rest`] >> simp[]) >>
  drule_all sha_fixed_abort_ptr_at >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`Abort (if s.vs_outcomes = [] then ExHalt_abort else Revert_abort) t`, `Gf`, `tf`] >>
  simp[] >> drule_all_then ACCEPT_TAC sha_fixed_ptr_restore
QED
