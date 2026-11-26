(* The selected callee loads its stack-return members from one covered
   tuple before executing RET. The machine path is independent of the
   source module and uses one endpoint for all dead masks. *)
Theory bodySelectedStackReturnRunMods
Ancestors
  stmtSimReturn bodyFullAssignTuple decoderGhostFramePtr freshWrites
  stateFrame ptrDiscipline vyperTyping list rich_list words venomState
  tupleLoadProps fragGasOriginPtr exprLoweringProps marker

Theorem selected_stack_eval_operands[local]:
  !ops vals s.
    LIST_REL (\op v. eval_operand op s = SOME v) ops vals ==>
    eval_operands ops s = SOME vals
Proof
  Induct >> Cases >> simp[eval_operands_def] >> rw[] >>
  first_x_assum drule >> simp[]
QED

Theorem selected_stack_loaded_words[local]:
  EVERY is_word_type tys /\ LENGTH elems = LENGTH tys /\
  LENGTH tys = LENGTH tvs /\ LENGTH tvs = LENGTH vs /\
  (!i. i < LENGTH tys ==>
    ?x. EL i elems = Var x /\ op_taint tf (Var x) = {} /\
      (is_word_type (EL i tys) ==>
       lookup_var x t = SOME (typed_val_to_w256 (EL i tvs) (EL i vs)))) ==>
  eval_operands elems t =
    SOME (MAP (\(tv,v). typed_val_to_w256 tv v) (ZIP (tvs,vs))) /\
  EVERY (\op. op_taint tf op = {}) elems
Proof
  simp[EVERY_EL] >> strip_tac >>
  `!i. i < LENGTH elems ==>
     eval_operand (EL i elems) t = SOME (typed_val_to_w256 (EL i tvs) (EL i vs)) /\
     op_taint tf (EL i elems) = {}` by
    (gen_tac >> strip_tac >>
     `i < LENGTH tys` by decide_tac >>
     `is_word_type (EL i tys)` by (first_assum irule >> simp[]) >>
     qpat_assum `!i. _ ==> ?x. _` (drule_then strip_assume_tac) >>
     simp[eval_operand_def]) >>
  conj_tac >-
    (irule selected_stack_eval_operands >>
     simp[LIST_REL_EL_EQN,LENGTH_ZIP,EL_MAP,EL_ZIP]) >>
  metis_tac[]
QED

Theorem selected_stack_load_ret[local]:
  compile_tuple_load_all cenv (Var root) tys 0 sa = (elems,sb) /\
  emit_inst RET (elems ++ [Var rpc]) [] sb = ((),sc) /\
  EVERY is_word_type tys /\
  cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  cenv.ce_return_buf = NONE /\
  not_fresh_at sa rpc /\ lookup_var rpc s = SOME pc /\
  op_taint tn (Var rpc) = {} /\
  not_fresh_at sa root /\ lookup_var root s = SOME w /\
  ptr_covers G tn root s capacity /\ type_memory_size_list tvs <= capacity /\
  w2n w + capacity < dimword (:256) /\ w2n w + capacity <= s.vs_alloca_next /\
  LIST_REL (\ty tv. evaluate_type (get_tenv cx) ty = SOME tv) tys tvs /\
  LIST_REL (\ty tv. type_memory_bytes cenv ty = type_memory_size tv) tys tvs /\
  values_have_types tvs vs /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    tuple_in_memory vs tvs (w2n w) mem) /\
  local_ptrs_reserved cenv sa /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ fn_has_code sb sc func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (IntRet <|iret_values := MAP (\(tv,v). typed_val_to_w256 tv v) (ZIP (tvs,vs));
                iret_adopt_fmp := NONE|> t,Gf,tf)) /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
    s.vs_inst_idx <= t.vs_inst_idx /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  mp_tac (Q.INST [`off` |-> `0`] body_assign_tuple_load_all_path) >>
  impl_tac >- simp[] >> strip_tac >>
  `t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|>` by
    (qpat_assum `state_frame t = _`
       (mp_tac o Q.AP_TERM `\s. s with vs_vars := t.vs_vars` o
         REWRITE_RULE [state_frame_eq_reconstruct]) >> simp[]) >>
  `LENGTH tys = LENGTH tvs /\ LENGTH tvs = LENGTH vs` by
    metis_tac[LIST_REL_LENGTH,values_have_types_length] >>
  qabbrev_tac `vals = MAP (\(tv,v). typed_val_to_w256 tv v) (ZIP (tvs,vs))` >>
  `eval_operands elems t = SOME vals /\ EVERY (\op. op_taint tf op = {}) elems` by
    (simp[Abbr `vals`] >> irule selected_stack_loaded_words >>
     simp[] >> qexists_tac `tys` >> simp[] >> rpt strip_tac >>
     `i < LENGTH tys` by decide_tac >>
     qpat_assum `!i. _ ==> ?x. _` (drule_then strip_assume_tac) >>
     qexists_tac `x` >> Cases_on `is_word_type (EL i tys)` >> fs[]) >>
  `lookup_var rpc t = SOME pc /\ op_taint tf (Var rpc) = {}` by
    (qpat_assum `!x. not_fresh_at sa x ==> _` (qspec_then `rpc` mp_tac) >> simp[]) >>
  `allocas_from lo t` by
    (rewrite_tac[allocas_from_def] >>
     qpat_assum `t.vs_allocas = s.vs_allocas` (rewrite_tac o single) >>
     qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (qpat_assum `t = s with <|vs_vars := _; vs_inst_idx := _|>`
       (once_rewrite_tac o single) >> simp[allocas_below_fmp_def] >>
     fs[allocas_below_fmp_def]) >>
  `s.vs_inst_idx <= t.vs_inst_idx` by
    (drule compile_tuple_load_all_values >>
     disch_then (qspecl_then [`s`,`w`] mp_tac) >> simp[eval_operand_def]) >>
  qexistsl_tac [`t`,`Gf`,`tf`] >>
  reverse conj_tac >-
    (simp[] >> rpt strip_tac >> first_x_assum drule >> simp[]) >>
  qpat_assum `Abbrev (vals = _)` (SUBST1_TAC o SYM o REWRITE_RULE [Abbrev_def]) >>
  gen_tac >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,Gf,tf) []
     (IntRet <|iret_values := vals; iret_adopt_fmp := NONE|> t,Gf,tf)` by
    (irule emitted_ret_origin_ptr >> simp[] >>
     qexistsl [`elems`,`pc`,`rpc`,`sb`,`sc`] >> simp[EVERY_APPEND]) >>
  metis_tac[gas_origin_ptr_path_append,APPEND_NIL]
QED

Theorem selected_stack_return_run_mods:
  compile_return_unlock cenv sm = ((),su) /\
  compile_tuple_load_all cenv (Var root) tys 0 su = (elems,sl) /\
  emit_inst RET (elems ++ [Var rpc]) [] sl = ((),sb) /\
  fn_has_code sm su func /\ fn_has_code su sl func /\ fn_has_code sl sb func /\
  EVERY is_word_type tys /\
  cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\ cenv.ce_return_buf = NONE /\
  not_fresh_at sm rpc /\ lookup_var rpc s = SOME pc /\ op_taint tn (Var rpc) = {} /\
  not_fresh_at sm root /\ lookup_var root s = SOME w /\
  ptr_covers G tn root s capacity /\ type_memory_size_list tvs <= capacity /\
  w2n w + capacity < dimword (:256) /\ w2n w + capacity <= s.vs_alloca_next /\
  LIST_REL (\ty tv. evaluate_type (get_tenv cx) ty = SOME tv) tys tvs /\
  LIST_REL (\ty tv. type_memory_bytes cenv ty = type_memory_size tv) tys tvs /\
  values_have_types tvs vs /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    tuple_in_memory vs tvs (w2n w) mem) /\
  local_ptrs_reserved cenv sm /\
  ((FST cenv.ce_nonreentrant /\ ~SND (SND (SND cenv.ce_nonreentrant))) ==>
     ~s.vs_call_ctx.cc_static) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (IntRet <|iret_values := MAP (\(tv,v). typed_val_to_w256 tv v) (ZIP (tvs,vs));
                iret_adopt_fmp := NONE|> t,Gf,tf)) /\
    t = (return_unlock_state cenv s) with
      <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
    LENGTH (return_unlock_insts cenv sm.cs_next_id) <= t.vs_inst_idx /\
    tf.t_mem = tn.t_mem /\
    (((FST cenv.ce_nonreentrant /\ ~SND (SND (SND cenv.ce_nonreentrant))) ==>
       FST (SND (SND cenv.ce_nonreentrant))) ==>
      tf.t_stor = tn.t_stor /\ tf.t_trans SUBSET tn.t_trans /\
      tf.t_imm = tn.t_imm) /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  mp_tac (Q.INST [`sa` |-> `sm`] (SPEC_ALL return_unlock_origin_ptr_taint)) >>
  impl_tac >- simp[] >> strip_tac >>
  drule compile_return_unlock_shape >> strip_tac >>
  qabbrev_tac `s1 = return_unlock_state cenv s` >>
  `s1.vs_alloca_next = s.vs_alloca_next` by
    (simp[Abbr `s1`] >>
     qabbrev_tac `info = cenv.ce_nonreentrant` >> PairCases_on `info` >>
     Cases_on `info0` >> Cases_on `info2` >> Cases_on `info3` >>
     simp[return_unlock_state_def, tstore_def, sstore_def]) >>
  `!x. lookup_var x s1 = lookup_var x s` by simp[Abbr `s1`, lookup_var_def] >>
  `allocas_from lo s1 /\ ~s1.vs_halted /\
    s1.vs_current_bb = su.cs_current_bb /\
    s1.vs_inst_idx = LENGTH su.cs_current_insts` by
    (qspecl_then [`cenv`,`s`,`sm.cs_next_id`] strip_assume_tac
       return_unlock_state_frames >>
     simp[Abbr `s1`, allocas_from_def] >> fs[allocas_from_def]) >>
  `ptr_covers G tn' root s1 capacity` by
    (irule ptr_covers_frame >> qexistsl [`G`,`s`,`tn`] >> simp[op_taint_def]) >>
  `!x. not_fresh_at sm x ==> not_fresh_at su x` by
    simp[loweringStateRelDefsTheory.not_fresh_at_def] >>
  `local_ptrs_reserved cenv su` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sm` >> simp[]) >>
  mp_tac (Q.INST [`sa` |-> `su`, `sb` |-> `sl`, `sc` |-> `sb`,
    `s` |-> `s1`, `tn` |-> `tn'`] selected_stack_load_ret) >>
  impl_tac >- fs[Abbr `s1`, op_taint_def] >> strip_tac >>
  qexistsl [`t`,`Gf`,`tf`] >>
  conj_tac >- metis_tac[gas_origin_ptr_path_append,APPEND_NIL] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qpat_assum `s1.vs_inst_idx = LENGTH su.cs_current_insts`
        (fn idx => qpat_assum `su.cs_current_insts = _`
          (fn code => assume_tac (SIMP_RULE (srw_ss()) [code] idx))) >>
      decide_tac) >>
  conj_tac >- simp[] >>
  conj_tac >- metis_tac[pred_setTheory.SUBSET_TRANS] >>
  rpt strip_tac >>
  `not_fresh_at su x` by simp[] >>
  metis_tac[]
QED
