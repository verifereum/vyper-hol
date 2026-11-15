(* Element-copy entry of the local DynArray loop: the three-instruction
   prefix that skips the length word, then the copy into the loop variable,
   stated as the copy-entry callback of the shared array loop. *)
Theory bodyIntCallFamStmtForDynArrayEntry
Ancestors
  bodyIntCallFamStmtForArrayFrame bodyIntCallFamStmtForArrayResources
  whitelistForIterDynLoop bodyIntCallJointContract
  bodyIntCallFamStmtForResources bodyIntCallFamStmtForFrontier
  bodyIntCallFamStmtForTransport bodyIntCallJointStmtJump
  stmtSimForArray stmtSimForArrayLoop stmtSimProps exprLoweringProps
  compileEnv loweringStateRelDefs venomState venomExecSemantics venomInst
  intCallFrame fragGasMode finite_map words list rich_list

Theorem intcall_dynarray_prefix_frame[local]:
  !j3 j4 j5.
  compile_iter_elem_copy ce (Var ep) (Var p) stride LocMemory F et et sa = ((),sb) /\
  stride = type_memory_size tv /\ type_memory_bytes ce et = stride /\
  evaluate_type tenv et = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  val_in_memory tv v (w2n arrbase + 32 + k * stride) s.vs_memory /\
  w2n arrbase + 32 + k * stride < dimword (:256) /\ stride + 64 < dimword (:256) /\
  lookup_var idx s = SOME (n2w k) /\ eval_operand saved s = SOME arrbase /\
  lookup_var p s = SOME dst /\ p <> ov /\ p <> tot /\ p <> ep /\ ov <> tot /\
  (!x. saved = Var x ==> x <> ov /\ x <> tot) /\
  not_fresh_at sa ep /\ not_fresh_at sa p ==>
  ?t. run_inst_seq
       ([mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
         mk_inst j4 ADD [Lit 32w; Var ov] [tot];
         mk_inst j5 ADD [saved; Var tot] [ep]] ++ emitted_insts sa sb) s = OK t /\
      (!a len. a + len <= w2n dst \/ w2n dst + stride <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `s2 = update_var ep (n2w (w2n arrbase + 32 + k * stride))
                      (update_var tot (n2w (32 + k * stride))
                        (update_var ov (n2w (k * stride)) s))` >>
  `run_inst_seq [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
                 mk_inst j4 ADD [Lit 32w; Var ov] [tot];
                 mk_inst j5 ADD [saved; Var tot] [ep]] s = OK s2` by
    (qunabbrev_tac `s2` >>
     mp_tac (Q.SPECL [`s`, `idx`, `saved`, `arrbase`, `k`, `stride`, `ov`,
       `tot`, `ep`, `j3`, `j4`, `j5`] dynarray_address_prefix_run) >>
     simp[]) >>
  `eval_operand (Var ep) s2 = SOME (n2w (w2n arrbase + 32 + k * stride)) /\
   eval_operand (Var p) s2 = SOME dst /\ s2.vs_memory = s.vs_memory` by
    fs[Abbr `s2`, eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE] >>
  drule array_iter_copy_run >>
  disch_then (qspecl_then [`s2`, `tenv`, `tv`, `v`,
    `n2w (w2n arrbase + 32 + k * stride)`, `dst`] mp_tac) >>
  (impl_tac >- gvs[]) >> strip_tac >>
  qexists_tac `t` >> conj_tac
  >- (qpat_x_assum `run_inst_seq [_; _; _] _ = _`
        (mp_then Any mp_tac run_inst_seq_append) >>
      disch_then (qspec_then `emitted_insts sa sb` mp_tac) >> gvs[]) >>
  qpat_x_assum `!a len. _ ==> mem_bytes_at _ _ t.vs_memory = _` mp_tac >>
  simp[]
QED

Theorem intcall_dynarray_body_entry_run_frame[local]:
  !j3 j4 j5.
  compile_iter_elem_copy cenv (Var ep) (Var p) stride LocMemory F et et sa = ((),sb0) /\
  stride = type_memory_size tv /\ type_memory_bytes cenv et = stride /\
  evaluate_type tenv et = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  val_in_memory tv v (w2n arr_base + 32 + k * stride) s.vs_memory /\
  w2n arr_base + 32 + k * stride < dimword (:256) /\ stride + 64 < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\
  cenv_top_ext cenv bc (FEMPTY :: es.scopes) /\ local_ptrs_reserved bc sa /\
  lookup_scopes id es.scopes = NONE /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  not_local_ptr cenv es.scopes ov /\ not_local_ptr cenv es.scopes tot /\
  not_local_ptr cenv es.scopes ep /\
  lookup_var idx s = SOME (n2w k) /\ eval_operand saved_base s = SOME arr_base /\
  lookup_var p s = SOME dst /\ p <> ov /\ p <> tot /\ p <> ep /\ ov <> tot /\
  (!x. saved_base = Var x ==> x <> ov /\ x <> tot) /\ not_fresh_at sa ep /\
  MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
  ainst.inst_outputs = [p] /\ fn_inst_ids_distinct func /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\ stride <= sz ==>
  ?t. run_inst_seq
    ([mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
      mk_inst j4 ADD [Lit 32w; Var ov] [tot];
      mk_inst j5 ADD [saved_base; Var tot] [ep]] ++ emitted_insts sa sb0) s = OK t /\
    stmt_state_rel ctx func bc cx
      (es with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>)) :: es.scopes) t /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep ==>
      lookup_var x t = lookup_var x s) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb0) /\
    (!a len. a + len <= w2n dst \/ w2n dst + stride <= a ==>
       mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >>
  `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  drule_all dynarray_for_body_entry_run >>
  disch_then (qspecl_then [`j3`, `j4`, `j5`] strip_assume_tac) >>
  drule_all intcall_dynarray_prefix_frame >>
  disch_then (qspecl_then [`j3`, `j4`, `j5`] strip_assume_tac) >>
  gvs[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem intcall_dynarray_copy_entry_frame[local]:
  dynarray_for_code fp.jc_func ce bc ty stmts id fty tv stride saved
    p sz aa idx dv ov tot ep nv lv cond exit bod incr
    j1 j2 j3 j4 j5 i1 i2 i3 sa sb0 sb1 sj /\
  evaluate_type (get_tenv fp.jc_cx) fty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  val_in_memory tv v (w2n arrbase + 32 + k * stride) s.vs_memory /\
  w2n arrbase + 32 + k * stride < dimword (:256) /\
  lookup_scopes id es.scopes = NONE /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  lookup_var idx s = SOME (n2w k) /\ eval_operand saved s = SOME arrbase /\
  lookup_var p s = SOME dst /\
  FLOOKUP s.vs_allocas aa.inst_id = SOME (w2n dst,sz) /\
  lookup_block sb0.cs_current_bb fp.jc_func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  s.vs_current_bb = sb0.cs_current_bb /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sc s /\
  declare_local ce id fty sd = (bc,sd') /\ ce.ce_alloca_locals /\
  FLOOKUP ce.ce_vars id = NONE /\ id NOTIN FDOM env.var_types /\
  type_memory_bytes ce fty < 2 ** 64 /\
  sc.cs_next_var <= sb0.cs_next_var /\
  (!x. not_fresh_at sc x ==>
       not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) ==>
  ?s2. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK s2) /\
    intcall_joint_res fp bc (extend_local env id fty F)
      (es with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv;
                          value := v; popped := []|>)) :: es.scopes) sb0 s2 /\
    s2.vs_current_bb = sb0.cs_current_bb /\
    s2.vs_inst_idx = LENGTH sb0.cs_current_insts /\ ~s2.vs_halted /\
    (!x. not_fresh_at sc x ==> lookup_var x s2 = lookup_var x s) /\
    s2.vs_allocas = s.vs_allocas /\ s.vs_alloca_next <= s2.vs_alloca_next /\
    (!x. not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep ==>
         lookup_var x s2 = lookup_var x s)
Proof
  strip_tac >>
  `cenv_top_ext ce bc (FEMPTY :: es.scopes)` by
    (drule_all dynarray_for_code_scope_frame >> simp[]) >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s` by
    fs[intcall_joint_res_def, intcall_expr_res_def] >>
  qhdtm_assum `dynarray_for_code`
    (strip_assume_tac o REWRITE_RULE [dynarray_for_code_def]) >>
  qpat_x_assum `ALL_DISTINCT _` (strip_assume_tac o SRULE [ALL_DISTINCT]) >>
  `type_memory_bytes ce fty = stride` by simp[] >>
  `not_local_ptr ce es.scopes ov /\ not_local_ptr ce es.scopes tot /\
   not_local_ptr ce es.scopes ep` by simp[] >>
  `p <> ov /\ p <> tot /\ p <> ep /\ ov <> tot` by metis_tac[] >>
  `sb0.cs_current_insts =
     [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
      mk_inst j4 ADD [Lit 32w; Var ov] [tot];
      mk_inst j5 ADD [saved; Var tot] [ep]] ++ emitted_insts sa sb0` by
    gvs[] >>
  `(!x. saved = Var x ==> x <> ov /\ x <> tot)` by
    (gen_tac >> strip_tac >>
     qpat_x_assum `!x. saved = Var x ==> ~MEM _ _` drule >> simp[]) >>
  drule_all intcall_dynarray_body_entry_run_frame >>
  disch_then (qspecl_then [`j3`, `j4`, `j5`] strip_assume_tac) >>
  `EVERY (\i. i.inst_opcode <> GAS) sb0.cs_current_insts` by
    (simp[mk_inst_def] >> metis_tac[iter_memory_copy_no_gas]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     sb0.cs_current_insts` by simp[mk_inst_def, is_terminator_def] >>
  `run_inst_seq sb0.cs_current_insts s = OK t` by gvs[] >>
  drule_all intcall_array_prefix_continuation_frame >> strip_tac >>
  `s.vs_alloca_next <= s2.vs_alloca_next` by
    (drule intcall_marked_path_frontier_mono >> simp[]) >>
  `allocas_above fp.jc_lo s2` by
    (fs[intcall_joint_res_def, intcall_expr_res_def, allocas_above_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `!a len. fp.jc_prot a len ==>
     mem_bytes_at a len s2.vs_memory = mem_bytes_at a len s.vs_memory` by
    (rpt strip_tac >> simp[] >> first_x_assum irule >> disj1_tac >>
     fs[intcall_frame_ok_def, intcall_joint_res_def, intcall_expr_res_def,
        allocas_above_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `!x. not_fresh_at sc x ==> lookup_var x s2 = lookup_var x s` by
    (simp[lookup_var_def] >> metis_tac[lookup_var_def]) >>
  `lookup_var p s2 = SOME dst` by
    (fs[local_ptrs_reserved_def] >> metis_tac[lookup_var_def]) >>
  qexists_tac `s2` >> simp[] >>
  conj_tac >- (irule intcall_for_declared_entry >> metis_tac[]) >>
  fs[lookup_var_def] >> metis_tac[]
QED

(* The copy-entry callback of intcall_array_gen_loop for a local DynArray,
   whose length register lv and saved base ip survive the copy. *)
Theorem intcall_dynarray_copy_entry:
  dynarray_for_code fp.jc_func ce bc ty stmts id fty tv stride (Var ip)
    p sz aa idx dv ov tot ep nv lv cond exit bod incr
    j1 j2 j3 j4 j5 i1 i2 i3 sa sb0 sb1 sj /\
  evaluate_type (get_tenv fp.jc_cx) fty = SOME tv /\
  (!k. k < LENGTH vs ==> value_has_type tv (EL k vs) /\ val_wf tv (EL k vs)) /\
  (!k ee s lbl. k < LENGTH vs /\
    array_loop_inv fp.jc_ctx fp.jc_func ce fp.jc_cx P vs id idx (Var ip)
      arrbase p dst sz aa lbl sc k ee s ==>
    val_in_memory tv (EL k vs) (w2n arrbase + 32 + k * stride) s.vs_memory /\
    w2n arrbase + 32 + k * stride < dimword (:256)) /\
  (!scopes. lookup_scopes id scopes = NONE ==>
    not_local_ptr bc (FEMPTY :: scopes) p) /\
  lookup_block sb0.cs_current_bb fp.jc_func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  intcall_frame_ok fp /\ declare_local ce id fty sd = (bc,sd') /\
  ce.ce_alloca_locals /\ FLOOKUP ce.ce_vars id = NONE /\
  id NOTIN FDOM env.var_types /\ type_memory_bytes ce fty < 2 ** 64 /\
  sc.cs_next_var <= sb0.cs_next_var /\ not_fresh_at sa lv /\
  (!x. not_fresh_at sc x ==>
       not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) ==>
  !k es next. k < LENGTH vs /\
    array_loop_inv fp.jc_ctx fp.jc_func ce fp.jc_cx P vs id idx (Var ip)
      arrbase p dst sz aa bod sc k es next /\
    intcall_joint_res fp ce env es sc next ==>
    ?s2. gas_marked_path F fp.jc_ctx fp.jc_func next 0 (OK s2) /\
      intcall_joint_res fp bc (extend_local env id fty F)
        (es with scopes :=
          (FEMPTY |+ (id, <|assignable := F; type := tv;
                            value := EL k vs; popped := []|>)) :: es.scopes)
        sb0 s2 /\
      s2.vs_current_bb = sb0.cs_current_bb /\
      s2.vs_inst_idx = LENGTH sb0.cs_current_insts /\ ~s2.vs_halted /\
      (!x. not_fresh_at sc x \/ x = idx \/ x = p \/ Var lv = Var x \/
           Var ip = Var x ==> lookup_var x s2 = lookup_var x next) /\
      (!aid b. FLOOKUP next.vs_allocas aid = SOME b ==>
               FLOOKUP s2.vs_allocas aid = SOME b) /\
      next.vs_alloca_next <= s2.vs_alloca_next
Proof
  strip_tac >>
  `!x. not_fresh_at sc x \/ x = idx \/ x = p \/ Var lv = Var x \/
       Var ip = Var x ==>
       not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep` by
    (qhdtm_assum `dynarray_for_code` mp_tac >>
     qpat_assum `!x. not_fresh_at sc x ==> _` mp_tac >>
     qpat_assum `not_fresh_at sa lv` mp_tac >>
     rpt (pop_assum kall_tac) >> rewrite_tac[dynarray_for_code_def] >>
     rpt strip_tac >> gvs[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `value_has_type tv (EL k vs) /\ val_wf tv (EL k vs)` by simp[] >>
  `val_in_memory tv (EL k vs) (w2n arrbase + 32 + k * stride) next.vs_memory /\
   w2n arrbase + 32 + k * stride < dimword (:256)` by
    (qpat_x_assum `!k ee s lbl. _` drule_all >> simp[]) >>
  qhdtm_assum `array_loop_inv`
    (strip_assume_tac o REWRITE_RULE [array_loop_inv_def]) >>
  `not_local_ptr bc (FEMPTY :: es.scopes) p` by
    (qpat_x_assum `!scopes. _` irule >> first_assum ACCEPT_TAC) >>
  `next.vs_current_bb = sb0.cs_current_bb` by
    (qhdtm_assum `dynarray_for_code`
       (strip_assume_tac o REWRITE_RULE [dynarray_for_code_def]) >>
     simp[]) >>
  drule_all intcall_dynarray_copy_entry_frame >> strip_tac >>
  `!x. not_fresh_at sc x \/ x = idx \/ x = p \/ Var lv = Var x \/
       Var ip = Var x ==> lookup_var x s2 = lookup_var x next` by
    (qx_gen_tac `x` >> disch_tac >>
     qpat_x_assum `!x. _ \/ _ ==> not_fresh_at sa x /\ _`
       (drule_then strip_assume_tac) >>
     qpat_x_assum `!x. not_fresh_at sa x /\ _ ==> _` irule >> simp[]) >>
  qexists_tac `s2` >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[]
QED
