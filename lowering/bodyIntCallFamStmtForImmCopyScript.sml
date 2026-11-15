(* The element copy at the top of an immutable-array For body, at the joint
   resources of the internal-call producer. *)
Theory bodyIntCallFamStmtForImmCopy
Ancestors
  bodyIntCallJointContract bodyIntCallFamStmtForArrayFrame
  bodyIntCallFamStmtForResources bodyIntCallFamStmtForFrontier
  whitelistForIterImmLoop whitelistForIterImmCopy stmtSimForArrayLoop
  stmtSimDeclCompose localPtrsProps exprSimCopy exprLoweringProps
  stmtSimProps loweringPosts loweringStateRelDefs intCallFrame compileEnv
  emitHelperProps vyperState venomState venomInst venomExecSemantics
  finite_map list rich_list

(* The address prefix and the copy, run straight through: the copy writes
   only the element slot. *)
Theorem immutable_body_entry_run_frame:
  compile_iter_elem_copy cenv (Var ep) (Var p) stride LocCode F et et sa =
    ((),sb0) /\
  sa.cs_current_insts =
    [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov]] ++
    (if dyn then [mk_inst j4 ADD [Lit 32w; Var ov] [tot]] else []) ++
    [mk_inst j5 ADD [Lit (n2w off); Var (if dyn then tot else ov)] [ep]] /\
  sb0.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb0 /\
  stride = type_memory_size tv /\ 0 < stride /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  stmt_state_rel ctx func cenv cx es s /\
  cenv_top_ext cenv bc (FEMPTY :: es.scopes) /\ local_ptrs_reserved bc sa /\
  lookup_scopes id es.scopes = NONE /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  not_local_ptr cenv es.scopes ov /\ not_local_ptr cenv es.scopes tot /\
  not_local_ptr cenv es.scopes ep /\
  lookup_var idx s = SOME (n2w k) /\ lookup_var p s = SOME dst /\
  p <> ov /\ p <> tot /\ p <> ep /\ ov <> tot /\ not_fresh_at sa ep /\
  MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
  ainst.inst_outputs = [p] /\ fn_inst_ids_distinct func /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\ stride <= sz /\
  w2n dst + stride < dimword (:256) /\
  immutable_holds cenv cx et (Value v)
    (n2w off + n2w ((if dyn then 32 else 0) + k * stride)) es s ==>
  ?t. run_inst_seq sb0.cs_current_insts s = OK t /\
    stmt_state_rel ctx func bc cx
      (es with scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := v; popped := []|>)) ::
        es.scopes) t /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep ==>
         lookup_var x t = lookup_var x s) /\
    (!a len. a + len <= w2n dst \/ w2n dst + stride <= a ==>
       mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)
Proof
  strip_tac >>
  qabbrev_tac `rhs = update_var ep
    (n2w off + n2w ((if dyn then 32 else 0) + k * stride))
    (if dyn then update_var tot (n2w (32 + k * stride))
       (update_var ov (n2w (k * stride)) s)
     else update_var ov (n2w (k * stride)) s)` >>
  `run_inst_seq sa.cs_current_insts s = OK rhs` by
    (qunabbrev_tac `rhs` >> asm_rewrite_tac[] >>
     irule immutable_address_prefix_run >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es rhs` by
    (Cases_on `dyn` >> simp[Abbr `rhs`] >>
     rpt (irule stmt_state_rel_update_var >> simp[])) >>
  `stmt_state_rel ctx func bc cx (es with scopes := FEMPTY :: es.scopes) rhs` by
    (irule array_empty_scope_rel_transport >> qexists_tac `cenv` >> simp[]) >>
  `immutable_holds bc cx et (Value v)
     (n2w off + n2w ((if dyn then 32 else 0) + k * stride))
     (es with scopes := FEMPTY :: es.scopes) rhs` by
    (irule immutable_value_holds_transport >>
     goal_assum (drule_at Any) >> simp[] >>
     qexists_tac `FEMPTY :: es.scopes` >> simp[] >>
     Cases_on `dyn` >> simp[Abbr `rhs`, update_var_def]) >>
  `compile_iter_elem_copy bc (Var ep) (Var p) stride LocCode F et et sa =
     ((),sb0)` by
    (drule immutable_iter_copy_top_ext >> disch_then (fn th => fs[GSYM th])) >>
  `lookup_var p rhs = SOME dst /\
   FLOOKUP rhs.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
   eval_operand (Var ep) rhs =
     SOME (n2w off + n2w ((if dyn then 32 else 0) + k * stride)) /\
   rhs.vs_memory = s.vs_memory` by
    (Cases_on `dyn` >>
     simp[Abbr `rhs`, lookup_var_update_var, eval_operand_def] >>
     simp[update_var_def]) >>
  `copy_old_operand sa (Var ep)` by simp[copy_old_operand_def] >>
  `!q. q = p \/ ~not_local_ptr bc
      (es with scopes := FEMPTY :: es.scopes).scopes q ==> not_fresh_at sa q` by
    (simp[] >> metis_tac[array_copy_live_ptrs_reserved]) >>
  `(es with scopes := FEMPTY :: es.scopes).scopes = FEMPTY :: es.scopes /\
   lookup_scopes id (es with scopes := FEMPTY :: es.scopes).scopes = NONE /\
   not_local_ptr bc (es with scopes := FEMPTY :: es.scopes).scopes p` by
    simp[lookup_scopes_def] >>
  drule_all immutable_iter_copy_declare_rel >>
  disch_then (qspec_then `F` strip_assume_tac) >>
  `(z with <|vs_vars := rhs.vs_vars; vs_memory := rhs.vs_memory|>) = rhs` by
    (drule_all immutable_iter_copy_state_frame >> simp[]) >>
  qexists_tac `z` >> rpt conj_tac
  >- (qpat_assum `run_inst_seq _ s = OK rhs`
        (mp_then Any (qspec_then `emitted_insts sa sb0` mp_tac)
           run_inst_seq_append) >>
      fs[copy_runtime_frame_def])
  >- fs[]
  >- (qpat_x_assum `_ = rhs` mp_tac >>
      Cases_on `dyn` >>
      simp[Abbr `rhs`, update_var_def, venom_state_component_equality])
  >- (rpt strip_tac >> fs[copy_runtime_frame_def] >>
      Cases_on `dyn` >>
      fs[Abbr `rhs`, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  rpt strip_tac >> fs[]
QED

(* The element copy, at the declared body's joint resources. *)
Theorem intcall_imm_copy_entry:
  compile_iter_elem_copy ce (Var ep) (Var p) stride LocCode F fty fty sa =
    ((),sb0) /\
  sa.cs_current_insts =
    [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov]] ++
    (if dyn then [mk_inst j4 ADD [Lit 32w; Var ov] [tot]] else []) ++
    [mk_inst j5 ADD [Lit (n2w off); Var (if dyn then tot else ov)] [ep]] /\
  sb0.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb0 /\
  lookup_block sb0.cs_current_bb fp.jc_func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  s.vs_current_bb = sb0.cs_current_bb /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  stride = type_memory_size tyv /\ 0 < stride /\
  evaluate_type (get_tenv fp.jc_cx) fty = SOME tyv /\ value_has_type tyv v /\
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sc s /\
  declare_local ce id fty sd = (bc,sd') /\ ce.ce_alloca_locals /\
  FLOOKUP ce.ce_vars id = NONE /\ id NOTIN FDOM env.var_types /\
  lookup_scopes id es.scopes = NONE /\ type_memory_bytes ce fty < 2 ** 64 /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  (!n. n <> id ==> FLOOKUP bc.ce_vars n = FLOOKUP ce.ce_vars n) /\
  bc.ce_imm_alloca = ce.ce_imm_alloca /\
  local_ptrs_reserved bc sa /\ local_ptrs_reserved bc sb0 /\
  sc.cs_next_var <= sb0.cs_next_var /\
  (!scs. not_local_ptr ce scs p /\ not_local_ptr ce scs ov /\
         not_local_ptr ce scs tot /\ not_local_ptr ce scs ep) /\
  lookup_var idx s = SOME (n2w k) /\ lookup_var p s = SOME dst /\
  p <> ov /\ p <> tot /\ p <> ep /\ ov <> tot /\ not_fresh_at sa ep /\
  MEM ainst (fn_insts fp.jc_func) /\ ainst.inst_opcode = ALLOCA /\
  ainst.inst_outputs = [p] /\ fn_inst_ids_distinct fp.jc_func /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\ stride <= sz /\
  w2n dst + stride < dimword (:256) /\
  immutable_holds ce fp.jc_cx fty (Value v)
    (n2w off + n2w ((if dyn then 32 else 0) + k * stride)) es s /\
  (!x. not_fresh_at sc x ==> not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) ==>
  ?s2. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK s2) /\
    intcall_joint_res fp bc (extend_local env id fty F)
      (es with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tyv;
                          value := v; popped := []|>)) :: es.scopes) sb0 s2 /\
    s2.vs_current_bb = sb0.cs_current_bb /\
    s2.vs_inst_idx = LENGTH sb0.cs_current_insts /\ ~s2.vs_halted /\
    s2.vs_allocas = s.vs_allocas /\ s.vs_alloca_next <= s2.vs_alloca_next /\
    (!x. not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep ==>
         lookup_var x s2 = lookup_var x s)
Proof
  strip_tac >>
  `cenv_top_ext ce bc (FEMPTY :: es.scopes)` by
    (drule cenv_top_ext_declare_local >>
     disch_then (qspecl_then [`FEMPTY`, `es.scopes`] mp_tac) >> simp[]) >>
  `not_local_ptr bc (FEMPTY :: es.scopes) p` by
    (irule not_local_ptr_name_update >> qexistsl_tac [`ce`, `id`] >> simp[]) >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s` by
    fs[intcall_joint_res_def, intcall_expr_res_def] >>
  `not_local_ptr ce es.scopes ov /\ not_local_ptr ce es.scopes tot /\
   not_local_ptr ce es.scopes ep` by simp[] >>
  drule_all immutable_body_entry_run_frame >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> GAS) sb0.cs_current_insts /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     sb0.cs_current_insts` by
    (drule immutable_iter_copy_opcodes >> strip_tac >>
     qpat_x_assum `sb0.cs_current_insts = sa.cs_current_insts ++ code` mp_tac >>
     qpat_x_assum `sa.cs_current_insts = _` mp_tac >>
     qpat_x_assum `EVERY _ code` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> Cases_on `dyn` >>
     gvs[mk_inst_def, is_terminator_def, EVERY_MEM] >>
     rpt strip_tac >> res_tac >> gvs[is_terminator_def]) >>
  drule_all intcall_array_prefix_continuation_frame >> strip_tac >>
  `s.vs_alloca_next <= s2.vs_alloca_next` by
    (drule intcall_marked_path_frontier_mono >> simp[]) >>
  `allocas_above fp.jc_lo s2` by
    (fs[intcall_joint_res_def, intcall_expr_res_def, allocas_above_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `fp.jc_lo <= w2n dst` by
    (fs[intcall_joint_res_def, intcall_expr_res_def, allocas_above_def] >>
     metis_tac[]) >>
  `!a len. fp.jc_prot a len ==>
     mem_bytes_at a len s2.vs_memory = mem_bytes_at a len s.vs_memory` by
    (rpt strip_tac >> simp[] >> first_x_assum irule >> disj1_tac >>
     fs[intcall_frame_ok_def] >> res_tac >> decide_tac) >>
  `!x. not_fresh_at sc x ==> lookup_var x s2 = lookup_var x s` by
    (simp[lookup_var_def] >> metis_tac[lookup_var_def]) >>
  `lookup_var p s2 = SOME dst` by
    (fs[local_ptrs_reserved_def] >> metis_tac[lookup_var_def]) >>
  qexists_tac `s2` >> simp[] >>
  conj_tac >- (irule intcall_for_declared_entry >> metis_tac[]) >>
  fs[lookup_var_def] >> metis_tac[]
QED
