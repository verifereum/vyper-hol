(* Seam 2 joint induction step: aggregate constructors and memory subplaces. *)
Theory bodyIntCallJointAgg
Ancestors
  bodyIntCallJointContract loweringPosts exprSimWordArgs
  compileEnv stmtSimProps bodyMemoryDefs freshWrites
  placeMemoryCopyEffect exprSimCopy bodyIntCallCopySharpDynamic
  venomState intCallFrame context emitHelper emitHelperProps
  exprLoweringProps venomExecSemantics venomInst venomMemProps
  bodyIntCallStorePost bodyIntCallProtectedAlloc exprSimAlloc

(* The continuation uses the standard write-back frame, so its composition
   and old-allocation interface are shared with other expression proofs. *)
Theorem intcall_expr_cont_frame:
  intcall_expr_cont fp ce env es sa s ee sb u <=>
  intcall_joint_res fp ce env ee sb u /\ ~u.vs_halted /\
  u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts /\
  s.vs_alloca_next <= u.vs_alloca_next /\
  wb_frame ce es sa s u
Proof
  simp[intcall_expr_cont_def, wb_frame_def] >> metis_tac[]
QED

Theorem intcall_expr_cont_trans:
  intcall_joint_res fp ce env es sa s /\
  intcall_expr_cont fp ce env es sa s em sm t /\
  intcall_expr_cont fp ce env em sm t ee sb u /\
  MAP FDOM es.scopes = MAP FDOM em.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id ==>
  intcall_expr_cont fp ce env es sa s ee sb u
Proof
  simp[intcall_expr_cont_frame] >> rpt strip_tac >>
  `wb_frame ce es sa s u` by
    (irule wb_frame_trans >>
     gvs[intcall_joint_res_def] >> metis_tac[]) >>
  simp[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

(* Transport the fixed-source resources across an operational suffix.  The
   state relation is supplied at that suffix's actual counted endpoint. *)
Theorem intcall_joint_res_frame:
  intcall_frame_ok fp /\
  intcall_joint_res fp ce env es sa s /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es u /\
  sa.cs_next_var <= sb.cs_next_var /\
  s.vs_alloca_next <= u.vs_alloca_next /\
  allocas_above fp.jc_lo u /\
  (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
         lookup_var x u = SOME w) /\
  (!a k. fp.jc_prot a k ==>
     mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory) /\
  (!op. fp.jc_reserved op ==> eval_operand op u = eval_operand op s) /\
  (!n b k. local_region ce es.scopes u n b k ==>
           local_region ce es.scopes s n b k) ==>
  intcall_joint_res fp ce env es sb u
Proof
  rpt strip_tac >>
  `local_ptrs_reserved ce sb` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     gvs[intcall_joint_res_def] >> metis_tac[]) >>
  `ret_pc_ok ce sb u` by
    (irule ret_pc_ok_frame >>
     gvs[intcall_joint_res_def] >> metis_tac[]) >>
  `return_buf_frame fp.jc_rb ce sb u` by
    (irule return_buf_frame_frame >>
     gvs[intcall_joint_res_def] >> metis_tac[]) >>
  `fp.jc_reserved fp.jc_rpc` by
    fs[intcall_frame_ok_def] >>
  gvs[intcall_joint_res_def] >>
  conj_tac
  >- (rpt strip_tac >> irule not_fresh_at_mono >>
      qexists_tac `sa` >> simp[]) >>
  conj_tac
  >- metis_tac[] >>
  gvs[]
QED

(* A store effect carries resources at its own operational endpoint. *)
Theorem intcall_joint_res_copy:
  intcall_frame_ok fp /\
  intcall_joint_res fp ce env es sa s /\
  typed_copy_effect fp.jc_ctx fp.jc_func sa sb s u dst len /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es u /\
  sa.cs_next_var <= sb.cs_next_var /\
  (!a k. fp.jc_prot a k ==> regions_disjoint a k dst len) ==>
  intcall_joint_res fp ce env es sb u
Proof
  rpt strip_tac >>
  `local_ptrs_reserved ce sa` by fs[intcall_joint_res_def] >>
  `!n b k. local_region ce es.scopes u n b k <=>
           local_region ce es.scopes s n b k` by
    (irule copy_buffer_local_region_frame >>
     qexists_tac `sa` >> fs[typed_copy_effect_def]) >>
  `u.vs_alloca_next = s.vs_alloca_next` by
    (drule typed_copy_effect_record >>
     simp[venom_state_component_equality]) >>
  `allocas_above fp.jc_lo u` by
    (fs[intcall_joint_res_def, allocas_above_def, typed_copy_effect_def] >>
     metis_tac[]) >>
  irule intcall_joint_res_frame >> simp[] >>
  qexistsl_tac [`s`, `sa`] >> simp[] >>
  conj_tac
  >- (fs[typed_copy_effect_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> irule typed_copy_effect_bytes >>
      goal_assum (drule_at Any) >> fs[regions_disjoint_def]) >>
  rpt strip_tac >> irule typed_copy_effect_operand_preserved >>
  goal_assum (drule_at Any) >> fs[intcall_joint_res_def] >> metis_tac[]
QED

(* Allocation fields do not require fresh_vars_wrt: ALLOCA overwrites only
   its own output even when stale temporary variables remain in the state. *)
Theorem intcall_alloc_run_frame:
  compile_alloc_buffer sz sa = (buf,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK u ==>
  (u with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
            vs_alloca_next := s.vs_alloca_next|>) = s /\
  s.vs_alloca_next <= u.vs_alloca_next
Proof
  simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
       comp_return_def, comp_ignore_bind_def, fresh_id_def, fresh_var_def,
       emit_def] >> strip_tac >>
  gvs[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND, run_inst_seq_def,
      step_inst_base_def, mk_inst_def] >>
  conj_tac
  >- (gvs[exec_alloca_def, AllCaseEqs(), update_var_def,
          venom_state_component_equality]) >>
  gvs[AllCaseEqs()] >> drule exec_alloca_alloca_next_mono >> simp[]
QED

(* Store into a root allocated since the expression began.  The existing
   owned-memory tail theorem supplies the old-allocation byte frame. *)
Theorem intcall_expr_cont_copy:
  intcall_expr_cont fp ce env es0 sa s0 es si s /\
  typed_copy_effect fp.jc_ctx fp.jc_func si sb s u dst len /\
  intcall_joint_res fp ce env es sb u /\
  alloca_inv s /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ sa.cs_next_id <= aid /\
  sa.cs_next_var <= si.cs_next_var /\
  b <= dst /\ dst + len <= b + sz /\
  (!n lb lsz. local_region ce es0.scopes s0 n lb lsz ==>
             lb + lsz <= b \/ b + sz <= lb) ==>
  intcall_expr_cont fp ce env es0 sa s0 es sb u
Proof
  rpt strip_tac >>
  `typed_copy_effect fp.jc_ctx fp.jc_func si sb s u b sz` by
    (irule typed_copy_effect_enlarge >> goal_assum (drule_at Any) >> simp[]) >>
  `wb_frame ce es0 sa s0 u` by
    (irule wb_frame_owned_memory_tail >> goal_assum (drule_at Any) >>
     qexistsl_tac [`aid`, `s`, `si`] >>
     fs[intcall_expr_cont_frame, typed_copy_effect_def] >> metis_tac[]) >>
  `u.vs_alloca_next = s.vs_alloca_next` by
    (drule typed_copy_effect_record >>
     simp[venom_state_component_equality]) >>
  fs[intcall_expr_cont_frame, typed_copy_effect_def]
QED

(* Project the resource invariant onto the supplied allocation run. *)
Theorem intcall_joint_res_alloc:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  compile_alloc_buffer sz sa = (buf,sb) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  sz < dimword (:256) /\
  run_inst_seq (emitted_insts sa sb) s = OK u ==>
  intcall_joint_res fp ce env es sb u
Proof
  rpt strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s /\
   local_ptrs_reserved ce sa /\ allocas_above fp.jc_lo s` by
    fs[intcall_joint_res_def] >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  gvs[] >> rename1 `run_inst_seq _ s = OK u` >>
  drule_all intcall_alloc_run_frame >> strip_tac >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (gvs[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
         comp_return_def, comp_ignore_bind_def, fresh_id_def, fresh_var_def,
         emit_def]) >>
  `allocas_above fp.jc_lo u` by
    (drule_all alloc_buffer_allocas_above >> simp[]) >>
  `!n b k. local_region ce es.scopes u n b k <=>
           local_region ce es.scopes s n b k` by
    (irule copy_buffer_local_region_frame >> qexists_tac `sa` >> simp[]) >>
  `u.vs_labels = s.vs_labels` by fs[venom_state_component_equality] >>
  irule intcall_joint_res_frame >> simp[] >>
  qexistsl_tac [`s`, `sa`] >> simp[] >>
  rpt strip_tac >> Cases_on `op` >>
  gvs[eval_operand_def, lookup_var_def, intcall_joint_res_def] >> metis_tac[]
QED

(* L-agg (C1.3.14.2.3), a step of the induction on expr_size: tuple
   literals (MakeArray NONE), array literals (MakeArray (SOME _)), struct
   literals, attributes and subscripts (every place_type case: tuple and
   struct literal-index, ValPT array, MapPT), given the producers of every
   smaller expression. *)
Theorem intcall_aggregate_producer_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  ((?a t n args. e = Builtin a (MakeArray t n) args) \/
   (?a nm fields. e = StructLit a nm fields) \/
   (?a base fld. e = Attribute a base fld) \/
   (?a base idx. e = Subscript a base idx)) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  cheat
QED
