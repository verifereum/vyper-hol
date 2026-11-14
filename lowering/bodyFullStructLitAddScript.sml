(* The destination ADD runs between the child expression and its unwrap. *)
Theory bodyFullStructLitAdd
Ancestors
  bodyFullAttributeAdd bodyPtrMakeArrayAddFrame bodyPtrMakeArrayEmission
  exprSimMemDefs assignBasePtrOffset exprSimVVFrame
  bodySimFull bodyPtrDefs allocaHistory emitHelperProps emitHelper
  loweringStateRelDefs compileEnv context venomInst venomState
  venomExecSemantics ptrDiscipline typedCopyPtr finite_map list arithmetic

Theorem structlit_child_add_full:
  emit_op ADD [Var root; Lit (n2w off)] sm = (Var out,sn) /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  lookup_var root s = SOME a /\ op_taint tn (Var root) = {} /\
  ptr_covers G tn root s capacity /\ FLOOKUP G root = SOME (region_base,cap) /\
  w2n a + off < dimword(:256) /\ off + n <= capacity /\
  local_ptrs_reserved ce si /\ si.cs_next_var <= sm.cs_next_var /\
  (!p. vv_operand vv = Var p ==> not_fresh_at sm p) /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func ce cx e es si sm s0 ee tv vv s /\
    ghost_inv_at (DF H) lo d ce cx ee G tn s) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv s /\
  ptr_vv_ok cx (post_value_type ce e) tv vv ee G tn s /\
  (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type ce e) ==>
    ptr_buf_ok ce e op G s) /\
  (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\
  ghost_kept_at lo ce es si Gi ti s0 G tn /\
  alloca_history func s /\ alloca_inv s ==>
  ?t G' tn'.
    (!D lo' explicit. allocas_from lo' s ==>
      gas_origin_ptr_path (D,lo',explicit,ctx,func,PG)
        (s,G,tn) [] (OK t,G',tn')) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      vv_post H ctx func ce cx e es si sm s0 ee tv vv t /\
      ghost_inv_at (DF H) lo d ce cx ee G' tn' t) /\
    vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv t /\
    ptr_vv_ok cx (post_value_type ce e) tv vv ee G' tn' t /\
    (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type ce e) ==>
      ptr_buf_ok ce e op G' t) /\
    (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok ce e p.ptr_operand G' t) /\
    ghost_kept_at lo ce es si Gi ti s0 G' tn' /\
    alloca_history func t /\ ~t.vs_halted /\
    t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!p. not_fresh_at sm p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p)) /\
    ptr_covers G' tn' out t n /\ lookup_var out t = SOME (a+n2w off)
Proof
  strip_tac >> drule_all emit_op_fetch_boundary >> strip_tac >>
  `out = STRING #"%" (toString sm.cs_next_var)` by fs[] >>
  `!p. not_fresh_at sm p ==> p <> out` by metis_tac[] >>
  qabbrev_tac `i = mk_inst sm.cs_next_id ADD [Var root; Lit (n2w off)] [out]` >>
  qabbrev_tac `u = update_var out (a+n2w off) s` >>
  qabbrev_tac `t = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G' = step_prov PG G i u` >>
  qabbrev_tac `tn' = step_taint i s u tn` >>
  `(!D lo' explicit. allocas_from lo' s ==>
     gas_origin_ptr_path (D,lo',explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
   FLOOKUP G' out = FLOOKUP G root /\ op_taint tn' (Var out) = {} /\
   tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
   tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
   (!p. p <> out ==> FLOOKUP G' p = FLOOKUP G p /\
     op_taint tn' (Var p) = op_taint tn (Var p))` by
    (`eval_operand (Var root) s = SOME a` by simp[eval_operand_def] >>
     rule_assum_tac (REWRITE_RULE [markerTheory.Abbrev_def]) >>
     drule_all attribute_add_full_frame >> simp[op_prov_def]) >>
  `(!D lo' d cx ee. ghost_inv_at D lo' d ce cx ee G tn s ==>
      ghost_inv_at D lo' d ce cx ee G' tn' t) /\
   ghost_kept_at lo ce es si Gi ti s0 G' tn'` by
    (mp_tac (attribute_fresh_full_ghost_update |> Q.INST
      [`sa` |-> `si`, `cenv` |-> `ce`, `w` |-> `a+n2w off`,
       `n` |-> `SUC s.vs_inst_idx`]) >>
     simp[Abbr `t`, Abbr `u`] >> metis_tac[]) >>
  `eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s` by
    (Cases_on `vv_operand vv` >>
     simp[Abbr `t`, Abbr `u`, eval_operand_def, lookup_var_def,
          update_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `alloca_history func t` by
    (`step_inst_base i s = OK u` by
       simp[Abbr `i`, Abbr `u`, step_inst_base_opcode_eqs,
            mk_inst_def, exec_pure2_def, eval_operand_def] >>
     `get_instruction bb s.vs_inst_idx = SOME i` by fs[Abbr `i`] >>
     drule_all alloca_history_base_step >>
     simp[Abbr `i`, mk_inst_def, is_terminator_def, Abbr `t`]) >>
  qexistsl_tac [`t`, `G'`, `tn'`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> simp[Abbr `t`, Abbr `u`] >>
      irule vv_post_update_var >> simp[] >>
      qexists_tac `sm` >> simp[not_fresh_at_def] >> metis_tac[]) >>
  conj_tac
  >- (irule vv_store_bound_frame_mem_src >> qexists_tac `s` >>
      simp[Abbr `t`, Abbr `u`, update_var_def]) >>
  conj_tac
  >- (unabbrev_all_tac >>
      irule binop_source_ptr_vv_ok >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      unabbrev_all_tac >>
      irule binop_source_ptr_buf_ok >> simp[] >> gvs[vv_operand_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      unabbrev_all_tac >>
      irule binop_source_ptr_buf_ok >> simp[] >> gvs[vv_operand_def] >> metis_tac[]) >>
  simp[Abbr `t`, Abbr `u`, update_var_def] >>
  conj_tac
  >- (rpt strip_tac >> simp[lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  reverse conj_tac >- simp[lookup_var_def, FLOOKUP_UPDATE] >>
  irule assign_base_ptr_covers_offset_address >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`G`, `region_base`, `cap`, `off`, `root`, `s`, `tn`, `capacity`, `a`] >>
  fs[lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[]
QED
