Theory bodyPtrAttributeCase
Ancestors
  bodyPtrAttributeAdd bodyPtrAttributeFields exprSimAttribute exprSimVVFrame
  exprOperandVar freshWrites ASCIInumbers emitHelperProps bodyPtrDefs
  exprLoweringProps exprSimAttributeProps exprLowering context compileEnv venomState ptrDiscipline ptrSafeRun finite_map list arithmetic

(* Ordinary post transport is kept separate from the counted ghost edge. *)
Theorem attribute_add_vv_post:
  compile_expr cenv ty e sa = (vv,sm) /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [vv_operand vv; Lit (n2w off)] sm = (dst,sn) /\
  vv_post ctx func cenv cx e es sa sm s0 es' tv vv s /\
  eval_operand (vv_operand vv) s = SOME w ==>
  vv_post ctx func cenv cx e es sa sn s0 es' tv vv
    (update_var (STRING #"%" (toString sm.cs_next_var)) (w + n2w off) s
      with vs_inst_idx := n) /\
  eval_operand (vv_operand vv)
    (update_var (STRING #"%" (toString sm.cs_next_var)) (w + n2w off) s
      with vs_inst_idx := n) = SOME w
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  `!z. vv_operand vv = Var z ==> not_fresh_at sm z` by
    metis_tac[cj 1 compiler_compile_var] >>
  simp[] >> conj_tac
  >- (irule vv_post_update_var >> simp[] >> qexists_tac `sm` >>
      simp[not_fresh_at_def, toString_11]) >>
  qpat_x_assum `eval_operand (vv_operand vv) s = _` (SUBST1_TAC o SYM) >>
  irule literal_operand_frame >>
  reverse conj_tac >- simp[update_var_def] >>
  qexists_tac `sm` >> simp[] >>
  rw[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]
QED

Theorem attribute_add_path_post_ptr:
  compile_expr cenv ty e sa = (vv,sm) /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [vv_operand vv; Lit (n2w off)] sm = (dst,sn) /\
  fn_has_code sm sn func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  vv_post ctx func cenv cx e es sa sm s0 es' tv vv s /\
  eval_operand (vv_operand vv) s = SOME w /\ op_taint tn (vv_operand vv) = {} ==>
  ?out G' tn' t.
    dst = Var out /\ gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK t) /\
    t = (update_var out (w + n2w off) s with vs_inst_idx := SUC s.vs_inst_idx) /\
    vv_post ctx func cenv cx e es sa sn s0 es' tv vv t /\
    eval_operand (vv_operand vv) t = SOME w /\
    eval_operand dst t = SOME (w + n2w off) /\
    FLOOKUP G' out = op_prov G (vv_operand vv) /\
    op_taint tn' dst = {} /\ tn'.t_mem = tn.t_mem /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!p. p <> out ==> FLOOKUP G' p = FLOOKUP G p /\
       op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `op_taint tn (Lit (n2w off)) = {}` by simp[op_taint_def] >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off)` by simp[eval_operand_def] >>
  drule_all (attribute_emit_binop_path_ptr |> SPEC_ALL
    |> Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  goal_assum (drule_at Any) >> simp[] >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  drule_all attribute_add_vv_post >>
  simp[attribute_add_provenance, eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE]
QED

Theorem attribute_fresh_ghost_update:
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  ghost_inv d cenv cx ee G tn s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
  tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  (!p. p <> STRING #"%" (toString sm.cs_next_var) ==>
     FLOOKUP G' p = FLOOKUP G p /\ op_taint tn' (Var p) = op_taint tn (Var p)) ==>
  ghost_inv d cenv cx ee G' tn'
    (update_var (STRING #"%" (toString sm.cs_next_var)) w s with vs_inst_idx := n) /\
  ghost_kept cenv es sa G0 tn0 s0 G' tn'
Proof
  strip_tac >>
  `!p. not_fresh_at sa p ==> p <> STRING #"%" (toString sm.cs_next_var)` by
    (rpt strip_tac >> gvs[not_fresh_at_def] >>
     first_x_assum (qspec_then `sm.cs_next_var` mp_tac) >> simp[]) >>
  conj_tac
  >- (irule attribute_ghost_inv_update >> simp[] >>
      gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
  irule attribute_ghost_kept_frame >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[]
QED

Theorem attribute_base_ptr_memory:
  ptr_vv_ok cx (StructT sid) tv vv ee G tn s /\
  read_result cx tv ee = (INL v, ee) /\ vv_loc vv = LocMemory ==>
  ptr_mem_ok cx (StructT sid) v (vv_operand vv) G tn s
Proof
  Cases_on `vv` >>
  simp[ptr_vv_ok_def, ptr_val_ok_def, is_word_type_def, vv_operand_def,
       vv_loc_def, vv_location_def] >> rpt strip_tac >> gvs[]
QED
