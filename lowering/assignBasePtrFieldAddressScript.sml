(* Ghost and value transport for the address ADD before word forcing. *)
Theory assignBasePtrFieldAddress
Ancestors assignBasePtrFieldForce bodyPtrAttributeAdd bodyPtrAttributeCase
  wordArgsPtr exprLoweringProps loweringPosts exprSimWordArgs assignBasePtrOffset
  exprSimAggregateChildren exprSimVVFrame exprOperandVar freshWrites
  bodyPtrDefs ptrDiscipline venomState venomExecSemantics finite_map
  compileEnv loweringStateRelDefs context ASCIInumbers emitHelper emitHelperProps pred_set arithmetic

Theorem assign_base_field_vv_update:
  ptr_vv_ok cx ty tv vv es G tn s /\
  (!x. vv_operand vv = Var x ==> x <> out) /\
  (!x. x <> out ==> FLOOKUP H x = FLOOKUP G x /\
    op_taint tf (Var x) = op_taint tn (Var x)) /\
  tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans ==>
  ptr_vv_ok cx ty tv vv es H tf
    (update_var out w s with vs_inst_idx := n)
Proof
  strip_tac >>
  `eval_operand (vv_operand vv) (update_var out w s with vs_inst_idx := n) =
   eval_operand (vv_operand vv) s /\
   op_taint tf (vv_operand vv) = op_taint tn (vv_operand vv) /\
   op_prov H (vv_operand vv) = op_prov G (vv_operand vv)` by
    (Cases_on `vv_operand vv` >>
     gvs[eval_operand_def, op_taint_def, op_prov_def, update_var_def,
         lookup_var_def, FLOOKUP_UPDATE]) >>
  Cases_on `vv` >>
  gvs[ptr_vv_ok_def, ptr_val_ok_def, ptr_mem_ok_def, vv_operand_def,
      update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem assign_base_field_add_vv_post:
  compile_expr cenv ty e sa = (vv,sm) /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [bop; Lit (n2w off)] sm = (dst,sn) /\
  vv_post ctx func cenv cx e es sa sm s0 ee tv vv s ==>
  vv_post ctx func cenv cx e es sa sn s0 ee tv vv
    (update_var (STRING #"%" (toString sm.cs_next_var)) bw s
      with vs_inst_idx := n)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  simp[] >> irule vv_post_update_var >> simp[] >> qexists_tac `sm` >> simp[] >>
  conj_tac >- metis_tac[cj 1 compiler_compile_var] >>
  simp[not_fresh_at_def, toString_11]
QED

Theorem assign_base_field_add_ptr_post:
  compile_expr cenv ty e sa = (vv,sm) /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [bop; Lit (n2w off)] sm = (dst,sn) /\
  vv_post ctx func cenv cx e es sa sm s0 ee tv vv s /\
  ptr_vv_ok cx (expr_type e) tv vv ee G tn s /\
  ghost_inv d cenv cx ee G tn s /\ ghost_kept cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!p. p <> STRING #"%" (toString sm.cs_next_var) ==>
    FLOOKUP H p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p)) /\
  tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
  tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm ==>
  vv_post ctx func cenv cx e es sa sn s0 ee tv vv
    (update_var (STRING #"%" (toString sm.cs_next_var)) bw s with vs_inst_idx := n) /\
  ptr_vv_ok cx (expr_type e) tv vv ee H tf
    (update_var (STRING #"%" (toString sm.cs_next_var)) bw s with vs_inst_idx := n) /\
  ghost_inv d cenv cx ee H tf
    (update_var (STRING #"%" (toString sm.cs_next_var)) bw s with vs_inst_idx := n) /\
  ghost_kept cenv es sa Gi ti s0 H tf
Proof
  strip_tac >> conj_tac
  >- (irule assign_base_field_add_vv_post >> goal_assum (drule_at Any) >>
      simp[] >> metis_tac[]) >>
  conj_tac
  >- (irule assign_base_field_vv_update >> simp[] >> conj_tac
      >- (strip_tac >>
          `not_fresh_at sm (STRING #"%" (toString sm.cs_next_var))` by
            metis_tac[cj 1 compiler_compile_var] >>
          gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
      qexistsl_tac [`G`, `tn`] >> simp[]) >>
  irule attribute_fresh_ghost_update >> goal_assum (drule_at Any) >>
  simp[] >> qexistsl_tac [`G`, `tn`] >> simp[]
QED

Theorem assign_base_field_add_vv_path_ptr:
  compile_expr cenv ty e sa = (vv,sm) /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [bop; Lit (n2w off)] sm = (dst,sn) /\
  fn_has_code sm sn func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  eval_operand bop s = SOME bw /\ op_taint tn bop = {} /\
  vv_post ctx func cenv cx e es sa sm s0 ee tv vv s /\
  ptr_vv_ok cx (expr_type e) tv vv ee G tn s /\
  ghost_inv d cenv cx ee G tn s /\ ghost_kept cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?out H tf q.
    dst = Var out /\
    gas_path_ptr D 0 ctx func PG G tn s 0 H tf (OK q) /\
    q = (update_var out (bw + n2w off) s with vs_inst_idx := SUC s.vs_inst_idx) /\
    vv_post ctx func cenv cx e es sa sn s0 ee tv vv q /\
    ptr_vv_ok cx (expr_type e) tv vv ee H tf q /\
    ghost_inv d cenv cx ee H tf q /\ ghost_kept cenv es sa Gi ti s0 H tf /\
    eval_operand dst q = SOME (bw + n2w off) /\
    FLOOKUP H out = op_prov G bop /\ op_taint tf dst = {} /\
    ~q.vs_halted /\ q.vs_current_bb = sn.cs_current_bb /\
    q.vs_inst_idx = LENGTH sn.cs_current_insts
Proof
  strip_tac >>
  `op_taint tn (Lit (n2w off)) = {}` by simp[op_taint_def] >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off)` by simp[eval_operand_def] >>
  drule_all (attribute_emit_binop_path_ptr |> SPEC_ALL
    |> Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  drule_all assign_base_field_add_ptr_post >>
  disch_then (qspecl_then [`SUC s.vs_inst_idx`, `bw + n2w off`] strip_assume_tac) >>
  goal_assum (drule_at Any) >> simp[] >>
  `sn.cs_current_bb = sm.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  gvs[attribute_add_provenance, eval_operand_def, lookup_var_def,
      update_var_def, FLOOKUP_UPDATE]
QED

(* Rebase at the post-ADD state so that the destination is protected. *)
Theorem assign_base_field_rebased_word_read_ptr:
  unwrap_value cenv vv sm = (op,sb) /\ is_word_type (expr_type e) /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  fn_has_code sm sb func /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME rty /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  vv_post ctx func cenv cx e es sa sm s0 ee tv vv s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ghost_inv d cenv cx ee G tn s /\
  ptr_vv_ok cx (expr_type e) tv vv ee G tn s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?v H tf z.
    gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG (read_result cx tv)
      (ee,s,G,tn) [] (INL v) ee H tf (OK z) /\
    expr_post ctx func cenv cx e ee (sa with cs_next_var := sm.cs_next_var)
      sb s ee v op z /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv d cenv cx ee H tf z /\
    ptr_val_ok cx (expr_type e) v op H tf z /\
    (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e op H z) /\
    ghost_kept cenv ee (sa with cs_next_var := sm.cs_next_var) G tn s H tf
Proof
  strip_tac >>
  drule vv_post_rebase >> strip_tac >>
  `local_ptrs_reserved cenv (sa with cs_next_var := sm.cs_next_var)` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  `!x. not_fresh_at sa x ==>
    not_fresh_at (sa with cs_next_var := sm.cs_next_var) x` by
    (simp[not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  irule assign_base_word_unwrap_marked_read_ptr >>
  simp[ghost_kept_refl] >> qexistsl_tac [`sm`, `vv`] >> simp[]
QED

Theorem assign_base_field_rebased_destination:
  expr_post ctx func cenv cx e ee (sa with cs_next_var := sm.cs_next_var)
    sb s ee v op z /\
  ghost_kept cenv ee (sa with cs_next_var := sm.cs_next_var) G tn s H tf /\
  not_fresh_at sm x /\ eval_operand (Var x) s = SOME w ==>
  eval_operand (Var x) z = SOME w /\
  FLOOKUP H x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)
Proof
  simp[expr_post_def, ghost_kept_def, not_fresh_at_def, eval_operand_def] >>
  metis_tac[]
QED


(* Compose the ordinary and ghost frames at the same post-ADD endpoint. *)
Theorem assign_base_field_rebased_posts:
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ is_word_type (expr_type e) /\
  vv_post ctx func cenv cx e es sa sm s0 ee tv vv q /\
  ghost_kept cenv es sa Gi ti s0 G tn /\
  expr_post ctx func cenv cx e ee (sa with cs_next_var := sm.cs_next_var)
    sb q ee v op z /\
  ghost_kept cenv ee (sa with cs_next_var := sm.cs_next_var) G tn q H tf ==>
  expr_post ctx func cenv cx e es sa sb s0 ee v op z /\
  ghost_kept cenv es sa Gi ti s0 H tf
Proof
  strip_tac >>
  `wb_frame cenv es sa s0 q` by
    (gvs[vv_post_def, wb_frame_def] >> metis_tac[]) >>
  `wb_frame cenv ee (sa with cs_next_var := sm.cs_next_var) q z` by
    metis_tac[expr_post_frame] >>
  `wb_frame cenv es sa s0 z` by
    (irule wb_frame_trans >> simp[] >> conj_tac
     >- (qexistsl_tac [`ee`, `sa with cs_next_var := sm.cs_next_var`, `q`] >> simp[]) >>
     metis_tac[]) >>
  conj_tac
  >- (gvs[expr_post_def, expr_val_at_def, wb_frame_def] >> metis_tac[]) >>
  irule ghost_kept_wb_trans >> simp[] >> conj_tac
  >- metis_tac[] >>
  goal_assum (drule_at (Pat `ghost_kept _ _ _ _ _ _ _ _`)) >>
  simp[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem assign_base_field_add_word_read_ptr:
  compile_expr cenv ty e sa = (vv,sm) /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\
  stmt_state_rel ctx func cenv cx es s0 /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  emit_op ADD [bop; Lit (n2w off)] sm = (dst,sn) /\
  unwrap_value cenv vv sn = (op,su) /\
  fn_has_code sm sn func /\ fn_has_code sn su func /\
  ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\ is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME rty /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  eval_operand bop s = SOME bw /\ op_taint tn bop = {} /\
  vv_post ctx func cenv cx e es sa sm s0 ee tv vv s /\
  ptr_vv_ok cx (expr_type e) tv vv ee G tn s /\
  ghost_inv d cenv cx ee G tn s /\ ghost_kept cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?v H tf z.
    gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG (read_result cx tv)
      (ee,s,G,tn) [] (INL v) ee H tf (OK z) /\
    expr_post ctx func cenv cx e es sa su s0 ee v op z /\
    ghost_kept cenv es sa Gi ti s0 H tf /\
    ghost_inv d cenv cx ee H tf z /\ ptr_val_ok cx (expr_type e) v op H tf z /\
    eval_operand dst z = SOME (bw + n2w off) /\
    op_prov H dst = op_prov G bop /\ op_taint tf dst = {} /\
    z.vs_current_bb = su.cs_current_bb /\ z.vs_inst_idx = LENGTH su.cs_current_insts
Proof
  strip_tac >>
  drule_all assign_base_field_add_vv_path_ptr >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  `sa.cs_next_var <= sn.cs_next_var` by
    (drule emitted_insts_emit_op >> simp[]) >>
  drule_all assign_base_field_rebased_word_read_ptr >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  drule_all assign_base_field_rebased_posts >> strip_tac >>
  `not_fresh_at sn out` by
    (drule emitted_insts_emit_op >> simp[not_fresh_at_def, toString_11]) >>
  qpat_x_assum `dst = Var out` SUBST_ALL_TAC >>
  drule_all assign_base_field_rebased_destination >> strip_tac >>
  qexistsl_tac [`v`, `H'`, `tf'`, `z`] >>
  gvs[op_prov_def] >>
  qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[gasSummaryComposePtrTheory.gas_marked_exec_ptr_def] >> strip_tac >> simp[] >>
  metis_tac[fragGasPathPtrTheory.gas_path_ptr_then, ADD_CLAUSES]
QED

(* The numerical bound is address-specific, not a provenance-site bound. *)
Theorem assign_base_field_destination_coverage:
  !G tn p s total bw dst out z off H tf n.
  ptr_covers G tn p s total /\ eval_operand (Var p) s = SOME bw /\
  dst = Var out /\ eval_operand dst z = SOME (bw + n2w off) /\
  op_prov H dst = op_prov G (Var p) /\ op_taint tf dst = {} /\
  w2n bw + off < dimword(:256) /\ off + n <= total ==>
  ptr_covers H tf out z n
Proof
  rpt strip_tac >>
  `?b cap. FLOOKUP G p = SOME (b,cap)` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  irule assign_base_ptr_covers_offset_address >>
  gvs[op_prov_def, eval_operand_def] >>
  goal_assum (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  qexistsl_tac [`off`, `bw`] >> simp[]
QED

Theorem assign_base_field_destination_storage:
  eval_operand dst z = SOME (slot + n2w off) /\
  op_prov H dst = op_prov G (Lit slot) /\ op_taint tf dst = {} ==>
  eval_operand dst z = SOME (slot + n2w off) /\
  op_prov H dst = NONE /\ op_taint tf dst = {}
Proof
  simp[op_prov_def]
QED
