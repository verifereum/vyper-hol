Theory bodyPtrAttributeCase
Ancestors
  bodyPtrAttributeAdd bodyPtrAttributeFields exprSimAttribute exprSimVVFrame
  exprSimFieldLayout vyperStoragePlaceRegion
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

(* Restrict a located storage/transient pointer's dead bytes to a field.
   Code pointers impose no storage condition. *)
Theorem attribute_nonmemory_field_ptr:
  ptr_vv_ok cx (StructT sid) tv vv ee G tn s /\ vv_loc vv <> LocMemory /\
  evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
  evaluate_type (get_tenv cx) ann = SOME ftv /\
  struct_field_slot fs fld = SOME (off,ftv) /\
  eval_operand (vv_operand vv) s = SOME w /\
  eval_operand dst t = SOME (w + n2w off) /\
  ((vv_loc vv = LocStorage \/ vv_loc vv = LocTransient) /\
   0 < type_slot_size ftv ==> w2n (w + n2w off) = w2n w + off) /\
  t.vs_accounts = s.vs_accounts /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_transient = s.vs_transient /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
  op_taint tn' dst = {} ==>
  ptr_vv_ok cx ann tv' (LocatedValue ann (mk_ptr dst (vv_loc vv))) ee' H tn' t
Proof
  strip_tac >> irule ptr_vv_ok_nonmemory >>
  simp[mk_ptr_def] >> rpt strip_tac >> gvs[] >>
  Cases_on `type_slot_size ftv = 0` >- gvs[] >>
  drule struct_field_slot_end_bound >> strip_tac >>
  `w2n w <= w2n k /\ w2n k < w2n w + type_slot_size (StructTV fs)` by decide_tac >>
  Cases_on `vv` >> gvs[vv_loc_def, vv_location_def] >>
  gvs[ptr_vv_ok_def, vv_operand_def] >>
  `w2n w <= w2n k /\ w2n k < w2n w + type_slot_size (StructTV fs)` by decide_tac >>
  `w2n w + off <= w2n k /\ w2n k < w2n w + off + type_slot_size ftv` by decide_tac >>
  metis_tac[struct_field_dead_bytes_iff, ADD_COMM]
QED

Theorem attribute_memory_field_ptr:
  ptr_vv_ok cx (StructT sid) tv vv ee G tn s /\ vv_loc vv = LocMemory /\
  read_result cx tv ee = (INL (StructV vals), ee) /\
  read_result cx tv' ee = (INL fv, ee) /\
  evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
  evaluate_type (get_tenv cx) ann = SOME ftv /\
  fields_layout fields fs /\ struct_has_type fs vals /\
  ALOOKUP vals fld = SOME fv /\ ALOOKUP fs fld = SOME ftv /\ val_wf ftv fv /\
  type_memory_bytes cenv (lowered_value_type cenv fldexpr) = type_memory_size ftv /\
  eval_operand (vv_operand vv) s = SOME w /\
  eval_operand dst t = SOME (w + n2w (struct_field_offset fields fld)) /\
  w2n (w + n2w (struct_field_offset fields fld)) = w2n w + struct_field_offset fields fld /\
  t.vs_memory = s.vs_memory /\ tn'.t_mem = tn.t_mem /\ op_taint tn' dst = {} /\
  (!x b sz. vv_operand vv = Var x /\ FLOOKUP G x = SOME (b,sz) ==>
     ?y. dst = Var y /\ FLOOKUP H y = SOME (b,sz)) ==>
  ptr_vv_ok cx ann tv' (LocatedValue ann (mk_ptr dst LocMemory)) ee H tn' t /\
  ptr_buf_ok cenv fldexpr dst H t
Proof
  strip_tac >>
  `ptr_mem_ok cx (StructT sid) (StructV vals) (vv_operand vv) G tn s` by
    (drule_all attribute_base_ptr_memory >> simp[]) >>
  `!u. eval_operand dst t = SOME u ==>
     u = w + n2w (struct_field_offset fields fld)` by (rpt strip_tac >> gvs[]) >>
  conj_tac
  >- (irule ptr_vv_ok_memory >> simp[mk_ptr_def] >>
      drule_all struct_ptr_mem_ok_field >> simp[]) >>
  irule struct_ptr_mem_ok_field_buffer >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  drule_all struct_field_offset_le >> simp[valueEncodingTheory.type_memory_size_def]
QED
