Theory bodyPtrPopTargetSimAttributeAdd
Ancestors
  bodyPtrPopTargetSimAttributeSource bodyPtrPopTargetDefs bodyPtrDefs
  bodyPtrAttributeAdd targetPlaceSimCasesBase emitHelperProps emitHelper
  compileEnv loweringStateRelDefs ptrDiscipline venomState venomInst words finite_map exprLowering
  fragGasPathPtr

(* Spatial extent is deliberately not asserted: a target pointer may denote
   a zero-sized child.  This transport only preserves its provenance class. *)
Theorem target_ptr_ok_operand_transport:
  target_ptr_ok cenv pv rb G tn s /\
  op_taint tn' (FST r) = {} /\
  op_prov G' (FST r) = op_prov G (FST rb) /\
  (!id p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) ==>
              FLOOKUP G' p = FLOOKUP G p) ==>
  target_ptr_ok cenv pv r G' tn' t
Proof
  simp[target_ptr_ok_def] >> metis_tac[]
QED

Theorem target_add_continuation_ptr:
  target_post ctx func cenv cx es sa sm s0 ee pv vt rb s /\
  ghost_inv d cenv cx ee G tn s /\ target_ptr_ok cenv pv' rb G tn s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  emit_op ADD [FST rb; Lit (n2w off)] sm = (dst,sb) /\
  fn_has_code sm sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  eval_operand (FST rb) s = SOME w0 /\
  place_ptr_rel cenv cx s pv' (w0 + n2w off) (FST (SND rb)) vt' /\
  place_readable cx ee pv' ==>
  ?H tm q.
    gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 H tm (OK q) /\
    target_post ctx func cenv cx es sa sb s0 ee pv' vt'
      (dst,FST (SND rb),SOME (value_type_place vt')) q /\
    q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv d cenv cx ee H tm q /\
    target_ptr_ok cenv pv' (dst,FST (SND rb),SOME (value_type_place vt')) H tm q /\
    ghost_kept cenv es sa G0 tn0 s0 H tm
Proof
  strip_tac >>
  `op_taint tn (FST rb) = {}` by gvs[target_ptr_ok_def] >>
  `?out H tm q.
    dst = Var out /\ gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 H tm (OK q) /\
    q = (update_var out (w0 + n2w off) s with vs_inst_idx := SUC s.vs_inst_idx) /\
    H = step_prov PG G (mk_inst sm.cs_next_id ADD [FST rb;Lit (n2w off)] [out])
          (update_var out (w0 + n2w off) s) /\
    tm = step_taint (mk_inst sm.cs_next_id ADD [FST rb;Lit (n2w off)] [out]) s
          (update_var out (w0 + n2w off) s) tn /\
    tm.t_imm = tn.t_imm /\ op_taint tm (Var out) = {} /\ tm.t_mem = tn.t_mem /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\
    (!p. p <> out ==> FLOOKUP H p = FLOOKUP G p /\
                       op_taint tm (Var p) = op_taint tn (Var p))` by
    (irule attribute_emit_binop_path_ptr >>
     simp[eval_operand_def, op_taint_def] >>
     qexistsl_tac [`FST rb`,`Lit (n2w off)`,`sb`] >> simp[]) >>
  `out = STRING #"%" (toString sm.cs_next_var) /\
   (!x. not_fresh_at sa x ==> x <> out)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL, arithmeticTheory.LESS_EQ_TRANS]) >>
  qexistsl_tac [`H`,`tm`,`q`] >> simp[] >>
  conj_tac >- suspend "semantic" >>
  conj_tac >- suspend "block" >>
  conj_tac >- suspend "index" >>
  conj_tac >- suspend "ghost" >>
  conj_tac >- suspend "pointer" >> suspend "frame"
QED

Resume target_add_continuation_ptr[semantic]:
  drule_all target_post_add >> strip_tac >>
  drule_all buffer_emit_add_run >> strip_tac >> gvs[]
QED

Resume target_add_continuation_ptr[block]:
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
      fresh_id_def, emit_def, comp_return_def, update_var_def]
QED

Resume target_add_continuation_ptr[index]:
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
      fresh_id_def, emit_def, comp_return_def, update_var_def]
QED

Resume target_add_continuation_ptr[ghost]:
  irule attribute_ghost_inv_update >> simp[] >>
  metis_tac[local_ptrs_reserved_def]
QED

Resume target_add_continuation_ptr[pointer]:
  irule target_ptr_ok_operand_transport >>
  conj_tac >- gvs[] >>
  qexistsl_tac [`G`,`rb`,`s`,`tn`] >>
  simp[op_prov_def, attribute_add_provenance] >>
  metis_tac[local_ptrs_reserved_def]
QED

Resume target_add_continuation_ptr[frame]:
  irule attribute_ghost_kept_frame >> metis_tac[]
QED

Finalise target_add_continuation_ptr
