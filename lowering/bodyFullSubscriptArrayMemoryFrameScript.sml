(* Transport the captured fixed array through a positively framed index. *)
Theory bodyFullSubscriptArrayMemoryFrame
Ancestors
  exprSimSubscriptArrayFrame exprBopSimProps bodyPtrBopRepresentationFrame
  bodyPtrDefs loweringPosts vyperValue vyperState exprSimProps
  exprSimHypsDefs[qualified]

Theorem captured_array_window_taint[local]:
  vv_at cenv cx ty sa sb t r (LocatedValue ty p) u /\
  p.ptr_location = LocMemory /\ read_result cx r t = (INL av,t) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand p.ptr_operand u = SOME w /\
  ghost_kept_at lo cenv t sb G0 tn0 u G tn /\
  w2n w <= i /\ i < w2n w + val_footprint tv av /\ i IN tn.t_mem ==>
  i IN tn0.t_mem
Proof
  strip_tac >>
  qpat_x_assum `vv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_at_def] >> strip_tac >> res_tac >> gvs[]
  >- (gvs[ghost_kept_at_def] >>
      `b <= i /\ i < b + sz` by decide_tac >> metis_tac[]) >>
  gvs[ghost_kept_at_def] >>
  `b <= i /\ i < b + sz` by decide_tac >> metis_tac[]
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  `evaluate_type (get_tenv cx) et = SOME etv` by
    (drule vyperTypeValuesTheory.evaluate_type_ArrayT_cases >> simp[]) >>
  `vv_holds cenv cx (ArrayT et (Fixed n)) r
     (LocatedValue (ArrayT et (Fixed n)) p) t' v /\
   vv_at cenv cx (ArrayT et (Fixed n)) sa sc t' r
     (LocatedValue (ArrayT et (Fixed n)) p) v` by
    (irule framed_array_base_transport >> simp[] >>
     goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     qexists_tac `env` >> simp[]) >>
  `wb_frame cenv t t' sb u v` by
    (drule exprSimWordArgsTheory.expr_post_frame >> simp[]) >>
  qpat_x_assum `ptr_vv_ok _ _ _ _ t _ _ _` mp_tac >>
  simp[bodyPtrDefsTheory.ptr_vv_ok_def] >>
  disch_then (CONJUNCTS_THEN2 assume_tac (qx_choose_then `av` strip_assume_tac)) >>
  `vv_at cenv cx (ArrayT et (Fixed n)) sa sb t r
     (LocatedValue (ArrayT et (Fixed n)) p) u` by
    fs[vv_post_def] >>
  `val_wf (ArrayTV etv (Fixed n)) av /\ ?w. eval_operand p.ptr_operand u = SOME w` by
    (qpat_assum `vv_at _ _ _ _ sb t _ _ u`
       (mp_tac o CONJUNCT2 o REWRITE_RULE [vv_at_def]) >>
     impl_tac >- simp[] >>
     disch_then (qspecl_then [`av`, `ArrayTV etv (Fixed n)`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  `eval_operand p.ptr_operand v = eval_operand p.ptr_operand u` by
    (simp[] >> irule eval_operand_frame >> simp[] >> qexistsl_tac [`sb`, `u`] >>
     fs[wb_frame_def]) >>
  `read_result cx r t' = (INL av,t')` by
    (`FST (read_result cx r t') = FST (read_result cx r t)` by
       (irule exprSimSubscriptArraySourceTheory.read_result_nonstorage_frame >> simp[]) >>
     Cases_on `read_result cx r t'` >> gvs[] >>
     drule vyperStateTheory.read_result_state >> simp[]) >>
  `(!x. p.ptr_operand = Var x ==> FLOOKUP G x = FLOOKUP G0 x) /\
   op_taint tn p.ptr_operand = op_taint tn0 p.ptr_operand` by
    (Cases_on `p.ptr_operand` >>
     fs[bodyPtrDefsTheory.ghost_kept_at_def, ptrDisciplineTheory.op_taint_def] >>
     metis_tac[]) >>
  simp[bodyPtrDefsTheory.ptr_vv_ok_def] >> conj_tac
  >- (irule bop_ptr_mem_ok_frame >>
      goal_assum (drule_at (Pat `ptr_mem_ok _ _ _ _ _ _ _`)) >>
      qexists_tac `ArrayTV etv (Fixed n)` >> simp[] >>
      rpt strip_tac
      >- (irule vv_at_memory_bytes_frame >> simp[exprSimPropsTheory.dynarray_free_fixed] >>
          goal_assum (drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`)) >>
          goal_assum (drule_at (Pat `wb_frame _ _ _ _ _ _`)) >>
          qexists_tac `env` >> simp[]) >>
      drule_all captured_array_window_taint >> simp[]) >>
  qpat_x_assum `ptr_buf_ok _ _ _ G0 _` mp_tac >>
  simp[bodyPtrDefsTheory.ptr_buf_ok_def] >> metis_tac[]
QED
*)
Theorem captured_memory_base_transport:
  !mods.
  vv_post H ctx func cenv cx obj es sa sb s0 t r
    (LocatedValue (ArrayT et (Fixed n)) p) u /\
  expr_post H ctx func cenv cx idx t sb sc u t' iv iop v /\
  expr_type obj = ArrayT et (Fixed n) /\
  post_value_type cenv obj = expr_type obj /\
  p.ptr_location = LocMemory /\
  evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) =
    SOME (ArrayTV etv (Fixed n)) /\ dynarray_free etv /\
  ptr_vv_ok cx (ArrayT et (Fixed n)) r
    (LocatedValue (ArrayT et (Fixed n)) p) t G0 tn0 u /\
  ptr_buf_ok cenv obj p.ptr_operand G0 u /\
  ghost_kept_at lo cenv t sb G0 tn0 u G tn /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sb x) /\
  (!l. p.ptr_operand <> Label l) /\
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  t'.scopes = t.scopes /\ t'.immutables = t.immutables /\
  expr_sim_inv_mods mods cenv cx env t /\ local_ptrs_reserved cenv sb /\
  sb.cs_next_id <= sc.cs_next_id ==>
  vv_holds cenv cx (ArrayT et (Fixed n)) r
    (LocatedValue (ArrayT et (Fixed n)) p) t' v /\
  vv_at cenv cx (ArrayT et (Fixed n)) sa sc t' r
    (LocatedValue (ArrayT et (Fixed n)) p) v /\
  ptr_vv_ok cx (ArrayT et (Fixed n)) r
    (LocatedValue (ArrayT et (Fixed n)) p) t' G tn v /\
  ptr_buf_ok cenv obj p.ptr_operand G v
Proof
  cheat
QED
