Theory bodyIntCallCopySharpFixed
Ancestors
  bodyIntCallCopySharpArray placeMemoryArrayForward placeMemoryArrayControl
  placeMemoryTypedBase placeMemoryCodeLayout placeMemoryCopyEffect
  context compileEnv emitHelper emitHelperProps exprLoweringProps
  venomState venomInst venomExecSemantics freshWrites list arithmetic

Theorem typed_memory_sarray_slow_forward_sharp:
  compile_copy_sarray_typed cenv dst dt src st N sa = ((),sb) /\
  ~(type_memory_bytes cenv dt = type_memory_bytes cenv st /\
    ~is_abi_dynamic cenv.ce_struct_fields dt) /\
  typed_memory_child_forward_sharp cenv tenv ctx func dt /\
  type_widens_to tenv st dt /\
  evaluate_type tenv dt = SOME dtv /\ evaluate_type tenv st = SOME stv /\
  type_memory_bytes cenv dt = type_memory_size dtv /\
  type_memory_bytes cenv st = type_memory_size stv /\
  value_has_type (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs)) /\
  val_wf (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs)) /\
  value_has_type (ArrayTV stv (Fixed N)) (ArrayV (SArrayV kvs)) /\
  val_wf (ArrayTV stv (Fixed N)) (ArrayV (SArrayV kvs)) /\
  val_in_memory (ArrayTV stv (Fixed N)) (ArrayV (SArrayV kvs))
    (w2n sw) s.vs_memory /\
  (w2n sw + N * type_memory_size stv <= w2n dw \/
   w2n dw + N * type_memory_size dtv <= w2n sw) /\
  w2n sw + N * type_memory_size stv < dimword (:256) /\
  w2n dw + N * type_memory_size dtv < dimword (:256) /\
  N < dimword (:256) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. val_in_memory (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs))
        (w2n dw) t.vs_memory /\
      typed_copy_effect ctx func sa sb s t (w2n dw) (N * type_memory_size dtv)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all typed_memory_sarray_slow_compile >> strip_tac >>
  drule_all typed_copy_slow_array_control_layout >> strip_tac >>
  `(do so <- emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv st))];
       doff <- emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv dt))];
       sp <- emit_op ADD [src; so]; dp <- emit_op ADD [dst; doff];
       return (sp,dp) od) stb = ((sp,dp),b4)` by
    simp[comp_bind_def, comp_return_def] >>
  rpt (qpat_x_assum `fresh_label _ _ = _` kall_tac) >>
  qpat_x_assum `fresh_var _ = _` kall_tac >>
  rpt (qpat_x_assum `emit_inst _ _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `emit_op _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `new_block _ _ = _` kall_tac) >>
  qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` kall_tac >>
  `?u. typed_copy_effect ctx func sa sth s u (w2n dw) (N * type_memory_size dtv) /\
       lookup_var counter u = SOME (n2w 0) /\ u.vs_memory = s.vs_memory` by
    suspend "initial" >>
  `default_value stv = default_value dtv` by metis_tac[typed_memory_widening_defaults] >>
  qabbrev_tac `elem = \i. case ALOOKUP kvs i of NONE => default_value stv | SOME v => v` >>
  `!i. value_has_type stv (elem i) /\ val_wf stv (elem i) /\
       value_has_type dtv (elem i) /\ val_wf dtv (elem i)` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`value_has_type (ArrayTV dtv _) _`, `value_has_type (ArrayTV stv _) _`,
        `val_wf (ArrayTV dtv _) _`, `val_wf (ArrayTV stv _) _`,
        `evaluate_type tenv dt = _`, `evaluate_type tenv st = _`,
        `default_value stv = _`] >>
     simp[Abbr `elem`, NoAsms] >> rpt (first_x_assum kall_tac) >>
     simp[valueEncodingDefsTheory.val_wf_def] >> rpt strip_tac >>
     metis_tac[typed_memory_sparse_lookup_type, typed_memory_sparse_lookup_wf]) >>
  `?z. val_in_memory (ArrayTV stv (Fixed N)) (ArrayV (SArrayV kvs))
          (w2n sw) z.vs_memory /\
       (!j. j < N ==> val_in_memory dtv (elem j)
          (w2n dw + j * type_memory_size dtv) z.vs_memory) /\
       typed_copy_effect ctx func sa sth s z (w2n dw) (N * type_memory_size dtv) /\
       lookup_var counter z = SOME (n2w N)` by
    (irule typed_memory_array_iteration_forward >>
     qpat_assum `typed_copy_effect _ _ sa sth s u _ _` (irule_at Any) >>
     rpt (goal_assum (drule_at Any)) >> simp[] >>
     suspend "round") >>
  suspend "exit"
QED

Resume typed_memory_sarray_slow_forward_sharp[initial]:
  markerLib.RESUME_TAC >>
  `gas_marked_path F ctx func s 0
     (OK (jump_to hdr ((update_var counter 0w s) with
                       vs_inst_idx := s.vs_inst_idx + 1)))` by
    (irule typed_memory_array_init_forward >> simp[] >>
     qexistsl_tac [`id1`, `id2`] >> simp[]) >>
  qexists_tac `jump_to hdr ((update_var counter 0w s) with
                       vs_inst_idx := s.vs_inst_idx + 1)` >>
  gvs[typed_copy_effect_def, jump_to_def, update_var_def,
      venom_state_component_equality, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> metis_tac[]
QED

Resume typed_memory_sarray_slow_forward_sharp[round]:
  markerLib.RESUME_TAC >>
  simp[valueEncodingTheory.type_memory_size_def] >>
  rpt strip_tac >>
  `~a.vs_halted /\ a.vs_current_bb = hdr /\ a.vs_inst_idx = 0` by
    gvs[typed_copy_effect_def] >>
  drule_at (Pat `hbb.bb_instructions = _`) typed_memory_array_round_effect >>
  disch_then irule >> simp[eval_operand_def] >>
  qpat_assum `DROP _ ebb.bb_instructions = _` (irule_at Any) >>
  rpt (goal_assum (drule_at Any)) >> simp[eval_operand_def] >>
  rpt strip_tac >>
  irule typed_memory_array_element_forward_sharp >>
  qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _` (irule_at Any) >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  qexists_tac `sw` >>
  `eval_operand src a' = SOME sw /\ eval_operand dst a' = SOME dw` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`typed_copy_effect ctx func sa sth s a _ _`,
        `typed_copy_effect ctx func sa stb a a' _ _`,
        `eval_operand src s = SOME sw`, `eval_operand dst s = SOME dw`,
        `!x. src = Var x ==> _`, `!x. dst = Var x ==> _`] >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `src` >> Cases_on `dst` >>
     simp[eval_operand_def, typed_copy_effect_def, venom_state_component_equality] >>
     rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `i * type_memory_size stv + type_memory_size stv <= N * type_memory_size stv /\
   i * type_memory_size dtv + type_memory_size dtv <= N * type_memory_size dtv` by
    (`SUC i <= N` by decide_tac >>
     `SUC i * type_memory_size stv <= N * type_memory_size stv /\
      SUC i * type_memory_size dtv <= N * type_memory_size dtv` by simp[] >>
     qpat_x_assum `SUC i * type_memory_size stv <= _` mp_tac >>
     qpat_x_assum `SUC i * type_memory_size dtv <= _` mp_tac >>
     pure_rewrite_tac[MULT_CLAUSES] >> decide_tac) >>
  `val_in_memory stv (elem i) (w2n sw + i * type_memory_size stv) a.vs_memory` by
    (simp[Abbr `elem`, NoAsms] >> irule typed_memory_sarray_element >>
     rpt (goal_assum (drule_at Any))) >>
  gvs[typed_copy_effect_def] >> decide_tac
QED

Resume typed_memory_sarray_slow_forward_sharp[exit]:
  markerLib.RESUME_TAC >>
  `~z.vs_halted /\ z.vs_current_bb = hdr /\ z.vs_inst_idx = 0` by
    gvs[typed_copy_effect_def] >>
  `?t. typed_copy_effect ctx func sa sb z t (w2n dw) (N * type_memory_size dtv) /\
       lookup_var counter t = SOME (n2w N) /\ t.vs_memory = z.vs_memory` by
    (drule_at (Pat `hbb.bb_instructions = _`) typed_memory_array_condition_effect >>
     disch_then irule >> simp[] >>
     rpt (goal_assum (drule_at Any)) >> simp[eval_operand_def] >> metis_tac[]) >>
  qexists_tac `t` >> conj_tac
  >- (irule typed_memory_sarray_intro >> simp[] >>
      qpat_x_assum `!j. j < N ==> val_in_memory _ _ _ _` mp_tac >>
      simp[Abbr `elem`]) >>
  irule placeMemoryCopyEffectTheory.typed_copy_effect_then >>
  qexistsl_tac [`sa`, `sth`, `z`] >> simp[]
QED

Finalise typed_memory_sarray_slow_forward_sharp
