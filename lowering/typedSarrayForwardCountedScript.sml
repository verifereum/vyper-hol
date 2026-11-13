Theory typedSarrayForwardCounted
Ancestors
  placeMemoryTypedBase typedArraySemanticCounted typedArrayTraversalCounted placeMemoryArrayForward placeMemoryChildForward
  placeMemoryCodeLayout placeMemoryCopyEffect bodyMemAssignTopCopyPaths
  allocaHistory fragGasPathMem fragGasMode fragExecMem instMemFrontier
  typedArrayControlCounted venomExecSemantics venomState venomInst
  context compileEnv emitHelper emitHelperProps exprLoweringProps
  freshWrites ASCIInumbers list rich_list arithmetic


Theorem typed_memory_sarray_slow_forward_counted:
  compile_copy_sarray_typed cenv dst dt src st N sa = ((),sb) /\
  ~(type_memory_bytes cenv dt = type_memory_bytes cenv st /\
    ~is_abi_dynamic cenv.ce_struct_fields dt) /\
  (!sty dtyv styv value dop sop a b u dword sword.
    type_widens_to tenv sty dt /\
    evaluate_type tenv dt = SOME dtyv /\ evaluate_type tenv sty = SOME styv /\
    type_memory_bytes cenv dt = type_memory_size dtyv /\
    type_memory_bytes cenv sty = type_memory_size styv /\
    value_has_type dtyv value /\ val_wf dtyv value /\
    value_has_type styv value /\ val_wf styv value /\
    val_in_memory styv value (w2n sword) u.vs_memory /\
    (w2n sword + type_memory_size styv <= w2n dword \/
     w2n dword + type_memory_size dtyv <= w2n sword) /\
    w2n sword + type_memory_size styv < dimword (:256) /\
    w2n dword + type_memory_size dtyv < dimword (:256) /\
    compile_store_memory_typed cenv dop dt sop sty a = ((),b) /\
    (!x. dop = Var x ==> not_fresh_at a x) /\
    (!x. sop = Var x ==> not_fresh_at a x) /\
    eval_operand dop u = SOME dword /\ eval_operand sop u = SOME sword /\
    fn_has_code a b func /\ ~u.vs_halted /\
    u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts /\
    alloca_history func u /\ alloca_inv u /\
    w2n sword + type_memory_size styv <= u.vs_alloca_next /\
    w2n dword + type_memory_size dtyv <= u.vs_alloca_next ==>
    ?t. val_in_memory dtyv value (w2n dword) t.vs_memory /\
        typed_copy_effect ctx func a b u t (w2n dword) (type_memory_size dtyv) /\
        gas_path_mem ctx func u 0 (OK t) /\ alloca_history func t) /\
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
  alloca_history func s /\ alloca_inv s /\
  w2n sw + N * type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + N * type_memory_size dtv <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. val_in_memory (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs))
        (w2n dw) t.vs_memory /\
      typed_copy_effect ctx func sa sb s t (w2n dw) (N * type_memory_size dtv) /\
      gas_path_mem ctx func s 0 (OK t) /\ alloca_history func t
Proof
  strip_tac >>
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
       lookup_var counter u = SOME (n2w 0) /\ u.vs_memory = s.vs_memory /\
       gas_path_mem ctx func s 0 (OK u) /\ alloca_history func u` by
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
     simp[valueEncodingTheory.val_wf_def] >> rpt strip_tac >>
     metis_tac[typed_memory_sparse_lookup_type, typed_memory_sparse_lookup_wf]) >>
  `?z. val_in_memory (ArrayTV stv (Fixed N)) (ArrayV (SArrayV kvs))
          (w2n sw) z.vs_memory /\
       (!j. j < N ==> val_in_memory dtv (elem j)
          (w2n dw + j * type_memory_size dtv) z.vs_memory) /\
       typed_copy_effect ctx func sa sth s z (w2n dw) (N * type_memory_size dtv) /\
       lookup_var counter z = SOME (n2w N) /\
       gas_path_mem ctx func u 0 (OK z) /\ alloca_history func z` by
    (irule typed_memory_array_iteration_path_mem >>
     qpat_assum `typed_copy_effect _ _ sa sth s u _ _` (irule_at Any) >>
     rpt (goal_assum (drule_at Any)) >> simp[] >>
     suspend "round") >>
  suspend "exit"
QED

Resume typed_memory_sarray_slow_forward_counted[initial]:
  markerLib.RESUME_TAC >>
  `gas_path_mem ctx func s 0
     (OK (jump_to hdr ((update_var counter 0w s) with
                       vs_inst_idx := s.vs_inst_idx + 1)))` by
    (irule sarray_initial_path >> simp[] >> metis_tac[]) >>
  qexists `jump_to hdr ((update_var counter 0w s) with
                       vs_inst_idx := s.vs_inst_idx + 1)` >>
  `alloca_history func (jump_to hdr ((update_var counter 0w s) with
                       vs_inst_idx := s.vs_inst_idx + 1))` by
    (irule alloca_history_jump >> simp[jump_to_def, update_var_def] >>
     qexists `s` >> simp[]) >>
  gvs[typed_copy_effect_def, jump_to_def, update_var_def,
      venom_state_component_equality, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[gas_marked_path_def] >> drule gas_path_mem_exec >> simp[]
QED

Resume typed_memory_sarray_slow_forward_counted[round]:
  markerLib.RESUME_TAC >>
  simp[valueEncodingTheory.type_memory_size_def] >>
  rpt strip_tac >>
  `~a.vs_halted /\ a.vs_current_bb = hdr /\ a.vs_inst_idx = 0` by
    gvs[typed_copy_effect_def] >>
  drule_at (Pat `hbb.bb_instructions = _`) typed_memory_array_round_effect_counted >>
  disch_then irule >> simp[eval_operand_def] >>
  qpat_assum `DROP _ ebb.bb_instructions = _` (irule_at Any) >>
  rpt (goal_assum (drule_at Any)) >> simp[eval_operand_def] >>
  rpt strip_tac >>
  irule typed_memory_array_element_forward_counted >>
  qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _` (irule_at Any) >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  qexists `sw` >>
  `eval_operand src a' = SOME sw /\ eval_operand dst a' = SOME dw` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`typed_copy_effect ctx func sa sth s a _ _`,
        `typed_copy_effect ctx func sa stb a a' _ _`,
        `!x. src = Var x ==> _`, `!x. dst = Var x ==> _`,
        `eval_operand src s = _`, `eval_operand dst s = _`] >>
     rpt (pop_assum kall_tac) >>
     Cases_on `src` >> Cases_on `dst` >>
     simp[eval_operand_def, typed_copy_effect_def] >>
     rpt strip_tac >> fs[venom_state_component_equality] >> metis_tac[]) >>
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
  qpat_x_assum `!sty dtyv styv value dop sop aa bb uu dword sword. _` kall_tac >>
  gvs[typed_copy_effect_def, venom_state_component_equality,
      venomMemDefsTheory.alloca_inv_def,
      venomMemDefsTheory.allocas_non_overlapping_def,
      venomMemDefsTheory.alloca_next_valid_def] >>
  conj_tac >- (first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC
QED

Resume typed_memory_sarray_slow_forward_counted[exit]:
  markerLib.RESUME_TAC >> (
  `~z.vs_halted /\ z.vs_current_bb = hdr /\ z.vs_inst_idx = 0` by
    gvs[typed_copy_effect_def] >>
  `?t. typed_copy_effect ctx func sa sb z t (w2n dw) (N * type_memory_size dtv) /\
       lookup_var counter t = SOME (n2w N) /\ t.vs_memory = z.vs_memory /\
       gas_path_mem ctx func z 0 (OK t) /\ alloca_history func t` by
    (drule_at (Pat `hbb.bb_instructions = _`) typed_memory_array_condition_effect_counted >>
     disch_then irule >> simp[] >>
     rpt (goal_assum (drule_at Any)) >> simp[eval_operand_def] >> metis_tac[]) >>
  qexists `t` >> conj_tac
  >- (irule typed_memory_sarray_intro >> simp[] >>
      qpat_x_assum `!j. j < N ==> val_in_memory _ _ _ _` mp_tac >>
      simp[Abbr `elem`]) >>
  conj_tac
  >- (irule typed_copy_effect_then >> qexistsl [`sa`, `sth`, `z`] >> simp[]) >>
  simp[] >>
  `gas_path_mem ctx func s 0 (OK z)` by
    (qpat_assum `gas_path_mem ctx func s 0 (OK u)` mp_tac >>
     qpat_assum `gas_path_mem ctx func u 0 (OK z)` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[gas_path_mem_then, ADD_CLAUSES]) >>
  qpat_assum `gas_path_mem ctx func s 0 (OK z)` mp_tac >>
  qpat_assum `gas_path_mem ctx func z 0 (OK t)` mp_tac >>
  rpt (pop_assum kall_tac) >> metis_tac[gas_path_mem_then, ADD_CLAUSES])
QED

Finalise typed_memory_sarray_slow_forward_counted
