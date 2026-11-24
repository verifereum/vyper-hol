Theory bodyFullSubscriptFixedSelect
Ancestors
  bodyFullTargetArraySuffix bodyFullTargetArrayLoad bodyBinopFragMemory
  stmtReasonLitFragMemory
  exprSimArrayIndex exprLoweringProps emitHelperProps emitHelper freshWrites
  fragExec fragGasOriginPtr compileEnv ptrDiscipline venomInst venomState
  venomExecSemantics words rich_list list
  exprSimSubscriptArraySource exprSimSubscriptArraySuffix vyperArray
  overflowElimHelpers integer_word vyperState vyperValue finite_map
  exprSimVVFrame exprSimSubscriptArrayFramed loweringPosts context
  typedCopyLayoutPtr bodyPtrDefs bodyPtrBopHashFootprint exprSimCopy
  valueEncoding vyperLookupStorage vyperAssignPreservesType vyperTyping
  valueTypingMemoryProps exprSimMemDefs exprSimProps loweringStateRelDefs
  bodyFullTargetAttribute bodyFullUnwrapRun bodyPtrSignedConvertSourceFrame
  exprSimWordArgs exprSimHash exprSimDefs gasOutcomeFullCompose exprLowering
  vyperAST

Definition fixed_select_cuts_def:
  fixed_select_cuts fn sa sc sb <=>
    same_blocks sa sc /\ same_blocks sc sb /\
    sc.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sc /\
    sb.cs_current_insts = sc.cs_current_insts ++ emitted_insts sc sb /\
    fn_has_code sa sc fn /\ fn_has_code sc sb fn /\
    EVERY (\ins. ins.inst_opcode <> INVOKE /\ ins.inst_opcode <> GAS /\
                 ~is_terminator ins.inst_opcode) (emitted_insts sa sc) /\
    EVERY (\ins. ins.inst_opcode <> INVOKE /\ ins.inst_opcode <> GAS /\
                 ~is_terminator ins.inst_opcode) (emitted_insts sc sb)
End

(* The scalar rule observes the very result whose ghosts witness the path.
   Its observation can distinguish the address run from the bounds failure. *)
Definition fixed_select_scalar_intro_def:
  fixed_select_scalar_intro lo explicit ctx fn PG Obs <=>
    !sa sc sb s G tn idx len sgn bop dyn ws esz p b iw nw.
      array_bounds_check idx len sgn sa = ((),sc) /\
      array_elem_ptr bop idx dyn ws esz sc = (p,sb) /\
      eval_operand bop s = SOME b /\ eval_operand idx s = SOME iw /\
      eval_operand len s = SOME nw /\
      (!x. bop = Var x ==> not_fresh_at sa x) /\
      (!x. idx = Var x ==> not_fresh_at sa x) /\
      (!x. len = Var x ==> not_fresh_at sa x) /\
      op_taint tn bop = {} /\ op_taint tn idx = {} /\ op_taint tn len = {} /\
      op_prov G idx = NONE /\ op_prov G len = NONE /\
      allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
      fixed_select_cuts fn sa sc sb /\
      ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      ?t H tm.
        Obs sa sc sb s
          (if idx_in_range sgn iw nw then OK t else Abort Revert_abort t) /\
        (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
          (if idx_in_range sgn iw nw then OK t else Abort Revert_abort t,H,tm)) /\
        tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
        tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
        (!x. not_fresh_at sa x ==>
          FLOOKUP H x = FLOOKUP G x /\ FLOOKUP tm.t_var x = FLOOKUP tn.t_var x /\
          FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x) /\
        (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) =
          (if idx_in_range sgn iw nw then s else revert_state (set_returndata [] s)) /\
        (idx_in_range sgn iw nw ==>
          ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          eval_operand p t = SOME ((if dyn then b + n2w ws else b) + iw * n2w esz) /\
          op_prov H p = op_prov G bop /\ op_taint tm p = {})
End

Theorem fixed_select_scalar_true[local]:
  fixed_select_scalar_intro lo explicit ctx fn PG (\sa sc sb s r. T)
Proof
  simp[fixed_select_scalar_intro_def, fixed_select_cuts_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all array_tail_scalar_uniform >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >> simp[]
QED

(* Fixed-length indexing needs only the scalar check and address code.
   The same entry and exit ghosts work at each finite horizon. *)
Theorem fixed_select_counted[local]:
  fixed_select_scalar_intro lo explicit ctx fn PG Obs /\
  compile_array_subscript bop iop F n ws esz sgn loader sn = (dst,sb) /\
  fn_has_code sn sb fn /\
  eval_operand bop u = SOME a /\ eval_operand iop u = SOME iw /\
  op_taint tn bop = {} /\ op_taint tn iop = {} /\ op_prov G iop = NONE /\
  (!x. bop = Var x ==> not_fresh_at sn x) /\
  (!x. iop = Var x ==> not_fresh_at sn x) /\
  allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ ~u.vs_halted /\
  u.vs_current_bb = sn.cs_current_bb /\ u.vs_inst_idx = LENGTH sn.cs_current_insts /\
  alloca_history fn u ==>
  ?sc q Gq tq.
    array_bounds_check iop (Lit (n2w n)) sgn sn = ((),sc) /\
    array_elem_ptr bop iop F ws esz sc = (dst,sb) /\
    fixed_select_cuts fn sn sc sb /\
    Obs sn sc sb u
      (if idx_in_range sgn iw (n2w n) then OK q else Abort Revert_abort q) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (u,G,tn) []
      (if idx_in_range sgn iw (n2w n) then OK q else Abort Revert_abort q,Gq,tq)) /\
    (idx_in_range sgn iw (n2w n) ==>
      ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
      q.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history fn q /\
      eval_operand dst q = SOME (a + iw * n2w esz) /\
      op_prov Gq dst = op_prov G bop /\ op_taint tq dst = {} /\
      array_length_frame sn u G tn q Gq tq)
Proof
  strip_tac >>
  qpat_x_assum `_ = (dst,sb)` mp_tac >>
  simp[compile_array_subscript_split, comp_bind_def, comp_ignore_bind_def,
      comp_return_def] >> pairarg_tac >> simp[] >> strip_tac >>
  rename1 `array_bounds_check _ _ _ sn = (unit,sc)` >>
  Cases_on `unit` >> gvs[] >>
  `same_blocks sn sc /\
   sc.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sc /\
   EVERY (\ins. ins.inst_opcode <> INVOKE /\ ins.inst_opcode <> GAS /\
                ~is_terminator ins.inst_opcode) (emitted_insts sn sc) /\
   EVERY (\ins. ins.inst_opcode <> ALLOCA) (emitted_insts sn sc)` by
    (qpat_x_assum `array_bounds_check _ _ _ _ = _` mp_tac >>
     simp[array_bounds_check_def, comp_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
     qpat_x_assum `array_bounds_valid _ _ _ _ = _` mp_tac >>
     simp[array_bounds_valid_def, comp_bind_def] >>
     Cases_on `sgn` >> simp[comp_return_def] >>
     rpt (pairarg_tac >> simp[]) >> strip_tac >>
     imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
     imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
     rpt (qpat_x_assum `_.cs_current_insts = _.cs_current_insts ++ emitted_insts _ _` kall_tac) >>
     gvs[same_blocks_def] >>
     simp[emitted_insts_def, DROP_LENGTH_APPEND, APPEND_ASSOC,
          mk_inst_def, is_terminator_def]) >>
  `same_blocks sc sb /\
   sb.cs_current_insts = sc.cs_current_insts ++ emitted_insts sc sb /\
   EVERY (\ins. ins.inst_opcode <> INVOKE /\ ins.inst_opcode <> GAS /\
                ~is_terminator ins.inst_opcode) (emitted_insts sc sb) /\
   EVERY (\ins. ins.inst_opcode <> ALLOCA) (emitted_insts sc sb)` by
    (qpat_x_assum `sc.cs_current_insts = sn.cs_current_insts ++ _` kall_tac >>
     qpat_x_assum `array_elem_ptr _ _ _ _ _ _ = _` mp_tac >>
     simp[array_elem_ptr_def, comp_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> simp[]) >> strip_tac >>
     imp_res_tac emit_op_extends >> imp_res_tac emitted_insts_emit_op >>
     rpt (qpat_x_assum `_.cs_current_insts = _.cs_current_insts ++ emitted_insts _ _` kall_tac) >>
     gvs[same_blocks_def] >>
     simp[emitted_insts_def, DROP_LENGTH_APPEND, APPEND_ASSOC,
          mk_inst_def, is_terminator_def]) >>
  `cs_extends sn sc /\ cs_extends sc sb` by
     fs[cs_extends_def, same_blocks_def, IS_PREFIX_APPEND] >>
  drule_all_then strip_assume_tac fn_has_code_split >>
  `eval_operand (Lit (n2w n)) u = SOME (n2w n) /\
   (!x. Lit (n2w n) = Var x ==> not_fresh_at sn x) /\
   op_prov G (Lit (n2w n)) = NONE /\ op_taint tn (Lit (n2w n)) = {}` by
    simp[eval_operand_def, op_prov_def, op_taint_def] >>
  `fixed_select_cuts fn sn sc sb` by simp[fixed_select_cuts_def] >>
  qpat_x_assum `fixed_select_scalar_intro _ _ _ _ _ _`
    (drule_all o REWRITE_RULE[fixed_select_scalar_intro_def]) >>
  disch_then (qx_choosel_then [`q`,`Gq`,`tq`] strip_assume_tac) >>
  qexistsl [`q`,`Gq`,`tq`] >> simp[] >> strip_tac >>
  `q.vs_allocas = u.vs_allocas /\ q.vs_current_bb = u.vs_current_bb` by
    fs[venom_state_component_equality] >>
  `alloca_history fn q` by
    (`emitted_insts sn sb = emitted_insts sn sc ++ emitted_insts sc sb` by
       metis_tac[emitted_insts_append] >>
     `sb.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sb /\
      EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sn sb)` by
       simp[APPEND_ASSOC] >>
     `sb.cs_current_bb = sn.cs_current_bb` by fs[same_blocks_def] >>
     drule_all_then strip_assume_tac fn_has_code_code >> fs[IS_PREFIX_APPEND] >>
     `q.vs_inst_idx = u.vs_inst_idx + LENGTH (emitted_insts sn sb)` by simp[] >>
     `alloca_history fn (q with vs_inst_idx := q.vs_inst_idx)` suffices_by simp[] >>
     qpat_assum `q.vs_inst_idx = u.vs_inst_idx + _` SUBST1_TAC >>
     irule alloca_history_no_alloca_slice >> simp[] >> qexistsl [`bb`,`l`] >> simp[]) >>
  fs[array_length_frame_def, lookup_var_def, venom_state_component_equality]
QED

(* Sparse fixed arrays count absent entries in their declared length. *)
Theorem fixed_select_source_bounds[local]:
  n < dimword (:256) /\ i = (if sgn then w2i iw else &(w2n iw)) ==>
  if idx_in_range sgn iw (n2w n) then
    0 <= i /\ Num i < n /\ iw = n2w (Num i) /\
    (?v. array_index (ArrayTV etv (Fixed n)) (SArrayV kvs) i = SOME v)
  else
    evaluate_subscripts (ArrayTV etv (Fixed n)) (ArrayV (SArrayV kvs))
      [ValueSubscript (IntV i)] = INR (RuntimeError "evaluate_subscripts array_index")
Proof
  strip_tac >>
  `idx_in_range sgn iw (n2w n) <=> 0 <= i /\ i < &n` by
    (drule idx_in_range_integer >> disch_then (qspecl_then [`iw`,`sgn`] mp_tac) >> simp[]) >>
  Cases_on `idx_in_range sgn iw (n2w n)`
  >- (`0 <= i /\ i < &n` by metis_tac[] >>
      `Num i < n` by
        (qpat_assum `0 <= i` mp_tac >> qpat_assum `i < &n` mp_tac >>
         rpt (pop_assum kall_tac) >> intLib.COOPER_TAC) >>
      `iw = n2w (Num i)` by
        (Cases_on `sgn` >> gvs[] >>
         drule overflowElimHelpersTheory.nonneg_w2i_eq_w2n >>
         disch_then (fn th => once_rewrite_tac [GSYM th]) >> simp[]) >>
      `valid_index (ArrayTV etv (Fixed n)) (SArrayV kvs) i` by
        simp[valid_index_def,vyperValueOperationTheory.array_length_def,
             IgnAsm `i = if _ then _ else _`] >>
      drule array_index_valid >>
      Cases_on `array_index (ArrayTV etv (Fixed n)) (SArrayV kvs) i` >>
      simp[IgnAsm `i = if _ then _ else _`]) >>
  simp[IgnAsm `idx_in_range _ _ _ <=> _`] >> irule evaluate_array_subscript_oob >>
  simp[valid_index_def,vyperValueOperationTheory.array_length_def] >> metis_tac[]
QED

Theorem fixed_select_source_result[local]:
  evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) = SOME (ArrayTV etv (Fixed n)) /\
  (r = Value (ArrayV (SArrayV kvs)) \/
   ?id path. r = PlaceR (MemoryPlace id path) /\
     runtime_place_typed cx fin (MemoryPlace id path) (ArrayTV etv (Fixed n)) /\
     popped_keys_indexed fin.scopes) /\
  read_result cx r fin = (INL (ArrayV (SArrayV kvs)),fin) ==>
  (!i v. evaluate_subscripts (ArrayTV etv (Fixed n)) (ArrayV (SArrayV kvs))
     [ValueSubscript (IntV i)] = INL v ==>
   ?child. select_result cx (ArrayT et (Fixed n)) r (ValueSubscript (IntV i)) fin = (INL child,fin) /\
           read_result cx child fin = (INL v,fin) /\
           (r = Value (ArrayV (SArrayV kvs)) ==> child = Value v) /\
           (!id path. child = PlaceR (MemoryPlace id path) <=>
             ?pre. path = pre ++ [ValueSubscript (IntV i)] /\ r = PlaceR (MemoryPlace id pre)) /\
           (!v. child = Value v ==> ?a. r = Value a)) /\
  (!i err. evaluate_subscripts (ArrayTV etv (Fixed n)) (ArrayV (SArrayV kvs))
     [ValueSubscript (IntV i)] = INR err ==>
   select_result cx (ArrayT et (Fixed n)) r (ValueSubscript (IntV i)) fin = (INR (Error err),fin))
Proof
  strip_tac
  >- (drule select_value_result >> simp[bind_def,lift_sum_def,read_result_def,return_def,raise_def]) >>
  gvs[] >> conj_tac
  >- (rpt gen_tac >> disch_tac >>
      drule_all_then strip_assume_tac select_fixed_memory_read >> simp[APPEND_11] >> metis_tac[]) >>
  rpt strip_tac >> irule select_nonstorage_place_error >> simp[] >> metis_tac[]
QED

(* The selected address is the same address used by the sparse representation,
   including entries represented by the default value. *)
Theorem fixed_select_layout[local]:
  evaluate_type (get_tenv cx) et = SOME etv /\
  value_has_type (ArrayTV etv (Fixed n)) (ArrayV (SArrayV kvs)) /\
  array_index (ArrayTV etv (Fixed n)) (SArrayV kvs) i = SOME v /\
  0 <= i /\ Num i < n /\
  j = Num i * type_memory_size etv /\
  w2n (a:256 word) + n * type_memory_size etv < dimword (:256) /\
  (!m. mem_agree_outside tn.t_mem u.vs_memory m ==>
       val_in_memory (ArrayTV etv (Fixed n)) (ArrayV (SArrayV kvs)) (w2n a) m) ==>
  value_has_type etv v /\ val_wf etv v /\ j + type_memory_size etv <= n * type_memory_size etv /\
  w2n (a + n2w j) = w2n a + j /\
  (!m. mem_agree_outside tn.t_mem u.vs_memory m ==> val_in_memory etv v (w2n a + j) m)
Proof
  strip_tac >>
  `well_formed_type_value etv` by metis_tac[evaluate_type_well_formed] >>
  `value_has_type etv v` by metis_tac[array_index_has_type] >>
  `val_wf etv v /\ val_wf (ArrayTV etv (Fixed n)) (ArrayV (SArrayV kvs))` by
    simp[value_has_type_memory_wf] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- metis_tac[array_index_element_end_bound,arithmeticTheory.ADD_COMM] >>
  conj_tac
  >- (qpat_assum `j = _` SUBST1_TAC >>
      irule fixed_array_element_nonwrapping >> qexistsl [`SArrayV kvs`,`n`,`v`] >>
      simp[val_footprint_def,type_memory_size_def]) >>
  `v = (case ALOOKUP kvs (Num i) of NONE => default_value etv | SOME x => x)` by
    (Cases_on `ALOOKUP kvs (Num i)` >> fs[array_index_sarray]) >>
  qpat_assum `j = _` SUBST1_TAC >> rpt strip_tac >>
  irule sarray_in_memory_robust_element >> qexistsl [`n`,`kvs`,`u.vs_memory`,`tn`] >> simp[]
QED

Theorem fixed_select_place_ptr[local]:
  (r = Value a \/ ?id path. r = PlaceR (MemoryPlace id path)) /\
  (!id path. r = PlaceR (MemoryPlace id path) ==>
    place_ptr_rel ce cx u r w (SOME LocMemory) (Type (ArrayT et (Fixed n)))) /\
  (!id path. child = PlaceR (MemoryPlace id path) <=>
    ?pre. path = pre ++ [ValueSubscript (IntV i)] /\ r = PlaceR (MemoryPlace id pre)) /\
  (r = Value a ==> ?v. child = Value v) /\
  mem_step_offset (ArrayTV etv (Fixed n)) (ValueSubscript (IntV i)) = SOME (j,etv) /\
  evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) = SOME (ArrayTV etv (Fixed n)) /\
  eval_operand dst q = SOME (w + n2w j) /\
  local_ptrs_reserved ce sn /\ array_length_frame sn u (G : string |-> num # num) tn q Gq tq ==>
  vv_place_ptr ce cx fin q child (LocatedValue et (mk_ptr dst LocMemory))
Proof
  strip_tac
  >- (first_x_assum drule >> strip_tac >> simp[vv_place_ptr_def]) >>
  qpat_x_assum `!id path. _ ==> place_ptr_rel _ _ _ _ _ _ _` (mp_tac o SPEC_ALL) >>
  simp[place_ptr_rel_def] >> strip_tac >>
  `child = PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)]))` by
    (first_x_assum (qspecl_then [`id`,`path ++ [ValueSubscript (IntV i)]`] mp_tac) >> simp[]) >>
  rename1 `FLOOKUP ce.ce_vars id = SOME (PtrVar (Var reg) sz)` >>
  `mem_path_offset tv0 (path ++ [ValueSubscript (IntV i)]) = SOME (k+j,etv)` by
    metis_tac[mem_path_offset_snoc,optionTheory.SOME_11] >>
  `lookup_var reg q = SOME b` by
    (fs[array_length_frame_def,local_ptrs_reserved_def] >> metis_tac[]) >>
  simp[vv_place_ptr_def,mk_ptr_def] >>
  simp[GSYM WORD_ADD_ASSOC,word_add_n2w,arithmeticTheory.ADD_COMM]
QED

(* The tail changes only variables and PC, preserving all reserved pointers. *)
Theorem fixed_select_readonly[local]:
  array_length_frame sn u G tn q Gq tq /\ local_ptrs_reserved ce sn ==>
  q = u with <|vs_vars := q.vs_vars; vs_inst_idx := q.vs_inst_idx|> /\
  q.vs_memory = u.vs_memory /\ q.vs_allocas = u.vs_allocas /\
  q.vs_alloca_next = u.vs_alloca_next /\ tq.t_mem = tn.t_mem /\
  (!bop. (!x. bop = Var x ==> not_fresh_at sn x) ==> eval_operand bop q = eval_operand bop u) /\
  (!fin name b sz. local_region ce fin.scopes q name b sz <=>
                   local_region ce fin.scopes u name b sz)
Proof
  strip_tac >>
  `q = u with <|vs_vars := q.vs_vars; vs_inst_idx := q.vs_inst_idx|>` by
    (qpat_assum `array_length_frame _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [array_length_frame_def]) >>
     strip_tac >> qpat_assum `_ = u` (fn th =>
       CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM th]))) >> simp[]) >>
  `q.vs_labels = u.vs_labels /\ q.vs_memory = u.vs_memory /\
   q.vs_allocas = u.vs_allocas /\ q.vs_alloca_next = u.vs_alloca_next` by
    (qpat_assum `q = u with <|vs_vars := _; vs_inst_idx := _|>` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  fs[array_length_frame_def] >> conj_tac
  >- (Cases >> simp[eval_operand_def]) >>
  `!x. not_fresh_at sn x ==> lookup_var x q = lookup_var x u` by simp[] >>
  rpt gen_tac >> irule copy_buffer_local_region_frame >> qexists `sn` >> simp[]
QED

(* Project the same child from the parent region at the index endpoint. *)
Theorem fixed_select_child_region[local]:
  !av v dw.
  vv_at ce cx (ArrayT et (Fixed n)) sa sn fin r (LocatedValue t (mk_ptr bop LocMemory)) u /\
  (!v. r = Value v ==> vv_own ce cx (ArrayT et (Fixed n)) sa sn fin r
                          (LocatedValue t (mk_ptr bop LocMemory)) u) /\
  evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) = SOME (ArrayTV etv (Fixed n)) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  read_result cx r fin = (INL (ArrayV av),fin) /\
  read_result cx child fin = (INL v,fin) /\ val_wf etv v /\
  mem_step_offset (ArrayTV etv (Fixed n)) (ValueSubscript (IntV i)) = SOME (j,etv) /\
  (!id path. child = PlaceR (MemoryPlace id path) <=>
    ?pre. path = pre ++ [ValueSubscript (IntV i)] /\ r = PlaceR (MemoryPlace id pre)) /\
  (!v. child = Value v ==> ?a. r = Value a) /\
  eval_operand bop u = SOME w /\ eval_operand bop q = SOME w /\
  eval_operand dst q = SOME dw /\ w2n dw = w2n w + j /\
  j + type_memory_size etv <= n * type_memory_size etv /\
  q.vs_allocas = u.vs_allocas /\ sn.cs_next_id <= sb.cs_next_id /\
  (!nm b sz. local_region ce fin.scopes q nm b sz <=> local_region ce fin.scopes u nm b sz) ==>
  vv_at ce cx et sa sb fin child (LocatedValue et (mk_ptr dst LocMemory)) q /\
  (!v. child = Value v ==> vv_own ce cx et sa sb fin child (LocatedValue et (mk_ptr dst LocMemory)) q)
Proof
  rpt gen_tac >> strip_tac >>
  `vv_at ce cx (ArrayT et (Fixed n)) sa sb fin r (LocatedValue t (mk_ptr bop LocMemory)) q` by
    (irule vv_at_vars_frame >> qexistsl [`u`,`sn`] >> simp[vv_operand_def,mk_ptr_def]) >>
  conj_tac
  >- (irule vv_at_fixed_array_element >>
      qexistsl [`t`,`av`,`dw`,`etv`,`i`,`j`,`n`,`mk_ptr bop LocMemory`,`r`,`v`,`w`] >>
      simp[mk_ptr_def]) >>
  rpt strip_tac >>
  `?a. r = Value a` by metis_tac[] >>
  `vv_own ce cx (ArrayT et (Fixed n)) sa sb fin r (LocatedValue t (mk_ptr bop LocMemory)) q` by
    (irule vv_own_vars_frame >> qexistsl [`u`,`sn`] >> simp[vv_operand_def,mk_ptr_def]) >>
  `val_footprint etv v <= type_memory_size etv` by simp[val_footprint_le] >>
  `j + val_footprint etv v <= val_footprint (ArrayTV etv (Fixed n)) (ArrayV av)` by
    (`val_footprint (ArrayTV etv (Fixed n)) (ArrayV av) = n * type_memory_size etv` by
       simp[val_footprint_def,type_memory_size_def] >> decide_tac) >>
  irule vv_own_memory_slice >>
  goal_assum (drule_at (Pat `vv_own _ _ _ _ _ _ _ _ _`)) >> simp[]
QED

(* Robust contents and byte capacity at the projected address. *)
Theorem fixed_select_child_bytes[local]:
  evaluate_type (get_tenv cx) et = SOME etv /\
  value_has_type etv v /\ val_wf etv v /\
  read_result cx child fin = (INL v,fin) /\
  eval_operand dst q = SOME dw /\ w2n dw = w2n (w:256 word) + j /\
  (!m. mem_agree_outside tq.t_mem q.vs_memory m ==> val_in_memory etv v (w2n dw) m) /\
  j + type_memory_size etv <= n * type_memory_size etv /\
  (type_memory_size etv <> 0 ==> w2n w + n * type_memory_size etv <= q.vs_alloca_next) /\
  (type_memory_size etv <> 0 ==>
   ?b sz. op_prov Gq dst = SOME (b,sz) /\ b <= w2n w /\
          w2n w + n * type_memory_size etv <= b + sz) /\
  op_taint tq dst = {} /\ type_memory_bytes ce et = type_memory_size etv ==>
  vv_holds ce cx et child (LocatedValue et (mk_ptr dst LocMemory)) fin q /\
  vv_store_bound cx et et fin child (LocatedValue et (mk_ptr dst LocMemory)) q /\
  ptr_vv_ok cx et child (LocatedValue et (mk_ptr dst LocMemory)) fin Gq tq q /\
  ptr_buf_ok ce (Subscript et obj idx) dst Gq q
Proof
  strip_tac >>
  `val_store_size etv v <= type_memory_size etv /\
   val_footprint etv v <= type_memory_size etv` by simp[val_store_size_le,val_footprint_le] >>
  `val_in_memory etv v (w2n dw) q.vs_memory` by fs[mem_agree_outside_def] >>
  conj_tac
  >- (simp[vv_holds_def,mk_ptr_def] >> strip_tac >>
      drule_all val_in_memory_word_type >> simp[]) >>
  `type_memory_size etv <> 0 ==> w2n dw + type_memory_size etv <= q.vs_alloca_next` by decide_tac >>
  conj_tac >- (simp[vv_store_bound_def,mk_ptr_def] >> decide_tac) >>
  `type_memory_size etv <> 0 ==>
    ?x b sz. dst = Var x /\ FLOOKUP Gq x = SOME (b,sz) /\
             b <= w2n dw /\ w2n dw + type_memory_size etv <= b + sz` by
    (strip_tac >> Cases_on `dst` >> gvs[op_prov_def] >>
     qexistsl [`b`,`sz`] >> simp[] >> decide_tac) >>
  conj_tac
  >- (simp[ptr_vv_ok_def,mk_ptr_def,ptr_mem_ok_def,IgnAsm `w2n dw = _`] >>
      strip_tac >> `type_memory_size etv <> 0` by decide_tac >>
      first_x_assum drule >> strip_tac >> qexistsl [`x`,`b`,`sz`] >> simp[] >> decide_tac) >>
  simp[ptr_buf_ok_def,exprLoweringTheory.lowered_value_type_def,vyperASTTheory.expr_type_def] >>
  gvs[]
QED

Theorem fixed_select_child_post[local]:
  stmt_state_rel H ctx fn ce cx fin u /\ storage_well_formed_on cx fin (FST H) /\
  wb_frame ce es fin sa s0 u /\
  (~expr_has_effect (Subscript et obj idx) ==> pure_frame ce fn es sa s0 u) /\
  ghost_inv_at D lo d ce cx fin G tn u /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved ce sn /\ sa.cs_next_var <= sn.cs_next_var /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
  array_length_frame sn u G tn q Gq tq /\
  q = u with <|vs_vars := q.vs_vars; vs_inst_idx := q.vs_inst_idx|> /\
  vv_holds ce cx et child (LocatedValue et (mk_ptr dst LocMemory)) fin q /\
  vv_at ce cx et sa sb fin child (LocatedValue et (mk_ptr dst LocMemory)) q /\
  vv_place_ptr ce cx fin q child (LocatedValue et (mk_ptr dst LocMemory)) ==>
  vv_post H ctx fn ce cx (Subscript et obj idx) es sa sb s0 fin
    child (LocatedValue et (mk_ptr dst LocMemory)) q /\
  ghost_inv_at D lo d ce cx fin Gq tq q /\
  ghost_kept_at lo ce es sa G0 tn0 s0 Gq tq
Proof
  strip_tac >>
  `q.vs_memory = u.vs_memory /\ q.vs_allocas = u.vs_allocas` by
    (qpat_assum `q = u with <|vs_vars := _; vs_inst_idx := _|>`
      (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `!x. not_fresh_at sn x ==> lookup_var x q = lookup_var x u /\
     FLOOKUP Gq x = FLOOKUP G x /\ op_taint tq (Var x) = op_taint tn (Var x)` by
    fs[array_length_frame_def,op_taint_def] >>
  conj_tac
  >- (`stmt_state_rel H ctx fn ce cx fin q` by
        (irule stmt_state_rel_readonly_vars_pc >> (metis_tac[])) >>
      `wb_frame ce es fin sa s0 q` by
        (irule wb_frame_readonly_tail >> simp[] >> metis_tac[]) >>
      `~expr_has_effect (Subscript et obj idx) ==> pure_frame ce fn es sa s0 q` by
        (strip_tac >> irule pure_frame_mem_tail >> qexists `u` >> simp[]) >>
      irule vv_post_frame_intro >> gvs[expr_type_def,mk_ptr_def]) >>
  conj_tac
  >- (irule ghost_inv_at_fresh_write >> qexistsl [`G`,`u`,`sn`,`tn`] >>
      simp[] >> fs[array_length_frame_def] >>
      qpat_assum `q = u with <|vs_vars := _; vs_inst_idx := _|>`
        (fn th => once_rewrite_tac [th]) >> simp[]) >>
  irule ghost_kept_at_clean_suffix >> qexistsl [`G`,`tn`] >>
  fs[array_length_frame_def,op_taint_def] >> metis_tac[not_fresh_at_mono]
QED

(* Selection uses the fixed array representation at fin, after all index
   effects. The prefix facts are restricted to the same source trace. *)
Theorem subscript_fixed_memory_select_observed:
  fixed_select_scalar_intro lo explicit ctx fn PG Obs /\
  compile_array_subscript bop iop F n ws (type_memory_bytes ce et)
    (is_signed_type (expr_type idx)) loader sn = (dst,sb) /\
  fn_has_code sn sb fn /\
  eval_operand bop u = SOME w /\ eval_operand iop u = SOME iw /\
  op_taint tn bop = {} /\ op_taint tn iop = {} /\ op_prov G iop = NONE /\
  (!x. bop = Var x ==> not_fresh_at sn x) /\
  (!x. iop = Var x ==> not_fresh_at sn x) /\
  allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ ~u.vs_halted /\
  u.vs_current_bb = sn.cs_current_bb /\ u.vs_inst_idx = LENGTH sn.cs_current_insts /\
  alloca_history fn u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
  local_ptrs_reserved ce sn /\ sa.cs_next_var <= sn.cs_next_var /\ sn.cs_next_id <= sb.cs_next_id /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  storage_trace_domain cx st0 fin.storage_trace /\ fin.gas_obs = [] /\
  i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw)) /\
  n < dimword (:256) /\ type_memory_bytes ce et = type_memory_size etv /\
  evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) = SOME (ArrayTV etv (Fixed n)) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  value_has_type (ArrayTV etv (Fixed n)) (ArrayV (SArrayV kvs)) /\
  (r = Value (ArrayV (SArrayV kvs)) \/
   ?id path. r = PlaceR (MemoryPlace id path) /\
     runtime_place_typed cx fin (MemoryPlace id path) (ArrayTV etv (Fixed n)) /\
     popped_keys_indexed fin.scopes) /\
  read_result cx r fin = (INL (ArrayV (SArrayV kvs)),fin) /\
  (!id path. r = PlaceR (MemoryPlace id path) ==>
    place_ptr_rel ce cx u r w (SOME LocMemory) (Type (ArrayT et (Fixed n)))) /\
  vv_at ce cx (ArrayT et (Fixed n)) sa sn fin r (LocatedValue t (mk_ptr bop LocMemory)) u /\
  (!v. r = Value v ==> vv_own ce cx (ArrayT et (Fixed n)) sa sn fin r
                          (LocatedValue t (mk_ptr bop LocMemory)) u) /\
  w2n w + n * type_memory_size etv < dimword (:256) /\
  (!m. mem_agree_outside tn.t_mem u.vs_memory m ==>
    val_in_memory (ArrayTV etv (Fixed n)) (ArrayV (SArrayV kvs)) (w2n w) m) /\
  (type_memory_size etv <> 0 ==> w2n w + n * type_memory_size etv <= u.vs_alloca_next) /\
  (type_memory_size etv <> 0 ==>
   ?b sz. op_prov G bop = SOME (b,sz) /\ b <= w2n w /\
          w2n w + n * type_memory_size etv <= b + sz) /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    stmt_state_rel H ctx fn ce cx fin u /\ storage_well_formed_on cx fin (FST H) /\
    wb_frame ce es fin sa s0 u /\
    (~expr_has_effect (Subscript et obj idx) ==> pure_frame ce fn es sa s0 u) /\
    ghost_inv_at (DF H) lo d ce cx fin G tn u) ==>
  ?sc res q Gq tq.
    let sgn = is_signed_type (expr_type idx) in
    let rr = if idx_in_range sgn iw (n2w n) then OK q else Abort Revert_abort q in
    array_bounds_check iop (Lit (n2w n)) sgn sn = ((),sc) /\
    array_elem_ptr bop iop F ws (type_memory_bytes ce et) sc = (dst,sb) /\
    fixed_select_cuts fn sn sc sb /\
    Obs sn sc sb u rr /\
    (!tail. select_result cx (ArrayT et (Fixed n)) r (ValueSubscript (IntV i))
      (fin with gas_obs := tail) = (res,fin with gas_obs := tail)) /\
    storage_trace_domain cx st0 fin.storage_trace /\
    (!H. valid_horizon cx st0 H fin.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (u,G,tn) [] (rr,Gq,tq) /\
      ((?z. rr = OK z /\
        (\H res ee Gz tnz z. ?child. res = INL child /\
       vv_post H ctx fn ce cx (Subscript et obj idx) es sa sb s0 ee
         child (LocatedValue et (mk_ptr dst LocMemory)) z /\
       vv_store_bound cx (post_value_type ce (Subscript et obj idx))
         (lowered_value_type ce (Subscript et obj idx)) ee
         child (LocatedValue et (mk_ptr dst LocMemory)) z /\
       z.vs_current_bb = sb.cs_current_bb /\
       z.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history fn z /\
       (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
       s0.vs_alloca_next <= z.vs_alloca_next /\
       ghost_inv_at (DF H) lo d ce cx ee Gz tnz z /\
       ptr_vv_ok cx (post_value_type ce (Subscript et obj idx))
         child (LocatedValue et (mk_ptr dst LocMemory)) ee Gz tnz z /\
       (!v. child = Value v /\ ~is_word_type (post_value_type ce (Subscript et obj idx)) /\
          ~is_bytestring_type (post_value_type ce (Subscript et obj idx)) ==>
          vv_own ce cx (post_value_type ce (Subscript et obj idx)) sa sb ee
            child (LocatedValue et (mk_ptr dst LocMemory)) z /\
          (!t' p'. LocatedValue et (mk_ptr dst LocMemory) = LocatedValue t' p' ==>
                   p'.ptr_location = LocMemory)) /\
       (ce.ce_is_ctor /\ vv_location (LocatedValue et (mk_ptr dst LocMemory)) = SOME LocCode ==>
        ?v. read_result cx child ee = (INL v,ee) /\
            !rt a. evaluate_type (get_tenv cx) (post_value_type ce (Subscript et obj idx)) = SOME rt /\
              eval_operand (vv_operand (LocatedValue et (mk_ptr dst LocMemory))) z = SOME a ==>
              w2n a + type_memory_size rt <= lo /\
              (!mem. mem_agree_outside tnz.t_mem z.vs_memory mem ==>
                val_in_memory rt v (w2n a) mem)) /\
       (!t' op. LocatedValue et (mk_ptr dst LocMemory) = StackValue t' op /\
          ~is_word_type (post_value_type ce (Subscript et obj idx)) ==>
          ptr_buf_ok ce (Subscript et obj idx) op Gz z) /\
       (!t' p'. LocatedValue et (mk_ptr dst LocMemory) = LocatedValue t' p' /\
          p'.ptr_location = LocMemory ==>
          ptr_buf_ok ce (Subscript et obj idx) p'.ptr_operand Gz z) /\
       ghost_kept_at lo ce es sa G0 tn0 s0 Gz tnz) H res fin Gq tq z) \/
       (exit_result rr /\ expr_exit res rr /\ halt_exit H cx fin res rr /\
        (ctx_has_dalloca ctx ==> !z. rr = Halt z ==> allocas_below_fmp z))))
Proof
  disch_then (EVERY o map assume_tac o CONJUNCTS) >>
  drule_all fixed_select_counted >>
  disch_then (qx_choosel_then [`sc`,`q`,`Gq`,`tq`] strip_assume_tac) >>
  (qpat_assum `n < dimword (:256)`
    (mp_then (Pos hd) mp_tac fixed_select_source_bounds) >>
   disch_then (qspecl_then [`is_signed_type (expr_type idx)`,`kvs`,`iw`,`i`,`etv`] mp_tac)) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_tac >> qpat_x_assum `i = if _ then _ else _` kall_tac >>
  drule_all_then strip_assume_tac fixed_select_source_result >>
  `!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)` by
    (qpat_assum `r = Value _ \/ _` strip_assume_tac >> simp[]) >>
  qexistsl [`sc`,
    `FST (select_result cx (ArrayT et (Fixed n)) r (ValueSubscript (IntV i)) fin)`,
    `q`,`Gq`,`tq`] >>
  simp[LET_THM, IgnAsm `i = _`] >>
  Cases_on `idx_in_range (is_signed_type (expr_type idx)) iw (n2w n)`
  >- (qpat_x_assum `if idx_in_range _ _ _ then _ else _` mp_tac >>
      asm_rewrite_tac[] >> strip_tac >>
      qpat_x_assum `idx_in_range _ _ _ ==> _` (drule_then strip_assume_tac) >>
      `evaluate_subscripts (ArrayTV etv (Fixed n)) (ArrayV (SArrayV kvs))
          [ValueSubscript (IntV i)] = INL v` by simp[evaluate_array_subscript_result,IgnAsm `i = _`] >>
      qpat_assum `!i v. _ = INL v ==> _` (drule_then strip_assume_tac) >>
      conj_tac
      >- (gen_tac >> irule select_result_nonstorage_gas_obs >> simp[IgnAsm `i = _`]) >>
      qabbrev_tac `j = Num i * type_memory_size etv` >>
      `j = Num i * type_memory_size etv` by simp[Abbr `j`] >>
      drule_all_then strip_assume_tac fixed_select_layout >>
      `mem_step_offset (ArrayTV etv (Fixed n)) (ValueSubscript (IntV i)) = SOME (j,etv)` by
        asm_rewrite_tac[mem_step_offset_def] >>
      `eval_operand dst q = SOME (w + n2w j)` by
        (qpat_assum `eval_operand dst q = SOME (w + _)` mp_tac >>
         asm_rewrite_tac[word_mul_n2w]) >>
      drule_all_then strip_assume_tac fixed_select_readonly >>
      qpat_assum `!f name b sz. local_region _ f.scopes _ _ _ _ <=> _`
        (qspec_then `fin` assume_tac) >>
      `eval_operand bop q = SOME w` by
        (qpat_assum `!op. _ ==> eval_operand op q = _` (qspec_then `bop` mp_tac) >>
         disch_then (drule_then SUBST1_TAC) >> first_assum ACCEPT_TAC) >>
      `vv_place_ptr ce cx fin q child (LocatedValue et (mk_ptr dst LocMemory))` by
        (irule fixed_select_place_ptr >> goal_assum (drule_at (Pat `place_ptr_rel _ _ _ _ _ _`)) >>
         goal_assum (drule_at (Pat `array_length_frame _ _ _ _ _ _ _`)) >>
         qexistsl [`ArrayV (SArrayV kvs)`,`etv`,`i`,`j`] >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
         >- (strip_tac >> qexists `v` >> qpat_assum `r = Value _ ==> _` (drule_then ACCEPT_TAC)) >>
         qpat_assum `r = Value _ \/ _` strip_assume_tac
         >- (disj1_tac >> first_assum ACCEPT_TAC) >>
         disj2_tac >> goal_assum (drule_at Any)) >>
      `vv_at ce cx et sa sb fin child (LocatedValue et (mk_ptr dst LocMemory)) q /\
       (!v. child = Value v ==> vv_own ce cx et sa sb fin child (LocatedValue et (mk_ptr dst LocMemory)) q)` by
        (qspecl_then [`SArrayV kvs`,`v`,`w + n2w j`] match_mp_tac fixed_select_child_region >>
         goal_assum (drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`)) >>
         goal_assum (drule_at (Pat `mem_step_offset _ _ = SOME _`)) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `vv_holds ce cx et child (LocatedValue et (mk_ptr dst LocMemory)) fin q /\
       vv_store_bound cx et et fin child (LocatedValue et (mk_ptr dst LocMemory)) q /\
       ptr_vv_ok cx et child (LocatedValue et (mk_ptr dst LocMemory)) fin Gq tq q /\
       ptr_buf_ok ce (Subscript et obj idx) dst Gq q` by
        (irule fixed_select_child_bytes >>
         conj_tac >- first_assum ACCEPT_TAC >>
         qexistsl [`w + n2w j`,`etv`,`j`,`n`,`v`,`w`] >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
         >- (qpat_assum `tq.t_mem = tn.t_mem` SUBST1_TAC >>
             qpat_assum `q.vs_memory = u.vs_memory` SUBST1_TAC >>
             qpat_assum `w2n (w + n2w j) = _` SUBST1_TAC >>
             first_assum ACCEPT_TAC)
         >- (qpat_assum `op_prov Gq dst = op_prov G bop` SUBST1_TAC >>
             first_assum ACCEPT_TAC) >>
         qpat_assum `q.vs_alloca_next = u.vs_alloca_next` SUBST1_TAC >>
         first_assum ACCEPT_TAC) >>
      `s0.vs_alloca_next <= q.vs_alloca_next` by
        (qpat_assum `q.vs_alloca_next = u.vs_alloca_next` SUBST1_TAC >>
         first_assum ACCEPT_TAC) >>
      rpt gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
      `vv_post H ctx fn ce cx (Subscript et obj idx) es sa sb s0 fin child
         (LocatedValue et (mk_ptr dst LocMemory)) q /\
       ghost_inv_at (DF H) lo d ce cx fin Gq tq q /\
       ghost_kept_at lo ce es sa G0 tn0 s0 Gq tq` by
        (irule fixed_select_child_post >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         goal_assum (drule_at (Pat `array_length_frame _ _ _ _ _ _ _`)) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `ctx_has_dalloca ctx ==> allocas_below_fmp q` by
        (qpat_assum `array_length_frame _ u _ _ q _ _`
           (strip_assume_tac o SRULE [] o
            Q.AP_TERM `\st. (st.vs_allocas,st.vs_initial_fmp,st.vs_fmp)` o
            cj 1 o REWRITE_RULE[array_length_frame_def]) >>
         strip_tac >>
         qpat_x_assum `ctx_has_dalloca ctx ==> allocas_below_fmp u` drule >>
         simp[allocas_below_fmp_def] >> metis_tac[]) >>
      disj1_tac >> qexists `q` >> conj_tac >- REFL_TAC >>
      qexists `child` >>
      qpat_assum `select_result _ _ _ _ _ = (INL child,fin)` SUBST1_TAC >>
      rewrite_tac[pairTheory.FST,expr_type_def,exprLoweringTheory.lowered_value_type_def] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      simp[mk_ptr_def,vv_location_def,IgnAsm `i = _`] >>
      gen_tac >> strip_tac >>
      qpat_assum `!v. child = Value v ==> vv_own _ _ _ _ _ _ _ _ _`
        (drule_then mp_tac) >>
      qpat_assum `child = Value _` (fn th => rewrite_tac[th,mk_ptr_def])) >>
  qpat_x_assum `if idx_in_range _ _ _ then _ else _` mp_tac >>
  asm_rewrite_tac[] >> disch_tac >>
  qpat_assum `!i err. _ = INR err ==> _` (drule_then assume_tac) >>
  conj_tac
  >- (gen_tac >> irule select_result_nonstorage_gas_obs >> simp[IgnAsm `i = _`]) >>
  simp[IgnAsm `i = _`, fragExecTheory.exit_result_def, expr_exit_def, halt_exit_def]
QED

Theorem subscript_fixed_memory_select_full:
  compile_array_subscript bop iop F n ws (type_memory_bytes ce et)
    (is_signed_type (expr_type idx)) loader sn = (dst,sb) /\
  fn_has_code sn sb fn /\
  eval_operand bop u = SOME w /\ eval_operand iop u = SOME iw /\
  op_taint tn bop = {} /\ op_taint tn iop = {} /\ op_prov G iop = NONE /\
  (!x. bop = Var x ==> not_fresh_at sn x) /\
  (!x. iop = Var x ==> not_fresh_at sn x) /\
  allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ ~u.vs_halted /\
  u.vs_current_bb = sn.cs_current_bb /\ u.vs_inst_idx = LENGTH sn.cs_current_insts /\
  alloca_history fn u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
  local_ptrs_reserved ce sn /\ sa.cs_next_var <= sn.cs_next_var /\ sn.cs_next_id <= sb.cs_next_id /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  storage_trace_domain cx st0 fin.storage_trace /\ fin.gas_obs = [] /\
  i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw)) /\
  n < dimword (:256) /\ type_memory_bytes ce et = type_memory_size etv /\
  evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) = SOME (ArrayTV etv (Fixed n)) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  value_has_type (ArrayTV etv (Fixed n)) (ArrayV (SArrayV kvs)) /\
  (r = Value (ArrayV (SArrayV kvs)) \/
   ?id path. r = PlaceR (MemoryPlace id path) /\
     runtime_place_typed cx fin (MemoryPlace id path) (ArrayTV etv (Fixed n)) /\
     popped_keys_indexed fin.scopes) /\
  read_result cx r fin = (INL (ArrayV (SArrayV kvs)),fin) /\
  (!id path. r = PlaceR (MemoryPlace id path) ==>
    place_ptr_rel ce cx u r w (SOME LocMemory) (Type (ArrayT et (Fixed n)))) /\
  vv_at ce cx (ArrayT et (Fixed n)) sa sn fin r (LocatedValue t (mk_ptr bop LocMemory)) u /\
  (!v. r = Value v ==> vv_own ce cx (ArrayT et (Fixed n)) sa sn fin r
                          (LocatedValue t (mk_ptr bop LocMemory)) u) /\
  w2n w + n * type_memory_size etv < dimword (:256) /\
  (!m. mem_agree_outside tn.t_mem u.vs_memory m ==>
    val_in_memory (ArrayTV etv (Fixed n)) (ArrayV (SArrayV kvs)) (w2n w) m) /\
  (type_memory_size etv <> 0 ==> w2n w + n * type_memory_size etv <= u.vs_alloca_next) /\
  (type_memory_size etv <> 0 ==>
   ?b sz. op_prov G bop = SOME (b,sz) /\ b <= w2n w /\
          w2n w + n * type_memory_size etv <= b + sz) /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    stmt_state_rel H ctx fn ce cx fin u /\ storage_well_formed_on cx fin (FST H) /\
    wb_frame ce es fin sa s0 u /\
    (~expr_has_effect (Subscript et obj idx) ==> pure_frame ce fn es sa s0 u) /\
    ghost_inv_at (DF H) lo d ce cx fin G tn u) ==>
  gas_outcome_full (DF,lo,explicit,ctx,fn,PG) (cx_tops cx) cx st0
    (select_result cx (ArrayT et (Fixed n)) r (ValueSubscript (IntV i))) (fin,u,G,tn)
    (\H res ee Gz tnz z. ?child. res = INL child /\
       vv_post H ctx fn ce cx (Subscript et obj idx) es sa sb s0 ee
         child (LocatedValue et (mk_ptr dst LocMemory)) z /\
       vv_store_bound cx (post_value_type ce (Subscript et obj idx))
         (lowered_value_type ce (Subscript et obj idx)) ee
         child (LocatedValue et (mk_ptr dst LocMemory)) z /\
       z.vs_current_bb = sb.cs_current_bb /\
       z.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history fn z /\
       (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
       s0.vs_alloca_next <= z.vs_alloca_next /\
       ghost_inv_at (DF H) lo d ce cx ee Gz tnz z /\
       ptr_vv_ok cx (post_value_type ce (Subscript et obj idx))
         child (LocatedValue et (mk_ptr dst LocMemory)) ee Gz tnz z /\
       (!v. child = Value v /\ ~is_word_type (post_value_type ce (Subscript et obj idx)) /\
          ~is_bytestring_type (post_value_type ce (Subscript et obj idx)) ==>
          vv_own ce cx (post_value_type ce (Subscript et obj idx)) sa sb ee
            child (LocatedValue et (mk_ptr dst LocMemory)) z /\
          (!t' p'. LocatedValue et (mk_ptr dst LocMemory) = LocatedValue t' p' ==>
                   p'.ptr_location = LocMemory)) /\
       (ce.ce_is_ctor /\ vv_location (LocatedValue et (mk_ptr dst LocMemory)) = SOME LocCode ==>
        ?v. read_result cx child ee = (INL v,ee) /\
            !rt a. evaluate_type (get_tenv cx) (post_value_type ce (Subscript et obj idx)) = SOME rt /\
              eval_operand (vv_operand (LocatedValue et (mk_ptr dst LocMemory))) z = SOME a ==>
              w2n a + type_memory_size rt <= lo /\
              (!mem. mem_agree_outside tnz.t_mem z.vs_memory mem ==>
                val_in_memory rt v (w2n a) mem)) /\
       (!t' op. LocatedValue et (mk_ptr dst LocMemory) = StackValue t' op /\
          ~is_word_type (post_value_type ce (Subscript et obj idx)) ==>
          ptr_buf_ok ce (Subscript et obj idx) op Gz z) /\
       (!t' p'. LocatedValue et (mk_ptr dst LocMemory) = LocatedValue t' p' /\
          p'.ptr_location = LocMemory ==>
          ptr_buf_ok ce (Subscript et obj idx) p'.ptr_operand Gz z) /\
       ghost_kept_at lo ce es sa G0 tn0 s0 Gz tnz)
    (\H res ee gt rr. expr_exit res rr /\ halt_exit H cx ee res rr /\
      (ctx_has_dalloca ctx ==> !z. rr = Halt z ==> allocas_below_fmp z))
Proof
  disch_then (EVERY o map assume_tac o CONJUNCTS) >>
  assume_tac fixed_select_scalar_true >>
  drule_all subscript_fixed_memory_select_observed >>
  simp_tac bool_ss [LET_THM] >>
  disch_then (qx_choosel_then [`sc`,`res`,`q`,`Gq`,`tq`] strip_assume_tac) >>
  irule gas_outcome_full_intro >>
  qexistsl [`Gq`,`fin`,`[]`,
    `if idx_in_range (is_signed_type (expr_type idx)) iw (n2w n)
     then OK q else Abort Revert_abort q`, `res`,`tq`] >>
  `fin with gas_obs := [] = fin` by simp[evaluation_state_component_equality] >>
  fs[gasSummaryTheory.gas_explicit_def, IgnAsm `i = _`]
QED
