(* Counted storage/transient array continuations after index evaluation. *)
Theory popNestedStorageArraySuffix
Ancestors
  targetSubscriptStorage targetSubscriptMemory bodyMemEmitOpFrame
  targetPlaceSimMem loweringPosts loweringStateRelDefs exprSimProps
  exprSimArrayIndex exprLoweringProps exprLowering emitHelper emitHelperProps
  freshWrites exprBopSimProps exprSimUnopProps fragExec fragGasMode
  compileEnv venomExecSemantics venomInst venomState
  finite_map list words arithmetic context

Theorem pop_nested_storage_header_load_mem[local]:
  compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca
    (if tr then LocTransient else LocStorage) base_op sa = (dst,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand base_op s = SOME w /\ alloca_history func s ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      eval_operand dst t = SOME (if tr then tload w s else sload w s) /\
      stmt_state_rel ctx func cenv cx es t /\
      (!x v. not_fresh_at sa x /\ lookup_var x s = SOME v ==> lookup_var x t = SOME v) /\
      t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `emit_op (if tr then TLOAD else SLOAD) [base_op] sa = (dst,sb)` by
    (Cases_on `tr` >> gvs[compile_ptr_load_def]) >>
  `step_inst_base
     (mk_inst sa.cs_next_id (if tr then TLOAD else SLOAD) [base_op]
       [STRING #"%" (toString sa.cs_next_var)]) s =
   OK (update_var (STRING #"%" (toString sa.cs_next_var))
       (if tr then tload w s else sload w s) s)` by
    (Cases_on `tr` >> simp[mk_inst_def, step_inst_base_def, exec_read1_def]) >>
  drule_at (Pat `step_inst_base _ _ = _`) emit_op_word_path_frame_mem >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then drule >>
  (impl_tac >- (Cases_on `tr` >> simp[])) >> strip_tac >>
  qexists_tac `t` >> simp[update_var_def]
QED

Theorem pop_nested_storage_dynamic_array_path_mem[local]:
  (!base_op idx_op len_op dyn ws esz sgn sa dst sb es s b i len.
    comp_ignore_bind (array_bounds_check idx_op len_op sgn)
      (array_elem_ptr base_op idx_op dyn ws esz) sa = (dst,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ alloca_history func s /\
    (!x. base_op = Var x ==> not_fresh_at sa x) /\
    (!x. idx_op = Var x ==> not_fresh_at sa x) /\
    (!x. len_op = Var x ==> not_fresh_at sa x) /\
    eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
    eval_operand len_op s = SOME len /\ idx_in_range sgn i len ==>
    ?t. gas_marked_path T ctx func s 0 (OK t) /\
        eval_operand dst t = SOME ((if dyn then b + n2w ws else b) + i * n2w esz) /\
        stmt_state_rel ctx func cenv cx es t /\
        (!x v. not_fresh_at sa x /\ lookup_var x s = SOME v ==> lookup_var x t = SOME v) /\
        (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP t.vs_allocas aid = SOME a) /\
        t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
        t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next) ==>
  compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca
    (if tr then LocTransient else LocStorage) base_op sa = (len_op,sm) /\
  comp_ignore_bind (array_bounds_check idx_op len_op sgn)
    (array_elem_ptr base_op idx_op T ws esz) sm = (dst,sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ alloca_history func s /\
  (!x. base_op = Var x ==> not_fresh_at sa x) /\
  (!x. idx_op = Var x ==> not_fresh_at sa x) /\
  (!l. base_op <> Label l) /\ (!l. idx_op <> Label l) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  idx_in_range sgn i (if tr then tload b s else sload b s) ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      eval_operand dst t = SOME (b + n2w ws + i * n2w esz) /\
      stmt_state_rel ctx func cenv cx es t /\
      (!x v. not_fresh_at sa x /\ lookup_var x s = SOME v ==> lookup_var x t = SOME v) /\
      (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP t.vs_allocas aid = SOME a) /\
      t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next
Proof
  disch_tac >> strip_tac >>
  drule target_storage_header_compile >> strip_tac >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!x. base_op = Var x ==> not_fresh_at sm x) /\
   (!x. idx_op = Var x ==> not_fresh_at sm x)` by
    metis_tac[not_fresh_at_mono] >>
  drule_all pop_nested_storage_header_load_mem >> strip_tac >>
  `eval_operand base_op t = SOME b /\ eval_operand idx_op t = SOME i` by
    (conj_tac >> irule eval_operand_frame >> simp[] >>
     qexistsl_tac [`sa`, `s`] >> simp[]) >>
  first_x_assum (drule_at (Pat `comp_ignore_bind _ _ _ = _`)) >>
  disch_then drule_all >> simp[] >> strip_tac >>
  qexists_tac `t'` >> conj_tac
  >- metis_tac[gas_marked_path_then, ADD_CLAUSES] >>
  simp[] >> rpt strip_tac >>
  `not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >> metis_tac[]
QED

Theorem pop_nested_storage_dynamic_array_abort_path_mem[local]:
  (!idx_op len_op base_op dyn ws esz sgn sa dst sb s i len.
    comp_ignore_bind (array_bounds_check idx_op len_op sgn)
      (array_elem_ptr base_op idx_op dyn ws esz) sa = (dst,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    (!x. idx_op = Var x ==> not_fresh_at sa x) /\
    (!x. len_op = Var x ==> not_fresh_at sa x) /\
    eval_operand idx_op s = SOME i /\ eval_operand len_op s = SOME len /\
    ~idx_in_range sgn i len ==>
    ?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t)) ==>
  compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca
    (if tr then LocTransient else LocStorage) base_op sa = (len_op,sm) /\
  comp_ignore_bind (array_bounds_check idx_op len_op sgn)
    (array_elem_ptr base_op idx_op T ws esz) sm = (dst,sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ alloca_history func s /\
  (!x. idx_op = Var x ==> not_fresh_at sa x) /\ (!l. idx_op <> Label l) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  ~idx_in_range sgn i (if tr then tload b s else sload b s) ==>
  ?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t)
Proof
  disch_tac >> strip_tac >>
  drule target_storage_header_compile >> strip_tac >>
  `!x. idx_op = Var x ==> not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
  drule_all pop_nested_storage_header_load_mem >> strip_tac >>
  `eval_operand idx_op t = SOME i` by
    (irule eval_operand_frame >> simp[] >> qexistsl_tac [`sa`, `s`] >> simp[]) >>
  first_x_assum (drule_at (Pat `comp_ignore_bind _ _ _ = _`)) >>
  disch_then drule_all >> strip_tac >>
  qexists_tac `t'` >> metis_tac[gas_marked_path_then, ADD_CLAUSES]
QED

Theorem pop_nested_storage_array_path_mem[local]:
  (!base_op idx_op len_op dyn ws esz sgn sa dst sb es s b i len.
    comp_ignore_bind (array_bounds_check idx_op len_op sgn)
      (array_elem_ptr base_op idx_op dyn ws esz) sa = (dst,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ alloca_history func s /\
    (!x. base_op = Var x ==> not_fresh_at sa x) /\
    (!x. idx_op = Var x ==> not_fresh_at sa x) /\
    (!x. len_op = Var x ==> not_fresh_at sa x) /\
    eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
    eval_operand len_op s = SOME len /\ idx_in_range sgn i len ==>
    ?t. gas_marked_path T ctx func s 0 (OK t) /\
        eval_operand dst t = SOME ((if dyn then b + n2w ws else b) + i * n2w esz) /\
        stmt_state_rel ctx func cenv cx es t /\
        (!x v. not_fresh_at sa x /\ lookup_var x s = SOME v ==> lookup_var x t = SOME v) /\
        (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP t.vs_allocas aid = SOME a) /\
        t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
        t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next) ==>
  compile_array_subscript base_op idx_op dyn cnt ws esz sgn
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca
      (if tr then LocTransient else LocStorage)) sa = (dst,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  alloca_history func s /\
  (!x. base_op = Var x ==> not_fresh_at sa x) /\
  (!x. idx_op = Var x ==> not_fresh_at sa x) /\
  (!l. base_op <> Label l) /\ (!l. idx_op <> Label l) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  idx_in_range sgn i (if dyn then (if tr then tload b s else sload b s) else n2w cnt) ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      eval_operand dst t = SOME ((if dyn then b + n2w ws else b) + i * n2w esz) /\
      stmt_state_rel ctx func cenv cx es t /\
      (!x v. not_fresh_at sa x /\ lookup_var x s = SOME v ==> lookup_var x t = SOME v) /\
      (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP t.vs_allocas aid = SOME a) /\
      t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next
Proof
  disch_tac >> reverse (Cases_on `dyn`) >>
  simp[compile_array_subscript_split, comp_bind_def, comp_return_def]
  >- (strip_tac >>
      `eval_operand (Lit (n2w cnt)) s = SOME (n2w cnt)` by simp[eval_operand_def] >>
      `!x. Lit (n2w cnt) = Var x ==> not_fresh_at sa x` by simp[] >>
      first_x_assum (drule_at (Pat `comp_ignore_bind _ _ _ = _`)) >>
      disch_then drule_all >> simp[]) >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_ptr_load _ _ _ _ sa = (len_op,sm)` >>
  drule target_storage_header_compile >> strip_tac >>
  `straight_fresh (comp_ignore_bind (array_bounds_check idx_op len_op sgn)
     (array_elem_ptr base_op idx_op T ws esz))` by
    simp[straight_fresh_array_check_ptr] >>
  drule_all straight_fresh_cs_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all pop_nested_storage_dynamic_array_path_mem >> simp[]
QED

Theorem pop_nested_storage_array_abort_path_mem[local]:
  (!idx_op len_op base_op dyn ws esz sgn sa dst sb s i len.
    comp_ignore_bind (array_bounds_check idx_op len_op sgn)
      (array_elem_ptr base_op idx_op dyn ws esz) sa = (dst,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    (!x. idx_op = Var x ==> not_fresh_at sa x) /\
    (!x. len_op = Var x ==> not_fresh_at sa x) /\
    eval_operand idx_op s = SOME i /\ eval_operand len_op s = SOME len /\
    ~idx_in_range sgn i len ==>
    ?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t)) ==>
  compile_array_subscript base_op idx_op dyn cnt ws esz sgn
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca
      (if tr then LocTransient else LocStorage)) sa = (dst,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  alloca_history func s /\
  (!x. idx_op = Var x ==> not_fresh_at sa x) /\ (!l. idx_op <> Label l) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  ~idx_in_range sgn i (if dyn then (if tr then tload b s else sload b s) else n2w cnt) ==>
  ?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t)
Proof
  disch_tac >> reverse (Cases_on `dyn`) >>
  simp[compile_array_subscript_split, comp_bind_def, comp_return_def]
  >- (strip_tac >>
      `eval_operand (Lit (n2w cnt)) s = SOME (n2w cnt)` by simp[eval_operand_def] >>
      `!x. Lit (n2w cnt) = Var x ==> not_fresh_at sa x` by simp[] >>
      first_x_assum (drule_at (Pat `comp_ignore_bind _ _ _ = _`)) >>
      disch_then drule_all >> simp[]) >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_ptr_load _ _ _ _ sa = (len_op,sm)` >>
  drule target_storage_header_compile >> strip_tac >>
  `straight_fresh (comp_ignore_bind (array_bounds_check idx_op len_op sgn)
     (array_elem_ptr base_op idx_op T ws esz))` by
    simp[straight_fresh_array_check_ptr] >>
  drule_all straight_fresh_cs_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all pop_nested_storage_dynamic_array_abort_path_mem >> simp[]
QED

Theorem pop_nested_storage_array_suffix_mem:
  (!base_op idx_op len_op dyn ws esz sgn sa dst sb es s b i len.
    comp_ignore_bind (array_bounds_check idx_op len_op sgn)
      (array_elem_ptr base_op idx_op dyn ws esz) sa = (dst,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ alloca_history func s /\
    (!x. base_op = Var x ==> not_fresh_at sa x) /\
    (!x. idx_op = Var x ==> not_fresh_at sa x) /\
    (!x. len_op = Var x ==> not_fresh_at sa x) /\
    eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
    eval_operand len_op s = SOME len /\ idx_in_range sgn i len ==>
    ?t. gas_marked_path T ctx func s 0 (OK t) /\
        eval_operand dst t = SOME ((if dyn then b + n2w ws else b) + i * n2w esz) /\
        stmt_state_rel ctx func cenv cx es t /\
        (!x v. not_fresh_at sa x /\ lookup_var x s = SOME v ==> lookup_var x t = SOME v) /\
        (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP t.vs_allocas aid = SOME a) /\
        t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
        t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next) ==>
  target_post ctx func cenv cx es0 sa sm s0 es
    (PlaceR (StoragePlace tr slot (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt))))
    (Type (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt))) rb s /\
  (dyn ==> w2n (lookup_storage slot (get_storage cx es tr)) <= cnt) /\
  storage_read_live cx tr (get_storage cx es tr) slot
    (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) /\
  w2n slot + type_slot_size (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) <= dimword(:256) /\
  evaluate_type (get_tenv cx) ity = SOME itv /\ value_has_type itv (IntV i) /\
  eval_operand idx s = SOME (i2w i) /\
  compile_array_subscript (FST rb) idx dyn cnt 1 (type_slot_size etv)
    (is_signed_type ity)
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca
      (if tr then LocTransient else LocStorage)) sm = (dst,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\ ~s.vs_halted /\ alloca_history func s /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!x. idx = Var x ==> not_fresh_at sm x) /\ (!l. idx <> Label l) /\
  (!l. FST rb <> Label l) /\ (!x. dst = Var x ==> not_fresh_at sb x) /\
  extend_place cx
    (PlaceR (StoragePlace tr slot (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt))))
    (ValueSubscript (IntV i)) es = (INL pv',es') ==>
  ?u. gas_marked_path T ctx func s 0 (OK u) /\
      target_post ctx func cenv cx es0 sa sb s0 es' pv' (Type ety)
        (dst,SOME (slot_loc tr),SOME (ValPT ety)) u /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next
Proof
  disch_tac >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es s /\
   eval_operand (FST rb) s = SOME slot /\
   evaluate_type (get_tenv cx) (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt)) =
     SOME (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) /\
   (!x. FST rb = Var x ==> not_fresh_at sm x)` by
    fs[target_post_def, place_ptr_rel_def] >>
  drule_all target_storage_array_live_range >> strip_tac >>
  qspecl_then [`cx`, `tr`, `slot`, `etv`,
    `if dyn then Dynamic cnt else Fixed cnt`, `i`, `es`]
    assume_tac extend_place_storage_array_index >>
  `0 <= i /\ es' = es /\
   pv' = PlaceR (StoragePlace tr
     (slot + n2w ((if dyn then 1 else 0) + Num i * type_slot_size etv)) etv) /\
   idx_in_range (is_signed_type ity) (i2w i)
     (if dyn then (if tr then tload slot s else sload slot s) else n2w cnt)` by
    (Cases_on `dyn` >> gvs[AllCaseEqs()]) >>
  drule_all pop_nested_storage_array_path_mem >> strip_tac >>
  drule_all target_storage_array_type_bound >> strip_tac >>
  `eval_operand dst t = SOME
     (slot + n2w ((if dyn then 1 else 0) + Num i * type_slot_size etv))` by
    metis_tac[target_storage_array_offset] >>
  qexists_tac `t` >> simp[] >>
  irule (SRULE [value_type_place_def]
    (Q.INST [`vt'` |-> `Type ety`] target_post_suffix_frame)) >>
  gvs[place_ptr_rel_def, place_readable_def, value_type_place_def] >>
  goal_assum (drule_at (Pat `target_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]
QED

Theorem pop_nested_storage_array_error_suffix_mem:
  (!idx_op len_op base_op dyn ws esz sgn sa dst sb s i len.
    comp_ignore_bind (array_bounds_check idx_op len_op sgn)
      (array_elem_ptr base_op idx_op dyn ws esz) sa = (dst,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    (!x. idx_op = Var x ==> not_fresh_at sa x) /\
    (!x. len_op = Var x ==> not_fresh_at sa x) /\
    eval_operand idx_op s = SOME i /\ eval_operand len_op s = SOME len /\
    ~idx_in_range sgn i len ==>
    ?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t)) ==>
  target_post ctx func cenv cx es0 sa sm s0 es
    (PlaceR (StoragePlace tr slot (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt))))
    (Type (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt))) rb s /\
  (dyn ==> w2n (lookup_storage slot (get_storage cx es tr)) <= cnt) /\
  storage_read_live cx tr (get_storage cx es tr) slot
    (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) /\
  w2n slot + type_slot_size (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) <= dimword(:256) /\
  evaluate_type (get_tenv cx) ity = SOME itv /\ value_has_type itv (IntV i) /\
  eval_operand idx s = SOME (i2w i) /\
  compile_array_subscript (FST rb) idx dyn cnt 1 (type_slot_size etv)
    (is_signed_type ity)
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca
      (if tr then LocTransient else LocStorage)) sm = (dst,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sm /\ ~s.vs_halted /\ alloca_history func s /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!x. idx = Var x ==> not_fresh_at sm x) /\ (!l. idx <> Label l) /\
  extend_place cx
    (PlaceR (StoragePlace tr slot (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt))))
    (ValueSubscript (IntV i)) es = (INR err,es') ==>
  (?u. gas_marked_path T ctx func s 0 (Abort Revert_abort u)) /\
  (?msg. err = Error (RuntimeError msg)) /\ es' = es
Proof
  disch_tac >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es s /\
   eval_operand (FST rb) s = SOME slot /\
   evaluate_type (get_tenv cx) (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt)) =
     SOME (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt))` by
    fs[target_post_def, place_ptr_rel_def] >>
  drule_all target_storage_array_live_range >> strip_tac >>
  qspecl_then [`cx`, `tr`, `slot`, `etv`,
    `if dyn then Dynamic cnt else Fixed cnt`, `i`, `es`]
    assume_tac extend_place_storage_array_index >>
  `~idx_in_range (is_signed_type ity) (i2w i)
    (if dyn then (if tr then tload slot s else sload slot s) else n2w cnt)` by
    (Cases_on `dyn` >> gvs[AllCaseEqs()]) >>
  drule_all pop_nested_storage_array_abort_path_mem >> strip_tac >>
  conj_tac >- metis_tac[] >>
  Cases_on `dyn` >> gvs[AllCaseEqs()]
QED
