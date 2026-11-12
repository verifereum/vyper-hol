(* Counted local-memory array continuations after target index evaluation. *)
Theory popNestedMemoryArraySuffix
Ancestors
  targetSubscriptMemory targetPlaceSimMem bodyMemTbConvertSourceMemory
  bodyDeclMemoryCore allocaFootprint emitHelperProps stmtSimProps
  fragGasMode fragGasPathMem exprLoweringProps exprSimProps freshWrites exprBopSimProps
  exprSimArrayIndex exprSimUnopProps fragExec
  compileEnv loweringPosts loweringStateRelDefs exprSimDefs exprSimHypsDefs vyperTyping
  valueEncoding vyperTypeInvariants bodySimAugPlaceLoad
  venomExecSemantics venomInstProofs venomState venomInst
  finite_map list words exprLowering emitHelper arithmetic context

Theorem pop_nested_memory_header_load_mem[local]:
  compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory base_op sa = (dst,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand base_op s = SOME w /\ alloca_history func s /\
  w2n w + 32 <= s.vs_alloca_next ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      eval_operand dst t = SOME (mload (w2n w) s) /\
      stmt_state_rel ctx func cenv cx es t /\
      (!x v. not_fresh_at sa x /\ lookup_var x s = SOME v ==>
             lookup_var x t = SOME v) /\
      t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  simp[compile_ptr_load_def] >> strip_tac >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  drule_all convert_emit_mload_path_mem >> strip_tac >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (simp[not_fresh_at_def, Abbr `out`] >> metis_tac[LESS_EQ_REFL]) >>
  `not_local_ptr cenv es.scopes out` by
    (simp[Abbr `out`] >> irule local_ptrs_reserved_fresh >>
     metis_tac[LESS_EQ_REFL]) >>
  `dst = Var out /\ sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts)` by
    gvs[Abbr `out`, emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  `alloca_history func
     (update_var out (mload (w2n w) s) s with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule body_store_memory_history >> simp[] >>
     qexistsl_tac [`s`, `sa`] >> simp[] >>
     drule emitted_insts_emit_op >> strip_tac >>
     drule emit_op_same_blocks >> strip_tac >>
     simp[Abbr `out`, run_inst_seq_def, mk_inst_def, is_terminator_def,
          step_inst_base_def, exec_read1_def, eval_operands_def]) >>
  `gas_marked_path T ctx func s 0
     (OK (update_var out (mload (w2n w) s) s with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    metis_tac[gas_marked_path_def, Abbr `out`] >>
  `stmt_state_rel ctx func cenv cx es (update_var out (mload (w2n w) s) s)` by
    (irule stmt_state_rel_update_var >> simp[]) >>
  qexists_tac `update_var out (mload (w2n w) s) s
                with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[stmt_state_rel_inst_idx, eval_operand_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE] >> rpt strip_tac >> metis_tac[lookup_var_def]
QED

Theorem pop_nested_memory_array_header_frontier[local]:
  stmt_state_rel ctx func cenv cx es s /\ expr_sim_inv cenv cx env es /\
  lookup_scopes id es.scopes = SOME entry /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) w loc (Type ty) /\
  evaluate_type (get_tenv cx) ty = SOME (ArrayTV etv (Dynamic cnt)) ==>
  w2n w + 32 <= s.vs_alloca_next
Proof
  rpt strip_tac >> gvs[place_ptr_rel_def] >>
  `evaluate_type (get_tenv cx) t0 = SOME entry.type` by
    (irule aug_place_entry_type_agrees >> metis_tac[]) >>
  gvs[] >>
  `local_ptrs_rel func cenv es.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `w2n b + sz <= s.vs_alloca_next /\ type_memory_size entry.type <= sz` by
    (qpat_x_assum `local_ptrs_rel _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
     first_x_assum drule_all >> strip_tac >> gvs[]) >>
  drule mem_path_offset_sound >> strip_tac >>
  irule local_ptr_field_below_frontier >>
  qexists_tac `sz` >> simp[] >>
  fs[type_memory_size_def]
QED

Theorem pop_nested_memory_dynamic_array_path_mem[local]:
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
  compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory base_op sa = (len_op,sm) /\
  comp_ignore_bind (array_bounds_check idx_op len_op sgn)
    (array_elem_ptr base_op idx_op T ws esz) sm = (dst,sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ alloca_history func s /\
  w2n b + 32 <= s.vs_alloca_next /\
  (!x. base_op = Var x ==> not_fresh_at sa x) /\
  (!x. idx_op = Var x ==> not_fresh_at sa x) /\
  (!l. base_op <> Label l) /\ (!l. idx_op <> Label l) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  idx_in_range sgn i (mload (w2n b) s) ==>
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
  drule target_memory_header_compile >> strip_tac >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!x. base_op = Var x ==> not_fresh_at sm x) /\
   (!x. idx_op = Var x ==> not_fresh_at sm x)` by
    metis_tac[not_fresh_at_mono] >>
  drule_all pop_nested_memory_header_load_mem >> strip_tac >>
  `eval_operand base_op t = SOME b /\ eval_operand idx_op t = SOME i` by
    (conj_tac >> irule eval_operand_frame >> simp[] >>
     qexistsl [`sa`, `s`] >> simp[]) >>
  first_x_assum (drule_at (Pat `comp_ignore_bind _ _ _ = _`)) >>
  disch_then drule_all >> simp[] >> strip_tac >>
  qexists_tac `t'` >> conj_tac
  >- metis_tac[gas_marked_path_then, ADD_CLAUSES] >>
  simp[] >> rpt strip_tac >>
  `not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
  metis_tac[]
QED

Theorem pop_nested_memory_dynamic_array_abort_path_mem[local]:
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
  compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory base_op sa = (len_op,sm) /\
  comp_ignore_bind (array_bounds_check idx_op len_op sgn)
    (array_elem_ptr base_op idx_op T ws esz) sm = (dst,sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ alloca_history func s /\
  w2n b + 32 <= s.vs_alloca_next /\
  (!x. idx_op = Var x ==> not_fresh_at sa x) /\ (!l. idx_op <> Label l) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  ~idx_in_range sgn i (mload (w2n b) s) ==>
  ?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t)
Proof
  disch_tac >> strip_tac >>
  drule target_memory_header_compile >> strip_tac >>
  `!x. idx_op = Var x ==> not_fresh_at sm x` by
    metis_tac[not_fresh_at_mono] >>
  drule_all pop_nested_memory_header_load_mem >> strip_tac >>
  `eval_operand idx_op t = SOME i` by
    (irule eval_operand_frame >> simp[] >> qexistsl [`sa`, `s`] >> simp[]) >>
  first_x_assum (drule_at (Pat `comp_ignore_bind _ _ _ = _`)) >>
  disch_then drule_all >> strip_tac >>
  qexists_tac `t'` >> metis_tac[gas_marked_path_then, ADD_CLAUSES]
QED

Theorem pop_nested_memory_array_path_mem[local]:
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
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory) sa = (dst,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  alloca_history func s /\ (dyn ==> w2n b + 32 <= s.vs_alloca_next) /\
  (!x. base_op = Var x ==> not_fresh_at sa x) /\
  (!x. idx_op = Var x ==> not_fresh_at sa x) /\
  (!l. base_op <> Label l) /\ (!l. idx_op <> Label l) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  idx_in_range sgn i (if dyn then mload (w2n b) s else n2w cnt) ==>
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
  drule target_memory_header_compile >> strip_tac >>
  `straight_fresh (comp_ignore_bind (array_bounds_check idx_op len_op sgn)
     (array_elem_ptr base_op idx_op T ws esz))` by
    simp[straight_fresh_array_check_ptr] >>
  drule_all straight_fresh_cs_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all pop_nested_memory_dynamic_array_path_mem >> simp[]
QED

Theorem pop_nested_memory_array_abort_path_mem[local]:
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
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory) sa = (dst,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  alloca_history func s /\ (dyn ==> w2n b + 32 <= s.vs_alloca_next) /\
  (!x. idx_op = Var x ==> not_fresh_at sa x) /\ (!l. idx_op <> Label l) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  ~idx_in_range sgn i (if dyn then mload (w2n b) s else n2w cnt) ==>
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
  drule target_memory_header_compile >> strip_tac >>
  `straight_fresh (comp_ignore_bind (array_bounds_check idx_op len_op sgn)
     (array_elem_ptr base_op idx_op T ws esz))` by
    simp[straight_fresh_array_check_ptr] >>
  drule_all straight_fresh_cs_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all pop_nested_memory_dynamic_array_abort_path_mem >> simp[]
QED

Theorem pop_nested_memory_array_suffix_mem:
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
    (PlaceR (MemoryPlace id path))
    (Type (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt))) rb s /\
  expr_sim_inv cenv cx env es /\ lookup_scopes id es.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV av) /\
  evaluate_type (get_tenv cx) (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt)) =
    SOME (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) /\
  evaluate_type (get_tenv cx) ity = SOME itv /\ value_has_type itv (IntV i) /\
  eval_operand idx s = SOME (i2w i) /\
  compile_array_subscript (FST rb) idx dyn cnt 32 (type_memory_bytes cenv ety)
    (is_signed_type ity)
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory) sm = (dst,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\ alloca_history func s /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!x. idx = Var x ==> not_fresh_at sm x) /\
  (!l. idx <> Label l) /\ (!l. FST rb <> Label l) /\
  (!x. dst = Var x ==> not_fresh_at sb x) /\
  extend_place cx (PlaceR (MemoryPlace id path)) (ValueSubscript (IntV i)) es =
    (INL pv',es') ==>
  ?u. gas_marked_path T ctx func s 0 (OK u) /\
      target_post ctx func cenv cx es0 sa sb s0 es' pv' (Type ety)
        (dst,SOME LocMemory,SOME (ValPT ety)) u /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next
Proof
  disch_tac >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es s /\
   (?b. eval_operand (FST rb) s = SOME b /\
        place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) b
          (FST (SND rb)) (Type (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt)))) /\
   (!x. FST rb = Var x ==> not_fresh_at sm x)` by fs[target_post_def] >>
  `dyn ==> w2n b + 32 <= s.vs_alloca_next` by
    (strip_tac >> gvs[] >>
     irule pop_nested_memory_array_header_frontier >> metis_tac[]) >>
  drule_all place_ptr_rel_memory_current >> strip_tac >>
  drule_all extend_place_memory_array_index >>
  disch_then (qspecl_then [`i`, `cx`] assume_tac) >>
  `0 <= i /\ Num i < array_length (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) av` by
    (gvs[AllCaseEqs()]) >>
  drule_all target_memory_array_range >> strip_tac >>
  `idx_in_range (is_signed_type ity) (i2w i)
     (if dyn then mload (w2n b) s else n2w cnt)` by metis_tac[] >>
  drule_all pop_nested_memory_array_path_mem >> strip_tac >>
  drule_all target_memory_array_offset >>
  disch_then (qspec_then `b` strip_assume_tac) >>
  `eval_operand dst t = SOME (b + n2w k)` by metis_tac[] >>
  drule_all target_post_memory_step >> strip_tac >>
  qexists_tac `t` >> simp[]
QED

Theorem pop_nested_memory_array_error_suffix_mem:
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
    (PlaceR (MemoryPlace id path))
    (Type (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt))) rb s /\
  expr_sim_inv cenv cx env es /\ lookup_scopes id es.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV av) /\
  evaluate_type (get_tenv cx) (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt)) =
    SOME (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) /\
  evaluate_type (get_tenv cx) ity = SOME itv /\ value_has_type itv (IntV i) /\
  eval_operand idx s = SOME (i2w i) /\
  compile_array_subscript (FST rb) idx dyn cnt 32 (type_memory_bytes cenv ety)
    (is_signed_type ity)
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory) sm = (dst,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\ alloca_history func s /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!x. idx = Var x ==> not_fresh_at sm x) /\
  (!l. idx <> Label l) /\ (!l. FST rb <> Label l) /\
  (!x. dst = Var x ==> not_fresh_at sb x) /\
  extend_place cx (PlaceR (MemoryPlace id path)) (ValueSubscript (IntV i)) es =
    (INR err,es') ==>
  (?u. gas_marked_path T ctx func s 0 (Abort Revert_abort u)) /\
  err = Error (RuntimeError "evaluate_subscripts array_index") /\ es' = es
Proof
  disch_tac >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es s /\
   ?b. eval_operand (FST rb) s = SOME b /\
       place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) b
         (FST (SND rb)) (Type (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt)))` by
    fs[target_post_def] >>
  `dyn ==> w2n b + 32 <= s.vs_alloca_next` by
    (strip_tac >> gvs[] >>
     irule pop_nested_memory_array_header_frontier >> metis_tac[]) >>
  drule_all place_ptr_rel_memory_current >> strip_tac >>
  drule_all extend_place_memory_array_index >>
  disch_then (qspecl_then [`i`, `cx`] assume_tac) >>
  drule_all target_memory_array_range >> strip_tac >>
  `~idx_in_range (is_signed_type ity) (i2w i)
     (if dyn then mload (w2n b) s else n2w cnt)` by gvs[AllCaseEqs()] >>
  drule_all pop_nested_memory_array_abort_path_mem >>
  gvs[AllCaseEqs()]
QED
