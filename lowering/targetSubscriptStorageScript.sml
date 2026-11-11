(* Live storage-array source bounds and compiler-header agreement. *)
Theory targetSubscriptStorage
Ancestors
  targetSubscriptMemory loweringPosts targetPlaceLive accountsRelProps exprSimArrayIndex
  vyperState vyperInterpreter vyperValue vyperStorageBackend
  venomState compileEnv context exprLowering exprLoweringProps exprBopSimProps freshWrites exprSimUnopProps fragExec
  vyperLookupStorage vyperStorage integer_word
  words arithmetic list rich_list finite_map emitHelper emitHelperProps fragGasMode venomInst venomExecSemantics

Theorem extend_place_storage_array_index:
  !cx tr slot et bd i es.
    extend_place cx (PlaceR (StoragePlace tr slot (ArrayTV et bd)))
      (ValueSubscript (IntV i)) es =
    (case bd of
       Fixed n =>
         if 0 <= i /\ Num i < n then
           (INL (PlaceR (StoragePlace tr
             (slot + n2w (Num i * type_slot_size et)) et)), es)
         else (INR (Error (RuntimeError "array fixed oob")), es)
     | Dynamic n =>
         if ~(0 <= i /\ Num i < n) then
           (INR (Error (RuntimeError "array dynamic capacity oob")), es)
         else if Num i < w2n (lookup_storage slot (get_storage cx es tr)) then
           (INL (PlaceR (StoragePlace tr
             (slot + n2w (1 + Num i * type_slot_size et)) et)), es)
         else (INR (Error (RuntimeError "array dynamic length oob")), es))
Proof
  rpt gen_tac >> Cases_on `et` >> Cases_on `bd` >>
  simp[extend_place_def, extend_storage_place_def, resolve_array_element_def,
       check_def, assert_def, bind_def, ignore_bind_def, return_def,
       raise_def, get_storage_backend_eq, LET_THM] >>
  rpt IF_CASES_TAC >> gvs[return_def, raise_def, bind_def, ignore_bind_def]
QED

Theorem target_storage_array_len_ok:
  stmt_state_rel ctx func cenv cx es s /\
  storage_read_live cx tr (get_storage cx es tr) slot (ArrayTV tv (Dynamic n)) /\
  w2n slot + type_slot_size (ArrayTV tv (Dynamic n)) <= dimword(:256) /\
  eval_operand base_op s = SOME slot ==>
  array_len_ok T cnt
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca
      (if tr then LocTransient else LocStorage)) base_op s
    (lookup_storage slot (get_storage cx es tr)) /\
  ((if tr then tload slot s else sload slot s) =
    lookup_storage slot (get_storage cx es tr))
Proof
  strip_tac >>
  `storage_range_agree (vyperStorageBackend$get_storage cx es tr)
     (if tr then contract_transient s else contract_storage s)
     slot (ArrayTV tv (Dynamic n))` by
    (irule storage_range_agree_of_live >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`cx`, `tr`] >> simp[] >> Cases_on `tr` >>
     gvs[stmt_state_rel_def, state_rel_def, storage_rel_def,
         transient_rel_def, vyperStorageBackendTheory.get_storage_def,
         vfmStateTheory.lookup_account_def]) >>
  `0 < type_slot_size (ArrayTV tv (Dynamic n))` by
    simp[type_slot_size_def] >>
  drule_all storage_range_agree_head >>
  Cases_on `tr` >> simp[] >> strip_tac >> simp[tload_def, sload_def]
  >- (drule array_len_ok_TLOAD >>
      disch_then (qspecl_then [`cenv.ce_is_ctor`, `cenv.ce_imm_alloca`, `cnt`] mp_tac) >>
      simp[tload_def]) >>
  drule array_len_ok_SLOAD >>
  disch_then (qspecl_then [`cenv.ce_is_ctor`, `cenv.ce_imm_alloca`, `cnt`] mp_tac) >>
  simp[sload_def]
QED

Theorem target_storage_header_load:
  compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca
    (if tr then LocTransient else LocStorage) base_op sa = (dst,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand base_op s = SOME w ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      eval_operand dst t = SOME (if tr then tload w s else sload w s) /\
      stmt_state_rel ctx func cenv cx es t /\
      (!x v. not_fresh_at sa x /\ lookup_var x s = SOME v ==>
             lookup_var x t = SOME v) /\
      t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  qexists_tac `update_var out (if tr then tload w s else sload w s) s
                with vs_inst_idx := SUC s.vs_inst_idx` >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (simp[not_fresh_at_def, Abbr `out`] >> metis_tac[LESS_EQ_REFL]) >>
  `not_local_ptr cenv es.scopes out` by
    (qunabbrev_tac `out` >> irule local_ptrs_reserved_fresh >>
     metis_tac[LESS_EQ_REFL]) >>
  `dst = Var out /\ sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts)` by
    (Cases_on `tr` >>
     gvs[compile_ptr_load_def, Abbr `out`, emit_op_def, comp_bind_def,
         fresh_var_def, fresh_id_def, comp_ignore_bind_def, comp_return_def, emit_def]) >>
  rpt conj_tac
  >- (pure_rewrite_tac[gas_marked_path_def, COND_CLAUSES] >>
      qunabbrev_tac `out` >> Cases_on `tr` >>
      rule_assum_tac (REWRITE_RULE [compile_ptr_load_def]) >>
      irule emit_op_zero_path >> simp[]
      >- (qexistsl_tac [`[base_op]`, `dst`, `TLOAD`, `sb`] >>
          simp[is_terminator_def, step_inst_base_def, exec_read1_def]) >>
      qexistsl_tac [`[base_op]`, `dst`, `SLOAD`, `sb`] >>
      simp[is_terminator_def, step_SLOAD])
  >- simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
  >- (simp[stmt_state_rel_inst_idx] >> irule stmt_state_rel_update_var >> simp[])
  >- (rpt strip_tac >>
      simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      metis_tac[lookup_var_def]) >>
  simp[update_var_def]
QED

Theorem target_storage_header_compile:
  compile_ptr_load ctor imm (if tr then LocTransient else LocStorage) base_op sa = (dst,sb) ==>
  cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
  (!x. dst = Var x ==> not_fresh_at sb x)
Proof
  Cases_on `tr` >>
  simp[compile_ptr_load_def, emit_op_def, comp_bind_def, fresh_var_def,
       fresh_id_def, comp_ignore_bind_def, comp_return_def, emit_def] >>
  strip_tac >> gvs[cs_extends_def, not_fresh_at_def, IS_PREFIX_APPEND] >> simp[]
QED

Theorem target_storage_dynamic_array_path:
  compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca
    (if tr then LocTransient else LocStorage) base_op sa = (len_op,sm) /\
  comp_ignore_bind (array_bounds_check idx_op len_op sgn)
    (array_elem_ptr base_op idx_op T ws esz) sm = (dst,sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. base_op = Var x ==> not_fresh_at sa x) /\
  (!x. idx_op = Var x ==> not_fresh_at sa x) /\
  (!l. base_op <> Label l) /\ (!l. idx_op <> Label l) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  idx_in_range sgn i (if tr then tload b s else sload b s) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      eval_operand dst t = SOME (b + n2w ws + i * n2w esz) /\
      stmt_state_rel ctx func cenv cx es t /\
      (!x v. not_fresh_at sa x /\ lookup_var x s = SOME v ==>
             lookup_var x t = SOME v) /\
      (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==>
                FLOOKUP t.vs_allocas aid = SOME a) /\
      t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  drule target_storage_header_compile >> strip_tac >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!x. base_op = Var x ==> not_fresh_at sm x) /\
   (!x. idx_op = Var x ==> not_fresh_at sm x)` by
    metis_tac[not_fresh_at_mono] >>
  drule_all target_storage_header_load >> strip_tac >>
  `eval_operand base_op t = SOME b /\ eval_operand idx_op t = SOME i` by
    (conj_tac >> irule eval_operand_frame >> simp[] >>
     qexistsl_tac [`sa`, `s`] >> simp[]) >>
  drule_all target_array_check_ptr_path >> strip_tac >>
  qexists_tac `t'` >> conj_tac
  >- (qpat_x_assum `gas_marked_path F ctx func s 0 (OK t)` mp_tac >>
      qpat_x_assum `gas_marked_path F ctx func t 0 (OK t')` mp_tac >>
      metis_tac[gas_marked_path_then, ADD_CLAUSES]) >>
  simp[] >> rpt strip_tac >>
  `not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >> metis_tac[]
QED

Theorem target_storage_dynamic_array_abort_path:
  compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca
    (if tr then LocTransient else LocStorage) base_op sa = (len_op,sm) /\
  comp_ignore_bind (array_bounds_check idx_op len_op sgn)
    (array_elem_ptr base_op idx_op T ws esz) sm = (dst,sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. idx_op = Var x ==> not_fresh_at sa x) /\
  (!l. idx_op <> Label l) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  ~idx_in_range sgn i (if tr then tload b s else sload b s) ==>
  ?t. gas_marked_path F ctx func s 0 (Abort Revert_abort t)
Proof
  strip_tac >>
  drule target_storage_header_compile >> strip_tac >>
  `!x. idx_op = Var x ==> not_fresh_at sm x` by
    metis_tac[not_fresh_at_mono] >>
  drule_all target_storage_header_load >> strip_tac >>
  `eval_operand idx_op t = SOME i` by
    (irule eval_operand_frame >> simp[] >> qexistsl_tac [`sa`, `s`] >> simp[]) >>
  drule_all target_array_check_ptr_abort_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t'` >>
  qpat_x_assum `gas_marked_path F ctx func s 0 (OK t)` mp_tac >>
  qpat_x_assum `gas_marked_path F ctx func t 0 (Abort Revert_abort t')` mp_tac >>
  metis_tac[gas_marked_path_then, ADD_CLAUSES]
QED

Theorem target_storage_array_path:
  compile_array_subscript base_op idx_op dyn cnt ws esz sgn
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca
      (if tr then LocTransient else LocStorage)) sa = (dst,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. base_op = Var x ==> not_fresh_at sa x) /\
  (!x. idx_op = Var x ==> not_fresh_at sa x) /\
  (!l. base_op <> Label l) /\ (!l. idx_op <> Label l) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  idx_in_range sgn i (if dyn then (if tr then tload b s else sload b s) else n2w cnt) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      eval_operand dst t = SOME ((if dyn then b + n2w ws else b) + i * n2w esz) /\
      stmt_state_rel ctx func cenv cx es t /\
      (!x v. not_fresh_at sa x /\ lookup_var x s = SOME v ==>
             lookup_var x t = SOME v) /\
      (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==>
                FLOOKUP t.vs_allocas aid = SOME a) /\
      t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  reverse (Cases_on `dyn`) >>
  simp[compile_array_subscript_split, comp_bind_def, comp_return_def]
  >- (strip_tac >>
      `eval_operand (Lit (n2w cnt)) s = SOME (n2w cnt)` by simp[eval_operand_def] >>
      `!x. Lit (n2w cnt) = Var x ==> not_fresh_at sa x` by simp[] >>
      drule_all target_array_check_ptr_path >> simp[]) >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_ptr_load _ _ _ _ sa = (len_op,sm)` >>
  drule target_storage_header_compile >> strip_tac >>
  `straight_fresh (comp_ignore_bind (array_bounds_check idx_op len_op sgn)
     (array_elem_ptr base_op idx_op T ws esz))` by
    simp[straight_fresh_array_check_ptr] >>
  drule_all straight_fresh_cs_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all target_storage_dynamic_array_path >> simp[]
QED

Theorem target_storage_array_abort_path:
  compile_array_subscript base_op idx_op dyn cnt ws esz sgn
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca
      (if tr then LocTransient else LocStorage)) sa = (dst,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. idx_op = Var x ==> not_fresh_at sa x) /\ (!l. idx_op <> Label l) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  ~idx_in_range sgn i (if dyn then (if tr then tload b s else sload b s) else n2w cnt) ==>
  ?t. gas_marked_path F ctx func s 0 (Abort Revert_abort t)
Proof
  reverse (Cases_on `dyn`) >>
  simp[compile_array_subscript_split, comp_bind_def, comp_return_def]
  >- (strip_tac >>
      `eval_operand (Lit (n2w cnt)) s = SOME (n2w cnt)` by simp[eval_operand_def] >>
      `!x. Lit (n2w cnt) = Var x ==> not_fresh_at sa x` by simp[] >>
      drule_all target_array_check_ptr_abort_path >> simp[]) >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_ptr_load _ _ _ _ sa = (len_op,sm)` >>
  drule target_storage_header_compile >> strip_tac >>
  `straight_fresh (comp_ignore_bind (array_bounds_check idx_op len_op sgn)
     (array_elem_ptr base_op idx_op T ws esz))` by
    simp[straight_fresh_array_check_ptr] >>
  drule_all straight_fresh_cs_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all target_storage_dynamic_array_abort_path >> simp[]
QED

Theorem target_storage_array_range:
  evaluate_type tenv ity = SOME itv /\ value_has_type itv (IntV i) /\
  cnt < dimword(:256) /\
  (dyn ==> w2n (lookup_storage slot (get_storage cx es tr)) <= cnt) /\
  (dyn ==> (if tr then tload slot s else sload slot s) =
             lookup_storage slot (get_storage cx es tr)) ==>
  (idx_in_range (is_signed_type ity) (i2w i)
     (if dyn then (if tr then tload slot s else sload slot s) else n2w cnt) <=>
   0 <= i /\ Num i < cnt /\
   (dyn ==> Num i < w2n (lookup_storage slot (get_storage cx es tr))))
Proof
  Cases_on `dyn` >> simp[] >> strip_tac
  >- (`idx_in_range (is_signed_type ity) (i2w i)
         (n2w (w2n (lookup_storage slot (get_storage cx es tr)))) <=>
       0 <= i /\ Num i < w2n (lookup_storage slot (get_storage cx es tr))` by
        (irule target_typed_index_range >> metis_tac[w2n_lt]) >>
      gvs[] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  drule_all target_typed_index_range >> simp[]
QED

Theorem target_storage_array_offset:
  0 <= i ==>
  ((if dyn then slot + n2w 1 else slot) + i2w i * n2w (type_slot_size etv) =
   (slot : bytes32) + n2w ((if dyn then 1 else 0) + Num i * type_slot_size etv))
Proof
  strip_tac >>
  `i = &Num i` by simp[integerTheory.INT_OF_NUM] >>
  qpat_x_assum `i = &Num i` SUBST1_TAC >>
  Cases_on `dyn` >> simp[integer_wordTheory.i2w_pos, word_mul_n2w,
    word_add_n2w, WORD_ADD_ASSOC] >>
  pure_rewrite_tac[GSYM word_add_n2w] >>
  metis_tac[WORD_ADD_ASSOC, WORD_ADD_COMM]
QED

Theorem target_storage_array_type_bound:
  evaluate_type tenv (ArrayT ety bd) = SOME (ArrayTV etv bd) ==>
  bound_length bd < dimword(:256) /\ evaluate_type tenv ety = SOME etv
Proof
  rw[evaluate_type_def, AllCaseEqs()] >> Cases_on `bd` >>
  gvs[type_slot_size_def, vyperASTTheory.bound_length_def] >>
  `n <= n * type_slot_size etv` by
    (Cases_on `type_slot_size etv` >> gvs[MULT_CLAUSES]) >> decide_tac
QED

Theorem target_storage_array_live_range:
  stmt_state_rel ctx func cenv cx es s /\
  eval_operand base_op s = SOME slot /\
  evaluate_type (get_tenv cx) (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt)) =
    SOME (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) /\
  (dyn ==> w2n (lookup_storage slot (get_storage cx es tr)) <= cnt) /\
  storage_read_live cx tr (get_storage cx es tr) slot
    (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) /\
  w2n slot + type_slot_size (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) <= dimword(:256) /\
  evaluate_type (get_tenv cx) ity = SOME itv /\ value_has_type itv (IntV i) ==>
  (idx_in_range (is_signed_type ity) (i2w i)
     (if dyn then (if tr then tload slot s else sload slot s) else n2w cnt) <=>
   0 <= i /\ Num i < cnt /\
   (dyn ==> Num i < w2n (lookup_storage slot (get_storage cx es tr))))
Proof
  strip_tac >>
  drule_all target_storage_array_type_bound >> strip_tac >>
  `cnt < dimword(:256)` by
    (Cases_on `dyn` >> gvs[vyperASTTheory.bound_length_def]) >>
  `(dyn ==> w2n (lookup_storage slot (get_storage cx es tr)) <= cnt) /\
   (dyn ==> (if tr then tload slot s else sload slot s) =
      lookup_storage slot (get_storage cx es tr))` by
    (Cases_on `dyn` >> gvs[] >>
     `w2n slot + type_slot_size (ArrayTV etv (Dynamic cnt)) <= dimword(:256)` by
       decide_tac >>
     drule_all target_storage_array_len_ok >> simp[]) >>
  drule_all target_storage_array_range >> simp[]
QED

Theorem target_storage_array_error_suffix:
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
  fn_has_code sm sb func /\ local_ptrs_reserved cenv sm /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!x. idx = Var x ==> not_fresh_at sm x) /\ (!l. idx <> Label l) /\
  extend_place cx
    (PlaceR (StoragePlace tr slot (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt))))
    (ValueSubscript (IntV i)) es = (INR err,es') ==>
  (?u. gas_marked_path F ctx func s 0 (Abort Revert_abort u)) /\
  (?msg. err = Error (RuntimeError msg)) /\ es' = es
Proof
  strip_tac >>
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
  drule_all target_storage_array_abort_path >> strip_tac >>
  conj_tac >- metis_tac[] >>
  Cases_on `dyn` >> gvs[AllCaseEqs()]
QED

Theorem target_storage_array_suffix:
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
  fn_has_code sm sb func /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!x. idx = Var x ==> not_fresh_at sm x) /\ (!l. idx <> Label l) /\
  (!l. FST rb <> Label l) /\ (!x. dst = Var x ==> not_fresh_at sb x) /\
  extend_place cx
    (PlaceR (StoragePlace tr slot (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt))))
    (ValueSubscript (IntV i)) es = (INL pv',es') ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
      target_post ctx func cenv cx es0 sa sb s0 es' pv' (Type ety)
        (dst,SOME (slot_loc tr),SOME (ValPT ety)) u /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
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
  drule_all target_storage_array_path >> strip_tac >>
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
