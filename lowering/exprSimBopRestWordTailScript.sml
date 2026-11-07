(* Header and located-array composition for nonliteral word membership. *)
Theory exprSimBopRestWordTail
Ancestors
  exprSimBopRestWordIterate exprSimBopRestWordBasics
  exprSimBopRestWordIndex exprSimBopRestWordStorageLoads

(* Located representations depend on the value read, not the syntax of the
   captured source result.  Normalize once before using value-load adapters. *)

(* Discharge the loop's element oracle at the actual arithmetic endpoint.
   No control-position premise is needed for this straight-line loader. *)
Theorem rest_word_memory_element_run:
  vv_post ctx func cenv cx e es va vb s0 es' (Value (ArrayV av)) vv p /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
  expr_type e = ArrayT ty bd /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV et bd) /\
  eval_operand (vv_operand vv) p = SOME baseword /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME et /\
  value_has_type (ArrayTV et bd) (ArrayV av) /\
  i < array_length (ArrayTV et bd) av /\
  array_index (ArrayTV et bd) av (&i) = SOME value /\
  context$compile_ptr_load ctor imm LocMemory addr cl = (v,cm) /\
  eval_operand addr p = SOME
    (baseword + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32)) ==>
  ?q. run_inst_seq (emitted_insts cl cm) p = OK q /\
      eval_operand v q = SOME (typed_val_to_w256 et value) /\
      run_inst_seq_mem_ok (emitted_insts cl cm) p
Proof
  strip_tac >>
  `vv_location vv = NONE \/ vv_location vv = SOME LocMemory` by simp[] >>
  `evaluate_type (get_tenv cx) (ArrayT ty bd) = SOME (ArrayTV et bd)` by metis_tac[] >>
  `vv_holds cenv cx (ArrayT ty bd) (Value (ArrayV av)) vv es' p` by
    fs[loweringPostsTheory.vv_post_def] >>
  `val_in_memory (ArrayTV et bd) (ArrayV av) (w2n baseword) p.vs_memory` by
    (irule exprSimBopRestWordLoadsTheory.rest_word_vv_memory_rep >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl [`cenv`, `cx`, `es'`, `ty`, `vv`] >> simp[]) >>
  `w2n (baseword + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32)) =
   w2n baseword + (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32` by
    (drule exprSimBopRestWordLoadsTheory.rest_word_vv_memory_offset >> simp[]) >>
  `type_memory_size et = 32` by metis_tac[exprSimPropsTheory.word_tv_memory_size] >>
  drule_all exprSimBopRestWordLoadsTheory.rest_word_array_memory_load >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts cl cm) p` by
    (drule exprSimBopRestWordLoadSafetyTheory.rest_word_array_memory_load_mem_ok >>
     simp[] >> disch_then irule >> goal_assum (drule_at Any) >> simp[] >>
     qexists `i` >> simp[]) >>
  drule (Q.INST [`b` |-> `0w`] exprSimBopRestWordLoadPathTheory.rest_word_ptr_load_run) >>
  simp[] >> disch_then (qspecl_then [`p`,
    `baseword + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32)`] mp_tac) >>
  simp[GSYM valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  strip_tac >> goal_assum (drule_at Any) >>
  qpat_x_assum `mem_word_at _ _ = _` mp_tac >> simp[]
QED


(* Slot-addressed loaders need no memory frontier premise. *)
Theorem rest_word_storage_element_run:
  storage_holds cx tr (ArrayT ty bd) (Value (ArrayV av)) baseword es' p /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME et /\
  i < array_length (ArrayTV et bd) av /\
  array_index (ArrayTV et bd) av (&i) = SOME value /\
  context$compile_ptr_load ctor imm (if tr then LocTransient else LocStorage) addr cl = (v,cm) /\
  eval_operand addr p = SOME
    (baseword + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 1) + i)) ==>
  ?q. run_inst_seq (emitted_insts cl cm) p = OK q /\
      eval_operand v q = SOME (typed_val_to_w256 et value) /\
      run_inst_seq_mem_ok (emitted_insts cl cm) p
Proof
  strip_tac >>
  `read_result cx (Value (ArrayV av)) es' = (INL (ArrayV av), es')` by
    simp[vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  drule_all exprSimBopRestWordStorageTheory.rest_word_storage_array_load >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts cl cm) p` by
    (drule exprSimBopRestWordLoadSafetyTheory.rest_word_ptr_load_mem_ok >>
     Cases_on `tr` >> simp[]) >>
  Cases_on `tr` >> gvs[] >>
  drule (Q.INST [`b` |-> `0w`] exprSimBopRestWordLoadPathTheory.rest_word_ptr_load_run) >>
  simp[] >> disch_then (qspecl_then [`p`,
    `baseword + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 1) + i)`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem rest_word_immutable_element_run:
  stmt_state_rel ctx func cenv cx es' p /\
  immutable_holds cenv cx (ArrayT ty bd) (Value (ArrayV av)) baseword es' p /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME et /\
  value_has_type (ArrayTV et bd) (ArrayV av) /\
  i < array_length (ArrayTV et bd) av /\
  array_index (ArrayTV et bd) av (&i) = SOME value /\
  context$compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocCode addr cl = (v,cm) /\
  eval_operand addr p = SOME
    (baseword + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32)) ==>
  ?q. run_inst_seq (emitted_insts cl cm) p = OK q /\
      eval_operand v q = SOME (typed_val_to_w256 et value) /\
      run_inst_seq_mem_ok (emitted_insts cl cm) p
Proof
  strip_tac >>
  drule_all exprSimBopRestWordLoadsTheory.rest_word_array_immutable_load >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts cl cm) p` by
    (drule_all exprSimBopRestWordLoadSafetyTheory.rest_word_array_immutable_load_mem_ok >> simp[]) >>
  `(cenv.ce_is_ctor /\ cenv.ce_imm_alloca <> NONE ==>
    eval_operand (THE cenv.ce_imm_alloca) p = SOME 0w)` by
    (fs[exprLoweringPropsTheory.stmt_state_rel_def, compileEnvTheory.immutable_base_zero_def] >>
     Cases_on `cenv.ce_imm_alloca` >> gvs[]) >>
  drule (Q.INST [`b` |-> `0w`] exprSimBopRestWordLoadPathTheory.rest_word_ptr_load_run) >> simp[] >>
  disch_then (qspecl_then [`p`,
    `baseword + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32)`] mp_tac) >>
  Cases_on `cenv.ce_is_ctor` >> Cases_on `cenv.ce_imm_alloca` >>
  gvs[wordsTheory.WORD_ADD_0] >> metis_tac[]
QED

Theorem rest_word_word_stride:
  is_word_type ty ==> elem_size_in_location cenv loc ty = word_scale loc
Proof
  Cases_on `loc` >> Cases_on `ty` >>
  gvs[compileEnvTheory.is_word_type_def, compileEnvTheory.elem_size_in_location_def,
    compileEnvTheory.type_memory_bytes_def, compileEnvTheory.word_scale_def,
    compileEnvTheory.is_slot_addressed_def] >>
  Cases_on `b` >> gvs[compileEnvTheory.is_word_type_def,
    compileEnvTheory.type_memory_bytes_def] >>
  Cases_on `b'` >> gvs[compileEnvTheory.is_word_type_def,
    compileEnvTheory.type_memory_bytes_def]
QED

Theorem rest_word_located_element_run:
  vv_post ctx func cenv cx e es va vb s0 es' (Value (ArrayV av)) vv p /\
  loc = (case vv_location vv of SOME l => l | NONE => LocMemory) /\
  loc <> LocCalldata /\
  expr_type e = ArrayT ty bd /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV et bd) /\
  eval_operand (vv_operand vv) p = SOME baseword /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME et /\
  value_has_type (ArrayTV et bd) (ArrayV av) /\
  i < array_length (ArrayTV et bd) av /\
  array_index (ArrayTV et bd) av (&i) = SOME value /\
  context$compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc addr cl = (v,cm) /\
  eval_operand addr p = SOME
    (baseword + n2w ((case bd of Fixed _ => 0 | Dynamic _ => word_scale loc) +
                     i * word_scale loc)) ==>
  ?q. run_inst_seq (emitted_insts cl cm) p = OK q /\
      eval_operand v q = SOME (typed_val_to_w256 et value) /\
      run_inst_seq_mem_ok (emitted_insts cl cm) p
Proof
  strip_tac >>
  Cases_on `vv_location vv = NONE \/ vv_location vv = SOME LocMemory`
  >- (`loc = LocMemory` by (Cases_on `vv_location vv` >> gvs[]) >>
      gvs[compileEnvTheory.word_scale_def] >>
      drule rest_word_memory_element_run >> simp[] >>
      disch_then irule >> goal_assum (drule_at Any) >> simp[] >>
      metis_tac[]) >>
  `vv_holds cenv cx (ArrayT ty bd) (Value (ArrayV av)) vv es' p /\
   stmt_state_rel ctx func cenv cx es' p` by
    fs[loweringPostsTheory.vv_post_def] >>
  Cases_on `vv` >>
  gvs[contextTheory.vv_location_def, contextTheory.vv_operand_def,
    loweringPostsTheory.vv_holds_def] >>
  Cases_on `p'.ptr_location` >>
  gvs[compileEnvTheory.word_scale_def,
    vyperStateTheory.read_result_def, vyperStateTheory.return_def]
  >- (drule (Q.INST [`tr` |-> `F`] rest_word_storage_element_run) >>
      simp[] >> disch_then assume_tac >> metis_tac[]) 
  >- (drule (Q.INST [`tr` |-> `T`] rest_word_storage_element_run) >>
      simp[] >> disch_then assume_tac >> metis_tac[]) >>
  drule rest_word_immutable_element_run >> simp[] >>
  disch_then assume_tac >> metis_tac[]
QED

(* Shared fixed/dynamic semantic consumer; the representation endpoint sm
   remains the operand endpoint even when cs follows the dynamic header. *)
Theorem rest_word_located_search:
  compile_array_membership_loop needleop (vv_operand vv) lenop
    (word_scale loc) (case bd of Fixed _ => 0 | Dynamic _ => word_scale loc)
    (context$compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc) is_in cs = (out,ct) /\
  fn_has_code cs ct fn /\
  vv_post ctx func cenv cx e es sa sm s0 es' tv vv s /\
  read_result cx tv es' = (INL (ArrayV av), es') /\
  loc = (case vv_location vv of SOME l => l | NONE => LocMemory) /\ loc <> LocCalldata /\
  expr_type e = ArrayT ty bd /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV et bd) /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME et /\
  value_has_type (ArrayTV et bd) (ArrayV av) /\ value_has_type et needle /\
  eval_operand needleop s = SOME (typed_val_to_w256 et needle) /\
  eval_operand (vv_operand vv) s = SOME baseword /\
  eval_operand lenop s = SOME (n2w len) /\ len = array_length (ArrayTV et bd) av /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  sm.cs_next_var <= cs.cs_next_var /\
  (!z. vv_operand vv = Var z ==> not_fresh_at sm z) /\
  (!z. needleop = Var z \/ vv_operand vv = Var z \/ lenop = Var z ==> not_fresh_at cs z) /\
  len < dimword (:256) /\
  s.vs_current_bb = cs.cs_current_bb /\
  s.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~s.vs_halted ==>
  ?t. gas_marked_path memory execctx fn s 0 (OK t) /\
      t.vs_current_bb = ct.cs_current_bb /\
      t.vs_inst_idx = LENGTH ct.cs_current_insts /\ ~t.vs_halted /\
      vv_post ctx func cenv cx e es sa sm s0 es' tv vv t /\
      eval_operand needleop t = SOME (typed_val_to_w256 et needle) /\
      eval_operand (vv_operand vv) t = SOME baseword /\
      eval_operand out t = SOME (bool_to_word
        (if is_in then evaluate_in_array (ArrayTV et bd) needle av
         else ~evaluate_in_array (ArrayTV et bd) needle av))
Proof
  strip_tac >>
  qabbrev_tac `elem = \i. typed_val_to_w256 et
    (THE (array_index (ArrayTV et bd) av (&i)))` >>
  `!i. i < len ==> array_index (ArrayTV et bd) av (&i) =
      SOME (THE (array_index (ArrayTV et bd) av (&i)))` by
    (rpt strip_tac >>
     `valid_index (ArrayTV et bd) av (&i)` by
       simp[vyperArrayTheory.valid_index_def] >>
     drule vyperArrayTheory.array_index_valid >>
     Cases_on `array_index (ArrayTV et bd) av (&i)` >> simp[]) >>
  `evaluate_in_array (ArrayTV et bd) needle av <=>
    ?i. i < len /\ elem i = typed_val_to_w256 et needle` by
    (drule_all rest_word_array_word_membership >>
     simp[Abbr `elem`] >> metis_tac[optionTheory.THE_DEF]) >>
  `!h cl cm v i p.
    rest_word_loop_prefix needleop (vv_operand vv) lenop (word_scale loc)
      (case bd of Fixed _ => 0 | Dynamic _ => word_scale loc) cs = (h,cl) /\
    context$compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc h.rw_addr cl = (v,cm) /\
    i < len /\
    rest_word_search_rep ctx func cenv cx e es sa sm s0 es' tv vv
      needleop (typed_val_to_w256 et needle) lenop len p /\
    eval_operand (vv_operand vv) p = SOME baseword /\
    eval_operand h.rw_addr p = SOME (baseword + n2w
      ((case bd of Fixed _ => 0 | Dynamic _ => word_scale loc) + i * word_scale loc)) ==>
    ?q. run_inst_seq (emitted_insts cl cm) p = OK q /\
        eval_operand v q = SOME (elem i) /\
        (memory ==> run_inst_seq_mem_ok (emitted_insts cl cm) p)` by
    (rpt gen_tac >> simp[rest_word_search_rep_def] >> strip_tac >>
     `vv_post ctx func cenv cx e es sa sm s0 es' (Value (ArrayV av)) vv p` by
       (irule exprSimUnwrapPropsTheory.vv_post_read_result >> qexists_tac `tv` >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     `evaluate_type (get_tenv cx) (ArrayT ty bd) = SOME (ArrayTV et bd)` by metis_tac[] >>
     drule rest_word_located_element_run >> simp[Abbr `elem`] >>
     disch_then assume_tac >> metis_tac[]) >>
  `rest_word_search_rep ctx func cenv cx e es sa sm s0 es' tv vv
      needleop (typed_val_to_w256 et needle) lenop len s` by
    simp[rest_word_search_rep_def] >>
  drule_all rest_word_compiled_search >>
  simp[rest_word_search_rep_def] >> metis_tac[]
QED

Theorem rest_word_fixed_tail:
  compile_var_array_membership cenv needleop vv (ArrayT ty (Fixed n)) is_in sm = (out,ct) /\
  fn_has_code sm ct fn /\
  vv_post ctx func cenv cx e es sa sm s0 es' tv vv s /\
  read_result cx tv es' = (INL (ArrayV av), es') /\
  loc = (case vv_location vv of SOME l => l | NONE => LocMemory) /\ loc <> LocCalldata /\
  expr_type e = ArrayT ty (Fixed n) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV et (Fixed n)) /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME et /\
  value_has_type (ArrayTV et (Fixed n)) (ArrayV av) /\ value_has_type et needle /\
  eval_operand needleop s = SOME (typed_val_to_w256 et needle) /\
  eval_operand (vv_operand vv) s = SOME baseword /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  (!z. needleop = Var z \/ vv_operand vv = Var z ==> not_fresh_at sm z) /\
  n < dimword (:256) /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~s.vs_halted ==>
  ?t. gas_marked_path memory execctx fn s 0 (OK t) /\
      t.vs_current_bb = ct.cs_current_bb /\
      t.vs_inst_idx = LENGTH ct.cs_current_insts /\ ~t.vs_halted /\
      vv_post ctx func cenv cx e es sa sm s0 es' tv vv t /\
      eval_operand needleop t = SOME (typed_val_to_w256 et needle) /\
      eval_operand (vv_operand vv) t = SOME baseword /\
      eval_operand out t = SOME (bool_to_word
        (if is_in then evaluate_in_array (ArrayTV et (Fixed n)) needle av
         else ~evaluate_in_array (ArrayTV et (Fixed n)) needle av))
Proof
  strip_tac >>
  `array_length (ArrayTV et (Fixed n)) av = n` by
    metis_tac[exprSimBopRestWordLoadsTheory.rest_word_array_fixed_length] >>
  `elem_size_in_location cenv loc ty = word_scale loc` by metis_tac[rest_word_word_stride] >>
  `compile_array_membership_loop needleop (vv_operand vv) (Lit (n2w n))
    (word_scale loc) 0
    (context$compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc) is_in sm = (out,ct)` by
    (qpat_x_assum `compile_var_array_membership _ _ _ _ _ _ = _` mp_tac >>
     simp[rest_word_fixed_dispatch] >> metis_tac[]) >>
  `!z. vv_operand vv = Var z ==> not_fresh_at sm z` by metis_tac[] >>
  `!z. needleop = Var z \/ vv_operand vv = Var z \/ Lit (n2w n) = Var z ==>
       not_fresh_at sm z` by (simp[] >> metis_tac[]) >>
  `sm.cs_next_var <= sm.cs_next_var` by simp[] >>
  `eval_operand (Lit (n2w n)) s = SOME (n2w n)` by simp[venomStateTheory.eval_operand_def] >>
  drule (SRULE [] (Q.INST [`bd` |-> `Fixed n`] rest_word_located_search)) >>
  simp[] >> disch_then irule >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem rest_word_storage_header_run:
  storage_holds cx tr (ArrayT ty (Dynamic cap)) (Value (ArrayV av)) w es' p /\
  evaluate_type (get_tenv cx) ty = SOME et /\
  context$compile_ptr_load ctor imm (if tr then LocTransient else LocStorage) addr cl = (v,cm) /\
  eval_operand addr p = SOME w ==>
  ?q. run_inst_seq (emitted_insts cl cm) p = OK q /\
      eval_operand v q = SOME (n2w (array_length (ArrayTV et (Dynamic cap)) av)) /\
      run_inst_seq_mem_ok (emitted_insts cl cm) p
Proof
  strip_tac >>
  `read_result cx (Value (ArrayV av)) es' = (INL (ArrayV av), es')` by
    simp[vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  drule_all exprSimBopRestWordStorageTheory.rest_word_storage_array_length >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts cl cm) p` by
    (drule exprSimBopRestWordLoadSafetyTheory.rest_word_ptr_load_mem_ok >>
     Cases_on `tr` >> simp[]) >>
  Cases_on `tr` >> gvs[] >>
  drule (Q.INST [`b` |-> `0w`] exprSimBopRestWordLoadPathTheory.rest_word_ptr_load_run) >>
  simp[] >> disch_then (qspecl_then [`p`, `w`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem rest_word_memory_header_run:
  vv_post ctx func cenv cx e es va vb s0 es' (Value (ArrayV av)) vv p /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
  expr_type e = ArrayT ty (Dynamic cap) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV et (Dynamic cap)) /\
  eval_operand (vv_operand vv) p = SOME w /\
  value_has_type (ArrayTV et (Dynamic cap)) (ArrayV av) /\
  context$compile_ptr_load ctor imm LocMemory addr cl = (v,cm) /\
  eval_operand addr p = SOME w ==>
  ?q. run_inst_seq (emitted_insts cl cm) p = OK q /\
      eval_operand v q = SOME (n2w (array_length (ArrayTV et (Dynamic cap)) av)) /\
      run_inst_seq_mem_ok (emitted_insts cl cm) p
Proof
  strip_tac >>
  `evaluate_type (get_tenv cx) (ArrayT ty (Dynamic cap)) =
    SOME (ArrayTV et (Dynamic cap))` by metis_tac[] >>
  `vv_holds cenv cx (ArrayT ty (Dynamic cap)) (Value (ArrayV av)) vv es' p` by
    fs[loweringPostsTheory.vv_post_def] >>
  `val_in_memory (ArrayTV et (Dynamic cap)) (ArrayV av) (w2n w) p.vs_memory` by
    (irule exprSimBopRestWordLoadsTheory.rest_word_vv_memory_rep >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl [`cenv`, `cx`, `es'`, `ty`, `vv`] >> simp[]) >>
  drule_all exprSimBopRestWordLoadsTheory.rest_word_array_memory_header >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts cl cm) p` by
    (drule exprSimBopRestWordLoadSafetyTheory.rest_word_array_memory_header_mem_ok >>
     simp[] >> disch_then irule >> goal_assum (drule_at Any) >> simp[] >>
     metis_tac[]) >>
  drule (Q.INST [`b` |-> `0w`] exprSimBopRestWordLoadPathTheory.rest_word_ptr_load_run) >>
  simp[] >> disch_then (qspecl_then [`p`, `w`] mp_tac) >>
  simp[GSYM valueEncodingPropsTheory.mem_word_at_eq_mload] >> metis_tac[]
QED

Theorem rest_word_immutable_header_run:
  stmt_state_rel ctx func cenv cx es' p /\
  immutable_holds cenv cx (ArrayT ty (Dynamic cap)) (Value (ArrayV av)) w es' p /\
  evaluate_type (get_tenv cx) ty = SOME et /\
  value_has_type (ArrayTV et (Dynamic cap)) (ArrayV av) /\
  context$compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocCode addr cl = (v,cm) /\
  eval_operand addr p = SOME w ==>
  ?q. run_inst_seq (emitted_insts cl cm) p = OK q /\
      eval_operand v q = SOME (n2w (array_length (ArrayTV et (Dynamic cap)) av)) /\
      run_inst_seq_mem_ok (emitted_insts cl cm) p
Proof
  strip_tac >>
  drule_all exprSimBopRestWordLoadsTheory.rest_word_array_immutable_header >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts cl cm) p` by
    (drule_all exprSimBopRestWordLoadSafetyTheory.rest_word_array_immutable_header_mem_ok >> simp[]) >>
  `(cenv.ce_is_ctor /\ cenv.ce_imm_alloca <> NONE ==>
    eval_operand (THE cenv.ce_imm_alloca) p = SOME 0w)` by
    (fs[exprLoweringPropsTheory.stmt_state_rel_def, compileEnvTheory.immutable_base_zero_def] >>
     Cases_on `cenv.ce_imm_alloca` >> gvs[]) >>
  drule (Q.INST [`b` |-> `0w`] exprSimBopRestWordLoadPathTheory.rest_word_ptr_load_run) >> simp[] >>
  disch_then (qspecl_then [`p`, `w`] mp_tac) >>
  Cases_on `cenv.ce_is_ctor` >> Cases_on `cenv.ce_imm_alloca` >>
  gvs[wordsTheory.WORD_ADD_0] >> metis_tac[]
QED

Theorem rest_word_located_header_run:
  vv_post ctx func cenv cx e es va vb s0 es' (Value (ArrayV av)) vv p /\
  loc = (case vv_location vv of SOME l => l | NONE => LocMemory) /\
  loc <> LocCalldata /\
  expr_type e = ArrayT ty (Dynamic cap) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV et (Dynamic cap)) /\
  eval_operand (vv_operand vv) p = SOME w /\
  evaluate_type (get_tenv cx) ty = SOME et /\
  value_has_type (ArrayTV et (Dynamic cap)) (ArrayV av) /\
  context$compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc addr cl = (v,cm) /\
  eval_operand addr p = SOME w ==>
  ?q. run_inst_seq (emitted_insts cl cm) p = OK q /\
      eval_operand v q = SOME (n2w (array_length (ArrayTV et (Dynamic cap)) av)) /\
      run_inst_seq_mem_ok (emitted_insts cl cm) p
Proof
  strip_tac >>
  Cases_on `vv_location vv = NONE \/ vv_location vv = SOME LocMemory`
  >- (`loc = LocMemory` by (Cases_on `vv_location vv` >> gvs[]) >>
      gvs[] >> drule rest_word_memory_header_run >> simp[] >>
      disch_then irule >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `vv_holds cenv cx (ArrayT ty (Dynamic cap)) (Value (ArrayV av)) vv es' p /\
   stmt_state_rel ctx func cenv cx es' p` by
    fs[loweringPostsTheory.vv_post_def] >>
  Cases_on `vv` >>
  gvs[contextTheory.vv_location_def, contextTheory.vv_operand_def,
    loweringPostsTheory.vv_holds_def] >>
  Cases_on `p'.ptr_location` >>
  gvs[vyperStateTheory.read_result_def, vyperStateTheory.return_def]
  >- (drule (Q.INST [`tr` |-> `F`] rest_word_storage_header_run) >>
      simp[] >> disch_then assume_tac >> metis_tac[])
  >- (drule (Q.INST [`tr` |-> `T`] rest_word_storage_header_run) >>
      simp[] >> disch_then assume_tac >> metis_tac[]) >>
  drule rest_word_immutable_header_run >> simp[] >>
  disch_then assume_tac >> metis_tac[]
QED

(* The header produces a fresh length operand, so frame only the captures
   that existed before it.  Do not require the new length to be old at sm. *)
Theorem rest_word_capture_load_frame:
  context$compile_ptr_load ctor imm loc addr cl = (op,cm) /\
  loc <> LocCalldata /\ sm.cs_next_var <= cl.cs_next_var /\
  vv_post ctx func cenv cx e es sa sm s0 es' tv vv s /\
  eval_operand needleop s = SOME needle /\
  eval_operand (vv_operand vv) s = SOME baseword /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  (!z. vv_operand vv = Var z ==> not_fresh_at sm z) /\
  (!z. needleop = Var z ==> not_fresh_at cl z) /\
  run_inst_seq (emitted_insts cl cm) s = OK t ==>
  vv_post ctx func cenv cx e es sa sm s0 es' tv vv t /\
  eval_operand needleop t = SOME needle /\
  eval_operand (vv_operand vv) t = SOME baseword
Proof
  strip_tac >>
  `rest_word_search_rep ctx func cenv cx e es sa sm s0 es' tv vv
    needleop needle (Lit 0w) 0 s` by
    simp[rest_word_search_rep_def, venomStateTheory.eval_operand_def] >>
  `rest_word_search_rep ctx func cenv cx e es sa sm s0 es' tv vv
    (vv_operand vv) baseword (Lit 0w) 0 s` by
    simp[rest_word_search_rep_def, venomStateTheory.eval_operand_def] >>
  `!z. vv_operand vv = Var z ==> not_fresh_at cl z` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!z. Lit 0w = Var z ==> not_fresh_at cl z` by simp[] >>
  drule_all rest_word_search_rep_load >>
  simp[rest_word_search_rep_def] >> strip_tac >>
  qpat_x_assum `rest_word_search_rep _ _ _ _ _ _ _ _ _ _ _ _ (vv_operand vv) _ _ _ _` kall_tac >>
  drule_all rest_word_search_rep_load >>
  simp[rest_word_search_rep_def]
QED

Theorem rest_word_ptr_load_marked:
  context$compile_ptr_load ctor imm loc addr cl = (op,cm) /\
  loc <> LocCalldata /\ fn_has_code cl cm fn /\ ~s.vs_halted /\
  s.vs_current_bb = cl.cs_current_bb /\
  s.vs_inst_idx = LENGTH cl.cs_current_insts /\
  run_inst_seq (emitted_insts cl cm) s = OK t /\
  (memory ==> run_inst_seq_mem_ok (emitted_insts cl cm) s) ==>
  gas_marked_path memory execctx fn s 0
    (OK (t with vs_inst_idx := LENGTH cm.cs_current_insts)) /\
  t.vs_current_bb = cm.cs_current_bb /\ ~t.vs_halted
Proof
  strip_tac >>
  drule_all exprSimBopRestWordLoadPathTheory.rest_word_ptr_load_code >> strip_tac >>
  drule_all exprSimBopRestWordLoadPathTheory.rest_word_ptr_load_run_frame >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts cl cm) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fragExecTheory.fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
     simp[listTheory.DROP_APPEND]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> GAS) (emitted_insts cl cm)` by
    (fs[listTheory.EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i _ ==> _` (qspec_then `i` mp_tac) >>
     simp[] >> rpt strip_tac >> gvs[venomInstTheory.is_terminator_def]) >>
  `gas_marked_path memory execctx fn s 0
    (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts cl cm)))` by
    (irule exprSimBopRestWordLoopPathTheory.rest_word_sequence_marked >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  gvs[] >> qpat_x_assum `t = _` (fn th => conj_tac >> simp[Once th])
QED

Theorem rest_word_capacity_check_run:
  eval_operand lenop s = SOME (n2w len) /\ len <= cap /\ cap < dimword (:256) ==>
  run_inst_seq
    [mk_inst id1 GT [lenop; Lit (n2w cap)] [invvar];
     mk_inst id2 ISZERO [Var invvar] [valid];
     mk_inst id3 ASSERT [Var valid] []] s =
  OK (update_var valid 1w (update_var invvar 0w s))
Proof
  strip_tac >>
  `len < dimword (:256)` by decide_tac >>
  `step_inst_base (mk_inst id1 GT [lenop; Lit (n2w cap)] [invvar]) s =
    OK (update_var invvar 0w s)` by
    (drule emitHelperPropsTheory.step_GT >>
     disch_then (qspecl_then [`Lit (n2w cap)`, `n2w cap`] mp_tac) >>
     simp[venomStateTheory.eval_operand_def, wordsTheory.w2n_n2w,
       venomExecSemanticsTheory.bool_to_word_def]) >>
  `step_inst_base (mk_inst id2 ISZERO [Var invvar] [valid]) (update_var invvar 0w s) =
    OK (update_var valid 1w (update_var invvar 0w s))` by
    (mp_tac (Q.SPECL [`Var invvar`, `0w`] emitHelperPropsTheory.step_ISZERO) >>
     simp[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
       venomStateTheory.update_var_def, finite_mapTheory.FLOOKUP_UPDATE,
       venomExecSemanticsTheory.bool_to_word_def]) >>
  `step_inst_base (mk_inst id3 ASSERT [Var valid] [])
    (update_var valid 1w (update_var invvar 0w s)) =
    OK (update_var valid 1w (update_var invvar 0w s))` by
    (irule emitHelperPropsTheory.step_ASSERT_ok >>
     simp[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
       venomStateTheory.update_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  simp[exprLoweringPropsTheory.run_inst_seq_def]
QED

Theorem rest_word_capacity_check_mem_ok:
  run_inst_seq_mem_ok
    [mk_inst id1 GT [lenop; Lit (n2w cap)] [invvar];
     mk_inst id2 ISZERO [Var invvar] [validvar];
     mk_inst id3 ASSERT [Var validvar] []] s
Proof
  irule fragExecMemTheory.run_inst_seq_mem_ok_every >>
  simp[venomInstTheory.mk_inst_def] >> rpt conj_tac >> gen_tac >>
  irule instMemFrontierTheory.below_frontier_no_ranges >> simp[]
QED

Theorem rest_word_capacity_check_shape:
  emit_op GT [lenop; Lit (n2w cap)] ca = (invop,cb) /\
  emit_op ISZERO [invop] cb = (validop,cc) /\
  emit_inst ASSERT [validop] [] cc = ((),cd) ==>
  ?invvar validvar.
    invop = Var invvar /\ validop = Var validvar /\
    emitted_insts ca cd =
      [mk_inst ca.cs_next_id GT [lenop; Lit (n2w cap)] [invvar];
       mk_inst (ca.cs_next_id + 1) ISZERO [Var invvar] [validvar];
       mk_inst (ca.cs_next_id + 2) ASSERT [Var validvar] []] /\
    cd.cs_blocks = ca.cs_blocks /\
    cd.cs_current_bb = ca.cs_current_bb /\
    cd.cs_current_insts = ca.cs_current_insts ++ emitted_insts ca cd /\
    ca.cs_next_var <= cd.cs_next_var /\
    ~not_fresh_at ca invvar /\ ~not_fresh_at ca validvar /\
    not_fresh_at cd invvar /\ not_fresh_at cd validvar /\
    invvar <> validvar /\
    (!z. not_fresh_at ca z ==> z <> invvar /\ z <> validvar)
Proof
  simp[emitHelperTheory.emit_op_def, emitHelperTheory.emit_inst_def,
    compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
    compileEnvTheory.comp_return_def, compileEnvTheory.fresh_var_def,
    compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def] >>
  strip_tac >> gvs[] >>
  simp[exprLoweringPropsTheory.emitted_insts_def,
    rich_listTheory.DROP_LENGTH_APPEND, compileEnvTheory.not_fresh_at_def]
QED

Theorem rest_word_loop_caller_prefix[local]:
  compile_array_membership_loop needle arr len stride off
    (compile_ptr_load ctor imm loc) is_in cs = (out,ct) /\
  fn_has_code cs ct fn ==>
  ?bb. lookup_block cs.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX cs.cs_current_insts bb.bb_instructions
Proof
  rewrite_tac[exprSimBopRestWordLayoutTheory.rest_word_loop_factor_eq] >> strip_tac >>
  drule exprSimBopRestWordLayoutTheory.rest_word_ptr_load_shape >> strip_tac >>
  drule exprSimBopRestWordLayoutTheory.rest_word_loop_prefix_shape >>
  drule exprSimBopRestWordLayoutTheory.rest_word_loop_suffix_shape >>
  rewrite_tac[exprSimBopRestWordLayoutTheory.rest_word_loop_prefix_shape_def,
    exprSimBopRestWordLayoutTheory.rest_word_loop_suffix_shape_def] >>
  rpt strip_tac >>
  gvs[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def,
    listTheory.LENGTH_APPEND, listTheory.APPEND_ASSOC,
    DISJ_IMP_THM, FORALL_AND_THM, arithmeticTheory.ADD1]
QED

Theorem rest_word_dynamic_code:
  compile_ptr_load ctor imm loc arr sm = (lenop,ch) /\
  emit_op GT [lenop; Lit (n2w cap)] ch = (invop,cg) /\
  emit_op ISZERO [invop] cg = (validop,cz) /\
  emit_inst ASSERT [validop] [] cz = ((),cs) /\
  compile_array_membership_loop needle arr lenop stride off
    (compile_ptr_load ctor imm loc) is_in cs = (out,ct) /\
  fn_has_code sm ct fn ==>
  fn_has_code sm ch fn /\ fn_has_code ch cs fn /\ fn_has_code cs ct fn
Proof
  strip_tac >>
  drule_all rest_word_capacity_check_shape >> strip_tac >>
  drule exprSimBopRestWordLayoutTheory.rest_word_ptr_load_shape >> strip_tac >>
  `fn_has_code cs ct fn` by
    fs[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def] >>
  drule_all rest_word_loop_caller_prefix >> strip_tac >>
  `isPREFIX ch.cs_current_insts bb.bb_instructions` by
    (irule rich_listTheory.IS_PREFIX_TRANS >>
     qexists `cs.cs_current_insts` >> simp[rich_listTheory.IS_PREFIX_APPEND]) >>
  `isPREFIX sm.cs_current_insts bb.bb_instructions` by
    (irule rich_listTheory.IS_PREFIX_TRANS >>
     qexists `ch.cs_current_insts` >> simp[rich_listTheory.IS_PREFIX_APPEND]) >>
  simp[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def] >>
  metis_tac[]
QED

Theorem rest_word_capacity_check_path:
  emit_op GT [lenop; Lit (n2w cap)] ch = (invop,cg) /\
  emit_op ISZERO [invop] cg = (validop,cz) /\
  emit_inst ASSERT [validop] [] cz = ((),cs) /\
  fn_has_code ch cs fn /\
  rest_word_search_rep ctx func cenv cx e es sa sm s0 es' tv vv
    needleop needle lenop len s /\
  eval_operand (vv_operand vv) s = SOME baseword /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  sm.cs_next_var <= ch.cs_next_var /\
  (!z. vv_operand vv = Var z ==> not_fresh_at sm z) /\
  (!z. needleop = Var z \/ vv_operand vv = Var z \/ lenop = Var z ==> not_fresh_at ch z) /\
  len <= cap /\ cap < dimword (:256) /\
  s.vs_current_bb = ch.cs_current_bb /\
  s.vs_inst_idx = LENGTH ch.cs_current_insts /\ ~s.vs_halted ==>
  ?t. gas_marked_path memory execctx fn s 0 (OK t) /\
    rest_word_search_rep ctx func cenv cx e es sa sm s0 es' tv vv
      needleop needle lenop len t /\
    eval_operand (vv_operand vv) t = SOME baseword /\
    t.vs_current_bb = cs.cs_current_bb /\
    t.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~t.vs_halted
Proof
  strip_tac >> drule_all rest_word_capacity_check_shape >> strip_tac >>
  `eval_operand lenop s = SOME (n2w len)` by fs[rest_word_search_rep_def] >>
  `run_inst_seq (emitted_insts ch cs) s =
    OK (update_var validvar 1w (update_var invvar 0w s))` by
    (asm_rewrite_tac[] >> irule rest_word_capacity_check_run >>
     conj_tac >- simp[] >> qexists `len` >> simp[]) >>
  `~not_fresh_at sm invvar /\ ~not_fresh_at sm validvar` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `needleop <> Var invvar /\ lenop <> Var invvar /\
   needleop <> Var validvar /\ lenop <> Var validvar` by metis_tac[] >>
  `rest_word_search_rep ctx func cenv cx e es sa sm s0 es' tv vv
    needleop needle lenop len (update_var invvar 0w s)` by
    (irule rest_word_search_rep_update >> simp[] >> metis_tac[]) >>
  `rest_word_search_rep ctx func cenv cx e es sa sm s0 es' tv vv
    needleop needle lenop len (update_var validvar 1w (update_var invvar 0w s))` by
    (irule rest_word_search_rep_update >> simp[] >> metis_tac[]) >>
  `eval_operand (vv_operand vv) (update_var validvar 1w (update_var invvar 0w s)) =
    SOME baseword` by
    (irule exprLoweringPropsTheory.eval_operand_update_other_local >>
     simp[] >> conj_tac >- metis_tac[] >>
     irule exprLoweringPropsTheory.eval_operand_update_other_local >> simp[] >> metis_tac[]) >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts ch cs) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fragExecTheory.fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
     simp[listTheory.DROP_APPEND]) >>
  `run_inst_seq_mem_ok (emitted_insts ch cs) s` by
    (asm_rewrite_tac[] >> irule rest_word_capacity_check_mem_ok) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> GAS) (emitted_insts ch cs)` by
    simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def] >>
  `gas_marked_path memory execctx fn s 0
    (OK ((update_var validvar 1w (update_var invvar 0w s)) with
      vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts ch cs)))` by
    (irule exprSimBopRestWordLoopPathTheory.rest_word_sequence_marked >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  qexists `(update_var validvar 1w (update_var invvar 0w s)) with
    vs_inst_idx := LENGTH cs.cs_current_insts` >>
  simp[rest_word_search_rep_control, venomStateTheory.update_var_def] >>
  qpat_x_assum `gas_marked_path _ _ _ _ _ _` mp_tac >>
  simp[venomStateTheory.update_var_def]
QED

Theorem rest_word_dynamic_tail:
  compile_var_array_membership cenv needleop vv (ArrayT ty (Dynamic cap)) is_in sm = (out,ct) /\
  fn_has_code sm ct fn /\
  vv_post ctx func cenv cx e es sa sm s0 es' tv vv s /\
  read_result cx tv es' = (INL (ArrayV av), es') /\
  loc = (case vv_location vv of SOME l => l | NONE => LocMemory) /\ loc <> LocCalldata /\
  expr_type e = ArrayT ty (Dynamic cap) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV et (Dynamic cap)) /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME et /\
  value_has_type (ArrayTV et (Dynamic cap)) (ArrayV av) /\ value_has_type et needle /\
  eval_operand needleop s = SOME (typed_val_to_w256 et needle) /\
  eval_operand (vv_operand vv) s = SOME baseword /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  (!z. needleop = Var z \/ vv_operand vv = Var z ==> not_fresh_at sm z) /\
  cap < dimword (:256) /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~s.vs_halted ==>
  ?t. gas_marked_path memory execctx fn s 0 (OK t) /\
      t.vs_current_bb = ct.cs_current_bb /\
      t.vs_inst_idx = LENGTH ct.cs_current_insts /\ ~t.vs_halted /\
      vv_post ctx func cenv cx e es sa sm s0 es' tv vv t /\
      eval_operand needleop t = SOME (typed_val_to_w256 et needle) /\
      eval_operand (vv_operand vv) t = SOME baseword /\
      eval_operand out t = SOME (bool_to_word
        (if is_in then evaluate_in_array (ArrayTV et (Dynamic cap)) needle av
         else ~evaluate_in_array (ArrayTV et (Dynamic cap)) needle av))
Proof
  strip_tac >>
  `vv_post ctx func cenv cx e es sa sm s0 es' (Value (ArrayV av)) vv s` by
    (irule exprSimUnwrapPropsTheory.vv_post_read_result >> qexists_tac `tv` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `elem_size_in_location cenv loc ty = word_scale loc` by metis_tac[rest_word_word_stride] >>
  qpat_x_assum `compile_var_array_membership _ _ _ _ _ _ = _` mp_tac >>
  simp[rest_word_dynamic_dispatch] >>
  qpat_assum `loc = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_x_assum `elem_size_in_location _ _ _ = _` (fn th => pure_rewrite_tac[th]) >>
  simp[compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> strip_tac >>
  drule rest_word_located_header_run >> simp[] >>
  disch_then drule_all >> strip_tac >>
  `sm.cs_next_var <= sm.cs_next_var` by simp[] >>
  `!z. vv_operand vv = Var z ==> not_fresh_at sm z` by metis_tac[] >>
  `!z. needleop = Var z ==> not_fresh_at sm z` by metis_tac[] >>
  `vv_post ctx func cenv cx e es sa sm s0 es' tv vv q /\
   eval_operand needleop q = SOME (typed_val_to_w256 et needle) /\
   eval_operand (vv_operand vv) q = SOME baseword` by
    (irule rest_word_capture_load_frame >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `word_scale loc` >>
  rename1 `compile_ptr_load _ _ loc _ sm = (lenop,ch)` >>
  rename1 `emit_op GT _ ch = (invop,cg)` >>
  rename1 `emit_op ISZERO _ cg = (validop,cz)` >>
  rename1 `emit_inst ASSERT _ _ cz = ((),cs)` >>
  drule_all rest_word_dynamic_code >> strip_tac >>
  `ci_mono sm ch` by
    (mp_tac (Q.SPECL [`cenv.ce_is_ctor`, `cenv.ce_imm_alloca`, `loc`,
       `vv_operand vv`, `sm`] exprLoweringPropsTheory.ci_mono_compile_ptr_load) >> simp[]) >>
  `sm.cs_next_var <= ch.cs_next_var` by fs[exprLoweringPropsTheory.ci_mono_def] >>
  `!z. needleop = Var z \/ vv_operand vv = Var z \/ lenop = Var z ==>
      not_fresh_at ch z` by
    (drule exprSafeOperandTheory.compile_ptr_load_safe_operand >>
     simp[exprSafeOperandTheory.safe_operand_def] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `gas_marked_path memory execctx fn s 0
     (OK (q with vs_inst_idx := LENGTH ch.cs_current_insts)) /\
   q.vs_current_bb = ch.cs_current_bb /\ ~q.vs_halted` by
    (drule rest_word_ptr_load_marked >>
     disch_then (qspecl_then [`q`, `s`, `memory`, `fn`, `execctx`] mp_tac) >> simp[]) >>
  `array_length (ArrayTV et (Dynamic cap)) av <= cap` by
    (Cases_on `av` >> gvs[vyperTypingTheory.value_has_type_def,
       vyperValueOperationTheory.array_length_def]) >>
  qabbrev_tac `p = q with vs_inst_idx := LENGTH ch.cs_current_insts` >>
  `rest_word_search_rep ctx func cenv cx e es sa sm s0 es' tv vv
    needleop (typed_val_to_w256 et needle) lenop
      (array_length (ArrayTV et (Dynamic cap)) av) p` by
    simp[Abbr `p`, rest_word_search_rep_control, rest_word_search_rep_def] >>
  `eval_operand (vv_operand vv) p = SOME baseword /\
   p.vs_current_bb = ch.cs_current_bb /\
   p.vs_inst_idx = LENGTH ch.cs_current_insts /\ ~p.vs_halted` by simp[Abbr `p`] >>
  drule_all rest_word_capacity_check_path >>
  disch_then (qspecl_then [`memory`, `execctx`] strip_assume_tac) >>
  `sm.cs_next_var <= cs.cs_next_var /\
   (!z. needleop = Var z \/ vv_operand vv = Var z \/ lenop = Var z ==>
      not_fresh_at cs z)` by
    (drule_all rest_word_capacity_check_shape >> strip_tac >>
     metis_tac[freshWritesTheory.not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS]) >>
  `array_length (ArrayTV et (Dynamic cap)) av < dimword (:256)` by decide_tac >>
  qpat_x_assum `rest_word_search_rep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t` mp_tac >>
  simp[rest_word_search_rep_def] >> strip_tac >>
  `loc = (case vv_location vv of SOME l => l | NONE => LocMemory)` by simp[Abbr `loc`] >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV et (Dynamic cap))` by simp[] >>
  drule_all (SRULE [] (Q.INST [`bd` |-> `Dynamic cap`,
    `len` |-> `array_length (ArrayTV et (Dynamic cap)) av`] rest_word_located_search)) >>
  disch_then (qspecl_then [`memory`, `execctx`] strip_assume_tac) >>
  qexists `t'` >> simp[] >>
  `gas_marked_path memory execctx fn s (0 + 0) (OK t)` by
    (irule fragGasModeTheory.gas_marked_path_then >> qexists `p` >> simp[]) >>
  pop_assum (assume_tac o SRULE []) >>
  `gas_marked_path memory execctx fn s (0 + 0) (OK t')` by
    (irule fragGasModeTheory.gas_marked_path_then >> qexists `t` >> simp[]) >>
  pop_assum mp_tac >> simp[]
QED
