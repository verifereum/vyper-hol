(* Header and located-array composition for nonliteral word membership. *)
Theory exprSimBopRestWordTail
Ancestors
  exprSimBopRestWordIterate exprSimBopRestWordProbe
  exprSimBopRestWordIndex exprSimBopRestWordStorageLoads

(* Located representations depend on the value read, not the syntax of the
   captured source result.  Normalize once before using value-load adapters. *)
Theorem rest_word_vv_post_value:
  vv_post ctx func cenv cx e es sa sm s0 es' tv vv s /\
  read_result cx tv es' = (INL v, es') ==>
  vv_post ctx func cenv cx e es sa sm s0 es' (Value v) vv s
Proof
  strip_tac >>
  `vv_holds cenv cx (expr_type e) tv vv es' s =
   vv_holds cenv cx (expr_type e) (Value v) vv es' s` by
    (Cases_on `vv` >> simp[loweringPostsTheory.vv_holds_def,
       vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
     Cases_on `p.ptr_location` >>
     simp[loweringPostsTheory.storage_holds_def,
       loweringPostsTheory.immutable_holds_def,
       vyperStateTheory.read_result_def, vyperStateTheory.return_def]) >>
  `vv_at cenv cx (expr_type e) sa sm es' tv vv s =
   vv_at cenv cx (expr_type e) sa sm es' (Value v) vv s` by
    (Cases_on `vv` >> simp[loweringPostsTheory.vv_at_def,
       vyperStateTheory.read_result_def, vyperStateTheory.return_def]) >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  asm_rewrite_tac[loweringPostsTheory.vv_post_def]
QED

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

Theorem rest_word_fixed_memory_tail:
  compile_var_array_membership cenv needleop vv (ArrayT ty (Fixed n)) is_in sm = (out,ct) /\
  fn_has_code sm ct fn /\
  vv_post ctx func cenv cx e es sa sm s0 es' (Value (ArrayV av)) vv s /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
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
      vv_post ctx func cenv cx e es sa sm s0 es' (Value (ArrayV av)) vv t /\
      eval_operand needleop t = SOME (typed_val_to_w256 et needle) /\
      eval_operand (vv_operand vv) t = SOME baseword /\
      eval_operand out t = SOME (bool_to_word
        (if is_in then evaluate_in_array (ArrayTV et (Fixed n)) needle av
         else ~evaluate_in_array (ArrayTV et (Fixed n)) needle av))
Proof
  strip_tac >>
  `array_length (ArrayTV et (Fixed n)) av = n` by
    metis_tac[exprSimBopRestWordLoadsTheory.rest_word_array_fixed_length] >>
  `elem_size_in_location cenv LocMemory ty = 32` by
    (Cases_on `ty` >>
     gvs[compileEnvTheory.is_word_type_def, compileEnvTheory.elem_size_in_location_def,
       compileEnvTheory.type_memory_bytes_def, compileEnvTheory.is_slot_addressed_def] >>
     Cases_on `b` >> gvs[compileEnvTheory.is_word_type_def,
       compileEnvTheory.type_memory_bytes_def] >>
     Cases_on `b'` >> gvs[compileEnvTheory.is_word_type_def,
       compileEnvTheory.type_memory_bytes_def]) >>
  `compile_array_membership_loop needleop (vv_operand vv) (Lit (n2w n)) 32 0
    (context$compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory) is_in sm = (out,ct)` by
    (qpat_x_assum `compile_var_array_membership _ _ _ _ _ _ = _` mp_tac >>
     simp[rest_word_fixed_dispatch] >>
     Cases_on `vv_location vv` >> gvs[]) >>
  qabbrev_tac `elem = \i. typed_val_to_w256 et
    (THE (array_index (ArrayTV et (Fixed n)) av (&i)))` >>
  `!i. i < n ==> array_index (ArrayTV et (Fixed n)) av (&i) =
      SOME (THE (array_index (ArrayTV et (Fixed n)) av (&i)))` by
    (rpt strip_tac >>
     `valid_index (ArrayTV et (Fixed n)) av (&i)` by
       simp[vyperArrayTheory.valid_index_def] >>
     drule vyperArrayTheory.array_index_valid >>
     Cases_on `array_index (ArrayTV et (Fixed n)) av (&i)` >> simp[]) >>
  `evaluate_in_array (ArrayTV et (Fixed n)) needle av <=>
    ?i. i < n /\ elem i = typed_val_to_w256 et needle` by
    (drule_all rest_word_array_word_membership >>
     simp[Abbr `elem`] >> metis_tac[optionTheory.THE_DEF]) >>
  `!h cl cm v i p.
    rest_word_loop_prefix needleop (vv_operand vv) (Lit (n2w n)) 32 0 sm = (h,cl) /\
    context$compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory h.rw_addr cl = (v,cm) /\
    i < n /\
    rest_word_search_rep ctx func cenv cx e es sa sm s0 es' (Value (ArrayV av)) vv
      needleop (typed_val_to_w256 et needle) (Lit (n2w n)) n p /\
    eval_operand (vv_operand vv) p = SOME baseword /\
    eval_operand h.rw_addr p = SOME (baseword + n2w (0 + i * 32)) ==>
    ?q. run_inst_seq (emitted_insts cl cm) p = OK q /\
        eval_operand v q = SOME (elem i) /\
        (memory ==> run_inst_seq_mem_ok (emitted_insts cl cm) p)` by
    (rpt gen_tac >> simp[rest_word_search_rep_def] >> strip_tac >>
     `evaluate_type (get_tenv cx) (ArrayT ty (Fixed n)) =
        SOME (ArrayTV et (Fixed n))` by metis_tac[] >>
     drule rest_word_memory_element_run >>
     simp[Abbr `elem`] >>
     disch_then assume_tac >> metis_tac[]) >>
  `rest_word_search_rep ctx func cenv cx e es sa sm s0 es' (Value (ArrayV av)) vv
      needleop (typed_val_to_w256 et needle) (Lit (n2w n)) n s` by
    simp[rest_word_search_rep_def, venomStateTheory.eval_operand_def] >>
  `!z. vv_operand vv = Var z ==> not_fresh_at sm z` by metis_tac[] >>
  `!z. needleop = Var z \/ vv_operand vv = Var z \/ Lit (n2w n) = Var z ==>
       not_fresh_at sm z` by (simp[] >> metis_tac[]) >>
  `sm.cs_next_var <= sm.cs_next_var` by simp[] >>
  `LocMemory <> LocCalldata` by simp[] >>
  drule_all rest_word_compiled_search >>
  simp[rest_word_search_rep_def] >> metis_tac[]
QED
