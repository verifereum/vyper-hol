(* Location adapters for the nonliteral membership loop. *)
Theory exprSimBopRestWordLoads
Ancestors
  exprSimBopRestWordLoadPath exprSimBopRestWordIndex exprSimAggregateEncoding valueEncodingProps vyperTyping
  compileEnv loweringStateRelDefs loweringPosts exprSimUnwrap exprLoweringProps venomMemDefs
  valueEncodingProofs valueEncoding valueEncodingDefs vyperValueOperation vyperValue list alist

Theorem rest_word_array_memory_index:
  value_has_type (ArrayTV et bd) (ArrayV av) /\
  val_in_memory (ArrayTV et bd) (ArrayV av) off mem /\
  array_index (ArrayTV et bd) av (&i) = SOME v ==>
  val_in_memory et v
    (off + (case bd of Fixed _ => 0 | Dynamic _ => 32) +
     i * type_memory_size et) mem
Proof
  Cases_on `bd` >> Cases_on `av` >>
  simp[value_has_type_def, val_in_memory_sarray, val_in_memory_dynarray,
       array_index_def, oEL_THM] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
  >- (drule_all kvs_in_memory_lookup >> simp[]) >>
  drule_all elems_in_memory_EL >> simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Theorem rest_word_memory_word:
  is_word_type ty /\ evaluate_type tenv ty = SOME tv /\
  value_has_type tv v /\ val_in_memory tv v off mem ==>
  mem_word_at off mem = typed_val_to_w256 tv v
Proof
  strip_tac >> Cases_on `ty` >>
  gvs[is_word_type_def, evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >>
  gvs[value_has_type_def, val_in_memory_def, typed_val_to_w256_def,
      val_to_w256_def]
QED

Theorem rest_word_array_memory_load:
  is_word_type ty /\ evaluate_type tenv ty = SOME et /\
  value_has_type (ArrayTV et bd) (ArrayV av) /\
  val_in_memory (ArrayTV et bd) (ArrayV av) off mem /\
  array_index (ArrayTV et bd) av (&i) = SOME v ==>
  mem_word_at (off + (case bd of Fixed _ => 0 | Dynamic _ => 32) +
               i * type_memory_size et) mem = typed_val_to_w256 et v
Proof
  strip_tac >> irule rest_word_memory_word >>
  `well_formed_type_value et` by metis_tac[evaluate_type_well_formed] >>
  `value_has_type et v` by
    (irule vyperAssignPreservesTypeTheory.array_index_has_type >> metis_tac[]) >>
  `val_in_memory et v
     (off + (case bd of Fixed _ => 0 | Dynamic _ => 32) +
      i * type_memory_size et) mem` by
    (irule rest_word_array_memory_index >> metis_tac[]) >>
  metis_tac[]
QED

Theorem rest_word_array_element_extent:
  value_has_type (ArrayTV et bd) (ArrayV av) /\
  type_memory_size et = 32 /\ i < array_length (ArrayTV et bd) av ==>
  (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32 + 32 <=
  type_memory_size (ArrayTV et bd)
Proof
  Cases_on `bd` >> Cases_on `av` >>
  simp[value_has_type_def, array_length_def, type_memory_size_def] >>
  decide_tac
QED

Theorem rest_word_vv_memory_bound:
  vv_post ctx func cenv cx e es sa sb s0 es' (Value (ArrayV av)) vv s /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
  post_value_type cenv e = ArrayT et bd /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME tv /\
  eval_operand (vv_operand vv) s = SOME w ==>
  w2n w + type_memory_size tv < dimword (:256) /\
  (0 < type_memory_size tv ==>
   w2n w + type_memory_size tv <= s.vs_alloca_next)
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es' s` by fs[vv_post_def] >>
  `s.vs_alloca_next < dimword (:256)` by
    (fs[stmt_state_rel_def, alloca_room_def] >> decide_tac) >>
  `alloca_next_valid s` by fs[stmt_state_rel_def, alloca_inv_def] >>
  `local_ptrs_rel func cenv es'.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_post_def] >> strip_tac >>
  qpat_x_assum `vv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  Cases_on `vv` >>
  gvs[contextTheory.vv_location_def, contextTheory.vv_operand_def,
      vv_at_def, expr_val_at_def, is_word_type_def,
      val_footprint_def, vyperStateTheory.read_result_def,
      vyperStateTheory.return_def] >>
  strip_tac >>
  gvs[alloca_next_valid_def, local_region_def, local_ptrs_rel_def]
  >>~- ([`sa.cs_next_id <= aid`],
        qpat_x_assum `!aid base sz. _` drule >> decide_tac)
  >>~- ([`local_val_at cenv cx n k tv (ArrayV av)`],
        qpat_x_assum `!name entry p sz. _` drule >>
        disch_then drule >> strip_tac >> gvs[] >> decide_tac) >>
  simp[wordsTheory.w2n_lt]
QED

Theorem rest_word_array_sub_layout:
  value_has_type (ArrayTV et bd) (ArrayV av) /\
  type_memory_size et = 32 /\ i < array_length (ArrayTV et bd) av /\
  array_index (ArrayTV et bd) av (&i) = SOME v ==>
  sub_layout (ArrayTV et bd) (ArrayV av)
    ((case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32) et v
Proof
  strip_tac >> simp[sub_layout_def] >> conj_tac
  >- (drule_all rest_word_array_element_extent >> simp[]) >>
  rpt strip_tac >> drule_all rest_word_array_memory_index >>
  simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  simp[]
QED

Theorem rest_word_sub_layout_trans:
  sub_layout tv1 v1 k1 tv2 v2 /\ sub_layout tv2 v2 k2 tv3 v3 ==>
  sub_layout tv1 v1 (k1 + k2) tv3 v3
Proof
  simp[sub_layout_def] >> strip_tac >>
  rpt strip_tac >>
  first_x_assum drule >> strip_tac >> first_x_assum drule >>
  simp_tac bool_ss [arithmeticTheory.ADD_ASSOC]
QED

(* Transport both immutable representation alternatives through an array index. *)
Theorem rest_word_array_immutable_index:
  immutable_holds cenv cx (ArrayT ty bd) (Value (ArrayV av)) w es s /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME et /\
  value_has_type (ArrayTV et bd) (ArrayV av) /\
  i < array_length (ArrayTV et bd) av /\
  array_index (ArrayTV et bd) av (&i) = SOME v ==>
  immutable_holds cenv cx ty (Value v)
    (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32)) es s
Proof
  strip_tac >>
  `evaluate_type (get_tenv cx) (ArrayT ty bd) = SOME (ArrayTV et bd)` by
    (fs[immutable_holds_def, evaluate_type_def, AllCaseEqs()]) >>
  irule exprSimPropsTheory.immutable_holds_sub >>
  `type_memory_size et = 32` by metis_tac[exprSimPropsTheory.word_tv_memory_size] >>
  `well_formed_type_value et` by metis_tac[evaluate_type_well_formed] >>
  `value_has_type et v` by
    (irule vyperAssignPreservesTypeTheory.array_index_has_type >> metis_tac[]) >>
  `sub_layout (ArrayTV et bd) (ArrayV av)
     ((case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32) et v` by
    (irule rest_word_array_sub_layout >> simp[]) >>
  qexistsl [`et`, `v`, `ArrayTV et bd`, `ArrayV av`, `ArrayT ty bd`,
            `Value (ArrayV av)`] >>
  simp[vyperStateTheory.read_result_def, vyperStateTheory.return_def]
QED

Theorem rest_word_vv_memory_rep:
  vv_holds cenv cx (ArrayT ty bd) (Value (ArrayV av)) vv es s /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
  evaluate_type (get_tenv cx) (ArrayT ty bd) = SOME (ArrayTV et bd) /\
  eval_operand (vv_operand vv) s = SOME w ==>
  val_in_memory (ArrayTV et bd) (ArrayV av) (w2n w) s.vs_memory
Proof
  Cases_on `vv` >>
  simp[vv_holds_def, contextTheory.vv_location_def, contextTheory.vv_operand_def, expr_val_rel_def,
       is_word_type_def, vyperStateTheory.read_result_def,
       vyperStateTheory.return_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem rest_word_vv_memory_index:
  vv_holds cenv cx (ArrayT ty bd) (Value (ArrayV av)) vv es s /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
  evaluate_type (get_tenv cx) (ArrayT ty bd) = SOME (ArrayTV et bd) /\
  eval_operand (vv_operand vv) s = SOME w /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME et /\
  value_has_type (ArrayTV et bd) (ArrayV av) /\
  array_index (ArrayTV et bd) av (&i) = SOME v ==>
  mem_word_at (w2n w + (case bd of Fixed _ => 0 | Dynamic _ => 32) +
               i * 32) s.vs_memory = typed_val_to_w256 et v
Proof
  strip_tac >>
  `type_memory_size et = 32` by metis_tac[exprSimPropsTheory.word_tv_memory_size] >>
  `val_in_memory (ArrayTV et bd) (ArrayV av) (w2n w) s.vs_memory` by
    metis_tac[rest_word_vv_memory_rep] >>
  drule_all rest_word_array_memory_load >> simp[]
QED

(* A read-only loop load is a zero-count path; its state change is explicit. *)
Theorem rest_word_memory_load_path:
  context$compile_ptr_load ctor imm LocMemory addr sa = (op, sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand addr s = SOME a /\
  mem_word_at (w2n a) s.vs_memory = value ==>
  gas_path ctx func s 0
    (OK ((update_var (STRING #"%" (toString sa.cs_next_var)) value s)
      with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  pure_rewrite_tac[contextTheory.compile_ptr_load_def] >> strip_tac >>
  irule emitHelperPropsTheory.emit_op_zero_path >>
  simp[] >>
  qexistsl [`[addr]`, `op`, `MLOAD`, `sb`] >>
  simp[venomInstTheory.is_terminator_def] >>
  gen_tac >> drule emitHelperPropsTheory.step_MLOAD >>
  simp[GSYM mem_word_at_eq_mload]
QED

Theorem rest_word_array_immutable_load:
  stmt_state_rel ctx func cenv cx es s /\
  immutable_holds cenv cx (ArrayT ty bd) (Value (ArrayV av)) w es s /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME et /\
  value_has_type (ArrayTV et bd) (ArrayV av) /\
  i < array_length (ArrayTV et bd) av /\
  array_index (ArrayTV et bd) av (&i) = SOME v ==>
  (if cenv.ce_is_ctor then
     mload (w2n (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32))) s
   else word_of_bytes T (0w:bytes32)
     (TAKE 32 (DROP (w2n (w + n2w
       ((case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32)))
       s.vs_data_section ++ REPLICATE 32 0w))) = typed_val_to_w256 et v
Proof
  strip_tac >> drule_all rest_word_array_immutable_index >> strip_tac >>
  Cases_on `cenv.ce_is_ctor`
  >- (drule_all immutable_holds_iload >> simp[]) >>
  drule_all immutable_holds_dload >> simp[]
QED

Theorem rest_word_vv_memory_offset:
  vv_post ctx func cenv cx e es sa sb s0 es' (Value (ArrayV av)) vv s /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
  post_value_type cenv e = ArrayT ty bd /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME (ArrayTV et bd) /\
  eval_operand (vv_operand vv) s = SOME w /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME et /\
  value_has_type (ArrayTV et bd) (ArrayV av) /\
  i < array_length (ArrayTV et bd) av ==>
  w2n (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32)) =
  w2n w + (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32
Proof
  strip_tac >>
  `type_memory_size et = 32` by metis_tac[exprSimPropsTheory.word_tv_memory_size] >>
  `w2n w + type_memory_size (ArrayTV et bd) < dimword (:256)` by
    metis_tac[rest_word_vv_memory_bound] >>
  drule_all rest_word_array_element_extent >> strip_tac >>
  simp_tac bool_ss [GSYM arithmeticTheory.ADD_ASSOC] >>
  irule exprSimPropsTheory.buffer_offset_no_wrap >>
  qexists_tac `type_memory_size (ArrayTV et bd)` >> simp[]
QED

Theorem rest_word_array_memory_load_path:
  is_word_type ty /\ evaluate_type tenv ty = SOME et /\
  value_has_type (ArrayTV et bd) (ArrayV av) /\
  val_in_memory (ArrayTV et bd) (ArrayV av) (w2n w) s.vs_memory /\
  array_index (ArrayTV et bd) av (&i) = SOME v /\
  w2n (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32)) =
    w2n w + (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32 /\
  context$compile_ptr_load ctor imm LocMemory addr sa = (op,sb) /\
  eval_operand addr s = SOME
    (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32)) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_path ctx func s 0 (OK u) /\
      eval_operand op u = SOME (typed_val_to_w256 et v) /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      u = s with <|vs_vars := u.vs_vars;
                   vs_inst_idx := LENGTH sb.cs_current_insts|> /\
      (!x. (!inst. MEM inst (emitted_insts sa sb) ==> ~MEM x inst.inst_outputs) ==>
           FLOOKUP u.vs_vars x = FLOOKUP s.vs_vars x)
Proof
  strip_tac >>
  `type_memory_size et = 32` by metis_tac[exprSimPropsTheory.word_tv_memory_size] >>
  drule_all rest_word_array_memory_load >> simp[] >> strip_tac >>
  `?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
       eval_operand op t = SOME (typed_val_to_w256 et v)` by
    (drule (Q.INST [`b` |-> `0w`] rest_word_ptr_load_run) >> simp[] >>
     disch_then (qspecl_then [`s`,
       `w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32)`] mp_tac) >>
     simp[GSYM mem_word_at_eq_mload]) >>
  drule rest_word_ptr_load_path >> simp[] >>
  disch_then drule_all >> simp[]
QED

Theorem rest_word_array_immutable_load_path:
  stmt_state_rel ctx func cenv cx es s /\
  immutable_holds cenv cx (ArrayT ty bd) (Value (ArrayV av)) w es s /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME et /\
  value_has_type (ArrayTV et bd) (ArrayV av) /\
  i < array_length (ArrayTV et bd) av /\
  array_index (ArrayTV et bd) av (&i) = SOME v /\
  context$compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocCode addr sa = (op,sb) /\
  eval_operand addr s = SOME
    (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32)) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_path ctx func s 0 (OK u) /\
      eval_operand op u = SOME (typed_val_to_w256 et v) /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      u = s with <|vs_vars := u.vs_vars;
                   vs_inst_idx := LENGTH sb.cs_current_insts|> /\
      (!x. (!inst. MEM inst (emitted_insts sa sb) ==> ~MEM x inst.inst_outputs) ==>
           FLOOKUP u.vs_vars x = FLOOKUP s.vs_vars x)
Proof
  strip_tac >> drule_all rest_word_array_immutable_load >> strip_tac >>
  `(cenv.ce_is_ctor /\ cenv.ce_imm_alloca <> NONE ==>
    eval_operand (THE cenv.ce_imm_alloca) s = SOME 0w)` by
    (fs[stmt_state_rel_def, immutable_base_zero_def] >>
     Cases_on `cenv.ce_imm_alloca` >> gvs[]) >>
  `?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
       eval_operand op t = SOME (typed_val_to_w256 et v)` by
    (drule (Q.INST [`b` |-> `0w`] rest_word_ptr_load_run) >> simp[] >>
     disch_then (qspecl_then [`s`,
       `w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32)`] mp_tac) >>
     Cases_on `cenv.ce_is_ctor` >> Cases_on `cenv.ce_imm_alloca` >>
     gvs[wordsTheory.WORD_ADD_0]) >>
  drule rest_word_ptr_load_path >> simp[] >>
  disch_then drule_all >> simp[]
QED

Theorem rest_word_array_memory_header:
  value_has_type (ArrayTV et (Dynamic cap)) (ArrayV av) /\
  val_in_memory (ArrayTV et (Dynamic cap)) (ArrayV av) off mem ==>
  mem_word_at off mem = n2w (array_length (ArrayTV et (Dynamic cap)) av) /\
  array_length (ArrayTV et (Dynamic cap)) av <= cap
Proof
  Cases_on `av` >>
  simp[value_has_type_def, val_in_memory_dynarray, array_length_def]
QED

Theorem rest_word_array_fixed_length:
  value_has_type (ArrayTV et (Fixed cap)) (ArrayV av) ==>
  array_length (ArrayTV et (Fixed cap)) av = cap
Proof
  Cases_on `av` >> simp[value_has_type_def, array_length_def]
QED


Theorem rest_word_array_immutable_header:
  stmt_state_rel ctx func cenv cx es s /\
  immutable_holds cenv cx (ArrayT ty (Dynamic cap)) (Value (ArrayV av)) w es s /\
  evaluate_type (get_tenv cx) ty = SOME et /\
  value_has_type (ArrayTV et (Dynamic cap)) (ArrayV av) ==>
  (if cenv.ce_is_ctor then mload (w2n w) s
   else word_of_bytes T (0w:bytes32)
     (TAKE 32 (DROP (w2n w) s.vs_data_section ++ REPLICATE 32 0w))) =
  n2w (array_length (ArrayTV et (Dynamic cap)) av)
Proof
  strip_tac >>
  `evaluate_type (get_tenv cx) (ArrayT ty (Dynamic cap)) =
   SOME (ArrayTV et (Dynamic cap))` by
    fs[immutable_holds_def, evaluate_type_def, AllCaseEqs()] >>
  Cases_on `cenv.ce_is_ctor` >> simp[]
  >- (drule_all exprSimCopyTheory.immutable_holds_memory >> strip_tac >>
      drule_all rest_word_array_memory_header >> simp[mem_word_at_eq_mload]) >>
  drule_all exprSimCopyTheory.immutable_holds_data >> strip_tac >>
  gvs[vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  drule_all rest_word_array_memory_header >>
  simp[mem_word_at_def, mem_bytes_at_def]
QED

Theorem rest_word_array_memory_header_path:
  value_has_type (ArrayTV et (Dynamic cap)) (ArrayV av) /\
  val_in_memory (ArrayTV et (Dynamic cap)) (ArrayV av) (w2n w) s.vs_memory /\
  context$compile_ptr_load ctor imm LocMemory addr sa = (op,sb) /\
  eval_operand addr s = SOME w /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_path ctx func s 0 (OK u) /\
      eval_operand op u = SOME (n2w (array_length (ArrayTV et (Dynamic cap)) av)) /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      u = s with <|vs_vars := u.vs_vars;
                   vs_inst_idx := LENGTH sb.cs_current_insts|> /\
      (!x. (!inst. MEM inst (emitted_insts sa sb) ==> ~MEM x inst.inst_outputs) ==>
           FLOOKUP u.vs_vars x = FLOOKUP s.vs_vars x)
Proof
  strip_tac >> drule_all rest_word_array_memory_header >> strip_tac >>
  `?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
       eval_operand op t = SOME (n2w (array_length (ArrayTV et (Dynamic cap)) av))` by
    (drule (Q.INST [`b` |-> `0w`] rest_word_ptr_load_run) >> simp[] >>
     disch_then (qspecl_then [`s`, `w`] mp_tac) >>
     simp[GSYM mem_word_at_eq_mload]) >>
  drule rest_word_ptr_load_path >> simp[] >>
  disch_then drule_all >> simp[]
QED

Theorem rest_word_array_immutable_header_path:
  stmt_state_rel ctx func cenv cx es s /\
  immutable_holds cenv cx (ArrayT ty (Dynamic cap)) (Value (ArrayV av)) w es s /\
  evaluate_type (get_tenv cx) ty = SOME et /\
  value_has_type (ArrayTV et (Dynamic cap)) (ArrayV av) /\
  context$compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocCode addr sa = (op,sb) /\
  eval_operand addr s = SOME w /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_path ctx func s 0 (OK u) /\
      eval_operand op u = SOME (n2w (array_length (ArrayTV et (Dynamic cap)) av)) /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      u = s with <|vs_vars := u.vs_vars;
                   vs_inst_idx := LENGTH sb.cs_current_insts|> /\
      (!x. (!inst. MEM inst (emitted_insts sa sb) ==> ~MEM x inst.inst_outputs) ==>
           FLOOKUP u.vs_vars x = FLOOKUP s.vs_vars x)
Proof
  strip_tac >> drule_all rest_word_array_immutable_header >> strip_tac >>
  `(cenv.ce_is_ctor /\ cenv.ce_imm_alloca <> NONE ==>
    eval_operand (THE cenv.ce_imm_alloca) s = SOME 0w)` by
    (fs[stmt_state_rel_def, immutable_base_zero_def] >>
     Cases_on `cenv.ce_imm_alloca` >> gvs[]) >>
  `?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
       eval_operand op t = SOME (n2w (array_length (ArrayTV et (Dynamic cap)) av))` by
    (drule (Q.INST [`b` |-> `0w`] rest_word_ptr_load_run) >> simp[] >>
     disch_then (qspecl_then [`s`, `w`] mp_tac) >>
     Cases_on `cenv.ce_is_ctor` >> Cases_on `cenv.ce_imm_alloca` >>
     gvs[wordsTheory.WORD_ADD_0]) >>
  drule rest_word_ptr_load_path >> simp[] >>
  disch_then drule_all >> simp[]
QED
