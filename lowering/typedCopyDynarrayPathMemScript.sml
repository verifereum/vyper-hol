(* Checked dynamic-array header and data execution. *)
Theory typedCopyDynarrayPathMem
Ancestors
  typedCopyArrayPathMem placeMemoryDynarrayForward placeMemoryTypedBase
  bodyDeclMemoryCounted instMemFrontier fragExecMem fragGasPathMem
  fragGasMode placeMemoryCopyEffect placeMemoryArrayForward placeMemoryCodeLayout
  placeMemoryArrayControl typedCopyControlPathMem placeMemoryChildForward
  placeMemoryCopyFrames exprSimAggregateEncoding
  context compileEnv emitHelper emitHelperProps exprLoweringProps
  venomState venomInst venomExecSemantics venomExecProofs immutableMemoryFrame
  valueEncoding valueEncodingProps ASCIInumbers list rich_list arithmetic finite_map

Theorem typed_memory_dynarray_setup_mem_ok[local]:
  (do length <- emit_op MLOAD [src];
      too_long <- emit_op GT [length; Lit (n2w cap)];
      ok <- emit_op ISZERO [too_long];
      emit_void ASSERT [ok];
      emit_void MSTORE [dst; length];
      src_data <- emit_op ADD [src; Lit 32w];
      dst_data <- emit_op ADD [dst; Lit 32w];
      return (length,src_data,dst_data)
   od) sa = ((length,src_data,dst_data),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  w2n sw + 32 <= s.vs_alloca_next /\ w2n dw + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >>
  `!k w t. sa.cs_next_var <= k ==>
     eval_operand src (update_var (STRING #"%" (toString k)) w t) = eval_operand src t /\
     eval_operand dst (update_var (STRING #"%" (toString k)) w t) = eval_operand dst t` by
    (rpt strip_tac >> irule typed_memory_fresh_operand >> qexists_tac `sa` >> simp[]) >>
  qpat_x_assum `_ sa = ((_,_,_),sb)` mp_tac >>
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       fresh_var_def, fresh_id_def, emit_def, comp_return_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_APPEND] >>
  simp[run_inst_seq_mem_ok_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_read1_def, exec_pure1_def, exec_pure2_def, exec_write2_def,
       eval_operand_def, lookup_var_update_var, toString_inj,
       below_frontier_MLOAD, below_frontier_MSTORE] >>
  simp[below_frontier_no_ranges] >>
  Cases_on `w2n (mload (w2n sw) s) > cap MOD dimword (:256)` >> simp[] >>
  simp[lookup_var_update_var, toString_inj, update_var_def] >>
  rpt CASE_TAC >> simp[]
QED

Theorem typed_memory_dynarray_setup_forward_mem:
  (do length <- emit_op MLOAD [src];
      too_long <- emit_op GT [length; Lit (n2w cap)];
      ok <- emit_op ISZERO [too_long];
      emit_void ASSERT [ok];
      emit_void MSTORE [dst; length];
      src_data <- emit_op ADD [src; Lit 32w];
      dst_data <- emit_op ADD [dst; Lit 32w];
      return (length,src_data,dst_data)
   od) sa = ((length,src_data,dst_data),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  mload (w2n sw) s = n2w n /\ n <= cap /\ cap < dimword (:256) /\
  w2n sw + 32 <= s.vs_alloca_next /\ w2n dw + 32 <= s.vs_alloca_next /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      eval_operand length t = SOME (n2w n) /\
      eval_operand src_data t = SOME (sw + 32w) /\
      eval_operand dst_data t = SOME (dw + 32w) /\
      t.vs_memory = (mstore (w2n dw) (n2w n) s).vs_memory /\
      mem_word_at (w2n dw) t.vs_memory = n2w n /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + 32 <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all typed_memory_dynarray_setup_sequence >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by gvs[same_blocks_def] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (qpat_assum `_ sa = ((_,_,_),sb)`
       (mp_then Any irule typed_memory_dynarray_setup_mem_ok) >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `gas_path_mem ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule (cj 1 body_decl_cursor_path) >> simp[] >>
     qexists_tac `sa` >> gvs[EVERY_MEM]) >>
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `(_ with <|vs_vars := _; vs_memory := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[eval_operand_def, lookup_var_def, mstore_mem_word_at_same] >>
  rpt conj_tac
  >- (qpat_x_assum `(_ with <|vs_vars := _; vs_memory := _|>) = s` mp_tac >>
      simp[venom_state_component_equality])
  >- metis_tac[lookup_var_def]
  >- metis_tac[mstore_mem_bytes_at_disjoint]
  >> simp[immutable_mstore_capacity, arithmeticTheory.MAX_DEF]
QED

Theorem typed_memory_dynarray_data_mem_ok[local]:
  (do data_sz <- emit_op MUL [length; Lit (n2w stride)];
      compile_copy_memory_dynamic dst src data_sz
   od) sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  eval_operand length s = SOME (n2w n) /\ n * stride < dimword (:256) /\
  w2n sw + n * stride <= s.vs_alloca_next /\
  w2n dw + n * stride <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >>
  `!w t. eval_operand src (update_var (STRING #"%" (toString sa.cs_next_var)) w t) = eval_operand src t /\
         eval_operand dst (update_var (STRING #"%" (toString sa.cs_next_var)) w t) = eval_operand dst t` by
    (rpt strip_tac >> irule typed_memory_fresh_operand >> qexists_tac `sa` >> simp[]) >>
  qpat_x_assum `_ sa = ((),sb)` mp_tac >>
  simp[compile_copy_memory_dynamic_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def,
       emit_def, comp_return_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, DROP_APPEND1, run_inst_seq_mem_ok_def,
       step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       wordsTheory.word_mul_n2w, eval_operand_def, lookup_var_update_var,
       below_frontier_MCOPY, below_frontier_no_ranges,
       wordsTheory.w2n_n2w, LESS_MOD] >>
  pure_once_rewrite_tac[GSYM mk_inst_def] >>
  simp[below_frontier_MCOPY, eval_operand_def, lookup_var_update_var,
       wordsTheory.w2n_n2w, LESS_MOD, update_var_def]
QED

Theorem typed_memory_dynarray_data_forward_mem:
  (do data_sz <- emit_op MUL [length; Lit (n2w stride)];
      compile_copy_memory_dynamic dst src data_sz
   od) sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  eval_operand length s = SOME (n2w n) /\ n * stride < dimword (:256) /\
  w2n sw + n * stride <= s.vs_alloca_next /\
  w2n dw + n * stride <= s.vs_alloca_next /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      mem_bytes_at (w2n dw) (n * stride) t.vs_memory =
        mem_bytes_at (w2n sw) (n * stride) s.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + n * stride <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all typed_memory_dynarray_data_sequence >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by gvs[same_blocks_def] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (drule_all typed_memory_dynarray_data_mem_ok >> simp[]) >>
  `gas_path_mem ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule (cj 1 body_decl_cursor_path) >> simp[] >>
     qexists_tac `sa` >> gvs[EVERY_MEM]) >>
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `(_ with <|vs_vars := _; vs_memory := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[lookup_var_def, mcopy_mem_bytes_at_same] >> rpt conj_tac
  >- (qpat_x_assum `(_ with <|vs_vars := _; vs_memory := _|>) = s` mp_tac >>
      simp[venom_state_component_equality])
  >- metis_tac[lookup_var_def]
  >- (rpt strip_tac >> irule mcopy_mem_bytes_at_disjoint >> decide_tac) >>
  simp[placeMemoryTypedPrimitiveTheory.mcopy_memory_length]
QED

Theorem typed_memory_dynarray_fast_bytes_forward_mem:
  compile_copy_dynarray_typed cenv dst et cap src et sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  mload (w2n sw) s = n2w n /\ n <= cap /\ cap < dimword (:256) /\
  n * type_memory_bytes cenv et < dimword (:256) /\
  w2n sw + 32 < dimword (:256) /\ w2n dw + 32 < dimword (:256) /\
  w2n sw + 32 + n * type_memory_bytes cenv et <= s.vs_alloca_next /\
  w2n dw + 32 + n * type_memory_bytes cenv et <= s.vs_alloca_next /\
  (w2n sw + 32 + n * type_memory_bytes cenv et <= w2n dw \/
   w2n dw + 32 <= w2n sw) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      mem_word_at (w2n dw) t.vs_memory = n2w n /\
      mem_bytes_at (w2n dw + 32) (n * type_memory_bytes cenv et) t.vs_memory =
        mem_bytes_at (w2n sw + 32) (n * type_memory_bytes cenv et) s.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/
               w2n dw + 32 + n * type_memory_bytes cenv et <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule typed_memory_dynarray_fast_split >> strip_tac >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (gvs[fragExecTheory.fn_has_code_def, same_blocks_def, fragExecTheory.emitted_blocks_def] >>
     metis_tac[IS_PREFIX_TRANS]) >>
  `w2n sw + 32 <= s.vs_alloca_next /\ w2n dw + 32 <= s.vs_alloca_next` by decide_tac >>
  drule_all typed_memory_dynarray_setup_forward_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_path_mem ctx func s 0 (OK mid)` >>
  `w2n (sw + 32w) = w2n sw + 32 /\ w2n (dw + 32w) = w2n dw + 32` by
    simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w, LESS_MOD] >>
  `mid.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `(mid with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `w2n (sw + 32w) + n * type_memory_bytes cenv et <= mid.vs_alloca_next /\
   w2n (dw + 32w) + n * type_memory_bytes cenv et <= mid.vs_alloca_next` by simp[] >>
  drule_all typed_memory_dynarray_data_forward_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_path_mem ctx func mid 0 (OK t)` >>
  qexists_tac `t` >> simp[] >>
  conj_tac >- metis_tac[gas_path_mem_then, ADD_CLAUSES] >>
  conj_tac
  >- (`mem_bytes_at (w2n dw) 32 t.vs_memory =
         mem_bytes_at (w2n dw) 32 mid.vs_memory` by
        (first_assum irule >> simp[]) >>
      gvs[mem_word_at_def, mem_bytes_at_def]) >>
  conj_tac
  >- (`mem_bytes_at (w2n sw + 32) (n * type_memory_bytes cenv et) mid.vs_memory =
         mem_bytes_at (w2n sw + 32) (n * type_memory_bytes cenv et) s.vs_memory` by
        (first_assum irule >> simp[] >> decide_tac) >> gvs[]) >>
  conj_tac
  >- (qpat_x_assum `_ = mid` mp_tac >> qpat_x_assum `_ = s` mp_tac >>
      simp[venom_state_component_equality] >> metis_tac[]) >>
  rpt strip_tac >>
  `mem_bytes_at a len t.vs_memory = mem_bytes_at a len mid.vs_memory` by
    (first_assum irule >> simp[] >> decide_tac) >>
  `mem_bytes_at a len mid.vs_memory = mem_bytes_at a len s.vs_memory` by
    (first_assum irule >> simp[] >> decide_tac) >> simp[]
QED

Theorem typed_memory_dynarray_fast_forward_mem:
  compile_copy_dynarray_typed cenv dst et cap src et sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  value_has_type (ArrayTV tv (Dynamic scap)) (ArrayV (DynArrayV vs)) /\
  val_wf (ArrayTV tv (Dynamic scap)) (ArrayV (DynArrayV vs)) /\
  val_in_memory (ArrayTV tv (Dynamic scap)) (ArrayV (DynArrayV vs)) (w2n sw) s.vs_memory /\
  type_memory_bytes cenv et = type_memory_size tv /\
  LENGTH vs <= cap /\ cap < dimword (:256) /\
  LENGTH vs * type_memory_size tv < dimword (:256) /\
  w2n sw + 32 < dimword (:256) /\ w2n dw + 32 < dimword (:256) /\
  w2n sw + type_memory_size (ArrayTV tv (Dynamic scap)) <= s.vs_alloca_next /\
  w2n dw + type_memory_size (ArrayTV tv (Dynamic cap)) <= s.vs_alloca_next /\
  (w2n sw + type_memory_size (ArrayTV tv (Dynamic scap)) <= w2n dw \/
   w2n dw + type_memory_size (ArrayTV tv (Dynamic cap)) <= w2n sw) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n dw) t.vs_memory /\
      typed_copy_effect ctx func sa sb s t (w2n dw)
        (type_memory_size (ArrayTV tv (Dynamic cap))) /\
      gas_path_mem ctx func s 0 (OK t)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `LENGTH vs <= scap` by metis_tac[typed_memory_dynarray_length] >>
  `LENGTH vs * type_memory_size tv <= scap * type_memory_size tv /\
   LENGTH vs * type_memory_size tv <= cap * type_memory_size tv` by simp[LE_MULT_RCANCEL] >>
  `mload (w2n sw) s = n2w (LENGTH vs)` by
    gvs[val_in_memory_dynarray, mem_word_at_eq_mload] >>
  `w2n sw + 32 + LENGTH vs * type_memory_bytes cenv et <= w2n dw \/
   w2n dw + 32 <= w2n sw` by
    (qpat_x_assum `w2n sw + type_memory_size _ <= _ \/ _` mp_tac >>
     simp[type_memory_size_def] >> decide_tac) >> (
  `w2n sw + 32 + LENGTH vs * type_memory_bytes cenv et <= s.vs_alloca_next /\
   w2n dw + 32 + LENGTH vs * type_memory_bytes cenv et <= s.vs_alloca_next` by
    (rule_assum_tac (PURE_REWRITE_RULE [type_memory_size_def]) >>
     pure_asm_rewrite_tac [] >> decide_tac) >>
  `LENGTH vs * type_memory_bytes cenv et < dimword (:256)` by simp[] >>
  drule_at (Pat `mload _ _ = _`) typed_memory_dynarray_fast_bytes_forward_mem >>
  disch_then drule >>
  disch_then (qspecl_then [`func`, `dw`, `ctx`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac []) >> strip_tac >>
  drule gas_marked_path_from_mem >> disch_then (qspec_then `F` assume_tac) >>
  qexists_tac `t` >> simp[] >> conj_tac
  >- (simp[val_in_memory_dynarray] >>
      irule (cj 3 valueEncodingProofsTheory.val_in_memory_relocate_proof) >>
      conj_tac >- gvs[val_wf_def] >>
      qexistsl_tac [`w2n sw + 32`, `s.vs_memory`] >>
      gvs[val_in_memory_dynarray, val_wf_def]) >>
  simp[typed_copy_effect_def] >> conj_tac
  >- (qpat_assum `_ = s` mp_tac >> simp[venom_state_component_equality]) >>
  conj_tac
  >- (qpat_assum `_ = s` mp_tac >> simp[venom_state_component_equality]) >>
  rpt gen_tac >> disch_tac >> first_x_assum irule >>
  qpat_x_assum `a + len <= w2n dw \/ _` mp_tac >>
  simp[type_memory_size_def] >> decide_tac)
QED

Theorem typed_memory_dynarray_slow_forward_mem:
  compile_copy_dynarray_typed cenv dst dt cap src st sa = ((),sb) /\
  ~(type_memory_bytes cenv dt = type_memory_bytes cenv st /\ dt = st) /\
  (!st dtv stv v dp sp a b u dw sw.
    type_widens_to tenv st dt /\
    evaluate_type tenv dt = SOME dtv /\ evaluate_type tenv st = SOME stv /\
    type_memory_bytes cenv dt = type_memory_size dtv /\
    type_memory_bytes cenv st = type_memory_size stv /\
    value_has_type dtv v /\ val_wf dtv v /\
    value_has_type stv v /\ val_wf stv v /\
    val_in_memory stv v (w2n sw) u.vs_memory /\
    (w2n sw + type_memory_size stv <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw) /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    w2n dw + type_memory_size dtv + 64 < dimword (:256) /\
    w2n sw + type_memory_size stv <= u.vs_alloca_next /\
    w2n dw + type_memory_size dtv <= u.vs_alloca_next /\
    compile_store_memory_typed cenv dp dt sp st a = ((),b) /\
    (!x. dp = Var x ==> not_fresh_at a x) /\
    (!x. sp = Var x ==> not_fresh_at a x) /\
    eval_operand dp u = SOME dw /\ eval_operand sp u = SOME sw /\
    fn_has_code a b func /\ ~u.vs_halted /\
    u.vs_current_bb = a.cs_current_bb /\
    u.vs_inst_idx = LENGTH a.cs_current_insts ==>
    ?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
        typed_copy_effect ctx func a b u t (w2n dw) (type_memory_size dtv) /\
        gas_path_mem ctx func u 0 (OK t)) /\
  type_widens_to tenv st dt /\
  evaluate_type tenv dt = SOME dtv /\ evaluate_type tenv st = SOME stv /\
  type_memory_bytes cenv dt = type_memory_size dtv /\
  type_memory_bytes cenv st = type_memory_size stv /\
  value_has_type (ArrayTV dtv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  val_wf (ArrayTV dtv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  value_has_type (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) /\
  val_wf (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) /\
  val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs))
    (w2n sw) s.vs_memory /\
  (w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) <= w2n dw \/
   w2n dw + type_memory_size (ArrayTV dtv (Dynamic cap)) <= w2n sw) /\
  w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) < dimword (:256) /\
  w2n dw + type_memory_size (ArrayTV dtv (Dynamic cap)) + 64 < dimword (:256) /\
  w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) <= s.vs_alloca_next /\
  w2n dw + type_memory_size (ArrayTV dtv (Dynamic cap)) <= s.vs_alloca_next /\
  cap < dimword (:256) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. val_in_memory (ArrayTV dtv (Dynamic cap)) (ArrayV (DynArrayV vs))
        (w2n dw) t.vs_memory /\
      typed_copy_effect ctx func sa sb s t (w2n dw)
        (type_memory_size (ArrayTV dtv (Dynamic cap))) /\
      gas_path_mem ctx func s 0 (OK t)
Proof
  strip_tac >> (
  drule_all typed_memory_dynarray_slow_compile >> strip_tac >>
  `fn_has_code sm sb func` by
    (qpat_x_assum `fn_has_code sa sb func` mp_tac >>
     gvs[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def, same_blocks_def]) >>
  drule_all typed_copy_dynarray_slow_code_lookup >> strip_tac >>
  `fn_has_code sa sm func` by suspend "setup_code" >>
  drule_all typed_copy_slow_array_control_layout >> strip_tac >>
  `(do so <- emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv st))];
       doff <- emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv dt))];
       sp <- emit_op ADD [src_data; so]; dp <- emit_op ADD [dst_data; doff];
       return (sp,dp) od) stb = ((sp,dp),b4)` by
    simp[comp_bind_def, comp_return_def] >>
  rpt (qpat_x_assum `fresh_label _ _ = _` kall_tac) >>
  qpat_x_assum `fresh_var _ = _` kall_tac >>
  rpt (qpat_x_assum `emit_inst _ _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `emit_op _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `new_block _ _ = _` kall_tac) >>
  qpat_x_assum `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `lookup_block st1.cs_current_bb _ = _` kall_tac >>
  qpat_x_assum `lookup_block st2.cs_current_bb _ = _` kall_tac >>
  qpat_x_assum `lookup_block st3.cs_current_bb _ = _` kall_tac >>
  `LENGTH vs <= cap /\ LENGTH vs <= scap` by
    metis_tac[typed_memory_dynarray_length] >>
  `mload (w2n sw) s = n2w (LENGTH vs)` by
    gvs[val_in_memory_dynarray, mem_word_at_eq_mload] >>
  `w2n sw + 32 <= s.vs_alloca_next /\ w2n dw + 32 <= s.vs_alloca_next` by
    (rule_assum_tac (PURE_REWRITE_RULE [type_memory_size_def]) >> decide_tac) >>
  drule_all typed_memory_dynarray_setup_forward_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `typed_copy_effect ctx func sa sm s t (w2n dw)
     (type_memory_size (ArrayTV dtv (Dynamic cap)))` by suspend "setup_effect" >>
  `?u. typed_copy_effect ctx func sm sth t u (w2n dw + 32)
        (LENGTH vs * type_memory_size dtv) /\
       gas_path_mem ctx func t 0 (OK u) /\
       lookup_var counter u = SOME 0w /\ u.vs_memory = t.vs_memory` by
    suspend "initial" >>
  suspend "integration")
QED

Resume typed_memory_dynarray_slow_forward_mem[setup_code]:
  markerLib.RESUME_TAC >>
  `isPREFIX sm.cs_current_insts st1.cs_current_insts /\
   st1.cs_current_bb = sm.cs_current_bb` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`fresh_label "typed_dyn_cond" _ = _`,
        `fresh_label "typed_dyn_body" _ = _`,
        `fresh_label "typed_dyn_exit" _ = _`,
        `fresh_var _ = _`, `emit_inst ASSIGN [Lit 0w] _ _ = _`,
        `emit_inst JMP [Label hdr] _ st0 = _`] >>
     rpt (first_x_assum kall_tac) >>
     simp[fresh_label_def, fresh_var_def, emit_inst_def, fresh_id_def,
          emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt strip_tac >> gvs[] >> simp[IS_PREFIX_APPEND]) >>
  simp[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def] >>
  gvs[same_blocks_def] >> metis_tac[IS_PREFIX_TRANS]
QED

Resume typed_memory_dynarray_slow_forward_mem[setup_effect]:
  markerLib.RESUME_TAC >>
  qpat_assum `gas_path_mem ctx func s 0 (OK t)`
    (mp_then Any (qspec_then `F` assume_tac) gas_marked_path_from_mem) >>
  `t.vs_allocas = s.vs_allocas /\
   (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
       vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
       vs_inst_idx := s.vs_inst_idx|>) = s` by
    (qpat_assum `(t with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  simp[typed_copy_effect_def] >> rpt strip_tac >>
  qpat_x_assum `!a len. _` (qspecl_then [`a`, `len`] mp_tac) >>
  simp[] >> gvs[type_memory_size_def] >> decide_tac
QED

Resume typed_memory_dynarray_slow_forward_mem[initial]:
  markerLib.RESUME_TAC >>
  `gas_path_mem ctx func t 0 (OK (jump_to hdr (update_var counter 0w t)))` by
    (irule typed_memory_array_init_path_mem >> simp[] >>
     qexistsl_tac [`id1`, `id2`] >> simp[]) >>
  drule gas_marked_path_from_mem >> disch_then (qspec_then `F` assume_tac) >>
  qexists_tac `jump_to hdr (update_var counter 0w t)` >> simp[] >>
  simp[typed_copy_effect_def, jump_to_def, update_var_def,
       venom_state_component_equality, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> metis_tac[]
QED

Resume typed_memory_dynarray_slow_forward_mem[integration]:
  markerLib.RESUME_TAC >> (
  qpat_x_assum `lookup_block sb.cs_current_bb _ = SOME bb` kall_tac >>
  qpat_x_assum `isPREFIX sb.cs_current_insts _` kall_tac >>
  `val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs))
     (w2n sw) u.vs_memory` by
    (simp[] >> irule val_in_memory_outside_write >> simp[] >>
     qexistsl_tac [`w2n dw`, `s.vs_memory`, `type_memory_size (ArrayTV dtv (Dynamic cap))`] >>
     simp[] >> rpt strip_tac >>
     qpat_x_assum `!a len. _` (qspecl_then [`a`, `len`] mp_tac) >>
     simp[] >> gvs[type_memory_size_def] >> decide_tac) >>
  qabbrev_tac `elem = \i. EL i vs` >>
  `!i. i < LENGTH vs ==>
       value_has_type stv (elem i) /\ val_wf stv (elem i) /\
       value_has_type dtv (elem i) /\ val_wf dtv (elem i)` by
    suspend "element_types" >>
  `?z. val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs))
          (w2n sw) z.vs_memory /\
       (!j. j < LENGTH vs ==> val_in_memory dtv (elem j)
          (w2n dw + 32 + j * type_memory_size dtv) z.vs_memory) /\
       typed_copy_effect ctx func sm sth t z (w2n dw + 32)
          (LENGTH vs * type_memory_size dtv) /\
       gas_path_mem ctx func t 0 (OK z) /\
       lookup_var counter z = SOME (n2w (LENGTH vs))` by
    (irule typed_memory_array_iteration_forward_mem >>
     qpat_assum `typed_copy_effect _ _ sm sth t u _ _` (irule_at Any) >>
     (conj_tac >- suspend "round") >>
     (conj_tac >- metis_tac[]) >>
     (conj_tac >-
       (`LENGTH vs * type_memory_size dtv <= cap * type_memory_size dtv` by simp[] >>
        rule_assum_tac (PURE_REWRITE_RULE [type_memory_size_def]) >>
        pure_rewrite_tac[type_memory_size_def] >> decide_tac)) >>
     simp[]) >>
  suspend "exit")
QED

Resume typed_memory_dynarray_slow_forward_mem[element_types]:
  markerLib.RESUME_TAC >>
  simp[Abbr `elem`, NoAsms] >>
  map_every (fn q => qpat_assum q mp_tac)
     [`value_has_type (ArrayTV dtv _) _`, `value_has_type (ArrayTV stv _) _`,
      `val_wf (ArrayTV dtv _) _`, `val_wf (ArrayTV stv _) _`] >>
  rpt (first_x_assum kall_tac) >>
  simp[val_wf_def, vyperTypingTheory.value_has_type_def] >>
  qid_spec_tac `vs` >> Induct >> simp[val_wf_def,
     vyperTypingTheory.value_has_type_def] >> rpt strip_tac >>
  Cases_on `i` >> gvs[] >> metis_tac[]
QED

Resume typed_memory_dynarray_slow_forward_mem[round]:
  markerLib.RESUME_TAC >>
  simp[type_memory_size_def] >> rpt strip_tac >>
  `~a.vs_halted /\ a.vs_current_bb = hdr /\ a.vs_inst_idx = 0` by
    gvs[typed_copy_effect_def] >>
  `eval_operand length a = SOME (n2w (LENGTH vs))` by
    (qpat_assum `typed_copy_effect ctx func sm sth t a _ _` mp_tac >>
     qpat_assum `eval_operand length t = _` mp_tac >>
     qpat_assum `!x. length = Var x ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `length` >>
     simp[typed_copy_effect_def, eval_operand_def, venom_state_component_equality] >>
     rpt strip_tac >> gvs[] >> metis_tac[]) >>
  drule_at (Pat `hbb.bb_instructions = _`) typed_memory_array_round_effect_mem >>
  disch_then irule >> simp[eval_operand_def] >>
  qpat_assum `DROP _ ebb.bb_instructions = _` (irule_at Any) >>
  rpt (goal_assum (drule_at Any)) >> simp[] >> rpt strip_tac >>
  `w2n (sw + 32w) = w2n sw + 32 /\
   w2n (dw + 32w) = w2n dw + 32` by
    (`w2n sw + 32 < dimword (:256) /\ w2n dw + 32 < dimword (:256)` by
       (rule_assum_tac (PURE_REWRITE_RULE [type_memory_size_def]) >> decide_tac) >>
     simp[wordsTheory.w2n_add_2]) >>
  `?v. val_in_memory dtv (elem i)
        (w2n (dw + 32w) + i * type_memory_size dtv) v.vs_memory /\
       typed_copy_effect ctx func stb b5 a' v
        (w2n (dw + 32w) + i * type_memory_size dtv) (type_memory_size dtv) /\
       gas_path_mem ctx func a' 0 (OK v)`
    suffices_by (simp[AC ADD_ASSOC ADD_COMM]) >>
  irule typed_memory_array_element_forward_mem >>
  qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _` (irule_at Any) >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  qexists_tac `sw + 32w` >> suspend "element"
QED

Resume typed_memory_dynarray_slow_forward_mem[element]:
  markerLib.RESUME_TAC >>
  `eval_operand src_data a' = SOME (sw + 32w) /\
   eval_operand dst_data a' = SOME (dw + 32w)` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`typed_copy_effect ctx func sm sth t a _ _`,
        `typed_copy_effect ctx func sm stb a a' _ _`,
        `eval_operand src_data t = SOME (sw + 32w)`,
        `eval_operand dst_data t = SOME (dw + 32w)`,
        `!x. src_data = Var x ==> _`, `!x. dst_data = Var x ==> _`] >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `src_data` >> Cases_on `dst_data` >>
     simp[eval_operand_def, typed_copy_effect_def,
          venom_state_component_equality] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `i * type_memory_size stv + type_memory_size stv <= scap * type_memory_size stv /\
   i * type_memory_size dtv + type_memory_size dtv <= cap * type_memory_size dtv` by
    (`SUC i <= scap /\ SUC i <= cap` by decide_tac >>
     `SUC i * type_memory_size stv <= scap * type_memory_size stv /\
      SUC i * type_memory_size dtv <= cap * type_memory_size dtv` by simp[] >>
     qpat_x_assum `SUC i * type_memory_size stv <= _` mp_tac >>
     qpat_x_assum `SUC i * type_memory_size dtv <= _` mp_tac >>
     pure_rewrite_tac[MULT_CLAUSES] >> decide_tac) >>
  `val_in_memory stv (elem i) (w2n sw + 32 + i * type_memory_size stv) a.vs_memory` by
    (qpat_x_assum `val_in_memory (ArrayTV stv _) _ _ a.vs_memory` mp_tac >>
     simp[val_in_memory_dynarray] >> strip_tac >>
     drule elems_in_memory_EL >> disch_then (qspec_then `i` mp_tac) >>
     simp[Abbr `elem`, AC ADD_ASSOC ADD_COMM]) >>
  `a'.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `typed_copy_effect ctx func sm sth t a _ _`
       (mp_then Any mp_tac typed_copy_effect_record) >>
     qpat_assum `typed_copy_effect ctx func sm stb a a' _ _`
       (mp_then Any mp_tac typed_copy_effect_record) >>
     qpat_assum `(t with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  drule typed_copy_effect_endpoint >> strip_tac >>
  qpat_assum `val_in_memory stv (elem i) _ a.vs_memory`
    (assume_tac o SRULE [AC ADD_ASSOC ADD_COMM]) >>
  simp[AC ADD_ASSOC ADD_COMM] >>
  rule_assum_tac (PURE_REWRITE_RULE [type_memory_size_def]) >> decide_tac
QED

Resume typed_memory_dynarray_slow_forward_mem[exit]:
  markerLib.RESUME_TAC >> (
  `~z.vs_halted /\ z.vs_current_bb = hdr /\ z.vs_inst_idx = 0` by
    gvs[typed_copy_effect_def] >>
  `eval_operand length z = SOME (n2w (LENGTH vs))` by
    (qpat_assum `typed_copy_effect ctx func sm sth t z _ _` mp_tac >>
     qpat_assum `eval_operand length t = _` mp_tac >>
     qpat_assum `!x. length = Var x ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `length` >>
     simp[eval_operand_def, typed_copy_effect_def, venom_state_component_equality] >>
     rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `?r. typed_copy_effect ctx func sm sb z r (w2n dw + 32)
         (LENGTH vs * type_memory_size dtv) /\
       gas_path_mem ctx func z 0 (OK r) /\
       lookup_var counter r = SOME (n2w (LENGTH vs)) /\ r.vs_memory = z.vs_memory` by
    (drule_at (Pat `hbb.bb_instructions = _`)
       (Q.INST [`N` |-> `LENGTH (vs:value list)`, `i` |-> `LENGTH (vs:value list)`]
         typed_memory_array_condition_effect_mem) >>
     disch_then (qspec_then `vs` irule) >> simp[] >>
     rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]) >>
  `typed_copy_effect ctx func sm sb t r (w2n dw + 32)
      (LENGTH vs * type_memory_size dtv)` by
    (irule typed_copy_effect_then >>
     qexistsl_tac [`sm`, `sth`, `z`] >> simp[]) >>
  `mem_bytes_at (w2n dw) 32 r.vs_memory = mem_bytes_at (w2n dw) 32 t.vs_memory` by
    (irule typed_copy_effect_bytes >> goal_assum (drule_at Any) >> simp[]) >>
  qexists_tac `r` >> conj_tac
  >- (simp[val_in_memory_dynarray] >> conj_tac
      >- (qpat_x_assum `mem_bytes_at _ _ r.vs_memory = _` mp_tac >>
          gvs[mem_word_at_def, mem_bytes_at_def]) >>
      irule elems_in_memory_intro >>
      qpat_x_assum `!j. j < LENGTH vs ==> val_in_memory _ _ _ _` mp_tac >>
      simp[Abbr `elem`]) >>
  conj_tac >- suspend "effect" >>
  metis_tac[gas_path_mem_then, ADD_CLAUSES])
QED

Resume typed_memory_dynarray_slow_forward_mem[effect]:
  markerLib.RESUME_TAC >> (
  irule typed_copy_effect_then >>
  qexistsl_tac [`sm`, `sm`, `t`] >> simp[] >> conj_tac
  >- (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
      goal_assum (drule_at Any) >> simp[]) >>
  irule typed_copy_effect_enlarge >> goal_assum (drule_at Any) >>
  simp[type_memory_size_def] >>
  `LENGTH vs * type_memory_size dtv <= cap * type_memory_size dtv` by simp[] >>
  decide_tac)
QED

Finalise typed_memory_dynarray_slow_forward_mem
