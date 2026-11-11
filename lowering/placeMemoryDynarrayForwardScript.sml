Theory placeMemoryDynarrayForward
Ancestors
  placeMemoryTypedPrimitive placeMemoryTypedBase placeMemoryPrimitiveForward
  context compileEnv loweringStateRelDefs exprLoweringProps emitHelper emitHelperProps
  venomState venomInst venomExecSemantics venomExecProofs fragExec
  valueEncodingProps valueEncoding valueEncodingDefs fragGasMode immutableMemoryFrame ASCIInumbers list rich_list finite_map

Theorem typed_memory_fresh_operand:
  (!x. op = Var x ==> not_fresh_at sa x) /\ sa.cs_next_var <= k ==>
  eval_operand op (update_var (STRING #"%" (toString k)) w s) = eval_operand op s
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_update_var] >>
  rpt strip_tac >>
  `s' <> STRING #"%" (toString k)` by metis_tac[not_fresh_at_def] >> simp[]
QED

Theorem typed_memory_dynarray_setup_sequence:
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
  mload (w2n sw) s = n2w n /\ n <= cap /\ cap < dimword (:256) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb) /\
  ?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
      eval_operand length u = SOME (n2w n) /\
      eval_operand src_data u = SOME (sw + 32w) /\
      eval_operand dst_data u = SOME (dw + 32w) /\
      u.vs_memory = (mstore (w2n dw) (n2w n) s).vs_memory /\
      (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s)
Proof
  strip_tac >>
  `!k w t. sa.cs_next_var <= k ==>
     eval_operand src (update_var (STRING #"%" (toString k)) w t) = eval_operand src t /\
     eval_operand dst (update_var (STRING #"%" (toString k)) w t) = eval_operand dst t` by
    (rpt strip_tac >> irule typed_memory_fresh_operand >> qexists_tac `sa` >> simp[]) >>
  qpat_x_assum `_ sa = ((_,_,_),sb)` mp_tac >>
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       fresh_var_def, fresh_id_def, emit_def, comp_return_def] >> strip_tac >>
  gvs[] >>
  simp[emitted_insts_def, same_blocks_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_APPEND, mk_inst_def, is_terminator_def] >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs,
       exec_read1_def, exec_write2_def, exec_pure1_def, exec_pure2_def,
       eval_operand_def, lookup_var_update_var, toString_inj] >>
  simp[update_var_def, mstore_def, write_memory_with_expansion_def,
       venom_state_component_equality] >>
  rpt strip_tac >>
  `!k. sa.cs_next_var <= k ==> x <> STRING #"%" (toString k)` by
    metis_tac[not_fresh_at_def] >> simp[]
QED

Theorem typed_memory_dynarray_setup_forward:
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
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
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
  `gas_marked_path F ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule straight_line_zero_gas_path >> simp[] >>
     qexistsl_tac [`emitted_insts sa sb`, `sa`] >> simp[]) >>
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

Theorem typed_memory_dynarray_data_sequence:
  (do data_sz <- emit_op MUL [length; Lit (n2w stride)];
      compile_copy_memory_dynamic dst src data_sz
   od) sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  eval_operand length s = SOME (n2w n) /\ n * stride < dimword (:256) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb) /\
  ?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
      u.vs_memory = (mcopy (w2n dw) (w2n sw) (n * stride) s).vs_memory /\
      (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s)
Proof
  strip_tac >>
  `!w t. eval_operand src (update_var (STRING #"%" (toString sa.cs_next_var)) w t) = eval_operand src t /\
         eval_operand dst (update_var (STRING #"%" (toString sa.cs_next_var)) w t) = eval_operand dst t` by
    (rpt strip_tac >> irule typed_memory_fresh_operand >> qexists_tac `sa` >> simp[]) >>
  qpat_x_assum `_ sa = ((),sb)` mp_tac >>
  simp[compile_copy_memory_dynamic_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def,
       emit_def, comp_return_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, same_blocks_def, DROP_APPEND1, mk_inst_def,
       is_terminator_def, run_inst_seq_def, step_inst_base_opcode_eqs,
       exec_pure2_def, eval_operand_def, lookup_var_update_var,
       wordsTheory.word_mul_n2w] >>
  simp[mcopy_def, write_memory_with_expansion_def, update_var_def,
       venom_state_component_equality] >> rpt strip_tac >>
  `x <> STRING #"%" (toString sa.cs_next_var)` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  simp[lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem typed_memory_dynarray_data_forward:
  (do data_sz <- emit_op MUL [length; Lit (n2w stride)];
      compile_copy_memory_dynamic dst src data_sz
   od) sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  eval_operand length s = SOME (n2w n) /\ n * stride < dimword (:256) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
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
  `gas_marked_path F ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule straight_line_zero_gas_path >> simp[] >>
     qexistsl_tac [`emitted_insts sa sb`, `sa`] >> simp[]) >>
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `(_ with <|vs_vars := _; vs_memory := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[lookup_var_def, mcopy_mem_bytes_at_same] >> rpt conj_tac
  >- (qpat_x_assum `(_ with <|vs_vars := _; vs_memory := _|>) = s` mp_tac >>
      simp[venom_state_component_equality])
  >- metis_tac[lookup_var_def]
  >- (rpt strip_tac >> irule mcopy_mem_bytes_at_disjoint >> decide_tac) >>
  simp[mcopy_memory_length]
QED

Theorem typed_memory_dynarray_fast_split:
  compile_copy_dynarray_typed cenv dst et cap src et sa = ((),sb) ==>
  ?length src_data dst_data sm.
    (do length <- emit_op MLOAD [src];
        too_long <- emit_op GT [length; Lit (n2w cap)];
        ok <- emit_op ISZERO [too_long];
        emit_void ASSERT [ok];
        emit_void MSTORE [dst; length];
        src_data <- emit_op ADD [src; Lit 32w];
        dst_data <- emit_op ADD [dst; Lit 32w];
        return (length,src_data,dst_data)
     od) sa = ((length,src_data,dst_data),sm) /\
    (do data_sz <- emit_op MUL [length; Lit (n2w (type_memory_bytes cenv et))];
        compile_copy_memory_dynamic dst_data src_data data_sz
     od) sm = ((),sb) /\
    (!x. src_data = Var x ==> not_fresh_at sm x) /\
    (!x. dst_data = Var x ==> not_fresh_at sm x) /\
    same_blocks sa sm /\ same_blocks sm sb /\
    sa.cs_current_bb = sm.cs_current_bb /\
    isPREFIX sa.cs_current_insts sm.cs_current_insts /\
    isPREFIX sm.cs_current_insts sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==> not_fresh_at sm x)
Proof
  strip_tac >>
  qabbrev_tac `setup =
    do length <- emit_op MLOAD [src];
       too_long <- emit_op GT [length; Lit (n2w cap)];
       ok <- emit_op ISZERO [too_long];
       emit_void ASSERT [ok];
       emit_void MSTORE [dst; length];
       src_data <- emit_op ADD [src; Lit 32w];
       dst_data <- emit_op ADD [dst; Lit 32w];
       return (length,src_data,dst_data)
    od` >>
  Cases_on `setup sa` >> rename1 `setup sa = (triple,sm)` >>
  PairCases_on `triple` >>
  qexistsl_tac [`triple0`, `triple1`, `triple2`, `sm`] >> simp[] >>
  `setup sa = ((triple0,triple1,triple2),sm)` by simp[] >>
  qpat_x_assum `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_x_assum `setup sa = _` mp_tac >>
  simp[Abbr `setup`, Once compile_store_memory_typed_def] >>
  simp[emit_op_def, emit_void_def, compile_copy_memory_dynamic_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
  simp[same_blocks_def, not_fresh_at_def, toString_inj, IS_PREFIX_APPEND] >>
  rpt strip_tac >> gvs[not_fresh_at_def] >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[]
QED

Theorem typed_memory_dynarray_fast_bytes_forward:
  compile_copy_dynarray_typed cenv dst et cap src et sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  mload (w2n sw) s = n2w n /\ n <= cap /\ cap < dimword (:256) /\
  n * type_memory_bytes cenv et < dimword (:256) /\
  w2n sw + 32 < dimword (:256) /\ w2n dw + 32 < dimword (:256) /\
  (w2n sw + 32 + n * type_memory_bytes cenv et <= w2n dw \/
   w2n dw + 32 <= w2n sw) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
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
    (gvs[fn_has_code_def, same_blocks_def, emitted_blocks_def] >>
     metis_tac[IS_PREFIX_TRANS]) >>
  drule_all typed_memory_dynarray_setup_forward >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_marked_path F ctx func s 0 (OK mid)` >>
  `w2n (sw + 32w) = w2n sw + 32 /\ w2n (dw + 32w) = w2n dw + 32` by
    simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  drule_all typed_memory_dynarray_data_forward >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_marked_path F ctx func mid 0 (OK t)` >>
  qexists_tac `t` >> simp[] >>
  conj_tac >- metis_tac[gas_marked_path_then, arithmeticTheory.ADD] >>
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
  >- (qpat_x_assum `_ = mid` mp_tac >>
      qpat_x_assum `_ = s` mp_tac >>
      simp[venom_state_component_equality] >> metis_tac[]) >>
  rpt strip_tac >>
  `mem_bytes_at a len t.vs_memory = mem_bytes_at a len mid.vs_memory` by
    (first_assum irule >> simp[] >> decide_tac) >>
  `mem_bytes_at a len mid.vs_memory = mem_bytes_at a len s.vs_memory` by
    (first_assum irule >> simp[] >> decide_tac) >> simp[]
QED

Theorem typed_memory_dynarray_fast_forward:
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
  (w2n sw + type_memory_size (ArrayTV tv (Dynamic scap)) <= w2n dw \/
   w2n dw + type_memory_size (ArrayTV tv (Dynamic cap)) <= w2n sw) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\
      (!a len. a + len <= w2n dw \/
               w2n dw + type_memory_size (ArrayTV tv (Dynamic cap)) <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `LENGTH vs <= scap` by metis_tac[typed_memory_dynarray_length] >>
  `LENGTH vs * type_memory_size tv <= scap * type_memory_size tv /\
   LENGTH vs * type_memory_size tv <= cap * type_memory_size tv` by
    simp[arithmeticTheory.LE_MULT_RCANCEL] >>
  `mload (w2n sw) s = n2w (LENGTH vs)` by
    gvs[val_in_memory_dynarray, mem_word_at_eq_mload] >>
  Q.SUBGOAL_THEN
    `w2n sw + 32 + LENGTH vs * type_memory_bytes cenv et <= w2n dw \/
     w2n dw + 32 <= w2n sw` assume_tac
  >- (qpat_x_assum `w2n sw + type_memory_size _ <= _ \/ _` mp_tac >>
      simp[type_memory_size_def] >> decide_tac) >>
  `LENGTH vs * type_memory_bytes cenv et < dimword (:256)` by simp[] >>
  drule_all typed_memory_dynarray_fast_bytes_forward >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> simp[] >>
  conj_tac
  >- (simp[val_in_memory_dynarray] >>
      irule (cj 3 valueEncodingProofsTheory.val_in_memory_relocate_proof) >>
      conj_tac >- gvs[val_wf_def] >>
      qexistsl_tac [`w2n sw + 32`, `s.vs_memory`] >>
      gvs[val_in_memory_dynarray, val_wf_def]) >>
  conj_tac
  >- (qpat_x_assum `_ = s` mp_tac >>
      simp[venomStateTheory.venom_state_component_equality]) >>
  conj_tac
  >- (qpat_x_assum `_ = s` mp_tac >>
      simp[venomStateTheory.venom_state_component_equality]) >>
  rpt gen_tac >> disch_tac >> first_x_assum irule >>
  qpat_x_assum `_ \/ _` (fn th => mp_tac th) >>
  simp[type_memory_size_def] >> decide_tac
QED
