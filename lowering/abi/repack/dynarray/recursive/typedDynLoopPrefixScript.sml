(* TOP-LEVEL: execute the actual shared length/capacity prefix, preserve
   the source and expose its live payload. Complete-array bounds, header
   layout and full-footprint memory frames compose independently of children. *)
Theory typedDynLoopPrefix
Ancestors
  typedCopyStateFrame
  typedArrayCopyMemory typedDynLoopMemory memoryValueTyping memoryValueFrame memoryValueDefs
  dynCopyPrefixPath typedDynLoopCode typedSArrayDynInvariant abiBytestringCode abiStaticLoopCode
  logBytesStoreProps valueEncoding valueEncodingProps compileEnv
  vyperValue vyperTyping venomState list words arithmetic

Theorem array_copy_dynamic_values:
  !tv capacity vs.
    value_has_type (ArrayTV tv (Dynamic capacity)) (ArrayV (DynArrayV vs)) ==>
    LENGTH vs <= capacity /\ (!j. j < LENGTH vs ==> value_has_type tv (EL j vs))
Proof
  simp[value_has_type_def, all_have_type_EVERY, EVERY_EL]
QED

Theorem array_copy_dynamic_payload_bounds:
  !tv capacity copy_count (addr:bytes32).
    copy_count <= capacity /\
    w2n addr + type_memory_size (ArrayTV tv (Dynamic capacity)) < dimword(:256) ==>
    w2n (addr + 32w) = w2n addr + 32 /\
    w2n (addr + 32w) + copy_count * type_memory_size tv < dimword(:256)
Proof
  rpt gen_tac >> strip_tac >>
  `copy_count * type_memory_size tv <= capacity * type_memory_size tv` by simp[LE_MULT_RCANCEL] >>
  `w2n addr + 32 < dimword(:256)` by
    (qpat_x_assum `w2n addr + _ < _` mp_tac >> simp_tac bool_ss [type_memory_size_def] >> decide_tac) >>
  `w2n (addr + 32w) = w2n addr + 32` by
    (mp_tac (Q.SPECL [`addr`, `32`] log_field_address) >> simp[]) >>
  asm_simp_tac bool_ss [] >>
  qpat_x_assum `w2n addr + type_memory_size (ArrayTV tv (Dynamic capacity)) < _` mp_tac >>
  simp_tac bool_ss [type_memory_size_def] >> decide_tac
QED

Theorem array_copy_dynamic_payload_separated:
  !ftv atv src_capacity dst_capacity copy_count src_off dst_off.
    copy_count <= src_capacity /\ copy_count <= dst_capacity /\
    (src_off + type_memory_size (ArrayTV atv (Dynamic src_capacity)) <= dst_off \/
      dst_off + type_memory_size (ArrayTV ftv (Dynamic dst_capacity)) <= src_off) ==>
    src_off + 32 + copy_count * type_memory_size atv <= dst_off + 32 \/
      dst_off + 32 + copy_count * type_memory_size ftv <= src_off + 32
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `copy_count * type_memory_size atv <= src_capacity * type_memory_size atv` by simp[LE_MULT_RCANCEL] >>
  `copy_count * type_memory_size ftv <= dst_capacity * type_memory_size ftv` by simp[LE_MULT_RCANCEL] >>
  qpat_x_assum `_ \/ _` mp_tac >> simp_tac bool_ss [type_memory_size_def] >> decide_tac
QED

Theorem array_copy_dynamic_source_prefix:
  !tv vs capacity src_off dst_off ss.
    value_has_type (ArrayTV tv (Dynamic capacity)) (ArrayV (DynArrayV vs)) /\
    memory_value_rel (ArrayTV tv (Dynamic capacity)) (ArrayV (DynArrayV vs)) src_off ss.vs_memory /\
    (src_off + type_memory_size (ArrayTV tv (Dynamic capacity)) <= dst_off \/ dst_off + 32 <= src_off) ==>
    array_copy_prefix tv (\j. EL j vs) (LENGTH vs) (src_off + 32)
      (mstore dst_off (n2w (LENGTH vs)) ss).vs_memory
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `val_wf (ArrayTV tv (Dynamic capacity)) (ArrayV (DynArrayV vs))` by
    (irule value_has_type_val_wf >> first_assum MATCH_ACCEPT_TAC) >>
  mp_tac (Q.SPECL [`ArrayTV tv (Dynamic capacity)`, `ArrayV (DynArrayV vs)`, `src_off`,
    `dst_off`, `(n2w (LENGTH (vs:value list)):bytes32)`, `ss`] mstore_preserves_memory_value_rel) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  simp_tac bool_ss [array_copy_dynamic_layout] >> simp[]
QED

Theorem array_copy_dynamic_header_separated:
  !ftv atv src_capacity dst_capacity src_off dst_off.
    (src_off + type_memory_size (ArrayTV atv (Dynamic src_capacity)) <= dst_off \/
      dst_off + type_memory_size (ArrayTV ftv (Dynamic dst_capacity)) <= src_off) ==>
    src_off + type_memory_size (ArrayTV atv (Dynamic src_capacity)) <= dst_off \/ dst_off + 32 <= src_off
Proof
  rpt gen_tac >> simp_tac bool_ss [type_memory_size_def] >> decide_tac
QED

Theorem dynarray_copy_prefix_source_path:
  !ctx func cs dst src capacity src_capacity atv vs ss dst_addr src_addr.
    fn_has_code cs (dyn_copy_prefix_state cs dst src capacity) func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    LENGTH vs <= capacity /\ capacity < dimword(:256) /\
    value_has_type (ArrayTV atv (Dynamic src_capacity)) (ArrayV (DynArrayV vs)) /\
    memory_value_rel (ArrayTV atv (Dynamic src_capacity)) (ArrayV (DynArrayV vs)) (w2n src_addr) ss.vs_memory /\
    (w2n src_addr + type_memory_size (ArrayTV atv (Dynamic src_capacity)) <= w2n dst_addr \/ w2n dst_addr + 32 <= w2n src_addr) /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    EVERY (\name. dst <> Var name /\ src <> Var name) (compiler_var_names cs.cs_next_var 5) ==>
    ?entry_ss. fragment_path ctx func ss entry_ss /\ copy_state_frame ss entry_ss /\ entry_ss.vs_current_bb = cs.cs_current_bb /\
      entry_ss.vs_inst_idx = LENGTH (dyn_copy_prefix_state cs dst src capacity).cs_current_insts /\ ~entry_ss.vs_halted /\
      entry_ss.vs_memory = (mstore (w2n dst_addr) (n2w (LENGTH vs)) ss).vs_memory /\
      eval_operand (Var (compiler_var_name cs.cs_next_var 0)) entry_ss = SOME (n2w (LENGTH vs)) /\
      eval_operand (Var (compiler_var_name cs.cs_next_var 3)) entry_ss = SOME (src_addr + 32w) /\
      eval_operand (Var (compiler_var_name cs.cs_next_var 4)) entry_ss = SOME (dst_addr + 32w) /\
      array_copy_prefix atv (\j. EL j vs) (LENGTH vs) (w2n src_addr + 32) entry_ss.vs_memory /\
      (!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names cs.cs_next_var 5) ==>
        eval_operand arg_op entry_ss = eval_operand arg_op ss)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `mload (w2n src_addr) ss = n2w (LENGTH vs)` by
    (qpat_x_assum `memory_value_rel _ _ _ ss.vs_memory` mp_tac >>
     simp_tac bool_ss [array_copy_dynamic_layout, mem_word_at_eq_mload] >> simp[]) >>
  drule_all_then (qspec_then `ctx` strip_assume_tac) dyn_copy_prefix_path >>
  `array_copy_prefix atv (\j. EL j vs) (LENGTH vs) (w2n src_addr + 32) entry_ss.vs_memory` by
    (asm_simp_tac bool_ss [] >> irule array_copy_dynamic_source_prefix >> qexists_tac `src_capacity` >> simp[]) >>
  qexists_tac `entry_ss` >> asm_simp_tac bool_ss [dyn_copy_prefix_state_fields] >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem dynarray_copy_complete_layout_frame:
  !ftv atv vs capacity src_data dst ss prefix_ss after_mem.
    LENGTH vs <= capacity /\ prefix_ss.vs_memory = (mstore dst (n2w (LENGTH vs)) ss).vs_memory /\
    array_copy_memory_inv ftv atv (\j. EL j vs) (LENGTH vs) src_data (dst + 32)
      prefix_ss.vs_memory (LENGTH vs) after_mem ==>
    memory_value_rel (ArrayTV ftv (Dynamic capacity)) (ArrayV (DynArrayV vs)) dst after_mem /\
    (!other_tv other_v offset.
      memory_value_rel other_tv other_v offset ss.vs_memory /\ val_wf other_tv other_v /\
      (offset + type_memory_size other_tv <= dst \/ dst + type_memory_size (ArrayTV ftv (Dynamic capacity)) <= offset) ==>
      memory_value_rel other_tv other_v offset after_mem)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >> conj_tac
  >- (mp_tac (Q.SPECL [`ftv`, `atv`, `vs`, `capacity`, `src_data`, `dst`, `prefix_ss.vs_memory`, `after_mem`]
        dynarray_copy_payload_layout) >> impl_tac >- simp[mstore_mem_word_at_same] >> simp[]) >>
  mp_tac (Q.SPECL [`ftv`, `capacity`, `dst`, `LENGTH (vs:value list)`, `ss`, `after_mem`] dynarray_copy_full_frame) >> impl_tac
  >- (asm_simp_tac bool_ss [] >> qpat_x_assum `array_copy_memory_inv _ _ _ _ _ _ _ _ _` mp_tac >>
      simp_tac bool_ss [array_copy_memory_inv_def] >> simp[]) >> simp[]
QED
