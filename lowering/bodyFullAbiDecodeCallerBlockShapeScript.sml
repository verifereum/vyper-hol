Theory bodyFullAbiDecodeCallerBlockShape
Ancestors exprSimAbiDecodeOblivious abiDecoderAppend abiBuiltinDecodeHeader
  abiBuiltinLengthGuard abiBuiltinBoundTests builtinAbi emitHelperProps
  fragExec exprSimAbiGasBridge list rich_list context emitHelper compileEnv

Theorem lower_abi_decode_last_suffix_nonempty[local]:
  lower_abi_decode data di mn mx msz a = (out,c) /\
  a.cs_blocks <> c.cs_blocks ==>
  DROP (LENGTH a.cs_current_insts)
       (LAST (emitted_blocks a c)).bb_instructions <> []
Proof
  strip_tac >> drule lower_abi_decode_trace >> strip_tac >>
  drule cs_extends_abi_decode >> strip_tac >>
  `header_st.cs_blocks = a.cs_blocks /\
   LENGTH a.cs_current_insts < LENGTH header_st.cs_current_insts` by
    (Cases_on `mn = mx` >>
     qpat_x_assum `abi_builtin_decode_header _ _ _ _ = _` mp_tac >>
     simp[abi_builtin_decode_header_def, abi_builtin_length_guard_def,
       abi_builtin_interval_guard_def, abi_builtin_eq_guard_def,
       abi_builtin_bound_test_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >> strip_tac >> gvs[]) >>
  `ready.cs_blocks = header_st.cs_blocks /\
   LENGTH header_st.cs_current_insts <= LENGTH ready.cs_current_insts` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
     strip_tac >> gvs[]) >>
  `emitted_blocks ready c = emitted_blocks a c` by simp[emitted_blocks_def] >>
  drule frag_extends_emitted_shape >>
  Cases_on `emitted_blocks ready c = []` >> simp[] >> strip_tac >>
  drule IS_PREFIX_LENGTH >> simp[] >> decide_tac
QED

Theorem decode_entry_not_opened_front[local]:
  cs_extends a b /\ a.cs_blocks <> b.cs_blocks /\ fn_has_code a b fn /\
  DROP (LENGTH a.cs_current_insts) (LAST (emitted_blocks a b)).bb_instructions <> [] /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code a b)) ==>
  ~MEM a.cs_current_bb (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks a b)))
Proof
  strip_tac >> drule frag_extends_emitted_shape >>
  Cases_on `emitted_blocks a b = []` >> simp[] >> strip_tac >>
  simp[MEM_MAP] >> rpt strip_tac >>
  `MEM bb (emitted_blocks a b) /\
   MEM (LAST (emitted_blocks a b)) (emitted_blocks a b)` by
    metis_tac[MEM_FRONT_NOT_NIL, MEM_LAST_NOT_NIL] >>
  `bb = LAST (emitted_blocks a b)` by
    (qpat_x_assum `fn_has_code _ _ _` mp_tac >>
     simp[fn_has_code_def] >> metis_tac[optionTheory.SOME_11]) >>
  `?i. MEM i (DROP (LENGTH a.cs_current_insts) (LAST (emitted_blocks a b)).bb_instructions)` by
    ((Cases_on `DROP (LENGTH a.cs_current_insts) (LAST (emitted_blocks a b)).bb_instructions` >> fs[] >> (metis_tac[]))) >>
  `MEM i bb.bb_instructions` by (drule MEM_DROP_IMP >> simp[]) >>
  `MEM i (FLAT (MAP (\bb. bb.bb_instructions) (FRONT (emitted_blocks a b))))` by
    (simp[MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  qpat_x_assum `ALL_DISTINCT _` mp_tac >>
  simp[frag_code_def, NULL_EQ, ALL_DISTINCT_APPEND, MAP_APPEND, MEM_MAP] >>
  metis_tac[]
QED

Theorem lower_abi_decode_opened_labels_exclude_entry:
  lower_abi_decode data di mn mx msz a = (out,b) /\
  a.cs_blocks <> b.cs_blocks /\ a.cs_current_bb <> b.cs_current_bb /\
  fn_has_code a b fn ==>
  ~MEM a.cs_current_bb (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks a b))) /\
  ~MEM b.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks a b))
Proof
  strip_tac >> drule lower_abi_decode_frag_facts >> strip_tac >>
  `~MEM a.cs_current_bb (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks a b)))` by
    metis_tac[decode_entry_not_opened_front, lower_abi_decode_last_suffix_nonempty] >>
  simp[] >> drule frag_extends_emitted_shape >>
  Cases_on `emitted_blocks a b = []` >> simp[] >> strip_tac >>
  drule APPEND_FRONT_LAST >>
  disch_then (fn th => pure_once_rewrite_tac[GSYM th]) >>
  simp[MAP_APPEND] >> metis_tac[]
QED
