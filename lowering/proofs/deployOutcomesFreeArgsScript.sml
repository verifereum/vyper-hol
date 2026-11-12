Theory deployOutcomesFreeArgs
Ancestors
  deployOutcomesFreeLowering deployOutcomesFreeGenerators abiEncoder moduleLowering context emitHelper
  compileEnv list pair

Theorem outcomes_free_abi_clamp:
  EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE) (state_insts s) ==>
  EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_abi_clamp_basetype v ci s)))
Proof
  strip_tac >> Cases_on `ci` >>
  simp[compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
       compile_abi_bytes_clamp_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_emit_ops, outcomes_free_return]),
    gen_tac, strip_tac, irule outcomes_free_bind,
    irule outcomes_free_ignore_bind, conj_tac, IF_CASES_TAC]) >> gvs[outcomes_free_emit_ops]
QED

Theorem outcomes_free_abi_dec_addr:
  EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE) (state_insts s) ==>
  EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_abi_dec_addr b p s)))
Proof
  strip_tac >> simp[compile_abi_dec_addr_def] >> IF_CASES_TAC >>
  gvs[outcomes_free_return, outcomes_free_emit_ops]
QED

Theorem outcomes_free_abi_range_check:
  EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE) (state_insts s) ==>
  EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_abi_decode_range_check a b hi s)))
Proof
  strip_tac >> simp[compile_abi_decode_range_check_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_emit_ops, outcomes_free_return]),
    gen_tac, strip_tac, irule outcomes_free_bind,
    irule outcomes_free_ignore_bind, conj_tac]) >> gvs[outcomes_free_emit_ops]
QED

Theorem outcomes_free_abi_static:
  ~MEM opc [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE] /\
  (!v s. EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE) (state_insts s) ==>
    EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE) (state_insts (SND (clamp v s)))) /\
  EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE) (state_insts s) ==>
  EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_abi_decode_static src dst opc clamp s)))
Proof
  strip_tac >> simp[compile_abi_decode_static_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_emit_ops, outcomes_free_return]),
    gen_tac, strip_tac, irule outcomes_free_bind,
    irule outcomes_free_ignore_bind, conj_tac]) >> gvs[outcomes_free_emit_ops, outcomes_free_abi_dec_addr, outcomes_free_abi_range_check]
QED

Theorem outcomes_free_getelemptr_abi:
  ~MEM opc [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE] /\
  EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE) (state_insts s) ==>
  EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_getelemptr_abi src dyn off opc b hi s)))
Proof
  strip_tac >> simp[compile_getelemptr_abi_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_emit_ops, outcomes_free_return,
    outcomes_free_abi_dec_addr]),
    gen_tac, strip_tac, irule outcomes_free_bind,
    irule outcomes_free_ignore_bind, conj_tac, IF_CASES_TAC]) >> gvs[outcomes_free_emit_ops, outcomes_free_abi_dec_addr, outcomes_free_abi_range_check]
QED

Theorem outcomes_free_abi_dyn_elem_ptr:
  ~MEM opc [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE] /\
  EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE) (state_insts s) ==>
  EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_abi_decode_dyn_elem_ptr opc b es sd hi asz s)))
Proof
  strip_tac >> simp[compile_abi_decode_dyn_elem_ptr_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_emit_ops, outcomes_free_return,
    outcomes_free_abi_dec_addr, outcomes_free_abi_range_check]),
    gen_tac, strip_tac, irule outcomes_free_bind,
    irule outcomes_free_ignore_bind, conj_tac, IF_CASES_TAC]) >> gvs[outcomes_free_emit_ops, outcomes_free_abi_dec_addr, outcomes_free_abi_range_check]
QED

Theorem outcomes_free_abi_bytes_copy[local]:
  EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE) (state_insts s) ==>
  EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE)
    (state_insts (SND ((case opc of
      CALLDATALOAD => emit_void CALLDATACOPY [dst; src; sz]
    | DLOAD => emit_void DLOADBYTES [dst; src; sz]
    | _ => emit_void MCOPY [dst; src; sz]) s)))
Proof
  Cases_on `opc` >> gvs[outcomes_free_emit_ops]
QED

val outcomes_free_decode_case_tac =
  simp[Once compile_abi_decode_to_buf_def] >>
  rpt (FIRST [gen_tac, strip_tac,
    irule outcomes_free_bind, irule outcomes_free_ignore_bind,
    conj_tac, IF_CASES_TAC,
    CHANGED_TAC (gvs[outcomes_free_emit_ops, outcomes_free_return,
      outcomes_free_fresh, outcomes_free_new_block,
      outcomes_free_abi_static, outcomes_free_abi_clamp,
      outcomes_free_getelemptr_abi, outcomes_free_abi_dyn_elem_ptr,
      outcomes_free_abi_dec_addr, outcomes_free_abi_range_check,
      outcomes_free_alloc_buffer, outcomes_free_abi_bytes_copy])]) >> gvs[];

Theorem outcomes_free_abi_decode:
  (!dst src opc b hi info s.
    ~MEM opc [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE] /\
    EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE) (state_insts s) ==>
    EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_abi_decode_to_buf dst src opc b hi info s)))) /\
  (!dst src opc b hi elems ao vo s.
    ~MEM opc [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE] /\
    EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE) (state_insts s) ==>
    EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_abi_decode_complex_elems dst src opc b hi elems ao vo s)))) /\
  (!dst src opc b hi ei asz msz ip cnt s.
    ~MEM opc [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE] /\
    EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE) (state_insts s) ==>
    EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_abi_decode_dyn_loop dst src opc b hi ei asz msz ip cnt s))))
Proof
  ho_match_mp_tac compile_abi_decode_to_buf_ind >> rpt strip_tac
  >~ [`compile_abi_decode_to_buf _ _ _ _ _ (DecPrimWord _) _`]
  >- outcomes_free_decode_case_tac
  >~ [`compile_abi_decode_to_buf _ _ _ _ _ (DecBytestring _) _`]
  >- outcomes_free_decode_case_tac
  >~ [`compile_abi_decode_to_buf _ _ _ _ _ (DecDynArray _ _ _ _ _) _`]
  >- outcomes_free_decode_case_tac
  >~ [`compile_abi_decode_to_buf _ _ _ _ _ (DecComplex _ _) _`]
  >- outcomes_free_decode_case_tac
  >~ [`compile_abi_decode_complex_elems _ _ _ _ _ [] _ _ _`]
  >- outcomes_free_decode_case_tac
  >~ [`compile_abi_decode_complex_elems _ _ _ _ _ (_::_) _ _ _`]
  >- outcomes_free_decode_case_tac >>
  outcomes_free_decode_case_tac
QED

Theorem outcomes_free_decode_args:
  !args env off opc hi base s.
  ~MEM opc [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE] /\
  EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE) (state_insts s) ==>
  EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_decode_args env args off opc hi base s)))
Proof
  Induct_on `args` >- simp[compile_decode_args_def, outcomes_free_return] >>
  gen_tac >> PairCases_on `h` >> rpt strip_tac >>
  Cases_on `h1` >> Cases_on `h2` >>
  Cases_on `FLOOKUP env.ce_vars h0` >>
  simp[compile_decode_args_def] >>
  rpt (FIRST [gen_tac, strip_tac,
    CHANGED_TAC (gvs[outcomes_free_emit_ops, outcomes_free_return,
      outcomes_free_abi_clamp, cj 1 outcomes_free_abi_decode]),
    irule outcomes_free_bind, irule outcomes_free_ignore_bind, conj_tac,
    (qmatch_goalsub_rename_tac `var_location_decode_operand loc` >>
      Cases_on `var_location_decode_operand loc`)]) >>
  qpat_x_assum `!env off opc hi base s. _` irule >> simp[]
QED

Theorem outcomes_free_register_constructor_args_state:
  !args env off sz s.
  EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE) (state_insts s) ==>
  EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_register_constructor_args env args off sz s)))
Proof
  Induct_on `args` >- simp[compile_register_constructor_args_def, outcomes_free_return] >>
  gen_tac >> PairCases_on `h` >> rpt strip_tac >>
  Cases_on `FLOOKUP env.ce_vars h0` >>
  simp[compile_register_constructor_args_def] >>
  rpt (FIRST [gen_tac, strip_tac,
    CHANGED_TAC (gvs[outcomes_free_alloc_buffer, outcomes_free_return,
      outcomes_free_decode_args]),
    irule outcomes_free_bind, irule outcomes_free_ignore_bind, conj_tac,
    (qmatch_goalsub_rename_tac `var_location_memory_size loc` >>
      Cases_on `var_location_memory_size loc`)]) >>
  qpat_x_assum `!env off sz s. _` irule >> simp[]
QED

Theorem outcomes_free_register_constructor_args:
  compile_register_constructor_args env args off sz s = (env', s') /\
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) bb.bb_instructions) (all_blocks s) ==>
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) bb.bb_instructions) (all_blocks s')
Proof
  strip_tac >>
  mp_tac outcomes_free_register_constructor_args_state >>
  disch_then (qspecl_then [`args`, `env`, `off`, `sz`, `s`] mp_tac) >>
  gvs[outcomes_free_all_blocks]
QED
