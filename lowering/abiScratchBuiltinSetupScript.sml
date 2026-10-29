(* Execute actual builtin output allocation, address setup and optional method ID.
   TOP-LEVEL: abi_scratch_builtin_setup_reach exposes a common physical setup
   frame for both options, retaining the full 32-byte method-store width. *)
Theory abiScratchBuiltinSetup
Ancestors
  abiBuiltinEncodeSetup abiBuiltinEncodeMethod abiBuiltinEncodeRun abiBuiltinAllocation
  abiDecoderFrame abiDecoderReentry abiDecoderContract abiDecoderLoop compileEnv valueEncoding
  venomState finite_map words list arithmetic

Theorem abi_scratch_builtin_none_frame:
  abi_builtin_allocation_frame next site outsz initial actual ==>
  abi_builtin_encode_setup_frame next site outsz p 0 initial actual
Proof
  simp[abi_builtin_allocation_frame_def, abi_builtin_encode_setup_frame_def, abi_decode_frame_def]
QED

Theorem abi_scratch_builtin_setup_reach:
  abi_builtin_encode_setup method_id_opt maxlen st = (ops,ready) /\ fn_has_code st ready func /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id =
      SOME (p,maxlen+32+(case method_id_opt of NONE => 0 | SOME _ => 4))) /\
  p+maxlen+32+(case method_id_opt of NONE => 0 | SOME _ => 4) < dimword (:256) /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand (FST ops) actual = SOME (n2w p) /\
    eval_operand (SND ops) actual = SOME (n2w (p+32+(case method_id_opt of NONE => 0 | SOME _ => 4))) /\
    mem_bytes_at (p+32) (LENGTH (abi_builtin_encode_prefix method_id_opt)) actual.vs_memory =
      abi_builtin_encode_prefix method_id_opt /\ fresh_vars_wrt limit_st actual /\
    abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id
      (maxlen+32+(case method_id_opt of NONE => 0 | SOME _ => 4)) p
      (case method_id_opt of NONE => 0 | SOME _ => 32) initial actual /\
    actual.vs_current_bb = ready.cs_current_bb /\ actual.vs_inst_idx = LENGTH ready.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  Cases_on `method_id_opt` >>
  simp_tac (srw_ss()) [abi_builtin_encode_prefix_def, abi_builtin_encode_method_bytes_length] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS)
  >- (`maxlen+32 < dimword (:256)` by decide_tac >>
      drule_all abi_builtin_encode_setup_none_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
      rename1 `abi_decode_sim ctx func initial actual` >>
      drule abi_scratch_builtin_none_frame >> disch_then (qspec_then `p` assume_tac) >>
      qexists_tac `actual` >> asm_simp_tac (srw_ss()) [mem_bytes_at_def]) >>
  `maxlen+36 < dimword (:256) /\ p+32 < dimword (:256)` by decide_tac >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [GSYM ADD_ASSOC]) >>
  drule_all abi_builtin_encode_method_setup_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) [GSYM ADD_ASSOC]
QED
