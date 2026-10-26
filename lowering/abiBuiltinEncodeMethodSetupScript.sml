(* Actual allocation, data-pointer ADD and method-ID ADD/MSTORE setup. *)
Theory abiBuiltinEncodeMethodSetup
Ancestors
  abiBuiltinEncodeMethodReach abiBuiltinEncodeMethod abiBuiltinEncodeAllocate abiBuiltinEncodeAllocateCode
  abiBuiltinEncodeCode abiBuiltinEncodeSetupFrame abiBuiltinAllocationState abiDecoderReentry
  abiDecoderContract abiDecoderLoop fragExec compileEnv venomState venomExecSemantics
  words finite_map list arithmetic

Theorem abi_builtin_encode_method_setup_context:
  abi_builtin_encode_setup (SOME mid) maxlen st = (ops,ready) /\ fn_has_code st ready func ==>
  ?address_st.
    abi_builtin_encode_allocate (maxlen+36) 36 st = (ops,address_st) /\
    abi_builtin_encode_method_id (SOME mid) (FST ops) address_st = ((),ready) /\
    fn_has_code st address_st func /\ fn_has_code address_st ready func /\
    address_st.cs_next_var = st.cs_next_var+2 /\ ready.cs_next_var = address_st.cs_next_var+1
Proof
  strip_tac >> drule abi_builtin_encode_setup_allocate_trace >> strip_tac >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [GSYM ADD_ASSOC]) >>
  drule abi_builtin_encode_allocate_shape >> strip_tac >>
  drule abi_builtin_encode_method_shape >> strip_tac >>
  `cs_extends st address_st /\ cs_extends address_st ready` by
    (conj_tac >> irule cs_extends_same_block >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.SPECL [`st`, `address_st`, `ready`, `func`] fn_has_code_split) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `address_st` >> asm_simp_tac bool_ss []
QED

Theorem abi_builtin_encode_method_setup_reach:
  abi_builtin_encode_setup (SOME mid) maxlen st = (ops,ready) /\ fn_has_code st ready func /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,maxlen+36)) /\
  maxlen+36 < dimword (:256) /\ p+32 < dimword (:256) /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand (FST ops) actual = SOME (n2w p) /\
    eval_operand (SND ops) actual = SOME (n2w (p+36)) /\
    mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes mid /\
    fresh_vars_wrt limit_st actual /\
    abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id (maxlen+36) p 32 initial actual /\
    actual.vs_current_bb = ready.cs_current_bb /\ actual.vs_inst_idx = LENGTH ready.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_builtin_encode_method_setup_context >> strip_tac >>
  drule abi_builtin_encode_allocate_live >> strip_tac >>
  `address_st.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= address_st.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`outsz` |-> `maxlen+36:num`, `data_offset` |-> `36:num`, `ctx` |-> `ctx`]
    abi_builtin_encode_allocate_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial addressed` >>
  mp_tac (Q.INST [`st` |-> `address_st`, `final` |-> `ready`, `buf` |-> `FST (ops:operand # operand)`,
    `initial` |-> `addressed:venom_state`, `ctx` |-> `ctx`] abi_builtin_encode_method_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func addressed actual` >>
  `actual.vs_halted = addressed.vs_halted` by simp[] >>
  `eval_operand (FST ops) actual = SOME (n2w p) /\
   eval_operand (SND ops) actual = SOME (n2w (p+36))` by
    (conj_tac >> first_x_assum irule >> asm_simp_tac bool_ss []) >>
  `abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id (maxlen+36) p 32 initial actual` by
    (drule_all abi_builtin_encode_setup_frame_compose >> simp[]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `addressed` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_ENCODE_METHOD_SETUP_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin method-ID setup not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinEncodeMethodSetup");
