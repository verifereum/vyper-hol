(* Reach the actual recursive decoder entry after all builtin setup actions. *)
Theory abiBuiltinSetupReach
Ancestors
  abiBuiltinSetupExecute abiBuiltinDecodeSetup abiBuiltinAllocationState
  abiDecoderReentry abiDecoderContract abiDecoderLoop fragExec instIdxIndep
  compileEnv emitHelperProps venomExecSemantics venomState venomInst finite_map words list

Theorem abi_builtin_decode_setup_from_state:
  abi_builtin_decode_setup data min_size max_size outsz st = (ops,ready) /\
  eval_operand data initial = SOME p /\ mload (w2n p) initial = n2w cnt /\
  min_size <= cnt /\ cnt <= max_size /\ max_size < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var data /\
  ((FLOOKUP initial.vs_allocas (abi_builtin_decode_output_site st min_size max_size) = NONE /\
      d = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas (abi_builtin_decode_output_site st min_size max_size) = SOME (d,outsz)) /\
  outsz < dimword (:256) /\ ready.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st ready (\s. s = initial)
    (\t. eval_operand (FST ops) t = SOME (n2w d) /\
      eval_operand (FST (SND ops)) t = SOME (p + 32w) /\
      eval_operand (SND (SND ops)) t = SOME (p + 32w + n2w cnt) /\
      fresh_vars_wrt limit_st t /\
      abi_builtin_allocation_frame st.cs_next_var
        (abi_builtin_decode_output_site st min_size max_size) outsz initial t) (K F)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_decode_setup_shape >> strip_tac >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_builtin_decode_setup_execute >> strip_tac >>
  rename1 `abi_builtin_allocation_frame _ _ _ initial actual` >>
  qexists_tac `actual` >>
  gvs[abi_builtin_allocation_frame_def, fresh_vars_wrt_def, eval_op_inst_idx]
QED

Theorem abi_builtin_decode_setup_reach:
  abi_builtin_decode_setup data min_size max_size outsz st = (ops,ready) /\ fn_has_code st ready func /\
  eval_operand data initial = SOME p /\ mload (w2n p) initial = n2w cnt /\
  min_size <= cnt /\ cnt <= max_size /\ max_size < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var data /\
  ((FLOOKUP initial.vs_allocas (abi_builtin_decode_output_site st min_size max_size) = NONE /\
      d = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas (abi_builtin_decode_output_site st min_size max_size) = SOME (d,outsz)) /\
  outsz < dimword (:256) /\ ready.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. eval_operand (FST ops) t = SOME (n2w d) /\
    eval_operand (FST (SND ops)) t = SOME (p + 32w) /\
    eval_operand (SND (SND ops)) t = SOME (p + 32w + n2w cnt) /\ fresh_vars_wrt limit_st t /\
    abi_builtin_allocation_frame st.cs_next_var
      (abi_builtin_decode_output_site st min_size max_size) outsz initial t /\
    t.vs_current_bb = ready.cs_current_bb /\ t.vs_inst_idx = LENGTH ready.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_builtin_decode_setup_from_state >> disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `~actual.vs_halted` by fs[abi_builtin_allocation_frame_def] >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_SETUP_REACH_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin setup reach not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinSetupReach");
