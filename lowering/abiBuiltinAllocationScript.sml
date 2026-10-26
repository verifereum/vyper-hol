(* Output allocation for ABI builtins, with fresh and reused instruction sites.
   TOP-LEVEL: abi_builtin_alloc_buffer.
   Helper: the buffer action emits exactly its ALLOCA instruction. *)
Theory abiBuiltinAllocation
Ancestors
  abiDecoderReentryAllocation abiDecoderReentry abiDecoderContract
  context compileEnv emitHelper emitHelperProps exprLoweringProps
  venomExecSemantics venomState venomInst finite_map words arithmetic list

Theorem abi_builtin_alloc_buffer_shape:
  compile_alloc_buffer outsz st = (buf,st') ==>
  buf.buf_size = outsz /\ emit_op ALLOCA [Lit (n2w outsz)] st = (buf.buf_operand,st')
Proof
  simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[]
QED

Theorem abi_builtin_alloc_buffer:
  compile_alloc_buffer outsz st = (buf,st') /\
  ((FLOOKUP s.vs_allocas st.cs_next_id = NONE /\ p = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\ st'.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand buf.buf_operand t = SOME (n2w p) /\ buf.buf_size = outsz /\
    fresh_vars_wrt limit_st t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==> eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_halted = s.vs_halted /\
    t.vs_allocas = (if FLOOKUP s.vs_allocas st.cs_next_id = NONE then
      s.vs_allocas |+ (st.cs_next_id,(p,outsz)) else s.vs_allocas) /\
    t.vs_alloca_next = (if FLOOKUP s.vs_allocas st.cs_next_id = NONE then
      s.vs_alloca_next + outsz else s.vs_alloca_next) /\ inst_extends st st'
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule inst_extends_emit_op >> strip_tac >>
  qabbrev_tac `allocated = if FLOOKUP s.vs_allocas st.cs_next_id = NONE then
    s with <|vs_allocas := s.vs_allocas |+ (st.cs_next_id,(s.vs_alloca_next,outsz));
      vs_alloca_next := s.vs_alloca_next + outsz|> else s` >>
  qabbrev_tac `t = update_var (STRING #"%" (toString st.cs_next_var)) (n2w p) allocated` >>
  `step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit (n2w outsz)]
    [STRING #"%" (toString st.cs_next_var)]) s = OK t` by
    (gvs[Abbr`t`, Abbr`allocated`] >>
     asm_simp_tac (srw_ss()) [Once step_inst_base_def, exec_alloca_def,
       mk_inst_def, w2n_n2w, eval_operand_def, LET_THM, ADD_COMM]) >>
  `t.vs_vars = s.vs_vars |+ (STRING #"%" (toString st.cs_next_var),n2w p) /\
   t.vs_labels = s.vs_labels` by
    (Cases_on `FLOOKUP s.vs_allocas st.cs_next_id = NONE` >>
     simp[Abbr`t`, Abbr`allocated`, update_var_def]) >>
  `st.cs_next_var < limit_st.cs_next_var` by decide_tac >>
  drule_all abi_decoder_register_update >> strip_tac >>
  `run_inst_seq (emitted_insts st st') s = OK t` by
    asm_simp_tac (srw_ss()) [run_inst_seq_def] >>
  qexists_tac `t` >>
  gvs[Abbr`t`, Abbr`allocated`, update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_ALLOCATION_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin allocation not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinAllocation");
