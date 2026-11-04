Theory abiBuiltinAllocation
Ancestors
  abiDecoderReentryAddress abiDecoderReentry abiDecoderContract context compileEnv emitHelper
  emitHelperProps exprLoweringProps venomExecSemantics venomState venomInst finite_map words
  arithmetic list abiBuiltinPrefix abiDecoderDynamicLoopSetup abiDecoderAllocation
  abiDecoderArrayInitExec abiDecoderFrame

(* ===== Builtin Allocation ===== *)

(* Output allocation for ABI builtins, with fresh and reused instruction sites.
   TOP-LEVEL: abi_builtin_alloc_buffer.
   Helper: the buffer action emits exactly its ALLOCA instruction. *)

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

(* ===== State ===== *)

(* Pure allocator metadata used to state incoming builtin resource bounds.
   TOP-LEVEL: abi_builtin_allocate_state and abi_builtin_allocation_frame. *)

Definition abi_builtin_allocate_state_def:
  abi_builtin_allocate_state site outsz s =
    if FLOOKUP s.vs_allocas site = NONE then
      s with <|vs_allocas := s.vs_allocas |+ (site,(s.vs_alloca_next,outsz));
        vs_alloca_next := s.vs_alloca_next + outsz|>
    else s
End

Definition abi_builtin_allocation_frame_def:
  abi_builtin_allocation_frame next site outsz s t <=>
    (!op w. abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_halted = s.vs_halted /\
    t.vs_allocas = (abi_builtin_allocate_state site outsz s).vs_allocas /\
    t.vs_alloca_next = (abi_builtin_allocate_state site outsz s).vs_alloca_next
End

Theorem abi_builtin_allocate_state_transport:
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next ==>
  (abi_builtin_allocate_state site outsz t).vs_allocas =
    (abi_builtin_allocate_state site outsz s).vs_allocas /\
  (abi_builtin_allocate_state site outsz t).vs_alloca_next =
    (abi_builtin_allocate_state site outsz s).vs_alloca_next
Proof
  strip_tac >> simp_tac bool_ss [abi_builtin_allocate_state_def] >>
  Cases_on `FLOOKUP s.vs_allocas site = NONE` >> asm_simp_tac (srw_ss()) []
QED

Theorem abi_builtin_alloc_buffer_frame:
  compile_alloc_buffer outsz st = (buf,st') /\
  ((FLOOKUP s.vs_allocas st.cs_next_id = NONE /\ p = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\ st'.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand buf.buf_operand t = SOME (n2w p) /\ fresh_vars_wrt limit_st t /\
    abi_builtin_allocation_frame st.cs_next_var st.cs_next_id outsz s t /\ inst_extends st st'
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_builtin_alloc_buffer >> strip_tac >>
  qexists_tac `t` >> asm_simp_tac bool_ss [] >>
  gvs[abi_builtin_allocation_frame_def, abi_builtin_allocate_state_def]
QED

Theorem abi_builtin_allocation_frame_budget:
  abi_builtin_allocation_frame next site outsz s t ==>
  (abi_decoder_budget first last b cap t <=>
    abi_decoder_budget first last b cap (abi_builtin_allocate_state site outsz s))
Proof
  simp_tac bool_ss [abi_builtin_allocation_frame_def] >> strip_tac >>
  irule abi_decoder_budget_transport >> asm_simp_tac bool_ss []
QED

Theorem abi_builtin_allocation_frame_outside:
  abi_builtin_allocation_frame next site outsz s t /\ id <> site ==>
  FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id
Proof
  simp_tac bool_ss [abi_builtin_allocation_frame_def] >> strip_tac >>
  Cases_on `FLOOKUP s.vs_allocas site = NONE` >>
  gvs[abi_builtin_allocate_state_def, FLOOKUP_UPDATE]
QED

Theorem abi_builtin_allocation_frame_footprint:
  abi_builtin_allocation_frame next site outsz s t ==>
  abi_decode_footprint_frame ranges s t
Proof
  simp[abi_builtin_allocation_frame_def, abi_decode_footprint_frame_def]
QED
