(* Pure allocator metadata used to state incoming builtin resource bounds.
   TOP-LEVEL: abi_builtin_allocate_state and abi_builtin_allocation_frame. *)
Theory abiBuiltinAllocationState
Ancestors
  abiBuiltinAllocation abiBuiltinPrefix abiDecoderReentry abiDecoderDynamicLoopSetup
  abiDecoderAllocation abiDecoderArrayInitExec abiDecoderFrame abiDecoderContract
  compileEnv venomState finite_map words list

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

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_ALLOCATION_STATE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin allocation state not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinAllocationState");
