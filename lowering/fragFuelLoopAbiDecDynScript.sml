(*
 * Fuel bound for the dynamic-array ABI decode loop.
 *
 * TOP-LEVEL:
 *   fuel_okS_compile_abi_decode_dyn_loop
 *)

Theory fragFuelLoopAbiDecDyn
Ancestors
  fragFuel fragFuelContextBase abiEncoder compileEnv emitHelper context
  venomInst venomMemProps venomInstProps venomExecSemantics venomEffects venomState
Libs
  fragFuelLib

(* A successful one-input header instruction preserves byte memory.
   Memory-writing non-call opcodes have incompatible arity; DLOAD is a
   conservative effect annotation but its semantics is a read. *)
Theorem abi_dyn_single_input_memory[local]:
  !fuel ctx opc id op out s t.
    ~is_terminator opc /\ opc <> PHI /\ opc <> INVOKE /\
    step_inst fuel ctx (mk_inst id opc [op] [out]) s = OK t ==>
    t.vs_memory = s.vs_memory
Proof
  rpt strip_tac >>
  Cases_on `is_alloca_op opc`
  >- (irule step_inst_alloca_preserves_memory >>
      qexistsl_tac [`ctx`, `fuel`, `mk_inst id opc [op] [out]`] >>
      simp[mk_inst_def]) >>
  Cases_on `Eff_MEMORY IN write_effects opc`
  >- (Cases_on `opc` >>
      gvs[write_effects_def, empty_effects_def, all_effects_def,
          is_terminator_def] >>
      gvs[step_inst_non_invoke, mk_inst_def] >>
      gvs[step_inst_base_opcode_eqs, exec_write2_def, exec_read1_def,
          AllCaseEqs(), update_var_def]) >>
  irule write_effects_sound_memory >>
  qexistsl_tac [`ctx`, `fuel`, `mk_inst id opc [op] [out]`] >>
  simp[mk_inst_def]
QED

(* Straight-line segment boundaries.  The exit sets name the loop's
   control-flow edges; no composition across the back edge is used here. *)
Theorem fuel_ok_decode_dyn_header[local]:
  !load_opc i_ptr base_op src_op exit_lbl body_lbl Wv E.
    ~is_terminator load_opc /\ load_opc <> PHI /\
    exit_lbl IN E /\ body_lbl IN E ==>
    fuel_ok Wv {} E
      (do i_op <- emit_op MLOAD [i_ptr];
          src_addr <- compile_abi_dec_addr base_op src_op;
          cnt_hdr <- emit_op load_opc [src_addr];
          cmp <- emit_op LT [i_op; cnt_hdr];
          done_op <- emit_op ISZERO [cmp];
          emit_inst JNZ [done_op; Label exit_lbl; Label body_lbl] []
       od)
Proof
  rpt strip_tac >>
  simp_tac std_ss [compile_abi_dec_addr_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_inst_jnz] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_decode_dyn_body[local]:
  !dst src_op load_opc base_op hi_op elem_info elem_abi_sz elem_mem_sz
     i_ptr hdr_lbl Wv E.
    ~is_terminator load_opc /\ load_opc <> PHI /\ hdr_lbl IN E /\
    (!d s Wv E. fuel_ok Wv {} E
       (compile_abi_decode_to_buf d s load_opc base_op hi_op elem_info)) ==>
    fuel_ok Wv {} E
      (do i_op2 <- emit_op MLOAD [i_ptr];
          src_data <- emit_op ADD [src_op; Lit 32w];
          src_off <- emit_op MUL [i_op2; Lit (n2w elem_abi_sz)];
          elem_src <- emit_op ADD [src_data; src_off];
          actual_src <-
            (if dec_info_needs_offset elem_info then
               compile_abi_decode_dyn_elem_ptr load_opc base_op elem_src
                 src_data hi_op elem_abi_sz
             else return elem_src);
          dst_data <- emit_op ADD [dst; Lit 32w];
          dst_off <- emit_op MUL [i_op2; Lit (n2w elem_mem_sz)];
          elem_dst <- emit_op ADD [dst_data; dst_off];
          compile_abi_decode_to_buf elem_dst actual_src
            load_opc base_op hi_op elem_info;
          new_i <- emit_op ADD [i_op2; Lit 1w];
          emit_void MSTORE [i_ptr; new_i];
          emit_inst JMP [Label hdr_lbl] []
       od)
Proof
  rpt strip_tac >>
  simp_tac std_ss [compile_abi_decode_dyn_elem_ptr_def,
    compile_abi_dec_addr_def, compile_abi_decode_range_check_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void, fuel_ok_emit_inst_jmp] >>
  simp[is_terminator_def]
QED

(* The counter need not be disjoint from the element destination.  The
   final MSTORE overwrites any writes by the element decoder.  The bound
   is reloaded at every header and need not stay fixed. *)
Theorem fuel_okS_compile_abi_decode_dyn_loop:
  !dst src_op load_opc base_op hi_op elem_info elem_abi_sz elem_mem_sz i_ptr cnt.
    ~is_terminator load_opc /\ load_opc <> PHI /\ load_opc <> INVOKE /\
    (!d s Wv E.
       fuel_ok Wv {} E
         (compile_abi_decode_to_buf d s load_opc base_op hi_op elem_info)) ==>
    !Wv E.
      fuel_okS (\st. !x. i_ptr = Var x ==> var_below st.cs_next_var x)
        Wv {} E
        (compile_abi_decode_dyn_loop dst src_op load_opc base_op hi_op
           elem_info elem_abi_sz elem_mem_sz i_ptr cnt)
Proof
  cheat
QED
