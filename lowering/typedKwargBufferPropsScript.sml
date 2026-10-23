(* Definition probes for external keyword buffers. No recursive decoder
   correctness theorem is assumed here. *)
Theory typedKwargBufferProps
Ancestors kwargBufferProps localPtrsProps exprLowering emitHelperProps
  context compileEnv valueEncoding venomState words finite_map moduleLowering
  vyperContext vyperValue abiEncoder venomExecSemantics emitHelper
Libs wordsLib

(* The operand must be an SSA pointer: local_ptrs_rel deliberately only
   covers PtrVar (Var p), not arbitrary literal operands. Type resolution is
   through the compiler's actual environment, not a scalar encoding. *)
Definition kwarg_buffer_rel_def:
  kwarg_buffer_rel func cenv p ty v ss <=>
    ?tv w.
      evaluate_type cenv.ce_type_env ty = SOME tv /\
      lookup_var p ss = SOME w /\
      local_backed func p ss (w2n w) (type_memory_bytes cenv ty) /\
      w2n w + type_memory_bytes cenv ty <= ss.vs_alloca_next /\
      w2n w + type_memory_bytes cenv ty < dimword (:256) /\
      type_memory_size tv <= type_memory_bytes cenv ty /\
      val_wf tv v /\ val_in_memory tv v (w2n w) ss.vs_memory
End

Theorem kwarg_buffer_name:
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
  compile_name_vv cenv ty name st =
    (LocatedValue ty (mk_ptr (Var p) LocMemory), st)
Proof
  simp[compile_name_vv_def, comp_return_def]
QED

Theorem kwarg_buffer_read:
  kwarg_buffer_rel func cenv p ty v ss ==>
  ?tv w. evaluate_type cenv.ce_type_env ty = SOME tv /\
    lookup_var p ss = SOME w /\ val_wf tv v /\
    val_in_memory tv v (w2n w) ss.vs_memory
Proof
  simp[kwarg_buffer_rel_def] >> metis_tac[]
QED

(* Registration really uses the same pointer, and does not reinterpret it
   as a numeric static offset. Works equally for scalar, bytes and arrays. *)
Theorem kwarg_buffer_register_read:
  ~MEM name (MAP (\(n,p,t,e). n) rest) ==>
  compile_name_vv
    (compile_register_kwarg_vars cenv ((name,Var p,ty,e)::rest)) ty name st =
    (LocatedValue ty (mk_ptr (Var p) LocMemory), st)
Proof
  strip_tac >> irule kwarg_buffer_name >>
  simp[compile_register_kwarg_vars_head]
QED

Theorem kwarg_buffer_mstore_frame:
  kwarg_buffer_rel func cenv p ty v ss /\
  (!w. lookup_var p ss = SOME w ==>
    off + 32 <= w2n w \/
    w2n w + type_memory_bytes cenv ty <= off) ==>
  kwarg_buffer_rel func cenv p ty v (mstore off x ss)
Proof
  rw[kwarg_buffer_rel_def] >> qexistsl_tac [`tv`,`w`] >>
  `val_in_memory tv v (w2n w) (mstore off x ss).vs_memory` by
    (irule mstore_keeps_val_in_memory >> simp[] >>
     first_x_assum drule >> decide_tac) >>
  gvs[local_backed_def, mstore_def, lookup_var_def] >> metis_tac[]
QED

(* A static two-element array needs two words, not val_to_w256 array = 0. *)
Theorem kwarg_static_pair_layout:
  val_in_memory (ArrayTV tv (Fixed 2))
    (ArrayV (SArrayV [(0,v0);(1,v1)])) addr mem <=>
  val_in_memory tv v0 addr mem /\
  val_in_memory tv v1 (addr + type_memory_size tv) mem
Proof
  simp[val_in_memory_def]
QED

Theorem kwarg_bytes_layout:
  val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) addr mem <=>
  mem_word_at addr mem = n2w (LENGTH bs) /\
  mem_bytes_at (addr + 32) (LENGTH bs) mem = bs
Proof
  simp[val_in_memory_def]
QED

(* Prefix invariant candidate for the counted decoder loop. The loop's
   temporary i_ptr must additionally be separated from the destination. *)
Definition kwarg_array_prefix_def:
  kwarg_array_prefix tv vs addr i mem <=>
    i <= LENGTH vs /\
    elems_in_memory (TAKE i vs) addr tv mem
End

Theorem kwarg_array_prefix_zero:
  kwarg_array_prefix tv vs addr 0 mem
Proof
  simp[kwarg_array_prefix_def, val_in_memory_def]
QED

Theorem kwarg_array_prefix_complete:
  kwarg_array_prefix tv vs addr (LENGTH vs) mem ==>
  elems_in_memory vs addr tv mem
Proof
  simp[kwarg_array_prefix_def]
QED

(* Execute the actual emitted decoder, not an opcode projection. There is
   one positional word before the kwarg head at byte 36. *)
Definition kwarg_word_input_def:
  kwarg_word_input =
    (init_venom_state "entry") with vs_call_ctx :=
      (empty_call_context with cc_calldata :=
        (REPLICATE 36 0w ++ word_to_bytes (7w:bytes32) T))
End

Theorem kwarg_word_decoder_execution:
  ?ss. run_inst_seq
    (SND (compile_abi_decode_to_buf (Lit 128w) (Lit 36w)
      CALLDATALOAD (Lit 0w) (DecPrimWord NoClamp)
      kwarg_probe_state)).cs_current_insts kwarg_word_input = OK ss /\
    val_in_memory (BaseTV (UintT 256)) (IntV 7) 128 ss.vs_memory
Proof
  EVAL_TAC >> simp_tac bool_ss [] >> EVAL_TAC >> simp[]
QED

Definition kwarg_bytes_input_def:
  kwarg_bytes_input =
    (init_venom_state "entry") with vs_call_ctx :=
      (empty_call_context with cc_calldata :=
        (REPLICATE 36 0w ++ word_to_bytes (64w:bytes32) T ++
         word_to_bytes (2w:bytes32) T ++ [42w;43w] ++ REPLICATE 30 0w))
End

Theorem kwarg_bytes_decoder_execution:
  ?ss. run_inst_seq
    (SND (compile_init_kwargs ARB
      [("b",Lit 128w, BaseT (BytesT (Dynamic 10)),
         Literal (BaseT (BytesT (Dynamic 10))) (BytesL []))]
      36 1 (Lit 0w) kwarg_probe_state)).cs_current_insts
    kwarg_bytes_input = OK ss /\
    val_in_memory (BaseTV (BytesT (Dynamic 10)))
      (BytesV [42w;43w]) 128 ss.vs_memory
Proof
  EVAL_TAC >> simp_tac bool_ss [] >> EVAL_TAC >> simp[]
QED

(* Binding supplies the resolved source type; separation is a property of
   the allocation set, not a property of any one descriptor. *)
Theorem kwarg_buffers_local_ptrs:
  (!name entry p sz.
    lookup_scopes name scopes = SOME entry /\
    FLOOKUP registered.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    ?ty. kwarg_buffer_rel func original p ty entry.value ss /\
      evaluate_type original.ce_type_env ty = SOME entry.type /\
      sz = type_memory_bytes original ty) /\
  (!n1 n2 b1 sz1 b2 sz2.
    n1 <> n2 /\ local_region registered scopes ss n1 b1 sz1 /\
    local_region registered scopes ss n2 b2 sz2 ==>
    regions_disjoint b1 sz1 b2 sz2) ==>
  local_ptrs_rel func registered scopes ss
Proof
  rw[local_ptrs_rel_def] >>
  first_x_assum drule_all >>
  simp[kwarg_buffer_rel_def] >> strip_tac >> gvs[] >>
  qexists_tac `w` >> simp[arithmeticTheory.ADD_COMM]
QED

(* Regression for the former zero-bound diagnostic: the compile-time
   sentinel now omits checks, as pinned Python's NONE branch does. *)
Definition kwarg_dyn_pointer_input_def:
  kwarg_dyn_pointer_input =
    (init_venom_state "entry") with vs_call_ctx :=
      (empty_call_context with cc_calldata :=
        (REPLICATE 100 0w ++ word_to_bytes (32w:bytes32) T))
End

Theorem kwarg_dyn_pointer_zero_bound_probe:
  (case run_inst_seq
    (SND (compile_abi_decode_dyn_elem_ptr CALLDATALOAD (Lit 100w)
      (Lit 100w) (Lit 0w) 32 kwarg_probe_state)).cs_current_insts
    kwarg_dyn_pointer_input of
      OK ss => eval_operand
        (FST (compile_abi_decode_dyn_elem_ptr CALLDATALOAD (Lit 100w)
          (Lit 100w) (Lit 0w) 32 kwarg_probe_state)) ss = SOME 132w
    | _ => F)
Proof
  EVAL_TAC
QED

(* Local straight-line regressions: absence is syntactic, never a test of
   the runtime value of a variable bound. *)
Definition dyn_pointer_probe_code_def:
  dyn_pointer_probe_code opc base hi =
    compile_abi_decode_dyn_elem_ptr opc (Lit 100w) base hi 32 kwarg_probe_state
End

Theorem dyn_pointer_unbounded_shape:
  MAP (\i. i.inst_opcode)
    (SND (dyn_pointer_probe_code CALLDATALOAD (Lit 100w) (Lit 0w))).cs_current_insts =
  [CALLDATALOAD; ADD]
Proof
  EVAL_TAC
QED

Theorem dyn_pointer_bounded_shape:
  MAP (\i. i.inst_opcode)
    (SND (dyn_pointer_probe_code CALLDATALOAD (Lit 100w) (Var "hi"))).cs_current_insts =
  [CALLDATALOAD; ADD; LT; ISZERO; ASSERT; ADD; GT; ISZERO; ASSERT]
Proof
  EVAL_TAC
QED

Theorem dyn_pointer_bounded_success:
  case run_inst_seq
    (SND (dyn_pointer_probe_code CALLDATALOAD (Lit 100w) (Lit 164w))).cs_current_insts
    kwarg_dyn_pointer_input of
      OK ss => eval_operand
        (FST (dyn_pointer_probe_code CALLDATALOAD (Lit 100w) (Lit 164w))) ss = SOME 132w
    | _ => F
Proof
  EVAL_TAC
QED

Theorem dyn_pointer_bounded_end_reject:
  case run_inst_seq
    (SND (dyn_pointer_probe_code CALLDATALOAD (Lit 100w) (Lit 163w))).cs_current_insts
    kwarg_dyn_pointer_input of
      Abort Revert_abort ss => T | _ => F
Proof
  EVAL_TAC
QED

Theorem dyn_pointer_variable_zero_reject:
  case run_inst_seq
    (SND (dyn_pointer_probe_code CALLDATALOAD (Lit 100w) (Var "hi"))).cs_current_insts
    (update_var "hi" 0w kwarg_dyn_pointer_input) of
      Abort Revert_abort ss => T | _ => F
Proof
  EVAL_TAC
QED

Definition dyn_pointer_wrap_input_def:
  dyn_pointer_wrap_input =
    (init_venom_state "entry") with vs_call_ctx :=
      (empty_call_context with cc_calldata :=
        (REPLICATE 100 0w ++ word_to_bytes (-1w:bytes32) T))
End

Theorem dyn_pointer_bounded_wrap_reject:
  case run_inst_seq
    (SND (dyn_pointer_probe_code CALLDATALOAD (Lit 1w) (Lit 164w))).cs_current_insts
    dyn_pointer_wrap_input of
      Abort Revert_abort ss => T | _ => F
Proof
  EVAL_TAC
QED

Theorem dyn_pointer_unbounded_wrap_success:
  case run_inst_seq
    (SND (dyn_pointer_probe_code CALLDATALOAD (Lit 1w) (Lit 0w))).cs_current_insts
    dyn_pointer_wrap_input of
      OK ss => eval_operand
        (FST (dyn_pointer_probe_code CALLDATALOAD (Lit 1w) (Lit 0w))) ss = SOME 0w
    | _ => F
Proof
  EVAL_TAC
QED

val _ = List.app (fn (name, th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))
     andalso null (#2 (Tag.dest_tag (Thm.tag th))) then ()
  else raise Fail ("unexpected oracle in typedKwargBufferProps: " ^ name))
  (DB.thms "typedKwargBufferProps");
