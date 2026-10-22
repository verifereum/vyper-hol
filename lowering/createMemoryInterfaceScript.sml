Theory createMemoryInterface
Ancestors
  createSourceCallback context contextProps emitHelperProps venomMemProps vyperABIValid
  valueEncoding vyperTyping vyperABI contractABI vyperValueOperation
  list rich_list words venomExecSemantics
Libs
  wordsLib

(* Checked preparation boundaries. These do not assert a simulation theorem
   for arbitrary operand callbacks or for the recursive ABI compiler.

   C2.5 interface audit (remaining proof dependencies, not assumptions):
   - Memory snapshots: dynamic MCOPY is covered below, with exact saved bytes
     and a disjoint-write frame. Preservation across arbitrary expression
     callbacks still requires proving create_source_callback_spec for the
     actual compiler; state_rel alone has no private-region frame.
   - Storage/transient snapshots: compile_slot_to_memory delegates to
     compile_word_copy_loop (LocStorage/LocTransient -> LocMemory). That
     helper introduces cond/body/exit blocks and an ASSIGN counter. Existing
     blocks_grow/ci_mono lemmas prove emission structure, not execution.
     Need a frag_exec loop invariant relating loaded slots to typed byte-array
     length/data layout, with nonwrapping slot and byte offsets.
   - Constructor tuple: compile_extcall_store_values uses unwrap_value,
     MSTORE/compile_store_bytestring/MCOPY. No execution boundary establishes
     tuple_in_memory from located values. It needs element-layout agreement,
     fresh nonoverlapping destinations, and a frame for saved bytecode.
   - ABI: compile_abi_encode_to_buf_correct in abiEncoderProps is explicitly
     restricted to single_block_enc_info, and eight Resume branches use
     admissions. It cannot justify even all fixed tuple cases kernel-closed,
     or general dynamic constructor encoding/CFG execution. A new proven
     recursive boundary must use type_to_abi_enc_info plus
     sfields_tenv_consistent, val_in_memory, value_has_type, has_type,
     vyper_to_abi and evaluate_type, and include output bytes/length and frame.
     Source encoding rejection must be matched, not assumed away.
   - Bounds: create_ctor_encoding_bound supplies semantic encoded length,
     not equality with the compiler's chosen abi_size. Allocator alloca_inv
     only bounds allocations by the natural bump pointer, not by 2**256;
     source typing alone does not supply that bound. Need a bridge from
     compiler environment/type metadata and reachable allocator state to
     capacity and nonwrapping bounds. The checked wrap probe below shows
     why omitting this bridge is unsound.
*)
Theorem compile_create_copy_dynamic_execution:
  compile_copy_memory_dynamic dst src len cs = ((),cs') /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME p /\
  eval_operand len s = SOME n /\ fresh_vars_wrt cs s ==>
  ?s'. run_inst_seq (emitted_insts cs cs') s = OK s' /\
    s' = mcopy (w2n d) (w2n p) (w2n n) s /\
    same_blocks cs cs' /\ fresh_vars_wrt cs' s' /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op s' = SOME w)
Proof
  simp[compile_copy_memory_dynamic_def] >> rpt strip_tac >>
  drule_all emit_void_MCOPY_correct >> simp[]
QED

Theorem create_copy_snapshot:
  TAKE n (DROP src s.vs_memory) = bs /\ LENGTH bs = n ==>
  create_memory_snapshot [(dst,bs)] (mcopy dst src n s)
Proof
  strip_tac >>
  `TAKE n (DROP src s.vs_memory ++ REPLICATE n 0w) = bs` by
    (`n <= LENGTH (DROP src s.vs_memory)` by
       (qpat_x_assum `TAKE _ _ = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
        simp[LENGTH_TAKE_EQ] >> decide_tac) >>
     fs[LENGTH_DROP] >> simp[TAKE_APPEND]) >>
  simp[create_memory_snapshot_def, mcopy_def] >>
  metis_tac[write_memory_with_expansion_read_self]
QED

Theorem create_snapshot_disjoint_write:
  create_memory_snapshot regions s /\
  EVERY (\(off,bs). off + LENGTH bs <= LENGTH s.vs_memory /\
           (off + LENGTH bs <= dst \/ dst + LENGTH data <= off)) regions ==>
  create_memory_snapshot regions (write_memory_with_expansion dst data s)
Proof
  simp[create_memory_snapshot_def, EVERY_MEM] >> rpt strip_tac >>
  PairCases_on `e` >> gvs[] >>
  first_x_assum (qspec_then `(e0,e1)` mp_tac) >> simp[] >> strip_tac >>
  first_x_assum (qspec_then `(e0,e1)` mp_tac) >> simp[] >> strip_tac >>
  metis_tac[write_memory_with_expansion_disjoint_read]
QED

Theorem create_bytecode_layout_bound:
  value_has_type (BaseTV (BytesT (Dynamic maxlen))) (BytesV bs) /\
  val_in_memory (BaseTV (BytesT (Dynamic maxlen))) (BytesV bs) off mem ==>
  LENGTH bs <= maxlen /\ mem_word_at off mem = n2w (LENGTH bs) /\
  mem_bytes_at (off + 32) (LENGTH bs) mem = bs
Proof
  simp[value_has_type_def, val_in_memory_def]
QED

(* Allocation size is a natural number until converted to a word. The strict
   bound is necessary: alloca non-overlap alone does not prevent word wrap. *)
Theorem create_append_nonwrapping:
  start + capacity < 2 ** 256 /\ n <= capacity ==>
  w2n ((n2w start : bytes32) + n2w n) = start + n /\
  start + n <= start + capacity
Proof
  strip_tac >> simp[word_add_n2w, w2n_n2w] >>
  `start + n < 2 ** 256` by decide_tac >> fs[arithmeticTheory.ADD_COMM]
QED

Theorem create_ctor_encoding_bound:
  vyper_to_abi tenv ty v = SOME av /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v ==>
  LENGTH (enc (vyper_to_abi_type tenv ty) av) <= vyper_abi_size_bound tenv ty
Proof
  metis_tac[cj 1 vyper_to_abi_enc_le_size_bound]
QED

(* Representative constructor tuples exercise both the static and dynamic
   size bounds without pretending the encoder implementation is verified. *)
Theorem create_fixed_ctor_preparation_probe:
  vyper_to_abi FEMPTY (TupleT [BaseT (UintT 256); BaseT BoolT])
    (ArrayV (TupleV [IntV 7; BoolV T])) =
      SOME (ListV [NumV 7; NumV 1]) /\
  vyper_abi_size_bound FEMPTY
    (TupleT [BaseT (UintT 256); BaseT BoolT]) = 64
Proof
  EVAL_TAC
QED

Theorem create_dynamic_ctor_preparation_probe:
  vyper_to_abi FEMPTY (TupleT [BaseT (BytesT (Dynamic 40))])
    (ArrayV (TupleV [BytesV [1w;2w;3w]])) =
      SOME (ListV [contractABI$BytesV [1w;2w;3w]]) /\
  LENGTH (enc (Tuple [Bytes NONE])
    (ListV [contractABI$BytesV [1w;2w;3w]])) = 96 /\
  vyper_abi_size_bound FEMPTY
    (TupleT [BaseT (BytesT (Dynamic 40))]) = 128
Proof
  EVAL_TAC
QED

Theorem create_pointer_wrap_probe:
  w2n ((n2w (2 ** 256 - 16) : bytes32) + 32w) = 16
Proof
  EVAL_TAC
QED

val _ = app (fn (name, th) =>
  if null (List.filter (fn s => s <> "DISK_THM")
             (#1 (Tag.dest_tag (Thm.tag th)))) then ()
  else raise Fail ("Oracle dependency in " ^ name))
  (DB.thms "createMemoryInterface");
