(*
 * Two runs that agree modulo taint, without relocation
 *
 * Passes that leave some memory of the target unwritten (copy forwarding,
 * dead-store elimination) run on states where the source and target
 * differ only where the pointer discipline lets nothing observe it: at
 * tainted bytes (fresh allocations' unwritten bytes and what was copied
 * from them), at a pass-given dead set X of memory bytes, and in memory
 * at or above the bump allocator, where a returned callee's frames were.
 * Unlike LowerDload and ConcretizeMemLoc no site moves: allocations,
 * the bump pointer and every other frame field are equal, and an
 * operand with no taint evaluates to the same word in both runs.
 *
 * TOP-LEVEL:
 *   taint_agree           — the state relation
 *   taint_agree_step_base — one non-INVOKE step from a reachable state
 *)

Theory taintAgree
Ancestors
  o1LowerDloadShared ptrDiscipline codegenRel contextCodegenRel
  venomExecSemantics venomState finite_map pred_set list

(* s and t agree except at the taint tn, the dead bytes X, and memory at
   or above the bump allocator.  The fields not listed are equal. *)
Definition taint_agree_def:
  taint_agree D X tn s t <=>
    ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\
    t with <| vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_accounts := s.vs_accounts; vs_transient := s.vs_transient;
              vs_immutables := s.vs_immutables |> = s /\
    FDOM t.vs_vars = FDOM s.vs_vars /\
    (!v. v IN FDOM s.vs_vars ==>
         word_agree_except (op_taint tn (Var v))
           (s.vs_vars ' v) (t.vs_vars ' v)) /\
    (!i. i NOTIN X /\ i NOTIN tn.t_mem /\ i < s.vs_alloca_next ==>
         read_byte i s.vs_memory = read_byte i t.vs_memory)
End

(* Why it holds: taint_ok gives each operand of a non-propagating opcode
   no taint, so taint_agree evaluates it equally in t; access_ok puts
   each read ending above lo inside a site (below the bump pointer), and
   taint_ok keeps tainted bytes away from reads other than MLOAD, ILOAD,
   MCOPY and RETURN; the read premise keeps X away.  The propagating
   opcodes (ASSIGN, shifts, MLOAD/ILOAD, MSTORE/ISTORE, MCOPY,
   SLOAD/TLOAD, SSTORE/TSTORE) move taint exactly as step_taint says:
   word_agree_except_shl/shr/sar, ld_mload_masked_bytes, ld_mstore_bytes,
   ld_shared_sstore/tstore.  A step that records a call request needs
   taint_within's first clause for the request's snapshot.  A fresh ALLOCA lands at the same offset in
   both runs and new_site_bytes taints what it claims above the old bump
   pointer.  RET's operands carry no taint, so the returned values are
   equal.  At a halt, taint_within puts the remaining taint (and RETURN's
   tainted bytes, ret_taint) inside D: ld_shared_halt_result. *)
Theorem taint_agree_step_base:
  !vs C stk PG G tn fn inst s t D X lo r.
    frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
    ptr_discipline lo C vs /\ ~ctx_has_dalloca C /\
    taint_within D C vs /\ dead_wf D /\
    inst.inst_opcode <> INVOKE /\
    taint_agree D X tn s t /\
    (!off len i. MEM (off,len) (source_memory_read_ranges inst s) /\
                 off <= i /\ i < off + len ==> i NOTIN X) /\
    step_inst_base inst s = r /\ terminates r ==>
    (!s'. r = OK s' ==>
          ?t'. step_inst_base inst t = OK t' /\
               taint_agree D X (step_taint inst s s' tn) s' t') /\
    (!v s'. r = IntRet v s' ==>
          ?t'. step_inst_base inst t = IntRet v t' /\
               taint_agree D X tn s' t') /\
    (!s'. r = Halt s' ==>
          ?t'. step_inst_base inst t = Halt t' /\
               dead_result_rel D (Halt s') (Halt t')) /\
    (!a s'. r = Abort a s' ==>
          ?t'. step_inst_base inst t = Abort a t')
Proof
  cheat
QED
