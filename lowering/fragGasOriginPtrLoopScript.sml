(* Zero-mark joint gas-origin pointer paths across control flow: a plain
   JMP edge, and a well-founded loop that reaches its exit through
   zero-mark iterations.  Straight-line runs use
   run_inst_seq_gas_origin_ptr_path; paths chain by
   gas_origin_ptr_path_append. *)
Theory fragGasOriginPtrLoop
Ancestors
  fragGasOriginPtr fragGasSeqPtr fragGasOrigin fragGasPathPtr ptrSafeRun
  ptrDiscipline venomExecSemantics venomInst venomState relation list

(* A JMP keeps the ghost and lands on the jump target, as in
   emit_jump_path_ptr. *)
Theorem jmp_origin_ptr_path:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst iid JMP [Label lbl] []) /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s ==>
  gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s, G, tn) []
    (OK (jump_to lbl s), G, tn)
Proof
  cheat
QED

(* A loop whose every non-exit state P reaches a smaller P state by a
   zero-mark path reaches an exit state Q by a zero-mark path. *)
Theorem gas_origin_ptr_path_loop:
  !R P Q.
    WF R /\
    (!s G tn. P (s, G, tn) ==> ~s.vs_halted) /\
    (!s G tn. P (s, G, tn) /\ ~Q (s, G, tn) ==>
       ?s' G' tn'. P (s', G', tn') /\ R (s', G', tn') (s, G, tn) /\
         gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s, G, tn) []
           (OK s', G', tn')) ==>
    !s G tn. P (s, G, tn) ==>
      ?s' G' tn'. P (s', G', tn') /\ Q (s', G', tn') /\
        gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s, G, tn) []
          (OK s', G', tn')
Proof
  cheat
QED
