(* Finite interface audit only: MLOAD deliberately does not recover memory
   pointer provenance. These facts do not refute the frozen body judgment. *)
Theory bodyPtrStructLitReturnAudit
Ancestors bodyPtrStructLitReturnCertificate ptrSafeRun finite_map
  ptrDiscipline venomInst venomState bodyPtrStructLitCalleeFixture codegenRel memLocDefs
  valueEncoding
Libs wordsLib intLib

Theorem structlit_return_loaded_pointer_no_provenance:
  !PG G s.
    FLOOKUP (step_prov PG G
      (EL 14 (SND (structlit_callee_return_compiled F)).cs_current_insts) s)
      "%10" = NONE
Proof
  rpt gen_tac >> rewrite_tac[structlit_return_instructions] >>
  simp[step_prov_def, out_prov_def, set_prov_def, mk_inst_def,
       FLOOKUP_DRESTRICT]
QED

Theorem structlit_return_suffix_operands:
  eval_operand (Lit 32w) (structlit_return_state 13) = SOME 32w /\
  eval_operand (Lit 0w) (structlit_return_state 14) = SOME 0w /\
  eval_operand (Var "%9") (structlit_return_state 16) = SOME 1w /\
  eval_operand (Var "%10") (structlit_return_state 15) = SOME 64w /\
  eval_operand (Var "%0") (structlit_return_state 15) = SOME 224w
Proof
  rewrite_tac[structlit_return_state_def, structlit_return_instructions] >>
  EVAL_TAC
QED

(* Audit design report (not a complete callee certificate).

   Ghost sequence: G_(n+1) = step_prov PG G_n inst_n state_(n+1),
   tn_(n+1) = step_taint inst_n state_n state_(n+1) tn_n.
   inst_seq_ptr checks ptr_inst_ok D lo 0 ctx fn G_n tn_n inst_n state_n;
   actual counted expression paths use lo=0. It stops at RET's IntRet,
   retaining the pre-RET ghost, rather than treating RET as an OK step.

   Memory obligations (outside in_revert_forward fn state_n):
   n=2: ptr_covers G_2 tn_2 "%1" state_2 32, literal value clean.
   n=4: read [384,416) through %1 with that site's provenance.
   n=8: dst %2 covers [224,256), src %1 covers [384,416),
        op_taint tn_8 (Var "%6") = {}. Empty length gives count32.
   n=10: %7 covers [416,448), literal value clean.
   n=12: dst %8 covers [320,384), src %7 covers [416,480).
   n=13: literal-address MLOAD [32,64), no variable provenance possible.
   n=14: literal-address MLOAD [0,32), no variable provenance possible.
   n=15: dst %10 covers [64,224), src %0 covers [224,384).
   ptr_inst_ok_mstore and ptr_inst_ok_mcopy_operand provide precisely
   these ptr_covers premises (plus ~ctx_has_dalloca ctx); ptr_inst_ok_alloca
   handles n=0,1,9 at lo=0 without initial provenance premises.

   Critical fixed-frame mismatch, not a target counterexample:
   access_ok at literal loads13/14 requires 64<=lo and 32<=lo,
   respectively, unless in_revert_forward holds. No initial G repairs a
   literal address above lo. Moreover theorem above proves MLOAD14 kills
   %10 provenance for *every* PG/G/s. Therefore outside revert forwarding,
   MCOPY15 requires 224<=lo even if its loaded pointer is numerically64.
   Initial provenance alone cannot prove this concrete whole-return trace
   at lo=0. An audit of legitimate frame/call invariants is essential;
   don't silently select lo=224 for the actual expression judgment.

   Scalar checks still needed: ADD3/5/7/11 and AND6 require all operands
   untainted; MLOAD4 must give an untainted length before ADD5. The initial
   memory words[0,64) must be clean so that MLOAD13/14 produce clean %9/%10;
   the arbitrary-tn clean-header certificate does NOT ensure this. RET16
   requires op_taint tn_16 (Var "%9") = {}; eval_operands [Var "%9"]
   is SOME [1w], so step_inst_base returns IntRet with iret_values=[],
   iret_adopt_fmp=NONE. It neither jumps to label1 nor halts; caller
   resumption is a separate INVOKE obligation. No storage requests/Halt
   occur in this suffix, so those ptr_inst_ok implications are vacuous.

   Actual-return robustness test still unproved:
     !mem. mem_agree_outside tn_16.t_mem state_16.vs_memory mem ==>
       val_in_memory
         (TupleTV [BaseTV (BytesT (Dynamic 33));
                   ArrayTV (BaseTV BoolT) (Dynamic 1)])
         (ArrayV (TupleV [BytesV []; ArrayV (DynArrayV [])])) 64 mem
   structlit_return_representation_test below checks this exact layout
   against val_in_memory: it is equivalent to the two zero header words.
   The old LayoutProbe uses two bytes children, NOT this fixture's layout.
   The universal mem_agree_outside test and source-value relation remain
   unproved here; the layout equivalence does not itself supply them.
   The source conditional selecting empty versus singleton arrays and its
   control-flow/INVOKE certificate remain absent; do not invent a compiler
   fixture here. They require strategist design before integration.
*)

Theorem structlit_return_representation_test:
  !mem.
    val_in_memory
      (TupleTV [BaseTV (BytesT (Dynamic 33));
                ArrayTV (BaseTV BoolT) (Dynamic 1)])
      (ArrayV (TupleV [BytesV []; ArrayV (DynArrayV [])])) 64 mem <=>
    mem_word_at 64 mem = 0w /\ mem_word_at 160 mem = 0w
Proof
  simp[val_in_memory_def, type_memory_size_def, mem_bytes_at_def] >>
  EVAL_TAC >> simp[]
QED
