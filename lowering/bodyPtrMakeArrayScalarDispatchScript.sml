(* Compiler-facing scalar audit.  No new definition is needed.

   Branch table at the post-ADD consumer:
     StackValue: identity (unwrap_stack_ptr_path).
     LocMemory: MLOAD; robust word cleanliness is ptr_mem_word_clean.
     LocStorage: SLOAD; ptr_vv_word_key_clean gives clean key bytes.
     LocTransient: TLOAD; the same theorem gives clean transient key bytes.
     LocCalldata: excluded by vv_post_calldata, not by a guessed shape rule.
     LocCode runtime: DLOAD (runtime_code_word_unwrap).
     LocCode constructor: excluded by ~ce_is_ctor in expr_vv_sim_ptr's
       universal caller premises.  Otherwise compile_imm_load_word uses
       ILOAD, optionally preceded by ADD; those are not external_load edges.

   Proposed public contract (NOT a theorem asserted by this audit):
     unwrap_value ce vv sm = (op,sb) /\
     vv_post ctx fn ce cx e es sa sm s0 es' tv vv s /\
     read_result cx tv es' = (INL v,es') /\
     is_word_type (expr_type e) /\
     ptr_vv_ok cx (expr_type e) tv vv es' G tn s /\
     fn_has_code sm sb fn /\ fn_inst_ids_distinct fn /\
     local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
     sa.cs_next_var <= sm.cs_next_var /\
     (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
     ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\ ~s.vs_halted /\
     s.vs_current_bb = sm.cs_current_bb /\
     s.vs_inst_idx = LENGTH sm.cs_current_insts /\
     ghost_inv d ce cx es' G tn s /\
     ghost_kept ce es sa G0 tn0 s0 G tn /\
     (!name p sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
                  not_fresh_at sm p) /\
     (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
     (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
     not_fresh_at sm dst /\ ptr_covers G tn dst s n
   implies existence of Gf,tnf,sf with gas_path_ptr D 0 ... s 0 ... (OK sf),
   expr_post, ptr_val_ok, ghost_inv, ghost_kept, final compiler PC alignment,
   lookup_var dst sf = lookup_var dst s and ptr_covers Gf tnf dst sf n.
   The old var/local/return premises are exactly the freshness interface of
   emit_op; aggregate callers must discharge them from local_ptrs_reserved,
   reserved return operands, monotonic counters and the emitted ADD result.

   Remaining boundary gaps: emitted code -> fetch/fresh output; typed load
   semantics from vv_post/read_result; memory ambient ghost frame.  Existing
   raw MemoryWord and ExternalWord endpoints do not prove this contract.
   No source-buffer premise or scalar ptr_buf_ok conclusion belongs here.
*)
Theory bodyPtrMakeArrayScalarDispatch
Ancestors
  bodyPtrMakeArrayDispatch bodyPtrMakeArrayWordClean exprSimUnwrap
  exprLowering context venomInst

Theorem scalar_unwrap_emits_load:
  vv_post ctx fn cenv cx e es sa sm s0 es' tv (LocatedValue t p) s /\
  is_word_type t /\ ~cenv.ce_is_ctor ==>
  ?opc.
    ((p.ptr_location = LocMemory /\ opc = MLOAD) \/
     (p.ptr_location = LocStorage /\ opc = SLOAD) \/
     (p.ptr_location = LocTransient /\ opc = TLOAD) \/
     (p.ptr_location = LocCode /\ opc = DLOAD)) /\
    unwrap_value cenv (LocatedValue t p) sm = emit_op opc [p.ptr_operand] sm
Proof
  strip_tac >>
  `p.ptr_location <> LocCalldata` by metis_tac[vv_post_calldata] >>
  Cases_on `p.ptr_location` >>
  gvs[unwrap_value_def, compile_ptr_load_def, compile_imm_load_word_def]
QED
