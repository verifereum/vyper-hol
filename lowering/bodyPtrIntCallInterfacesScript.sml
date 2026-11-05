(* Checked projections at the internal-call ghost boundary.
   The INVOKE rule resets only callee variables, not memory taint. *)
Theory bodyPtrIntCallInterfaces
Ancestors ptrSafeRun ptrDiscipline finite_map pred_set list

Theorem intcall_initial_taint_memory:
  (tn with t_var := FEMPTY).t_mem = tn.t_mem
Proof
  simp[]
QED

Theorem intcall_ghost_caller_variable:
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm, ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  ~MEM x inst.inst_outputs ==>
  FLOOKUP (FST (ghost_step fuel ctx PG G tn inst s)) x = FLOOKUP G x /\
  op_taint (SND (ghost_step fuel ctx PG G tn inst s)) (Var x) =
    op_taint tn (Var x)
Proof
  rpt strip_tac >> drule_all ghost_step_invoke >>
  disch_then (fn th => rewrite_tac[th]) >>
  simp[op_taint_def, FLOOKUP_DRESTRICT]
QED

(* Premise ledger for the subsequent pointer proof (not assumptions):
   ENTRY. The body IH is body_stmts_ptr_ok: its inputs include body_inv,
   supported/typechecked statements, expression invariants, local allocation
   conditions, call_evaluation_safe, and frame_ret_ok_ptr. At the fragment
   boundary stmt_frag_ptr additionally needs reserved local pointers,
   return-PC validity, distinct instruction ids, code inclusion, admissible
   gas, state relation, and ghost_inv. compile_internal_prologue_entry
   supplies the ordinary state relation and fresh variables, but no pointer
   path or ghost_inv. Thus a pointer-counted prologue is still required.

   STAGING. Proposed interface: for every memory-passed operand, expose its
   evaluated address, op_prov site, empty op_taint, site coverage, robust
   val_in_memory under mem_agree_outside, and disjointness from protected
   caller regions. Stack arguments instead need clean operand taint and
   their ordinary typed word relation. A memory return buffer needs site
   coverage but not initially clean contents. PG is exactly MAP (op_prov G)
   of the final INVOKE operands; the initial G is FEMPTY. The checked reset
   projection above rules out treating initial callee memory as clean.

   RETURN. Proposed continuation: expose an IntRet counted path ending in
   the callee ghost, typed robust result (buffer or clean stack words), and
   protected caller-memory taint inclusion in the pre-call taint. Memory
   return (zero stack results) needs ptr_covers of the explicit first
   operand; stack multi-return needs clean returned operands followed by
   counted pointer-safe stores into the caller's fresh buffer; void needs
   neither buffer nor result stores. frame_ret_ok_ptr quantifies over all
   same_frame environments and return expressions, not just one exit.

   RUN BRIDGE. gas_path_ptr_exec supplies a safe ghost_run only for an
   exit_result, otherwise a continuation implication. INVOKE asks for
   ptr_safe_blocks from entry. The entry-block/phi bridge and non-error
   callee termination must be connected, with the same fuel used for
   ghost_blocks and ptr_safe_blocks.

   FRAME GAP. stmt_frag_ptr's normal post preserves old variables only.
   ghost_kept additionally requires no new taint in protected caller bytes.
   callee_writes_above is ordinary byte equality, not taint equality.
   decoderGhostFramePtr.step_taint_memory_bound is only a one-step bound;
   a whole-run bound must also constrain inherited sites, new allocations,
   and nested calls. No such whole-run pointer/taint boundary was found in
   the searched toolkit. Access safety alone permits writes anywhere in an
   inherited site; staging must ensure inherited sites do not cover caller
   protected bytes (including unused tails of older sites).
*)
