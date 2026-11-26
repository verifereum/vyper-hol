Theory functionInlinerContract
Ancestors
  functionInlinerDefs functionInlinerPtrCheck o1PassContract ptrDiscipline
  contextRawReachable unitTransformDefs lowerDloadDefs vyperCompiler
  callLayoutDefs stackPlanGen unitShapeDefs fcgDefs contextCodegenRel
  venomExecSemantics venomWf venomInst venomState list string words

Definition reachable_ctx_def:
  reachable_ctx C =
    C with ctx_functions :=
      FILTER (\fn. fcg_is_reachable (fcg_analyze C) fn.fn_name)
        C.ctx_functions
End

(* A round can remove a callee still named by an unvisited caller. Keep
   function-local well-formedness and uniqueness on the full context. *)
Definition inliner_shape_ok_def:
  inliner_shape_ok C <=>
    let R = reachable_ctx C in
    ctx_inst_ids_distinct C /\
    EVERY wf_function C.ctx_functions /\
    ALL_DISTINCT (MAP (\fn. fn.fn_name) C.ctx_functions) /\
    o1_ctx_shape R /\
    EVERY fn_defs_reach_uses R.ctx_functions /\
    EVERY fn_phis_cover_preds R.ctx_functions /\
    EVERY (\fn.
      canonical_param_prefix fn /\ opaque_use_ok fn /\ retpc_shape_ok fn /\
      EVERY (\x. LENGTH (FILTER (\i. MEM x i.inst_outputs) (fn_insts fn)) = 1)
        (FLAT (MAP (\i. i.inst_outputs)
           (FILTER (\i. i.inst_opcode = PARAM) (fn_insts fn)))) /\
      EVERY (\inst.
        label_positions_ok inst /\
        (inst.inst_opcode = PHI ==>
          EVERY (\op. !l. op = Label l ==> MEM l (fn_labels fn))
            inst.inst_operands) /\
        (inst.inst_opcode = INVOKE ==>
          ALL_DISTINCT inst.inst_outputs /\
          EVERY (\op. !v. op = Var v ==> ~MEM v inst.inst_outputs)
            (TL inst.inst_operands)))
        (fn_insts fn))
      R.ctx_functions /\
    (!caller inst callee args.
       MEM caller R.ctx_functions /\ MEM inst (fn_insts caller) /\
       MEM callee R.ctx_functions /\ inst.inst_opcode = INVOKE /\
       inst.inst_operands = Label callee.fn_name :: args ==>
       IS_SOME (fn_retpc_param callee) /\
       LENGTH (rotate_invoke_ops inst.inst_operands) =
         LENGTH (get_params (fn_entry_insts callee)) /\
       EVERY (\r. raw_return_user_arity r = SOME (LENGTH inst.inst_outputs))
         (fn_return_insts callee)) /\
    (!fn other. MEM fn R.ctx_functions /\ MEM other R.ctx_functions /\
       fn.fn_name <> other.fn_name ==> ~MEM other.fn_name (fn_labels fn)) /\
    (!entry fn inst args.
       R.ctx_entry = SOME entry /\ MEM fn R.ctx_functions /\
       MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE ==>
       inst.inst_operands <> Label entry :: args) /\
    (?rank : string -> num.
       !caller callee. fn_directly_calls R caller callee ==>
                       rank callee < rank caller)
End

(* Inlining introduces "inl" names and grows the caller's entry block.
   The proof of the loop tracks the name counter and the original prologue.
   Each revert-forward pair of the input stays one when its block is cut at
   the pair's start, as inlining may cut it there. This is asked of the
   input only: inlining a PARAM as an ASSIGN can create new pairs in the
   output that fail it (inliner_rfp_cut_witness). *)
Definition inliner_input_guard_def:
  inliner_input_guard C <=>
    (!fn bb i j. MEM fn (reachable_ctx C).ctx_functions /\
       MEM bb fn.fn_blocks /\ revert_forward_pair bb i j ==>
       revert_forward_pair
         (bb with bb_instructions := DROP i bb.bb_instructions) 0 (j - i)) /\
    EVERY (\fn.
      LENGTH (fn_entry_insts fn) < dimword (:256) /\
      ~isPREFIX "inl" fn.fn_name /\
      EVERY (\bb. ~isPREFIX "inl" bb.bb_label) fn.fn_blocks /\
      EVERY (\inst.
        EVERY (\v. ~isPREFIX "inl" v) inst.inst_outputs /\
        EVERY (\op. case op of Var v => ~isPREFIX "inl" v | _ => T)
          inst.inst_operands) (fn_insts fn))
      (reachable_ctx C).ctx_functions
End

(* The map P is used by the syntactic conjunct of ptr_discipline. Its
   reachable-state clauses are independent of P, so this conjunct supplies
   a single map that also meets the inliner's pointer requirements. W holds
   the pointer positions a write can reach; only those need a single root,
   since the relation relocates pointers by their run's ghost provenance. *)
Definition inliner_stage_inv_def:
  inliner_stage_inv D C vs <=>
    inliner_shape_ok C /\ o1_src_inv D C vs /\
    (?P W. (!nm. W nm SUBSET P nm) /\
           EVERY (\fn. fn_ptr_ok P fn /\ fn_ptr_ok P (reachable_fn fn))
             C.ctx_functions /\ inline_ptr_ok P W (reachable_ctx C))
End

(* Each activation inherits its parent's current static frontier. Its
   entry therefore pays for that frontier plus its own reachable sites.
   The DLOAD scratch allowance uses the same count as dload_headroom_ok. *)
Definition inlined_allocas_fit_def:
  inlined_allocas_fit vs C <=>
    !fn inst s bb.
      raw_reachable vs C fn inst s /\ entry_block fn = SOME bb /\
      s.vs_current_bb = bb.bb_label /\
      s.vs_inst_idx = phi_prefix_length bb.bb_instructions ==>
      let insts = fn_insts (reachable_fn fn) in
      let bound = s.vs_alloca_next +
        SUM (MAP alloca_size (FILTER (\i. i.inst_opcode = ALLOCA) insts)) +
        32 * ctx_dload_count C in
      bound < dimword (:256) /\
      (ctx_has_dalloca C ==> bound <= w2n vs.vs_initial_fmp)
End

(* At every finite execution prefix, charge the pending DALLOCA against the
   current FMP before the addition. In pre-FMP code that pointer accumulates
   the rounded sizes since entry, restoring the saved amount on a real RET.
   Repeated executions of one site are charged separately. *)
Definition inlined_dallocas_fit_def:
  inlined_dallocas_fit vs C <=>
    !fn inst s. raw_reachable vs C fn inst s ==> dalloca_no_wrap inst s
End

(* Prove the simulation and invariant transport one call site at a time
   using frame relocation, then compose across the inliner's rounds. *)
Definition function_inliner_pass_correct_stmt_def:
  function_inliner_pass_correct_stmt <=>
    !D C vs threshold.
      let C' = function_inliner_ctx threshold C in
      o1_run_state_ok vs /\ dead_wf D /\
      inliner_stage_inv D C vs /\ inliner_input_guard C /\
      inlined_allocas_fit vs C' /\ inlined_dallocas_fit vs C' ==>
      ctx_sim D C C' vs vs /\ inliner_stage_inv D C' vs
End
