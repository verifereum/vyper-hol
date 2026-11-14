(* Allocation-producing tuple RHS checkpoint.  These facts retain the
   envelope owner rather than strengthening the ordinary same-layout post. *)
Theory tupleAssignImmutableDeployConstructors
Ancestors
  exprSimAggregates exprSimAggregateLayout exprSimAggregateChildren
  exprSimAggregateLoops exprSimBufferEmptyExec exprOperandVar
  tuplePlaceSnapshot localPtrsProps loweringStateRelDefs loweringPosts exprLoweringProps

(* The final operand is precisely the allocated envelope, even when fields
   are bytestrings.  This is not merely an ALLOCA occurrence in the code. *)
Theorem tuple_immutable_make_tuple_buffer:
  compile_expr ce ty (Builtin ann (MakeArray NONE bnd) args) sa = (vv,sb) ==>
  ?ba sm. compile_alloc_buffer
      (SUM (MAP (type_memory_bytes ce o expr_type) args)) sa = (ba,sm) /\
    compile_make_tuple compile_expr ce args ba.buf_operand 0 sm =
      (ba.buf_operand,sb) /\
    vv = LocatedValue ann (mk_ptr ba.buf_operand LocMemory)
Proof
  strip_tac >> drule compile_tuple_literal_inv >> strip_tac >>
  drule compiler_make_tuple_result >> strip_tac >> gvs[] >>
  simp[contextTheory.base_ptr_def]
QED

(* Empty's exported execution theorem already retains the allocation through
   zero initialization.  Convert its initial-scope clearance to final-state
   clearance and retain the exact age interval needed by tuple snapshots. *)
Theorem tuple_immutable_empty_snapshot_run:
  compile_builtin_empty_complex sz F sa = (buf,sb) /\
  fn_has_code sa sb func /\ stmt_state_rel ctx func cenv cx es s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  sz = type_memory_size_list tvs /\ sz < dimword (:256) /\ sz MOD 32 = 0 ==>
  ?t w. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func cenv cx es t /\
    eval_operand buf.buf_operand t = SOME w /\
    (type_memory_size_list tvs = 0 \/
     ?aid b n. FLOOKUP t.vs_allocas aid = SOME (b,n) /\
       sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
       b <= w2n w /\ w2n w + type_memory_size_list tvs <= b+n /\
       (!name lb lsz. local_region cenv es.scopes t name lb lsz ==>
          b+n <= lb \/ lb+lsz <= b))
Proof
  strip_tac >> drule_all (SRULE [] (Q.SPEC `sz` compile_builtin_empty_complex_run |> Q.SPEC `F`)) >>
  disch_then (qx_choosel_then [`t`, `w`] strip_assume_tac) >>
  qexistsl [`t`, `w`] >> simp[] >> disj2_tac >>
  qexistsl [`sa.cs_next_id`, `w2n w`, `sz`] >> simp[] >>
  rpt strip_tac >>
  `local_region cenv es.scopes s name lb lsz` by
    (irule exprSimPropsTheory.local_region_frame >> conj_tac
     >- (qexists `func` >> gvs[stmt_state_rel_def, state_rel_def]) >>
     qexistsl [`sa`, `es.scopes`, `t`] >> simp[]) >>
  qpat_x_assum `!name b len. local_region _ _ s _ _ _ ==> _` drule >>
  simp[arithmeticTheory.ADD_COMM]
QED

(* At the successful endpoint of aggregate_make_tuple_sim, its retained
   lookup/allocation clauses and final stmt_state_rel suffice: no field-store
   frame has to be proved again, including for bytes/string fields. *)
Theorem tuple_immutable_make_tuple_snapshot_endpoint:
  stmt_state_rel ctx func ce cx es r /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [x] /\
  not_local_ptr ce es.scopes x /\
  FLOOKUP r.vs_allocas inst.inst_id = SOME (b,n) /\
  sa.cs_next_id <= inst.inst_id /\ inst.inst_id < sb.cs_next_id /\
  lookup_var x r = SOME (n2w b) /\ b+n < dimword (:256) /\
  type_memory_size_list tvs <= n ==>
  eval_operand (Var x) r = SOME (n2w b) /\
  (type_memory_size_list tvs = 0 \/
   ?aid p sz. FLOOKUP r.vs_allocas aid = SOME (p,sz) /\
     sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
     p <= w2n (n2w b : bytes32) /\
     w2n (n2w b : bytes32) + type_memory_size_list tvs <= p+sz /\
     (!name lb lsz. local_region ce es.scopes r name lb lsz ==>
       p+sz <= lb \/ lb+lsz <= p))
Proof
  strip_tac >>
  `b < dimword (:256)` by decide_tac >>
  simp[venomStateTheory.eval_operand_def, wordsTheory.w2n_n2w] >>
  disj2_tac >> qexistsl [`inst.inst_id`, `b`, `n`] >> simp[] >>
  rpt strip_tac >> drule_all exprSimOperandsTheory.alloca_clear_of_locals >> simp[]
QED

(* C0.6 premise-discharge ledger (interface checkpoint, not caller coverage).

   MAKEARRAY NONE -- compile_make_array_vv_case[tuple], exprSimAggregates.
   Compiler: tuple_immutable_make_tuple_buffer identifies the final value as
   LocatedValue ann (mk_ptr ba.buf_operand LocMemory).  The buffer metadata is
   NOT base_ptr ba.  The successful unwrap must still be composed by a caller;
   its pointer operand is ba.buf_operand, not a separately guessed operand.

   Existing producer proof discharges aggregate_make_tuple_sim as follows:
   - expr_body_pre gives typing, expr_sim_inv and allocation limits;
     make_tuple_evaluated_layout gives ann, evaluated tvs and EXACT equality
     SUM (MAP (type_memory_bytes ce o expr_type) args) =
       type_memory_size_list tvs.  This is the complete envelope, including
     reserved capacity of BytesT/StringT fields, not val_footprint.
   - expr_body_pre_builtin_arg and int_calls_builtin_arg supply the quantified
     child preconditions at every reachable expr_sim_inv state.
   - exprs_case and the child lowered-value-type alternative are INPUTS of
     compile_make_array_vv_case.  They are not consequences of typing alone.
   - ci_mono_compile_alloc_buffer and ci_mono_compile_make_tuple_cfn split
     fn_has_code and give sa <= sm <= sb for allocation ages.
   - buffer_alloc_code plus buffer_alloc_counted identify x and inst, with
     ba.buf_operand = Var x, inst.inst_id = sa.cs_next_id < sm.cs_next_id,
     inst.inst_outputs = [x], MEM inst (fn_insts func), not_fresh_at sm x,
     local_ptrs_reserved ce sm and not_local_ptr ce scopes x for ALL scopes.
     Allocation yields lookup_var x t = SOME (n2w b),
     FLOOKUP t.vs_allocas inst.inst_id = SOME (b,envelope_size),
     b+envelope_size < dimword (:256), and a zero-cost gas_marked_path F
     from the original runtime state to t at the sm program counter.
   - The constructor-immutable separation premise of aggregate_make_tuple_sim
     follows from aggregate_alloca_immutable_sep at t (opcode ALLOCA comes
     from buffer_alloc_code), not an extra premise on source values.
   - aggregate_make_tuple_sim at off=0 retains BOTH the pointer lookup and
     the complete allocation entry through field construction.  It also gives
     stmt_state_rel at the final source/runtime endpoint.  These clauses,
     the age inequalities above and final-scope not_local_ptr discharge EVERY
     premise of tuple_immutable_make_tuple_snapshot_endpoint.  In particular
     alloca_clear_of_locals supplies final local clearance directly, without
     requiring source scopes to be unchanged by a child.  This holds for
     bytes/string children as well as word children; there is no word-only
     supported_scalar_type inference.  Zero size needs no positive-size axiom.
   - gas_outcome_zero_prefix and aggregate_tuple_action are used in the
     existing proof to join allocation to field construction; aggregate_eval_
     make_tuple maps its successful eval_exprs result to the source tuple.

   EMPTY -- compile_empty_memory_sim, exprSimAggregates.
   - empty_eval_all_tails and source typing give args=[], ann=target; a tuple
     target is not a word.  expr_sim_pre gives allocation limits and invariant;
     empty_type_buffer_size derives the required buffer size and alignment.
     For TupleTV tvs, header=F and sz=type_memory_size_list tvs, including zero.
   - compile_builtin_empty_complex_run retains the allocation at sa.cs_next_id
     and buffer operand through zero initialization, with strict upper age
     sb.cs_next_id.  tuple_immutable_empty_snapshot_run packages that exact
     envelope and transports clearance from initial locals to final locals.
     No child evaluation or per-field store theorem is needed in this branch.
   - empty_complex_gas_path is the existing gas/control interface: it replaces
     t's instruction index by LENGTH sb.cs_current_insts.  compile_empty_memory_
     sim combines it with empty_type_default_memory and default-value typing.
     Snapshot lookup, allocation and local_region are unaffected by this index
     adjustment; the gas-observation adjustment uses msg_gas_state_frame.

   STILL UNPROVED AT THE FROZEN TUPLE-ASSIGN CALLER (both origins):
   The frozen assumptions are not literally expr_body_pre / exprs_case or
   expr_sim_pre.  Their derivation from body_inv, body_expr_ok, typing,
   supported_stmt, stmt_exprs_ok and call_evaluation_safe must be connected at
   the actual RHS invocation, with env and evaluated/lowered tuple layouts.
   Code inclusion/distinctness, initial PC/not-halted, local_ptrs_reserved,
   and initial stmt_state_rel come from stmt_frag's runtime/compilation setup,
   not from the source precondition alone.  The producer success must retain
   the extra owner witness INSIDE its gas_outcome, through unwrap_value and
   the RHS read_result, and deliver it at the actual pre-target PC.  Ordinary
   same-layout vv_post/expr_post exports do not retain that witness.  The
   existing make-array and Empty proofs above show where it is available,
   but these three checkpoint theorems do NOT strengthen those simulations or
   discharge that caller join.  Pending-value preservation across later
   target evaluation AND earlier element stores is outside this checkpoint.
   No missing external premise or reachable counterexample is established.
*)
