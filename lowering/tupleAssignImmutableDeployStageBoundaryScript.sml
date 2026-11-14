(* Actual tuple staging boundary.  See the interface ledger at the end. *)
Theory tupleAssignImmutableDeployStageBoundary
Ancestors
  tuplePlaceSnapshot tupleAssignPrefix stmtLowering exprLowering context
  tupleStageProps localPtrsProps loweringStateRelDefs venomInst emitHelper compileEnv
Libs
  monadsyntax

(* may_stage is not itself the copying guard: complex fields and positive
   size are also required, and the target must support MCOPY. *)
Theorem tuple_immutable_unpack_staging_branch:
  compile_tuple_unpack cenv (TupleT tys)
    (is_memory_view e /\ vv_location vv = SOME LocMemory) targets op =
  (let n = SUM (MAP (type_memory_bytes cenv) tys) in
   let copy = (is_memory_view e /\ vv_location vv = SOME LocMemory /\
              EXISTS (\t. ~is_word_type t) tys /\ 0 < n) in
   if copy /\ ~cenv.ce_target CapMcopy then emit_inst INVALID [] []
   else
     do staged <- (if copy then
          do buf <- compile_alloc_buffer n;
             ptr <- comp_return buf.buf_operand;
             emit_void MCOPY [ptr; op; Lit (n2w n)];
             comp_return ptr od
        else comp_return op);
        vals <- compile_tuple_load_all cenv staged tys 0;
        compile_tuple_store_all cenv tys targets vals
     od)
Proof
  simp[compile_tuple_unpack_def, LET_THM, GSYM CONJ_ASSOC,
       arithmeticTheory.GREATER_DEF, comp_bind_def, comp_return_def]
QED

(* The nonmemory branch is a materializer, not the identity.  This equation
   also covers the zero-byte case; it does not assert runtime ownership. *)
Theorem tuple_immutable_unwrap_nonmemory:
  p.ptr_location <> LocMemory ==>
  unwrap_value cenv (LocatedValue (TupleT tys) p) =
    compile_ensure_in_memory p.ptr_operand p.ptr_location
      (type_memory_bytes cenv (TupleT tys))
      ((type_memory_bytes cenv (TupleT tys) + 31) DIV 32)
      cenv.ce_is_ctor cenv.ce_imm_alloca
Proof
  strip_tac >> simp[unwrap_value_def, is_word_type_def] >>
  Cases_on `p.ptr_location` >> gvs[]
QED

Theorem tuple_immutable_unpack_zero_layout:
  SUM (MAP (type_memory_bytes cenv) tys) = 0 ==>
  compile_tuple_unpack cenv (TupleT tys) may_stage targets op =
    do vals <- compile_tuple_load_all cenv op tys 0;
       compile_tuple_store_all cenv tys targets vals od
Proof
  strip_tac >> simp[compile_tuple_unpack_def] >>
  simp[FUN_EQ_THM, comp_bind_def, comp_return_def]
QED

(* Retain the missing age bound when using the existing owned run probe.
   This is intentionally a run contract, NOT a gas-marked-path contract. *)
Theorem tuple_immutable_stage_owned_age:
  (do buf <- compile_alloc_buffer sz;
      emit_void MCOPY [buf.buf_operand; op; Lit (n2w sz)];
      comp_return buf.buf_operand od) sa = (staged,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  eval_operand op s = SOME sw /\
  val_in_memory tv v (w2n sw) s.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= sz /\ sz < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t w. eval_operand staged t = SOME w /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    sa.cs_next_id < sb.cs_next_id /\
    val_in_memory tv v (w2n w) t.vs_memory /\
    stmt_state_rel ctx func cenv cx es t /\
    (!n lb lsz. local_region cenv es.scopes t n lb lsz ==>
      w2n w + sz <= lb \/ lb + lsz <= w2n w) /\
    (!fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx func s = r)
Proof
  strip_tac >> drule_all tuple_place_stage_owned_probe >> strip_tac >>
  drule_all tuple_stage_copy_parts >> strip_tac >>
  qexistsl [`t`, `w`] >> simp[] >>
  gvs[emit_void_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
      fresh_id_def, comp_return_def, emit_def] >> metis_tac[]
QED

(* Interface/caller discharge ledger (bounded checkpoint, NOT gate release).

   Compiler states and values:
     compile_expr cenv (expr_type e) e sE = (src_vv,sU)
     unwrap_value cenv src_vv sU = (src_op,sA)
     optional staging sA = (staged,sB)
     compile_tuple_load_all ... sB = (elems,sL)
   Runtime/source states at these boundaries must be supplied by the RHS
   evaluation and read_result simulations. In particular the stage source
   state is the state AFTER read_result/unwrap, not the initial stmt state.
   compile_stmt_def's TupleTarget clause supplies the first two compiler
   calls and may_stage = is_memory_view e /\ vv_location src_vv = SOME LocMemory.
   tuple_immutable_unpack_staging_branch checks the further actual guard:
     copy = may_stage /\ EXISTS nonword tys /\ 0 < total_mem.
   There is also a CapMcopy rejection branch. Name, TopLevelName, Subscript,
   Attribute all have is_memory_view = T by is_memory_view_def; their final
   location must still be obtained from the compile_expr/vv_post instance.

   Existing positive-size gas interface (reuse, do not duplicate):
     tupleAssignPrefix.optional_tuple_stage_path
   Instantiate flag with copy above, se with the expression's compiler
   origin, sa/sb with sA/sB, op with src_op, es with the source state after
   read_result, and s with its matching post-unwrap runtime state. Its
   conclusion contains gas_marked_path F ctx func s 0 (OK t), tuple bytes,
   alloca_frame and old operand/allocation preservation. Its container is
   ALLOCATION OR LOCAL; it does not supply allocation id/age/separation.
   tuple_immutable_stage_owned_age gives allocation id sA.cs_next_id,
   age < sB.cs_next_id, exact envelope and nonlocal separation, even at
   size zero, but only a run_from continuation contract. These two
   existential runtime states have NOT been identified: joining them
   requires an additional common-witness gas/ownership boundary. No theorem
   in this file claims that the run contract supplies a gas-marked path.

   Premise ledger for that join and for the frozen caller:
   - evaluate_type TupleT and value_has_type: must be derived from the frozen
     typing / expr_sim_inv and successful source evaluation/read_result.
   - expr_val_rel, expr_val_at, stmt_state_rel: supplied conditionally by
     the instantiated expression and unwrap post, not by syntax alone.
   - val_wf, val_in_memory, footprint <= total_mem: derived from those
     tuple posts and type layout (expr_tuple_memory_owned at positive size).
   - total_mem = type_memory_size_list tvs: type_memory_bytes_tuple_list
     given LIST_REL layout; tuple_element_sizes reduces its word cases.
   - copy ==> size < dimword(:256): needs the caller's supported-layout
     bound; optional_tuple_stage_path does not prove it. Zero is handled by
     tuple_immutable_unpack_zero_layout, not by dropping positivity from
     optional_tuple_stage_path. All-word positive tuples also skip copying:
     their eagerly loaded scalar operands require no pending tuple bytes.
   - src_op freshness: compiler_unwrap_value_var needs freshness of src_vv;
     derive that from compiler_compile_var in the actual compile_expr instance.
   - local_ptrs_reserved cenv sA: transport the original reservation through
     compiler growth (local_ptrs_reserved_next_var); not a frozen premise.
   - fn_has_code sA sB func: split the full compiled stmt's code inclusion
     at the stage with compiler extension facts / fn_has_code_split.
   - fn_inst_ids_distinct: project from the caller's function wellformedness.
   - not halted, current_bb, inst_idx: the actual unwrap runtime path must
     end at sA; the compiler equations do not establish runtime alignment.
   Each entry above is a discharge route or explicit remaining obligation;
   this checkpoint does not assert that the frozen caller has discharged it.

   False may_stage / nonmemory unwrap:
   tuple_immutable_unwrap_nonmemory checks the materializer call for a tuple
   LocatedValue. context.compile_ensure_in_memory_def allocates and copies
   for LocStorage (SLOAD/word-copy), LocTransient (TLOAD/word-copy), and
   LocCode (compile_imm_copy_to_memory using ce_is_ctor/ce_imm_alloca).
   LocCalldata is different: it loads a length word and allocates bytes+32;
   exclude it using vv_post_calldata, as existing unwrap proofs do, rather
   than claiming tuple ownership for that path. StackValue simply returns
   its operand; its tuple exclusion needs vv_holds, not this equation.
   Existing bodyMemAggregateUnwrap.aggregate_unwrap_value_path_mem_capacity
   exports a gas_path_mem and capacity, but not age/nonlocal ownership;
   exprSimUnwrap.unwrap_value_path exports expr_post with the same-layout
   conditional ownership limitation. The missing nonmemory producer
   contract must retain the returned operand, allocation entry, full tuple
   envelope, age, local separation, and gas-marked path at ONE returned
   runtime state (also audit zero-sized layouts). No branch here is a
   checked reachable counterexample or a demonstrated external premise gap.
*)
