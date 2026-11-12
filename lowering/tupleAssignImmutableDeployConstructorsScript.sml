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
