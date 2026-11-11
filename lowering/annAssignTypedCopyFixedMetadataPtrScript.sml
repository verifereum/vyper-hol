(* Evaluated strides and generated-register bounds for typed array copying.
   Concrete instruction locations are supplied by typedCopyLoopLayoutPtr. *)
Theory annAssignTypedCopyFixedMetadataPtr
Ancestors
  typedCopyLoopLayoutPtr exprLoweringProps fragExec compileEnv vyperStorageWritePreservation valueEncodingProps
  typedMemoryCopy freshWrites loweringStateRelDefs builtinIntClamp ASCIInumbers arithmetic list

Theorem annassign_evaluated_array_stride_positive:
  !tenv ty tv bd.
    evaluate_type tenv ty = SOME (ArrayTV tv bd) ==>
    0 < type_memory_size tv
Proof
  rpt strip_tac >> drule evaluate_type_ArrayTV_inv >> strip_tac >>
  metis_tac[type_memory_size_pos]
QED

Theorem annassign_positive_stride_offsets:
  !k count stride off limit.
    0 < stride /\ k < count /\ off + count * stride <= limit ==>
    k * stride < count * stride /\
    off <= off + k * stride /\
    off + k * stride + stride <= off + count * stride /\
    off + k * stride + stride <= limit
Proof
  rpt strip_tac >>
  drule typed_copy_array_subinterval >>
  disch_then (qspecl_then [`off`, `stride`] strip_assume_tac) >>
  simp[]
QED

(* A range boundary rather than separate fixed-list freshness variants. *)
Theorem annassign_generated_register_range:
  !sa si width.
    sa.cs_next_var + width <= si.cs_next_var ==>
    (!j. j < width ==>
      not_fresh_at si ("%" ++ toString (sa.cs_next_var+j))) /\
    (!x j. not_fresh_at sa x ==>
      x <> "%" ++ toString (sa.cs_next_var+j)) /\
    (!x. not_fresh_at sa x ==> not_fresh_at si x) /\
    ALL_DISTINCT (GENLIST (\j. "%" ++ toString (sa.cs_next_var+j)) width)
Proof
  rpt strip_tac >>
  simp[not_fresh_at_def, toString_inj, ALL_DISTINCT_GENLIST] >>
  rpt strip_tac >> gvs[not_fresh_at_def, toString_inj] >>
  metis_tac[LESS_EQ_TRANS, DECIDE ``a <= a+j``]
QED

Theorem annassign_sarray_child_frontier:
  !ce dst dty src sty count sa sz fn.
    ~(type_memory_bytes ce dty = type_memory_bytes ce sty /\
      ~is_abi_dynamic ce.ce_struct_fields dty) /\
    compile_copy_sarray_typed ce dst dty src sty count sa = ((),sz) /\
    fn_has_code sa sz fn ==>
    ?si se bb.
      compile_store_memory_typed ce
        (Var ("%" ++ toString (sa.cs_next_var+6))) dty
        (Var ("%" ++ toString (sa.cs_next_var+5))) sty si = ((),se) /\
      si.cs_next_var = sa.cs_next_var + 7 /\
      si.cs_next_id = sa.cs_next_id + 9 /\
      si.cs_current_bb =
        fresh_label_output "typed_sa_body" (sa.cs_next_label+1) /\
      si.cs_next_var <= se.cs_next_var /\
      cs_extends sa si /\ cs_extends si se /\ cs_extends se sz /\
      fn_has_code si se fn /\
      lookup_block si.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX si.cs_current_insts bb.bb_instructions
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_copy_sarray_typed_loop_layout >> strip_tac >>
  rename1 `compile_store_memory_typed ce (Var dp) dty (Var sp) sty si = ((),se)` >>
  `ci_mono si se` by
    (mp_tac (cj 1 exprLoweringPropsTheory.ci_mono_typed_memory_family) >>
     disch_then (qspecl_then [`ce`, `Var dp`, `dty`, `Var sp`, `sty`, `si`] mp_tac) >>
     simp[]) >>
  `cs_extends sa si` by
    (simp[cs_extends_def] >> qexists_tac `TAKE 2 si.cs_blocks` >> simp[]) >>
  `cs_extends se sz` by
    (simp[cs_extends_def] >> qexists_tac `[HD sz.cs_blocks]` >> simp[]) >>
  `cs_extends si se /\ si.cs_next_var <= se.cs_next_var` by
    gvs[ci_mono_def] >>
  `cs_extends si sz` by metis_tac[cs_extends_trans] >>
  `fn_has_code si se fn` by metis_tac[fn_has_code_split] >>
  `?bb. lookup_block si.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX si.cs_current_insts bb.bb_instructions` by
    metis_tac[fn_has_code_start] >>
  qexistsl_tac [`si`, `se`, `bb`] >>
  gvs[]
QED
