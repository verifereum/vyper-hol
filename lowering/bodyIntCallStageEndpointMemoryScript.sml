(* A producer followed immediately by allocation, forcing, and typed store. *)
Theory bodyIntCallStageEndpointMemory
Ancestors
  bodyIntCallStageEndpointLanding bodyIntCallStageEndpointStore
  bodyIntCallFamStmtReturnTypes bodyIntCallFamStmtLogArgsFrame
  exprSimAggregateChildren memoryLocalRhsProps typedMemoryCopy
  bodyIntCallJointForce exprSimSource exprSimMemDefs stmtSimForLoop
  exprBopSimProps exprSimHyps valueEncodingTyping exprLoweringProps

Theorem stage_incompatible_geometry[local]:
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  (!src:256 word. ~is_word_type sty /\ val_footprint stv v <> 0 /\
    eval_operand op u = SOME src ==>
    regions_disjoint (w2n src) (val_footprint stv v) (w2n dw) cap) /\
  type_memory_size dtv <= cap /\
  (sty <> NoneT /\ ~is_word_type sty /\ ~is_bytestring_type sty ==>
    ?src:256 word a k. eval_operand op u = SOME src /\ a <= w2n src /\
      w2n src + type_memory_size stv <= a+k /\ a+k < dimword (:256)) ==>
  ~(dty = sty \/ is_bytestring_type dty /\ is_bytestring_type sty) ==>
  !src:256 word. eval_operand op u = SOME src ==>
    regions_disjoint (w2n src) (type_memory_size stv)
      (w2n dw) (type_memory_size dtv) /\
    w2n src + type_memory_size stv < dimword (:256)
Proof
  rpt strip_tac >>
  `~is_word_type sty` by metis_tac[return_source_word_widens_eq] >>
  `~is_bytestring_type sty` by
    (fs[vyperTypeSystemTheory.type_widens_to_def] >>
     metis_tac[memoryLocalRhsPropsTheory.arg_type_fits_bytestring_target]) >>
  `val_footprint stv v = type_memory_size stv` by
    metis_tac[evaluated_nonbytes_footprint] >>
  Cases_on `type_memory_size stv = 0`
  >- (drule_all widening_zero_memory_size >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def, wordsTheory.w2n_lt]) >>
  `sty <> NoneT` by
    (Cases_on `sty` >> gvs[vyperValueTheory.evaluate_type_def,
      valueEncodingTheory.type_memory_size_def]) >>
  fs[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]
QED
