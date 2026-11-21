(* Compiler geometry, child representation, joint copy and endpoint interpretation
   for storage/transient For iteration. The element copy creates its own CFG. *)
Theory bodyFullForStorage
Ancestors exprSimSubscriptArrayLiveStorageSuffix[qualified,ignore_grammar] exprPtrStorageLoad[qualified,ignore_grammar] exprSimConcatResult[qualified,ignore_grammar] exprSimAggregatesAllocCounted[qualified,ignore_grammar] marker[qualified,ignore_grammar] bodySim[qualified,ignore_grammar]
  bodyFullShadowBodyInv
  stmtLowering exprLowering compileEnv context stmtSimProps
  stmtSimForArrayParts stmtLoweringMono copyExecution emitHelper emitHelperProps
  slotCopyExecution loweringStateRelDefs words string numposrep
  exprLoweringProps fragExec venomInst venomState vyperAST
  finite_map list rich_list arithmetic
  accountsRelProps stmtSimAugAssignPlaceStorage
  exprSimSubscriptArrayLiveStorage
  vyperStorageBackend vyperState vyperLookupStorage
  bodyFullToplevelSlotEntry bodyFullToplevelSlotLoopFrame
  exprPtrUnwrapLoopInvariant exprPtrUnwrapRuntimeFrame exprSimStorageCopy
  loweringPosts fragGasOriginPtr
  exprPtrUnwrapStoragePost exprPtrUnwrapCopyPost stmtSimDefs bodyPtrDefs
  fragGasSeqPtr decoderNavigationPtr bodyPtrBopInLiteralSuffix
  stmtAppendStorageRunPtr
  exprSimWordArgs fragExecMem venomExecSemantics venomExecProps
  instMemFrontier gasEvents gasCount ptrSafeRun
  unitTransformDefs contextCodegenRel codegenRel
  bodyPtrBopInLiveStorage bodyPtrBopInLoadOutput bodyPtrMakeArrayEmission
  exprPtrUnwrapStorageSource exprPtrUnwrapCopyEdges
  typedCopyOriginPtrBase bodyFullGhostFrame bodyFullShared
  bodyMemoryDefs allocaHistory assignTuplePtrCopyLen memSafeRun
  ptrDiscipline exprSimHyps exprSimFieldLayout valueEncodingProps
  exprPtrUnwrapTypedSize
  stmtSimAssignStorageCopy exprSimPopStorage stateRelProj sourceUnitExecution
  vyperStoragePlaceObserved vyperStoragePlaceRegion vyperStorageFootprint
  pred_set fragGasSeqPtr decoderNavigationPtr
  ptrSafeRun venomExecSemantics codegenRel contextCodegenRel unitTransformDefs
  exprPtrUnwrapScalarEdges
  bodyFullPreds bodySimFull gasOutcomeFullCompose
  gasShadow gasShadowState gasShadowUnit gasExplicitSites
  bodyFullForFrame bodyExprPreFacts bodySimDeclCases
  stmtSimForArrayLoop vyperEvalPreservesScopes vyperStorageTrace
  fragGasOriginPtrLoop placeTypedCopyPath
  contextCodegenRel codegenRel venomExecSemantics venomExecProps
  stmtSimDeclCopyFrame bodyFullMemoryFrames
  bodyDeclCopyMemory stmtSimDeclCompose bodySim
  vyperTypeEnv
  bodyFullAllocGeneric bodyPtrIfExpAllocCompiler bodyPtrIfExpAllocSource
  bodyPtrEnvBuiltinsAllocation storageNormalizationAllocPtr
  bodyFullHashKeccakFixed stmtSimDeclPath exprSimOperands allocaSiteResource
  bodyFullForArray allocationPtr loweringHalt
  bodyFullForHandlers haltExitProj gasOutcomeFull vyperStorageFootprint
  gasOutcomeInitialObsPtr[qualified] gasStorage[qualified]
  bodyFullIfExpReach[qualified,ignore_grammar]
  stmtSimForParts[qualified] vyperInterpreter[qualified] gasContext[qualified] fragGasCopyLoop augAssignPtrScalarSafety augAssignPtrScalarCertificate
  supportedExprForms whitelistVisibility immutableLocationProps
  bodyFullForRounds[qualified] gasExemptCert[qualified]
Libs
  monadsyntax

Theorem for_storage_array_stages[local]:
  FLOOKUP cenv.ce_module_vars nid =
    SOME (if tr then TransientLoc slot else StorageLoc slot) /\
  compile_stmt cenv lctx ty
    (For id et (Array (TopLevelName (ArrayT et bd) nid)) n stmts) st =
    ((),st') ==>
  ?lvo sd bc entry cond bod incr exit idx offo toto epo sa sb0 sb1 sj.
    (if (case bd of Dynamic _ => T | Fixed _ => F) then
       compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca
         (if tr then LocTransient else LocStorage) (Lit slot)
     else return (Lit (n2w (bound_length bd)))) st = (lvo,sd) /\
    (do bc <- declare_local cenv id et;
        emit_local_alloca bc id;
        entry <- fresh_label "iter_entry";
        cond <- fresh_label "iter_cond";
        bod <- fresh_label "iter_body";
        incr <- fresh_label "iter_incr";
        exit <- fresh_label "iter_exit";
        emit_inst JMP [Label entry] [];
        new_block entry;
        idx <- fresh_var;
        emit_inst ASSIGN [Lit 0w] [idx];
        (if (case bd of Dynamic _ => T | Fixed _ => F) then
           do invalid <- emit_op GT [lvo; Lit (n2w (bound_length bd))];
              valid <- emit_op ISZERO [invalid];
              emit_void ASSERT [valid] od
         else return ());
        emit_inst JMP [Label cond] [];
        new_block cond;
        done <- emit_op EQ [Var idx; lvo];
        emit_inst JNZ [done; Label exit; Label bod] [];
        new_block bod;
        offv <- emit_op MUL [Var idx;
          Lit (n2w (elem_size_in_location cenv
            (if tr then LocTransient else LocStorage) et))];
        tot <- (if (case bd of Dynamic _ => T | Fixed _ => F) then
                  emit_op ADD [Lit 1w; offv] else return offv);
        ep <- emit_op ADD [Lit slot; tot];
        return (bc,entry,cond,bod,incr,exit,idx,offv,tot,ep)
     od) sd = ((bc,entry,cond,bod,incr,exit,idx,offo,toto,epo),sa) /\
    (case FLOOKUP bc.ce_vars id of
       SOME (MemLoc dst _) =>
         compile_iter_elem_copy cenv epo (Lit (n2w dst))
           (elem_size_in_location cenv
             (if tr then LocTransient else LocStorage) et)
           (if tr then LocTransient else LocStorage) T et et
     | SOME (PtrVar ptr_op _) =>
         compile_iter_elem_copy cenv epo ptr_op
           (elem_size_in_location cenv
             (if tr then LocTransient else LocStorage) et)
           (if tr then LocTransient else LocStorage) T et et
     | _ => emit_void INVALID []) sa = ((),sb0) /\
    compile_stmts bc (InLoop exit incr) ty stmts sb0 = ((),sb1) /\
    emit_jmp_if_not_terminated incr sb1 = ((),sj) /\
    (do new_block incr;
        next <- emit_op ADD [Var idx; Lit 1w];
        emit_inst ASSIGN [next] [idx];
        emit_inst JMP [Label cond] [];
        new_block exit;
        return () od) sj = ((),st')
Proof
  strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  Cases_on `bd` >> Cases_on `tr` >>
  simp[Once compile_stmt_def, Once compile_expr_def, expr_type_def,
       LET_THM, vv_location_def, vv_operand_def, mk_ptr_def,
       is_slot_addressed_def, word_scale_def, bound_length_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> metis_tac[]
QED

(* The declaration state sd is after the optional length load.  This
   certificate keeps the storage header (one slot) distinct from stride. *)
Theorem for_storage_array_prefix[local]:
  cenv.ce_alloca_locals /\
  (do bc <- declare_local cenv id et;
      emit_local_alloca bc id;
      entry <- fresh_label "iter_entry";
      cond <- fresh_label "iter_cond";
      bod <- fresh_label "iter_body";
      incr <- fresh_label "iter_incr";
      exit <- fresh_label "iter_exit";
      emit_inst JMP [Label entry] [];
      new_block entry;
      idx <- fresh_var;
      emit_inst ASSIGN [Lit 0w] [idx];
      (if dyn then
         do invalid <- emit_op GT [lvo; Lit (n2w cap)];
            valid <- emit_op ISZERO [invalid];
            emit_void ASSERT [valid] od
       else return ());
      emit_inst JMP [Label cond] [];
      new_block cond;
      done <- emit_op EQ [Var idx; lvo];
      emit_inst JNZ [done; Label exit; Label bod] [];
      new_block bod;
      offv <- emit_op MUL [Var idx; Lit (n2w stride)];
      tot <- (if dyn then emit_op ADD [Lit 1w; offv] else return offv);
      ep <- emit_op ADD [Lit slot; tot];
      return (bc,entry,cond,bod,incr,exit,idx,offv,tot,ep)
   od) sd = ((bc,entry,cond,bod,incr,exit,idx,offo,toto,epo),sa) ==>
  ?p dv ov ep h.
    p = STRING #"%" (toString sd.cs_next_var) /\
    idx = STRING #"%" (toString (sd.cs_next_var + 1)) /\
    dv = STRING #"%" (toString (sd.cs_next_var + (if dyn then 4 else 2))) /\
    ov = STRING #"%" (toString (sd.cs_next_var + (if dyn then 5 else 3))) /\
    ep = STRING #"%" (toString (sd.cs_next_var + (if dyn then 7 else 4))) /\
    h = sd.cs_next_id + (if dyn then 9 else 6) /\
    offo = Var ov /\ epo = Var ep /\
    toto = Var (STRING #"%" (toString
      (sd.cs_next_var + (if dyn then 6 else 3)))) /\
    entry = fresh_label_output "iter_entry" sd.cs_next_label /\
    cond = fresh_label_output "iter_cond" (sd.cs_next_label + 1) /\
    bod = fresh_label_output "iter_body" (sd.cs_next_label + 2) /\
    incr = fresh_label_output "iter_incr" (sd.cs_next_label + 3) /\
    exit = fresh_label_output "iter_exit" (sd.cs_next_label + 4) /\
    declare_local cenv id et sd =
      (bc, sd with cs_next_var := sd.cs_next_var + 1) /\
    FLOOKUP bc.ce_vars id =
      SOME (PtrVar (Var p) (type_memory_bytes cenv et)) /\
    (!name. name <> id ==> FLOOKUP bc.ce_vars name = FLOOKUP cenv.ce_vars name) /\
    bc with <|ce_vars := cenv.ce_vars; ce_var_type := cenv.ce_var_type;
              ce_dynarray_capacity := cenv.ce_dynarray_capacity|> = cenv /\
    sa.cs_current_bb = bod /\
    sa.cs_current_insts =
      [mk_inst h MUL [Var idx; Lit (n2w stride)] [ov]] ++
      (if dyn then [mk_inst (h+1) ADD [Lit 1w; Var ov]
        [STRING #"%" (toString (sd.cs_next_var+6))]] else []) ++
      [mk_inst (h + (if dyn then 2 else 1)) ADD [Lit slot; toto] [ep]] /\
    sa.cs_next_var = sd.cs_next_var + (if dyn then 8 else 5) /\
    sa.cs_next_id = h + (if dyn then 3 else 2) /\
    sa.cs_next_label = sd.cs_next_label + 5 /\
    sa.cs_blocks =
      [<|bb_label := cond; bb_instructions :=
         [mk_inst (h-2) EQ [Var idx; lvo] [dv];
          mk_inst (h-1) JNZ [Var dv; Label exit; Label bod] []]|>;
       <|bb_label := entry; bb_instructions :=
         [mk_inst (sd.cs_next_id+2) ASSIGN [Lit 0w] [idx]] ++
         (if dyn then
           [mk_inst (sd.cs_next_id+3) GT [lvo; Lit (n2w cap)]
              [STRING #"%" (toString (sd.cs_next_var+2))];
            mk_inst (sd.cs_next_id+4) ISZERO
              [Var (STRING #"%" (toString (sd.cs_next_var+2)))]
              [STRING #"%" (toString (sd.cs_next_var+3))];
            mk_inst (sd.cs_next_id+5) ASSERT
              [Var (STRING #"%" (toString (sd.cs_next_var+3)))] []]
          else []) ++ [mk_inst (h-3) JMP [Label cond] []]|>;
       <|bb_label := sd.cs_current_bb; bb_instructions :=
         sd.cs_current_insts ++
         [mk_inst sd.cs_next_id ALLOCA
            [Lit (n2w (type_memory_bytes cenv et))] [p];
          mk_inst (sd.cs_next_id+1) JMP [Label entry] []]|>] ++ sd.cs_blocks
Proof
  strip_tac >>
  Cases_on `declare_local cenv id et sd` >>
  rename1 `declare_local cenv id et sd = (bc0,sd1)` >>
  drule_all declare_local_ptr >> strip_tac >>
  qpat_x_assum `_ sd = ((bc,entry,cond,bod,incr,exit,idx,offo,toto,epo),sa)` mp_tac >>
  Cases_on `dyn` >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  simp[emit_local_alloca_def, fresh_label_def, emit_inst_def, emit_op_def,
       emit_void_def, fresh_id_def, emit_def, new_block_def, fresh_var_def,
       comp_get_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       LET_THM] >> strip_tac >> gvs[] >>
  simp[GSYM arithmeticTheory.ADD_ASSOC] >> metis_tac[]
QED

(* Code cuts retain the copy's actual CFG, not the straight-line memory
   copy contract.  Capacity and per-child slot count remain independent. *)
Theorem for_storage_array_code:
  FLOOKUP cenv.ce_module_vars nid =
    SOME (if tr then TransientLoc slot else StorageLoc slot) /\
  cenv.ce_alloca_locals /\
  compile_stmt cenv lctx ty
    (For id et (Array (TopLevelName (ArrayT et bd) nid)) n stmts) st =
    ((),st') /\ fn_has_code st st' func ==>
  ?lvo sd bc p entry cond bod incr exit idx dv ov ep h sa sb0 sb1 sj nv.
    (if (case bd of Dynamic _ => T | Fixed _ => F) then
       compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca
         (if tr then LocTransient else LocStorage) (Lit slot)
     else return (Lit (n2w (bound_length bd)))) st = (lvo,sd) /\
    ci_mono st sd /\ same_blocks st sd /\
    p = STRING #"%" (toString sd.cs_next_var) /\
    idx = STRING #"%" (toString (sd.cs_next_var+1)) /\
    dv = STRING #"%" (toString (sd.cs_next_var+
      (case bd of Dynamic _ => 4 | Fixed _ => 2))) /\
    ov = STRING #"%" (toString (sd.cs_next_var+
      (case bd of Dynamic _ => 5 | Fixed _ => 3))) /\
    ep = STRING #"%" (toString (sd.cs_next_var+
      (case bd of Dynamic _ => 7 | Fixed _ => 4))) /\
    h = sd.cs_next_id+(case bd of Dynamic _ => 9 | Fixed _ => 6) /\
    declare_local cenv id et sd =
      (bc,sd with cs_next_var := sd.cs_next_var+1) /\
    FLOOKUP bc.ce_vars id =
      SOME (PtrVar (Var p) (type_memory_bytes cenv et)) /\
    (!name. name <> id ==> FLOOKUP bc.ce_vars name = FLOOKUP cenv.ce_vars name) /\
    bc with <|ce_vars := cenv.ce_vars; ce_var_type := cenv.ce_var_type;
              ce_dynarray_capacity := cenv.ce_dynarray_capacity|> = cenv /\
    entry = fresh_label_output "iter_entry" sd.cs_next_label /\
    cond = fresh_label_output "iter_cond" (sd.cs_next_label+1) /\
    bod = fresh_label_output "iter_body" (sd.cs_next_label+2) /\
    incr = fresh_label_output "iter_incr" (sd.cs_next_label+3) /\
    exit = fresh_label_output "iter_exit" (sd.cs_next_label+4) /\
    sa.cs_current_bb = bod /\
    sa.cs_current_insts =
      [mk_inst h MUL [Var idx; Lit (n2w (elem_size_in_location cenv
        (if tr then LocTransient else LocStorage) et))] [ov]] ++
      (case bd of Dynamic _ =>
         [mk_inst (h+1) ADD [Lit 1w; Var ov]
            [STRING #"%" (toString (sd.cs_next_var+6))]]
       | Fixed _ => []) ++
      [mk_inst (h+(case bd of Dynamic _ => 2 | Fixed _ => 1)) ADD
         [Lit slot; Var (STRING #"%" (toString (sd.cs_next_var+
           (case bd of Dynamic _ => 6 | Fixed _ => 3))))] [ep]] /\
    sa.cs_next_var = sd.cs_next_var+(case bd of Dynamic _ => 8 | Fixed _ => 5) /\
    sa.cs_next_id = h+(case bd of Dynamic _ => 3 | Fixed _ => 2) /\
    sa.cs_next_label = sd.cs_next_label+5 /\
    compile_iter_elem_copy cenv (Var ep) (Var p)
      (elem_size_in_location cenv (if tr then LocTransient else LocStorage) et)
      (if tr then LocTransient else LocStorage) T et et sa = ((),sb0) /\
    sb0 = slot_copy_final sa (Var ep) (Var p)
      (elem_size_in_location cenv (if tr then LocTransient else LocStorage) et)
      (if tr then TLOAD else SLOAD) /\
    sb0.cs_current_bb = slot_copy_exit sa /\ sb0.cs_current_insts = [] /\
    sb0.cs_next_var = sa.cs_next_var+7 /\
    sb0.cs_next_id = sa.cs_next_id+12 /\
    sb0.cs_next_label = sa.cs_next_label+3 /\
    compile_stmts bc (InLoop exit incr) ty stmts sb0 = ((),sb1) /\
    ci_mono sb0 sb1 /\
    emit_jmp_if_not_terminated incr sb1 = ((),sj) /\
    sj.cs_next_var = sb1.cs_next_var /\
    (~block_is_terminated sb1 ==> sj.cs_current_insts = sb1.cs_current_insts ++
      [mk_inst sb1.cs_next_id JMP [Label incr] []]) /\
    cs_extends sd sa /\ cs_extends sa sb0 /\ cs_extends sb1 sj /\
    cs_extends sj st' /\
    fn_has_code st sd func /\ fn_has_code sd sa func /\
    fn_has_code sa sb0 func /\ fn_has_code sb0 sb1 func /\
    fn_has_code sb1 sj func /\ fn_has_code sj st' func /\
    nv = STRING #"%" (toString sj.cs_next_var) /\
    lookup_block cond func.fn_blocks =
      SOME <|bb_label := cond; bb_instructions :=
        [mk_inst (h-2) EQ [Var idx; lvo] [dv];
         mk_inst (h-1) JNZ [Var dv; Label exit; Label bod] []]|> /\
    lookup_block entry func.fn_blocks =
      SOME <|bb_label := entry; bb_instructions :=
        [mk_inst (sd.cs_next_id+2) ASSIGN [Lit 0w] [idx]] ++
        (case bd of Dynamic _ =>
          [mk_inst (sd.cs_next_id+3) GT [lvo; Lit (n2w (bound_length bd))]
            [STRING #"%" (toString (sd.cs_next_var+2))];
           mk_inst (sd.cs_next_id+4) ISZERO
            [Var (STRING #"%" (toString (sd.cs_next_var+2)))]
            [STRING #"%" (toString (sd.cs_next_var+3))];
           mk_inst (sd.cs_next_id+5) ASSERT
            [Var (STRING #"%" (toString (sd.cs_next_var+3)))] []]
         | Fixed _ => []) ++ [mk_inst (h-3) JMP [Label cond] []]|> /\
    lookup_block sd.cs_current_bb func.fn_blocks =
      SOME <|bb_label := sd.cs_current_bb; bb_instructions := sd.cs_current_insts ++
        [mk_inst sd.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv et))] [p];
         mk_inst (sd.cs_next_id+1) JMP [Label entry] []]|> /\
    lookup_block incr func.fn_blocks =
      SOME <|bb_label := incr; bb_instructions :=
        [mk_inst sj.cs_next_id ADD [Var idx; Lit 1w] [nv];
         mk_inst (sj.cs_next_id+1) ASSIGN [Var nv] [idx];
         mk_inst (sj.cs_next_id+2) JMP [Label cond] []]|> /\
    st'.cs_current_bb = exit /\ st'.cs_current_insts = []
Proof
  strip_tac >> drule_all for_storage_array_stages >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` kall_tac >>
  drule_all for_storage_array_prefix >> strip_tac >>
  dxrule compile_for_array_suffix >> strip_tac >>
  `ci_mono st sd /\ same_blocks st sd` by
    (qpat_x_assum `_ st = (lvo,sd)` mp_tac >>
     Cases_on `bd` >> Cases_on `tr` >>
     simp[compile_ptr_load_def, emit_op_def, emit_inst_def, fresh_var_def,
       fresh_id_def, emit_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, LET_THM] >> strip_tac >> gvs[] >>
     simp[ci_mono_def, cs_extends_same_block, same_blocks_def,
       IS_PREFIX_APPEND]) >>
  `cs_extends sd sa` by (irule array_prefix_extends >> simp[] >> metis_tac[]) >>
  `compile_iter_elem_copy cenv (Var ep) (Var p)
     (elem_size_in_location cenv (if tr then LocTransient else LocStorage) et)
     (if tr then LocTransient else LocStorage) T et et sa = ((),sb0)` by
    (qpat_x_assum `_ sa = ((),sb0)` mp_tac >> simp[]) >>
  `sb0 = slot_copy_final sa (Var ep) (Var p)
     (elem_size_in_location cenv (if tr then LocTransient else LocStorage) et)
     (if tr then TLOAD else SLOAD)` by
    (qpat_x_assum `_ sa = ((),sb0)` mp_tac >> simp[] >>
     Cases_on `tr` >>
     simp[compile_iter_elem_copy_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, compile_slot_to_memory_shape]) >>
  `ci_mono sb0 sb1` by
    (qspec_then `sb0` mp_tac (Q.SPECL [`bc`,`InLoop exit incr`,`ty`,`stmts`]
      (cj 2 compile_stmt_ci_mono)) >> simp[]) >>
  drule array_body_backedge >> strip_tac >>
  `cs_extends st sa` by metis_tac[ci_mono_def,cs_extends_trans] >>
  `cs_extends sa sb0 /\ cs_extends sb0 sb1` by
    (fs[ci_mono_def] >> simp[slot_copy_extends]) >>
  drule_all array_stages_code >> strip_tac >>
  `fn_has_code st sd func /\ fn_has_code sd sa func` by
    metis_tac[fn_has_code_split,ci_mono_def] >>
  `sb0.cs_current_bb = slot_copy_exit sa /\ sb0.cs_current_insts = [] /\
   sb0.cs_next_var = sa.cs_next_var+7 /\
   sb0.cs_next_id = sa.cs_next_id+12 /\
   sb0.cs_next_label = sa.cs_next_label+3` by simp[slot_copy_final_def] >>
  qexistsl_tac [`lvo`,`sd`,`bc`,`p`,`entry`,`cond`,`bod`,`incr`,`exit`,
    `idx`,`dv`,`ov`,`ep`,`h`,`sa`,`sb0`,`sb1`,`sj`,`nv`] >>
  Cases_on `bd` >| [(gvs[] >> rpt conj_tac
   >- (irule array_emitted_block_lookup >> simp[] >>
       qexistsl_tac [`TAKE 3 sa.cs_blocks`,`sd`,`sa`] >> simp[])
   >- (irule array_emitted_block_lookup >> simp[] >>
       qexistsl_tac [`TAKE 3 sa.cs_blocks`,`sd`,`sa`] >>
       conj_tac >- (qpat_assum `sa.cs_blocks = _`
         (fn th => simp[th,NoAsms])) >>
       conj_tac >- (qpat_assum `sa.cs_blocks = _`
         (fn th => pure_rewrite_tac[th]) >>
         CONV_TAC (RAND_CONV (SIMP_CONV (srw_ss()) [listTheory.TAKE_compute])) >>
         pure_rewrite_tac[pred_setTheory.IN_INSERT,pred_setTheory.NOT_IN_EMPTY] >>
         disj2_tac >> disj1_tac >> REFL_TAC) >>
       simp[])
   >- (irule array_emitted_block_lookup >> simp[] >>
       qexistsl_tac [`TAKE 3 sa.cs_blocks`,`sd`,`sa`] >>
       conj_tac >- (qpat_assum `sa.cs_blocks = _`
         (fn th => simp[th,NoAsms])) >>
       conj_tac >- (qpat_assum `sa.cs_blocks = _`
         (fn th => pure_rewrite_tac[th]) >>
         CONV_TAC (RAND_CONV (SIMP_CONV (srw_ss()) [listTheory.TAKE_compute])) >>
         pure_rewrite_tac[pred_setTheory.IN_INSERT,pred_setTheory.NOT_IN_EMPTY] >>
         disj2_tac >> disj2_tac >> disj1_tac >> REFL_TAC) >> simp[])
   >> irule array_emitted_block_lookup >> simp[] >>
   qexistsl_tac [`TAKE 2 st'.cs_blocks`,`sj`,`st'`] >> simp[]), (gvs[] >> rpt conj_tac
   >- (irule array_emitted_block_lookup >> simp[] >>
       qexistsl_tac [`TAKE 3 sa.cs_blocks`,`sd`,`sa`] >> simp[])
   >- (irule array_emitted_block_lookup >> simp[] >>
       qexistsl_tac [`TAKE 3 sa.cs_blocks`,`sd`,`sa`] >>
       conj_tac >- (qpat_assum `sa.cs_blocks = _`
         (fn th => simp[th,NoAsms])) >>
       conj_tac >- (qpat_assum `sa.cs_blocks = _`
         (fn th => pure_rewrite_tac[th]) >>
         CONV_TAC (RAND_CONV (SIMP_CONV (srw_ss()) [listTheory.TAKE_compute])) >>
         pure_rewrite_tac[pred_setTheory.IN_INSERT,pred_setTheory.NOT_IN_EMPTY] >>
         disj2_tac >> disj1_tac >> REFL_TAC) >>
       simp[])
   >- (irule array_emitted_block_lookup >> simp[] >>
       qexistsl_tac [`TAKE 3 sa.cs_blocks`,`sd`,`sa`] >>
       conj_tac >- (qpat_assum `sa.cs_blocks = _`
         (fn th => simp[th,NoAsms])) >>
       conj_tac >- (qpat_assum `sa.cs_blocks = _`
         (fn th => pure_rewrite_tac[th]) >>
         CONV_TAC (RAND_CONV (SIMP_CONV (srw_ss()) [listTheory.TAKE_compute])) >>
         pure_rewrite_tac[pred_setTheory.IN_INSERT,pred_setTheory.NOT_IN_EMPTY] >>
         disj2_tac >> disj2_tac >> disj1_tac >> REFL_TAC) >> simp[])
   >> irule array_emitted_block_lookup >> simp[] >>
   qexistsl_tac [`TAKE 2 st'.cs_blocks`,`sj`,`st'`] >> simp[])]
QED

(* Joint execution and interpretation for the existing storage-copy destination. *)

Theorem for_storage_element_copy_run:
  !ce tyarr ann nid ca place cb cenv typ tr src root n cs sb lo ctx func
   PG s G tn w (d:bytes32) regions.
    compile_expr ce tyarr (TopLevelName ann nid) ca = (place,cb) /\
    compile_iter_elem_copy cenv src (Var root) n (slot_loc tr) T
      typ typ cs = ((),sb) /\
    compile_slot_to_memory src (Var root) n (slot_loc tr) cs =
      (slot_copy_body cs,sb) /\
    eval_operand src s = SOME w /\ lookup_var root s = SOME d /\
    op_taint tn src = {} /\
    slot_copy_external cs src /\ slot_copy_external cs (Var root) /\
    ptr_covers G tn root s (32*n) /\
    n < 2**256 /\ w2n d+32*n < 2**256 /\
    w2n d+32*n <= s.vs_alloca_next /\
    create_memory_snapshot regions s /\
    EVERY (\(off,bs). off+LENGTH bs <= LENGTH s.vs_memory /\
      (off+LENGTH bs <= w2n d \/ w2n d+32*n <= off)) regions /\
    s.vs_current_bb = cs.cs_current_bb /\
    s.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~s.vs_halted /\
    lookup_block cs.cs_current_bb func.fn_blocks =
      SOME <|bb_label := cs.cs_current_bb;
             bb_instructions := cs.cs_current_insts ++ slot_copy_init_insts cs|> /\
    lookup_block (slot_copy_cond cs) func.fn_blocks =
      SOME <|bb_label := slot_copy_cond cs;
             bb_instructions := slot_copy_cond_insts cs n|> /\
    lookup_block (slot_copy_body cs) func.fn_blocks =
      SOME <|bb_label := slot_copy_body cs;
             bb_instructions := slot_copy_body_insts cs src (Var root)
               (if tr then TLOAD else SLOAD)|> /\
    allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
    ?z Gf tnf.
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK z,Gf,tnf)) /\
      z.vs_current_bb = slot_copy_exit cs /\ z.vs_inst_idx = 0 /\
      z.vs_current_bb = sb.cs_current_bb /\
      z.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~z.vs_halted /\
      slot_copy_inv cs (if tr then TLOAD else SLOAD) s w d n regions n z /\
      slot_copy_ghost_inv cs (if tr then TLOAD else SLOAD)
        w d root n G tn n Gf tnf z /\
      slot_copy_runtime_frame cs d n s z /\
      allocas_from lo z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
      z.vs_alloca_next = s.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks =
    SOME <|bb_label := cs.cs_current_bb;
           bb_instructions := cs.cs_current_insts ++ slot_copy_init_insts cs|>`
    by simp[] >>
  qmatch_asmsub_abbrev_tac `lookup_block s.vs_current_bb func.fn_blocks = SOME initbb` >>
  `initbb.bb_instructions = cs.cs_current_insts ++ slot_copy_init_insts cs`
    by simp[Abbr `initbb`] >>
  drule_all toplevel_slot_copy_initial_joint >>
  disch_then (qspecl_then [`w`, `if tr then TLOAD else SLOAD`, `PG`]
    strip_assume_tac) >>
  qabbrev_tac `h = slot_copy_initial cs s` >>
  `slot_copy_runtime_frame cs d 0 s h` by
    simp[Abbr `h`, slot_copy_runtime_frame_initial] >>
  `~h.vs_halted /\ h.vs_current_bb = slot_copy_cond cs /\
   h.vs_inst_idx = 0 /\ h.vs_alloca_next = s.vs_alloca_next` by
    simp[Abbr `h`, slot_copy_initial_def, jump_to_def, update_var_def] >>
  `op_taint tn1 src = {}` by metis_tac[copy_ghost_external_taint] >>
  qmatch_asmsub_abbrev_tac `lookup_block (slot_copy_cond cs) func.fn_blocks = SOME condbb` >>
  qmatch_asmsub_abbrev_tac `lookup_block (slot_copy_body cs) func.fn_blocks = SOME bodybb` >>
  `condbb.bb_instructions = slot_copy_cond_insts cs n /\
   bodybb.bb_instructions = slot_copy_body_insts cs src (Var root)
     (if tr then TLOAD else SLOAD)` by simp[Abbr `condbb`, Abbr `bodybb`] >>
  `0 <= n /\ w2n d+32*n <= h.vs_alloca_next` by simp[] >>
  Q.SUBGOAL_THEN `(if tr then TLOAD else SLOAD) = SLOAD \/
    (if tr then TLOAD else SLOAD) = TLOAD` assume_tac
    >- (Cases_on `tr` >> simp[]) >>
  drule_all toplevel_slot_copy_joint_finish_framed >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `~t.vs_halted` by
    (qpat_x_assum `slot_copy_runtime_frame cs d n s t` mp_tac >>
     simp[slot_copy_runtime_frame_def] >> strip_tac >>
     drule copy_static_fields >> simp[]) >>
  Q.SUBGOAL_THEN `slot_loc tr = LocStorage \/ slot_loc tr = LocTransient` assume_tac
    >- (Cases_on `tr` >> simp[slot_loc_def]) >>
  drule_all compile_slot_to_memory_boundary >> strip_tac >>
  qexistsl [`t`, `Gf`, `tnf`] >> simp[] >>
  rpt gen_tac >>
  qpat_x_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) _ _`
    (qspecl_then [`D`, `explicit`]
      (mp_then Any mp_tac gas_origin_ptr_path_append)) >>
  disch_then (qspecl_then [`h`, `G1`, `tn1`, `[]`] mp_tac) >>
  simp[] >> disch_then irule >> simp[]
QED

Theorem for_storage_observed_child_holds:
  !cx tr typ r slot mid u vt H ctx func cenv ee s.
    storage_holds cx tr typ r slot mid u /\
    evaluate_type (get_tenv cx) typ = SOME vt /\
    well_formed_type_value vt /\
    stmt_state_rel H ctx func cenv cx ee s /\
    storage_place_observed H (StoragePlace tr slot vt) /\
    regions_consistent (FST H) /\
    storage_well_formed_on cx ee (FST H) /\
    0 < type_slot_size vt ==>
    storage_holds cx tr typ (PlaceR (StoragePlace tr slot vt)) slot ee s
Proof
  rpt strip_tac >>
  `storage_read_live H tr (get_storage cx ee tr) slot vt` by
    (irule storage_place_observed_read_live >> simp[]) >>
  drule_all aug_place_observed_slots_in_range >> strip_tac >>
  drule_all live_storage_holds_current >> simp[]
QED

(* The endpoint is supplied by the joint execution adapter. Semantic ownership
   is refreshed at its current source entry, not saved from iterator evaluation. *)
Theorem for_storage_element_copy_post:
  !cx typ ty tv tag ptr tr src root n nb id cs cenv es s G tn w
   (d:bytes32) regions z Gf tnf.
    evaluate_type (get_tenv cx) typ = SOME ty /\
    n = type_slot_size ty /\
    storage_holds cx tr typ tv w es s /\
    ptr_vv_ok cx typ tv (LocatedValue tag ptr) es G tn s /\
    ptr.ptr_location = slot_loc tr /\ ptr.ptr_operand = src /\
    eval_operand src s = SOME w /\
    local_region cenv es.scopes s id (w2n d) nb /\ 32*n <= nb /\
    (!aid off sz.
       FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
       aid < cs.cs_next_id /\
       (!name b sz'. local_region cenv es.scopes s name b sz' ==>
          off+sz <= b \/ b+sz' <= off) ==>
       off+sz <= w2n d \/ w2n d+32*n <= off) /\
    slot_copy_inv cs (if tr then TLOAD else SLOAD)
      s w d n regions n z /\
    slot_copy_ghost_inv cs (if tr then TLOAD else SLOAD)
      w d root n G tn n Gf tnf z /\
    slot_copy_runtime_frame cs d n s z ==>
    ?v.
      read_result cx tv es = (INL v,es) /\
      (!mem. mem_agree_outside tnf.t_mem z.vs_memory mem ==>
        val_in_memory ty v (w2n d) mem) /\
      z.vs_alloca_next = s.vs_alloca_next /\ z.vs_allocas = s.vs_allocas /\
      ptr_covers Gf tnf root z (32*n) /\
      create_memory_snapshot regions z /\
      (!j. j<n ==> mem_word_at (w2n d+32*j) z.vs_memory =
        slot_copy_word (if tr then TLOAD else SLOAD) s (w+n2w j)) /\
      (!j b. j<n /\ b<32 /\ w2n d+32*j+b IN tnf.t_mem ==>
        b IN key_taint (if tr then tn.t_trans else tn.t_stor) (w+n2w j)) /\
      (!op. slot_copy_external cs op ==>
        eval_operand op z = eval_operand op s) /\
      (!x. slot_copy_external cs (Var x) ==>
        FLOOKUP Gf x = FLOOKUP G x /\
        op_taint tnf (Var x) = op_taint tn (Var x)) /\
      (!a k. a+k <= w2n d \/ w2n d+32*n <= a ==>
        mem_bytes_at a k z.vs_memory = mem_bytes_at a k s.vs_memory) /\
      (!a. ~(w2n d <= a /\ a < w2n d+32*n) ==>
        (a IN tnf.t_mem <=> a IN tn.t_mem)) /\
      (!aid off sz i.
        FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
        aid < cs.cs_next_id /\
        (!name b sz'. local_region cenv es.scopes s name b sz' ==>
          off+sz <= b \/ b+sz' <= off) /\ off<=i /\ i<off+sz ==>
        mem_bytes_at i 1 z.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tnf.t_mem <=> i IN tn.t_mem))
Proof
  rpt gen_tac >> strip_tac >>
  drule copy_prefix_words >> strip_tac >>
  drule copy_prefix_taint >> strip_tac >>
  `!j b. j<n /\ b<32 /\ w2n d+32*j+b IN tnf.t_mem ==>
    b IN key_taint (if tr then tn.t_trans else tn.t_stor) (w+n2w j)` by
    (Cases_on `tr` >> gvs[]) >>
  `?v. read_result cx tv es = (INL v,es) /\
    !mem. mem_agree_outside tnf.t_mem z.vs_memory mem ==>
      val_in_memory ty v (w2n d) mem` by
    (irule unwrap_storage_copied_robust >>
     goal_assum (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
     qexistsl [`tr`, `w`] >> gvs[]) >>
  qexists `v` >>
  gvs[slot_copy_inv_def, slot_copy_ghost_inv_def, slot_copy_runtime_frame_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  `off+sz <= w2n d \/ 32*type_slot_size ty+w2n d <= off` by
    (qpat_x_assum `!aid off sz. _` irule >> metis_tac[]) >>
  `~(w2n d <= i /\ i < 32*type_slot_size ty+w2n d)` by decide_tac >>
  metis_tac[]
QED

(* Recover a local predicate abbreviation from the expanded statement. *)
fun abbrev_lambda_tac name arity existentials =
  Q_TAC (fn pattern => W (fn (_, goal) =>
    let
      fun matches tm =
        let
          val (args, body) = strip_abs tm
          val (witnesses, core) = strip_exists body
        in
          length args = arity andalso length witnesses = existentials andalso
          can (match_term pattern) core
        end
      val tm = find_term matches goal
    in
      markerLib.ABBREV_TAC (mk_eq (mk_var (name, type_of tm), tm))
    end));

(* Exhausted captured storage iterator: the only instructions are scalar EQ
   and the taken exit branch. The frame stays anchored at the original entry. *)
(* The exhausted guard only needs the saved counter/length equality and the
   exterior frame; it need not know how the iterator obtained either value. *)
Theorem for_storage_array_nil_core:
  !DF lo d ctx func cx lctx c0 e0 sa0 sb s0 G0 tn0 st0 explicit PG dv eid
    exit blabel bb cond idx lvo es s G tn len.
    local_ptrs_reserved c0 sa0 /\
    (!x sz. c0.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
    (!x sz. c0.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
    (!x. not_fresh_at sa0 x ==> x <> dv) /\
    sa0.cs_next_var <= sb.cs_next_var /\ sb.cs_current_bb = exit /\
    sb.cs_current_insts = [] /\ ~block_is_terminated sb /\
    lookup_block cond func.fn_blocks = SOME bb /\
    get_instruction bb 0 = SOME (mk_inst eid EQ [Var idx; lvo] [dv]) /\
    get_instruction bb 1 =
      SOME (mk_inst (eid + 1) JNZ [Var dv; Label exit; Label blabel] []) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      s.vs_current_bb = cond /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
      lookup_var idx s = SOME (n2w len) /\ FLOOKUP G idx = NONE /\
      op_taint tn (Var idx) = {} /\ eval_operand lvo s = SOME (n2w len) /\
      op_taint tn lvo = {} /\ op_prov G lvo = NONE /\
      cenv_top_ext c0 c0 es.scopes /\ stmt_state_rel H ctx func c0 cx es s /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d c0 cx es G tn s /\
      return_buf_frame d c0 sa0 s /\ return_buf_sep d c0 es s /\
      (\c ee s G tn.
        alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
        s0.vs_alloca_next <= s.vs_alloca_next /\
        (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
               lookup_var x s = SOME w) /\
        (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
        (!x. not_fresh_at sa0 x ==> FLOOKUP G x = FLOOKUP G0 x /\
             op_taint tn (Var x) = op_taint tn0 (Var x)) /\
        alloca_frame c0 e0 sa0 s0 c ee s /\
        !aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
          aid < sa0.cs_next_id /\
          (!name b sz'. local_region c0 e0.scopes s0 name b sz' ==>
            off + sz <= b \/ b + sz' <= off) /\ off <= i /\
          i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem) c0 es s G tn) ==>
    ?t G1 tn1. !H.
      valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
        (OK t,G1,tn1) /\
      (\H ee G tn t.
         ?c. stmt_lands lctx sb (INL ()) t /\ ~t.vs_halted /\
             ~block_is_terminated sb /\ c = c0 /\
             cenv_top_ext c0 c ee.scopes /\ stmt_state_rel H ctx func c cx ee t /\
             storage_well_formed_on cx ee (FST H) /\
             return_buf_frame d c sb t /\ return_buf_sep d c ee t /\
             ghost_inv_at (DF H) lo d c cx ee G tn t /\
             (\c ee s G tn.
               alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
               s0.vs_alloca_next <= s.vs_alloca_next /\
               (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
                      lookup_var x s = SOME w) /\
               (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
               (!x. not_fresh_at sa0 x ==> FLOOKUP G x = FLOOKUP G0 x /\
                    op_taint tn (Var x) = op_taint tn0 (Var x)) /\
               alloca_frame c0 e0 sa0 s0 c ee s /\
               !aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
                 aid < sa0.cs_next_id /\
                 (!name b sz'. local_region c0 e0.scopes s0 name b sz' ==>
                   off + sz <= b \/ b + sz' <= off) /\ off <= i /\
                 i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem) c ee t G tn)
        H (es with gas_obs := []) G1 tn1 t
Proof
  rpt gen_tac >>
  abbrev_lambda_tac "Fr" 5 0 `alloca_history func s /\ _` >>
  abbrev_lambda_tac "Done" 5 1 `stmt_lands lctx sb (INL ()) t /\ _` >>
  rpt strip_tac >>
  qabbrev_tac `i = mk_inst eid EQ [Var idx;lvo] [dv]` >>
  qabbrev_tac `u = update_var dv 1w s` >>
  qabbrev_tac `G1 = step_prov PG G i u` >>
  qabbrev_tac `tn1 = step_taint i s u tn` >>
  qexistsl [`jump_to exit u`, `G1`, `tn1`] >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _` drule >> BETA_TAC >> strip_tac >>
  `Fr c0 es s G tn` by simp[Abbr `Fr`] >>
  `allocas_from lo s` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ _ _ _ _`
      (mp_tac o REWRITE_RULE [ghost_inv_at_def]) >> simp[]) >>
  `not_local_ptr c0 es.scopes dv` by
    (simp[not_local_ptr_def] >> metis_tac[local_ptrs_reserved_def]) >>
  `tn1 = tn with t_var := tn.t_var |+ (dv,{})` by
    simp[Abbr `tn1`, Abbr `i`, Abbr `u`, membership_scalar_ghost_frame] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by
    (qpat_x_assum `Fr c0 es s G tn` mp_tac >> simp[NoAsms, Abbr `Fr`]) >>
  conj_tac >- suspend "nil_path" >>
  suspend "nil_post"
QED

Resume for_storage_array_nil_core[nil_path]:
  `step_inst_base i s = OK u` by
    (gvs[Abbr `i`, Abbr `u`, step_inst_base_opcode_eqs,
          exec_pure2_def, eval_operand_def, bool_to_word_def]) >>
  `ptr_inst_ok (DF H) lo 0 ctx func G tn i s` by
    suspend "nil_compare_checks" >>
  `inst_mem_below_frontier i s /\ inst_dload_in_section i s /\
   i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode` by
    simp[Abbr `i`, mk_inst_def, is_terminator_def,
         inst_mem_below_frontier_def, inst_dload_in_section_def,
         source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  `gas_origin_ptr_edge (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (u with vs_inst_idx := SUC s.vs_inst_idx),G1,tn1)` by
    (`lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx = SOME i` by simp[] >>
     drule_all straight_line_origin_ptr_edge >>
     simp[Abbr `G1`, Abbr `tn1`, Abbr `i`, mk_inst_def]) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
     (u with vs_inst_idx := SUC s.vs_inst_idx,G1,tn1) []
     (OK (jump_to exit u),G1,tn1)` by suspend "nil_branch" >>
  drule (cj 2 gas_origin_ptr_path_rules) >> disch_then drule >> simp[]
QED

Resume for_storage_array_nil_core[nil_compare_checks]:
  simp[Abbr `i`, ptr_inst_ok_def, access_ok_def, taint_ok_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def, mk_inst_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke, Abbr `u`, update_var_def] >>
  rpt strip_tac >> gvs[op_prov_def, FLOOKUP_DEF] >> metis_tac[]
QED

Resume for_storage_array_nil_core[nil_branch]:
  qmatch_goalsub_abbrev_tac `gas_origin_ptr_path _ (v,G1,tn1) _ _` >>
  `lookup_block v.vs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb v.vs_inst_idx =
     SOME (mk_inst (eid+1) JNZ [Var dv;Label exit;Label blabel] []) /\
   ~v.vs_halted /\ eval_operand (Var dv) v = SOME 1w /\
   op_taint tn1 (Var dv) = {} /\ allocas_from lo v /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp v)` by
    simp[Abbr `v`, Abbr `u`, update_var_def, eval_operand_def,
         lookup_var_def, allocas_from_def, allocas_below_fmp_def,
         op_taint_def, FLOOKUP_UPDATE] >>
  drule_all decoderNavigationPtrTheory.jnz_origin_ptr_path >>
  simp[Abbr `v`, jump_to_def]
QED

Resume for_storage_array_nil_core[nil_post]:
  `!x. not_fresh_at sa0 x ==>
     lookup_var x (jump_to exit u) = lookup_var x s /\
     FLOOKUP G1 x = FLOOKUP G x /\
     op_taint tn1 (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> `x <> dv` by metis_tac[] >>
     simp[Abbr `u`, Abbr `G1`, Abbr `i`, jump_to_def, update_var_def,
          lookup_var_def, step_prov_def, out_prov_def, set_prov_def,
          mk_inst_def, FLOOKUP_DRESTRICT, op_taint_def, FLOOKUP_UPDATE]) >>
  `ghost_inv_at (DF H) lo d c0 cx (es with gas_obs := []) G1 tn1
     (jump_to exit u)` by
    (irule ghost_inv_at_exterior_frame >>
     goal_assum (drule_at (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)) >>
     qexists `sa0` >> simp[Abbr `u`, jump_to_def, update_var_def]) >>
  `stmt_state_rel H ctx func c0 cx (es with gas_obs := []) (jump_to exit u)` by
    (simp[stmt_state_rel_jump_to, Abbr `u`] >>
     irule stmt_state_rel_update_var >> simp[]) >>
  `return_buf_frame d c0 sb (jump_to exit u)` by
    (irule return_buf_frame_frame >>
     goal_assum (drule_at (Pat `return_buf_frame _ _ _ _`)) >>
     simp[Abbr `u`, jump_to_def, update_var_def] >> metis_tac[]) >>
  `return_buf_sep d c0 (es with gas_obs := []) (jump_to exit u)` by
    suspend "nil_sep" >>
  `Fr c0 (es with gas_obs := []) (jump_to exit u) G1 tn1` by
    suspend "nil_frame" >>
  `storage_well_formed_on cx (es with gas_obs := []) (FST H)` by
    (qpat_x_assum `storage_well_formed_on _ _ _` mp_tac >>
     simp[NoAsms, vyperStorageFootprintTheory.storage_well_formed_on_def,
          stmtSimAppendStorageComposeTheory.get_storage_gas_obs]) >>
  simp[Abbr `Done`, stmt_lands_def] >>
  gvs[Abbr `u`, jump_to_def, update_var_def]
QED

Resume for_storage_array_nil_core[nil_sep]:
  simp[return_buf_sep_gas_obs, return_buf_sep_jump] >>
  `!name b sz. local_region c0 es.scopes u name b sz <=>
               local_region c0 es.scopes s name b sz` by
    (rpt gen_tac >> irule local_region_lookup_cong >> rpt strip_tac >>
     rename1 `lookup_var q u = lookup_var q s` >>
     `q <> dv` by
       (strip_tac >> qpat_assum `not_local_ptr c0 es.scopes dv`
          (mp_tac o CONJUNCT1 o REWRITE_RULE [not_local_ptr_def]) >>
        disch_then (drule_then mp_tac) >> simp[]) >>
     simp[Abbr `u`, update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  Cases_on `d` >- simp[return_buf_sep_def] >>
  rename1 `return_buf_sep (SOME buf) _ _ _` >> PairCases_on `buf` >>
  qpat_x_assum `return_buf_sep (SOME _) c0 es s` mp_tac >>
  pure_rewrite_tac[return_buf_sep_def] >>
  simp[allocas_from_def, Abbr `u`, update_var_def]
QED

Resume for_storage_array_nil_core[nil_frame]:
  qpat_x_assum `Fr c0 es s G tn` mp_tac >> simp[Abbr `Fr`] >> strip_tac >>
  `alloca_frame c0 e0 sa0 s0 c0 es u` by
    (simp[Abbr `u`] >> irule alloca_frame_update_var >> simp[]) >>
  `alloca_frame c0 e0 sa0 s0 c0 es (jump_to exit u)` by
    (irule alloca_frame_same_state >> goal_assum (drule_at Any) >> simp[jump_to_def]) >>
  `alloca_history func (jump_to exit u)` by
    (irule alloca_history_jump >> simp[Abbr `u`, jump_to_def, update_var_def] >>
     qexists `s` >> simp[]) >>
  simp[] >>
  conj_tac >-
    (gvs[Abbr `u`, jump_to_def, update_var_def, allocas_below_fmp_def] >> metis_tac[]) >>
  simp[Abbr `u`, jump_to_def, update_var_def] >>
  conj_tac
  >- (rpt strip_tac >> `x <> dv` by metis_tac[] >>
      qpat_x_assum `!x. not_fresh_at sa0 x ==> FLOOKUP G x = _ /\ _`
        (qspec_then `x` mp_tac) >> simp[op_taint_def, FLOOKUP_UPDATE]) >>
  first_assum ACCEPT_TAC
QED

Finalise for_storage_array_nil_core

Theorem for_storage_array_nil_full:
  !DF lo d ctx func cx lctx c0 e0 sa0 sb s0 G0 tn0 tr slot dst tyv typ bd vs
      len nb id env p idx cond lvo sd body st0 ok explicit PG dv eid exit
      blabel bb.
    local_ptrs_reserved c0 sa0 /\
    (!x sz. c0.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
    (!x sz. c0.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
    (!x. not_fresh_at sa0 x ==> x <> dv) /\
    sa0.cs_next_var <= sb.cs_next_var /\ sb.cs_current_bb = exit /\
    sb.cs_current_insts = [] /\ ~block_is_terminated sb /\
    lookup_block cond func.fn_blocks = SOME bb /\
    get_instruction bb 0 = SOME (mk_inst eid EQ [Var idx; lvo] [dv]) /\
    get_instruction bb 1 =
    SOME (mk_inst (eid + 1) JNZ [Var dv; Label exit; Label blabel] []) ==>
    !es s G tn.
      ~s.vs_halted /\ storage_trace_domain cx st0 es.storage_trace /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
           (\H rs ee G tn s.
              ?k off.
                k <= len /\ len = LENGTH vs /\ len <= bound_length bd /\
                vs =
                GENLIST
                  (\j.
                     PlaceR
                       (StoragePlace tr
                          ((case bd of
                              Fixed v => slot
                            | Dynamic v1 => slot + 1w) +
                           n2w (j * type_slot_size tyv)) tyv)) len /\
                rs = DROP k vs /\ slot = n2w off /\
                MEM (StorageRoot tr off (ArrayTV tyv bd)) ee.storage_trace /\
                evaluate_type (get_tenv cx) typ = SOME tyv /\
                well_formed_type_value tyv /\ s.vs_current_bb = cond /\
                s.vs_inst_idx = 0 /\ ~s.vs_halted /\
                lookup_var idx s = SOME (n2w k) /\ FLOOKUP G idx = NONE /\
                op_taint tn (Var idx) = {} /\
                eval_operand lvo s = SOME (n2w len) /\ op_taint tn lvo = {} /\
                op_prov G lvo = NONE /\
                eval_operand (Lit slot) s = SOME slot /\
                op_taint tn (Lit slot) = {} /\ lookup_var p s = SOME dst /\
                FLOOKUP s.vs_allocas sd.cs_next_id = SOME (w2n dst,nb) /\
                ptr_covers G tn p s nb /\ 32 * type_slot_size tyv <= nb /\
                w2n dst + nb < 2 ** 256 /\ w2n dst + nb <= s.vs_alloca_next /\
                (!name b sz.
                   local_region c0 ee.scopes s name b sz ==>
                   w2n dst + nb <= b \/ b + sz <= w2n dst) /\
                lookup_scopes id ee.scopes = NONE /\
                expr_sim_inv c0 cx env ee /\ ce_locals_declared c0 env /\
                locals_alloc_ok c0 env /\ cenv_top_ext c0 c0 ee.scopes /\
                stmt_state_rel H ctx func c0 cx ee s /\
                storage_well_formed_on cx ee (FST H) /\
                ghost_inv_at (DF H) lo d c0 cx ee G tn s /\
                return_buf_frame d c0 sa0 s /\ ret_pc_ok c0 sa0 s /\
                return_buf_sep d c0 ee s /\
                (k <> 0 ==> body_stmts_full_ok cx body) /\
                (\c ee s G tn.
                   alloca_history func s /\
                   (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
                   s0.vs_alloca_next <= s.vs_alloca_next /\
                   (!x w.
                      not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
                      lookup_var x s = SOME w) /\
                   (!aid b.
                      FLOOKUP s0.vs_allocas aid = SOME b ==>
                      FLOOKUP s.vs_allocas aid = SOME b) /\
                   (!x. not_fresh_at sa0 x ==>
                        FLOOKUP G x = FLOOKUP G0 x /\
                        op_taint tn (Var x) = op_taint tn0 (Var x)) /\
                   alloca_frame c0 e0 sa0 s0 c ee s /\
                   !aid off sz i.
                     FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
                     aid < sa0.cs_next_id /\
                     (!name b sz'.
                        local_region c0 e0.scopes s0 name b sz' ==>
                        off + sz <= b \/ b + sz' <= off) /\ off <= i /\
                     i < off + sz /\ i IN tn.t_mem ==>
                     i IN tn0.t_mem) c0 ee s G tn) H [] es G tn s) /\
      gas_admissible (eval_for cx tyv id body []) ok es ==>
      ?t G1 tn1. !H.
        valid_horizon cx st0 H es.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
          (OK t,G1,tn1) /\
        (\H ee G tn t.
           ?c. stmt_lands lctx sb (INL ()) t /\ ~t.vs_halted /\
               ~block_is_terminated sb /\ c = c0 /\
               cenv_top_ext c0 c ee.scopes /\
               stmt_state_rel H ctx func c cx ee t /\
               storage_well_formed_on cx ee (FST H) /\
               return_buf_frame d c sb t /\ return_buf_sep d c ee t /\
               ghost_inv_at (DF H) lo d c cx ee G tn t /\
               (\c ee s G tn.
                  alloca_history func s /\
                  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
                  s0.vs_alloca_next <= s.vs_alloca_next /\
                  (!x w.
                     not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
                     lookup_var x s = SOME w) /\
                  (!aid b.
                     FLOOKUP s0.vs_allocas aid = SOME b ==>
                     FLOOKUP s.vs_allocas aid = SOME b) /\
                  (!x. not_fresh_at sa0 x ==>
                       FLOOKUP G x = FLOOKUP G0 x /\
                       op_taint tn (Var x) = op_taint tn0 (Var x)) /\
                  alloca_frame c0 e0 sa0 s0 c ee s /\
                  !aid off sz i.
                    FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
                    aid < sa0.cs_next_id /\
                    (!name b sz'.
                       local_region c0 e0.scopes s0 name b sz' ==>
                       off + sz <= b \/ b + sz' <= off) /\ off <= i /\
                    i < off + sz /\ i IN tn.t_mem ==>
                    i IN tn0.t_mem) c ee t G tn) H (es with gas_obs := []) G1
          tn1 t
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  irule for_storage_array_nil_core >>
  simp[] >> qexistsl [`bb`,`blabel`,`cond`,`dv`,`eid`,`idx`,`len`,`lvo`] >> simp[] >>
  conj_tac >- metis_tac[] >> qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _` drule >> BETA_TAC >>
  strip_tac >>
  `k = len` by
    (qpat_assum `[] = DROP k vs` (mp_tac o SYM) >>
     rewrite_tac[DROP_EQ_NIL] >> decide_tac) >>
  qpat_x_assum `k = len` SUBST_ALL_TAC >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* The captured length is a scalar, not the iterator's located pointer. *)
Theorem for_storage_array_length_full:
  !DF lo d ctx func cx c0 e0 sa0 s0 G0 tn0 tr slot tyv typ bd vs len id env st0
      explicit PG saL sbL lvo out ptr ann ee s G tn.
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
         (\H ee s G tn.
            ?off.
              len = LENGTH vs /\ len <= bound_length bd /\
              vs =
              GENLIST
                (\j.
                   PlaceR
                     (StoragePlace tr
                        ((case bd of Fixed v => slot | Dynamic v1 => slot + 1w) +
                         n2w (j * type_slot_size tyv)) tyv)) len /\
              slot = n2w off /\
              MEM (StorageRoot tr off (ArrayTV tyv bd)) ee.storage_trace /\
              evaluate_type (get_tenv cx) typ = SOME tyv /\
              well_formed_type_value tyv /\
              lookup_scopes id ee.scopes = NONE /\ expr_sim_inv c0 cx env ee /\
              ce_locals_declared c0 env /\ locals_alloc_ok c0 env /\
              cenv_top_ext c0 c0 ee.scopes /\
              stmt_state_rel H ctx func c0 cx ee s /\
              storage_well_formed_on cx ee (FST H) /\
              ghost_inv_at (DF H) lo d c0 cx ee G tn s /\
              return_buf_frame d c0 sa0 s /\ ret_pc_ok c0 sa0 s /\
              (\c ee s G tn.
                 alloca_history func s /\
                 (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
                 s0.vs_alloca_next <= s.vs_alloca_next /\
                 (!x w.
                    not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
                    lookup_var x s = SOME w) /\
                 (!aid b.
                    FLOOKUP s0.vs_allocas aid = SOME b ==>
                    FLOOKUP s.vs_allocas aid = SOME b) /\
                 (!x. not_fresh_at sa0 x ==>
                      FLOOKUP G x = FLOOKUP G0 x /\
                      op_taint tn (Var x) = op_taint tn0 (Var x)) /\
                 alloca_frame c0 e0 sa0 s0 c ee s /\
                 !aid off sz i.
                   FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
                   aid < sa0.cs_next_id /\
                   (!name b sz'.
                      local_region c0 e0.scopes s0 name b sz' ==>
                      off + sz <= b \/ b + sz' <= off) /\ off <= i /\
                   i < off + sz /\ i IN tn.t_mem ==>
                   i IN tn0.t_mem) c0 ee s G tn) H ee s G tn) /\
    len < 2 ** 256 /\ ~s.vs_halted /\ s.vs_current_bb = saL.cs_current_bb /\
    s.vs_inst_idx = LENGTH saL.cs_current_insts /\
    local_ptrs_reserved c0 sa0 /\
    (!x sz. c0.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
    (!x sz. c0.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
    (case bd of
       Fixed cap => len = cap /\ sbL = saL /\ lvo = Lit (n2w cap)
     | Dynamic cap' =>
       compile_ptr_load c0.ce_is_ctor c0.ce_imm_alloca (slot_loc tr)
         ptr.ptr_operand saL = (lvo,sbL) /\ lvo = Var out /\
       fn_has_code saL sbL func /\ (!x. not_fresh_at sa0 x ==> x <> out) /\
       evaluate_type (get_tenv cx) typ = SOME tyv /\
       storage_holds cx tr (ArrayT typ bd)
         (PlaceR (StoragePlace tr slot (ArrayTV tyv bd))) slot ee s /\
       ptr_vv_ok cx (ArrayT typ bd)
         (PlaceR (StoragePlace tr slot (ArrayTV tyv bd)))
         (LocatedValue ann ptr) ee G tn s /\ ptr.ptr_location = slot_loc tr /\
       eval_operand ptr.ptr_operand s = SOME slot /\
       op_taint tn ptr.ptr_operand = {} /\
       lookup_storage slot (get_storage cx ee tr) = n2w len /\
       allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s)) ==>
    ?t G1 tn1.
      (case bd of
         Fixed cap => t = s /\ G1 = G /\ tn1 = tn
       | Dynamic cap' =>
         t = update_var out (n2w len) s with vs_inst_idx := SUC s.vs_inst_idx /\
         G1 =
         step_prov PG G
           (mk_inst saL.cs_next_id (if tr then TLOAD else SLOAD)
              [ptr.ptr_operand] [out]) (update_var out (n2w len) s) /\
         tn1 =
         step_taint
           (mk_inst saL.cs_next_id (if tr then TLOAD else SLOAD)
              [ptr.ptr_operand] [out]) s (update_var out (n2w len) s) tn) /\
      (!x. (case bd of Fixed v => T | Dynamic v1 => x <> out) ==>
           lookup_var x t = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
           op_taint tn1 (Var x) = op_taint tn (Var x)) /\
      t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|> = s /\
      tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
      tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
      eval_operand lvo t = SOME (n2w len) /\ op_taint tn1 lvo = {} /\
      op_prov G1 lvo = NONE /\ ~t.vs_halted /\
      t.vs_current_bb = sbL.cs_current_bb /\
      t.vs_inst_idx = LENGTH sbL.cs_current_insts /\
      !H. valid_horizon cx st0 H ee.storage_trace ==>
          gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
            (OK t,G1,tn1) /\
          (\H ee s G tn.
             ?off.
               len = LENGTH vs /\ len <= bound_length bd /\
               vs =
               GENLIST
                 (\j.
                    PlaceR
                      (StoragePlace tr
                         ((case bd of
                             Fixed v => slot
                           | Dynamic v1 => slot + 1w) +
                          n2w (j * type_slot_size tyv)) tyv)) len /\
               slot = n2w off /\
               MEM (StorageRoot tr off (ArrayTV tyv bd)) ee.storage_trace /\
               evaluate_type (get_tenv cx) typ = SOME tyv /\
               well_formed_type_value tyv /\
               lookup_scopes id ee.scopes = NONE /\
               expr_sim_inv c0 cx env ee /\ ce_locals_declared c0 env /\
               locals_alloc_ok c0 env /\ cenv_top_ext c0 c0 ee.scopes /\
               stmt_state_rel H ctx func c0 cx ee s /\
               storage_well_formed_on cx ee (FST H) /\
               ghost_inv_at (DF H) lo d c0 cx ee G tn s /\
               return_buf_frame d c0 sa0 s /\ ret_pc_ok c0 sa0 s /\
               (\c ee s G tn.
                  alloca_history func s /\
                  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
                  s0.vs_alloca_next <= s.vs_alloca_next /\
                  (!x w.
                     not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
                     lookup_var x s = SOME w) /\
                  (!aid b.
                     FLOOKUP s0.vs_allocas aid = SOME b ==>
                     FLOOKUP s.vs_allocas aid = SOME b) /\
                  (!x. not_fresh_at sa0 x ==>
                       FLOOKUP G x = FLOOKUP G0 x /\
                       op_taint tn (Var x) = op_taint tn0 (Var x)) /\
                  alloca_frame c0 e0 sa0 s0 c ee s /\
                  !aid off sz i.
                    FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
                    aid < sa0.cs_next_id /\
                    (!name b sz'.
                       local_region c0 e0.scopes s0 name b sz' ==>
                       off + sz <= b \/ b + sz' <= off) /\ off <= i /\
                    i < off + sz /\ i IN tn.t_mem ==>
                    i IN tn0.t_mem) c0 ee s G tn) H ee t G1 tn1
Proof
  rpt gen_tac >>
  abbrev_lambda_tac "Fr" 5 0 `alloca_history func s /\ _` >>
  abbrev_lambda_tac "Base" 5 1 `len = LENGTH vs /\ _` >>
  rpt strip_tac >>
  Cases_on `bd`
  >- (gvs[] >>
      simp[eval_operand_def, op_taint_def, op_prov_def,
           venom_state_component_equality, cj 1 gas_origin_ptr_path_rules]) >>
  gvs[] >> suspend "length_dynamic"
QED

Resume for_storage_array_length_full[length_dynamic]:
  rename1 `eval_operand ptr0.ptr_operand s = SOME slot` >>
  `evaluate_type (get_tenv cx) (ArrayT typ (Dynamic n)) =
     SOME (ArrayTV tyv (Dynamic n))` by
    (qpat_x_assum `storage_holds _ _ _ _ _ _ _` mp_tac >>
     simp[storage_holds_def] >> strip_tac >>
     drule vyperTypeValuesTheory.evaluate_type_ArrayT_cases >> gvs[]) >>
  `key_taint (if tr then tn.t_trans else tn.t_stor) slot = {}` by
    (irule located_dynamic_header_clean >>
     goal_assum (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
     simp[GSYM slot_loc_def]) >>
  `emit_op (if tr then TLOAD else SLOAD) [ptr0.ptr_operand] saL =
     (Var out,sbL)` by
    (Cases_on `tr` >> gvs[slot_loc_def, contextTheory.compile_ptr_load_def]) >>
  drule_all emit_op_fetch_boundary >> strip_tac >>
  `(if tr then tload slot s else sload slot s) = n2w len` by
    suspend "length_header_value" >>
  qabbrev_tac `i = mk_inst saL.cs_next_id (if tr then TLOAD else SLOAD)
     [ptr0.ptr_operand] [out]` >>
  qabbrev_tac `u = update_var out (n2w len) s` >>
  qabbrev_tac `t = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G1 = step_prov PG G i u` >>
  qabbrev_tac `tn1 = step_taint i s u tn` >>
  `tn1 = tn with t_var := tn.t_var |+ (out,{})` by
    suspend "length_taint_update" >>
  `FLOOKUP G1 out = NONE` by
    (simp[Abbr `G1`, Abbr `i`] >> irule scalar_load_output_prov >>
     Cases_on `tr` >> simp[]) >>
  `!x. x <> out ==> lookup_var x t = lookup_var x s /\
     FLOOKUP G1 x = FLOOKUP G x /\
     op_taint tn1 (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     simp[Abbr `t`, Abbr `u`, Abbr `G1`, Abbr `i`, update_var_def,
       lookup_var_def, op_taint_def, FLOOKUP_UPDATE] >>
     Cases_on `tr` >>
     simp[step_prov_def, set_prov_def, out_prov_def, mk_inst_def,
          FLOOKUP_DRESTRICT]) >>
  `saL.cs_current_bb = sbL.cs_current_bb` by metis_tac[] >>
  simp[Abbr `t`, Abbr `u`, eval_operand_def, lookup_var_def,
       update_var_def, op_taint_def, op_prov_def, FLOOKUP_UPDATE,
       venom_state_component_equality] >>
  gen_tac >> disch_tac >> conj_tac
  >- suspend "length_joint_path" >>
  suspend "length_base"
QED

Resume for_storage_array_length_full[length_header_value]:
  drule_all storage_holds_decode >> strip_tac >>
  `0 < type_slot_size (ArrayTV tyv (Dynamic n))` by
    simp[vyperValueTheory.type_slot_size_def] >>
  drule_all storage_range_agree_head >>
  Cases_on `tr` >> gvs[sload_def, tload_def]
QED

Resume for_storage_array_length_full[length_taint_update]:
  simp[Abbr `tn1`, Abbr `i`] >>
  irule scalar_storage_load_taint >>
  simp[Abbr `u`, update_var_def]
QED

Resume for_storage_array_length_full[length_joint_path]:
  `step_inst_base i s = OK (update_var out (n2w len) s)` by
    (Cases_on `tr` >>
     gvs[Abbr `i`, step_inst_base_opcode_eqs, exec_read1_def]) >>
  `ptr_inst_ok (DF H) lo 0 ctx func G tn i s` by
    (simp[Abbr `i`] >> irule ptr_inst_ok_slot_load >>
     (metis_tac[])) >>
  `inst_mem_below_frontier i s /\ inst_dload_in_section i s /\
   i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
   i.inst_opcode <> GAS` by
    (Cases_on `tr` >>
     simp[Abbr `i`, mk_inst_def, is_terminator_def,
       inst_mem_below_frontier_def, inst_dload_in_section_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
  `get_instruction bb s.vs_inst_idx = SOME i` by
    gvs[Abbr `i`] >>
  `gas_origin_ptr_edge (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (update_var out (n2w len) s with vs_inst_idx := SUC s.vs_inst_idx),G1,tn1)` by
    (drule_all straight_line_origin_ptr_edge >>
     simp[Abbr `G1`, Abbr `tn1`]) >>
  drule (cj 2 gas_origin_ptr_path_rules) >>
  disch_then (qspecl_then [`[]`, `OK (update_var out (n2w len) s with vs_inst_idx := SUC s.vs_inst_idx)`, `G1`, `tn1`] mp_tac) >>
  simp[cj 1 gas_origin_ptr_path_rules, update_var_def] >>
  metis_tac[]
QED

Resume for_storage_array_length_full[length_base]:
  qmatch_goalsub_abbrev_tac `Base H ee v G1 ta` >>
  `Base H ee s G tn` by metis_tac[] >>
  `!x. not_fresh_at sa0 x ==>
     lookup_var x v = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
     op_taint ta (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> `x <> out` by metis_tac[] >>
     first_x_assum (drule_at (Pat `x <> out`)) >>
     simp[Abbr `v`, Abbr `ta`, update_var_def, lookup_var_def,
          op_taint_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `not_local_ptr c0 ee.scopes out` by
    (simp[not_local_ptr_def] >> metis_tac[local_ptrs_reserved_def]) >>
  qpat_x_assum `Base H ee s G tn` mp_tac >>
  simp[Abbr `Base`, NoAsms] >> strip_tac >>
  `ghost_inv_at (DF H) lo d c0 cx ee G1 ta v` by
    (irule ghost_inv_at_exterior_frame >>
     goal_assum (drule_at (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)) >>
     qexists `sa0` >> simp[Abbr `v`, Abbr `ta`]) >>
  `stmt_state_rel H ctx func c0 cx ee v` by
    (`v = update_var out (n2w len) s with
       vs_inst_idx := SUC (LENGTH saL.cs_current_insts)` by
       (simp[Abbr `v`, update_var_def, NoAsms] >>
        AP_TERM_TAC >> metis_tac[]) >>
     qpat_x_assum `v = _` (fn th => pure_rewrite_tac[th]) >>
     pure_rewrite_tac[stmt_state_rel_inst_idx] >>
     irule stmt_state_rel_update_var >> metis_tac[]) >>
  `return_buf_frame d c0 sa0 v` by
    (irule return_buf_frame_frame >>
     goal_assum (drule_at (Pat `return_buf_frame _ _ _ _`)) >>
     simp[Abbr `v`] >> metis_tac[]) >>
  `ret_pc_ok c0 sa0 v` by
    (irule stmtSimPropsTheory.ret_pc_ok_frame >>
     goal_assum (drule_at (Pat `ret_pc_ok _ _ _`)) >>
     simp[] >> metis_tac[]) >>
  `Fr c0 ee v G1 ta` by suspend "length_frame" >>
  metis_tac[]
QED

Resume for_storage_array_length_full[length_frame]:
  qpat_x_assum `len = LENGTH vs` kall_tac >>
  qpat_x_assum `vs = GENLIST _ _` kall_tac >>
  qpat_x_assum `Fr c0 ee s G tn` mp_tac >>
  simp[Abbr `Fr`, NoAsms] >> strip_tac >>
  `alloca_history func v` by suspend "length_history" >>
  `alloca_frame c0 e0 sa0 s0 c0 ee v` by
    (`alloca_frame c0 e0 sa0 s0 c0 ee (update_var out (n2w len) s)` by
       (irule alloca_frame_update_var >> metis_tac[]) >>
     irule alloca_frame_same_state >>
     goal_assum (drule_at (Pat `alloca_frame _ _ _ _ _ _ _`)) >>
     simp[Abbr `v`, update_var_def]) >>
  simp[Abbr `v`, Abbr `ta`, allocas_below_fmp_def] >>
  conj_tac
  >- (qpat_x_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
      simp[allocas_below_fmp_def] >> metis_tac[]) >>
  metis_tac[]
QED

Resume for_storage_array_length_full[length_history]:
  qpat_x_assum `alloca_history func s` mp_tac >>
  simp[alloca_history_def, Abbr `v`, NoAsms] >> strip_tac >>
  rpt strip_tac >>
  `k < s.vs_inst_idx \/ k = s.vs_inst_idx` by decide_tac
  >- metis_tac[] >>
  Cases_on `tr` >> gvs[mk_inst_def]
  >>> NTH_GOAL (gvs[(DB.fetch "bodyFullForStorage" "for_storage_array_nil_full"), (DB.fetch "bodyFullForStorage" "for_storage_element_copy_post"), exprSimSubscriptArrayLiveStorageSuffixTheory.live_storage_array_represented_suffix_summary_family, exprPtrStorageLoadTheory.emit_storage_load_ptr_path, bodySimFullTheory.expr_map_sim_full_def, exprSimConcatResultTheory.concat_prefix_run, bodySimFullTheory.stmt_frag_full_def, exprSimAggregatesAllocCountedTheory.buffer_alloc_counted_horizons, allocaHistoryTheory.alloca_block_order_def, markerTheory.Abbrev_def, bodySimTheory.ce_locals_declared_def, bodySimTheory.locals_alloc_ok_def, loweringPostsTheory.ret_pc_ok_def, loweringPostsTheory.return_buf_frame_def, bodyPtrDefsTheory.ghost_inv_at_def, bodyPtrDefsTheory.ptr_vv_ok_def]) 1
  >> (gvs[(DB.fetch "bodyFullForStorage" "for_storage_array_nil_full"), (DB.fetch "bodyFullForStorage" "for_storage_element_copy_post"), exprSimSubscriptArrayLiveStorageSuffixTheory.live_storage_array_represented_suffix_summary_family, exprPtrStorageLoadTheory.emit_storage_load_ptr_path, exprSimAggregatesAllocCountedTheory.buffer_alloc_counted_horizons, bodySimFullTheory.expr_map_sim_full_def, exprSimConcatResultTheory.concat_prefix_run, bodySimFullTheory.stmt_frag_full_def, allocaHistoryTheory.alloca_block_order_def, markerTheory.Abbrev_def, bodySimTheory.ce_locals_declared_def, bodySimTheory.locals_alloc_ok_def, loweringPostsTheory.ret_pc_ok_def, loweringPostsTheory.return_buf_frame_def, bodyPtrDefsTheory.ghost_inv_at_def, bodyPtrDefsTheory.ptr_vv_ok_def])
QED

Finalise for_storage_array_length_full

(* The source scope has already been popped.  Only the scalar counter changes. *)
Theorem for_storage_array_backedge_full:
  !DF lo d ctx func cx st0 PG explicit c0 e0 sa0 s0 G0 tn0 tr slot dst tyv typ
      bd vs len nb id env p idx cond lvo sd body si sj sk sl out.
    emit_op ADD [Var idx; Lit 1w] si = (Var out,sj) /\
    emit_inst ASSIGN [Var out] [idx] sj = ((),sk) /\
    emit_inst JMP [Label cond] [] sk = ((),sl) /\ fn_has_code si sl func /\
    not_fresh_at si idx /\ len < dimword (:256) /\
    local_ptrs_reserved c0 sa0 /\ ~not_fresh_at sa0 idx /\
    ~not_fresh_at sa0 out /\
    (!x sz. c0.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
    (!x sz. c0.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
    p <> idx /\ p <> out /\ (!x. lvo = Var x ==> x <> idx /\ x <> out) ==>
    !a rs ee s G tn.
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
           (\H rs ee G tn s.
              ?k off.
                k < len /\ len = LENGTH vs /\ len <= bound_length bd /\
                vs =
                GENLIST
                  (\j.
                     PlaceR
                       (StoragePlace tr
                          ((case bd of
                              Fixed v => slot
                            | Dynamic v1 => slot + 1w) +
                           n2w (j * type_slot_size tyv)) tyv)) len /\
                rs = DROP k vs /\ slot = n2w off /\
                MEM (StorageRoot tr off (ArrayTV tyv bd)) ee.storage_trace /\
                evaluate_type (get_tenv cx) typ = SOME tyv /\
                well_formed_type_value tyv /\
                s.vs_current_bb = si.cs_current_bb /\
                s.vs_inst_idx = LENGTH si.cs_current_insts /\ ~s.vs_halted /\
                lookup_var idx s = SOME (n2w k) /\ FLOOKUP G idx = NONE /\
                op_taint tn (Var idx) = {} /\
                eval_operand lvo s = SOME (n2w len) /\ op_taint tn lvo = {} /\
                op_prov G lvo = NONE /\
                eval_operand (Lit slot) s = SOME slot /\
                op_taint tn (Lit slot) = {} /\ lookup_var p s = SOME dst /\
                FLOOKUP s.vs_allocas sd.cs_next_id = SOME (w2n dst,nb) /\
                ptr_covers G tn p s nb /\ 32 * type_slot_size tyv <= nb /\
                w2n dst + nb < 2 ** 256 /\ w2n dst + nb <= s.vs_alloca_next /\
                (!name b sz.
                   local_region c0 ee.scopes s name b sz ==>
                   w2n dst + nb <= b \/ b + sz <= w2n dst) /\
                lookup_scopes id ee.scopes = NONE /\
                expr_sim_inv c0 cx env ee /\ ce_locals_declared c0 env /\
                locals_alloc_ok c0 env /\ cenv_top_ext c0 c0 ee.scopes /\
                stmt_state_rel H ctx func c0 cx ee s /\
                storage_well_formed_on cx ee (FST H) /\
                ghost_inv_at (DF H) lo d c0 cx ee G tn s /\
                return_buf_frame d c0 sa0 s /\ ret_pc_ok c0 sa0 s /\
                return_buf_sep d c0 ee s /\ body_stmts_full_ok cx body /\
                (\c ee s G tn.
                   alloca_history func s /\
                   (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
                   s0.vs_alloca_next <= s.vs_alloca_next /\
                   (!x w.
                      not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
                      lookup_var x s = SOME w) /\
                   (!aid b.
                      FLOOKUP s0.vs_allocas aid = SOME b ==>
                      FLOOKUP s.vs_allocas aid = SOME b) /\
                   (!x. not_fresh_at sa0 x ==>
                        FLOOKUP G x = FLOOKUP G0 x /\
                        op_taint tn (Var x) = op_taint tn0 (Var x)) /\
                   alloca_frame c0 e0 sa0 s0 c ee s /\
                   !aid off sz i.
                     FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
                     aid < sa0.cs_next_id /\
                     (!name b sz'.
                        local_region c0 e0.scopes s0 name b sz' ==>
                        off + sz <= b \/ b + sz' <= off) /\ off <= i /\
                     i < off + sz /\ i IN tn.t_mem ==>
                     i IN tn0.t_mem) c0 ee s G tn) H (a::rs) ee G tn s) /\
      ~s.vs_halted /\ allocas_from lo s /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
      ?t G1 tn1. !H.
        valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
          (OK t,G1,tn1) /\
        (\H rs ee G tn s.
           ?k off.
             k <= len /\ len = LENGTH vs /\ len <= bound_length bd /\
             vs =
             GENLIST
               (\j.
                  PlaceR
                    (StoragePlace tr
                       ((case bd of Fixed v => slot | Dynamic v1 => slot + 1w) +
                        n2w (j * type_slot_size tyv)) tyv)) len /\
             rs = DROP k vs /\ slot = n2w off /\
             MEM (StorageRoot tr off (ArrayTV tyv bd)) ee.storage_trace /\
             evaluate_type (get_tenv cx) typ = SOME tyv /\
             well_formed_type_value tyv /\ s.vs_current_bb = cond /\
             s.vs_inst_idx = 0 /\ ~s.vs_halted /\
             lookup_var idx s = SOME (n2w k) /\ FLOOKUP G idx = NONE /\
             op_taint tn (Var idx) = {} /\
             eval_operand lvo s = SOME (n2w len) /\ op_taint tn lvo = {} /\
             op_prov G lvo = NONE /\ eval_operand (Lit slot) s = SOME slot /\
             op_taint tn (Lit slot) = {} /\ lookup_var p s = SOME dst /\
             FLOOKUP s.vs_allocas sd.cs_next_id = SOME (w2n dst,nb) /\
             ptr_covers G tn p s nb /\ 32 * type_slot_size tyv <= nb /\
             w2n dst + nb < 2 ** 256 /\ w2n dst + nb <= s.vs_alloca_next /\
             (!name b sz.
                local_region c0 ee.scopes s name b sz ==>
                w2n dst + nb <= b \/ b + sz <= w2n dst) /\
             lookup_scopes id ee.scopes = NONE /\ expr_sim_inv c0 cx env ee /\
             ce_locals_declared c0 env /\ locals_alloc_ok c0 env /\
             cenv_top_ext c0 c0 ee.scopes /\
             stmt_state_rel H ctx func c0 cx ee s /\
             storage_well_formed_on cx ee (FST H) /\
             ghost_inv_at (DF H) lo d c0 cx ee G tn s /\
             return_buf_frame d c0 sa0 s /\ ret_pc_ok c0 sa0 s /\
             return_buf_sep d c0 ee s /\ (k <> 0 ==> body_stmts_full_ok cx body) /\
             (\c ee s G tn.
                alloca_history func s /\
                (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
                s0.vs_alloca_next <= s.vs_alloca_next /\
                (!x w.
                   not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
                   lookup_var x s = SOME w) /\
                (!aid b.
                   FLOOKUP s0.vs_allocas aid = SOME b ==>
                   FLOOKUP s.vs_allocas aid = SOME b) /\
                (!x. not_fresh_at sa0 x ==>
                     FLOOKUP G x = FLOOKUP G0 x /\
                     op_taint tn (Var x) = op_taint tn0 (Var x)) /\
                alloca_frame c0 e0 sa0 s0 c ee s /\
                !aid off sz i.
                  FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
                  aid < sa0.cs_next_id /\
                  (!name b sz'.
                     local_region c0 e0.scopes s0 name b sz' ==>
                     off + sz <= b \/ b + sz' <= off) /\ off <= i /\
                  i < off + sz /\ i IN tn.t_mem ==>
                  i IN tn0.t_mem) c0 ee s G tn) H rs ee G1 tn1 t
Proof
  rpt gen_tac >>
  abbrev_lambda_tac "Fr" 5 0 `alloca_history func s /\ _` >>
  abbrev_lambda_tac "Inv" 6 2 `k <= len /\ _` >>
  abbrev_lambda_tac "Ready" 6 2 `k < len /\ _` >>
  rpt strip_tac >>
  Cases_on `?H. valid_horizon cx st0 H ee.storage_trace`
  >- (pop_assum (qx_choose_then `H0` assume_tac) >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _`
        (qspec_then `H0` mp_tac) >>
      (impl_tac >- simp[]) >>
      simp[NoAsms, Abbr `Ready`] >> strip_tac >>
      qexistsl [`jump_to cond (update_var idx (n2w (k+1))
          (update_var out (n2w (k+1)) s))`,
        `DRESTRICT (DRESTRICT G (COMPL {out})) (COMPL {idx})`,
        `tn with t_var := (tn.t_var |+ (out,{})) |+ (idx,{})`] >>
      gen_tac >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _`
        (qspec_then `H` mp_tac) >>
      (impl_tac >- simp[]) >>
      BETA_TAC >> disch_then
        (qx_choose_then `j` (qx_choose_then `off_cur` strip_assume_tac)) >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` kall_tac >>
      `j = k` by
        (`(n2w j : bytes32) = n2w k` by fs[] >>
         `j < dimword (:256) /\ k < dimword (:256)` by decide_tac >>
         qpat_x_assum `(n2w j : bytes32) = n2w k` mp_tac >>
         simp[n2w_11]) >>
      qpat_x_assum `j = k` SUBST_ALL_TAC >>
      drule_all typed_copy_origin_ptr_counter_backedge_path >>
      disch_then (qspecl_then [`explicit`,`PG`,`DF H`] strip_assume_tac) >>
      qpat_x_assum `Var out = Var out'`
        (SUBST_ALL_TAC o SYM o SRULE []) >>
      qpat_assum `t = jump_to _ _` (fn th => pure_rewrite_tac[GSYM th]) >>
      qpat_assum `Gf = DRESTRICT _ _` (fn th => pure_rewrite_tac[GSYM th]) >>
      qpat_assum `tnf = _` (fn th => pure_rewrite_tac[GSYM th]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      `!x. not_fresh_at sa0 x ==>
         lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
         op_taint tnf (Var x) = op_taint tn (Var x)` by
        (gen_tac >> disch_tac >>
         qpat_x_assum `!p. p <> idx /\ p <> out ==> _` irule >>
         metis_tac[]) >>
      `not_local_ptr c0 ee.scopes idx /\ not_local_ptr c0 ee.scopes out` by
        metis_tac[exprSimOperandsTheory.fresh_not_local_ptr] >>
      `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
       t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
       t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables /\
       t.vs_labels = s.vs_labels /\
       tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
       tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm` by
        (qpat_assum `t = jump_to _ _` (fn th =>
           simp[th, jump_to_def, update_var_def]) >>
         qpat_assum `tnf = _` (fn th => simp[th])) >>
      `ghost_inv_at (DF H) lo d c0 cx ee Gf tnf t` by
        (irule ghost_inv_at_exterior_frame >>
         qexistsl [`G`,`ee`,`s`,`sa0`,`tn`] >> simp[]) >>
      `stmt_state_rel H ctx func c0 cx ee t` by
        (qpat_assum `t = jump_to _ _` (fn th => pure_rewrite_tac[th]) >>
         simp[stmt_state_rel_jump_to] >>
         irule stmt_state_rel_update_var >> simp[] >>
         irule stmt_state_rel_update_var >> simp[]) >>
      `return_buf_frame d c0 sa0 t` by
        (irule return_buf_frame_frame >>
         qexistsl [`c0`,`s`,`sa0`] >> simp[] >> metis_tac[]) >>
      `ret_pc_ok c0 sa0 t` by
        (irule ret_pc_ok_frame >>
         qexistsl [`c0`,`s`,`sa0`] >> simp[] >> metis_tac[]) >>
      `!name b sz. local_region c0 ee.scopes t name b sz <=>
                   local_region c0 ee.scopes s name b sz` by
        (rpt gen_tac >> irule local_region_lookup_cong >>
         rpt strip_tac >> metis_tac[not_local_ptr_def]) >>
      `return_buf_sep d c0 ee t` by
        (irule return_buf_sep_transport >>
         conj_tac
         >- (map_every qx_gen_tac [`bw`,`cap`] >> disch_tac >>
             qpat_assum `d = SOME (bw,cap)` SUBST_ALL_TAC >>
             qpat_assum `return_buf_sep (SOME (bw,cap)) c0 ee s`
               (mp_tac o CONJUNCT1 o REWRITE_RULE [return_buf_sep_def]) >>
             rewrite_tac[allocas_from_def] >>
             qpat_assum `t.vs_allocas = s.vs_allocas` SUBST1_TAC >> simp[NoAsms]) >>
         qexistsl_tac [`c0`, `ee`, `s`] >>
         reverse conj_tac >- first_assum ACCEPT_TAC >>
         qpat_assum `!n b sz. local_region c0 ee.scopes t n b sz <=> _`
           (rewrite_tac o single)) >>
      `alloca_frame c0 e0 sa0 s0 c0 ee t` by
        (qpat_assum `Fr c0 ee s G tn` mp_tac >>
         simp[NoAsms, Abbr `Fr`] >> strip_tac >>
         qpat_assum `t = jump_to _ _` (fn th => pure_rewrite_tac[th]) >>
         irule alloca_frame_same_state >>
         qexists `update_var idx (n2w (k+1)) (update_var out (n2w (k+1)) s)` >>
         simp[jump_to_def] >>
         irule alloca_frame_update_var >> simp[] >>
         irule alloca_frame_update_var >> simp[]) >>
      `(ctx_has_dalloca ctx ==> allocas_below_fmp t)` by
        (qpat_assum `t = jump_to _ _` (fn th => pure_rewrite_tac[th]) >>
         simp[allocas_below_fmp_def, jump_to_def, update_var_def] >>
         metis_tac[allocas_below_fmp_def]) >>
      `Fr c0 ee t Gf tnf` by
        (qpat_assum `Fr c0 ee s G tn` mp_tac >>
         simp[NoAsms, Abbr `Fr`] >> strip_tac >>
         qpat_x_assum `t = jump_to _ _` kall_tac >>
         qpat_x_assum `Gf = _` kall_tac >>
         qpat_x_assum `tnf = _` kall_tac >>
         simp[] >> conj_tac
         >- (irule alloca_history_jump >> simp[] >> qexists `s` >> simp[]) >>
         first_assum MATCH_ACCEPT_TAC) >>
      qpat_x_assum `t = jump_to _ _` kall_tac >>
      qpat_x_assum `Gf = _` kall_tac >>
      qpat_x_assum `tnf = _` kall_tac >>
      `eval_operand lvo t = SOME (n2w len) /\
       op_taint tnf lvo = {} /\ op_prov Gf lvo = NONE` by
        (Cases_on `lvo` >>
         fs[IgnAsm `len = LENGTH vs`, eval_operand_def, op_taint_def, op_prov_def] >>
         metis_tac[]) >>
      `ptr_covers Gf tnf p t nb` by
        (irule ptr_covers_lookup_frame >>
         qexistsl [`G`,`s`,`tn`] >> simp[]) >>
      `rs = DROP (k+1) vs` by
        (`rs = DROP 1 (DROP k vs)` by
          (qpat_assum `a::rs = DROP k vs`
            (fn th => pure_rewrite_tac[GSYM th]) >> simp[]) >>
         pop_assum mp_tac >> simp[NoAsms, DROP_DROP_T, ADD_COMM]) >>
      simp[NoAsms, Abbr `Inv`] >>
      qexistsl [`k+1`,`off_cur`] >>
      simp[IgnAsm `len = LENGTH vs`, eval_operand_def, op_taint_def] >>
      first_assum MATCH_ACCEPT_TAC) >>
  qexistsl [`s`,`G`,`tn`] >> metis_tac[]
QED

(* Small static companions: the optional header load precedes declaration. *)
Theorem for_storage_length_geometry:
  (if dyn then
     compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca
       (if tr then LocTransient else LocStorage) (Lit slot)
   else return (Lit (n2w cap))) st = (lvo,sd) ==>
  sd.cs_next_var = st.cs_next_var + (if dyn then 1 else 0) /\
  sd.cs_next_id = st.cs_next_id + (if dyn then 1 else 0) /\
  sd.cs_next_label = st.cs_next_label /\
  sd.cs_current_bb = st.cs_current_bb /\ sd.cs_blocks = st.cs_blocks /\
  (if dyn then
     lvo = Var (STRING #"%" (toString st.cs_next_var)) /\
     sd.cs_current_insts = st.cs_current_insts ++
       [mk_inst st.cs_next_id (if tr then TLOAD else SLOAD) [Lit slot]
          [STRING #"%" (toString st.cs_next_var)]]
   else lvo = Lit (n2w cap) /\ sd = st) /\
  (!x. lvo = Var x ==> not_fresh_at sd x)
Proof
  Cases_on `dyn` >> Cases_on `tr` >>
  simp[compile_ptr_load_def, emit_op_def, emit_inst_def, fresh_var_def,
    fresh_id_def, emit_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, LET_THM] >>
  rpt strip_tac >> gvs[] >> simp[not_fresh_at_def]
QED

Theorem for_storage_element_layout:
  expr_sim_inv cenv cx env es /\
  evaluate_type (get_tenv cx) et = SOME tv ==>
  elem_size_in_location cenv (if tr then LocTransient else LocStorage) et =
    type_slot_size tv /\
  type_memory_bytes cenv et = 32 * type_slot_size tv /\
  (type_memory_size tv < 2**64 ==>
    type_slot_size tv < 2**256 /\
    type_memory_bytes cenv et + 64 < 2**256)
Proof
  strip_tac >> drule_all expr_sim_inv_memory_size >> strip_tac >>
  conj_tac >- (Cases_on `tr` >>
    simp[elem_size_in_location_def, is_slot_addressed_def,
      slot_count_of_memory_size]) >>
  conj_tac >- simp[type_memory_size_slots] >>
  strip_tac >> drule unwrap_typed_buffer_count_bound >> strip_tac >>
  simp[]
  >> (gvs[])
QED

(* Invoke the body at its actual compiler age.  The non-Label fact is
   supplied by the iterator's literal/load compilation, not source typing. *)
Theorem for_storage_body_invoke_full:
  !DF lo d ctx shadow_ctx PG func shadow_func cx RetQ tops bindings env id typ
      tyv v ei body env_b ret_ty bc bc1 sb0 sb1 shadow_sb0 shadow_sb1 st0 s G
      tn idx p lvo k dst len.
    body_stmts_full_ok cx body /\ body_inv tops ctx bc cx /\ shadow_body_inv tops ctx shadow_ctx /\
    supported_stmts tops bindings body /\
    (!target.
       supported_stmts_expr_exists (expr_abi_decode_target_root target) body ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv bc cx (extend_local env id typ F)
      (ei with
       scopes :=
         fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
           FEMPTY::ei.scopes) /\
    ce_locals_declared bc (extend_local env id typ F) /\
    locals_alloc_ok bc (extend_local env id typ F) /\
    type_stmts (extend_local env id typ F) ret_ty body = SOME env_b /\
    stmts_exprs_ok bc body /\ call_evaluation_safe cx (int_calls_stmts body) /\
    frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ bc
      ret_ty /\ stmts_env bc (InLoop exit incr) ret_ty body sb0 = (bc1,sb1) /\
    stmts_env bc (InLoop exit incr) ret_ty (MAP gas_shadow_stmt body)
      shadow_sb0 = (bc1,shadow_sb1) /\ gas_shadow_state sb0 shadow_sb0 /\
    gas_shadow_state sb1 shadow_sb1 /\ gas_shadow_context ctx shadow_ctx /\
    ctx_inst_ids_distinct ctx /\ gas_shadow_function func shadow_func /\
    MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sb0 sb1 func /\
    fn_has_code shadow_sb0 shadow_sb1 shadow_func /\
    (!H. dead_lo_ok H (DF H) lo bc cx) /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved bc sb0 /\ ret_pc_ok bc sb0 s /\
    (!x sz. bc.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb0 x) /\
    ~block_is_terminated sb0 /\
    gas_admissible (eval_stmts cx body) (stmt_res_ok (InLoop exit incr))
      (ei with
       scopes :=
         fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
           FEMPTY::ei.scopes) /\ return_buf_frame d bc sb0 s /\
    return_buf_sep d bc
      (ei with scopes :=
        fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
          FEMPTY::ei.scopes) s /\
    alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_no_wrap inst u) /\
    (!H. valid_horizon cx st0 H
           (ei with
            scopes :=
              fmupdate id
                <|assignable := F; type := tyv; value := v; popped := []|>
                FEMPTY::ei.scopes).storage_trace ==>
         stmt_state_rel H ctx func bc cx
           (ei with
            scopes :=
              fmupdate id
                <|assignable := F; type := tyv; value := v; popped := []|>
                FEMPTY::ei.scopes) s /\
         storage_well_formed_on cx
           (ei with
            scopes :=
              fmupdate id
                <|assignable := F; type := tyv; value := v; popped := []|>
                FEMPTY::ei.scopes) (FST H) /\
         ghost_inv_at (DF H) lo d bc cx
           (ei with
            scopes :=
              fmupdate id
                <|assignable := F; type := tyv; value := v; popped := []|>
                FEMPTY::ei.scopes) G tn s) /\ ~s.vs_halted /\
    s.vs_current_bb = sb0.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb0.cs_current_insts /\ not_fresh_at sb0 idx /\
    not_fresh_at sb0 p /\ (!x. lvo = Var x ==> not_fresh_at sb0 x) /\
    (!lbl. lvo <> Label lbl) /\ lookup_var idx s = SOME (n2w k) /\
    lookup_var p s = SOME dst /\ eval_operand lvo s = SOME (n2w len) ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (eval_stmts cx body)
      (ei with
       scopes :=
         fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
           FEMPTY::ei.scopes,s,G,tn)
      (\H res ee G1 tn1 t.
         (\H res ee G1 tn1 t.
            ?c3.
              stmt_lands (InLoop exit incr) sb1 res t /\ ~t.vs_halted /\
              (res = INL () ==> ~block_is_terminated sb1 /\ c3 = bc1) /\
              cenv_top_ext bc c3 ee.scopes /\
              stmt_state_rel H ctx func c3 cx ee t /\
              storage_well_formed_on cx ee (FST H) /\
              return_buf_frame d c3 sb1 t /\ alloca_history func t /\
              return_buf_sep d c3 ee t /\
              (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
              s.vs_alloca_next <= t.vs_alloca_next /\
              ghost_inv_at (DF H) lo d c3 cx ee G1 tn1 t /\
              (!x w.
                 not_fresh_at sb0 x /\ lookup_var x s = SOME w ==>
                 lookup_var x t = SOME w) /\
              (!aid b.
                 FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
              (!x. not_fresh_at sb0 x ==>
                   FLOOKUP G1 x = FLOOKUP G x /\
                   op_taint tn1 (Var x) = op_taint tn (Var x)) /\
              alloca_frame bc
                (ei with
                 scopes :=
                   fmupdate id
                     <|assignable := F; type := tyv; value := v; popped := []|>
                     FEMPTY::ei.scopes) sb0 s c3 ee t /\
              !aid off sz i.
                FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
                aid < sb0.cs_next_id /\
                (!name b sz'.
                   local_region bc
                     (ei with
                      scopes :=
                        fmupdate id
                          <|assignable := F; type := tyv; value := v;
                            popped := []|> FEMPTY::ei.scopes).scopes s name b
                     sz' ==>
                   off + sz <= b \/ b + sz' <= off) /\ off <= i /\
                i < off + sz /\ i IN tn1.t_mem ==>
                i IN tn.t_mem) H res ee G1 tn1 t /\
         (\G1 tn1 t.
            lookup_var idx t = lookup_var idx s /\
            lookup_var p t = lookup_var p s /\
            eval_operand lvo t = eval_operand lvo s /\
            FLOOKUP G1 idx = FLOOKUP G idx /\ FLOOKUP G1 p = FLOOKUP G p /\
            op_prov G1 lvo = op_prov G lvo /\
            op_taint tn1 (Var idx) = op_taint tn (Var idx) /\
            op_taint tn1 (Var p) = op_taint tn (Var p) /\
            op_taint tn1 lvo = op_taint tn lvo) G1 tn1 t /\ ee.gas_obs = [] /\
         ?xs. !tail.
           eval_stmts cx body
             (ei with
              <|gas_obs := xs ++ tail;
                scopes :=
                  fmupdate id
                    <|assignable := F; type := tyv; value := v; popped := []|>
                    FEMPTY::ei.scopes|>) = (res,ee with gas_obs := tail))
      (\H res ee gt r.
         (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
         halt_exit H cx ee res r /\
         (ctx_has_dalloca ctx ==>
          !u. r = Halt u \/ (?ir. r = IntRet ir u) ==> allocas_below_fmp u))
Proof
  rpt gen_tac >>
  qpat_abbrev_tac `envb = extend_local env id typ F` >>
  qpat_abbrev_tac `eb = ei with scopes := (FEMPTY |+ (id, _)) :: ei.scopes` >>
  qpat_abbrev_tac `explicit = gas_explicit_sites ctx shadow_ctx` >>
  abbrev_lambda_tac "Qb" 6 1 `stmt_lands (InLoop exit incr) sb1 res t /\ _` >>
  abbrev_lambda_tac "Rb" 5 0 `(!tail. stmt_exit_ptr _ (ee with gas_obs := tail) res gt r) /\ _` >>
  abbrev_lambda_tac "Keep" 3 0 `lookup_var idx t = lookup_var idx s /\ _` >>
  rpt strip_tac >>
  rename1 `body_stmts_full_ok cx stmts` >>
  qpat_x_assum `body_stmts_full_ok _ _`
    (mp_tac o REWRITE_RULE [body_stmts_full_ok_def]) >>
  disch_then drule_all >>
  disch_then (qspec_then `InLoop exit incr` mp_tac) >>
  rewrite_tac [stmt_frag_full_def] >>
  disch_then (qspecl_then [`st0`, `sb0`, `sb1`, `shadow_sb0`,
    `shadow_sb1`, `s`, `G`, `tn`, `bc1`] mp_tac) >>
  simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  irule gas_outcome_full_post_source >>
  goal_assum (drule_at Any) >>
  reverse conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  BETA_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
  simp[] >>
  reverse conj_tac >- (qexists_tac `xs` >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `Qb _ _ _ _ _ _` mp_tac >>
  simp[Abbr `Qb`] >> strip_tac >>
  simp[Abbr `Keep`] >>
  Cases_on `lvo` >> gvs[eval_operand_def, op_prov_def, op_taint_def] >>
  metis_tac[]
QED

(* Entry control writes only scalar temporaries. The source and allocation
   anchors are deliberately the original For entry, not the entry block. *)
Theorem for_storage_array_entry_full:
  !DF lo d ctx func cx c0 e0 sa0 s0 G0 tn0 tr slot tyv typ bd vs len nb id env
      p idx lvo sd st0 explicit PG entry cond bad good jid eid s G tn es dst bb
      eb.
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst jid JMP [Label entry] []) /\
    lookup_block entry func.fn_blocks = SOME eb /\
    eb.bb_instructions =
    [mk_inst eid ASSIGN [Lit 0w] [idx]] ++
    (if case bd of Fixed v => F | Dynamic v1 => T then
       [mk_inst (eid + 1) GT [lvo; Lit (n2w (bound_length bd))] [bad];
        mk_inst (eid + 2) ISZERO [Var bad] [good];
        mk_inst (eid + 3) ASSERT [Var good] []]
     else []) ++
    [mk_inst
       (eid +
        LENGTH
          ([mk_inst eid ASSIGN [Lit 0w] [idx]] ++
           if case bd of Fixed v => F | Dynamic v1 => T then
             [mk_inst (eid + 1) GT [lvo; Lit (n2w (bound_length bd))] [bad];
              mk_inst (eid + 2) ISZERO [Var bad] [good];
              mk_inst (eid + 3) ASSERT [Var good] []]
           else [])) JMP [Label cond] []] /\ ~s.vs_halted /\
    len <= bound_length bd /\ bound_length bd < 2 ** 256 /\
    (\s G tn.
       eval_operand lvo s = SOME (n2w len) /\ op_taint tn lvo = {} /\
       op_prov G lvo = NONE) s G tn /\
    (\s G tn.
       lookup_var p s = SOME dst /\
       FLOOKUP s.vs_allocas sd.cs_next_id = SOME (w2n dst,nb) /\
       ptr_covers G tn p s nb /\ 32 * type_slot_size tyv <= nb /\
       w2n dst + nb < 2 ** 256 /\ w2n dst + nb <= s.vs_alloca_next /\
       !name b sz.
         local_region c0 es.scopes s name b sz ==>
         w2n dst + nb <= b \/ b + sz <= w2n dst) s G tn /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
         (\H ee s G tn.
            ?off.
              len = LENGTH vs /\ len <= bound_length bd /\
              vs =
              GENLIST
                (\j.
                   PlaceR
                     (StoragePlace tr
                        ((case bd of Fixed v => slot | Dynamic v1 => slot + 1w) +
                         n2w (j * type_slot_size tyv)) tyv)) len /\
              slot = n2w off /\
              MEM (StorageRoot tr off (ArrayTV tyv bd)) ee.storage_trace /\
              evaluate_type (get_tenv cx) typ = SOME tyv /\
              well_formed_type_value tyv /\
              lookup_scopes id ee.scopes = NONE /\ expr_sim_inv c0 cx env ee /\
              ce_locals_declared c0 env /\ locals_alloc_ok c0 env /\
              cenv_top_ext c0 c0 ee.scopes /\
              stmt_state_rel H ctx func c0 cx ee s /\
              storage_well_formed_on cx ee (FST H) /\
              ghost_inv_at (DF H) lo d c0 cx ee G tn s /\
              return_buf_frame d c0 sa0 s /\ ret_pc_ok c0 sa0 s /\
              (\c ee s G tn.
                 alloca_history func s /\
                 (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
                 s0.vs_alloca_next <= s.vs_alloca_next /\
                 (!x w.
                    not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
                    lookup_var x s = SOME w) /\
                 (!aid b.
                    FLOOKUP s0.vs_allocas aid = SOME b ==>
                    FLOOKUP s.vs_allocas aid = SOME b) /\
                 (!x. not_fresh_at sa0 x ==>
                      FLOOKUP G x = FLOOKUP G0 x /\
                      op_taint tn (Var x) = op_taint tn0 (Var x)) /\
                 alloca_frame c0 e0 sa0 s0 c ee s /\
                 !aid off sz i.
                   FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
                   aid < sa0.cs_next_id /\
                   (!name b sz'.
                      local_region c0 e0.scopes s0 name b sz' ==>
                      off + sz <= b \/ b + sz' <= off) /\ off <= i /\
                   i < off + sz /\ i IN tn.t_mem ==>
                   i IN tn0.t_mem) c0 ee s G tn) H es s G tn) /\
    local_ptrs_reserved c0 sa0 /\
    (!x sz. c0.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
    (!x sz. c0.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
    (!x. not_fresh_at sa0 x ==>
         x NOTIN
         if case bd of Fixed v => F | Dynamic v1 => T then {idx; bad; good}
         else {idx}) /\
    p NOTIN
    (if case bd of Fixed v => F | Dynamic v1 => T then {idx; bad; good}
     else {idx}) /\
    (!x. lvo = Var x ==>
         x NOTIN
         if case bd of Fixed v => F | Dynamic v1 => T then {idx; bad; good}
         else {idx}) /\ (!lbl. lvo <> Label lbl) /\
    ((case bd of Fixed v => F | Dynamic v1 => T) ==>
     idx <> bad /\ idx <> good /\ bad <> good) ==>
    ?t G1 tn1.
      (!x. x NOTIN
           (if case bd of Fixed v => F | Dynamic v1 => T then {idx; bad; good}
            else {idx}) ==>
           lookup_var x t = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
           op_taint tn1 (Var x) = op_taint tn (Var x)) /\
      tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
      tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
      t =
      jump_to cond
        (jump_to entry
           (if (case bd of Fixed v => F | Dynamic v1 => T) then
              update_var good 1w (update_var bad 0w (update_var idx 0w s))
            else update_var idx 0w s)) /\
      !H. valid_horizon cx st0 H es.storage_trace ==>
          gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
            (OK t,G1,tn1) /\
          (\H ee s G tn.
             ?off.
               len = LENGTH vs /\ len <= bound_length bd /\
               vs =
               GENLIST
                 (\j.
                    PlaceR
                      (StoragePlace tr
                         ((case bd of
                             Fixed v => slot
                           | Dynamic v1 => slot + 1w) +
                          n2w (j * type_slot_size tyv)) tyv)) len /\
               slot = n2w off /\
               MEM (StorageRoot tr off (ArrayTV tyv bd)) ee.storage_trace /\
               evaluate_type (get_tenv cx) typ = SOME tyv /\
               well_formed_type_value tyv /\
               lookup_scopes id ee.scopes = NONE /\
               expr_sim_inv c0 cx env ee /\ ce_locals_declared c0 env /\
               locals_alloc_ok c0 env /\ cenv_top_ext c0 c0 ee.scopes /\
               stmt_state_rel H ctx func c0 cx ee s /\
               storage_well_formed_on cx ee (FST H) /\
               ghost_inv_at (DF H) lo d c0 cx ee G tn s /\
               return_buf_frame d c0 sa0 s /\ ret_pc_ok c0 sa0 s /\
               (\c ee s G tn.
                  alloca_history func s /\
                  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
                  s0.vs_alloca_next <= s.vs_alloca_next /\
                  (!x w.
                     not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
                     lookup_var x s = SOME w) /\
                  (!aid b.
                     FLOOKUP s0.vs_allocas aid = SOME b ==>
                     FLOOKUP s.vs_allocas aid = SOME b) /\
                  (!x. not_fresh_at sa0 x ==>
                       FLOOKUP G x = FLOOKUP G0 x /\
                       op_taint tn (Var x) = op_taint tn0 (Var x)) /\
                  alloca_frame c0 e0 sa0 s0 c ee s /\
                  !aid off sz i.
                    FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
                    aid < sa0.cs_next_id /\
                    (!name b sz'.
                       local_region c0 e0.scopes s0 name b sz' ==>
                       off + sz <= b \/ b + sz' <= off) /\ off <= i /\
                    i < off + sz /\ i IN tn.t_mem ==>
                    i IN tn0.t_mem) c0 ee s G tn) H es t G1 tn1 /\
          (\s G tn.
             lookup_var p s = SOME dst /\
             FLOOKUP s.vs_allocas sd.cs_next_id = SOME (w2n dst,nb) /\
             ptr_covers G tn p s nb /\ 32 * type_slot_size tyv <= nb /\
             w2n dst + nb < 2 ** 256 /\ w2n dst + nb <= s.vs_alloca_next /\
             !name b sz.
               local_region c0 es.scopes s name b sz ==>
               w2n dst + nb <= b \/ b + sz <= w2n dst) t G1 tn1 /\
          (\s G tn.
             eval_operand lvo s = SOME (n2w len) /\ op_taint tn lvo = {} /\
             op_prov G lvo = NONE) t G1 tn1 /\ t.vs_current_bb = cond /\
          t.vs_inst_idx = 0 /\ ~t.vs_halted /\ lookup_var idx t = SOME 0w /\
          FLOOKUP G1 idx = NONE /\ op_taint tn1 (Var idx) = {}
Proof
  rpt gen_tac >>
  abbrev_lambda_tac "Fr" 5 0 `alloca_history func s /\ _` >>
  abbrev_lambda_tac "Base" 5 1 `len = LENGTH vs /\ _` >>
  abbrev_lambda_tac "Buf" 3 0 `lookup_var p s = SOME dst /\ _` >>
  abbrev_lambda_tac "LenP" 3 0 `eval_operand lvo s = SOME (n2w len) /\ _` >>
  qpat_abbrev_tac `dyn = (case bd of Fixed _ => F | Dynamic _ => T)` >>
  qpat_abbrev_tac `Written = (if dyn then {idx;bad;good} else {idx})` >>
  qpat_abbrev_tac `code = [mk_inst eid ASSIGN [Lit 0w] [idx]] ++ _` >>
  rpt strip_tac >>
  qabbrev_tac `u = if dyn then
    update_var good 1w (update_var bad 0w (update_var idx 0w s))
    else update_var idx 0w s` >>
  qabbrev_tac `G1 = if dyn then
    DRESTRICT (DRESTRICT (DRESTRICT G (COMPL {idx})) (COMPL {bad})) (COMPL {good})
    else DRESTRICT G (COMPL {idx})` >>
  qabbrev_tac `tn1 = if dyn then
    tn with t_var := tn.t_var |+ (idx,{}) |+ (bad,{}) |+ (good,{})
    else tn with t_var := tn.t_var |+ (idx,{})` >>
  qexistsl [`jump_to cond (jump_to entry u)`, `G1`, `tn1`] >>
  conj_tac >- suspend "entry_registers" >>
  ntac 4 (conj_tac >- (Cases_on `dyn` >> simp[Abbr `tn1`])) >>
  conj_tac >- REFL_TAC >>
  gen_tac >> disch_tac >>
  first_x_assum drule >> simp[Abbr `Base`] >> strip_tac >>
  `allocas_from lo s` by
    (qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >> simp[ghost_inv_at_def]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by
    (qpat_x_assum `Fr c0 es s G tn` mp_tac >> simp[Abbr `Fr`]) >>
  conj_tac >- suspend "entry_path" >>
  suspend "entry_post"
QED

Resume for_storage_array_entry_full[entry_registers]:
  rpt strip_tac >>
  Cases_on `dyn` >>
  gvs[Abbr `Written`, Abbr `G1`, Abbr `tn1`, Abbr `u`, jump_to_def,
      lookup_var_def, update_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
      op_taint_def]
QED

Resume for_storage_array_entry_full[entry_path]:
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (jump_to entry s),G,tn)` by
    (drule_all jmp_origin_ptr_path >> simp[]) >>
  `run_inst_seq code (jump_to entry s) = OK (jump_to entry u)` by
    suspend "entry_run" >>
  `inst_seq_ptr (DF H) lo ctx func PG G tn code (jump_to entry s) G1 tn1` by
    suspend "entry_ghost" >>
  `run_inst_seq_mem_ok code (jump_to entry s)` by
    suspend "entry_mem" >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
     (jump_to entry s,G,tn) []
     (OK (jump_to entry u with vs_inst_idx := LENGTH code),G1,tn1)` by
    suspend "entry_sequence" >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
     (jump_to entry u with vs_inst_idx := LENGTH code,G1,tn1) []
     (OK (jump_to cond (jump_to entry u)),G1,tn1)` by suspend "entry_final_jump" >>
  suspend "entry_compose"
QED

Resume for_storage_array_entry_full[entry_run]:
  qpat_x_assum `vs = GENLIST _ _` kall_tac >>
  qpat_x_assum `LenP s G tn` mp_tac >> simp[Abbr `LenP`] >> strip_tac >>
  Cases_on `dyn` >>
  simp[Abbr `code`, Abbr `u`, run_inst_seq_def,
      step_inst_base_opcode_eqs, exec_pure1_def, exec_pure2_def,
      eval_operand_def, lookup_var_update_var, jump_to_def, bool_to_word_def] >>
  Cases_on `lvo` >> gvs[Abbr `Written`, eval_operand_def] >>
  simp[lookup_var_update_var, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, w2n_n2w, dimword_def, LESS_MOD, bool_to_word_def, NOT_LESS] >>
  gvs[lookup_var_def] >>
  simp[FLOOKUP_UPDATE, w2n_n2w, dimword_def, LESS_MOD, bool_to_word_def, NOT_LESS]
QED

Resume for_storage_array_entry_full[entry_ghost]:
  `!i s u tn. scalar_shape i /\ step_inst_base i s = OK u ==>
     step_taint i s u tn = tn with t_var :=
       set_var_taint tn.t_var i.inst_outputs (out_taint tn i s)` by
    (rpt gen_tac >> strip_tac >>
     drule_all scalar_ambient_taint >> strip_tac >>
     simp[taint_component_equality] >>
     simp[step_taint_def]) >>
  qpat_x_assum `vs = GENLIST _ _` kall_tac >>
  qpat_x_assum `LenP s G tn` mp_tac >> simp[Abbr `LenP`] >> strip_tac >>
  reverse (Cases_on `dyn`)
  >- (simp[Abbr `code`, Once inst_seq_ptr_def, step_inst_base_opcode_eqs,
           exec_pure1_def, eval_operand_def, jump_to_def] >>
      conj_tac
      >- (irule scalar_ptr_inst_ok_lo >>
          simp[scalar_shape_def, scalar_binary_def, scalar_unary_def,
               op_prov_def, op_taint_def, jump_to_def,
               allocas_from_def, allocas_below_fmp_def] >>
          fs[allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
      simp[scalar_shape_def, scalar_binary_def, scalar_unary_def,
           step_inst_base_opcode_eqs, exec_pure1_def, eval_operand_def,
           jump_to_def, set_var_taint_def, out_taint_def, op_taint_def] >>
      simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
           op_prov_def, Abbr `G1`, Abbr `tn1`, inst_seq_ptr_def, DRESTRICT_UNIV]) >>
  Cases_on `lvo` >> gvs[Abbr `Written`, eval_operand_def] >>
  (fs[lookup_var_def, op_prov_def, op_taint_def] >>
  simp[NoAsms, Abbr `code`, Once inst_seq_ptr_def,
       step_inst_base_opcode_eqs, exec_pure1_def, eval_operand_def,
       jump_to_def] >>
  conj_tac
  >- (((irule scalar_ptr_inst_ok_lo >>
      simp[scalar_shape_def, scalar_binary_def, scalar_unary_def,
           mk_inst_def, op_prov_def, op_taint_def,
           allocas_from_def, allocas_below_fmp_def, jump_to_def] >>
      fs[allocas_from_def, allocas_below_fmp_def] >> (metis_tac[scalar_shape_def, scalar_binary_def, scalar_unary_def, mk_inst_def, op_prov_def, op_taint_def, allocas_from_def, allocas_below_fmp_def, jump_to_def, scalar_ptr_inst_ok_lo])))) >>
  simp[scalar_shape_def, scalar_binary_def, scalar_unary_def,
       mk_inst_def, step_inst_base_opcode_eqs, exec_pure1_def,
       eval_operand_def, jump_to_def, set_var_taint_def,
       out_taint_def, op_taint_def] >>
  simp[NoAsms, step_prov_def, set_prov_def, out_prov_def,
       first_prov_def, op_prov_def, FLOOKUP_DRESTRICT, mk_inst_def] >>
  simp[Abbr `G1`, Abbr `tn1`, cj 1 inst_seq_ptr_def] >>
  simp[NoAsms, Excl "step_taint_inst_idx", Excl "step_taint_inst_idx_left",
       Excl "step_taint_inst_idx_right", Once inst_seq_ptr_def] >>
  conj_tac
  >- (irule scalar_ptr_inst_ok_lo >>
      simp[scalar_shape_def, scalar_binary_def, scalar_unary_def,
           op_prov_def, op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
           allocas_from_def, allocas_below_fmp_def, update_var_def] >>
      fs[allocas_from_def, allocas_below_fmp_def, op_prov_def, op_taint_def] >>
      metis_tac[]) >>
  simp[Excl "step_taint_inst_idx", Excl "step_taint_inst_idx_left",
       Excl "step_taint_inst_idx_right",
       step_inst_base_opcode_eqs, exec_pure1_def, exec_pure2_def,
       eval_operand_def, lookup_var_update_var, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE, w2n_n2w, dimword_def, LESS_MOD,
       bool_to_word_def, NOT_LESS] >>
  simp[Excl "step_taint_inst_idx", Excl "step_taint_inst_idx_left",
       Excl "step_taint_inst_idx_right",
       scalar_shape_def, scalar_binary_def, scalar_unary_def,
       step_inst_base_opcode_eqs, exec_pure1_def, exec_pure2_def,
       eval_operand_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, w2n_n2w, dimword_def, LESS_MOD,
       bool_to_word_def, NOT_LESS, set_var_taint_def, out_taint_def, op_taint_def] >>
  simp[NoAsms, Excl "step_taint_inst_idx", Excl "step_taint_inst_idx_left",
       Excl "step_taint_inst_idx_right", step_prov_def, set_prov_def, out_prov_def,
       first_prov_def, op_prov_def, FLOOKUP_DRESTRICT] >>
  (* ISZERO *)
  simp[NoAsms, Excl "step_taint_inst_idx", Excl "step_taint_inst_idx_left",
       Excl "step_taint_inst_idx_right", Once inst_seq_ptr_def] >>
  conj_tac >- (
    irule scalar_ptr_inst_ok_lo >>
    simp[scalar_shape_def, scalar_binary_def, scalar_unary_def,
         op_prov_def, op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
    qpat_assum `allocas_from lo s` mp_tac >>
    qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >>
    simp[allocas_from_def, allocas_below_fmp_def] >>
    metis_tac[]) >>
  simp[Excl "step_taint_inst_idx", Excl "step_taint_inst_idx_left",
       Excl "step_taint_inst_idx_right", step_inst_base_opcode_eqs,
       exec_pure1_def, eval_operand_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE, bool_to_word_def] >>
  simp[Excl "step_taint_inst_idx", Excl "step_taint_inst_idx_left",
       Excl "step_taint_inst_idx_right", scalar_shape_def, scalar_binary_def,
       scalar_unary_def, step_inst_base_opcode_eqs, exec_pure1_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       bool_to_word_def, set_var_taint_def, out_taint_def, op_taint_def] >>
  simp[NoAsms, Excl "step_taint_inst_idx", Excl "step_taint_inst_idx_left",
       Excl "step_taint_inst_idx_right", step_prov_def, set_prov_def,
       out_prov_def, first_prov_def, op_prov_def, FLOOKUP_DRESTRICT] >>
  (* ASSERT *)
  simp[NoAsms, Excl "step_taint_inst_idx", Excl "step_taint_inst_idx_left",
       Excl "step_taint_inst_idx_right", Once inst_seq_ptr_def] >>
  conj_tac >- (
    irule scalar_ptr_inst_ok_lo >>
    simp[scalar_shape_def, scalar_binary_def, scalar_unary_def,
         op_prov_def, op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
    qpat_assum `allocas_from lo s` mp_tac >>
    qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >>
    simp[allocas_from_def, allocas_below_fmp_def] >>
    metis_tac[]) >>
  simp[Excl "step_taint_inst_idx", Excl "step_taint_inst_idx_left",
       Excl "step_taint_inst_idx_right", step_inst_base_opcode_eqs,
       exec_pure1_def, eval_operand_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE, bool_to_word_def] >>
  simp[Excl "step_taint_inst_idx", Excl "step_taint_inst_idx_left",
       Excl "step_taint_inst_idx_right", scalar_shape_def, scalar_binary_def,
       scalar_unary_def, step_inst_base_opcode_eqs, exec_pure1_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       bool_to_word_def, set_var_taint_def, out_taint_def, op_taint_def] >>
  simp[NoAsms, Excl "step_taint_inst_idx", Excl "step_taint_inst_idx_left",
       Excl "step_taint_inst_idx_right", step_prov_def, set_prov_def,
       out_prov_def, first_prov_def, op_prov_def, FLOOKUP_DRESTRICT] >>
  simp[inst_seq_ptr_def, pred_setTheory.INTER_ASSOC, DRESTRICT_UNIV])
QED
Resume for_storage_array_entry_full[entry_mem]:
  irule run_inst_seq_mem_ok_every >>
  Cases_on `dyn` >>
  simp[Abbr `code`, inst_mem_below_frontier_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def]
QED
Resume for_storage_array_entry_full[entry_sequence]:
  `isPREFIX code (DROP (jump_to entry s).vs_inst_idx eb.bb_instructions) /\
   lookup_block (jump_to entry s).vs_current_bb func.fn_blocks = SOME eb /\
   ~(jump_to entry s).vs_halted` by simp[jump_to_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
   FILTER (\i. i.inst_opcode = GAS) code = []` by
    (Cases_on `dyn` >> simp[Abbr `code`, is_terminator_def]) >>
  drule_all run_inst_seq_gas_origin_ptr_path >>
  simp[jump_to_def]
QED
Resume for_storage_array_entry_full[entry_final_jump]:
  `jump_to cond (jump_to entry u with vs_inst_idx := LENGTH code) =
   jump_to cond (jump_to entry u)` by simp[jump_to_def] >>
  pop_assum (SUBST1_TAC o SYM) >>
  irule jmp_origin_ptr_path >>
  simp[jump_to_def, get_instruction_def, EL_LENGTH_APPEND_0] >>
  conj_tac >- (Cases_on `dyn` >> simp[Abbr `u`, update_var_def]) >>
  conj_tac >- (qexists_tac `eid + LENGTH code` >> simp[]) >>
  qpat_x_assum `allocas_from _ _`
    (mp_tac o REWRITE_RULE [allocas_from_def]) >>
  qpat_x_assum `ctx_has_dalloca _ ==> allocas_below_fmp _`
    (mp_tac o REWRITE_RULE [allocas_below_fmp_def]) >>
  Cases_on `dyn` >>
  simp[Abbr `u`, jump_to_def, update_var_def, allocas_from_def,
       allocas_below_fmp_def] >> metis_tac[]
QED
Resume for_storage_array_entry_full[entry_compose]:
  `!cfg a b C U r E V.
     gas_origin_ptr_path cfg a [] (OK b,C,U) /\
     gas_origin_ptr_path cfg (b,C,U) [] (r,E,V) ==>
     gas_origin_ptr_path cfg a [] (r,E,V)` by
    (POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     qpat_assum `gas_origin_ptr_path _ a _ _`
       (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
     disch_then (qspecl_then [`b`, `C`, `U`, `[]`, `r`, `E`, `V`] mp_tac) >>
     simp[]) >>
  first_assum irule >>
  qexistsl [`G`, `tn`, `jump_to entry s`] >> simp[] >>
  first_assum irule >>
  qexistsl [`G1`, `tn1`, `jump_to entry u with vs_inst_idx := LENGTH code`] >> simp[]
QED
Resume for_storage_array_entry_full[entry_post]:
  qabbrev_tac `t = jump_to cond (jump_to entry u)` >>
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
   t.vs_alloca_next = s.vs_alloca_next /\ t.vs_fmp = s.vs_fmp /\
   t.vs_initial_fmp = s.vs_initial_fmp /\ t.vs_call_ctx = s.vs_call_ctx /\
   t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
   t.vs_immutables = s.vs_immutables` by
    (Cases_on `dyn` >> simp[Abbr `t`, Abbr `u`, jump_to_def, update_var_def]) >>
  `tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
   tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm` by
    (Cases_on `dyn` >> simp[Abbr `tn1`]) >>
  `!x. x NOTIN Written ==> lookup_var x t = lookup_var x s /\
       FLOOKUP G1 x = FLOOKUP G x /\ op_taint tn1 (Var x) = op_taint tn (Var x)` by
    (Cases_on `dyn` >>
     simp[Abbr `t`, Abbr `Written`, Abbr `G1`, Abbr `tn1`, Abbr `u`,
          jump_to_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
          FLOOKUP_DRESTRICT, op_taint_def, SF CONJ_ss]) >>
  `!x. not_fresh_at sa0 x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP G1 x = FLOOKUP G x /\ op_taint tn1 (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> first_assum (qspecl_then [`x`] mp_tac) >> simp[]) >>
  `!name b z. local_region c0 es.scopes t name b z <=>
              local_region c0 es.scopes s name b z` by
    (rpt gen_tac >> irule local_region_lookup_cong >> rpt strip_tac >>
     rename1 `FLOOKUP c0.ce_vars nm = SOME (PtrVar (Var q) sz)` >>
     `not_fresh_at sa0 q` by
       (qpat_assum `local_ptrs_reserved _ _`
          (drule o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [local_ptrs_reserved_def]) >>
        simp[]) >> simp[]) >>
  conj_tac >- suspend "entry_base" >>
  conj_tac >- suspend "entry_buf" >>
  conj_tac >- suspend "entry_len" >>
  qpat_assum `dyn ==> _` mp_tac >> Cases_on `dyn` >>
  simp[Abbr `t`, Abbr `u`, Abbr `G1`, Abbr `tn1`, jump_to_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def]
QED
Resume for_storage_array_entry_full[entry_base]:
  qexists_tac `off` >> ntac 11 (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_x_assum `vs = GENLIST _ _` kall_tac >>
  qpat_x_assum `len = LENGTH vs` kall_tac >>
  conj_tac
  >- (`!x. x IN Written ==> not_local_ptr c0 es.scopes x` by
        (rpt strip_tac >> irule exprSimOperandsTheory.fresh_not_local_ptr >>
         qexists_tac `sa0` >> simp[] >> strip_tac >>
         qpat_assum `!x. not_fresh_at sa0 x ==> x NOTIN Written`
           (qspec_then `x` mp_tac) >> simp[]) >>
      `not_local_ptr c0 es.scopes idx` by
        (first_assum irule >> Cases_on `dyn` >> simp[Abbr `Written`]) >>
      Cases_on `dyn` >> simp[Abbr `t`, Abbr `u`, stmt_state_rel_jump_to]
      >- (`not_local_ptr c0 es.scopes bad` by
            (first_assum irule >> simp[Abbr `Written`]) >>
          `not_local_ptr c0 es.scopes good` by
            (first_assum irule >> simp[Abbr `Written`]) >>
          ntac 3 (irule stmt_state_rel_update_var >> simp[])) >>
      irule stmt_state_rel_update_var >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (irule ghost_inv_at_exterior_frame >>
      qexistsl [`G`, `es`, `s`, `sa0`, `tn`] >> simp[]) >>
  conj_tac
  >- (irule return_buf_frame_frame >> qexistsl [`c0`, `s`, `sa0`] >> simp[]) >>
  conj_tac
  >- (irule ret_pc_ok_frame >> qexistsl [`c0`, `s`, `sa0`] >> simp[]) >>
  suspend "entry_frame"
QED
Resume for_storage_array_entry_full[entry_frame]:
  qpat_x_assum `Fr c0 es s G tn` mp_tac >> simp[Abbr `Fr`] >> strip_tac >>
  conj_tac
  >- (irule alloca_history_jump >> conj_tac
      >- simp[Abbr `t`, jump_to_def] >>
      qexists_tac `s` >> simp[]) >>
  conj_tac
  >- (qpat_assum `ctx_has_dalloca _ ==> allocas_below_fmp s` mp_tac >>
      simp[allocas_below_fmp_def] >> gvs[allocas_below_fmp_def]) >>
  conj_tac
  >- (qpat_assum `alloca_frame _ _ _ _ _ _ s` mp_tac >>
      simp[alloca_frame_def] >> gvs[alloca_frame_def]) >>
  first_assum ACCEPT_TAC
QED
Resume for_storage_array_entry_full[entry_buf]:
  qpat_assum `!x. x NOTIN Written ==> _`
    (qspec_then `p` (drule_then strip_assume_tac)) >>
  qpat_x_assum `Buf s G tn` mp_tac >>
  simp[Abbr `Buf`, ptr_covers_def, SF CONJ_ss] >> metis_tac[]
QED
Resume for_storage_array_entry_full[entry_len]:
  qpat_x_assum `vs = GENLIST _ _` kall_tac >>
  qpat_x_assum `LenP s G tn` mp_tac >>
  namedCases_on `lvo` ["w", "v", "lbl"]
  >- simp[Abbr `LenP`, eval_operand_def, op_prov_def, op_taint_def]
  >- (`v NOTIN Written` by
        (qpat_assum `!x. Var v = Var x ==> x NOTIN Written`
           (qspec_then `v` mp_tac) >> simp[]) >>
      qpat_assum `!x. x NOTIN Written ==> _`
        (qspec_then `v` (drule_then strip_assume_tac)) >>
      simp[Abbr `LenP`, eval_operand_def, op_prov_def]) >>
  qpat_assum `!l. Label lbl <> Label l` (qspec_then `lbl` mp_tac) >> simp[]
  >> (gvs[])
QED
Finalise for_storage_array_entry_full

(* Current observed children need no saved value or current array length. *)
Theorem for_storage_current_child_holds:
  stmt_state_rel H ctx func cenv cx ee s /\
  storage_place_observed H (StoragePlace tr slot tyv) /\
  regions_consistent (FST H) /\
  storage_well_formed_on cx ee (FST H) /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  well_formed_type_value tyv /\ 0 < type_slot_size tyv ==>
  storage_holds cx tr typ (PlaceR (StoragePlace tr slot tyv)) slot ee s
Proof
  strip_tac >>
  `w2n slot + type_slot_size tyv <= dimword (:256)` by
    (qpat_x_assum `storage_place_observed _ _` mp_tac >>
     simp[storage_place_observed_def] >> strip_tac >>
     drule storage_subregion_bounds >> strip_tac >>
     `w2n root + type_slot_size tv <= dimword (:256)` by
       metis_tac[regions_consistent_def] >>
     `delta < dimword (:256) /\ w2n root + delta < dimword (:256)` by
       decide_tac >>
     simp[word_add_def, w2n_n2w] >> decide_tac) >>
  drule_all aug_place_observed_slots_in_range >> strip_tac >>
  drule storage_copy_initial_agree >>
  disch_then (qspec_then `tr` assume_tac) >>
  `storage_read_live H tr (get_storage cx ee tr) slot tyv` by
    (irule storage_place_observed_read_live >> simp[]) >>
  drule_all storage_range_agree_of_live >> strip_tac >>
  irule pop_storage_holds >> simp[]
QED

(* Decode the current element before pushing its scope. Neither action
   consumes gas observations. *)
Theorem for_storage_current_read_push:
  !cx tr slot tyv id typ ei s.
    storage_holds cx tr typ (PlaceR (StoragePlace tr slot tyv)) slot ei s /\
    evaluate_type (get_tenv cx) typ = SOME tyv ==>
    ?v. read_result cx (PlaceR (StoragePlace tr slot tyv)) ei = (INL v,ei) /\
        value_has_type tyv v /\ val_wf tyv v /\
        push_scope_with_var id tyv v ei =
        (INL (),
         (\ee v.
            ee with
            scopes :=
              fmupdate id
                <|assignable := F; type := tyv; value := v; popped := []|>
                FEMPTY::ee.scopes) ei v) /\
        (!tail.
           read_result cx (PlaceR (StoragePlace tr slot tyv))
             (ei with gas_obs := tail) = (INL v,ei with gas_obs := tail)) /\
        !tail.
          bind (read_result cx (PlaceR (StoragePlace tr slot tyv)))
            (\w. push_scope_with_var id tyv w) (ei with gas_obs := tail) =
          (INL (),
           (\ee v.
              ee with
              scopes :=
                fmupdate id
                  <|assignable := F; type := tyv; value := v; popped := []|>
                  FEMPTY::ee.scopes) ei v with gas_obs := tail)
Proof
  simp[LET_THM] >> rpt gen_tac >> strip_tac >>
  drule_all storage_holds_decode >>
  disch_then (qx_choose_then `v` strip_assume_tac) >>
  drule_all (cj 1 vyperTypeStatePreservationTheory.decode_value_well_typed) >>
  strip_tac >>
  drule_all storage_holds_value_bounds >> strip_tac >>
  drule_then assume_tac exprSimMemorySourceTheory.read_result_gas_obs >>
  qexists_tac `v` >>
  simp[push_scope_with_var_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def, evaluation_state_component_equality]
QED

Theorem for_storage_current_child_ptr:
  !H ctx func cenv cx ee s D lo d G tn tr slot tyv typ p tag.
  stmt_state_rel H ctx func cenv cx ee s /\
  ghost_inv_at D lo d cenv cx ee G tn s /\
  dead_lo_ok H D lo cenv cx /\
  storage_place_observed H (StoragePlace tr slot tyv) /\
  0 < type_slot_size tyv /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  p.ptr_location = slot_loc tr /\
  eval_operand p.ptr_operand s = SOME slot /\
  op_taint tn p.ptr_operand = {} ==>
  ptr_vv_ok cx typ (PlaceR (StoragePlace tr slot tyv))
    (LocatedValue tag p) ee G tn s
Proof
  rpt gen_tac >> strip_tac >>
  drule stmt_state_rel_state_rel >> strip_tac >>
  drule state_rel_call_ctx_rel >>
  simp[call_ctx_rel_def] >> strip_tac >>
  `stor_taint_ok_at D tn s` by
    (gvs[ghost_inv_at_def]) >>
  drule_all storage_place_observed_read_live >>
  disch_then (qspec_then
    `if tr then s.vs_transient s.vs_call_ctx.cc_address
     else (s.vs_accounts s.vs_call_ctx.cc_address).storage` assume_tac) >>
  Cases_on `tr` >>
  gvs[ptr_vv_ok_def, slot_loc_def] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `storage_read_live _ _ _ _ _` mp_tac >>
  simp[storage_read_live_def] >>
  disch_then (qspecl_then [`w2n k`, `b`] mp_tac) >>
  (impl_tac >-
    (qpat_x_assum `stor_taint_ok_at _ _ _` mp_tac >>
     gvs[stor_taint_ok_at_def, dead_lo_ok_def, cx_dead_def, SUBSET_DEF] >>
     simp[pairTheory.FORALL_PROD] >> strip_tac >> first_x_assum drule >> simp[])) >>
  simp[]
QED

(* The allocation endpoint is selected before the horizon.  Declaration is
   solely compiler bookkeeping: the source scopes are unchanged. *)
Theorem for_storage_array_allocate_full:
  !DF lo d explicit ctx func PG cx st0 c0 e0 sa0 s0 G0 tn0 ee env sd sdecl sc
      bc id typ tyv tr slot bd vs len nb p lvo s G tn.
    declare_local c0 id typ sd = (bc,sdecl) /\
    emit_local_alloca bc id sdecl = ((),sc) /\ c0.ce_alloca_locals /\
    p = STRING #"%" (toString sd.cs_next_var) /\
    nb = type_memory_bytes c0 typ /\
    FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) nb) /\
    fn_has_code sd sc func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved c0 sd /\ local_ptrs_reserved c0 sa0 /\
    sa0.cs_next_var <= sd.cs_next_var /\
    (!x sz. c0.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
    (!x sz. c0.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
    (!x. lvo = Var x ==> x <> p) /\ nb < 2 ** 256 /\
    32 * type_slot_size tyv <= nb /\ allocas_from lo s /\
    lo <= s.vs_alloca_next /\ ~s.vs_halted /\
    s.vs_current_bb = sd.cs_current_bb /\
    s.vs_inst_idx = LENGTH sd.cs_current_insts /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
         (\H s G tn.
            len = LENGTH vs /\ len <= bound_length bd /\
            vs =
            GENLIST
              (\j.
                 PlaceR
                   (StoragePlace tr
                      ((case bd of Fixed v => slot | Dynamic v1 => slot + 1w) +
                       n2w (j * type_slot_size tyv)) tyv)) len /\
            (?off.
               slot = n2w off /\
               MEM (StorageRoot tr off (ArrayTV tyv bd)) ee.storage_trace) /\
            evaluate_type (get_tenv cx) typ = SOME tyv /\
            well_formed_type_value tyv /\ lookup_scopes id ee.scopes = NONE /\
            expr_sim_inv c0 cx env ee /\ ce_locals_declared c0 env /\
            locals_alloc_ok c0 env /\ cenv_top_ext c0 c0 ee.scopes /\
            stmt_state_rel H ctx func c0 cx ee s /\
            storage_well_formed_on cx ee (FST H) /\
            ghost_inv_at (DF H) lo d c0 cx ee G tn s /\
            return_buf_frame d c0 sa0 s /\ ret_pc_ok c0 sa0 s /\
            (\c ee s G tn.
               alloca_history func s /\
               (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
               s0.vs_alloca_next <= s.vs_alloca_next /\
               (!x w.
                  not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
                  lookup_var x s = SOME w) /\
               (!aid b.
                  FLOOKUP s0.vs_allocas aid = SOME b ==>
                  FLOOKUP s.vs_allocas aid = SOME b) /\
               (!x. not_fresh_at sa0 x ==>
                    FLOOKUP G x = FLOOKUP G0 x /\
                    op_taint tn (Var x) = op_taint tn0 (Var x)) /\
               alloca_frame c0 e0 sa0 s0 c ee s /\
               !aid off sz i.
                 FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
                 aid < sa0.cs_next_id /\
                 (!name b sz'.
                    local_region c0 e0.scopes s0 name b sz' ==>
                    off + sz <= b \/ b + sz' <= off) /\ off <= i /\
                 i < off + sz /\ i IN tn.t_mem ==>
                 i IN tn0.t_mem) c0 ee s G tn) H s G tn) /\
    (\s G tn.
       eval_operand lvo s = SOME (n2w len) /\ op_taint tn lvo = {} /\
       op_prov G lvo = NONE) s G tn ==>
    ?dst u t G1 tn1.
      step_inst_base (mk_inst sd.cs_next_id ALLOCA [Lit (n2w nb)] [p]) s = OK u /\
      t = u with vs_inst_idx := SUC s.vs_inst_idx /\
      G1 = step_prov PG G (mk_inst sd.cs_next_id ALLOCA [Lit (n2w nb)] [p]) u /\
      tn1 = step_taint (mk_inst sd.cs_next_id ALLOCA [Lit (n2w nb)] [p]) s u tn /\
      !H. valid_horizon cx st0 H ee.storage_trace ==>
          gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
            (OK t,G1,tn1) /\
          (\H s G tn.
             len = LENGTH vs /\ len <= bound_length bd /\
             vs =
             GENLIST
               (\j.
                  PlaceR
                    (StoragePlace tr
                       ((case bd of Fixed v => slot | Dynamic v1 => slot + 1w) +
                        n2w (j * type_slot_size tyv)) tyv)) len /\
             (?off.
                slot = n2w off /\
                MEM (StorageRoot tr off (ArrayTV tyv bd)) ee.storage_trace) /\
             evaluate_type (get_tenv cx) typ = SOME tyv /\
             well_formed_type_value tyv /\ lookup_scopes id ee.scopes = NONE /\
             expr_sim_inv c0 cx env ee /\ ce_locals_declared c0 env /\
             locals_alloc_ok c0 env /\ cenv_top_ext c0 c0 ee.scopes /\
             stmt_state_rel H ctx func c0 cx ee s /\
             storage_well_formed_on cx ee (FST H) /\
             ghost_inv_at (DF H) lo d c0 cx ee G tn s /\
             return_buf_frame d c0 sa0 s /\ ret_pc_ok c0 sa0 s /\
             (\c ee s G tn.
                alloca_history func s /\
                (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
                s0.vs_alloca_next <= s.vs_alloca_next /\
                (!x w.
                   not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
                   lookup_var x s = SOME w) /\
                (!aid b.
                   FLOOKUP s0.vs_allocas aid = SOME b ==>
                   FLOOKUP s.vs_allocas aid = SOME b) /\
                (!x. not_fresh_at sa0 x ==>
                     FLOOKUP G x = FLOOKUP G0 x /\
                     op_taint tn (Var x) = op_taint tn0 (Var x)) /\
                alloca_frame c0 e0 sa0 s0 c ee s /\
                !aid off sz i.
                  FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
                  aid < sa0.cs_next_id /\
                  (!name b sz'.
                     local_region c0 e0.scopes s0 name b sz' ==>
                     off + sz <= b \/ b + sz' <= off) /\ off <= i /\
                  i < off + sz /\ i IN tn.t_mem ==>
                  i IN tn0.t_mem) c0 ee s G tn) H t G1 tn1 /\
          (\s G tn.
             eval_operand lvo s = SOME (n2w len) /\ op_taint tn lvo = {} /\
             op_prov G lvo = NONE) t G1 tn1 /\
          (\dst s G tn.
             lookup_var p s = SOME dst /\
             FLOOKUP s.vs_allocas sd.cs_next_id = SOME (w2n dst,nb) /\
             ptr_covers G tn p s nb /\ 32 * type_slot_size tyv <= nb /\
             w2n dst + nb < 2 ** 256 /\ w2n dst + nb <= s.vs_alloca_next /\
             !name b sz.
               local_region c0 ee.scopes s name b sz ==>
               w2n dst + nb <= b \/ b + sz <= w2n dst) dst t G1 tn1 /\
          ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
          t.vs_inst_idx = LENGTH sc.cs_current_insts
Proof
  rpt gen_tac >>
  abbrev_lambda_tac "Fr" 5 0 `alloca_history func s /\ _` >>
  abbrev_lambda_tac "Base" 4 0 `len = LENGTH vs /\ _` >>
  abbrev_lambda_tac "SavedLen" 3 0 `eval_operand lvo s = SOME (n2w len) /\ _` >>
  abbrev_lambda_tac "Buf" 4 0 `lookup_var p s = SOME dst /\ _` >>
  rpt strip_tac >>
  `compile_alloc_buffer nb sd =
    (<|buf_operand := Var p; buf_size := nb|>,sc)` by
    (drule_all for_array_declare_emit_alloc_buffer >> gvs[]) >>
  `?u dst. step_inst_base
     (mk_inst sd.cs_next_id ALLOCA [Lit (n2w nb)] [p]) s = OK u /\
     lookup_var p u = SOME dst` by
    (simp[Once step_inst_base_def, mk_inst_def, exec_alloca_def] >>
     Cases_on `FLOOKUP s.vs_allocas sd.cs_next_id` >>
     simp[AllCaseEqs(), update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
     Cases_on `x` >> simp[FLOOKUP_UPDATE]) >>
  qexistsl_tac [`dst`, `u`, `u with vs_inst_idx := SUC s.vs_inst_idx`,
    `step_prov PG G (mk_inst sd.cs_next_id ALLOCA [Lit (n2w nb)] [p]) u`,
    `step_taint (mk_inst sd.cs_next_id ALLOCA [Lit (n2w nb)] [p]) s u tn`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  ntac 3 (conj_tac >- REFL_TAC) >>
  qx_gen_tac `H` >> strip_tac >>
  `Base H s G tn` by metis_tac[] >>
  qpat_x_assum `!H. valid_horizon _ _ _ _ ==> _` kall_tac >>
  qpat_x_assum `Base H s G tn` mp_tac >>
  simp_tac pure_ss [Abbr `Base`, Abbr `Fr`] >>
  CONV_TAC (LAND_CONV (DEPTH_CONV BETA_CONV)) >>
  disch_then strip_assume_tac >>
  drule compile_alloc_buffer_emission >> strip_tac >>
  drule emit_inst_extends >> strip_tac >>
  qpat_x_assum `sx = _` SUBST_ALL_TAC >>
  qpat_x_assum `<|buf_operand := _; buf_size := _|>.buf_operand = _`
    (SUBST_ALL_TAC o SYM o SIMP_RULE (srw_ss()) []) >>
  qpat_x_assum `sc.cs_current_bb = _`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  qpat_x_assum `sc.cs_current_insts = _`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst sd.cs_next_id ALLOCA [Lit (n2w nb)] [p])` by
    (drule_all fn_has_code_same_block >> strip_tac >>
     qexists_tac `bb` >> simp[] >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `gas_origin_ptr_edge (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G (mk_inst sd.cs_next_id ALLOCA [Lit (n2w nb)] [p]) u,
     step_taint (mk_inst sd.cs_next_id ALLOCA [Lit (n2w nb)] [p]) s u tn)` by
    (irule ifexp_alloca_origin_ptr_edge >> simp[] >>
     qpat_x_assum `get_instruction _ _ = _` mp_tac >> simp[]) >>
  `nb < dimword (:256)` by
    (qpat_x_assum `nb < _` mp_tac >> simp[dimword_def]) >>
  `<|buf_operand := Var p; buf_size := nb|>.buf_operand = Var p` by simp[] >>
  drule_all compile_alloc_buffer_raw_resources >> strip_tac >>
  drule_all alloca_step_contracts >> strip_tac >>
  conj_tac >-
    (qpat_x_assum `gas_origin_ptr_edge _ _ _ _` mp_tac >>
     simp[] >> strip_tac >>
     irule (Q.INST [`left` |-> `[]`, `right` |-> `[]`]
       (SPEC_ALL (cj 2 gas_origin_ptr_path_rules)) |> SRULE []) >>
     goal_assum (drule_at Any) >>
     irule (cj 1 gas_origin_ptr_path_rules) >> simp[]) >>
  drule_all compile_alloc_buffer_ghost_frame_at >>
  disch_then (qspec_then `PG` assume_tac) >>
  drule_all alloca_step_buffer_resources >>
  disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >>
  drule_all alloca_step_frame_effects >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
  `alloca_inv s /\ alloca_inv u` by
    (metis_tac[stmt_state_rel_def]) >>
  `s.vs_alloca_next <= u.vs_alloca_next` by
    (qpat_x_assum `step_inst_base _ s = OK u` mp_tac >>
     simp[Once step_inst_base_def, mk_inst_def] >>
     strip_tac >> drule venomMemPropsTheory.exec_alloca_alloca_next_mono >> simp[]) >>
  `!x. not_fresh_at sa0 x ==> not_fresh_at sd x /\ x <> p` by
    (rpt strip_tac >>
     `not_fresh_at sd x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     metis_tac[]) >>
  `alloca_history func (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (drule_all alloca_history_base_step >> simp[mk_inst_def, is_terminator_def]) >>
  `w2n dst = b` by
    (qpat_x_assum `eval_operand (Var p) u = _` mp_tac >>
     simp[eval_operand_def] >> strip_tac >>
     `b < dimword (:256)` by decide_tac >> simp[]) >>
  `b+nb <= u.vs_alloca_next` by
    (irule alloca_site_registered_below >> simp[] >>
     qexists_tac `sd.cs_next_id` >> metis_tac[]) >>
  `!name b sz. local_region c0 ee.scopes u name b sz <=>
      local_region c0 ee.scopes s name b sz` by
    (rpt gen_tac >> irule local_region_lookup_cong >>
     rpt strip_tac >>
     qpat_x_assum `local_ptrs_reserved c0 sd` mp_tac >>
     simp[local_ptrs_reserved_def] >> strip_tac >> metis_tac[]) >>
  `not_local_ptr c0 ee.scopes p` by
    (irule fresh_not_local_ptr >> metis_tac[]) >>
  `!name b' sz. local_region c0 ee.scopes u name b' sz ==>
      b+nb <= b' \/ b'+sz <= b` by
    (rpt strip_tac >>
     irule (INST_TYPE [``:'a`` |-> ``:256``] alloca_clear_of_locals) >>
     qexistsl_tac [`H`, `c0`, `ctx`, `cx`, `ee`, `func`,
       `mk_inst sd.cs_next_id ALLOCA [Lit (n2w nb)] [p]`, `name`, `p`, `u`] >>
     simp[mk_inst_def]) >>
  `return_buf_frame d c0 sa0 u /\ ret_pc_ok c0 sa0 u` by
    (conj_tac
     >- (irule return_buf_frame_frame >> goal_assum (drule_at Any) >> simp[] >>
         qexistsl_tac [`c0`, `sa0`] >> simp[] >> rpt strip_tac >> metis_tac[]) >>
     irule ret_pc_ok_frame >> goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`c0`, `sa0`] >> simp[] >> rpt strip_tac >> metis_tac[]) >>
  `alloca_frame c0 e0 sa0 s0 c0 ee u` by
    (qpat_x_assum `alloca_frame _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac [alloca_frame_def] >> rpt strip_tac >>
     first_x_assum drule_all >> simp[] >> metis_tac[]) >>
  `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
    aid < sa0.cs_next_id /\
    (!name b sz'. local_region c0 e0.scopes s0 name b sz' ==>
      off+sz <= b \/ b+sz' <= off) /\
    off <= i /\ i < off+sz /\
    i IN (step_taint (mk_inst sd.cs_next_id ALLOCA [Lit (n2w nb)] [p]) s u tn).t_mem ==>
    i IN tn0.t_mem` by
    (map_every qx_gen_tac [`aid0`, `base0`, `size0`, `byte0`] >> strip_tac >>
     `FLOOKUP s.vs_allocas aid0 = SOME (base0,size0)` by metis_tac[] >>
     `base0+size0 <= s.vs_alloca_next` by
       (irule alloca_site_registered_below >> simp[] >> qexists_tac `aid0` >> simp[]) >>
     `byte0 < s.vs_alloca_next` by decide_tac >>
     `byte0 IN tn.t_mem` by metis_tac[] >>
     qpat_x_assum `!aid off sz i. _ ==> i IN tn0.t_mem` irule >>
     simp[] >> qexistsl_tac [`aid0`, `base0`, `size0`] >> simp[] >>
     rpt strip_tac >> metis_tac[]) >>
  `SavedLen u (step_prov PG G (mk_inst sd.cs_next_id ALLOCA [Lit (n2w nb)] [p]) u)
    (step_taint (mk_inst sd.cs_next_id ALLOCA [Lit (n2w nb)] [p]) s u tn)` by
    (qpat_x_assum `SavedLen _ _ _` mp_tac >>
     simp_tac pure_ss [Abbr `SavedLen`] >> BETA_TAC >>
     namedCases_on `lvo` ["w", "x", "lab"]
     >- simp[NoAsms, eval_operand_def, op_prov_def, op_taint_def]
     >- (simp[NoAsms, eval_operand_def, op_prov_def] >>
         qpat_x_assum `!p'. p' <> p ==> lookup_var p' u = _ /\ _`
           (qspec_then `x` mp_tac) >>
         (impl_tac >-
           (qpat_assum `!v. Var x = Var v ==> v <> p`
              (qspec_then `x` mp_tac) >> simp[NoAsms])) >>
         disch_then (fn th => simp[NoAsms, th])) >>
     drule (cj 3 bodyPtrMakeArrayAllocBufferTheory.literal_alloca_static_frame) >>
     disch_then (fn th => simp[NoAsms, eval_operand_def, op_prov_def, op_taint_def, th])) >>
  `!k name a sz. local_region c0 ee.scopes (u with vs_inst_idx := k) name a sz <=>
      local_region c0 ee.scopes u name a sz` by
    (simp[NoAsms, local_region_def, blockPrefixEquivTheory.lookup_var_set_inst_idx]) >>
  `!k. alloca_frame c0 e0 sa0 s0 c0 ee (u with vs_inst_idx := k) <=>
      alloca_frame c0 e0 sa0 s0 c0 ee u` by
    (qpat_assum `!k name a sz. local_region _ _ (_ with vs_inst_idx := _) _ _ _ <=> _`
       (fn th => simp[NoAsms, alloca_frame_def, th])) >>
  `!k. return_buf_frame d c0 sa0 (u with vs_inst_idx := k) <=>
      return_buf_frame d c0 sa0 u` by
    (namedCases_on `d` ["", "buf"] >- simp[NoAsms, return_buf_frame_def] >>
     PairCases_on `buf` >>
     simp[NoAsms, return_buf_frame_def, blockPrefixEquivTheory.lookup_var_set_inst_idx]) >>
  `!k. ret_pc_ok c0 sa0 (u with vs_inst_idx := k) <=> ret_pc_ok c0 sa0 u` by
    simp[NoAsms, ret_pc_ok_def, blockPrefixEquivTheory.lookup_var_set_inst_idx] >>
  drule stmt_state_rel_allocas_below_fmp >> strip_tac >>
  qpat_x_assum `SavedLen u _ _` mp_tac >>
  simp_tac pure_ss [Abbr `SavedLen`, Abbr `Buf`] >> BETA_TAC >>
  simp[NoAsms, stmt_state_rel_inst_idx, ghostPcTransportPtrTheory.ghost_inv_at_inst_idx,
       ghostPcTransportPtrTheory.ptr_covers_inst_idx, ghostPcTransportPtrTheory.eval_operand_inst_idx,
       blockPrefixEquivTheory.lookup_var_set_inst_idx] >> strip_tac >>
  qpat_x_assum `p = STRING _ _` SUBST_ALL_TAC >>
  qpat_x_assum `nb = type_memory_bytes _ _` SUBST_ALL_TAC >>
  qpat_x_assum `s.vs_inst_idx = LENGTH _` SUBST_ALL_TAC >>
  qpat_x_assum `!name a sz. local_region _ _ u _ _ _ <=> local_region _ _ s _ _ _`
    kall_tac >>
  conj_tac >-
    (conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qexists_tac `off` >> conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_x_assum `vs = GENLIST _ _` kall_tac >>
     simp[] >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `vs = GENLIST _ _` kall_tac >>
  simp[LENGTH_APPEND, ADD_COMM, dimword_def] >>
  conj_tac >-
    (qpat_assum `b + _ < dimword (:256)` mp_tac >> simp[NoAsms, dimword_def]) >>
  first_assum ACCEPT_TAC
QED

(* Pointwise body cleanup, with the frame still anchored at For entry. *)
Theorem for_storage_body_post_land_full:
  !DF lo d ctx shadow_ctx func PG cx c0 e0 sa0 sb s0 G0 tn0 tr slot dst tyv typ
      bd vs len nb id env p idx lvo sd body si lctx ei v bc bc1 sb0 sb1 sj tops
      bindings ret_ty env_b k off a rs H st0 s G tn raw ef G1 tn1 t exit incr.
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    supported_stmts tops bindings body /\ id NOTIN FDOM env.var_types /\
    evaluate_type (get_tenv cx) typ = SOME tyv /\ value_has_type tyv v /\
    type_stmts (extend_local env id typ F) ret_ty body = SOME env_b /\
    call_evaluation_safe cx (int_calls_stmts body) /\
    expr_sim_inv c0 cx env ei /\ lookup_scopes id ei.scopes = NONE /\
    ce_locals_declared c0 env /\ locals_alloc_ok c0 env /\
    cenv_top_ext c0 c0 ei.scopes /\
    cenv_top_ext c0 bc
      (ei with
       scopes :=
         fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
           FEMPTY::ei.scopes).scopes /\ same_frame c0 bc /\
    local_ptrs_reserved c0 sb0 /\ sa0.cs_next_id <= sb0.cs_next_id /\
    (!x. not_fresh_at sa0 x ==> not_fresh_at sb0 x) /\
    stmts_env bc (InLoop exit incr) ret_ty body sb0 = (bc1,sb1) /\
    (!x sz. c0.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x) /\
    emit_jmp_if_not_terminated incr sb1 = ((),sj) /\ fn_has_code sb1 sj func /\
    si.cs_current_bb = incr /\ si.cs_current_insts = [] /\
    sb.cs_current_bb = exit /\ sb.cs_current_insts = [] /\
    ~block_is_terminated sb /\ k < len /\ len = LENGTH vs /\
    len <= bound_length bd /\
    vs =
    GENLIST
      (\j.
         PlaceR
           (StoragePlace tr
              ((case bd of Fixed v => slot | Dynamic v1 => slot + 1w) +
               n2w (j * type_slot_size tyv)) tyv)) len /\ a::rs = DROP k vs /\
    slot = n2w off /\
    MEM (StorageRoot tr off (ArrayTV tyv bd)) ei.storage_trace /\
    well_formed_type_value tyv /\ s.vs_current_bb = sb0.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb0.cs_current_insts /\ ~s.vs_halted /\
    lookup_var idx s = SOME (n2w k) /\ FLOOKUP G idx = NONE /\
    op_taint tn (Var idx) = {} /\ eval_operand lvo s = SOME (n2w len) /\
    op_taint tn lvo = {} /\ op_prov G lvo = NONE /\
    eval_operand (Lit slot) s = SOME slot /\ op_taint tn (Lit slot) = {} /\
    lookup_var p s = SOME dst /\
    FLOOKUP s.vs_allocas sd.cs_next_id = SOME (w2n dst,nb) /\
    ptr_covers G tn p s nb /\ 32 * type_slot_size tyv <= nb /\
    w2n dst + nb < 2 ** 256 /\ w2n dst + nb <= s.vs_alloca_next /\
    (!name b sz.
       local_region c0 ei.scopes s name b sz ==>
       w2n dst + nb <= b \/ b + sz <= w2n dst) /\
    return_buf_frame d c0 sa0 s /\ ret_pc_ok c0 sa0 s /\
    body_stmts_full_ok cx body /\
    stmt_state_rel H ctx func bc cx
      (ei with
       scopes :=
         fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
           FEMPTY::ei.scopes) s /\
    storage_well_formed_on cx
      (ei with
       scopes :=
         fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
           FEMPTY::ei.scopes) (FST H) /\
    ghost_inv_at (DF H) lo d bc cx
      (ei with
       scopes :=
         fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
           FEMPTY::ei.scopes) G tn s /\
    (\c ee u GG tt.
       alloca_history func u /\
       (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
       s0.vs_alloca_next <= u.vs_alloca_next /\
       (!x w.
          not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
          lookup_var x u = SOME w) /\
       (!aid b.
          FLOOKUP s0.vs_allocas aid = SOME b ==>
          FLOOKUP u.vs_allocas aid = SOME b) /\
       (!x. not_fresh_at sa0 x ==>
            FLOOKUP GG x = FLOOKUP G0 x /\
            op_taint tt (Var x) = op_taint tn0 (Var x)) /\
       alloca_frame c0 e0 sa0 s0 c ee u /\
       !aid off sz i.
         FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
         (!name b sz'.
            local_region c0 e0.scopes s0 name b sz' ==>
            off + sz <= b \/ b + sz' <= off) /\ off <= i /\ i < off + sz /\
         i IN tt.t_mem ==>
         i IN tn0.t_mem) bc
      (ei with
       scopes :=
         fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
           FEMPTY::ei.scopes) s G tn /\
    (\H res ee GG tt u.
       ?c3.
         stmt_lands (InLoop exit incr) sb1 res u /\ ~u.vs_halted /\
         (res = INL () ==> ~block_is_terminated sb1 /\ c3 = bc1) /\
         cenv_top_ext bc c3 ee.scopes /\
         stmt_state_rel H ctx func c3 cx ee u /\
         storage_well_formed_on cx ee (FST H) /\ return_buf_frame d c3 sb1 u /\
         alloca_history func u /\ return_buf_sep d c3 ee u /\
         (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
         s.vs_alloca_next <= u.vs_alloca_next /\
         ghost_inv_at (DF H) lo d c3 cx ee GG tt u /\
         (!x w.
            not_fresh_at sb0 x /\ lookup_var x s = SOME w ==>
            lookup_var x u = SOME w) /\
         (!aid b.
            FLOOKUP s.vs_allocas aid = SOME b ==>
            FLOOKUP u.vs_allocas aid = SOME b) /\
         (!x. not_fresh_at sb0 x ==>
              FLOOKUP GG x = FLOOKUP G x /\
              op_taint tt (Var x) = op_taint tn (Var x)) /\
         alloca_frame bc
           (ei with
            scopes :=
              fmupdate id
                <|assignable := F; type := tyv; value := v; popped := []|>
                FEMPTY::ei.scopes) sb0 s c3 ee u /\
         !aid off sz i.
           FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ aid < sb0.cs_next_id /\
           (!name b sz'.
              local_region bc
                (ei with
                 scopes :=
                   fmupdate id
                     <|assignable := F; type := tyv; value := v; popped := []|>
                     FEMPTY::ei.scopes).scopes s name b sz' ==>
              off + sz <= b \/ b + sz' <= off) /\ off <= i /\ i < off + sz /\
           i IN tt.t_mem ==>
           i IN tn.t_mem) H raw ef G1 tn1 t /\
    (\GG tt u.
       lookup_var idx u = lookup_var idx s /\
       lookup_var p u = lookup_var p s /\
       eval_operand lvo u = eval_operand lvo s /\
       FLOOKUP GG idx = FLOOKUP G idx /\ FLOOKUP GG p = FLOOKUP G p /\
       op_prov GG lvo = op_prov G lvo /\
       op_taint tt (Var idx) = op_taint tn (Var idx) /\
       op_taint tt (Var p) = op_taint tn (Var p) /\
       op_taint tt lvo = op_taint tn lvo) G1 tn1 t /\ ef.gas_obs = [] /\
    valid_horizon cx st0 H ef.storage_trace /\
    (?xs. !tail.
       eval_stmts cx body
         (ei with
          <|gas_obs := xs ++ tail;
            scopes :=
              fmupdate id
                <|assignable := F; type := tyv; value := v; popped := []|>
                FEMPTY::ei.scopes|>) = (raw,ef with gas_obs := tail)) ==>
    ?sc rest b.
      ef.scopes = sc::rest /\
      (case raw of
         INL v => INL F
       | INR ex => FST (handle_loop_exception ex ef)) = INL b /\
      gas_origin_ptr_path
        (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (t,G1,tn1) []
        (OK (if raw = INL () then jump_to incr t else t),G1,tn1) /\
      (ef with scopes := rest).gas_obs = [] /\
      ~(if raw = INL () then jump_to incr t else t).vs_halted /\
      (b ==>
       (\H ee GG tt u.
          ?c. stmt_lands lctx sb (INL ()) u /\ ~u.vs_halted /\
              ~block_is_terminated sb /\ c = c0 /\
              cenv_top_ext c0 c ee.scopes /\
              stmt_state_rel H ctx func c cx ee u /\
              storage_well_formed_on cx ee (FST H) /\
              return_buf_frame d c sb u /\ return_buf_sep d c ee u /\
              ghost_inv_at (DF H) lo d c cx ee GG tt u /\
              (\c ee u GG tt.
                 alloca_history func u /\
                 (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
                 s0.vs_alloca_next <= u.vs_alloca_next /\
                 (!x w.
                    not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
                    lookup_var x u = SOME w) /\
                 (!aid b.
                    FLOOKUP s0.vs_allocas aid = SOME b ==>
                    FLOOKUP u.vs_allocas aid = SOME b) /\
                 (!x. not_fresh_at sa0 x ==>
                      FLOOKUP GG x = FLOOKUP G0 x /\
                      op_taint tt (Var x) = op_taint tn0 (Var x)) /\
                 alloca_frame c0 e0 sa0 s0 c ee u /\
                 !aid off sz i.
                   FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
                   aid < sa0.cs_next_id /\
                   (!name b sz'.
                      local_region c0 e0.scopes s0 name b sz' ==>
                      off + sz <= b \/ b + sz' <= off) /\ off <= i /\
                   i < off + sz /\ i IN tt.t_mem ==>
                   i IN tn0.t_mem) c ee u GG tt) H (ef with scopes := rest) G1
         tn1 (if raw = INL () then jump_to incr t else t)) /\
      (~b ==>
       (\H rr ee GG tt u.
          ?k off.
            k < len /\ len = LENGTH vs /\ len <= bound_length bd /\
            vs =
            GENLIST
              (\j.
                 PlaceR
                   (StoragePlace tr
                      ((case bd of Fixed v => slot | Dynamic v1 => slot + 1w) +
                       n2w (j * type_slot_size tyv)) tyv)) len /\
            rr = DROP k vs /\ slot = n2w off /\
            MEM (StorageRoot tr off (ArrayTV tyv bd)) ee.storage_trace /\
            evaluate_type (get_tenv cx) typ = SOME tyv /\
            well_formed_type_value tyv /\ u.vs_current_bb = si.cs_current_bb /\
            u.vs_inst_idx = LENGTH si.cs_current_insts /\ ~u.vs_halted /\
            lookup_var idx u = SOME (n2w k) /\ FLOOKUP GG idx = NONE /\
            op_taint tt (Var idx) = {} /\
            eval_operand lvo u = SOME (n2w len) /\ op_taint tt lvo = {} /\
            op_prov GG lvo = NONE /\ eval_operand (Lit slot) u = SOME slot /\
            op_taint tt (Lit slot) = {} /\ lookup_var p u = SOME dst /\
            FLOOKUP u.vs_allocas sd.cs_next_id = SOME (w2n dst,nb) /\
            ptr_covers GG tt p u nb /\ 32 * type_slot_size tyv <= nb /\
            w2n dst + nb < 2 ** 256 /\ w2n dst + nb <= u.vs_alloca_next /\
            (!name b sz.
               local_region c0 ee.scopes u name b sz ==>
               w2n dst + nb <= b \/ b + sz <= w2n dst) /\
            lookup_scopes id ee.scopes = NONE /\ expr_sim_inv c0 cx env ee /\
            ce_locals_declared c0 env /\ locals_alloc_ok c0 env /\
            cenv_top_ext c0 c0 ee.scopes /\
            stmt_state_rel H ctx func c0 cx ee u /\
            storage_well_formed_on cx ee (FST H) /\
            ghost_inv_at (DF H) lo d c0 cx ee GG tt u /\
            return_buf_frame d c0 sa0 u /\ ret_pc_ok c0 sa0 u /\
            return_buf_sep d c0 ee u /\ body_stmts_full_ok cx body /\
            (\c ee u GG tt.
               alloca_history func u /\
               (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
               s0.vs_alloca_next <= u.vs_alloca_next /\
               (!x w.
                  not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
                  lookup_var x u = SOME w) /\
               (!aid b.
                  FLOOKUP s0.vs_allocas aid = SOME b ==>
                  FLOOKUP u.vs_allocas aid = SOME b) /\
               (!x. not_fresh_at sa0 x ==>
                    FLOOKUP GG x = FLOOKUP G0 x /\
                    op_taint tt (Var x) = op_taint tn0 (Var x)) /\
               alloca_frame c0 e0 sa0 s0 c ee u /\
               !aid off sz i.
                 FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
                 aid < sa0.cs_next_id /\
                 (!name b sz'.
                    local_region c0 e0.scopes s0 name b sz' ==>
                    off + sz <= b \/ b + sz' <= off) /\ off <= i /\
                 i < off + sz /\ i IN tt.t_mem ==>
                 i IN tn0.t_mem) c0 ee u GG tt) H (a::rs)
         (ef with scopes := rest) G1 tn1
         (if raw = INL () then jump_to incr t else t))
Proof
  rpt gen_tac >>
  qpat_abbrev_tac `eb = ei with scopes := (FEMPTY |+ (id, _)) :: ei.scopes` >>
  qpat_abbrev_tac `explicit = gas_explicit_sites ctx shadow_ctx` >>
  abbrev_lambda_tac "Fr" 5 0 `alloca_history func s /\ _` >>
  abbrev_lambda_tac "Ready" 6 2 `k < len /\ _` >>
  abbrev_lambda_tac "Done" 5 1 `stmt_lands lctx sb (INL ()) t /\ _` >>
  abbrev_lambda_tac "Qb" 6 1 `stmt_lands (InLoop exit incr) sb1 res t /\ _` >>
  abbrev_lambda_tac "Keep" 3 0 `lookup_var idx t = lookup_var idx s /\ _` >>
  strip_tac >> rename1 `value_has_type tyv v` >>
  rename1 `eval_stmts cx stmts _ = _` >>
  `ef with gas_obs := [] = ef` by
    (simp[NoAsms, evaluation_state_component_equality] >>
     first_assum ACCEPT_TAC) >>
  `eval_stmts cx stmts (eb with gas_obs := xs) = (raw,ef)` by
    (qpat_assum `ef with gas_obs := [] = ef` (fn upd =>
       qpat_assum `!tail. eval_stmts _ _ _ = _`
         (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [APPEND_NIL, upd])))) >>
  `eval_stmts cx stmts
     ((ei with gas_obs := xs) with scopes :=
       (FEMPTY |+ (id, <|assignable := F; type := tyv;
         value := v; popped := []|>))::(ei with gas_obs := xs).scopes) =
     (raw,ef)` by
    (qpat_x_assum `eval_stmts _ _ (eb with gas_obs := xs) = _` mp_tac >>
     simp[NoAsms, Abbr `eb`, evaluation_state_fupdfupds,
       evaluation_state_fn_updates]) >>
  `lookup_scopes id (ei with gas_obs := xs).scopes = NONE` by
    (pure_rewrite_tac [evaluation_state_accfupds] >>
     first_assum ACCEPT_TAC) >>
  drule_all array_body_scope_shape >> strip_tac >>
  qunabbrev_tac `Qb` >> qunabbrev_tac `Keep` >>
  RULE_ASSUM_TAC BETA_RULE >>
  qpat_x_assum `?c3. stmt_lands _ _ _ _ /\ _` strip_assume_tac >>
  `stmt_state_rel H ctx func c0 cx (ef with scopes := rest) t` by
    (irule array_body_scope_projection >>
     conj_tac >- (qexists_tac `sc` >> asm_rewrite_tac[]) >>
     qexistsl_tac [`bc`, `c3`, `eb with gas_obs := xs`, `raw`, `stmts`] >>
     asm_rewrite_tac[evaluation_state_accfupds]) >>
  `cenv_top_ext c0 c3 ef.scopes` by
    (qpat_assum `eval_stmts _ _ (eb with gas_obs := xs) = _`
       (mp_tac o MATCH_MP eval_stmts_preserves_scopes_dom) >>
     simp_tac (srw_ss()) [preserves_scopes_dom_def] >> strip_tac >>
     irule cenv_top_ext_trans >>
     qexistsl_tac [`bc`, `eb.scopes`] >> asm_rewrite_tac[]) >>
  `return_buf_sep d c0 (ef with scopes := rest) t` by
    (irule return_buf_sep_pop >> qexistsl_tac [`c3`, `sc`] >>
     `((ef with scopes := rest) with scopes := sc::rest) = ef` by
       simp[evaluation_state_component_equality] >>
     asm_rewrite_tac[evaluation_state_accfupds, combinTheory.K_THM] >>
     qpat_x_assum `cenv_top_ext c0 c3 ef.scopes` mp_tac >>
     qpat_assum `ef.scopes = sc::rest` (rewrite_tac o single)) >>
  `ghost_inv_at (DF H) lo d c0 cx (ef with scopes := rest) G1 tn1 t` by
    (irule ghost_inv_at_pop >>
     conj_tac >- (qexists_tac `sc` >> asm_rewrite_tac[]) >>
     qexists_tac `c3` >> asm_rewrite_tac[]) >>
  `Fr c3 ef t G1 tn1` by
    (qpat_assum `Abbrev (Fr = _)` (fn ab =>
       pure_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] ab]) >>
     BETA_TAC >> irule for_full_frame_compose >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     goal_assum (drule_at Any) >>
     qexists_tac `G` >>
     qpat_assum `Abbrev (Fr = _)` (fn ab =>
       qpat_assum `Fr bc eb s G tn`
         (strip_assume_tac o BETA_RULE o
           PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] ab])) >>
     asm_rewrite_tac[]) >>
  `Fr c0 (ef with scopes := rest) t G1 tn1` by
    (qpat_assum `Abbrev (Fr = _)` (fn ab =>
       (pure_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] ab] >>
        qpat_assum `Fr c3 ef t G1 tn1`
          (strip_assume_tac o BETA_RULE o
            PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] ab]))) >>
     BETA_TAC >> irule for_full_frame_pop >>
     goal_assum (drule_at Any) >> asm_rewrite_tac[] >>
     conj_tac >- (qexists_tac `sc` >> asm_rewrite_tac[]) >>
     qexists_tac `c3` >> asm_rewrite_tac[] >>
     metis_tac[for_full_frame_pop]) >>
  `MAP FDOM ei.scopes = MAP FDOM rest` by
    (qpat_assum `eval_stmts _ _ (eb with gas_obs := xs) = _`
       (mp_tac o MATCH_MP eval_stmts_preserves_scopes_dom) >>
     simp[NoAsms, preserves_scopes_dom_def, Abbr `eb`,
       evaluation_state_accfupds] >> asm_rewrite_tac[] >> simp[]) >>
  `lookup_scopes id rest = NONE` by
    (irule lookup_scopes_none_map_fdom >>
     qexists_tac `ei.scopes` >> asm_rewrite_tac[]) >>
  `stmt_state_rel H ctx func c0 cx ei s` by
    (`ei = eb with scopes := ei.scopes` by
       simp[NoAsms, Abbr `eb`, evaluation_state_fupdfupds] >>
     pop_assum SUBST1_TAC >> irule stmt_state_rel_pop_top_ext >>
     reverse conj_tac >- (qexists_tac `bc` >> asm_rewrite_tac[]) >>
     simp[NoAsms, Abbr `eb`, evaluation_state_accfupds] >>
     asm_rewrite_tac[FDOM_FUPDATE, FDOM_FEMPTY, IN_INSERT, NOT_IN_EMPTY]) >>
  `!name b sz. local_region c0 rest t name b sz ==>
     w2n dst+nb <= b \/ b+sz <= w2n dst` by
    (rpt strip_tac >>
     `local_region c0 ei.scopes s name b sz` by
       (irule (INST_TYPE [alpha |-> ``:256``] local_region_kept) >>
        reverse conj_tac >-
          (qexistsl_tac [`H`, `ctx`, `cx`, `func`] >> first_assum ACCEPT_TAC) >>
        qexistsl_tac [`ef with scopes := rest`, `t`, `sb0`] >>
        asm_rewrite_tac[evaluation_state_accfupds] >> simp[]) >>
     metis_tac[]) >>
  `ptr_covers G1 tn1 p t nb` by
    (irule decoderGhostFramePtrTheory.ptr_covers_frame >>
     qexistsl_tac [`G`, `s`, `tn`] >> asm_rewrite_tac[] >>
     metis_tac[]) >>
  `(raw = INL () \/ raw = INR ContinueException) ==>
     expr_sim_inv c0 cx env (ef with scopes := rest)` by
    (strip_tac >> irule expr_sim_inv_for_pop >>
     conj_tac >- (qexists_tac `sc` >> first_assum ACCEPT_TAC) >>
     goal_assum (drule_at Any) >>
     asm_rewrite_tac[exprSimHypsDefsTheory.expr_sim_inv_gas_obs] >>
     metis_tac[]) >>
  `return_buf_frame d c0 sa0 t /\ ret_pc_ok c0 sa0 t` by
    (conj_tac >- (irule return_buf_frame_frame >>
       qexistsl_tac [`c0`, `s`, `sa0`] >>
       simp[] >> rpt strip_tac >>
       qpat_assum `!x w. not_fresh_at sb0 x /\ _ ==> _` irule >>
       asm_rewrite_tac[] >> first_x_assum irule >> first_assum ACCEPT_TAC) >>
     irule ret_pc_ok_frame >> qexistsl_tac [`c0`, `s`, `sa0`] >>
     simp[] >> rpt strip_tac >>
     qpat_assum `!x w. not_fresh_at sb0 x /\ _ ==> _` irule >>
     asm_rewrite_tac[] >> first_x_assum irule >> first_assum ACCEPT_TAC) >>
  `MEM (StorageRoot tr off (ArrayTV tyv bd)) ef.storage_trace` by
    (mp_tac (Q.SPECL [`cx`, `stmts`] (cj 2 evaluate_storage_trace_frame)) >>
     rewrite_tac[storage_trace_frame_def] >>
     disch_then (qspecl_then [`eb with gas_obs := xs`,
       `(eb with gas_obs := xs).storage_trace`] mp_tac) >>
     simp[NoAsms] >>
     Cases_on `eval_stmts cx stmts
       ((eb with gas_obs := xs) with storage_trace := [])` >>
     simp[NoAsms] >> strip_tac >>
     pop_assum mp_tac >>
     RULE_ASSUM_TAC (REWRITE_RULE [evaluation_state_fupdcanon]) >>
     asm_rewrite_tac[evaluation_state_fupdcanon] >>
     simp[Abbr `eb`, evaluation_state_accfupds, MEM_APPEND] >>
     metis_tac[]) >>
  `storage_well_formed_on cx (ef with scopes := rest) (FST H)` by
    (`storage_well_formed_on cx (ef with scopes := rest) (FST H) <=>
       storage_well_formed_on cx ef (FST H)` by
       (irule storage_well_formed_on_backends >> simp[]) >>
     asm_rewrite_tac[]) >>
  `cenv_top_ext c0 c0 rest` by simp[cenv_top_ext_refl] >>
  Cases_on `raw = INL ()`
  >- suspend "normal" >>
  Cases_on `raw = INR BreakException`
  >- suspend "break" >>
  suspend "continue"
QED

Resume for_storage_body_post_land_full[break]:
  qpat_x_assum `raw = INR BreakException` SUBST_ALL_TAC >>
  simp[NoAsms, vyperInterpreterTheory.handle_loop_exception_def, return_def] >>
  qexistsl_tac [`sc`, `rest`] >>
  asm_rewrite_tac[] >>
  simp[gas_origin_ptr_path_rules] >>
  simp[Abbr `Done`] >>
  conj_tac >-
    (qpat_x_assum `stmt_lands (InLoop _ _) _ _ _` mp_tac >>
     simp[stmt_lands_def]) >>
  qpat_assum `return_buf_frame d c0 sa0 t` mp_tac >>
  Cases_on `d` >- simp[NoAsms, return_buf_frame_def] >>
  rename1 `return_buf_frame (SOME pair) c0 sb t` >> Cases_on `pair` >>
  simp[NoAsms, return_buf_frame_def] >>
  strip_tac >> qexistsl_tac [`x`, `slot_size`] >> asm_rewrite_tac[] >>
  qpat_assum `!x sz. c0.ce_return_buf = _ ==> not_fresh_at sb x` irule >>
  qexists_tac `slot_size` >> first_assum ACCEPT_TAC
QED

Resume for_storage_body_post_land_full[continue]:
  `raw = INR ContinueException` by
    (qpat_assum `stmt_lands (InLoop _ _) _ _ _`
       (mp_tac o REWRITE_RULE [stmt_lands_def]) >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  pop_assum SUBST_ALL_TAC >>
  simp[NoAsms, vyperInterpreterTheory.handle_loop_exception_def, return_def] >>
  qexistsl_tac [`sc`, `rest`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (irule (cj 1 gas_origin_ptr_path_rules) >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qunabbrev_tac `Ready` >> BETA_TAC >> qexistsl_tac [`k`, `off`] >>
  ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_x_assum `vs = GENLIST _ _` kall_tac >>
  qpat_assum `lookup_var idx t = _ /\ _` strip_assume_tac >>
  simp[evaluation_state_accfupds, eval_operand_def, op_taint_def] >>
  conj_tac >-
    (qpat_assum `stmt_lands (InLoop _ _) _ _ _` mp_tac >>
     simp[NoAsms, stmt_lands_def]) >>
  conj_tac >-
    (qpat_assum `stmt_lands (InLoop _ _) _ _ _` mp_tac >>
     simp[NoAsms, stmt_lands_def]) >>
  qpat_assum `!name b sz. local_region c0 rest t name b sz ==> _` mp_tac >>
  simp[NoAsms, ADD_COMM]
QED

Resume for_storage_body_post_land_full[normal]:
  qpat_x_assum `raw = INL ()` SUBST_ALL_TAC >>
  `~block_is_terminated sb1` by metis_tac[] >>
  `emit_inst JMP [Label incr] [] sb1 = ((),sj)` by
    (qpat_assum `emit_jmp_if_not_terminated incr sb1 = _` mp_tac >>
     simp[NoAsms, emit_jmp_if_not_terminated_def, comp_get_def, comp_bind_def] >>
     asm_rewrite_tac[]) >>
  `t.vs_current_bb = sb1.cs_current_bb /\
   t.vs_inst_idx = LENGTH sb1.cs_current_insts` by
    (qpat_assum `stmt_lands (InLoop _ _) _ _ _` mp_tac >>
     simp[NoAsms, stmt_lands_def]) >>
  `?bb. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb t.vs_inst_idx =
      SOME (mk_inst sb1.cs_next_id JMP [Label incr] [])` by
    (asm_rewrite_tac[] >> irule place_copy_emit_instruction >>
     qexists_tac `sj` >> asm_rewrite_tac[]) >>
  `allocas_from lo t` by
    (qpat_assum `ghost_inv_at _ _ _ c0 _ _ _ _ t` mp_tac >>
     simp[NoAsms, ghost_inv_at_def]) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G1,tn1) []
    (OK (jump_to incr t),G1,tn1)` by
    (irule fragGasOriginPtrLoopTheory.jump_origin_ptr_path >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`bb`, `mk_inst sb1.cs_next_id JMP [Label incr] []`] >>
     asm_rewrite_tac[] >>
     simp[NoAsms, mk_inst_def, is_terminator_def,
       unitTransformDefsTheory.inst_mem_below_frontier_def, inst_dload_in_section_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def,
       venomExecPropsTheory.step_jmp_behavior] >>
     simp[ptrSafeRunTheory.ptr_safe_step_def, ptrSafeRunTheory.ptr_inst_ok_def, access_ok_def, taint_ok_def,
       mk_inst_def, step_inst_non_invoke, venomExecPropsTheory.step_jmp_behavior, jump_to_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def, op_taint_def]) >>
  `return_buf_sep d c0 (ef with scopes := rest) (jump_to incr t)` by
    simp[return_buf_sep_jump] >>
  `Fr c0 (ef with scopes := rest) (jump_to incr t) G1 tn1` by
    (qpat_assum `Fr c0 (ef with scopes := rest) t G1 tn1` mp_tac >>
     simp[NoAsms, Abbr `Fr`] >> strip_tac >>
     conj_tac >- (irule alloca_history_jump >> simp[jump_to_def] >>
       qexists_tac `t` >> simp[]) >>
     `allocas_below_fmp (jump_to incr t) = allocas_below_fmp t` by
       simp[allocas_below_fmp_def, jump_to_def] >>
     asm_rewrite_tac[] >>
     simp[jump_to_def, lookup_var_def] >>
     irule alloca_frame_same_state >> qexists_tac `t` >>
     simp[jump_to_def]) >>
  simp[NoAsms] >> qexistsl_tac [`sc`, `rest`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[] >>
  conj_tac >- simp[jump_to_def] >>
  qunabbrev_tac `Ready` >> BETA_TAC >> qexistsl_tac [`k`, `off`] >>
  ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_x_assum `vs = GENLIST _ _` kall_tac >>
  qpat_assum `lookup_var idx t = _ /\ _` strip_assume_tac >>
  simp[evaluation_state_accfupds, stmt_state_rel_jump_to,
    ghost_inv_at_jump, return_buf_frame_jump_to, ret_pc_ok_jump_to,
    jump_to_def, lookup_var_def, eval_operand_def, op_taint_def] >>
  conj_tac >-
    (irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >>
     qexistsl_tac [`G1`, `t`, `tn1`] >>
     simp[NoAsms, lookup_var_def] >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >>
  `local_region c0 rest
    (t with <|vs_prev_bb := SOME sb1.cs_current_bb;
              vs_current_bb := incr; vs_inst_idx := 0|>) name b sz =
   local_region c0 rest t name b sz` by
    (irule local_region_lookup_cong >> simp[lookup_var_def]) >>
  asm_rewrite_tac[] >>
  qpat_assum `!name b sz. local_region c0 rest t name b sz ==> _` mp_tac >>
  simp[NoAsms, ADD_COMM] >> metis_tac[]
QED

Finalise for_storage_body_post_land_full

(* Live outer locals have bounded, well-formed value footprints. *)
Theorem for_storage_outer_local_footprint:
  stmt_state_rel H ctx func cenv cx es s /\
  lookup_scopes name es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME w /\
  (w2n w + sz <= a \/ a + bytes <= w2n w) ==>
  val_wf entry.type entry.value /\
  (!i. w2n w <= i /\
       i < w2n w + val_footprint entry.type entry.value ==>
       ~(a <= i /\ i < a + bytes))
Proof
  strip_tac >> drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  qpat_x_assum `local_ptrs_rel _ _ _ _` mp_tac >>
  simp[local_ptrs_rel_def] >> strip_tac >>
  first_x_assum (qspecl_then [`name`, `entry`, `p`, `sz`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  drule exprSimPropsTheory.val_footprint_le >> strip_tac >>
  simp[] >> rpt strip_tac >> decide_tac
QED

(* A fresh destination write keeps the original, possibly different-cenv anchor. *)
Theorem for_storage_copy_alloca_frame:
  alloca_frame cinit e0 sa0 s0 c ei u /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP u.vs_allocas aid = SOME b) /\
  allocas_non_overlapping u /\
  FLOOKUP u.vs_allocas aid0 = SOME (w2n dst,nb) /\
  sa0.cs_next_id <= aid0 /\
  lookup_scopes id ei.scopes = NONE /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) nb) /\
  lookup_var p z = SOME dst /\
  (!name entry. lookup_scopes name ei.scopes = SOME entry ==>
    FLOOKUP bc.ce_vars name = FLOOKUP c.ce_vars name) /\
  local_ptrs_reserved c sa /\
  (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x u) /\
  (!a len. a+len <= w2n dst \/ w2n dst+nb <= a ==>
    mem_bytes_at a len z.vs_memory = mem_bytes_at a len u.vs_memory) ==>
  alloca_frame cinit e0 sa0 s0 bc
    (ei with scopes := (FEMPTY |+ (id,entry0))::ei.scopes) z
Proof
  strip_tac >> simp[alloca_frame_def] >> rpt gen_tac >> strip_tac >>
  `FLOOKUP u.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
  `aid <> aid0` by decide_tac >>
  qpat_x_assum `allocas_non_overlapping _` mp_tac >>
  simp[venomMemDefsTheory.allocas_non_overlapping_def] >>
  disch_then (qspecl_then [`aid`, `aid0`, `off`, `sz`, `w2n dst`, `nb`] mp_tac) >>
  simp[] >> disch_tac >>
  `mem_bytes_at off sz u.vs_memory = mem_bytes_at off sz s0.vs_memory /\
   (!name b sz'. local_region c ei.scopes u name b sz' ==>
     off + sz <= b \/ b + sz' <= off)` by
    (qpat_x_assum `alloca_frame _ _ _ _ _ _ _` mp_tac >>
     simp[alloca_frame_def] >> metis_tac[]) >>
  conj_tac >-
    (qpat_x_assum `!a len. _` (qspecl_then [`off`, `sz`] mp_tac) >>
     simp[ADD_COMM]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `local_region _ _ _ _ _ _` mp_tac >>
  simp[local_region_def, vyperStateTheory.lookup_scopes_def, FLOOKUP_UPDATE] >>
  strip_tac >> Cases_on `n = id` >> gvs[] >>
  rename1 `lookup_var q z = SOME w` >>
  `lookup_var q u = SOME w` by
    (gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
  qpat_x_assum `!name b sz'. local_region c _ _ _ _ _ ==> _`
    (qspecl_then [`n`, `w2n w`, `sz'`] mp_tac) >>
  simp[local_region_def] >> metis_tac[]
QED

(* Interpret the existing copy endpoint; no execution witness is selected here. *)
Theorem for_storage_copy_body_entry:
  !H D lo d ctx func cx c0 e0 sa0 s0 G0 tn0 ei env id typ tyv v sd st bc sa sb0
      inst p nb dst n src load u Gu tnu z Gf tnf idx k lvo len.
    expr_sim_inv c0 cx env ei /\ ce_locals_declared c0 env /\
    locals_alloc_ok c0 env /\ id NOTIN FDOM env.var_types /\
    evaluate_type (get_tenv cx) typ = SOME tyv /\ value_has_type tyv v /\
    val_wf tyv v /\ declare_local c0 id typ sd = (bc,st) /\
    c0.ce_alloca_locals /\ type_memory_bytes c0 typ < 2 ** 64 /\
    (!l. FLOOKUP c0.ce_vars id = SOME l ==> ?q sz. l = PtrVar q sz) /\
    FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) nb) /\
    lookup_scopes id ei.scopes = NONE /\
    return_buf_sep d c0 ei u /\ stmt_state_rel H ctx func c0 cx ei u /\
    storage_well_formed_on cx ei (FST H) /\
    ghost_inv_at D lo d c0 cx ei Gu tnu u /\
    (\c ee s G tn.
       alloca_history func s /\
       (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
       s0.vs_alloca_next <= s.vs_alloca_next /\
       (!x w.
          not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
          lookup_var x s = SOME w) /\
       (!aid b.
          FLOOKUP s0.vs_allocas aid = SOME b ==>
          FLOOKUP s.vs_allocas aid = SOME b) /\
       (!x. not_fresh_at sa0 x ==>
            FLOOKUP G x = FLOOKUP G0 x /\
            op_taint tn (Var x) = op_taint tn0 (Var x)) /\
       alloca_frame c0 e0 sa0 s0 c ee s /\
       !aid off sz i.
         FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
         (!name b sz'.
            local_region c0 e0.scopes s0 name b sz' ==>
            off + sz <= b \/ b + sz' <= off) /\ off <= i /\ i < off + sz /\
         i IN tn.t_mem ==>
         i IN tn0.t_mem) c0 ei u Gu tnu /\ return_buf_frame d c0 sa0 u /\
    ret_pc_ok c0 sa0 u /\ sa0.cs_next_var <= sb0.cs_next_var /\
    (!x. not_fresh_at sa0 x ==> not_fresh_at sa x) /\
    local_ptrs_reserved c0 sa /\ local_ptrs_reserved bc sa /\
    (!x cap. c0.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
    (!x cap. c0.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
    not_fresh_at sa p /\ not_local_ptr bc (FEMPTY::ei.scopes) p /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [p] /\ fn_inst_ids_distinct func /\
    sa0.cs_next_id <= inst.inst_id /\
    FLOOKUP u.vs_allocas inst.inst_id = SOME (w2n dst,nb) /\
    allocas_non_overlapping u /\ lookup_var p u = SOME dst /\
    ptr_covers Gu tnu p u nb /\ slot_copy_external sa (Var p) /\
    n = type_slot_size tyv /\ 32 * n <= nb /\ lo <= w2n dst /\
    (!name b sz.
       local_region c0 ei.scopes u name b sz ==>
       w2n dst + nb <= b \/ b + sz <= w2n dst) /\
    slot_copy_runtime_frame sa dst n u z /\
    slot_copy_ghost_inv sa load src dst p n Gu tnu n Gf tnf z /\
    (!mem.
       mem_agree_outside tnf.t_mem z.vs_memory mem ==>
       val_in_memory tyv v (w2n dst) mem) /\
    z.vs_immutables = u.vs_immutables /\ alloca_history func z /\
    allocas_from lo z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    ~z.vs_halted /\ z.vs_current_bb = sb0.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb0.cs_current_insts /\
    lookup_var idx z = SOME (n2w k) /\ FLOOKUP Gf idx = NONE /\
    op_taint tnf (Var idx) = {} /\ eval_operand lvo z = SOME (n2w len) /\
    op_prov Gf lvo = NONE /\ op_taint tnf lvo = {} ==>
    push_scope_with_var id tyv v ei =
    (INL (),
     ei with
     scopes :=
       fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
         FEMPTY::ei.scopes) /\
    expr_sim_inv bc cx (extend_local env id typ F)
      (ei with
       scopes :=
         fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
           FEMPTY::ei.scopes) /\
    ce_locals_declared bc (extend_local env id typ F) /\
    locals_alloc_ok bc (extend_local env id typ F) /\
    cenv_top_ext c0 bc
      (ei with
       scopes :=
         fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
           FEMPTY::ei.scopes).scopes /\
    stmt_state_rel H ctx func bc cx
      (ei with
       scopes :=
         fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
           FEMPTY::ei.scopes) z /\
    storage_well_formed_on cx
      (ei with
       scopes :=
         fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
           FEMPTY::ei.scopes) (FST H) /\
    ghost_inv_at D lo d bc cx
      (ei with
       scopes :=
         fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
           FEMPTY::ei.scopes) Gf tnf z /\ ret_pc_ok bc sb0 z /\
    return_buf_frame d bc sb0 z /\
    return_buf_sep d bc
      (ei with scopes :=
        fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
          FEMPTY::ei.scopes) z /\
    (\c ee s G tn.
       alloca_history func s /\
       (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
       s0.vs_alloca_next <= s.vs_alloca_next /\
       (!x w.
          not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
          lookup_var x s = SOME w) /\
       (!aid b.
          FLOOKUP s0.vs_allocas aid = SOME b ==>
          FLOOKUP s.vs_allocas aid = SOME b) /\
       (!x. not_fresh_at sa0 x ==>
            FLOOKUP G x = FLOOKUP G0 x /\
            op_taint tn (Var x) = op_taint tn0 (Var x)) /\
       alloca_frame c0 e0 sa0 s0 c ee s /\
       !aid off sz i.
         FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
         (!name b sz'.
            local_region c0 e0.scopes s0 name b sz' ==>
            off + sz <= b \/ b + sz' <= off) /\ off <= i /\ i < off + sz /\
         i IN tn.t_mem ==>
         i IN tn0.t_mem) bc
      (ei with
       scopes :=
         fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
           FEMPTY::ei.scopes) z Gf tnf /\ ~z.vs_halted /\
    z.vs_current_bb = sb0.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb0.cs_current_insts /\
    lookup_var idx z = SOME (n2w k) /\ FLOOKUP Gf idx = NONE /\
    op_taint tnf (Var idx) = {} /\ lookup_var p z = SOME dst /\
    eval_operand lvo z = SOME (n2w len) /\ op_prov Gf lvo = NONE /\
    op_taint tnf lvo = {} /\ allocas_from lo z /\
    FLOOKUP z.vs_allocas inst.inst_id = SOME (w2n dst,nb) /\
    ptr_covers Gf tnf p z nb /\
    !aid b.
      FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP z.vs_allocas aid = SOME b
Proof
 rpt gen_tac >>
  abbrev_lambda_tac "Fr" 5 0 `alloca_history func s /\ _` >>
  qpat_abbrev_tac `eb = ei with scopes := (FEMPTY |+ (id, _)) :: ei.scopes` >>
 strip_tac >>
 `expr_sim_inv bc cx (extend_local env id typ F) eb` by
   (simp[Abbr `eb`] >> irule expr_sim_inv_for_scope >> metis_tac[]) >>
 `ce_locals_declared bc (extend_local env id typ F)` by
   (irule ce_locals_declared_declare_local >> metis_tac[]) >>
 `locals_alloc_ok bc (extend_local env id typ F)` by
   (drule_all declare_local_memory_types_mem >> strip_tac >>
    simp[locals_alloc_ok_def, vyperTypeSystemTheory.extend_local_def, FLOOKUP_UPDATE] >>
    map_every qx_gen_tac [`nm`,`tv`] >> Cases_on `id = nm` >>
    strip_tac >> gvs[locals_alloc_ok_def] >>
    qpat_x_assum `!nm tv. FLOOKUP env.var_types nm = SOME tv ==> _` irule >>
    qexists `nm` >> simp[]) >>
 `cenv_top_ext c0 bc (FEMPTY::ei.scopes) /\ cenv_top_ext c0 bc eb.scopes` by
   (simp[Abbr `eb`] >> conj_tac >> irule cenv_top_ext_declare_local >> metis_tac[]) >>
 drule_all slot_copy_semantic_frame >> strip_tac >>
 `type_memory_size tyv = 32*n` by simp[type_memory_size_slots] >>
 `lookup_var p z = SOME dst` by metis_tac[] >>
 `stmt_state_rel H ctx func bc cx eb z` by
   (qabbrev_tac `empty = ei with scopes := FEMPTY::ei.scopes` >>
    `stmt_state_rel H ctx func bc cx empty u` by
      (simp[Abbr `empty`] >> irule array_empty_scope_rel_transport >> metis_tac[]) >>
    `eb = empty with scopes :=
      (FEMPTY |+ (id,<|assignable:=F; type:=tyv; value:=v; popped:=[]|>))::ei.scopes` by
      simp[Abbr `eb`, Abbr `empty`] >>
    pop_assum SUBST1_TAC >> irule stmt_state_rel_declare_copy_frame >>
    simp[Abbr `empty`,lookup_scopes_def] >>
    qexistsl [`inst`,`u`,`sa`,`dst`] >>
    simp[] >> conj_tac
    >- (qpat_x_assum `slot_copy_runtime_frame _ _ _ _ _` mp_tac >>
        simp[slot_copy_runtime_frame_def] >> metis_tac[ADD_COMM]) >>
    qpat_x_assum `!mem. mem_agree_outside _ _ mem ==> _` irule >>
    simp[mem_agree_outside_def]) >>
 `(!x. not_fresh_at sa x ==>
     lookup_var x z = lookup_var x u /\ FLOOKUP Gf x = FLOOKUP Gu x /\
     op_taint tnf (Var x) = op_taint tnu (Var x))` by
   (rpt strip_tac >> drule slot_copy_not_fresh_external >> strip_tac >>
    gvs[slot_copy_ghost_inv_def]) >>
 `z.vs_allocas = u.vs_allocas /\ z.vs_alloca_next = u.vs_alloca_next /\
  z.vs_accounts = u.vs_accounts /\ z.vs_transient = u.vs_transient /\
  z.vs_call_ctx = u.vs_call_ctx` by gvs[slot_copy_runtime_frame_def] >>
 `lo <= z.vs_alloca_next` by
   (qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >> simp[ghost_inv_at_def]) >>
 `ghost_inv_at D lo d c0 cx ei Gf tnf z` by
   (irule body_full_memory_ghost_frame >> simp[] >>
    qexistsl [`Gu`,`u`,`sa`,`tnu`,`{i | w2n dst <= i /\ i < w2n dst+32*n}`] >>
    simp[] >> conj_tac
    >- (rpt gen_tac >> strip_tac >>
        `local_region c0 ei.scopes u name (w2n w) sz` by
          (simp[local_region_def] >> metis_tac[]) >>
        Q.SUBGOAL_THEN
          `w2n w + sz <= w2n dst \/ w2n dst + 32*n <= w2n w` assume_tac
        >- (qpat_x_assum `!name b sz. local_region c0 _ _ _ _ _ ==> _` drule >>
            decide_tac) >>
        drule_all for_storage_outer_local_footprint >>
        metis_tac[ADD_COMM]) >>
    gvs[slot_copy_ghost_inv_def, slot_copy_runtime_frame_def] >>
    rpt conj_tac >> rpt strip_tac >> metis_tac[ADD_COMM, DECIDE ``i < lo /\ lo <= a ==> ~(a <= i)``]) >>
 `ptr_covers Gf tnf p z nb` by
   (drule copy_external_ptr_covers >>
    disch_then (qspecl_then [`p`,`u`,`nb`] mp_tac) >>
    simp[eval_operand_def]) >>
 drule_all declare_local_ptr >> strip_tac >>
 `bc.ce_return_buf = c0.ce_return_buf /\
  bc.ce_return_pc = c0.ce_return_pc /\
  bc.ce_imm_alloca = c0.ce_imm_alloca` by
   (qpat_x_assum `bc with <|ce_vars := _; ce_var_type := _; ce_dynarray_capacity := _|> = c0`
      (fn th => once_rewrite_tac[GSYM th] >> simp[NoAsms])) >>
 `ghost_inv_at D lo d bc cx eb Gf tnf z` by
   (qpat_x_assum `ghost_inv_at D lo d c0 cx ei Gf tnf z` mp_tac >>
    simp[ghost_inv_at_def, Abbr `eb`, lookup_scopes_def, FLOOKUP_UPDATE] >>
    strip_tac >> conj_tac
    >- (rpt gen_tac >> Cases_on `name = id` >> simp[] >> strip_tac >> gvs[] >>
        metis_tac[]) >>
    Cases_on `d` >> gvs[return_buf_ptr_def] >>
    rename1 `return_buf_ptr (SOME pair) _ _ _ _` >>
    PairCases_on `pair` >> gvs[return_buf_ptr_def]) >>
 `ret_pc_ok bc sb0 z` by
   (irule ret_pc_ok_frame >> qexistsl [`c0`,`u`,`sa0`] >>
    simp[] >> metis_tac[]) >>
 `return_buf_frame d bc sb0 z` by
   (irule return_buf_frame_frame >> qexistsl [`c0`,`u`,`sa0`] >>
    simp[] >> metis_tac[]) >>
 `return_buf_sep d bc eb z` by
   ((qpat_x_assum `FLOOKUP bc.ce_vars id = SOME (PtrVar (Var (STRING _ _)) _)` kall_tac >>
    irule return_buf_sep_allocated_local >>
    qpat_assum `FLOOKUP bc.ce_vars id = SOME _` (irule_at Any) >>
    qexistsl_tac [`dst`, `sa`, `u`, `func`, `ei`, `cx`, `ctx`, `c0`,
                  `inst.inst_id`, `H`] >>
    simp[Abbr `eb`, lookup_scopes_def, FLOOKUP_UPDATE] >>
    rpt strip_tac >> gvs[return_buf_sep_def, allocas_from_def] >> (metis_tac[Abbr `eb`, lookup_scopes_def, FLOOKUP_UPDATE, return_buf_sep_def, allocas_from_def, return_buf_sep_allocated_local]))) >>
 `alloca_frame c0 e0 sa0 s0 bc eb z` by
   (simp[Abbr `eb`] >> irule for_storage_copy_alloca_frame >>
    conj_tac >- simp[] >>
    qexistsl [`inst.inst_id`,`c0`,`dst`,`nb`,`p`,`sa`,`u`] >>
    qpat_x_assum `Fr c0 ei u Gu tnu` mp_tac >>
    simp[Abbr `Fr`] >> strip_tac >>
    rpt conj_tac
    >- (rpt strip_tac >> Cases_on `name = id` >> gvs[]) >>
    rpt strip_tac >> gvs[]) >>
 `Fr bc eb z Gf tnf` by
   (qpat_x_assum `Fr c0 ei u Gu tnu` mp_tac >>
    simp[Abbr `Fr`] >> strip_tac >> simp[] >>
    rpt gen_tac >> strip_tac >>
    `FLOOKUP u.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
    `aid <> inst.inst_id` by decide_tac >>
    qpat_x_assum `allocas_non_overlapping u` mp_tac >>
    simp[venomMemDefsTheory.allocas_non_overlapping_def] >>
    disch_then (qspecl_then [`aid`,`inst.inst_id`,`off`,`sz`,`w2n dst`,`nb`] mp_tac) >>
    simp[] >> strip_tac >>
    `~(w2n dst <= i /\ i < w2n dst + 32*n)` by decide_tac >>
    `i IN tnu.t_mem` by
      (qpat_x_assum `slot_copy_ghost_inv _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
       pure_rewrite_tac[slot_copy_ghost_inv_def] >> strip_tac >>
       qpat_x_assum `!a. ~(_ /\ _) ==> _` (qspec_then `i` mp_tac) >> simp[]) >>
    qpat_x_assum `!aid off sz i. _` irule >>
    metis_tac[]) >>
 simp[] >> conj_tac
 >- simp[Abbr `eb`,push_scope_with_var_def,return_def,
         evaluation_state_component_equality,combinTheory.o_DEF] >>
 conj_tac
 >- (`storage_well_formed_on cx eb (FST H) <=>
      storage_well_formed_on cx ei (FST H)` suffices_by simp[] >>
     irule vyperStorageFootprintTheory.storage_well_formed_on_backends >>
     simp[Abbr `eb`]) >>
 qpat_x_assum `Fr c0 ei u Gu tnu` mp_tac >>
 simp[Abbr `Fr`]
QED

(* Pure scalar prefix steps have explicit finite ghost updates. *)
Theorem for_storage_scalar_step[local]:
  MEM opc [EQ;MUL;ADD] /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst iid opc [a;b] [out]) /\
  eval_operand a s = SOME x /\ eval_operand b s = SOME y /\
  op_taint tn a = {} /\ op_taint tn b = {} /\
  op_prov G a = NONE /\ op_prov G b = NONE /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\
  w = (if opc = EQ then bool_to_word (x=y)
       else if opc = MUL then x*y else x+y) ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx),
     DRESTRICT G (COMPL {out}), tn with t_var := tn.t_var |+ (out,{}))
Proof
  strip_tac >>
  `step_inst_base (mk_inst iid opc [a;b] [out]) s =
     OK (update_var out w s)` by
    (gvs[] >> metis_tac[emitHelperPropsTheory.step_EQ,
      emitHelperPropsTheory.step_MUL, emitHelperPropsTheory.step_ADD]) >>
  `ptr_inst_ok D lo 0 ctx func G tn (mk_inst iid opc [a;b] [out]) s` by
    suspend "checks" >>
  `step_prov PG G (mk_inst iid opc [a;b] [out]) (update_var out w s) =
     DRESTRICT G (COMPL {out}) /\
   step_taint (mk_inst iid opc [a;b] [out]) s (update_var out w s) tn =
     (tn with t_var := tn.t_var |+ (out,{}))` by suspend "ghosts" >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx),
     DRESTRICT G (COMPL {out}), tn with t_var := tn.t_var |+ (out,{}))` by
    (`(mk_inst iid opc [a;b] [out]).inst_opcode <> INVOKE /\
      ~is_terminator (mk_inst iid opc [a;b] [out]).inst_opcode /\
      inst_mem_below_frontier (mk_inst iid opc [a;b] [out]) s /\
      inst_dload_in_section (mk_inst iid opc [a;b] [out]) s` by
       (gvs[] >> simp[mk_inst_def, is_terminator_def,
         unitTransformDefsTheory.inst_mem_below_frontier_def,
         memSafeRunTheory.inst_dload_in_section_def,
         source_memory_write_ranges_def, source_memory_read_ranges_def]) >>
     drule_all straight_line_origin_ptr_edge >>
     disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
     gvs[] >> simp[mk_inst_def]) >>
  `~(update_var out w s with vs_inst_idx := SUC s.vs_inst_idx).vs_halted` by
    simp[update_var_def] >>
  metis_tac[gas_origin_ptr_path_rules, APPEND]
QED

Resume for_storage_scalar_step[checks]:
  Cases_on `opc = EQ`
  >- (gvs[] >>
      simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
           source_memory_write_ranges_def, source_memory_read_ranges_def] >>
      conj_tac
      >- (rpt strip_tac >> gvs[op_prov_def, FLOOKUP_DEF]) >>
      conj_tac >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
      simp[GSYM mk_inst_def, step_inst_non_invoke] >>
      simp[update_var_def]) >>
  irule ptr_inst_ok_copy_arith >> gvs[]
QED

Resume for_storage_scalar_step[ghosts]:
  `new_site_bytes s (update_var out w s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         EXTENSION, SF CONJ_ss] >>
  gvs[] >>
  simp[step_prov_def, out_prov_def, first_prov_def, set_prov_def,
       step_taint_def, set_var_taint_def, out_taint_def, mem_taint_def,
       written_taint_def, step_writes_def, store_taint_def, imm_taint_def,
       adopt_reset_def, range_bytes_def, source_memory_write_ranges_def,
       mk_inst_def, taint_component_equality]
QED

Finalise for_storage_scalar_step

(* Code geometry is explicit: this boundary neither assumes a body frame
   callback nor fixes the dead policy of a scalar storage address. *)
Theorem for_storage_array_head_prefix_at:
  lookup_block cond func.fn_blocks = SOME cb /\
  cb.bb_instructions =
  [mk_inst (h - 2) EQ [Var idx; lvo] [dv];
   mk_inst (h - 1) JNZ [Var dv; Label exit; Label bod] []] /\
  lookup_block bod func.fn_blocks = SOME bb /\ sa.cs_current_bb = bod /\
  sa.cs_current_insts =
  [mk_inst h MUL [Var idx; Lit (n2w n)] [ov]] ++
  (if case bd of Fixed v => F | Dynamic v1 => T then
     [mk_inst (h + 1) ADD [Lit 1w; Var ov] [tot]]
   else []) ++
  [mk_inst (h + if case bd of Fixed v => F | Dynamic v1 => T then 2 else 1) ADD
     [base_op;
      Var (if (case bd of Fixed v => F | Dynamic v1 => T) then tot else ov)]
     [ep]] /\
  (!j. j < LENGTH sa.cs_current_insts ==>
       get_instruction bb j = SOME (fEL sa.cs_current_insts j)) /\
  ALL_DISTINCT
    (if (case bd of Fixed v => F | Dynamic v1 => T) then [dv; ov; tot; ep]
     else [dv; ov; ep]) /\
  ~MEM idx
    (if (case bd of Fixed v => F | Dynamic v1 => T) then [dv; ov; tot; ep]
     else [dv; ov; ep]) /\
  ~MEM p
    (if (case bd of Fixed v => F | Dynamic v1 => T) then [dv; ov; tot; ep]
     else [dv; ov; ep]) /\
  (!x. lvo = Var x ==>
       ~MEM x
         (if (case bd of Fixed v => F | Dynamic v1 => T) then [dv; ov; tot; ep]
          else [dv; ov; ep])) /\ s.vs_current_bb = cond /\ s.vs_inst_idx = 0 /\
  ~s.vs_halted /\ lookup_var idx s = SOME (n2w k) /\ k < len /\
  len < 2 ** 256 /\ FLOOKUP G idx = NONE /\ op_taint tn (Var idx) = {} /\
  eval_operand lvo s = SOME (n2w len) /\ op_prov G lvo = NONE /\
  op_taint tn lvo = {} /\
  eval_operand base_op s = SOME slot /\ op_prov G base_op = NONE /\
  op_taint tn base_op = {} /\
  (!x. base_op = Var x ==>
     ~MEM x (if (case bd of Fixed _ => F | Dynamic _ => T)
             then [dv; ov; tot; ep] else [dv; ov; ep])) /\
  allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?u Gu tnu.
    (!D explicit.
       gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
         (OK u,Gu,tnu)) /\
    u =
    update_var ep
      ((if case bd of Fixed v => F | Dynamic v1 => T then slot + 1w else slot) +
       n2w (k * n))
      (if (case bd of Fixed v => F | Dynamic v1 => T) then
         update_var tot (1w + n2w (k * n))
           (update_var ov (n2w (k * n)) (jump_to bod (update_var dv 0w s)))
       else update_var ov (n2w (k * n)) (jump_to bod (update_var dv 0w s))) with
    vs_inst_idx := LENGTH sa.cs_current_insts /\
    Gu =
    DRESTRICT G
      (COMPL
         (set
            (if (case bd of Fixed v => F | Dynamic v1 => T) then
               [dv; ov; tot; ep]
             else [dv; ov; ep]))) /\
    tnu =
    tn with
    t_var :=
      FOLDL (\m x. fmupdate x {} m) tn.t_var
        (if (case bd of Fixed v => F | Dynamic v1 => T) then [dv; ov; tot; ep]
         else [dv; ov; ep]) /\ u.vs_current_bb = sa.cs_current_bb /\
    u.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~u.vs_halted /\
    eval_operand (Var ep) u =
    SOME
      ((if case bd of Fixed v => F | Dynamic v1 => T then slot + 1w else slot) +
       n2w (k * n)) /\ FLOOKUP Gu ep = NONE /\ op_taint tnu (Var ep) = {} /\
    (!x. ~MEM x
           (if (case bd of Fixed v => F | Dynamic v1 => T) then
              [dv; ov; tot; ep]
            else [dv; ov; ep]) ==>
         lookup_var x u = lookup_var x s /\ FLOOKUP Gu x = FLOOKUP G x /\
         op_taint tnu (Var x) = op_taint tn (Var x)) /\ allocas_from lo u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u)
Proof
  pure_rewrite_tac [LET_THM] >> BETA_TAC >> strip_tac >>
  `n2w k <> (n2w len : bytes32)` by
    (`k < 2**256` by decide_tac >>
     gvs[wordsTheory.n2w_11, wordsTheory.dimword_def] >>
     simp[LESS_MOD] >> decide_tac) >>
  qabbrev_tac `s1 = update_var dv 0w s with vs_inst_idx := 1` >>
  qabbrev_tac `G1 = DRESTRICT G (COMPL {dv})` >>
  qabbrev_tac `tn1 = tn with t_var := tn.t_var |+ (dv,{})` >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (s,G,tn) [] (OK s1,G1,tn1)` by suspend "eq" >>
  qabbrev_tac `q = jump_to bod s1` >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (s1,G1,tn1) [] (OK q,G1,tn1)` by suspend "branch" >>
  suspend "address"
QED

Resume for_storage_array_head_prefix_at[eq]:
  rpt gen_tac >>
  simp[Abbr `s1`, Abbr `G1`, Abbr `tn1`] >>
  `get_instruction cb s.vs_inst_idx =
     SOME (mk_inst (h-2) EQ [Var idx;lvo] [dv])` by
    simp[venomInstTheory.get_instruction_def] >>
  drule_at (Pos (el 3)) for_storage_scalar_step >>
  disch_then (qspecl_then [`n2w len`,`n2w k`,`0w`] mp_tac) >>
  simp[eval_operand_def, op_prov_def, venomExecSemanticsTheory.bool_to_word_def] >>
  disch_then irule >> simp[GSYM op_prov_def]
QED

Resume for_storage_array_head_prefix_at[branch]:
  rpt gen_tac >>
  `lookup_block s1.vs_current_bb func.fn_blocks = SOME cb /\
   get_instruction cb s1.vs_inst_idx =
     SOME (mk_inst (h-1) JNZ [Var dv;Label exit;Label bod] []) /\
   eval_operand (Var dv) s1 = SOME 0w /\ op_taint tn1 (Var dv) = {} /\
   ~s1.vs_halted /\ allocas_from lo s1 /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp s1)` by
    (simp[Abbr `s1`, Abbr `tn1`, venomInstTheory.get_instruction_def,
          update_var_def, eval_operand_def, lookup_var_def, op_taint_def,
          FLOOKUP_UPDATE, allocas_from_def, allocas_below_fmp_def] >>
     gvs[allocas_from_def, allocas_below_fmp_def]) >>
  drule_all decoderNavigationPtrTheory.jnz_origin_ptr_path >>
  disch_then (qspecl_then [`explicit`,`PG`,`G1`,`D`] mp_tac) >>
  simp[Abbr `q`]
QED

Resume for_storage_array_head_prefix_at[address]:
  qabbrev_tac `dyn = (case bd of Dynamic _ => T | Fixed _ => F)` >>
  qabbrev_tac `s2 = update_var ov (n2w(k*n)) q with vs_inst_idx := 1` >>
  qabbrev_tac `G2 = DRESTRICT G1 (COMPL {ov})` >>
  qabbrev_tac `tn2 = tn1 with t_var := tn1.t_var |+ (ov,{})` >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (q,G1,tn1) [] (OK s2,G2,tn2)` by suspend "mul" >>
  qabbrev_tac `s3 = if dyn then
    update_var tot (1w+n2w(k*n)) s2 with vs_inst_idx := 2 else s2` >>
  qabbrev_tac `G3 = if dyn then DRESTRICT G2 (COMPL {tot}) else G2` >>
  qabbrev_tac `tn3 = if dyn then tn2 with t_var := tn2.t_var |+ (tot,{}) else tn2` >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (s2,G2,tn2) [] (OK s3,G3,tn3)` by suspend "optional" >>
  qabbrev_tac `u = update_var ep ((if dyn then slot+1w else slot)+n2w(k*n)) s3
    with vs_inst_idx := LENGTH sa.cs_current_insts` >>
  qabbrev_tac `Gu = DRESTRICT G3 (COMPL {ep})` >>
  qabbrev_tac `tnu = tn3 with t_var := tn3.t_var |+ (ep,{})` >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (s3,G3,tn3) [] (OK u,Gu,tnu)` by suspend "last" >>
  qexistsl_tac [`u`,`Gu`,`tnu`] >>
  conj_tac >- metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans] >>
  suspend "endpoint"
QED

Resume for_storage_array_head_prefix_at[mul]:
  `get_instruction bb q.vs_inst_idx =
    SOME (mk_inst h MUL [Var idx;Lit (n2w n)] [ov])` by
    (simp[Abbr `q`, Abbr `s1`, jump_to_def] >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `q.vs_inst_idx = 0` by simp[Abbr `q`, jump_to_def] >>
  rpt gen_tac >>
  simp[Abbr `s2`, Abbr `G2`, Abbr `tn2`] >>
  drule_at (Pos (el 3)) for_storage_scalar_step >>
  disch_then (qspecl_then [`n2w n`,`n2w k`,`n2w(k*n)`] mp_tac) >>
  simp[wordsTheory.word_mul_n2w] >>
  disch_then irule >>
  Cases_on `dyn` >>
  gvs[allocas_from_def, allocas_below_fmp_def, op_taint_def,
    Abbr `q`, Abbr `s1`, Abbr `G1`, Abbr `tn1`,
    eval_operand_def, lookup_var_def, update_var_def, jump_to_def,
    op_prov_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Resume for_storage_array_head_prefix_at[optional]:
  Cases_on `dyn`
  >- (gvs[Abbr `s3`, Abbr `G3`, Abbr `tn3`] >>
      `get_instruction bb s2.vs_inst_idx =
        SOME (mk_inst (h+1) ADD [Lit 1w;Var ov] [tot])` by
        (simp[Abbr `s2`] >>
         qpat_x_assum `!j. _ ==> get_instruction bb j = _`
           (qspec_then `1` mp_tac) >> simp[]) >>
      `s2.vs_inst_idx = 1` by simp[Abbr `s2`] >>
      rpt gen_tac >>
      drule_at (Pos (el 3)) for_storage_scalar_step >>
      disch_then (qspecl_then [`n2w(k*n)`,`1w`,`1w+n2w(k*n)`] mp_tac) >>
      simp[] >> disch_then irule >>
      gvs[Abbr `s2`, Abbr `q`, Abbr `s1`, Abbr `G2`, Abbr `tn2`,
        eval_operand_def, lookup_var_def, update_var_def, jump_to_def,
        op_taint_def, op_prov_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
        allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  simp[Abbr `s3`, Abbr `G3`, Abbr `tn3`] >> rpt gen_tac >>
  irule (cj 1 gas_origin_ptr_path_rules) >>
  simp[Abbr `s2`, Abbr `q`, Abbr `s1`, update_var_def, jump_to_def]
QED

Resume for_storage_array_head_prefix_at[last]:
  rpt (qpat_x_assum `!D explicit. gas_origin_ptr_path _ _ _ _` kall_tac) >>
  `s3.vs_inst_idx = (if dyn then 2 else 1) /\
   LENGTH sa.cs_current_insts = SUC s3.vs_inst_idx /\
   get_instruction bb s3.vs_inst_idx = SOME
     (mk_inst (h+(if dyn then 2 else 1)) ADD
       [base_op;Var (if dyn then tot else ov)] [ep])` by
    (Cases_on `dyn` >>
     simp[Abbr `s3`, Abbr `s2`] >>
     qpat_x_assum `!j. _ ==> get_instruction bb j = _`
       (qspec_then `if dyn then 2 else 1` mp_tac) >> gvs[]) >>
  rpt gen_tac >>
  simp[Abbr `u`, Abbr `Gu`, Abbr `tnu`] >>
  drule_at (Pos (el 3)) for_storage_scalar_step >>
  disch_then (qspecl_then
    [`(if dyn then 1w else 0w)+n2w(k*n)`,`slot`,
     `(if dyn then slot+1w else slot)+n2w(k*n)`] mp_tac) >>
  Cases_on `dyn` >> simp[wordsTheory.WORD_ADD_ASSOC, wordsTheory.WORD_ADD_0] >>
  disch_then irule >>
  Cases_on `base_op` >>
  gvs[Abbr `s3`, Abbr `s2`, Abbr `q`, Abbr `s1`,
    Abbr `G3`, Abbr `G2`, Abbr `G1`, Abbr `tn3`, Abbr `tn2`, Abbr `tn1`,
    eval_operand_def, lookup_var_def, update_var_def, jump_to_def,
    op_taint_def, op_prov_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
    allocas_from_def, allocas_below_fmp_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Resume for_storage_array_head_prefix_at[endpoint]:
  rpt (qpat_x_assum `!D explicit. gas_origin_ptr_path _ _ _ _` kall_tac) >>
  Cases_on `dyn` >>
  gvs[Abbr `u`, Abbr `Gu`, Abbr `tnu`, Abbr `s3`, Abbr `s2`,
    Abbr `q`, Abbr `s1`, Abbr `G3`, Abbr `G2`, Abbr `G1`,
    Abbr `tn3`, Abbr `tn2`, Abbr `tn1`,
    update_var_def, jump_to_def, eval_operand_def, lookup_var_def,
    op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
    allocas_from_def, allocas_below_fmp_def] >>
  (conj_tac
   >- (AP_TERM_TAC >> simp[EXTENSION] >> metis_tac[]) >>
   rpt strip_tac >> gvs[] >> metis_tac[])
QED

Finalise for_storage_array_head_prefix_at

Theorem for_storage_array_head_prefix:
  lookup_block cond func.fn_blocks = SOME cb /\
  cb.bb_instructions =
  [mk_inst (h - 2) EQ [Var idx; lvo] [dv];
   mk_inst (h - 1) JNZ [Var dv; Label exit; Label bod] []] /\
  lookup_block bod func.fn_blocks = SOME bb /\ sa.cs_current_bb = bod /\
  sa.cs_current_insts =
  [mk_inst h MUL [Var idx; Lit (n2w n)] [ov]] ++
  (if case bd of Fixed v => F | Dynamic v1 => T then
     [mk_inst (h + 1) ADD [Lit 1w; Var ov] [tot]]
   else []) ++
  [mk_inst (h + if case bd of Fixed v => F | Dynamic v1 => T then 2 else 1) ADD
     [Lit slot;
      Var (if (case bd of Fixed v => F | Dynamic v1 => T) then tot else ov)]
     [ep]] /\
  (!j. j < LENGTH sa.cs_current_insts ==>
       get_instruction bb j = SOME (fEL sa.cs_current_insts j)) /\
  ALL_DISTINCT
    (if (case bd of Fixed v => F | Dynamic v1 => T) then [dv; ov; tot; ep]
     else [dv; ov; ep]) /\
  ~MEM idx
    (if (case bd of Fixed v => F | Dynamic v1 => T) then [dv; ov; tot; ep]
     else [dv; ov; ep]) /\
  ~MEM p
    (if (case bd of Fixed v => F | Dynamic v1 => T) then [dv; ov; tot; ep]
     else [dv; ov; ep]) /\
  (!x. lvo = Var x ==>
       ~MEM x
         (if (case bd of Fixed v => F | Dynamic v1 => T) then [dv; ov; tot; ep]
          else [dv; ov; ep])) /\ s.vs_current_bb = cond /\ s.vs_inst_idx = 0 /\
  ~s.vs_halted /\ lookup_var idx s = SOME (n2w k) /\ k < len /\
  len < 2 ** 256 /\ FLOOKUP G idx = NONE /\ op_taint tn (Var idx) = {} /\
  eval_operand lvo s = SOME (n2w len) /\ op_prov G lvo = NONE /\
  op_taint tn lvo = {} /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?u Gu tnu.
    (!D explicit.
       gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
         (OK u,Gu,tnu)) /\
    u =
    update_var ep
      ((if case bd of Fixed v => F | Dynamic v1 => T then slot + 1w else slot) +
       n2w (k * n))
      (if (case bd of Fixed v => F | Dynamic v1 => T) then
         update_var tot (1w + n2w (k * n))
           (update_var ov (n2w (k * n)) (jump_to bod (update_var dv 0w s)))
       else update_var ov (n2w (k * n)) (jump_to bod (update_var dv 0w s))) with
    vs_inst_idx := LENGTH sa.cs_current_insts /\
    Gu =
    DRESTRICT G
      (COMPL
         (set
            (if (case bd of Fixed v => F | Dynamic v1 => T) then
               [dv; ov; tot; ep]
             else [dv; ov; ep]))) /\
    tnu =
    tn with
    t_var :=
      FOLDL (\m x. fmupdate x {} m) tn.t_var
        (if (case bd of Fixed v => F | Dynamic v1 => T) then [dv; ov; tot; ep]
         else [dv; ov; ep]) /\ u.vs_current_bb = sa.cs_current_bb /\
    u.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~u.vs_halted /\
    eval_operand (Var ep) u =
    SOME
      ((if case bd of Fixed v => F | Dynamic v1 => T then slot + 1w else slot) +
       n2w (k * n)) /\ FLOOKUP Gu ep = NONE /\ op_taint tnu (Var ep) = {} /\
    (!x. ~MEM x
           (if (case bd of Fixed v => F | Dynamic v1 => T) then
              [dv; ov; tot; ep]
            else [dv; ov; ep]) ==>
         lookup_var x u = lookup_var x s /\ FLOOKUP Gu x = FLOOKUP G x /\
         op_taint tnu (Var x) = op_taint tn (Var x)) /\ allocas_from lo u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u)
Proof
  strip_tac >>
  MATCH_MP_TAC (Q.INST [`base_op` |-> `Lit slot`] for_storage_array_head_prefix_at) >>
  asm_rewrite_tac[] >> simp[op_taint_def, op_prov_def, cj 1 eval_operand_def]
QED

(* Execute and pop the real body scope, then land before the increment or
   at the loop exit. The allocation frame stays anchored at the For entry. *)
Theorem for_storage_array_body_cleanup_full:
  !DF lo d ctx shadow_ctx func shadow_func PG cx RetQ c0 e0 sa0 sb s0 G0 tn0 tr
      slot dst tyv typ bd vs len nb id env p idx lvo sd body si lctx ei v bc
      bc1 sb0 sb1 sj tops bindings ret_ty env_b k off a rs st0 s G tn exit incr
      shadow_sb0 shadow_sb1.
    body_stmts_full_ok cx body /\ body_inv tops ctx bc cx /\ shadow_body_inv tops ctx shadow_ctx /\
    supported_stmts tops bindings body /\
    (!target.
       supported_stmts_expr_exists (expr_abi_decode_target_root target) body ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv bc cx (extend_local env id typ F)
      (ei with
       scopes :=
         fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
           FEMPTY::ei.scopes) /\
    ce_locals_declared bc (extend_local env id typ F) /\
    locals_alloc_ok bc (extend_local env id typ F) /\
    type_stmts (extend_local env id typ F) ret_ty body = SOME env_b /\
    stmts_exprs_ok bc body /\ call_evaluation_safe cx (int_calls_stmts body) /\
    frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ bc
      ret_ty /\ stmts_env bc (InLoop exit incr) ret_ty body sb0 = (bc1,sb1) /\
    stmts_env bc (InLoop exit incr) ret_ty (MAP gas_shadow_stmt body)
      shadow_sb0 = (bc1,shadow_sb1) /\ gas_shadow_state sb0 shadow_sb0 /\
    gas_shadow_state sb1 shadow_sb1 /\ gas_shadow_context ctx shadow_ctx /\
    ctx_inst_ids_distinct ctx /\ gas_shadow_function func shadow_func /\
    MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sb0 sb1 func /\
    fn_has_code shadow_sb0 shadow_sb1 shadow_func /\
    (!H. dead_lo_ok H (DF H) lo bc cx) /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved bc sb0 /\ ret_pc_ok bc sb0 s /\
    (!x sz. bc.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb0 x) /\
    ~block_is_terminated sb0 /\
    gas_admissible (eval_stmts cx body) (stmt_res_ok (InLoop exit incr))
      (ei with
       scopes :=
         fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
           FEMPTY::ei.scopes) /\ return_buf_frame d bc sb0 s /\
    return_buf_sep d bc
      (ei with scopes :=
        fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
          FEMPTY::ei.scopes) s /\
    (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_no_wrap inst u) /\
    (!H. valid_horizon cx st0 H
           (ei with
            scopes :=
              fmupdate id
                <|assignable := F; type := tyv; value := v; popped := []|>
                FEMPTY::ei.scopes).storage_trace ==>
         stmt_state_rel H ctx func bc cx
           (ei with
            scopes :=
              fmupdate id
                <|assignable := F; type := tyv; value := v; popped := []|>
                FEMPTY::ei.scopes) s /\
         storage_well_formed_on cx
           (ei with
            scopes :=
              fmupdate id
                <|assignable := F; type := tyv; value := v; popped := []|>
                FEMPTY::ei.scopes) (FST H) /\
         ghost_inv_at (DF H) lo d bc cx
           (ei with
            scopes :=
              fmupdate id
                <|assignable := F; type := tyv; value := v; popped := []|>
                FEMPTY::ei.scopes) G tn s) /\ ~s.vs_halted /\
    s.vs_current_bb = sb0.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb0.cs_current_insts /\ not_fresh_at sb0 idx /\
    not_fresh_at sb0 p /\ (!x. lvo = Var x ==> not_fresh_at sb0 x) /\
    (!lbl. lvo <> Label lbl) /\ lookup_var idx s = SOME (n2w k) /\
    lookup_var p s = SOME dst /\ eval_operand lvo s = SOME (n2w len) /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    id NOTIN FDOM env.var_types /\
    evaluate_type (get_tenv cx) typ = SOME tyv /\ value_has_type tyv v /\
    expr_sim_inv c0 cx env ei /\ lookup_scopes id ei.scopes = NONE /\
    ce_locals_declared c0 env /\ locals_alloc_ok c0 env /\
    cenv_top_ext c0 c0 ei.scopes /\
    cenv_top_ext c0 bc
      (ei with
       scopes :=
         fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
           FEMPTY::ei.scopes).scopes /\ same_frame c0 bc /\
    local_ptrs_reserved c0 sb0 /\ sa0.cs_next_id <= sb0.cs_next_id /\
    (!x. not_fresh_at sa0 x ==> not_fresh_at sb0 x) /\
    (!x sz. c0.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x) /\
    emit_jmp_if_not_terminated incr sb1 = ((),sj) /\ fn_has_code sb1 sj func /\
    si.cs_current_bb = incr /\ si.cs_current_insts = [] /\
    sb.cs_current_bb = exit /\ sb.cs_current_insts = [] /\
    ~block_is_terminated sb /\ k < len /\ len = LENGTH vs /\
    len <= bound_length bd /\
    vs =
    GENLIST
      (\j.
         PlaceR
           (StoragePlace tr
              ((case bd of Fixed v => slot | Dynamic v1 => slot + 1w) +
               n2w (j * type_slot_size tyv)) tyv)) len /\ a::rs = DROP k vs /\
    slot = n2w off /\
    MEM (StorageRoot tr off (ArrayTV tyv bd)) ei.storage_trace /\
    well_formed_type_value tyv /\ FLOOKUP G idx = NONE /\
    op_taint tn (Var idx) = {} /\ op_taint tn lvo = {} /\
    op_prov G lvo = NONE /\ eval_operand (Lit slot) s = SOME slot /\
    op_taint tn (Lit slot) = {} /\
    FLOOKUP s.vs_allocas sd.cs_next_id = SOME (w2n dst,nb) /\
    ptr_covers G tn p s nb /\ 32 * type_slot_size tyv <= nb /\
    w2n dst + nb < 2 ** 256 /\ w2n dst + nb <= s.vs_alloca_next /\
    (!name b sz.
       local_region c0 ei.scopes s name b sz ==>
       w2n dst + nb <= b \/ b + sz <= w2n dst) /\
    return_buf_frame d c0 sa0 s /\ ret_pc_ok c0 sa0 s /\
    (\c ee u GG tt.
       alloca_history func u /\
       (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
       s0.vs_alloca_next <= u.vs_alloca_next /\
       (!x w.
          not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
          lookup_var x u = SOME w) /\
       (!aid b.
          FLOOKUP s0.vs_allocas aid = SOME b ==>
          FLOOKUP u.vs_allocas aid = SOME b) /\
       (!x. not_fresh_at sa0 x ==>
            FLOOKUP GG x = FLOOKUP G0 x /\
            op_taint tt (Var x) = op_taint tn0 (Var x)) /\
       alloca_frame c0 e0 sa0 s0 c ee u /\
       !aid off sz i.
         FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
         (!name b sz'.
            local_region c0 e0.scopes s0 name b sz' ==>
            off + sz <= b \/ b + sz' <= off) /\ off <= i /\ i < off + sz /\
         i IN tt.t_mem ==>
         i IN tn0.t_mem) bc
      (ei with
       scopes :=
         fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
           FEMPTY::ei.scopes) s G tn ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0
      (finally
         (try (ignore_bind (eval_stmts cx body) (return F))
            handle_loop_exception) pop_scope)
      (ei with
       scopes :=
         fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
           FEMPTY::ei.scopes,s,G,tn)
      (\H res ee G1 tn1 t.
         ee.gas_obs = [] /\ ~t.vs_halted /\
         ?b. res = INL b /\
             (b ==>
              (\H ee GG tt u.
                 ?c. stmt_lands lctx sb (INL ()) u /\ ~u.vs_halted /\
                     ~block_is_terminated sb /\ c = c0 /\
                     cenv_top_ext c0 c ee.scopes /\
                     stmt_state_rel H ctx func c cx ee u /\
                     storage_well_formed_on cx ee (FST H) /\
                     return_buf_frame d c sb u /\ return_buf_sep d c ee u /\
                     ghost_inv_at (DF H) lo d c cx ee GG tt u /\
                     (\c ee u GG tt.
                        alloca_history func u /\
                        (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
                        s0.vs_alloca_next <= u.vs_alloca_next /\
                        (!x w.
                           not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
                           lookup_var x u = SOME w) /\
                        (!aid b.
                           FLOOKUP s0.vs_allocas aid = SOME b ==>
                           FLOOKUP u.vs_allocas aid = SOME b) /\
                        (!x. not_fresh_at sa0 x ==>
                             FLOOKUP GG x = FLOOKUP G0 x /\
                             op_taint tt (Var x) = op_taint tn0 (Var x)) /\
                        alloca_frame c0 e0 sa0 s0 c ee u /\
                        !aid off sz i.
                          FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
                          aid < sa0.cs_next_id /\
                          (!name b sz'.
                             local_region c0 e0.scopes s0 name b sz' ==>
                             off + sz <= b \/ b + sz' <= off) /\ off <= i /\
                          i < off + sz /\ i IN tt.t_mem ==>
                          i IN tn0.t_mem) c ee u GG tt) H ee G1 tn1 t) /\
             (~b ==>
              (\H rr ee GG tt u.
                 ?k off.
                   k < len /\ len = LENGTH vs /\ len <= bound_length bd /\
                   vs =
                   GENLIST
                     (\j.
                        PlaceR
                          (StoragePlace tr
                             ((case bd of
                                 Fixed v => slot
                               | Dynamic v1 => slot + 1w) +
                              n2w (j * type_slot_size tyv)) tyv)) len /\
                   rr = DROP k vs /\ slot = n2w off /\
                   MEM (StorageRoot tr off (ArrayTV tyv bd)) ee.storage_trace /\
                   evaluate_type (get_tenv cx) typ = SOME tyv /\
                   well_formed_type_value tyv /\
                   u.vs_current_bb = si.cs_current_bb /\
                   u.vs_inst_idx = LENGTH si.cs_current_insts /\
                   ~u.vs_halted /\ lookup_var idx u = SOME (n2w k) /\
                   FLOOKUP GG idx = NONE /\ op_taint tt (Var idx) = {} /\
                   eval_operand lvo u = SOME (n2w len) /\
                   op_taint tt lvo = {} /\ op_prov GG lvo = NONE /\
                   eval_operand (Lit slot) u = SOME slot /\
                   op_taint tt (Lit slot) = {} /\ lookup_var p u = SOME dst /\
                   FLOOKUP u.vs_allocas sd.cs_next_id = SOME (w2n dst,nb) /\
                   ptr_covers GG tt p u nb /\ 32 * type_slot_size tyv <= nb /\
                   w2n dst + nb < 2 ** 256 /\
                   w2n dst + nb <= u.vs_alloca_next /\
                   (!name b sz.
                      local_region c0 ee.scopes u name b sz ==>
                      w2n dst + nb <= b \/ b + sz <= w2n dst) /\
                   lookup_scopes id ee.scopes = NONE /\
                   expr_sim_inv c0 cx env ee /\ ce_locals_declared c0 env /\
                   locals_alloc_ok c0 env /\ cenv_top_ext c0 c0 ee.scopes /\
                   stmt_state_rel H ctx func c0 cx ee u /\
                   storage_well_formed_on cx ee (FST H) /\
                   ghost_inv_at (DF H) lo d c0 cx ee GG tt u /\
                   return_buf_frame d c0 sa0 u /\ ret_pc_ok c0 sa0 u /\
                   return_buf_sep d c0 ee u /\ body_stmts_full_ok cx body /\
                   (\c ee u GG tt.
                      alloca_history func u /\
                      (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
                      s0.vs_alloca_next <= u.vs_alloca_next /\
                      (!x w.
                         not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
                         lookup_var x u = SOME w) /\
                      (!aid b.
                         FLOOKUP s0.vs_allocas aid = SOME b ==>
                         FLOOKUP u.vs_allocas aid = SOME b) /\
                      (!x. not_fresh_at sa0 x ==>
                           FLOOKUP GG x = FLOOKUP G0 x /\
                           op_taint tt (Var x) = op_taint tn0 (Var x)) /\
                      alloca_frame c0 e0 sa0 s0 c ee u /\
                      !aid off sz i.
                        FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
                        aid < sa0.cs_next_id /\
                        (!name b sz'.
                           local_region c0 e0.scopes s0 name b sz' ==>
                           off + sz <= b \/ b + sz' <= off) /\ off <= i /\
                        i < off + sz /\ i IN tt.t_mem ==>
                        i IN tn0.t_mem) c0 ee u GG tt) H (a::rs) ee G1 tn1 t))
      (\H res ee gt r.
         ?ex.
           res = INR ex /\
           (\H ex ee gt r.
              (!tail.
                 stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt r) /\
              halt_exit H cx ee (INR ex) r /\
              (ctx_has_dalloca ctx ==>
               !u. r = Halt u \/ (?ir. r = IntRet ir u) ==> allocas_below_fmp u))
             H ex ee gt r)
Proof
  rpt gen_tac >>
  qpat_abbrev_tac `eb = ei with scopes := (FEMPTY |+ (id, _)) :: ei.scopes` >>
  qpat_abbrev_tac `explicit = gas_explicit_sites ctx shadow_ctx` >>
  abbrev_lambda_tac "Fr" 5 0 `alloca_history func s /\ _` >>
  abbrev_lambda_tac "Ready" 6 2 `k < len /\ _` >>
  abbrev_lambda_tac "Done" 5 1 `stmt_lands lctx sb (INL ()) t /\ _` >>
  abbrev_lambda_tac "R" 5 0 `(!tail. stmt_exit_ptr _ (ee with gas_obs := tail) (INR ex) gt r) /\ _` >>
  strip_tac >> rename1 `value_has_type tyv v` >>
  rename1 `body_stmts_full_ok cx stmts` >>
  `(alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s))` by
    (qpat_assum `Fr bc eb s G tn` mp_tac >> simp[NoAsms, Abbr `Fr`]) >>
  qunabbrev_tac `eb` >> qunabbrev_tac `explicit` >>
  qpat_assum `frame_ret_ok_full _ _ _ _ _`
    (mp_then (Pat `frame_ret_ok_full _ _ _ _ _`) mp_tac
      (BETA_RULE for_storage_body_invoke_full)) >>
  disch_then (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  disch_then (fn th => qpat_assum `stmts_env bc (InLoop exit incr) ret_ty stmts sb0 = _`
    (mp_then (Pat `stmts_env _ _ _ _ _`) mp_tac th)) >>
  disch_then (drule_at (Pat `gas_shadow_state sb0 _`)) >>
  disch_then (drule_at (Pat `supported_stmts _ _ _`)) >>
  disch_then (drule_at (Pat `type_stmts _ _ _`)) >>
  disch_then (drule_at (Pat `valid_horizon _ _ _ _`)) >>
  disch_then (fn th => qpat_assum `lookup_var idx s = _`
    (mp_then (Pat `lookup_var _ _ = SOME (n2w _)`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `lookup_var p s = _`
    (mp_then (Pat `lookup_var _ _ = _`) mp_tac th)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (qspec_then `shadow_sb0` (mp_tac o CONV_RULE (DEPTH_CONV BETA_CONV))) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ (eval_stmts _ _) _ Qraw _` >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ (eval_stmts _ _) _ Qraw Rraw` >>
  (* Choose the suffix endpoint with the raw result still in scope.
     In particular, the loop handler maps both normal and Continue to INL F. *)
  qabbrev_tac `Qland = (\H (raw : unit + exception) ef GG tt u.
    ?sc rest b. ef.scopes = sc::rest /\
      (case raw of INL () => INL F
         | INR ex => FST (handle_loop_exception ex ef)) = INL b /\
      (ef with scopes := rest).gas_obs = [] /\ ~u.vs_halted /\
      (b ==> Done H (ef with scopes := rest) GG tt u) /\
      (~b ==> Ready H (a::rs) (ef with scopes := rest) GG tt u))` >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full fp _ _ _ _ (eb,s,G,tn) Qraw Rraw` >>
  sg `gas_outcome_full fp (cx_tops cx) cx st0 (eval_stmts cx stmts)
       (eb,s,G,tn) Qland Rraw`
  >- (qunabbrev_tac `fp` >> irule gas_outcome_full_zero_suffix >>
      qexists_tac `Qraw` >> conj_tac >- suspend "landing" >>
      first_assum ACCEPT_TAC) >>
  suspend "handler"
QED

Resume for_storage_array_body_cleanup_full[landing]:
  map_every qx_gen_tac [`raw`, `ef`, `G1`, `tn1`, `t`] >> strip_tac >>
  qexistsl_tac [`if raw = INL () then jump_to incr t else t`, `G1`, `tn1`] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> Qraw H _ _ _ _ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  simp[NoAsms, Abbr `Qraw`] >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 strip_assume_tac
    (CONJUNCTS_THEN2 assume_tac (fn th =>
      assume_tac th >> qx_choose_then `xs` assume_tac th)))) >>
  `valid_horizon cx st0 H eb.storage_trace` by
    (qpat_assum `!tail. eval_stmts _ _ _ = _`
       (qspec_then `[]` (mp_then (Pat `f st = (res,st')`) mp_tac
         valid_horizon_frame)) >>
     simp[evaluation_state_accfupds,
          CONJUNCT1 (CONJUNCT2 evaluate_storage_trace_frame)]) >>
  qpat_assum `!H. valid_horizon _ _ H eb.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  sg `?sc rest b. ef.scopes = sc::rest /\
      (case raw of INL () => INL F
         | INR ex => FST (handle_loop_exception ex ef)) = INL b /\
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (t,G1,tn1) [] (OK (if raw = INL () then jump_to incr t else t),G1,tn1) /\
      (ef with scopes := rest).gas_obs = [] /\
      ~(if raw = INL () then jump_to incr t else t).vs_halted /\
      (b ==> Done H (ef with scopes := rest) G1 tn1
                   (if raw = INL () then jump_to incr t else t)) /\
      (~b ==> Ready H (a::rs) (ef with scopes := rest) G1 tn1
                   (if raw = INL () then jump_to incr t else t))`
  >- (map_every qunabbrev_tac [`Done`, `Ready`, `Fr`, `eb`] >>
      CONV_TAC (REDEPTH_CONV BETA_CONV) >>
      RULE_ASSUM_TAC (CONV_RULE (REDEPTH_CONV BETA_CONV)) >>
      irule (CONV_RULE (REDEPTH_CONV BETA_CONV)
        (REWRITE_RULE [LET_THM, combinTheory.S_DEF, combinTheory.C_DEF,
          combinTheory.o_DEF] for_storage_body_post_land_full)) >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      conj_tac >- (qexistsl_tac [`bindings`, `tops`] >> asm_rewrite_tac[]) >>
      conj_tac >- (qexists_tac `st0` >> first_assum ACCEPT_TAC) >>
      qexistsl_tac [`G`, `bc`, `bc1`, `ei`, `env_b`, `exit`, `k`, `off`,
        `ret_ty`, `s`, `sb0`, `sb1`, `sj`, `tn`, `v`] >>
      qpat_assum `alloca_history func s /\ _` (map_every assume_tac o CONJUNCTS) >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  simp[NoAsms, Abbr `Qland`] >>
  qexistsl_tac [`sc`, `rest`, `b`] >>
  asm_rewrite_tac[]
QED

Resume for_storage_array_body_cleanup_full[handler]:
  qunabbrev_tac `fp` >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ Qland Rraw`
    (mp_then (Pat `gas_outcome_full _ _ _ _ _ _ _ _`) mp_tac
      for_body_cleanup_full) >>
  (impl_tac >- simp[Abbr `eb`]) >>
  disch_then (mp_then (Pat `gas_outcome_full _ _ _ _ _ _ _ _`) mp_tac
    gas_outcome_full_post_mono) >>
  disch_then irule >>
  conj_tac >- suspend "normal_post" >> suspend "exit_post"
QED

Resume for_storage_array_body_cleanup_full[normal_post]:
  map_every qx_gen_tac [`H`, `out`, `ee`, `G1`, `tn1`, `t`] >> BETA_TAC >>
  disch_then (qx_choose_then `raw` (qx_choose_then `sc` strip_assume_tac)) >>
  qpat_x_assum `Qland H raw _ G1 tn1 t` mp_tac >>
  simp[NoAsms, Abbr `Qland`, evaluation_state_accfupds] >>
  disch_then (qx_choose_then `b` strip_assume_tac) >>
  `out = INL b` by
    (qpat_x_assum `out = _` SUBST1_TAC >>
     qpat_x_assum `_ = INL b` mp_tac >>
     Cases_on `raw` >> simp[NoAsms] >>
     rename1 `handle_loop_exception ex _` >> Cases_on `ex` >>
     simp[NoAsms, vyperInterpreterTheory.handle_loop_exception_def,
       return_def, raise_def]) >>
  (metis_tac[])
QED

Resume for_storage_array_body_cleanup_full[exit_post]:
  map_every qx_gen_tac [`H`, `out`, `ee`, `gt`, `r`] >> BETA_TAC >>
  disch_then (qx_choose_then `raw` (qx_choose_then `sc` strip_assume_tac)) >>
  sg `?ex. raw = INR ex /\ out = INR ex`
  >- (qpat_assum `out = _` SUBST1_TAC >>
      qpat_assum `Rraw H raw _ gt r` mp_tac >>
      simp[NoAsms, Abbr `Rraw`] >>
      disch_then (qspec_then `[]` mp_tac o CONJUNCT1) >>
      Cases_on `raw` >>
      simp[NoAsms, stmt_exit_ptr_def, oneline exprSimDefsTheory.expr_exit_def] >>
      rename1 `_ = INR ex` >> Cases_on `ex` >> simp[NoAsms] >>
      Cases_on `r` >> simp[NoAsms]) >>
  qexists_tac `ex` >> conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `raw = INR ex` SUBST_ALL_TAC >>
  simp[NoAsms, Abbr `R`] >>
  qpat_x_assum `Rraw H (INR ex) _ gt r` mp_tac >>
  qpat_assum `Abbrev (Rraw = _)`
    (fn th => pure_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
  BETA_TAC >>
  disch_then (mp_tac o MATCH_MP for_full_exit_scopes_gas_obs) >>
  disch_then (qspecl_then [`ee.scopes`, `ee.gas_obs`] mp_tac) >>
  `((ee with scopes := sc::ee.scopes) with
     <|scopes := ee.scopes; gas_obs := ee.gas_obs|>) = ee` by
    simp[NoAsms, evaluation_state_component_equality] >>
  pop_assum SUBST1_TAC >>
  `!tail. (ee with <|scopes := ee.scopes; gas_obs := tail|>) =
          ee with gas_obs := tail` by
    simp[NoAsms, evaluation_state_component_equality] >>
  pop_assum (fn th => pure_rewrite_tac [th]) >>
  simp[NoAsms, halt_exit_INR_type] >>
  disch_then (ACCEPT_TAC o CONJUNCT2 o CONJUNCT2)
QED

Finalise for_storage_array_body_cleanup_full

(* Interpret the scalar-prefix endpoint at the original loop-entry anchor.
   Its new cursor is justified by the ALLOCA-free destination prefix. *)
Theorem for_storage_array_head_prefix_transport:
  !H D lo d ctx func cx c0 e0 sa0 s0 G0 tn0 ei s G tn u Gu tnu bd dv ov tot ep
      slot k n sa bod bb idx p dst nb lvo len.
    u =
    update_var ep
      ((if case bd of Fixed v => F | Dynamic v1 => T then slot + 1w else slot) +
       n2w (k * n))
      (if (case bd of Fixed v => F | Dynamic v1 => T) then
         update_var tot (1w + n2w (k * n))
           (update_var ov (n2w (k * n)) (jump_to bod (update_var dv 0w s)))
       else update_var ov (n2w (k * n)) (jump_to bod (update_var dv 0w s))) with
    vs_inst_idx := LENGTH sa.cs_current_insts /\
    Gu =
    DRESTRICT G
      (COMPL
         (set
            (if (case bd of Fixed v => F | Dynamic v1 => T) then
               [dv; ov; tot; ep]
             else [dv; ov; ep]))) /\
    tnu =
    tn with
    t_var :=
      FOLDL (\m x. fmupdate x {} m) tn.t_var
        (if (case bd of Fixed v => F | Dynamic v1 => T) then [dv; ov; tot; ep]
         else [dv; ov; ep]) /\ lookup_block bod func.fn_blocks = SOME bb /\
    (!j. j < LENGTH sa.cs_current_insts ==>
         ?inst. get_instruction bb j = SOME inst /\ inst.inst_opcode <> ALLOCA) /\
    ALL_DISTINCT
      (if (case bd of Fixed v => F | Dynamic v1 => T) then [dv; ov; tot; ep]
       else [dv; ov; ep]) /\
    (!x. MEM x
           (if (case bd of Fixed v => F | Dynamic v1 => T) then
              [dv; ov; tot; ep]
            else [dv; ov; ep]) ==>
         ~not_fresh_at sa0 x) /\
    ~MEM idx
      (if (case bd of Fixed v => F | Dynamic v1 => T) then [dv; ov; tot; ep]
       else [dv; ov; ep]) /\
    ~MEM p
      (if (case bd of Fixed v => F | Dynamic v1 => T) then [dv; ov; tot; ep]
       else [dv; ov; ep]) /\
    (!x. lvo = Var x ==>
         ~MEM x
           (if (case bd of Fixed v => F | Dynamic v1 => T) then
              [dv; ov; tot; ep]
            else [dv; ov; ep])) /\ sa.cs_current_bb = bod /\ ~s.vs_halted /\
    local_ptrs_reserved c0 sa0 /\
    (!x cap.
       c0.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa0 x) /\
    (!x cap. c0.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa0 x) /\
    stmt_state_rel H ctx func c0 cx ei s /\
    storage_well_formed_on cx ei (FST H) /\
    ghost_inv_at D lo d c0 cx ei G tn s /\
    (\c ee s G tn.
       alloca_history func s /\
       (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
       s0.vs_alloca_next <= s.vs_alloca_next /\
       (!x w.
          not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
          lookup_var x s = SOME w) /\
       (!aid b.
          FLOOKUP s0.vs_allocas aid = SOME b ==>
          FLOOKUP s.vs_allocas aid = SOME b) /\
       (!x. not_fresh_at sa0 x ==>
            FLOOKUP G x = FLOOKUP G0 x /\
            op_taint tn (Var x) = op_taint tn0 (Var x)) /\
       alloca_frame c0 e0 sa0 s0 c ee s /\
       !aid off sz i.
         FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
         (!name b sz'.
            local_region c0 e0.scopes s0 name b sz' ==>
            off + sz <= b \/ b + sz' <= off) /\ off <= i /\ i < off + sz /\
         i IN tn.t_mem ==>
         i IN tn0.t_mem) c0 ei s G tn /\ return_buf_frame d c0 sa0 s /\
    ret_pc_ok c0 sa0 s /\ lookup_var idx s = SOME (n2w k) /\
    FLOOKUP G idx = NONE /\ op_taint tn (Var idx) = {} /\
    lookup_var p s = SOME dst /\ ptr_covers G tn p s nb /\
    eval_operand lvo s = SOME (n2w len) /\ op_prov G lvo = NONE /\
    op_taint tn lvo = {} ==>
    stmt_state_rel H ctx func c0 cx ei u /\
    storage_well_formed_on cx ei (FST H) /\
    ghost_inv_at D lo d c0 cx ei Gu tnu u /\
    (\c ee s G tn.
       alloca_history func s /\
       (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
       s0.vs_alloca_next <= s.vs_alloca_next /\
       (!x w.
          not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
          lookup_var x s = SOME w) /\
       (!aid b.
          FLOOKUP s0.vs_allocas aid = SOME b ==>
          FLOOKUP s.vs_allocas aid = SOME b) /\
       (!x. not_fresh_at sa0 x ==>
            FLOOKUP G x = FLOOKUP G0 x /\
            op_taint tn (Var x) = op_taint tn0 (Var x)) /\
       alloca_frame c0 e0 sa0 s0 c ee s /\
       !aid off sz i.
         FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
         (!name b sz'.
            local_region c0 e0.scopes s0 name b sz' ==>
            off + sz <= b \/ b + sz' <= off) /\ off <= i /\ i < off + sz /\
         i IN tn.t_mem ==>
         i IN tn0.t_mem) c0 ei u Gu tnu /\ return_buf_frame d c0 sa0 u /\
    ret_pc_ok c0 sa0 u /\ u.vs_current_bb = sa.cs_current_bb /\
    u.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~u.vs_halted /\
    allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    lookup_var idx u = SOME (n2w k) /\ FLOOKUP Gu idx = NONE /\
    op_taint tnu (Var idx) = {} /\ eval_operand lvo u = SOME (n2w len) /\
    op_prov Gu lvo = NONE /\ op_taint tnu lvo = {} /\
    lookup_var p u = SOME dst /\ ptr_covers Gu tnu p u nb /\
    eval_operand (Var ep) u =
    SOME
      ((if case bd of Fixed v => F | Dynamic v1 => T then slot + 1w else slot) +
       n2w (k * n)) /\ FLOOKUP Gu ep = NONE /\ op_taint tnu (Var ep) = {} /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    u.vs_memory = s.vs_memory /\ u.vs_immutables = s.vs_immutables /\
    tnu.t_mem = tn.t_mem /\
    !name b sz.
      local_region c0 ei.scopes u name b sz <=>
      local_region c0 ei.scopes s name b sz
Proof
 rpt gen_tac >>
  abbrev_lambda_tac "Fr" 5 0 `alloca_history func s /\ _` >>
  qpat_abbrev_tac `dyn = (case bd of Dynamic _ => T | Fixed _ => F)` >>
  qpat_abbrev_tac `outs = if dyn then [dv;ov;tot;ep] else [dv;ov;ep]` >>
  qpat_abbrev_tac `addr = (if dyn then slot+1w else slot)+n2w(k*n)` >>
  strip_tac >>
 `u.vs_current_bb = sa.cs_current_bb /\
  u.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~u.vs_halted /\
  u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
  u.vs_memory = s.vs_memory /\ u.vs_immutables = s.vs_immutables /\
  u.vs_call_ctx = s.vs_call_ctx /\ u.vs_accounts = s.vs_accounts /\
  u.vs_transient = s.vs_transient /\ u.vs_fmp = s.vs_fmp /\
  u.vs_initial_fmp = s.vs_initial_fmp /\
  tnu.t_mem = tn.t_mem /\ tnu.t_stor = tn.t_stor /\
  tnu.t_trans = tn.t_trans /\ tnu.t_imm = tn.t_imm /\
  u = jump_to bod s with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|> /\
  eval_operand (Var ep) u = SOME addr /\ FLOOKUP Gu ep = NONE /\
  op_taint tnu (Var ep) = {} /\
  (!x. ~MEM x outs ==>
    lookup_var x u = lookup_var x s /\ FLOOKUP Gu x = FLOOKUP G x /\
    op_taint tnu (Var x) = op_taint tn (Var x))` by suspend "endpoint" >>
 qpat_x_assum `u = (update_var _ _ _) with vs_inst_idx := _` kall_tac >>
 qpat_x_assum `Gu = DRESTRICT _ _` kall_tac >>
 qpat_x_assum `tnu = tn with t_var := _` kall_tac >>
 `!x. not_fresh_at sa0 x ==>
    lookup_var x u = lookup_var x s /\ FLOOKUP Gu x = FLOOKUP G x /\
    op_taint tnu (Var x) = op_taint tn (Var x)` by
   (rpt strip_tac >> `~MEM x outs` by metis_tac[] >> simp[]) >>
 `!name b sz. local_region c0 ei.scopes u name b sz <=>
               local_region c0 ei.scopes s name b sz` by
   (irule exprSimPtrLiteralBufferTheory.literal_ptr_local_region_frame >>
    qexists_tac `sa0` >> simp[]) >>
 `stmt_state_rel H ctx func c0 cx ei u` by suspend "rel" >>
 `ghost_inv_at D lo d c0 cx ei Gu tnu u` by
   (irule ghost_inv_at_exterior_frame >>
    qexistsl [`G`,`ei`,`s`,`sa0`,`tn`] >> simp[]) >>
 `Fr c0 ei u Gu tnu` by suspend "frame" >>
 suspend "post"
QED

Resume for_storage_array_head_prefix_transport[endpoint]:
 fs[Abbr `outs`] >> Cases_on `dyn` >>
 gvs[update_var_def, jump_to_def, eval_operand_def, lookup_var_def,
     op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >> metis_tac[]
QED

Resume for_storage_array_head_prefix_transport[rel]:
 irule bodyPtrSignedConvertSourceFrameTheory.stmt_state_rel_readonly_vars_pc >>
 qexistsl [`jump_to bod s`,`sa0`] >> simp[stmt_state_rel_jump_to] >>
 simp[jump_to_def, lookup_var_def, GSYM lookup_var_def]
QED

Resume for_storage_array_head_prefix_transport[frame]:
 qpat_x_assum `Fr c0 ei s G tn` mp_tac >> simp[Abbr `Fr`] >> strip_tac >>
 `alloca_history func u` by
   (qpat_x_assum `alloca_history func s` mp_tac >>
    simp[alloca_history_def] >> disch_tac >>
    qx_gen_tac `j` >> qx_gen_tac `inst` >> strip_tac >>
    qpat_assum `!i. i < LENGTH sa.cs_current_insts ==>
        ?a. get_instruction bb i = SOME a /\ a.inst_opcode <> ALLOCA`
      (qspec_then `j` mp_tac) >>
    (impl_tac >- simp[]) >> disch_then (qx_choose_then `other` strip_assume_tac) >>
    `other = inst` by
      (qpat_x_assum `get_instruction bb j = SOME other` mp_tac >> simp[]) >>
    gvs[]) >>
 `alloca_frame c0 e0 sa0 s0 c0 ei u` by
   (qpat_x_assum `alloca_frame c0 e0 sa0 s0 c0 ei s` mp_tac >>
    simp[alloca_frame_def]) >>
 simp[allocas_below_fmp_def] >> metis_tac[allocas_below_fmp_def]
QED

Resume for_storage_array_head_prefix_transport[post]:
 `return_buf_frame d c0 sa0 u` by
   (irule return_buf_frame_frame >> qexistsl [`c0`,`s`,`sa0`] >> simp[] >> metis_tac[]) >>
 `ret_pc_ok c0 sa0 u` by
   (irule ret_pc_ok_frame >> qexistsl [`c0`,`s`,`sa0`] >> simp[] >> metis_tac[]) >>
 `ptr_covers Gu tnu p u nb` by
   (irule ptr_covers_lookup_frame >> qexistsl [`G`,`s`,`tn`] >> simp[]) >>
 `allocas_from lo u` by
   (qpat_x_assum `ghost_inv_at D lo d c0 cx ei Gu tnu u` mp_tac >> simp[ghost_inv_at_def]) >>
 `(ctx_has_dalloca ctx ==> allocas_below_fmp u)` by
   (qpat_x_assum `Fr c0 ei u Gu tnu` mp_tac >> simp[Abbr `Fr`]) >>
 `u.vs_labels = s.vs_labels` by
   (qpat_assum `u = jump_to bod s with <|vs_vars := _; vs_inst_idx := _|>`
      SUBST1_TAC >> simp[jump_to_def]) >>
 simp[] >> Cases_on `lvo` >> gvs[eval_operand_def, op_prov_def, op_taint_def]
QED

Finalise for_storage_array_head_prefix_transport

(* Read the current captured child, execute the scalar head and copy, and
   register the one selected copy endpoint as the actual body entry. *)
Theorem for_storage_array_head_full:
  !DF lo d ctx func cx RetQ lctx c0 e0 sa0 s0 G0 tn0 tr slot dst tyv typ bd vs
      len nb id env p idx cond lvo sd body st0 explicit PG dv ov tot ep h exit
      bod incr cb bb sa st bc sb0 inst ce tyarr ann nid ca place cb0.
    0 < type_slot_size tyv /\ len < 2 ** 256 /\
    body_for_full_ok cx tyv id body vs /\ id NOTIN FDOM env.var_types /\
    declare_local c0 id typ sd = (bc,st) /\ c0.ce_alloca_locals /\
    type_memory_bytes c0 typ < 2 ** 64 /\
    (!l. FLOOKUP c0.ce_vars id = SOME l ==> ?q sz. l = PtrVar q sz) /\
    FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) nb) /\
    sa0.cs_next_var <= sb0.cs_next_var /\
    (!x. not_fresh_at sa0 x ==> not_fresh_at sa x) /\
    local_ptrs_reserved c0 sa0 /\ local_ptrs_reserved c0 sa /\
    local_ptrs_reserved bc sa /\
    (!x cap.
       c0.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa0 x) /\
    (!x cap. c0.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa0 x) /\
    not_fresh_at sa p /\ not_fresh_at sa idx /\
    (!x. lvo = Var x ==> not_fresh_at sa x) /\ (!lbl. lvo <> Label lbl) /\
    (!scs. lookup_scopes id scs = NONE ==> not_local_ptr bc (FEMPTY::scs) p) /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [p] /\ inst.inst_id = sd.cs_next_id /\
    sa0.cs_next_id <= inst.inst_id /\ fn_inst_ids_distinct func /\
    (!H. dead_lo_ok H (DF H) lo c0 cx) /\
    lookup_block cond func.fn_blocks = SOME cb /\
    cb.bb_instructions =
    [mk_inst (h - 2) EQ [Var idx; lvo] [dv];
     mk_inst (h - 1) JNZ [Var dv; Label exit; Label bod] []] /\
    lookup_block bod func.fn_blocks = SOME bb /\ sa.cs_current_bb = bod /\
    sa.cs_current_insts =
    [mk_inst h MUL [Var idx; Lit (n2w (type_slot_size tyv))] [ov]] ++
    (if case bd of Fixed v => F | Dynamic v1 => T then
       [mk_inst (h + 1) ADD [Lit 1w; Var ov] [tot]]
     else []) ++
    [mk_inst (h + if case bd of Fixed v => F | Dynamic v1 => T then 2 else 1)
       ADD
       [Lit slot;
        Var (if (case bd of Fixed v => F | Dynamic v1 => T) then tot else ov)]
       [ep]] /\
    (!j. j < LENGTH sa.cs_current_insts ==>
         get_instruction bb j = SOME (fEL sa.cs_current_insts j)) /\
    ALL_DISTINCT
      (if (case bd of Fixed v => F | Dynamic v1 => T) then [dv; ov; tot; ep]
       else [dv; ov; ep]) /\
    (!x. MEM x
           (if (case bd of Fixed v => F | Dynamic v1 => T) then
              [dv; ov; tot; ep]
            else [dv; ov; ep]) ==>
         ~not_fresh_at sa0 x) /\
    ~MEM idx
      (if (case bd of Fixed v => F | Dynamic v1 => T) then [dv; ov; tot; ep]
       else [dv; ov; ep]) /\
    ~MEM p
      (if (case bd of Fixed v => F | Dynamic v1 => T) then [dv; ov; tot; ep]
       else [dv; ov; ep]) /\
    (!x. lvo = Var x ==>
         ~MEM x
           (if (case bd of Fixed v => F | Dynamic v1 => T) then
              [dv; ov; tot; ep]
            else [dv; ov; ep])) /\
    compile_expr ce tyarr (TopLevelName ann nid) ca = (place,cb0) /\
    compile_iter_elem_copy bc (Var ep) (Var p) (type_slot_size tyv)
      (slot_loc tr) T typ typ sa = ((),sb0) /\
    compile_slot_to_memory (Var ep) (Var p) (type_slot_size tyv) (slot_loc tr)
      sa = (slot_copy_body sa,sb0) /\ slot_copy_external sa (Var ep) /\
    lookup_block sa.cs_current_bb func.fn_blocks =
    SOME
      <|bb_label := sa.cs_current_bb;
        bb_instructions := sa.cs_current_insts ++ slot_copy_init_insts sa|> /\
    lookup_block (slot_copy_cond sa) func.fn_blocks =
    SOME
      <|bb_label := slot_copy_cond sa;
        bb_instructions := slot_copy_cond_insts sa (type_slot_size tyv)|> /\
    lookup_block (slot_copy_body sa) func.fn_blocks =
    SOME
      <|bb_label := slot_copy_body sa;
        bb_instructions :=
          slot_copy_body_insts sa (Var ep) (Var p)
            (if tr then TLOAD else SLOAD)|> ==>
    !a rs ei s G tn.
      ~s.vs_halted /\ storage_trace_domain cx st0 ei.storage_trace /\
      (!H. valid_horizon cx st0 H ei.storage_trace ==>
           (\H rs ee G tn s.
              ?k off.
                k <= len /\ len = LENGTH vs /\ len <= bound_length bd /\
                vs =
                GENLIST
                  (\j.
                     PlaceR
                       (StoragePlace tr
                          ((case bd of
                              Fixed v => slot
                            | Dynamic v1 => slot + 1w) +
                           n2w (j * type_slot_size tyv)) tyv)) len /\
                rs = DROP k vs /\ slot = n2w off /\
                MEM (StorageRoot tr off (ArrayTV tyv bd)) ee.storage_trace /\
                evaluate_type (get_tenv cx) typ = SOME tyv /\
                well_formed_type_value tyv /\ s.vs_current_bb = cond /\
                s.vs_inst_idx = 0 /\ ~s.vs_halted /\
                lookup_var idx s = SOME (n2w k) /\ FLOOKUP G idx = NONE /\
                op_taint tn (Var idx) = {} /\
                eval_operand lvo s = SOME (n2w len) /\ op_taint tn lvo = {} /\
                op_prov G lvo = NONE /\
                eval_operand (Lit slot) s = SOME slot /\
                op_taint tn (Lit slot) = {} /\ lookup_var p s = SOME dst /\
                FLOOKUP s.vs_allocas sd.cs_next_id = SOME (w2n dst,nb) /\
                ptr_covers G tn p s nb /\ 32 * type_slot_size tyv <= nb /\
                w2n dst + nb < 2 ** 256 /\ w2n dst + nb <= s.vs_alloca_next /\
                (!name b sz.
                   local_region c0 ee.scopes s name b sz ==>
                   w2n dst + nb <= b \/ b + sz <= w2n dst) /\
                lookup_scopes id ee.scopes = NONE /\
                expr_sim_inv c0 cx env ee /\ ce_locals_declared c0 env /\
                locals_alloc_ok c0 env /\ cenv_top_ext c0 c0 ee.scopes /\
                stmt_state_rel H ctx func c0 cx ee s /\
                storage_well_formed_on cx ee (FST H) /\
                ghost_inv_at (DF H) lo d c0 cx ee G tn s /\
                return_buf_frame d c0 sa0 s /\ ret_pc_ok c0 sa0 s /\
                return_buf_sep d c0 ee s /\
                (k <> 0 ==> body_stmts_full_ok cx body) /\
                (\c ee s G tn.
                   alloca_history func s /\
                   (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
                   s0.vs_alloca_next <= s.vs_alloca_next /\
                   (!x w.
                      not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
                      lookup_var x s = SOME w) /\
                   (!aid b.
                      FLOOKUP s0.vs_allocas aid = SOME b ==>
                      FLOOKUP s.vs_allocas aid = SOME b) /\
                   (!x. not_fresh_at sa0 x ==>
                        FLOOKUP G x = FLOOKUP G0 x /\
                        op_taint tn (Var x) = op_taint tn0 (Var x)) /\
                   alloca_frame c0 e0 sa0 s0 c ee s /\
                   !aid off sz i.
                     FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
                     aid < sa0.cs_next_id /\
                     (!name b sz'.
                        local_region c0 e0.scopes s0 name b sz' ==>
                        off + sz <= b \/ b + sz' <= off) /\ off <= i /\
                     i < off + sz /\ i IN tn.t_mem ==>
                     i IN tn0.t_mem) c0 ee s G tn) H (a::rs) ei G tn s) /\
      gas_admissible (eval_for cx tyv id body (a::rs)) (stmt_res_ok lctx) ei ==>
      (?v. !tail.
         bind (read_result cx a) (\w. push_scope_with_var id tyv w)
           (ei with gas_obs := tail) =
         (INL (),
          (\ee v.
             ee with
             scopes :=
               fmupdate id
                 <|assignable := F; type := tyv; value := v; popped := []|>
                 FEMPTY::ee.scopes) ei v with gas_obs := tail)) /\
      gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
        (bind (read_result cx a) (\v. push_scope_with_var id tyv v))
        (ei,s,G,tn)
        (\H res eb Gf tnf z.
           res = INL () /\ eb.gas_obs = [] /\
           ?v k.
             eb =
             (\ee v.
                ee with
                scopes :=
                  fmupdate id
                    <|assignable := F; type := tyv; value := v; popped := []|>
                    FEMPTY::ee.scopes) (ei with gas_obs := []) v /\
             read_result cx a ei = (INL v,ei) /\
             (\H ei v k z Gf tnf.
                push_scope_with_var id tyv v ei =
                (INL (),
                 (\ee v.
                    ee with
                    scopes :=
                      fmupdate id
                        <|assignable := F; type := tyv; value := v;
                          popped := []|> FEMPTY::ee.scopes) ei v) /\
                expr_sim_inv bc cx (extend_local env id typ F)
                  ((\ee v.
                      ee with
                      scopes :=
                        fmupdate id
                          <|assignable := F; type := tyv; value := v;
                            popped := []|> FEMPTY::ee.scopes) ei v) /\
                ce_locals_declared bc (extend_local env id typ F) /\
                locals_alloc_ok bc (extend_local env id typ F) /\
                cenv_top_ext c0 bc
                  ((\ee v.
                      ee with
                      scopes :=
                        fmupdate id
                          <|assignable := F; type := tyv; value := v;
                            popped := []|> FEMPTY::ee.scopes) ei v).scopes /\
                stmt_state_rel H ctx func bc cx
                  ((\ee v.
                      ee with
                      scopes :=
                        fmupdate id
                          <|assignable := F; type := tyv; value := v;
                            popped := []|> FEMPTY::ee.scopes) ei v) z /\
                storage_well_formed_on cx
                  ((\ee v.
                      ee with
                      scopes :=
                        fmupdate id
                          <|assignable := F; type := tyv; value := v;
                            popped := []|> FEMPTY::ee.scopes) ei v) (FST H) /\
                ghost_inv_at (DF H) lo d bc cx
                  ((\ee v.
                      ee with
                      scopes :=
                        fmupdate id
                          <|assignable := F; type := tyv; value := v;
                            popped := []|> FEMPTY::ee.scopes) ei v) Gf tnf z /\
                ret_pc_ok bc sb0 z /\ return_buf_frame d bc sb0 z /\
                return_buf_sep d bc
                  (ei with scopes :=
                    fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
                      FEMPTY::ei.scopes) z /\
                (\c ee s G tn.
                   alloca_history func s /\
                   (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
                   s0.vs_alloca_next <= s.vs_alloca_next /\
                   (!x w.
                      not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
                      lookup_var x s = SOME w) /\
                   (!aid b.
                      FLOOKUP s0.vs_allocas aid = SOME b ==>
                      FLOOKUP s.vs_allocas aid = SOME b) /\
                   (!x. not_fresh_at sa0 x ==>
                        FLOOKUP G x = FLOOKUP G0 x /\
                        op_taint tn (Var x) = op_taint tn0 (Var x)) /\
                   alloca_frame c0 e0 sa0 s0 c ee s /\
                   !aid off sz i.
                     FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
                     aid < sa0.cs_next_id /\
                     (!name b sz'.
                        local_region c0 e0.scopes s0 name b sz' ==>
                        off + sz <= b \/ b + sz' <= off) /\ off <= i /\
                     i < off + sz /\ i IN tn.t_mem ==>
                     i IN tn0.t_mem) bc
                  ((\ee v.
                      ee with
                      scopes :=
                        fmupdate id
                          <|assignable := F; type := tyv; value := v;
                            popped := []|> FEMPTY::ee.scopes) ei v) z Gf tnf /\
                ~z.vs_halted /\ z.vs_current_bb = sb0.cs_current_bb /\
                z.vs_inst_idx = LENGTH sb0.cs_current_insts /\
                lookup_var idx z = SOME (n2w k) /\ FLOOKUP Gf idx = NONE /\
                op_taint tnf (Var idx) = {} /\ lookup_var p z = SOME dst /\
                eval_operand lvo z = SOME (n2w len) /\ op_prov Gf lvo = NONE /\
                op_taint tnf lvo = {} /\ allocas_from lo z /\
                FLOOKUP z.vs_allocas inst.inst_id = SOME (w2n dst,nb) /\
                ptr_covers Gf tnf p z nb /\
                !aid b.
                  FLOOKUP s0.vs_allocas aid = SOME b ==>
                  FLOOKUP z.vs_allocas aid = SOME b) H (ei with gas_obs := [])
               v k z Gf tnf /\ a::rs = DROP k vs /\
             body_stmts_full_ok cx body /\
             gas_admissible (eval_stmts cx body)
               (stmt_res_ok (InLoop exit incr)) eb)
        (\H res ee gt r.
           ?ex.
             res = INR ex /\
             (\H ex ee gt r.
                (!tail.
                   stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt
                     r) /\ halt_exit H cx ee (INR ex) r /\
                (ctx_has_dalloca ctx ==>
                 !s. r = Halt s \/ (?ir. r = IntRet ir s) ==>
                     allocas_below_fmp s)) H ex ee gt r)
Proof
 rpt gen_tac >>
  abbrev_lambda_tac "Fr" 5 0 `alloca_history func s /\ _` >>
  abbrev_lambda_tac "Inv" 6 2 `k <= len /\ _` >>
  abbrev_lambda_tac "R" 5 0 `(!tail. stmt_exit_ptr _ (ee with gas_obs := tail) (INR ex) gt r) /\ _` >>
  abbrev_lambda_tac "EB" 2 0 `ee with scopes := (FEMPTY |+ (id, _)) :: ee.scopes` >>
  abbrev_lambda_tac "Entry" 7 0 `push_scope_with_var id tyv v ei = _ /\ _` >>
  qpat_abbrev_tac `n = type_slot_size tyv` >>
  qpat_abbrev_tac `dyn = (case bd of Dynamic _ => T | Fixed _ => F)` >>
  qpat_abbrev_tac `outs = if dyn then [dv;ov;tot;ep] else [dv;ov;ep]` >>
 strip_tac >> map_every qx_gen_tac [`a`, `rs`, `ei`, `s`, `G`, `tn`] >>
 strip_tac >> rename1 `body_for_full_ok cx tyv id stmts vs` >>
 qabbrev_tac `H0 = storage_trace_horizon ei.storage_trace` >>
 `valid_horizon cx st0 H0 ei.storage_trace` by
   fs[Abbr `H0`, storage_trace_domain_def] >>
 qpat_assum `!H. valid_horizon _ _ _ _ ==> Inv _ _ _ _ _ _`
   (qspec_then `H0` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
 qpat_assum `Abbrev (Inv = _)`
   (fn th => CONV_TAC (LAND_CONV (REWRITE_CONV [REWRITE_RULE [markerTheory.Abbrev_def] th]))) >>
 BETA_TAC >> disch_then (qx_choose_then `k` (qx_choose_then `off` strip_assume_tac)) >>
 `DROP k vs = a::rs` by (qpat_assum `a::rs = DROP k vs` (ACCEPT_TAC o SYM)) >>
 drule_then strip_assume_tac DROP_EQ_CONS >>
 `k < len` by (metis_tac[]) >>
 qpat_x_assum `len = LENGTH vs` kall_tac >>
 qpat_x_assum `DROP k vs = a::rs` kall_tac >>
 qabbrev_tac `addr = (if dyn then slot+1w else slot) + n2w(k*n)` >>
 `a = PlaceR (StoragePlace tr addr tyv)` by suspend "child" >>
 `!H. valid_horizon cx st0 H ei.storage_trace ==>
     storage_place_observed H (StoragePlace tr addr tyv)` by suspend "observed" >>
 `storage_holds cx tr typ a addr ei s` by suspend "holds" >>
 `?v. read_result cx a ei = (INL v,ei) /\ value_has_type tyv v /\ val_wf tyv v /\
    (!tail. read_result cx a (ei with gas_obs:=tail) = (INL v,ei with gas_obs:=tail)) /\
    (!tail. (do w <- read_result cx a; push_scope_with_var id tyv w od)
       (ei with gas_obs:=tail) = (INL (),EB ei v with gas_obs:=tail))` by suspend "read" >>
 rename1 `read_result cx a ei = (INL v,ei)` >>
 conj_tac >- (qexists_tac `v` >> first_assum ACCEPT_TAC) >>
 `body_stmts_full_ok cx stmts` by suspend "activate" >>
 `gas_admissible (eval_stmts cx stmts) (stmt_res_ok (InLoop exit incr))
    (EB (ei with gas_obs:=[]) v)` by suspend "body_gas" >>
 suspend "execute"
QED

Resume for_storage_array_head_full[child]:
 qpat_assum `EL k vs = a` mp_tac >>
 simp[Abbr `addr`, Abbr `dyn`, Abbr `n`, EL_GENLIST] >>
 Cases_on `bd` >> simp[]
  >> (gvs[])
QED

Resume for_storage_array_head_full[observed]:
 qx_gen_tac `H` >> strip_tac >>
 qabbrev_tac `delta = (if dyn then 1 else 0) + k*n` >>
 `k < bound_length bd` by decide_tac >>
 `storage_subregion (ArrayTV tyv bd) [ValueSubscript (IntV (&k))] delta tyv` by
   (Cases_on `bd` >>
    qpat_assum `k < bound_length _`
      (assume_tac o REWRITE_RULE [bound_length_def]) >>
    simp[Abbr `delta`, Abbr `dyn`, Abbr `n`, storage_subregion_def]) >>
 `addr = n2w off + n2w delta` by
   (Cases_on `dyn` >>
    simp[Abbr `addr`, Abbr `delta`, GSYM word_add_n2w, WORD_ADD_ASSOC, WORD_ADD_0]) >>
 drule_all aug_place_storage_rooted_observed >> simp[]
QED

Resume for_storage_array_head_full[holds]:
 `regions_consistent (FST H0)` by
   (qpat_assum `valid_horizon cx st0 H0 _`
      (strip_assume_tac o REWRITE_RULE [valid_horizon_def]) >> first_assum ACCEPT_TAC) >>
 qpat_assum `!H. valid_horizon _ _ _ _ ==> storage_place_observed _ _`
   (qspec_then `H0` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
 disch_tac >>
 `0 < type_slot_size tyv` by
   (qpat_assum `Abbrev (n = type_slot_size tyv)`
      (SUBST1_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >> first_assum ACCEPT_TAC) >>
 drule_all for_storage_current_child_holds >> simp[]
QED

Resume for_storage_array_head_full[read]:
 qpat_assum `a = PlaceR _` SUBST_ALL_TAC >>
 drule_all (BETA_RULE (REWRITE_RULE [LET_THM] for_storage_current_read_push)) >>
 disch_then (qspec_then `id` (qx_choose_then `v` strip_assume_tac)) >>
 qexists_tac `v` >> simp[Abbr `EB`]
QED

Resume for_storage_array_head_full[activate]:
 reverse (Cases_on `k = 0`)
 >- (qpat_assum `k <> 0 ==> _` irule >> first_assum ACCEPT_TAC) >>
 `a::rs = vs` by
   (qpat_assum `a::rs = DROP k vs` mp_tac >>
    qpat_assum `k = 0` SUBST1_TAC >> rewrite_tac [DROP_0]) >>
 qpat_assum `body_for_full_ok _ _ _ _ _`
   (MATCH_MP_TAC o REWRITE_RULE [body_for_full_ok_def]) >>
 qpat_assum `a::rs = vs` (SUBST1_TAC o SYM) >>
 qexistsl [`ei`,`v`,`ei`] >> rewrite_tac [NOT_CONS_NIL, HD] >>
 first_assum ACCEPT_TAC
QED

Resume for_storage_array_head_full[body_gas]:
 rewrite_tac [gasContextTheory.gas_admissible_def] >>
 map_every qx_gen_tac [`gs`, `res`, `ef`] >>
 `EB (ei with gas_obs := []) v with gas_obs := gs = EB (ei with gas_obs := gs) v`
   by simp[Abbr `EB`] >>
 qpat_assum `EB _ _ with gas_obs := gs = _` SUBST1_TAC >> disch_tac >>
 `eval_for cx tyv id stmts (a::rs) (ei with gas_obs := gs) =
  eval_for cx tyv id stmts (Value v::rs) (ei with gas_obs := gs)` by
   (`read_result cx (Value v) (ei with gas_obs := gs) =
       (INL v,ei with gas_obs := gs)` by simp[vyperStateTheory.read_result_def,
                                             vyperStateTheory.return_def] >>
    qpat_assum `!tail. read_result cx a _ = _`
      (qspec_then `gs` (mp_then Any (rewrite_tac o single)
        vyperInterpreterTheory.eval_for_cons_read)) >>
    qpat_assum `read_result cx (Value v) _ = _`
      (mp_then Any (rewrite_tac o single) vyperInterpreterTheory.eval_for_cons_read)) >>
 Cases_on `eval_for cx tyv id stmts (Value v::rs) (ei with gas_obs := gs)` >>
 rename1 `_ = (lr,le)` >>
 `stmt_res_ok lctx lr` by
   (qpat_assum `gas_admissible _ _ _`
      (qspecl_then [`gs`,`lr`,`le`] MATCH_MP_TAC o
       REWRITE_RULE [gasContextTheory.gas_admissible_def]) >>
    first_assum ACCEPT_TAC) >>
 qpat_assum `eval_stmts cx stmts (EB _ _) = (res,ef)`
   (assume_tac o SIMP_RULE (srw_ss()) [Abbr `EB`]) >>
 drule stmtSimForPartsTheory.eval_for_cons_cases >> simp[] >>
 strip_tac
 >- simp[stmt_res_ok_def]
 >- simp[stmt_res_ok_def]
 >- (qpat_assum `res = INR BreakException` SUBST1_TAC >> simp[stmt_res_ok_def]) >>
 qpat_assum `lr = res` (SUBST1_TAC o SYM) >>
 qpat_assum `stmt_res_ok lctx lr` mp_tac >>
 simp[NoAsms, stmt_res_ok_def] >>
 POP_ASSUM_LIST (K (rpt strip_tac >> simp[]))
QED

Resume for_storage_array_head_full[execute]:
 `allocas_from lo s` by
   ((qpat_assum `ghost_inv_at (DF H0) lo d c0 cx ei G tn s` mp_tac >>
    simp[ghost_inv_at_def] >> (gvs[ghost_inv_at_def]))) >>
 `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by
   (qpat_assum `Abbrev (Fr = _)` (fn th =>
      qpat_assum `Fr c0 ei s G tn`
        (strip_assume_tac o BETA_RULE o
         PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] th])) >>
    first_assum ACCEPT_TAC) >>
 qpat_assum `Abbrev (dyn = _)`
   (fn th => qpat_assum `sa.cs_current_insts = _`
      (assume_tac o REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] th])) >>
 qpat_assum `Abbrev (outs = _)`
   (fn th => map_every (fn q => qpat_assum q (assume_tac o REWRITE_RULE
      [REWRITE_RULE [markerTheory.Abbrev_def] th]))
      [`ALL_DISTINCT outs`, `~MEM idx outs`, `~MEM p outs`,
       `!x. lvo = Var x ==> ~MEM x outs`]) >>
 qpat_assum `Abbrev (dyn = _)`
   (fn th => map_every (fn q => qpat_assum q (assume_tac o REWRITE_RULE
      [REWRITE_RULE [markerTheory.Abbrev_def] th]))
      [`ALL_DISTINCT (if _ then _ else _)`, `~MEM idx (if _ then _ else _)`,
       `~MEM p (if _ then _ else _)`, `!x. lvo = Var x ==> ~MEM x (if _ then _ else _)`]) >>
 drule_all (BETA_RULE (REWRITE_RULE [LET_THM] for_storage_array_head_prefix)) >>
 disch_then (qspec_then `PG`
   (qx_choose_then `u` (qx_choose_then `Gu` (qx_choose_then `tnu` strip_assume_tac)))) >>
 `!j. j < LENGTH sa.cs_current_insts ==>
     ?i. get_instruction bb j = SOME i /\ i.inst_opcode <> ALLOCA`
   by suspend "scalar_code" >>
 `!H. valid_horizon cx st0 H ei.storage_trace ==>
     stmt_state_rel H ctx func c0 cx ei u /\
     storage_well_formed_on cx ei (FST H) /\
     ghost_inv_at (DF H) lo d c0 cx ei Gu tnu u /\ Fr c0 ei u Gu tnu /\
     return_buf_frame d c0 sa0 u /\ ret_pc_ok c0 sa0 u /\
     return_buf_sep d c0 ei u /\
     lookup_var idx u = SOME (n2w k) /\ FLOOKUP Gu idx = NONE /\
     op_taint tnu (Var idx) = {} /\ eval_operand lvo u = SOME (n2w len) /\
     op_prov Gu lvo = NONE /\ op_taint tnu lvo = {} /\
     lookup_var p u = SOME dst /\ ptr_covers Gu tnu p u nb /\
     eval_operand (Var ep) u = SOME addr /\
     u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
     (!name b sz. local_region c0 ei.scopes u name b sz <=>
                  local_region c0 ei.scopes s name b sz)` by suspend "prefix_frame" >>
 qpat_assum `!H. valid_horizon _ _ _ _ ==> stmt_state_rel _ _ _ _ _ _ u /\ _`
   (qspec_then `H0` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
 disch_then strip_assume_tac >>
 `32*n <= nb` by simp[Abbr `n`] >>
 `ptr_covers Gu tnu p u (32*n)` by
   (irule reasonCopySourcePtrTheory.ptr_covers_mono >> qexists `nb` >> simp[]) >>
 `n < 2**256 /\ w2n dst+32*n < 2**256 /\
  w2n dst+32*n <= u.vs_alloca_next` by decide_tac >>
 `slot_copy_external sa (Var p)` by (irule slot_copy_not_fresh_external >> simp[]) >>
 `allocas_from lo u` by
   (qpat_assum `ghost_inv_at (DF H0) lo d c0 cx ei Gu tnu u` mp_tac >>
    simp[ghost_inv_at_def]) >>
 `(ctx_has_dalloca ctx ==> allocas_below_fmp u)` by
   (qpat_assum `Abbrev (Fr = _)` (fn th =>
      qpat_assum `Fr c0 ei u Gu tnu`
        (strip_assume_tac o BETA_RULE o
         PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] th])) >>
    first_assum ACCEPT_TAC) >>
 `create_memory_snapshot [] u` by simp[createSourceCallbackTheory.create_memory_snapshot_def] >>
 drule_at (Pat `compile_expr _ _ _ _ = _`) for_storage_element_copy_run >>
 disch_then (drule_at (Pat `compile_iter_elem_copy _ _ _ _ _ _ _ _ _ = _`)) >>
 disch_then (drule_at (Pat `eval_operand (Var ep) _ = SOME _`)) >>
 disch_then (qspecl_then [`lo`, `ctx`, `func`, `PG`, `Gu`, `tnu`, `dst`, `[]`] mp_tac) >>
 (impl_tac >- simp[]) >>
 disch_then (qx_choose_then `z` (qx_choose_then `Gf` (qx_choose_then `tnf` strip_assume_tac))) >>
 `!mem. mem_agree_outside tnf.t_mem z.vs_memory mem ==>
        val_in_memory tyv v (w2n dst) mem` by suspend "copy_value" >>
 `lookup_var idx z = SOME (n2w k) /\ FLOOKUP Gf idx = NONE /\
    op_taint tnf (Var idx) = {} /\ eval_operand lvo z = SOME (n2w len) /\
    op_prov Gf lvo = NONE /\ op_taint tnf lvo = {}` by suspend "copy_scalars" >>
 `z.vs_allocas = u.vs_allocas` by
   (qpat_assum `slot_copy_runtime_frame sa dst n u z`
      (strip_assume_tac o REWRITE_RULE [slot_copy_runtime_frame_def]) >>
    first_assum ACCEPT_TAC) >>
 `z.vs_immutables = u.vs_immutables` by
   (qpat_assum `slot_copy_runtime_frame sa dst n u z`
      (strip_assume_tac o REWRITE_RULE [slot_copy_runtime_frame_def]) >>
    qpat_assum `copy_static z = copy_static u`
      (ACCEPT_TAC o SIMP_RULE (srw_ss()) [copy_static_def] o
       AP_TERM ``\r:venom_state. r.vs_immutables``)) >>
 `alloca_history func z` by
   (irule alloca_history_jump >> metis_tac[]) >>
 `!H. valid_horizon cx st0 H ei.storage_trace ==>
      Entry H (ei with gas_obs := []) v k z Gf tnf` by suspend "register" >>
 suspend "finish"
QED

Resume for_storage_array_head_full[copy_value]:
 qpat_assum `!H. valid_horizon _ _ _ _ ==> storage_place_observed _ _`
   (qspec_then `H0` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
 disch_tac >>
 `regions_consistent (FST H0)` by
   (qpat_assum `valid_horizon cx st0 H0 _`
      (strip_assume_tac o REWRITE_RULE [valid_horizon_def]) >> first_assum ACCEPT_TAC) >>
 `0 < type_slot_size tyv` by simp[Abbr `n`] >>
 `storage_holds cx tr typ (PlaceR (StoragePlace tr addr tyv)) addr ei u` by
   (qpat_assum `a = PlaceR _` SUBST_ALL_TAC >>
    irule for_storage_observed_child_holds >>
    (metisTools.METIS_TAC [])) >>
 `ptr_vv_ok cx typ (PlaceR (StoragePlace tr addr tyv))
     (LocatedValue typ (mk_ptr (Var ep) (slot_loc tr))) ei Gu tnu u` by
   (qpat_assum `stmt_state_rel H0 ctx func c0 cx ei u`
      (mp_then Any (fn th =>
         qpat_assum `ghost_inv_at (DF H0) lo d c0 cx ei Gu tnu u`
           (mp_then (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`) irule th))
        for_storage_current_child_ptr) >>
    qpat_x_assum `u = _` kall_tac >>
    qpat_x_assum `tnu = _` kall_tac >>
    qpat_assum `!H. dead_lo_ok H (DF H) lo c0 cx` (qspec_then `H0` assume_tac) >>
    simp[mk_ptr_def]) >>
 drule_then assume_tac copy_prefix_words >> drule_then assume_tac copy_prefix_taint >>
 `?vv. read_result cx (PlaceR (StoragePlace tr addr tyv)) ei = (INL vv,ei) /\
   !mem. mem_agree_outside tnf.t_mem z.vs_memory mem ==>
         val_in_memory tyv vv (w2n dst) mem` by
   (((irule unwrap_storage_copied_robust >>
    goal_assum (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
    qexistsl [`tr`,`addr`] >>
    qpat_x_assum `u = _` kall_tac >> qpat_x_assum `tnu = _` kall_tac >>
    Cases_on `tr` >> fs[Abbr `n`,mk_ptr_def] >>> NTH_GOAL (metis_tac[]) 1 >> (metis_tac[Abbr `n`, mk_ptr_def, unwrap_storage_copied_robust])))) >>
 `v = vv` by
   (qpat_assum `a = PlaceR _` SUBST_ALL_TAC >>
    qpat_assum `read_result cx _ ei = (INL vv,ei)` mp_tac >>
    qpat_assum `read_result cx _ ei = (INL v,ei)` (rewrite_tac o single) >>
    simp[NoAsms]) >>
 qpat_assum `v = vv` SUBST1_TAC >> first_assum ACCEPT_TAC
QED

Resume for_storage_array_head_full[scalar_code]:
 gen_tac >> disch_tac >> qexists_tac `EL j sa.cs_current_insts` >>
 conj_tac >- (first_x_assum irule >> first_assum ACCEPT_TAC) >>
 qpat_assum `sa.cs_current_insts = [_] ++ (if dyn then _ else _) ++ [_]`
   SUBST_ALL_TAC >>
 Cases_on `bd` >> fs[Abbr `dyn`]
 >- (`j = 0 \/ j = 1` by decide_tac >>
     qpat_assum `j = _` SUBST1_TAC >> simp[NoAsms, EL, mk_inst_def]) >>
 `j = 0 \/ j = 1 \/ j = 2` by decide_tac >>
 qpat_assum `j = _` SUBST1_TAC >> simp[NoAsms, EL, mk_inst_def]
QED

Resume for_storage_array_head_full[prefix_frame]:
 qx_gen_tac `H` >> strip_tac >>
 qpat_assum `Abbrev (Inv = _)` (fn inv =>
   qpat_assum `!H. valid_horizon _ _ _ _ ==> Inv _ _ _ _ _ _`
     (qspec_then `H` (mp_tac o BETA_RULE o
       PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] inv]))) >>
 (impl_tac >- first_assum ACCEPT_TAC) >> disch_then strip_assume_tac >>
 qpat_assum `Abbrev (Fr = _)` (fn th =>
   qpat_assum `Fr c0 ei s G tn`
     (strip_assume_tac o BETA_RULE o
      PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] th])) >>
 `!x. MEM x (if (case bd of Dynamic _ => T | Fixed _ => F)
             then [dv;ov;tot;ep] else [dv;ov;ep]) ==> ~not_fresh_at sa0 x` by
   (qpat_assum `!x. MEM x outs ==> _` mp_tac >> simp[Abbr `outs`, Abbr `dyn`]) >>
 qpat_assum `stmt_state_rel H ctx func c0 cx ei s`
   (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) mp_tac
     (BETA_RULE (REWRITE_RULE [LET_THM] for_storage_array_head_prefix_transport))) >>
 disch_then (fn th => qpat_assum `ghost_inv_at (DF H) lo d c0 cx ei G tn s`
   (mp_then (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`) mp_tac th)) >>
 disch_then (drule_at (Pat `_ = (update_var _ _ _) with vs_inst_idx := _`)) >>
 disch_then (drule_at (Pat `_ = DRESTRICT _ _`)) >>
 disch_then (drule_at (Pat `_ = _ with t_var := FOLDL _ _ _`)) >>
 disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
 disch_then (drule_at (Pat `lookup_block _ _ = SOME _`)) >>
 disch_then (drule_at (Pat `eval_operand _ _ = SOME (n2w _)`)) >>
 disch_then (drule_at (Pat `lookup_var _ _ = SOME (n2w _)`)) >>
 disch_then (drule_at (Pat `return_buf_frame _ _ _ _`) o
   CONV_RULE (DEPTH_CONV BETA_CONV)) >>
 disch_then (drule_at (Pat `alloca_frame _ _ _ _ _ _ _`)) >>
 disch_then (fn th => qpat_assum `lookup_var p s = SOME dst`
   (mp_then (Pat `lookup_var _ _ = SOME _`) mp_tac th)) >>
 disch_then (qspecl_then [`G0`,`tn0`] mp_tac) >>
 (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
 disch_then strip_assume_tac >>
 `return_buf_sep d c0 ei u` by
   (irule return_buf_sep_transport >>
    conj_tac
    >- (map_every qx_gen_tac [`bw`,`cap`] >> disch_tac >>
        qpat_assum `d = SOME (bw,cap)` SUBST_ALL_TAC >>
        qpat_assum `return_buf_sep (SOME (bw,cap)) c0 ei s`
          (assume_tac o CONJUNCT1 o REWRITE_RULE [return_buf_sep_def]) >>
        qpat_assum `allocas_from (w2n bw + cap) s` mp_tac >>
        rewrite_tac[allocas_from_def] >>
        qpat_assum `u.vs_allocas = s.vs_allocas` SUBST1_TAC >> simp[NoAsms]) >>
    qexistsl_tac [`c0`, `ei`, `s`] >>
    reverse conj_tac >- first_assum ACCEPT_TAC >>
    qpat_assum `!name b sz. local_region c0 ei.scopes u name b sz <=> _`
      (rewrite_tac o single)) >>
 qpat_assum `Abbrev (Fr = _)` (fn f =>
   qpat_assum `Abbrev (addr = _)` (fn a =>
     qpat_assum `Abbrev (dyn = _)` (fn b =>
       pure_rewrite_tac (map (REWRITE_RULE [markerTheory.Abbrev_def]) [f,a,b])))) >>
 BETA_TAC >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume for_storage_array_head_full[copy_scalars]:
 `slot_copy_external sa (Var idx) /\ slot_copy_external sa lvo` by
   (conj_tac >- (irule slot_copy_not_fresh_external >> first_assum ACCEPT_TAC) >>
    Cases_on `lvo`
    >- simp[NoAsms, slot_copy_external_def]
    >- (rename1 `slot_copy_external sa (Var x)` >>
        irule slot_copy_not_fresh_external >>
        qpat_assum `!y. Var x = Var y ==> not_fresh_at sa y`
          (qspec_then `x` mp_tac) >> simp[NoAsms]) >>
    rename1 `slot_copy_external sa (Label lab)` >>
    qpat_assum `!lbl. Label lab <> Label lbl` (qspec_then `lab` mp_tac) >>
    simp[NoAsms]) >>
 qpat_assum `slot_copy_runtime_frame sa dst n u z`
   (strip_assume_tac o REWRITE_RULE [slot_copy_runtime_frame_def]) >>
 qpat_assum `slot_copy_ghost_inv sa _ addr dst p n Gu tnu n Gf tnf z`
   (strip_assume_tac o REWRITE_RULE [slot_copy_ghost_inv_def]) >>
 `lookup_var idx z = lookup_var idx u /\ eval_operand lvo z = eval_operand lvo u` by
   (qpat_assum `!op. slot_copy_external sa op ==> eval_operand op z = eval_operand op u`
      (fn th => map_every (fn q => qspec_then q mp_tac th >>
         (impl_tac >- first_assum ACCEPT_TAC)) [`Var idx`,`lvo`]) >>
    simp[NoAsms, eval_operand_def]) >>
 qpat_assum `!x. slot_copy_external sa (Var x) ==> FLOOKUP Gf x = _ /\ _`
   (qspec_then `idx` mp_tac) >>
 (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
 ntac 4 (conj_tac >-
   (qpat_assum `lookup_var idx z = lookup_var idx u` (rewrite_tac o single) >>
    qpat_assum `FLOOKUP Gf idx = FLOOKUP Gu idx` (rewrite_tac o single) >>
    qpat_assum `op_taint tnf (Var idx) = op_taint tnu (Var idx)` (rewrite_tac o single) >>
    qpat_assum `eval_operand lvo z = eval_operand lvo u` (rewrite_tac o single) >>
    first_assum ACCEPT_TAC)) >>
 Cases_on `lvo`
 >- simp[NoAsms, op_prov_def, op_taint_def]
 >- (rename1 `op_prov Gf (Var x) = NONE` >>
     qpat_assum `!y. slot_copy_external sa (Var y) ==> FLOOKUP Gf y = _ /\ _`
       (qspec_then `x` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     simp[NoAsms, op_prov_def] >>
     qpat_assum `FLOOKUP Gf x = FLOOKUP Gu x` (rewrite_tac o single) >>
     qpat_assum `op_taint tnf (Var x) = op_taint tnu (Var x)` (rewrite_tac o single) >>
     conj_tac >- (qpat_assum `op_prov Gu (Var x) = NONE`
                    (ACCEPT_TAC o SIMP_RULE (srw_ss()) [op_prov_def])) >>
     first_assum ACCEPT_TAC) >>
 simp[NoAsms, op_prov_def, op_taint_def]
QED

Resume for_storage_array_head_full[register]:
 qx_gen_tac `H` >> strip_tac >>
 qpat_assum `!H. valid_horizon _ _ _ _ ==> stmt_state_rel _ _ _ _ _ _ u /\ _`
   (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
 disch_then strip_assume_tac >>
 `allocas_non_overlapping u` by
   (qpat_assum `stmt_state_rel H ctx func c0 cx ei u`
     (mp_then Any mp_tac bodyMemBopRestWordPathTheory.rest_word_state_alloca_inv) >>
    simp[venomMemDefsTheory.alloca_inv_def]) >>
 `!name b sz. local_region c0 ei.scopes u name b sz ==>
    w2n dst+nb <= b \/ b+sz <= w2n dst` by
   (qpat_assum `!name b sz. local_region c0 ei.scopes u name b sz <=> _`
     (rewrite_tac o single) >> first_assum ACCEPT_TAC) >>
 qmatch_goalsub_abbrev_tac `Entry H er v k z Gf tnf` >>
 `return_buf_sep d c0 er u` by simp[Abbr `er`, return_buf_sep_gas_obs] >>
 `stmt_state_rel H ctx func c0 cx er u` by
   (simp[Abbr `er`,stmt_state_rel_start_gas_obs] >> first_assum ACCEPT_TAC) >>
 `ghost_inv_at (DF H) lo d c0 cx er Gu tnu u` by
   ((qpat_assum `ghost_inv_at (DF H) lo d c0 cx ei Gu tnu u` mp_tac >>
    simp[NoAsms,Abbr `er`,ghost_inv_at_def] >> (metis_tac[NoAsms, Abbr `er`, ghost_inv_at_def]))) >>
 `expr_sim_inv c0 cx env er` by simp[Abbr `er`] >>
 `storage_well_formed_on cx er (FST H)` by
   (qpat_assum `storage_well_formed_on cx ei (FST H)` mp_tac >>
    simp[NoAsms, Abbr `er`, vyperStorageFootprintTheory.storage_well_formed_on_def,
         stmtSimAppendStorageComposeTheory.get_storage_gas_obs]) >>
 `Fr c0 er u Gu tnu` by
   ((qpat_assum `Fr c0 ei u Gu tnu` mp_tac >>
    qpat_assum `Abbrev (er = _)`
      (rewrite_tac o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
    simp[NoAsms, Abbr `Fr`, alloca_frame_gas_obs] >> (metis_tac[NoAsms, Abbr `Fr`, alloca_frame_gas_obs]))) >>
 `lookup_scopes id er.scopes = NONE` by simp[Abbr `er`] >>
 `not_local_ptr bc (FEMPTY::er.scopes) p` by
   (qpat_assum `!scs. lookup_scopes id scs = NONE ==> _`
     (qspec_then `er.scopes` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC) >>
 `!name b sz. local_region c0 er.scopes u name b sz ==>
    w2n dst+nb <= b \/ b+sz <= w2n dst` by
   (qpat_assum `!name b sz. local_region c0 ei.scopes u name b sz ==> _`
     mp_tac >> simp[NoAsms, Abbr `er`]) >>
 `(!x cap. c0.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. c0.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x)` by
   (conj_tac >> map_every qx_gen_tac [`x`,`cap`] >> disch_tac >>
    qpat_assum `!x. not_fresh_at sa0 x ==> not_fresh_at sa x` irule
    >- (qpat_assum `!x cap. c0.ce_return_buf = _ ==> not_fresh_at sa0 x`
          (qspecl_then [`x`,`cap`] mp_tac) >> simp[])
    >> qpat_assum `!x cap. c0.ce_return_pc = _ ==> not_fresh_at sa0 x`
         (qspecl_then [`x`,`cap`] mp_tac) >> simp[]) >>
 `FLOOKUP u.vs_allocas inst.inst_id = SOME (w2n dst,nb)` by
   (qpat_assum `u.vs_allocas = s.vs_allocas` (rewrite_tac o single) >>
    qpat_assum `inst.inst_id = sd.cs_next_id` (rewrite_tac o single) >>
    first_assum ACCEPT_TAC) >>
 `lo <= w2n dst` by
   (qpat_assum `allocas_from lo u` (mp_tac o REWRITE_RULE [allocas_from_def]) >>
    disch_then (qspecl_then [`inst.inst_id`,`w2n dst`,`nb`] mp_tac) >> simp[]) >>
 qpat_assum `Abbrev (Fr = _)` (fn fr =>
   mp_tac (BETA_RULE (REWRITE_RULE [LET_THM]
     (PURE_REWRITE_RULE [SYM (REWRITE_RULE [markerTheory.Abbrev_def] fr)]
       (Q.INST [`D` |-> `DF H`, `ei` |-> `er`, `src` |-> `addr`,
                `load` |-> `if tr then TLOAD else SLOAD`]
         (SPEC_ALL (Q.ISPEC `H : (bool # 256 word # type_value) list # num list`
                      for_storage_copy_body_entry))))))) >>
 (impl_tac >- (simp[Abbr `n`] >>
   qpat_assum `!name b sz. local_region c0 er.scopes u name b sz ==> _` mp_tac >>
   simp[Q.SPECL [`w2n (dst:256 word)`,`nb`] arithmeticTheory.ADD_COMM])) >>
 qpat_assum `Abbrev (Entry = _)` (rewrite_tac o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
 qpat_assum `Abbrev (EB = _)` (rewrite_tac o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
 BETA_TAC >> disch_then ACCEPT_TAC
QED

Resume for_storage_array_head_full[finish]:
 irule gas_outcome_full_pure >>
 reverse conj_tac >- first_assum ACCEPT_TAC >>
 qexistsl [`Gf`,`EB ei v`,`INL ()`,`z`,`tnf`] >>
 conj_tac >- first_assum ACCEPT_TAC >>
 qx_gen_tac `H` >>
 `((EB ei v).storage_trace = ei.storage_trace) /\
  (EB ei v with gas_obs := [] = EB (ei with gas_obs := []) v) /\
  (EB (ei with gas_obs := []) v).gas_obs = []` by simp[Abbr `EB`] >>
 simp[] >> strip_tac >> conj_tac
 >- (qpat_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) [] _`
       (qspecl_then [`DF H`,`explicit`] (mp_then Any mp_tac gas_origin_ptr_path_append)) >>
     disch_then (qspecl_then [`u`,`Gu`,`tnu`,`[]`,`OK z`,`Gf`,`tnf`] mp_tac) >> simp[]) >>
 qexists_tac `k` >> simp[]
QED

Finalise for_storage_array_head_full

(* Compose the read/copy entry, cleaned body, and continuing backedge. *)
Theorem for_storage_array_round_full:
  !(DF :(bool # 256 word # type_value) list # num list -> dead) (lo :num)
      (d :(256 word # num) option) (ctx :venom_context)
      (shadow_ctx :venom_context) (func :ir_function)
      (shadow_func :ir_function) (PG :(num # num) option list)
      (cx :evaluation_context)
      (RetQ :(bool # 256 word # type_value) list # num list ->
             value ->
             evaluation_state ->
             (string |-> num # num) # taint -> exec_result -> bool)
      (c0 :compile_env) (e0 :evaluation_state) (sa0 :compile_state)
      (sb :compile_state) (s0 :venom_state) (G0 :string |-> num # num)
      (tn0 :taint) (tr :bool) (slot :256 word) (dst :256 word)
      (tyv :type_value) (typ :type) (bd :bound) (vs :eval_result list)
      (len :num) (nb :num) (id :string) (env :typing_env) (p :string)
      (idx :string) (cond :string) (lvo :operand) (sd :compile_state)
      (body :stmt list) (si :compile_state) (lctx :loop_ctx) (bc :compile_env)
      (bc1 :compile_env) (sb0 :compile_state) (sb1 :compile_state)
      (sj :compile_state) (sj' :compile_state) (sk :compile_state)
      (sl :compile_state) (out :string) (tops :toplevel list)
      (bindings :(string # type) list) (ret_ty :type) (env_b :typing_env)
      (st0 :evaluation_state) (ok :unit + vyperState$exception -> bool)
      (exit :string) (incr :string) (shadow_sb0 :compile_state)
      (shadow_sb1 :compile_state).
    body_inv tops ctx bc cx /\ shadow_body_inv tops ctx shadow_ctx /\ supported_stmts tops bindings body /\
    (!(target :type).
       supported_stmts_expr_exists (expr_abi_decode_target_root target) body ==>
       occurs_abi_decode_target target tops) /\
    type_stmts (extend_local env id typ F) ret_ty body = SOME env_b /\
    stmts_exprs_ok bc body /\ call_evaluation_safe cx (int_calls_stmts body) /\
    frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ bc
      ret_ty /\ stmts_env bc (InLoop exit incr) ret_ty body sb0 = (bc1,sb1) /\
    stmts_env bc (InLoop exit incr) ret_ty (MAP gas_shadow_stmt body)
      shadow_sb0 = (bc1,shadow_sb1) /\ gas_shadow_state sb0 shadow_sb0 /\
    gas_shadow_state sb1 shadow_sb1 /\ gas_shadow_context ctx shadow_ctx /\
    ctx_inst_ids_distinct ctx /\ gas_shadow_function func shadow_func /\
    MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sb0 sb1 func /\
    fn_has_code shadow_sb0 shadow_sb1 shadow_func /\
    (!(H :(bool # 256 word # type_value) list # num list).
       dead_lo_ok H (DF H) lo bc cx) /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved bc sb0 /\
    (!(x :string) (sz :num).
       bc.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb0 x) /\
    ~block_is_terminated sb0 /\ not_fresh_at sb0 idx /\ not_fresh_at sb0 p /\
    (!(x :string). lvo = Var x ==> not_fresh_at sb0 x) /\
    (!(lbl :string). lvo <> Label lbl) /\ supported_program tops /\
    get_module_code cx (NONE :num option) = SOME tops /\
    id NOTIN FDOM env.var_types /\ same_frame c0 bc /\
    local_ptrs_reserved c0 sb0 /\ sa0.cs_next_id <= sb0.cs_next_id /\
    (!(x :string). not_fresh_at sa0 x ==> not_fresh_at sb0 x) /\
    (!(x :string) (sz :num).
       c0.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x) /\
    emit_jmp_if_not_terminated incr sb1 = ((),sj) /\ fn_has_code sb1 sj func /\
    si.cs_current_bb = incr /\ si.cs_current_insts = ([] :instruction list) /\
    sb.cs_current_bb = exit /\ sb.cs_current_insts = ([] :instruction list) /\
    ~block_is_terminated sb /\
    emit_op ADD [Var idx; Lit (1w :256 word)] si = (Var out,sj') /\
    emit_inst ASSIGN [Var out] [idx] sj' = ((),sk) /\
    emit_inst JMP [Label cond] ([] :string list) sk = ((),sl) /\
    fn_has_code si sl func /\ not_fresh_at si idx /\ len < dimword (:256) /\
    local_ptrs_reserved c0 sa0 /\ ~not_fresh_at sa0 idx /\
    ~not_fresh_at sa0 out /\
    (!(x :string) (sz :num).
       c0.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
    (!(x :string) (sz :num).
       c0.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
    p <> idx /\ p <> out /\
    (!(x :string). lvo = Var x ==> x <> idx /\ x <> out) /\
    (!(res :unit + vyperState$exception). ok res ==> stmt_res_ok lctx res) /\
    (!(a :eval_result) (rs :eval_result list) (ei :evaluation_state)
         (s :venom_state) (G :string |-> num # num) (tn :taint).
       ~s.vs_halted /\ storage_trace_domain cx st0 ei.storage_trace /\
       (!(H :(bool # 256 word # type_value) list # num list).
          valid_horizon cx st0 H ei.storage_trace ==>
          (\(H :(bool # 256 word # type_value) list # num list)
             (rs :eval_result list) (ee :evaluation_state)
             (G :string |-> num # num) (tn :taint) (s :venom_state).
             ?(k :num) (off :num).
               k <= len /\ len = LENGTH vs /\ len <= bound_length bd /\
               vs =
               GENLIST
                 (\(j :num).
                    PlaceR
                      (StoragePlace tr
                         ((case bd of
                             (Fixed v :bound) => slot
                           | Dynamic v1 => slot + (1w :256 word)) +
                          (n2w (j * type_slot_size tyv) :256 word)) tyv)) len /\
               rs = DROP k vs /\ slot = (n2w off :256 word) /\
               MEM (StorageRoot tr off (ArrayTV tyv bd)) ee.storage_trace /\
               evaluate_type (get_tenv cx) typ = SOME tyv /\
               well_formed_type_value tyv /\ s.vs_current_bb = cond /\
               s.vs_inst_idx = (0 :num) /\ ~s.vs_halted /\
               lookup_var idx s = SOME (n2w k :256 word) /\
               FLOOKUP G idx = (NONE :(num # num) option) /\
               op_taint tn (Var idx) = ({} :num -> bool) /\
               eval_operand lvo s = SOME (n2w len :256 word) /\
               op_taint tn lvo = ({} :num -> bool) /\
               op_prov G lvo = (NONE :(num # num) option) /\
               eval_operand (Lit slot) s = SOME slot /\
               op_taint tn (Lit slot) = ({} :num -> bool) /\
               lookup_var p s = SOME dst /\
               FLOOKUP s.vs_allocas sd.cs_next_id = SOME (w2n dst,nb) /\
               ptr_covers G tn p s nb /\
               (32 :num) * type_slot_size tyv <= nb /\
               w2n dst + nb < (2 :num) ** (256 :num) /\
               w2n dst + nb <= s.vs_alloca_next /\
               (!(name :string) (b :num) (sz :num).
                  local_region c0 ee.scopes s name b sz ==>
                  w2n dst + nb <= b \/ b + sz <= w2n dst) /\
               lookup_scopes id ee.scopes = (NONE :scope_entry option) /\
               expr_sim_inv c0 cx env ee /\ ce_locals_declared c0 env /\
               locals_alloc_ok c0 env /\ cenv_top_ext c0 c0 ee.scopes /\
               stmt_state_rel H ctx func c0 cx ee s /\
               storage_well_formed_on cx ee (FST H) /\
               ghost_inv_at (DF H) lo d c0 cx ee G tn s /\
               return_buf_frame d c0 sa0 s /\ ret_pc_ok c0 sa0 s /\
               return_buf_sep d c0 ee s /\
               (k <> (0 :num) ==> body_stmts_full_ok cx body) /\
               (\(c :compile_env) (ee :evaluation_state) (s :venom_state)
                  (G :string |-> num # num) (tn :taint).
                  alloca_history func s /\
                  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
                  s0.vs_alloca_next <= s.vs_alloca_next /\
                  (!(x :string) (w :256 word).
                     not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
                     lookup_var x s = SOME w) /\
                  (!(aid :num) (b :num # num).
                     FLOOKUP s0.vs_allocas aid = SOME b ==>
                     FLOOKUP s.vs_allocas aid = SOME b) /\
                  (!(x :string).
                     not_fresh_at sa0 x ==>
                     FLOOKUP G x = FLOOKUP G0 x /\
                     op_taint tn (Var x) = op_taint tn0 (Var x)) /\
                  alloca_frame c0 e0 sa0 s0 c ee s /\
                  !(aid :num) (off :num) (sz :num) (i :num).
                    FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
                    aid < sa0.cs_next_id /\
                    (!(name :string) (b :num) (sz' :num).
                       local_region c0 e0.scopes s0 name b sz' ==>
                       off + sz <= b \/ b + sz' <= off) /\ off <= i /\
                    i < off + sz /\ i IN tn.t_mem ==>
                    i IN tn0.t_mem) c0 ee s G tn) H (a::rs) ei G tn s) /\
       gas_admissible (eval_for cx tyv id body (a::rs)) ok ei ==>
       gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (cx_tops cx) cx st0
         ((\(a :eval_result).
             bind (read_result cx a) (push_scope_with_var id tyv)) a)
         (ei,s,G,tn)
         (\(H :(bool # 256 word # type_value) list # num list)
            (res :unit + vyperState$exception) (eb :evaluation_state)
            (Gf :string |-> num # num) (tnf :taint) (z :venom_state).
            res = (INL () :unit + vyperState$exception) /\
            eb.gas_obs = ([] :256 word list) /\
            ?(v :value) (k :num).
              eb =
              (\(ei :evaluation_state) (v :value).
                 ei with
                 scopes :=
                   fmupdate id
                     <|assignable := F; type := tyv; value := v;
                       popped := ([] :(subscript list # value) list)|>
                     (FEMPTY :string |-> scope_entry)::ei.scopes)
                (ei with gas_obs := ([] :256 word list)) v /\
              read_result cx a ei = ((INL v :value + vyperState$exception),ei) /\
              a::rs = DROP k vs /\
              (\(H :(bool # 256 word # type_value) list # num list)
                 (ei :evaluation_state) (v :value) (k :num) (z :venom_state)
                 (Gf :string |-> num # num) (tnf :taint).
                 value_has_type tyv v /\ body_stmts_full_ok cx body /\
                 expr_sim_inv bc cx (extend_local env id typ F)
                   ((\(ei :evaluation_state) (v :value).
                       ei with
                       scopes :=
                         fmupdate id
                           <|assignable := F; type := tyv; value := v;
                             popped := ([] :(subscript list # value) list)|>
                           (FEMPTY :string |-> scope_entry)::ei.scopes) ei v) /\
                 ce_locals_declared bc (extend_local env id typ F) /\
                 locals_alloc_ok bc (extend_local env id typ F) /\
                 cenv_top_ext c0 bc
                   ((\(ei :evaluation_state) (v :value).
                       ei with
                       scopes :=
                         fmupdate id
                           <|assignable := F; type := tyv; value := v;
                             popped := ([] :(subscript list # value) list)|>
                           (FEMPTY :string |-> scope_entry)::ei.scopes) ei v).
                   scopes /\
                 stmt_state_rel H ctx func bc cx
                   ((\(ei :evaluation_state) (v :value).
                       ei with
                       scopes :=
                         fmupdate id
                           <|assignable := F; type := tyv; value := v;
                             popped := ([] :(subscript list # value) list)|>
                           (FEMPTY :string |-> scope_entry)::ei.scopes) ei v) z /\
                 storage_well_formed_on cx
                   ((\(ei :evaluation_state) (v :value).
                       ei with
                       scopes :=
                         fmupdate id
                           <|assignable := F; type := tyv; value := v;
                             popped := ([] :(subscript list # value) list)|>
                           (FEMPTY :string |-> scope_entry)::ei.scopes) ei v)
                   (FST H) /\
                 ghost_inv_at (DF H) lo d bc cx
                   ((\(ei :evaluation_state) (v :value).
                       ei with
                       scopes :=
                         fmupdate id
                           <|assignable := F; type := tyv; value := v;
                             popped := ([] :(subscript list # value) list)|>
                           (FEMPTY :string |-> scope_entry)::ei.scopes) ei v)
                   Gf tnf z /\ ret_pc_ok bc sb0 z /\
                 return_buf_frame d bc sb0 z /\
                 return_buf_sep d bc
                   (ei with scopes :=
                     fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
                       FEMPTY::ei.scopes) z /\
                 (\(c :compile_env) (ee :evaluation_state) (s :venom_state)
                    (G :string |-> num # num) (tn :taint).
                    alloca_history func s /\
                    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
                    s0.vs_alloca_next <= s.vs_alloca_next /\
                    (!(x :string) (w :256 word).
                       not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
                       lookup_var x s = SOME w) /\
                    (!(aid :num) (b :num # num).
                       FLOOKUP s0.vs_allocas aid = SOME b ==>
                       FLOOKUP s.vs_allocas aid = SOME b) /\
                    (!(x :string).
                       not_fresh_at sa0 x ==>
                       FLOOKUP G x = FLOOKUP G0 x /\
                       op_taint tn (Var x) = op_taint tn0 (Var x)) /\
                    alloca_frame c0 e0 sa0 s0 c ee s /\
                    !(aid :num) (off :num) (sz :num) (i :num).
                      FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
                      aid < sa0.cs_next_id /\
                      (!(name :string) (b :num) (sz' :num).
                         local_region c0 e0.scopes s0 name b sz' ==>
                         off + sz <= b \/ b + sz' <= off) /\ off <= i /\
                      i < off + sz /\ i IN tn.t_mem ==>
                      i IN tn0.t_mem) bc
                   ((\(ei :evaluation_state) (v :value).
                       ei with
                       scopes :=
                         fmupdate id
                           <|assignable := F; type := tyv; value := v;
                             popped := ([] :(subscript list # value) list)|>
                           (FEMPTY :string |-> scope_entry)::ei.scopes) ei v) z
                   Gf tnf /\ ~z.vs_halted /\
                 z.vs_current_bb = sb0.cs_current_bb /\
                 z.vs_inst_idx = LENGTH sb0.cs_current_insts /\
                 lookup_var idx z = SOME (n2w k :256 word) /\
                 FLOOKUP Gf idx = (NONE :(num # num) option) /\
                 op_taint tnf (Var idx) = ({} :num -> bool) /\
                 lookup_var p z = SOME dst /\
                 eval_operand lvo z = SOME (n2w len :256 word) /\
                 op_prov Gf lvo = (NONE :(num # num) option) /\
                 op_taint tnf lvo = ({} :num -> bool) /\ allocas_from lo z /\
                 FLOOKUP z.vs_allocas sd.cs_next_id = SOME (w2n dst,nb) /\
                 ptr_covers Gf tnf p z nb /\
                 w2n dst + nb <= z.vs_alloca_next /\
                 (!(name :string) (b :num) (sz :num).
                    local_region c0 ei.scopes z name b sz ==>
                    w2n dst + nb <= b \/ b + sz <= w2n dst) /\
                 return_buf_frame d c0 sa0 z /\ ret_pc_ok c0 sa0 z) H
                (ei with gas_obs := ([] :256 word list)) v k z Gf tnf)
         (\(H :(bool # 256 word # type_value) list # num list)
            (res :unit + vyperState$exception) (ee :evaluation_state)
            (gt :(string |-> num # num) # taint) (r :exec_result).
            ?(ex :vyperState$exception).
              res = (INR ex :unit + vyperState$exception) /\
              (\(H :(bool # 256 word # type_value) list # num list)
                 (ex :vyperState$exception) (ee :evaluation_state)
                 (gt :(string |-> num # num) # taint) (r :exec_result).
                 (!(tail :256 word list).
                    stmt_exit_ptr (RetQ H) (ee with gas_obs := tail)
                      (INR ex :unit + vyperState$exception) gt r) /\
                 halt_exit H cx ee (INR ex :'a + vyperState$exception) r /\
                 (ctx_has_dalloca ctx ==>
                  !(u :venom_state).
                    r = Halt u \/ (?(ir :internal_return). r = IntRet ir u) ==>
                    allocas_below_fmp u)) H ex ee gt r)) ==>
    !(a :eval_result) (rs :eval_result list) (es :evaluation_state)
        (s :venom_state) (G :string |-> num # num) (tn :taint).
      ~s.vs_halted /\
      (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_no_wrap inst u) /\
      (!(H :(bool # 256 word # type_value) list # num list).
         valid_horizon cx st0 H es.storage_trace ==>
         (\(H :(bool # 256 word # type_value) list # num list)
            (rs :eval_result list) (ee :evaluation_state)
            (G :string |-> num # num) (tn :taint) (s :venom_state).
            ?(k :num) (off :num).
              k <= len /\ len = LENGTH vs /\ len <= bound_length bd /\
              vs =
              GENLIST
                (\(j :num).
                   PlaceR
                     (StoragePlace tr
                        ((case bd of
                            (Fixed v :bound) => slot
                          | Dynamic v1 => slot + (1w :256 word)) +
                         (n2w (j * type_slot_size tyv) :256 word)) tyv)) len /\
              rs = DROP k vs /\ slot = (n2w off :256 word) /\
              MEM (StorageRoot tr off (ArrayTV tyv bd)) ee.storage_trace /\
              evaluate_type (get_tenv cx) typ = SOME tyv /\
              well_formed_type_value tyv /\ s.vs_current_bb = cond /\
              s.vs_inst_idx = (0 :num) /\ ~s.vs_halted /\
              lookup_var idx s = SOME (n2w k :256 word) /\
              FLOOKUP G idx = (NONE :(num # num) option) /\
              op_taint tn (Var idx) = ({} :num -> bool) /\
              eval_operand lvo s = SOME (n2w len :256 word) /\
              op_taint tn lvo = ({} :num -> bool) /\
              op_prov G lvo = (NONE :(num # num) option) /\
              eval_operand (Lit slot) s = SOME slot /\
              op_taint tn (Lit slot) = ({} :num -> bool) /\
              lookup_var p s = SOME dst /\
              FLOOKUP s.vs_allocas sd.cs_next_id = SOME (w2n dst,nb) /\
              ptr_covers G tn p s nb /\ (32 :num) * type_slot_size tyv <= nb /\
              w2n dst + nb < (2 :num) ** (256 :num) /\
              w2n dst + nb <= s.vs_alloca_next /\
              (!(name :string) (b :num) (sz :num).
                 local_region c0 ee.scopes s name b sz ==>
                 w2n dst + nb <= b \/ b + sz <= w2n dst) /\
              lookup_scopes id ee.scopes = (NONE :scope_entry option) /\
              expr_sim_inv c0 cx env ee /\ ce_locals_declared c0 env /\
              locals_alloc_ok c0 env /\ cenv_top_ext c0 c0 ee.scopes /\
              stmt_state_rel H ctx func c0 cx ee s /\
              storage_well_formed_on cx ee (FST H) /\
              ghost_inv_at (DF H) lo d c0 cx ee G tn s /\
              return_buf_frame d c0 sa0 s /\ ret_pc_ok c0 sa0 s /\
              return_buf_sep d c0 ee s /\
              (k <> (0 :num) ==> body_stmts_full_ok cx body) /\
              (\(c :compile_env) (ee :evaluation_state) (s :venom_state)
                 (G :string |-> num # num) (tn :taint).
                 alloca_history func s /\
                 (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
                 s0.vs_alloca_next <= s.vs_alloca_next /\
                 (!(x :string) (w :256 word).
                    not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
                    lookup_var x s = SOME w) /\
                 (!(aid :num) (b :num # num).
                    FLOOKUP s0.vs_allocas aid = SOME b ==>
                    FLOOKUP s.vs_allocas aid = SOME b) /\
                 (!(x :string).
                    not_fresh_at sa0 x ==>
                    FLOOKUP G x = FLOOKUP G0 x /\
                    op_taint tn (Var x) = op_taint tn0 (Var x)) /\
                 alloca_frame c0 e0 sa0 s0 c ee s /\
                 !(aid :num) (off :num) (sz :num) (i :num).
                   FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
                   aid < sa0.cs_next_id /\
                   (!(name :string) (b :num) (sz' :num).
                      local_region c0 e0.scopes s0 name b sz' ==>
                      off + sz <= b \/ b + sz' <= off) /\ off <= i /\
                   i < off + sz /\ i IN tn.t_mem ==>
                   i IN tn0.t_mem) c0 ee s G tn) H (a::rs) es G tn s) /\
      gas_admissible (eval_for cx tyv id body (a::rs)) ok es ==>
      gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (cx_tops cx) cx st0
        (bind (read_result cx a)
           (\(v :value).
              ignore_bind (push_scope_with_var id tyv v)
                (finally
                   (try
                      (ignore_bind (eval_stmts cx body)
                         (return F :
                          evaluation_state ->
                          (bool + vyperState$exception) # evaluation_state))
                      handle_loop_exception) pop_scope))) (es,s,G,tn)
        (\(H :(bool # 256 word # type_value) list # num list)
           (res :bool + vyperState$exception) (ee :evaluation_state)
           (G1 :string |-> num # num) (tn1 :taint) (t :venom_state).
           ee.gas_obs = ([] :256 word list) /\ ~t.vs_halted /\
           ?(b :bool).
             res = (INL b :bool + vyperState$exception) /\
             (b ==>
              (\(H :(bool # 256 word # type_value) list # num list)
                 (ee :evaluation_state) (G :string |-> num # num) (tn :taint)
                 (t :venom_state).
                 ?(c :compile_env).
                   stmt_lands lctx sb (INL () :unit + vyperState$exception) t /\
                   ~t.vs_halted /\ ~block_is_terminated sb /\ c = c0 /\
                   cenv_top_ext c0 c ee.scopes /\
                   stmt_state_rel H ctx func c cx ee t /\
                   storage_well_formed_on cx ee (FST H) /\
                   return_buf_frame d c sb t /\ return_buf_sep d c ee t /\
                   ghost_inv_at (DF H) lo d c cx ee G tn t /\
                   (\(c :compile_env) (ee :evaluation_state) (s :venom_state)
                      (G :string |-> num # num) (tn :taint).
                      alloca_history func s /\
                      (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
                      s0.vs_alloca_next <= s.vs_alloca_next /\
                      (!(x :string) (w :256 word).
                         not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
                         lookup_var x s = SOME w) /\
                      (!(aid :num) (b :num # num).
                         FLOOKUP s0.vs_allocas aid = SOME b ==>
                         FLOOKUP s.vs_allocas aid = SOME b) /\
                      (!(x :string).
                         not_fresh_at sa0 x ==>
                         FLOOKUP G x = FLOOKUP G0 x /\
                         op_taint tn (Var x) = op_taint tn0 (Var x)) /\
                      alloca_frame c0 e0 sa0 s0 c ee s /\
                      !(aid :num) (off :num) (sz :num) (i :num).
                        FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
                        aid < sa0.cs_next_id /\
                        (!(name :string) (b :num) (sz' :num).
                           local_region c0 e0.scopes s0 name b sz' ==>
                           off + sz <= b \/ b + sz' <= off) /\ off <= i /\
                        i < off + sz /\ i IN tn.t_mem ==>
                        i IN tn0.t_mem) c ee t G tn) H ee G1 tn1 t) /\
             (~b ==>
              (\(H :(bool # 256 word # type_value) list # num list)
                 (rs :eval_result list) (ee :evaluation_state)
                 (G :string |-> num # num) (tn :taint) (s :venom_state).
                 ?(k :num) (off :num).
                   k <= len /\ len = LENGTH vs /\ len <= bound_length bd /\
                   vs =
                   GENLIST
                     (\(j :num).
                        PlaceR
                          (StoragePlace tr
                             ((case bd of
                                 (Fixed v :bound) => slot
                               | Dynamic v1 => slot + (1w :256 word)) +
                              (n2w (j * type_slot_size tyv) :256 word)) tyv))
                     len /\ rs = DROP k vs /\ slot = (n2w off :256 word) /\
                   MEM (StorageRoot tr off (ArrayTV tyv bd)) ee.storage_trace /\
                   evaluate_type (get_tenv cx) typ = SOME tyv /\
                   well_formed_type_value tyv /\ s.vs_current_bb = cond /\
                   s.vs_inst_idx = (0 :num) /\ ~s.vs_halted /\
                   lookup_var idx s = SOME (n2w k :256 word) /\
                   FLOOKUP G idx = (NONE :(num # num) option) /\
                   op_taint tn (Var idx) = ({} :num -> bool) /\
                   eval_operand lvo s = SOME (n2w len :256 word) /\
                   op_taint tn lvo = ({} :num -> bool) /\
                   op_prov G lvo = (NONE :(num # num) option) /\
                   eval_operand (Lit slot) s = SOME slot /\
                   op_taint tn (Lit slot) = ({} :num -> bool) /\
                   lookup_var p s = SOME dst /\
                   FLOOKUP s.vs_allocas sd.cs_next_id = SOME (w2n dst,nb) /\
                   ptr_covers G tn p s nb /\
                   (32 :num) * type_slot_size tyv <= nb /\
                   w2n dst + nb < (2 :num) ** (256 :num) /\
                   w2n dst + nb <= s.vs_alloca_next /\
                   (!(name :string) (b :num) (sz :num).
                      local_region c0 ee.scopes s name b sz ==>
                      w2n dst + nb <= b \/ b + sz <= w2n dst) /\
                   lookup_scopes id ee.scopes = (NONE :scope_entry option) /\
                   expr_sim_inv c0 cx env ee /\ ce_locals_declared c0 env /\
                   locals_alloc_ok c0 env /\ cenv_top_ext c0 c0 ee.scopes /\
                   stmt_state_rel H ctx func c0 cx ee s /\
                   storage_well_formed_on cx ee (FST H) /\
                   ghost_inv_at (DF H) lo d c0 cx ee G tn s /\
                   return_buf_frame d c0 sa0 s /\ ret_pc_ok c0 sa0 s /\
                   return_buf_sep d c0 ee s /\
                   (k <> (0 :num) ==> body_stmts_full_ok cx body) /\
                   (\(c :compile_env) (ee :evaluation_state) (s :venom_state)
                      (G :string |-> num # num) (tn :taint).
                      alloca_history func s /\
                      (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
                      s0.vs_alloca_next <= s.vs_alloca_next /\
                      (!(x :string) (w :256 word).
                         not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
                         lookup_var x s = SOME w) /\
                      (!(aid :num) (b :num # num).
                         FLOOKUP s0.vs_allocas aid = SOME b ==>
                         FLOOKUP s.vs_allocas aid = SOME b) /\
                      (!(x :string).
                         not_fresh_at sa0 x ==>
                         FLOOKUP G x = FLOOKUP G0 x /\
                         op_taint tn (Var x) = op_taint tn0 (Var x)) /\
                      alloca_frame c0 e0 sa0 s0 c ee s /\
                      !(aid :num) (off :num) (sz :num) (i :num).
                        FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
                        aid < sa0.cs_next_id /\
                        (!(name :string) (b :num) (sz' :num).
                           local_region c0 e0.scopes s0 name b sz' ==>
                           off + sz <= b \/ b + sz' <= off) /\ off <= i /\
                        i < off + sz /\ i IN tn.t_mem ==>
                        i IN tn0.t_mem) c0 ee s G tn) H rs ee G1 tn1 t))
        (\(H :(bool # 256 word # type_value) list # num list)
           (res :bool + vyperState$exception) (ee :evaluation_state)
           (gt :(string |-> num # num) # taint) (r :exec_result).
           ?(ex :vyperState$exception).
             res = (INR ex :bool + vyperState$exception) /\
             (\(H :(bool # 256 word # type_value) list # num list)
                (ex :vyperState$exception) (ee :evaluation_state)
                (gt :(string |-> num # num) # taint) (r :exec_result).
                (!(tail :256 word list).
                   stmt_exit_ptr (RetQ H) (ee with gas_obs := tail)
                     (INR ex :unit + vyperState$exception) gt r) /\
                halt_exit H cx ee (INR ex :'a + vyperState$exception) r /\
                (ctx_has_dalloca ctx ==>
                 !(u :venom_state).
                   r = Halt u \/ (?(ir :internal_return). r = IntRet ir u) ==>
                   allocas_below_fmp u)) H ex ee gt r)
Proof
 rpt gen_tac >>
  qpat_abbrev_tac `explicit = gas_explicit_sites ctx shadow_ctx` >>
  abbrev_lambda_tac "EB" 2 0 `ee with scopes := (FEMPTY |+ (id, _)) :: ee.scopes` >>
  abbrev_lambda_tac "Fr" 5 0 `alloca_history func s /\ _` >>
  abbrev_lambda_tac "Inv" 6 2 `k <= len /\ _` >>
  qabbrev_tac `Ready = (\H rs ee G tn s. ?k off.
   k < len /\ len = LENGTH vs /\ len <= bound_length bd /\
   vs = GENLIST (\j. PlaceR (StoragePlace tr
     ((case bd of Fixed _ => slot | Dynamic _ => slot+1w) +
       n2w (j * type_slot_size tyv)) tyv)) len /\
   rs = DROP k vs /\ slot = n2w off /\
   MEM (StorageRoot tr off (ArrayTV tyv bd)) ee.storage_trace /\
   evaluate_type (get_tenv cx) typ = SOME tyv /\ well_formed_type_value tyv /\
   s.vs_current_bb = si.cs_current_bb /\
   s.vs_inst_idx = LENGTH si.cs_current_insts /\ ~s.vs_halted /\
   lookup_var idx s = SOME (n2w k) /\
   FLOOKUP G idx = NONE /\ op_taint tn (Var idx) = {} /\
   eval_operand lvo s = SOME (n2w len) /\ op_taint tn lvo = {} /\
   op_prov G lvo = NONE /\
   eval_operand (Lit slot) s = SOME slot /\ op_taint tn (Lit slot) = {} /\
   lookup_var p s = SOME dst /\
   FLOOKUP s.vs_allocas sd.cs_next_id = SOME (w2n dst,nb) /\
   ptr_covers G tn p s nb /\ 32 * type_slot_size tyv <= nb /\
   w2n dst+nb < 2**256 /\ w2n dst+nb <= s.vs_alloca_next /\
   (!name b sz. local_region c0 ee.scopes s name b sz ==>
      w2n dst+nb <= b \/ b+sz <= w2n dst) /\
   lookup_scopes id ee.scopes = NONE /\
   expr_sim_inv c0 cx env ee /\ ce_locals_declared c0 env /\
   locals_alloc_ok c0 env /\ cenv_top_ext c0 c0 ee.scopes /\
   stmt_state_rel H ctx func c0 cx ee s /\
   storage_well_formed_on cx ee (FST H) /\
   ghost_inv_at (DF H) lo d c0 cx ee G tn s /\
   return_buf_frame d c0 sa0 s /\ ret_pc_ok c0 sa0 s /\
   return_buf_sep d c0 ee s /\ body_stmts_full_ok cx body' /\ Fr c0 ee s G tn)` >>
  abbrev_lambda_tac "Done" 5 1 `stmt_lands lctx sb (INL ()) t /\ _` >>
  abbrev_lambda_tac "R" 5 0 `(!tail. stmt_exit_ptr _ (ee with gas_obs := tail) (INR ex) gt r) /\ _` >>
  abbrev_lambda_tac "Entry" 7 0 `value_has_type tyv v /\ _` >>
  abbrev_lambda_tac "head" 1 0 `bind (read_result cx a) (push_scope_with_var id tyv)` >>
  qabbrev_tac `clean =
    finally (try (do eval_stmts cx body'; return F od) handle_loop_exception)
      pop_scope` >>
  abbrev_lambda_tac "X" 5 1 `res = INR ex /\ R H ex ee gt r` >>
 strip_tac >> rpt gen_tac >> strip_tac >>
 sg `storage_trace_frame clean` >- suspend "clean_trace" >>
 sg `storage_trace_frame (head a)` >- suspend "head_trace" >>
 irule gas_outcome_full_initial_domain >>
 conj_tac >- suspend "round_trace" >>
 conj_tac >- first_assum ACCEPT_TAC >>
 strip_tac >>
 `bind (head a) (\u:unit. clean) =
      (do v <- read_result cx a; push_scope_with_var id tyv v; clean od)` by
   simp[Abbr `head`, vyperStateTheory.bind_assoc, vyperStateTheory.ignore_bind_def] >>
 pop_assum (SUBST1_TAC o SYM) >>
 suspend "compose"
QED

Resume for_storage_array_round_full[clean_trace]:
 simp[Abbr `clean`] >> irule storage_trace_frame_finally >>
 simp[storage_trace_frame_pop_scope] >> irule storage_trace_frame_try >>
 simp[storage_trace_frame_loop_handler] >>
 irule storage_trace_frame_ignore_bind >>
 simp[storage_trace_frame_return,
      CONJUNCT1 (CONJUNCT2 evaluate_storage_trace_frame)]
QED

Resume for_storage_array_round_full[head_trace]:
 simp[Abbr `head`] >> irule storage_trace_frame_bind_all >>
 simp[storage_trace_frame_read_result, storage_trace_frame_state_updates]
QED

Resume for_storage_array_round_full[round_trace]:
 irule storage_trace_frame_bind_all >> simp[storage_trace_frame_read_result] >>
 gen_tac >> irule storage_trace_frame_ignore_bind >>
 simp[storage_trace_frame_state_updates]
QED

Resume for_storage_array_round_full[compose]:
 qabbrev_tac `Qmid = (\H (res:bool + exception) ee G1 tn1 t.
    ee.gas_obs = [] /\ ~t.vs_halted /\
    ?b. res = INL b /\ (b ==> Done H ee G1 tn1 t) /\
      (~b ==> Ready H (a::rs) ee G1 tn1 t))` >>
 irule gas_outcome_full_zero_suffix >> qexists_tac `Qmid` >>
 reverse conj_tac >- suspend "bind_head" >> suspend "increment"
QED

Resume for_storage_array_round_full[bind_head]:
 qunabbrev_tac `X` >> irule gas_outcome_full_bind_all_path >>
 simp[] >>
 conj_tac >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_unit >>
              qexistsl [`mid`,`t`] >> simp[]) >>
 conj_tac >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_unit >> simp[]) >>
 qexists_tac `\H (res:unit + exception) eb Gf tnf z.
    res = INL () /\ eb.gas_obs = [] /\
    ?v k. eb = EB (es with gas_obs := []) v /\
      read_result cx a es = (INL v,es) /\ a::rs = DROP k vs /\
      Entry H (es with gas_obs := []) v k z Gf tnf` >>
 reverse conj_tac >- suspend "head_exec" >> suspend "head_continue"
QED

Resume for_storage_array_round_full[head_exec]:
 first_x_assum irule >> simp[]
QED

Resume for_storage_array_round_full[head_continue]:
 BETA_TAC >> rpt gen_tac >> strip_tac >>
 rename1 `storage_trace_domain cx st0 mid.storage_trace` >>
 rename1 `gas_outcome_full _ _ _ _ clean (mid,z,GG,tt) _ _` >>
 qabbrev_tac `Hm = storage_trace_horizon mid.storage_trace` >>
 `valid_horizon cx st0 Hm mid.storage_trace` by
   simp[Abbr `Hm`, GSYM storage_trace_domain_def] >>
 qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
              _ /\ _ /\ (?v k. _ /\ _ /\ _ /\ Entry H _ v k z GG tt)`
   (qspec_then `Hm` mp_tac) >>
 (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
 rename1 `read_result cx a es = (INL value,es)` >>
 rename1 `a::rs = DROP k vs` >>
 disj1_tac >> simp[] >>
 `mid.storage_trace = es.storage_trace` by simp[Abbr `EB`] >>
 `Inv Hm (a::rs) es G tn s` by
   (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> Inv H _ _ _ _ _`
      (qspec_then `Hm` irule) >>
    qpat_assum `mid.storage_trace = es.storage_trace` (SUBST1_TAC o SYM) >>
    first_assum ACCEPT_TAC) >>
 sg `!H. valid_horizon cx st0 H mid.storage_trace ==>
      Entry H (es with gas_obs := []) value k z GG tt`
 >- (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
              _ /\ _ /\ (?v k. _ /\ _ /\ _ /\ Entry H _ v k z GG tt)`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     rename1 `Entry H _ value' k' z GG tt` >>
     `value' = value` by
       (qpat_assum `read_result cx a es = (INL value',es)` mp_tac >>
        qpat_assum `read_result cx a es = (INL value,es)`
          (fn th => simp[NoAsms,th])) >>
     `k' = k` by
       (`LENGTH (a::rs) = LENGTH vs - k` by
          (qpat_assum `a::rs = DROP k vs` SUBST1_TAC >> simp[]) >>
        `LENGTH (a::rs) = LENGTH vs - k'` by
          (qpat_assum `a::rs = DROP k' vs` SUBST1_TAC >> simp[]) >>
        qpat_assum `LENGTH (a::rs) = LENGTH vs - k` mp_tac >>
        qpat_assum `LENGTH (a::rs) = LENGTH vs - k'` mp_tac >>
        simp[NoAsms] >> decide_tac) >>
     qpat_assum `value' = value` (SUBST1_TAC o SYM) >>
     qpat_assum `k' = k` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
 rename1 `body_stmts_full_ok cx stmts` >>
 sg `lookup_scopes id es.scopes = NONE`
 >- (qpat_assum `Inv Hm (a::rs) es G tn s` mp_tac >>
     simp[NoAsms,Abbr `Inv`] >> rpt strip_tac >> first_assum ACCEPT_TAC) >>
 sg `gas_admissible (eval_stmts cx stmts) (stmt_res_ok (InLoop exit incr))
       (EB (es with gas_obs := []) value)`
 >- suspend "body_admissible" >>
 suspend "cleanup_packet"
QED

Resume for_storage_array_round_full[body_admissible]:
 simp[gasContextTheory.gas_admissible_def] >>
 rpt gen_tac >> strip_tac >>
 rename1 `eval_stmts cx stmts _ = (raw,ef)` >>
 rename1 `eval_stmts cx stmts (_ with gas_obs := gs) = (raw,ef)` >>
 `eval_for cx tyv id stmts (a::rs) (es with gas_obs := gs) =
  eval_for cx tyv id stmts (Value value::rs) (es with gas_obs := gs)` by
   (`read_result cx a (es with gas_obs := gs) =
         (INL value,es with gas_obs := gs)` by
      (drule exprSimMemorySourceTheory.read_result_gas_obs >> simp[]) >>
    `read_result cx (Value value) (es with gas_obs := gs) =
         (INL value,es with gas_obs := gs)` by
      simp[vyperStateTheory.read_result_def,vyperStateTheory.return_def] >>
    qpat_assum `read_result cx a (es with gas_obs := gs) = _`
      (mp_then Any (rewrite_tac o single) vyperInterpreterTheory.eval_for_cons_read) >>
    qpat_assum `read_result cx (Value value) (es with gas_obs := gs) = _`
      (mp_then Any (rewrite_tac o single) vyperInterpreterTheory.eval_for_cons_read)) >>
 Cases_on `eval_for cx tyv id stmts (Value value::rs) (es with gas_obs := gs)` >>
 rename1 `eval_for cx tyv id stmts (Value value::rs) _ = (lr,le)` >>
 `stmt_res_ok lctx lr` by
   (qpat_assum `!res. ok res ==> stmt_res_ok lctx res` irule >>
    qpat_assum `gas_admissible (eval_for _ _ _ _ _) ok es`
      (qspecl_then [`gs`,`lr`,`le`] mp_tac o
       REWRITE_RULE [gasContextTheory.gas_admissible_def]) >> simp[]) >>
 qpat_assum `eval_for cx tyv id stmts (Value value::rs) _ = (lr,le)`
   (mp_then Any mp_tac stmtSimForPartsTheory.eval_for_cons_cases) >>
 simp[] >> strip_tac >>
 gvs[Abbr `EB`] >> simp[stmt_res_ok_def] >>
 qpat_x_assum `stmt_res_ok lctx _` mp_tac >> simp[stmt_res_ok_def]
QED

Resume for_storage_array_round_full[cleanup_packet]:
 qabbrev_tac `ei = es with gas_obs := []` >>
 qabbrev_tac `eb = EB ei value` >>
 simp[NoAsms,Abbr `Qmid`,Abbr `clean`] >>
 sg `!f inst u. frag_reachable ctx func z f inst u ==> dalloca_no_wrap inst u`
 >- (`!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
       (qpat_assum `body_inv tops ctx bc cx` (fn inv =>
          qpat_assum `MEM func ctx.ctx_functions` (fn member =>
            ACCEPT_TAC (MATCH_MP bodyFullIfExpReachTheory.body_inv_no_phi
              (CONJ inv member))))) >>
     qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
                  gas_origin_ptr_path _ (s,G,tn) _ (OK z,GG,tt)`
       (qspec_then `Hm` (drule_then
         (mp_then (Pos hd) mp_tac bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_no_wrap))) >>
     asm_rewrite_tac []) >>
 `ei.scopes = es.scopes /\ ei.storage_trace = es.storage_trace` by
   simp[Abbr `ei`] >>
 `expr_sim_inv c0 cx env ei` suffices_by (strip_tac >> suspend "cleanup_apply") >>
 qpat_assum `Inv Hm (a::rs) es G tn s` mp_tac >>
 simp[NoAsms, Abbr `Inv`, Abbr `ei`] >>
 disch_then (qx_choose_then `ki` (qx_choose_then `root` strip_assume_tac)) >>
 first_assum ACCEPT_TAC
QED

Resume for_storage_array_round_full[cleanup_apply]:
 qpat_assum `Inv Hm (a::rs) es G tn s` mp_tac >>
 simp[NoAsms, Abbr `Inv`] >>
 disch_then (qx_choose_then `ki` (qx_choose_then `root` strip_assume_tac)) >>
 `k < len` by
   (qpat_assum `a::rs = DROP k vs` (mp_tac o AP_TERM ``LENGTH : eval_result list -> num``) >>
    qpat_assum `len = LENGTH vs` (fn th =>
      simp[NoAsms, listTheory.LENGTH_DROP, SYM th]) >> decide_tac) >>
 qpat_assum `Entry Hm ei value k z GG tt` mp_tac >>
 qpat_assum `Abbrev (Entry = _)`
   (SUBST1_TAC o PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
 simp[NoAsms] >>
 qpat_assum `Abbrev (eb = _)` (SUBST1_TAC o SYM o PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
 strip_tac >>
 `!H. valid_horizon cx st0 H eb.storage_trace ==>
       stmt_state_rel H ctx func bc cx eb z /\
       storage_well_formed_on cx eb (FST H) /\
       ghost_inv_at (DF H) lo d bc cx eb GG tt z` by
   (qx_gen_tac `H` >> disch_tac >>
    `valid_horizon cx st0 H mid.storage_trace` by (simp[] >> (metis_tac[])) >>
    qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> Entry H ei value k z GG tt`
      (qspec_then `H` (fn th =>
        qpat_assum `valid_horizon cx st0 H mid.storage_trace` (mp_tac o MP th))) >>
    simp[NoAsms, Abbr `Entry`] >>
    qpat_assum `Abbrev (eb = _)` (SUBST1_TAC o SYM o PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
    strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
 `lookup_scopes id ei.scopes = NONE /\ cenv_top_ext c0 c0 ei.scopes` by
   (qpat_assum `ei.scopes = es.scopes` SUBST1_TAC >>
    conj_tac >> first_assum ACCEPT_TAC) >>
 `MEM (StorageRoot tr root (ArrayTV tyv bd)) ei.storage_trace` by
   (qpat_assum `ei.storage_trace = es.storage_trace` SUBST1_TAC >>
    first_assum ACCEPT_TAC) >>
 `eval_operand (Lit slot) z = SOME slot /\ op_taint tt (Lit slot) = {}` by
   simp[NoAsms,eval_operand_def,op_taint_def] >>
 qspecl_then
    [`DF`,`lo`,`d`,`ctx`,`shadow_ctx`,`func`,`shadow_func`,`PG`,`cx`,`RetQ`,
     `c0`,`e0`,`sa0`,`sb`,`s0`,`G0`,`tn0`,`tr`,`slot`,`dst`,`tyv`,`typ`,
     `bd`,`vs`,`len`,`nb`,`id`,`env`,`p`,`idx`,`lvo`,`sd`,`stmts`,
     `si`,`lctx`,`ei`,`value`,`bc`,`bc1`,`sb0`,`sb1`,`sj`,`tops`,`bindings`,
     `ret_ty`,`env_b`,`k`,`root`,`a`,`rs`,`st0`,`z`,`GG`,`tt`,`exit`,`incr`,
     `shadow_sb0`,`shadow_sb1`] mp_tac for_storage_array_body_cleanup_full >>
 qpat_assum `Abbrev (eb = _)` (fn eb_th =>
   qpat_assum `Abbrev (EB = _)` (fn EB_th =>
     CONV_TAC (LAND_CONV (PURE_REWRITE_CONV [SYM (BETA_RULE
       (PURE_REWRITE_RULE [PURE_REWRITE_RULE [markerTheory.Abbrev_def] EB_th,
                           markerTheory.Abbrev_def] eb_th))])))) >>
 map_every (fn q => qpat_assum q (fn th =>
   CONV_TAC (LAND_CONV (PURE_REWRITE_CONV
     [SYM (PURE_REWRITE_RULE [markerTheory.Abbrev_def] th)]))))
   [`Abbrev (explicit = _)`, `Abbrev (Fr = _)`, `Abbrev (Ready = _)`,
    `Abbrev (Done = _)`, `Abbrev (R = _)`] >>
 BETA_TAC >>
 (impl_tac >-
   (rpt conj_tac >> simp[NoAsms] >>
    FIRST [first_assum ACCEPT_TAC,
      qpat_assum `return_buf_sep d bc _ z` mp_tac >>
      simp[NoAsms, Abbr `eb`, Abbr `EB`]])) >>
 disch_then ACCEPT_TAC
QED

Resume for_storage_array_round_full[increment]:
 qx_gen_tac `res` >> qx_gen_tac `ee` >> qx_gen_tac `G1` >>
 qx_gen_tac `tn1` >> qx_gen_tac `t` >> strip_tac >>
 rename1 `supported_stmts tops bindings stmts` >>
 qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
 `valid_horizon cx st0 H0 ee.storage_trace` by
   simp[Abbr `H0`, GSYM storage_trace_domain_def] >>
 `Qmid H0 res ee G1 tn1 t` by
   (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> Qmid H res ee G1 tn1 t`
      (qspec_then `H0` irule) >> first_assum ACCEPT_TAC) >>
 qpat_assum `Qmid H0 res ee G1 tn1 t` mp_tac >>
 qpat_assum `Abbrev (Qmid = _)`
   (SUBST1_TAC o PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
 BETA_TAC >> strip_tac >> rename1 `res = INL (b:bool)` >>
 Q_TAC ASM_CASES_TAC `b:bool`
 >- suspend "increment_break" >>
 suspend "increment_continue"
QED

Resume for_storage_array_round_full[increment_break]:
 qexistsl [`t`,`G1`,`tn1`] >> qx_gen_tac `H` >> disch_tac >> BETA_TAC >>
 conj_tac
 >- (irule (CONJUNCT1 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >>
     first_assum ACCEPT_TAC) >>
 `Done H ee G1 tn1 t` by
   (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> Qmid H res ee G1 tn1 t`
      (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
    qpat_assum `res = INL b` (fn th => simp[NoAsms, Abbr `Qmid`, th]) >>
    strip_tac >> first_x_assum irule >> first_assum ACCEPT_TAC) >>
 qpat_assum `res = INL b` (fn th => simp[th])
QED

Resume for_storage_array_round_full[increment_continue]:
 `!H. valid_horizon cx st0 H ee.storage_trace ==> Ready H (a::rs) ee G1 tn1 t` by
   (qx_gen_tac `H` >> disch_tac >>
    qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> Qmid H res ee G1 tn1 t`
      (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
    qpat_assum `res = INL b` (fn th => simp[NoAsms, Abbr `Qmid`, th]) >>
    strip_tac >> first_x_assum irule >> first_assum ACCEPT_TAC) >>
 `allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t)` by
   (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> Ready H (a::rs) ee G1 tn1 t`
      (qspec_then `H0` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
    simp[NoAsms, Abbr `Ready`] >> strip_tac >>
    conj_tac
    >- (qpat_assum `ghost_inv_at (DF H0) lo d c0 cx ee G1 tn1 t` mp_tac >>
        simp[NoAsms,ghost_inv_at_def]) >>
    qpat_assum `Fr c0 ee t G1 tn1` mp_tac >> simp[NoAsms, Abbr `Fr`]) >>
 qspecl_then
   [`DF`,`lo`,`d`,`ctx`,`func`,`cx`,`st0`,`PG`,`explicit`,`c0`,`e0`,
    `sa0`,`s0`,`G0`,`tn0`,`tr`,`slot`,`dst`,`tyv`,`typ`,`bd`,`vs`,`len`,
    `nb`,`id`,`env`,`p`,`idx`,`cond`,`lvo`,`sd`,`stmts`,`si`,`sj'`,`sk`,`sl`,`out`]
   mp_tac for_storage_array_backedge_full >>
 map_every (fn q => qpat_assum q (fn th =>
   CONV_TAC (LAND_CONV (PURE_REWRITE_CONV
     [SYM (PURE_REWRITE_RULE [markerTheory.Abbrev_def] th)]))))
   [`Abbrev (Fr = _)`, `Abbrev (Inv = _)`, `Abbrev (Ready = _)`] >>
 (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
 disch_then (qspecl_then [`a`,`rs`,`ee`,`t`,`G1`,`tn1`] mp_tac) >>
 (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
 disch_then (qx_choose_then `u` (qx_choose_then `G2` (qx_choose_then `tn2` assume_tac))) >>
 qexistsl [`u`,`G2`,`tn2`] >> qx_gen_tac `H` >> disch_tac >>
 qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _ /\ Inv H rs ee G2 tn2 u`
   (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
 `~u.vs_halted` by
   (qpat_assum `Inv H rs ee G2 tn2 u` mp_tac >>
    simp[NoAsms, Abbr `Inv`] >> strip_tac >> first_assum ACCEPT_TAC) >>
 BETA_TAC >> qpat_assum `res = INL b` (fn th => simp[th])
QED

Finalise for_storage_array_round_full

(* Join the saved length, loop-local allocation and counter entry at the
   successful iterator endpoint. Only the compiler geometry is threaded
   across the three execution boundaries; their runtime packets are produced
   by the paths themselves. *)
Theorem for_storage_array_initial_full:
  !DF lo d ctx func cx c0 e0 sa0 s0 G0 tn0 tr slot tyv typ bd vs len nb id env
      p idx lvo saL sd sdecl sc bc st0 explicit PG entry cond bad good jid eid
      s G tn ee bb eb out ptr ann body.
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
         (\H ee s G tn.
            ?off.
              len = LENGTH vs /\ len <= bound_length bd /\
              vs =
              GENLIST
                (\j.
                   PlaceR
                     (StoragePlace tr
                        ((case bd of Fixed v => slot | Dynamic v1 => slot + 1w) +
                         n2w (j * type_slot_size tyv)) tyv)) len /\
              slot = n2w off /\
              MEM (StorageRoot tr off (ArrayTV tyv bd)) ee.storage_trace /\
              evaluate_type (get_tenv cx) typ = SOME tyv /\
              well_formed_type_value tyv /\
              lookup_scopes id ee.scopes = NONE /\ expr_sim_inv c0 cx env ee /\
              ce_locals_declared c0 env /\ locals_alloc_ok c0 env /\
              cenv_top_ext c0 c0 ee.scopes /\
              stmt_state_rel H ctx func c0 cx ee s /\
              storage_well_formed_on cx ee (FST H) /\
              ghost_inv_at (DF H) lo d c0 cx ee G tn s /\
              return_buf_frame d c0 sa0 s /\ ret_pc_ok c0 sa0 s /\
              (\c ee s G tn.
                 alloca_history func s /\
                 (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
                 s0.vs_alloca_next <= s.vs_alloca_next /\
                 (!x w.
                    not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
                    lookup_var x s = SOME w) /\
                 (!aid b.
                    FLOOKUP s0.vs_allocas aid = SOME b ==>
                    FLOOKUP s.vs_allocas aid = SOME b) /\
                 (!x. not_fresh_at sa0 x ==>
                      FLOOKUP G x = FLOOKUP G0 x /\
                      op_taint tn (Var x) = op_taint tn0 (Var x)) /\
                 alloca_frame c0 e0 sa0 s0 c ee s /\
                 !aid off sz i.
                   FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
                   aid < sa0.cs_next_id /\
                   (!name b sz'.
                      local_region c0 e0.scopes s0 name b sz' ==>
                      off + sz <= b \/ b + sz' <= off) /\ off <= i /\
                   i < off + sz /\ i IN tn.t_mem ==>
                   i IN tn0.t_mem) c0 ee s G tn) H ee s G tn) /\
    ~s.vs_halted /\ s.vs_current_bb = saL.cs_current_bb /\
    s.vs_inst_idx = LENGTH saL.cs_current_insts /\
    local_ptrs_reserved c0 sa0 /\
    (!x sz. c0.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
    (!x sz. c0.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
    (case bd of
       Fixed cap => len = cap /\ sd = saL /\ lvo = Lit (n2w cap)
     | Dynamic cap' =>
       compile_ptr_load c0.ce_is_ctor c0.ce_imm_alloca (slot_loc tr)
         ptr.ptr_operand saL = (lvo,sd) /\ lvo = Var out /\
       fn_has_code saL sd func /\ (!x. not_fresh_at sa0 x ==> x <> out) /\
       storage_holds cx tr (ArrayT typ bd)
         (PlaceR (StoragePlace tr slot (ArrayTV tyv bd))) slot ee s /\
       ptr_vv_ok cx (ArrayT typ bd)
         (PlaceR (StoragePlace tr slot (ArrayTV tyv bd)))
         (LocatedValue ann ptr) ee G tn s /\ ptr.ptr_location = slot_loc tr /\
       ptr.ptr_operand = Lit slot /\
       lookup_storage slot (get_storage cx ee tr) = n2w len) /\
    declare_local c0 id typ sd = (bc,sdecl) /\
    emit_local_alloca bc id sdecl = ((),sc) /\ c0.ce_alloca_locals /\
    p = STRING #"%" (toString sd.cs_next_var) /\
    nb = type_memory_bytes c0 typ /\
    FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) nb) /\
    fn_has_code sd sc func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved c0 sd /\ sa0.cs_next_var <= sd.cs_next_var /\
    (!x. lvo = Var x ==> x <> p) /\ nb < 2 ** 256 /\
    32 * type_slot_size tyv <= nb /\
    lookup_block sc.cs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sc.cs_current_insts) =
    SOME (mk_inst jid JMP [Label entry] []) /\
    lookup_block entry func.fn_blocks = SOME eb /\
    eb.bb_instructions =
    [mk_inst eid ASSIGN [Lit 0w] [idx]] ++
    (if case bd of Fixed v => F | Dynamic v1 => T then
       [mk_inst (eid + 1) GT [lvo; Lit (n2w (bound_length bd))] [bad];
        mk_inst (eid + 2) ISZERO [Var bad] [good];
        mk_inst (eid + 3) ASSERT [Var good] []]
     else []) ++
    [mk_inst
       (eid +
        LENGTH
          ([mk_inst eid ASSIGN [Lit 0w] [idx]] ++
           if case bd of Fixed v => F | Dynamic v1 => T then
             [mk_inst (eid + 1) GT [lvo; Lit (n2w (bound_length bd))] [bad];
              mk_inst (eid + 2) ISZERO [Var bad] [good];
              mk_inst (eid + 3) ASSERT [Var good] []]
           else [])) JMP [Label cond] []] /\ bound_length bd < 2 ** 256 /\
    (!x. not_fresh_at sa0 x ==>
         x NOTIN
         if case bd of Fixed v => F | Dynamic v1 => T then {idx; bad; good}
         else {idx}) /\
    p NOTIN
    (if case bd of Fixed v => F | Dynamic v1 => T then {idx; bad; good}
     else {idx}) /\
    (!x. lvo = Var x ==>
         x NOTIN
         if case bd of Fixed v => F | Dynamic v1 => T then {idx; bad; good}
         else {idx}) /\
    ((case bd of Fixed v => F | Dynamic v1 => T) ==>
     idx <> bad /\ idx <> good /\ bad <> good) ==>
    ?dst t G1 tn1. !H.
      valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
        (OK t,G1,tn1) /\
      (\dst H rs ee G tn s.
         ?k off.
           k <= len /\ len = LENGTH vs /\ len <= bound_length bd /\
           vs =
           GENLIST
             (\j.
                PlaceR
                  (StoragePlace tr
                     ((case bd of Fixed v => slot | Dynamic v1 => slot + 1w) +
                      n2w (j * type_slot_size tyv)) tyv)) len /\
           rs = DROP k vs /\ slot = n2w off /\
           MEM (StorageRoot tr off (ArrayTV tyv bd)) ee.storage_trace /\
           evaluate_type (get_tenv cx) typ = SOME tyv /\
           well_formed_type_value tyv /\ s.vs_current_bb = cond /\
           s.vs_inst_idx = 0 /\ ~s.vs_halted /\
           lookup_var idx s = SOME (n2w k) /\ FLOOKUP G idx = NONE /\
           op_taint tn (Var idx) = {} /\ eval_operand lvo s = SOME (n2w len) /\
           op_taint tn lvo = {} /\ op_prov G lvo = NONE /\
           eval_operand (Lit slot) s = SOME slot /\
           op_taint tn (Lit slot) = {} /\ lookup_var p s = SOME dst /\
           FLOOKUP s.vs_allocas sd.cs_next_id = SOME (w2n dst,nb) /\
           ptr_covers G tn p s nb /\ 32 * type_slot_size tyv <= nb /\
           w2n dst + nb < 2 ** 256 /\ w2n dst + nb <= s.vs_alloca_next /\
           (!name b sz.
              local_region c0 ee.scopes s name b sz ==>
              w2n dst + nb <= b \/ b + sz <= w2n dst) /\
           lookup_scopes id ee.scopes = NONE /\ expr_sim_inv c0 cx env ee /\
           ce_locals_declared c0 env /\ locals_alloc_ok c0 env /\
           cenv_top_ext c0 c0 ee.scopes /\
           stmt_state_rel H ctx func c0 cx ee s /\
           storage_well_formed_on cx ee (FST H) /\
           ghost_inv_at (DF H) lo d c0 cx ee G tn s /\
           return_buf_frame d c0 sa0 s /\ ret_pc_ok c0 sa0 s /\
           (k <> 0 ==> body_stmts_full_ok cx body) /\
           (\c ee s G tn.
              alloca_history func s /\
              (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
              s0.vs_alloca_next <= s.vs_alloca_next /\
              (!x w.
                 not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
                 lookup_var x s = SOME w) /\
              (!aid b.
                 FLOOKUP s0.vs_allocas aid = SOME b ==>
                 FLOOKUP s.vs_allocas aid = SOME b) /\
              (!x. not_fresh_at sa0 x ==>
                   FLOOKUP G x = FLOOKUP G0 x /\
                   op_taint tn (Var x) = op_taint tn0 (Var x)) /\
              alloca_frame c0 e0 sa0 s0 c ee s /\
              !aid off sz i.
                FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
                aid < sa0.cs_next_id /\
                (!name b sz'.
                   local_region c0 e0.scopes s0 name b sz' ==>
                   off + sz <= b \/ b + sz' <= off) /\ off <= i /\
                i < off + sz /\ i IN tn.t_mem ==>
                i IN tn0.t_mem) c0 ee s G tn) dst H vs ee G1 tn1 t
Proof
  rpt gen_tac >>
  abbrev_lambda_tac "Fr" 5 0 `alloca_history func s /\ _` >>
  abbrev_lambda_tac "Base" 5 1 `len = LENGTH vs /\ _` >>
  abbrev_lambda_tac "Inv" 7 2 `k <= len /\ _` >>
  qpat_abbrev_tac `dyn = (case bd of Fixed _ => F | Dynamic _ => T)` >>
  qpat_abbrev_tac `Written = (if dyn then {idx;bad;good} else {idx})` >>
  qpat_abbrev_tac `code = [mk_inst eid ASSIGN [Lit 0w] [idx]] ++ _` >>
  rpt strip_tac >>
  Cases_on `?H. valid_horizon cx st0 H ee.storage_trace`
  >- (qpat_x_assum `?H. valid_horizon _ _ H _` (qx_choose_then `H0` assume_tac) >>
      `Base H0 ee s G tn` by
        (qpat_assum `!H. valid_horizon _ _ H _ ==> Base H _ _ _ _` irule >>
         first_assum ACCEPT_TAC) >>
      suspend "initial_length") >>
  qexistsl_tac [`0w`, `s`, `G`, `tn`] >>
  qpat_x_assum `~(?H. valid_horizon _ _ H _)` (mp_tac o REWRITE_RULE [NOT_EXISTS_THM]) >>
  simp[]
QED

Resume for_storage_array_initial_full[initial_length]:
  `len <= bound_length bd /\ evaluate_type (get_tenv cx) typ = SOME tyv /\
   allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s)` by
    (qpat_assum `Base H0 ee s G tn` mp_tac >>
     simp_tac pure_ss [Abbr `Base`, Abbr `Fr`] >> BETA_TAC >> strip_tac >>
     qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[ghost_inv_at_def]) >>
  `len < 2**256` by decide_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> Base H ee s G tn` mp_tac >>
  simp_tac pure_ss [Abbr `Base`, Abbr `Fr`] >> BETA_TAC >> disch_tac >>
  qmatch_asmsub_rename_tac `ptr0.ptr_operand` >>
  `(case bd of
      Fixed cap => len = cap /\ sd = saL /\ lvo = Lit (n2w cap)
    | Dynamic cap =>
      compile_ptr_load c0.ce_is_ctor c0.ce_imm_alloca (slot_loc tr)
        ptr0.ptr_operand saL = (lvo,sd) /\
      lvo = Var out /\ fn_has_code saL sd func /\
      (!x. not_fresh_at sa0 x ==> x <> out) /\
      evaluate_type (get_tenv cx) typ = SOME tyv /\
      storage_holds cx tr (ArrayT typ bd)
        (PlaceR (StoragePlace tr slot (ArrayTV tyv bd))) slot ee s /\
      ptr_vv_ok cx (ArrayT typ bd)
        (PlaceR (StoragePlace tr slot (ArrayTV tyv bd)))
        (LocatedValue ann ptr0) ee G tn s /\
      ptr0.ptr_location = slot_loc tr /\
      eval_operand ptr0.ptr_operand s = SOME slot /\ op_taint tn ptr0.ptr_operand = {} /\
      lookup_storage slot (get_storage cx ee tr) = n2w len /\
      allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s))` by
    (qpat_x_assum `case bd of Fixed _ => _ | Dynamic _ => _` mp_tac >>
     Cases_on `bd` >> simp_tac (srw_ss()) [eval_operand_def, op_taint_def] >>
     strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule (SIMP_RULE pure_ss [LET_THM] for_storage_array_length_full) >>
  disch_then (drule_at (Pos List.last)) >>
  disch_then (qspecl_then [`explicit`, `PG`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `sl` (qx_choose_then `GL` (qx_choose_then `tnL` STRIP_ASSUME_TAC))) >>
  suspend "initial_allocation"
QED

Resume for_storage_array_initial_full[initial_allocation]:
  `allocas_from lo sl /\ lo <= sl.vs_alloca_next` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ (OK sl,GL,tnL) /\ _`
       (qspec_then `H0` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> BETA_TAC >>
     disch_then (CONJUNCTS_THEN2 kall_tac (CHOOSE_THEN STRIP_ASSUME_TAC)) >>
     qpat_x_assum `ghost_inv_at _ _ _ _ _ _ GL tnL sl` mp_tac >>
     simp[ghost_inv_at_def]) >>
  (* Move the captured root binder across only the independent Base fields. *)
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ (OK sl,GL,tnL) /\ _`
    (assume_tac o
     CONV_RULE (QUANT_CONV (RAND_CONV
       (HO_REWR_CONV RIGHT_EXISTS_AND_THM THENC RAND_CONV
        (HO_REWR_CONV RIGHT_EXISTS_AND_THM THENC RAND_CONV
         (HO_REWR_CONV RIGHT_EXISTS_AND_THM THENC RAND_CONV
          (QUANT_CONV (REWR_CONV CONJ_ASSOC) THENC
           HO_REWR_CONV LEFT_EXISTS_AND_THM)))))) o cj 2 o BETA_RULE) >>
  drule (BETA_RULE (SIMP_RULE pure_ss [LET_THM] for_storage_array_allocate_full)) >>
  (* The guarded Base precedes the three saved-length conjuncts. *)
  disch_then (fn th => pop_assum
    (mp_then (Pos (fn cs => List.nth (cs,List.length cs - 4))) mp_tac th)) >>
  disch_then (qspecl_then [`explicit`, `PG`] drule) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME (PtrVar (Var _) _)`)) >>
  disch_then (drule_at (Pat `eval_operand _ sl = SOME (n2w len)`)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qspecl_then [`explicit`, `PG`]
    (qx_choose_then `dst` (qx_choose_then `uA` (qx_choose_then `sA`
      (qx_choose_then `GA` (qx_choose_then `tnA` STRIP_ASSUME_TAC)))))) >>
  suspend "initial_entry"
QED

Resume for_storage_array_initial_full[initial_entry]:
  qpat_assum `!H. valid_horizon _ _ H _ ==>
       gas_origin_ptr_path _ (sl,GL,tnL) [] (OK sA,GA,tnA) /\ _`
    (qspec_then `H0` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then STRIP_ASSUME_TAC >>
  `!lbl. lvo <> Label lbl` by
    (qpat_assum `case bd of
        Fixed _ => _ /\ _ /\ lvo = Lit _ | Dynamic _ => _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `bd` >> simp[] >>
     strip_tac >> simp[]) >>
  (* Restore the root witness scope expected by the entry boundary. *)
  qpat_assum `!H. valid_horizon _ _ H _ ==>
       gas_origin_ptr_path _ (sl,GL,tnL) [] (OK sA,GA,tnA) /\ _`
    (assume_tac o CONV_RULE (QUANT_CONV (RAND_CONV
       (RAND_CONV (RAND_CONV (RAND_CONV
         (HO_REWR_CONV (GSYM LEFT_EXISTS_AND_THM) THENC
          QUANT_CONV (REWR_CONV (GSYM CONJ_ASSOC))) THENC
         HO_REWR_CONV (GSYM RIGHT_EXISTS_AND_THM)) THENC
        HO_REWR_CONV (GSYM RIGHT_EXISTS_AND_THM)) THENC
       HO_REWR_CONV (GSYM RIGHT_EXISTS_AND_THM)))) o
     underAIs (CONJUNCT1 o CONJUNCT2)) >>
  `lookup_block sA.vs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb sA.vs_inst_idx = SOME (mk_inst jid JMP [Label entry] [])` by
    simp[] >>
  drule (BETA_RULE (SIMP_RULE pure_ss [LET_THM] for_storage_array_entry_full)) >>
  disch_then (drule_at (Pat `get_instruction _ sA.vs_inst_idx = _`)) >>
  (* Match the guarded Base before the eight compiler-side premises. *)
  disch_then (fn th => qpat_assum `!H. valid_horizon _ _ H _ ==> ?off. _`
    (mp_then (Pos (fn cs => List.nth (cs,List.length cs - 9))) mp_tac th)) >>
  disch_then (drule_at (Pat `eval_operand _ sA = SOME (n2w len)`)) >>
  disch_then (drule_at (Pat `lookup_var _ sA = SOME dst`)) >>
  disch_then (drule_at (Pat `FLOOKUP sA.vs_allocas _ = _`)) >>
  disch_then (drule_at (Pat `lookup_block entry func.fn_blocks = _`)) >>
  disch_then (fn th =>
    qpat_assum `eb.bb_instructions = _` mp_tac >>
    simp_tac pure_ss [Abbr `code`, Abbr `dyn`] >>
    disch_then (mp_then (Pat `eb.bb_instructions = _`) mp_tac th)) >>
  disch_then (qspecl_then [`explicit`, `PG`] mp_tac) >>
  simp_tac pure_ss [Abbr `Written`] >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `t` (qx_choose_then `G1` (qx_choose_then `tn1`
    STRIP_ASSUME_TAC))) >>
  suspend "initial_compose"
QED

Resume for_storage_array_initial_full[initial_compose]:
  qexistsl_tac [`dst`, `t`, `G1`, `tn1`] >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==>
       gas_origin_ptr_path _ (s,G,tn) [] (OK sl,GL,tnL) /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (assume_tac o CONJUNCT1) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==>
       gas_origin_ptr_path _ (sl,GL,tnL) [] (OK sA,GA,tnA) /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (assume_tac o CONJUNCT1) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==>
       gas_origin_ptr_path _ (sA,GA,tnA) [] (OK t,G1,tn1) /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 (qx_choose_then `offT` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC)) >>
  conj_tac
  >- (`gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
         (s,G,tn) [] (OK sA,GA,tnA)` by
        (qpat_assum `gas_origin_ptr_path _ (s,G,tn) [] (OK sl,GL,tnL)`
           (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
         disch_then (qspecl_then [`sl`, `GL`, `tnL`, `[]`] mp_tac) >>
         simp[NoAsms] >> disch_then irule >> first_assum ACCEPT_TAC) >>
      qpat_assum `gas_origin_ptr_path _ (s,G,tn) [] (OK sA,GA,tnA)`
        (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
      disch_then (qspecl_then [`sA`, `GA`, `tnA`, `[]`] mp_tac) >>
      simp[NoAsms] >> disch_then irule >> first_assum ACCEPT_TAC) >>
  simp_tac pure_ss [Abbr `Inv`] >> BETA_TAC >>
  qexistsl_tac [`0`, `offT`] >>
  rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC, simp[NoAsms, eval_operand_def, op_taint_def]]
QED

Finalise for_storage_array_initial_full

Theorem compile_for_storage_array_frag_full:
  !cx id typ bd nid n body DF lo d PG tops bindings ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
    (!c0 e0 sa0 s0 c1 e1 s1 sa1 c2 e2 s2.
       alloca_frame c0 e0 sa0 s0 c1 e1 s1 /\
       alloca_frame c1 e1 sa1 s1 c2 e2 s2 /\
       sa0.cs_next_id <= sa1.cs_next_id /\
       (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
         FLOOKUP s1.vs_allocas aid = SOME b) ==>
       alloca_frame c0 e0 sa0 s0 c2 e2 s2) /\
    (!c0 e0 sa0 s0 c1 e1 s1 sa1 tn0 tn1 tn2.
       alloca_frame c0 e0 sa0 s0 c1 e1 s1 /\
       sa0.cs_next_id <= sa1.cs_next_id /\
       (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
         FLOOKUP s1.vs_allocas aid = SOME b) /\
       (!aid off sz i.
          FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
          aid < sa0.cs_next_id /\
          (!name b sz'. local_region c0 e0.scopes s0 name b sz' ==>
            off+sz <= b \/ b+sz' <= off) /\
          off<=i /\ i<off+sz /\ i IN tn1.t_mem ==> i IN tn0.t_mem) /\
       (!aid off sz i.
          FLOOKUP s1.vs_allocas aid = SOME (off,sz) /\
          aid < sa1.cs_next_id /\
          (!name b sz'. local_region c1 e1.scopes s1 name b sz' ==>
            off+sz <= b \/ b+sz' <= off) /\
          off<=i /\ i<off+sz /\ i IN tn2.t_mem ==> i IN tn1.t_mem) ==>
       !aid off sz i.
          FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
          aid < sa0.cs_next_id /\
          (!name b sz'. local_region c0 e0.scopes s0 name b sz' ==>
            off+sz <= b \/ b+sz' <= off) /\
          off<=i /\ i<off+sz /\ i IN tn2.t_mem ==> i IN tn0.t_mem) /\
    (!H cc ee res r sc g.
       halt_exit H cc ee res r ==>
       halt_exit H cc (ee with <|scopes := sc; gas_obs := g|>) res r) /\
    supported_storage_value tops nid (ArrayT typ bd) /\
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
         (INL tyv,t) /\
       eval_iterator cx (Array (TopLevelName (ArrayT typ bd) nid)) s'3' =
         (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
         (INL x,t'') ==>
       body_for_full_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
         (INL tyv,t) ==>
       body_iterator_full_ok cx (Array (TopLevelName (ArrayT typ bd) nid))) /\
    body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
    supported_stmt tops bindings
      (For id typ (Array (TopLevelName (ArrayT typ bd) nid)) n body) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (For id typ (Array (TopLevelName (ArrayT typ bd) nid)) n body) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty
      (For id typ (Array (TopLevelName (ArrayT typ bd) nid)) n body) = SOME env' /\
    stmt_exprs_ok cenv
      (For id typ (Array (TopLevelName (ArrayT typ bd) nid)) n body) /\
    call_evaluation_safe cx (int_calls_stmt
      (For id typ (Array (TopLevelName (ArrayT typ bd) nid)) n body)) /\
    frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cx RetQ cenv ret_ty ==>
    stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
        (For id typ (Array (TopLevelName (ArrayT typ bd) nid)) n body))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt
        (For id typ (Array (TopLevelName (ArrayT typ bd) nid)) n body)))
      (eval_stmt cx
        (For id typ (Array (TopLevelName (ArrayT typ bd) nid)) n body)) es
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ (For _ _ _ _ _) _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  qpat_x_assum `cenv = cenv'` (SUBST_ALL_TAC o SYM) >>
  `compile_stmt cenv lctx ret_ty
      (For id typ (Array (TopLevelName (ArrayT typ bd) nid)) n body') sa =
     ((),sb)` by gvs[] >>
  `cenv.ce_alloca_locals /\ get_module_code cx NONE = SOME tops /\
   ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by
    (qpat_assum `body_inv tops ctx cenv cx`
       (mp_tac o REWRITE_RULE [bodySimTheory.body_inv_def]) >> simp[]) >>
  drule_then strip_assume_tac bodyFullForFactsTheory.type_stmt_for_projection >>
  `?tr slot name. nid = (NONE,name) /\
     FLOOKUP cenv.ce_module_vars nid =
       SOME (if tr then TransientLoc slot else StorageLoc slot) /\
     find_var_decl_by_name name tops = SOME (StorageVarDecl tr (ArrayT typ bd), name)` by
    (PairCases_on `nid` >>
     qpat_x_assum `supported_storage_value _ _ _` mp_tac >>
     simp[supported_storage_value_def] >>
     Cases_on `supported_variable_decl tops (nid0,nid1)` >> simp[] >>
     rename1 `supported_variable_decl _ _ = SOME info` >>
     PairCases_on `info` >> Cases_on `info1` >> Cases_on `info3` >> simp[] >>
     strip_tac >>
     drule build_compile_env_storage_binding >> disch_then drule >>
     simp[build_compile_env_module_vars] >> strip_tac >>
     drule whitelistVisibilityTheory.supported_variable_decl_storage_binding >>
     disch_then drule >> simp[] >> strip_tac >>
     qpat_assum `body_inv tops ctx cenv cx`
       (mp_tac o REWRITE_RULE [bodySimTheory.body_inv_def,bodySimTheory.cenv_module_pins_def]) >>
     strip_tac >> gvs[] >> metis_tac[]) >>
  drule_all_then strip_assume_tac for_storage_array_code >>
  `env_consistent env cx es` by
    fs[exprSimHypsDefsTheory.expr_sim_inv_def] >>
  `well_typed_expr env (TopLevelName (ArrayT typ bd) (NONE,name))` by
    fs[vyperTypeSystemTheory.well_typed_iterator_def] >>
  `FLOOKUP env.toplevel_vtypes (NONE,name) = SOME (Type (ArrayT typ bd))` by
    (irule vyperTypeGlobalLookupSoundnessTheory.TopLevelName_toplevel_vtypes_Type >>
     simp[] >> qexistsl [`cx`, `es`] >> simp[]) >>
  `FLOOKUP env.bare_globals (NONE,name) = NONE` by
    (Cases_on `FLOOKUP env.bare_globals (NONE,name)` >> simp[] >>
     drule_all_then strip_assume_tac
       vyperTypeInvariantsTheory.env_consistent_bare_global_find_NONE >> gvs[]) >>
  `?off tv. lookup_var_slot_from_layout cx tr NONE name = SOME off /\
            evaluate_type (get_tenv cx) (ArrayT typ bd) = SOME tv` by
    (drule_all_then strip_assume_tac env_consistent_toplevel_storage_static >>
     gvs[optionTheory.IS_SOME_EXISTS]) >>
  drule_then strip_assume_tac vyperTypeValuesTheory.evaluate_type_ArrayT_cases >>
  `!tail. eval_expr cx (TopLevelName (ArrayT typ bd) (NONE,name))
      (es with gas_obs := tail) =
    (INL (PlaceR (StoragePlace tr (n2w off) (ArrayTV elem_tv bd))),
     es with <|storage_trace := es.storage_trace ++ [StorageRoot tr off (ArrayTV elem_tv bd)];
               gas_obs := tail|>)` by
    simp[Once vyperInterpreterTheory.evaluate_def, lookup_global_def, bind_def,
         ignore_bind_def, record_storage_event_def, lift_option_type_def,
         return_def, raise_def] >>
  qabbrev_tac `ee = es with storage_trace :=
    es.storage_trace ++ [StorageRoot tr off (ArrayTV elem_tv bd)]` >>
  qabbrev_tac `alen = case bd of Fixed cap => cap | Dynamic cap =>
    w2n (lookup_storage (n2w off) (get_storage cx es tr))` >>
  qabbrev_tac `vs = GENLIST (\j. PlaceR (StoragePlace tr
    ((case bd of Fixed cap => n2w off | Dynamic cap => n2w off+1w) +
     n2w (j * type_slot_size elem_tv)) elem_tv)) alen` >>
  `LENGTH vs = alen` by simp[Abbr `vs`] >>
  `!tail. eval_iterator cx (Array (TopLevelName (ArrayT typ bd) (NONE,name)))
      (es with gas_obs := tail) =
    (if compatible_bound bd alen then INL vs
     else INR (Error (RuntimeError "For storage array length")),
     ee with gas_obs := tail)` by
    (gen_tac >> simp[Once vyperInterpreterTheory.evaluate_def] >>
     simp[bind_def, vyperInterpreterTheory.array_iterator_results_storage] >>
     Cases_on `bd` >> Cases_on `tr` >>
     simp[Abbr `ee`, Abbr `alen`, Abbr `vs`, result_array_length_def,
          get_storage_backend_eq, get_storage_def, bind_def, ignore_bind_def,
          check_def, assert_def, return_def] >>
     IF_CASES_TAC >> simp[]) >>
  `!tail. eval_stmt cx (For id typ (Array (TopLevelName (ArrayT typ bd) nid)) n body')
      (es with gas_obs := tail) =
    if compatible_bound bd alen /\ compatible_bound (Dynamic n) alen then
      eval_for cx elem_tv id body' vs (ee with gas_obs := tail)
    else (INR (Error (RuntimeError
        (if compatible_bound bd alen then "For too long" else "For storage array length"))),
      ee with gas_obs := tail)` by
    (gen_tac >> simp[Once vyperInterpreterTheory.evaluate_def, bind_def,
        lift_option_type_def, return_def] >>
     Cases_on `compatible_bound bd alen` >> Cases_on `compatible_bound (Dynamic n) alen` >>
     simp[bind_def, ignore_bind_def, check_def, assert_def]) >>
  reverse (Cases_on `storage_trace_domain cx st0 ee.storage_trace`)
  >- (irule gas_outcome_full_bad_nil >> simp[] >> gen_tac >>
      Cases_on `compatible_bound bd alen /\ compatible_bound (Dynamic n) alen` >> simp[] >>
      Cases_on `eval_for cx elem_tv id body' vs (ee with gas_obs := tail)` >> simp[] >>
      `storage_trace_frame (eval_for cx elem_tv id body' vs)` by
        simp[cj 4 evaluate_storage_trace_frame] >>
      drule_all_then strip_assume_tac storage_trace_frame_prefix >>
      fs[] >> metis_tac[storage_trace_domain_prefix]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) es.storage_trace` by
    (fs[Abbr `ee`] >> drule_then ACCEPT_TAC valid_horizon_append) >>
  `slot = n2w off` by
    (qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
       (qspec_then `storage_trace_horizon ee.storage_trace`
          (drule_then strip_assume_tac)) >>
     drule_then strip_assume_tac stateRelProjTheory.stmt_state_rel_vars_rels >>
     `FLOOKUP cenv.ce_module_vars (NONE,name) =
         SOME (if tr then TransientLoc (n2w off) else StorageLoc (n2w off))` by
       (irule exprSimTopLevelPropsTheory.toplevel_storage_ce_vars >>
        qexistsl [`cx`, `name`, `tops`, `ArrayT typ bd`] >> simp[]) >>
     Cases_on `tr` >> gvs[]) >>
  `MEM (StorageRoot tr off (ArrayTV elem_tv bd)) ee.storage_trace` by
    simp[Abbr `ee`, MEM_APPEND] >>
  `MEM (tr,slot,ArrayTV elem_tv bd)
       (FST (storage_trace_horizon ee.storage_trace))` by
    (simp[] >> irule vyperFiniteStoragePreservationTheory.storage_observations_ok_root >>
     qexistsl [`cx`, `ee.storage_trace`] >>
     fs[valid_horizon_def]) >>
  `slots_in_range (get_storage cx es tr) (w2n slot) (ArrayTV elem_tv bd)` by
    (qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
       (qspec_then `storage_trace_horizon ee.storage_trace`
          (drule_then strip_assume_tac)) >>
     fs[storage_well_formed_on_def]) >>
  `compatible_bound bd alen /\ alen <= bound_length bd` by
    (Cases_on `bd` >>
     simp[Abbr `alen`, vyperValueTheory.compatible_bound_def, bound_length_def] >>
     drule_then mp_tac pop_array_length_bound >> simp[]) >>
  `bound_length bd <= n` by
    (drule_then strip_assume_tac bodyFullForFactsTheory.supported_stmt_for_projection >>
     fs[supportedStmtsTheory.supported_iterator_def]) >>
  `compatible_bound (Dynamic n) alen` by
    simp[vyperValueTheory.compatible_bound_def] >>
  `erase_storage_trace ee = erase_storage_trace es` by
    simp[Abbr `ee`, erase_storage_trace_def] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func cenv cx ee s0 /\
     storage_well_formed_on cx ee (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx ee G0 tn0 s0` by
    (qx_gen_tac `H` >> strip_tac >>
     `valid_horizon cx st0 H es.storage_trace` by
       (fs[Abbr `ee`] >> drule_then ACCEPT_TAC valid_horizon_append) >>
     qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     conj_tac
     >- (drule_then (fn th => once_rewrite_tac[th]) stmt_state_rel_erasure >>
         first_assum ACCEPT_TAC) >>
     fs[Abbr `ee`, storage_well_formed_on_def]) >>
  `lookup_scopes id ee.scopes = NONE` by
    (simp[Abbr `ee`] >> Cases_on `lookup_scopes id es.scopes` >> simp[] >>
     fs[vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_scopes_consistent_def, FLOOKUP_DEF]) >>
  `alloca_frame cenv es sa s0 cenv ee s0` by
    (irule alloca_frame_same >> simp[Abbr `ee`]) >>
  `expr_sim_inv cenv cx env ee` by
    simp[Abbr `ee`, exprSimHypsDefsTheory.expr_sim_inv_storage_trace] >>
  `well_formed_type_value elem_tv` by
    (irule vyperTypeValuesTheory.evaluate_type_well_formed_type_value >>
     qexistsl [`get_tenv cx`, `typ`] >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> ?r.
     alen = LENGTH vs /\ alen <= bound_length bd /\
     vs = GENLIST (\j. PlaceR (StoragePlace tr
       ((case bd of Fixed cap => slot | Dynamic cap => slot+1w) +
         n2w (j * type_slot_size elem_tv)) elem_tv)) alen /\
     slot = n2w r /\ MEM (StorageRoot tr r (ArrayTV elem_tv bd)) ee.storage_trace /\
     evaluate_type (get_tenv cx) typ = SOME elem_tv /\
     well_formed_type_value elem_tv /\ lookup_scopes id ee.scopes = NONE /\
     expr_sim_inv cenv cx env ee /\ ce_locals_declared cenv env /\
     locals_alloc_ok cenv env /\ cenv_top_ext cenv cenv ee.scopes /\
     stmt_state_rel H ctx func cenv cx ee s0 /\
     storage_well_formed_on cx ee (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx ee G0 tn0 s0 /\
     return_buf_frame d cenv sa s0 /\ ret_pc_ok cenv sa s0 /\
     alloca_history func s0 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
     alloca_frame cenv es sa s0 cenv ee s0` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     qexists_tac `off` >> simp[cenv_top_ext_refl, Abbr `vs`]) >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `MEM (tr,slot,ArrayTV elem_tv bd) (FST H0)` by simp[Abbr `H0`] >>
  `storage_place_observed H0 (StoragePlace tr slot (ArrayTV elem_tv bd))` by
    (rewrite_tac[storage_place_observed_def] >>
     qexistsl [`slot`, `ArrayTV elem_tv bd`, `[]`, `0`] >>
     simp[storage_subregion_def, wordsTheory.WORD_ADD_0]) >>
  `!cap. bd = Dynamic cap ==>
     storage_holds cx tr (ArrayT typ bd)
       (PlaceR (StoragePlace tr slot (ArrayTV elem_tv bd))) slot ee s0 /\
     ptr_vv_ok cx (ArrayT typ bd)
       (PlaceR (StoragePlace tr slot (ArrayTV elem_tv bd)))
       (LocatedValue (ArrayT typ bd) (mk_ptr (Lit slot) (slot_loc tr))) ee G0 tn0 s0 /\
     lookup_storage slot (get_storage cx ee tr) = n2w alen` by
    (gen_tac >> strip_tac >>
     `0 < type_slot_size (ArrayTV elem_tv bd)` by simp[vyperValueTheory.type_slot_size_def] >>
     `regions_consistent (FST H0)` by fs[Abbr `H0`, valid_horizon_def] >>
     `valid_horizon cx st0 H0 ee.storage_trace` by simp[Abbr `H0`] >>
     qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (qspec_then `H0` (drule_then strip_assume_tac)) >>
     `evaluate_type (get_tenv cx) (ArrayT typ bd) = SOME (ArrayTV elem_tv bd)` by simp[] >>
     `well_formed_type_value (ArrayTV elem_tv bd)` by
       (irule vyperTypeValuesTheory.evaluate_type_well_formed_type_value >>
        qexistsl [`get_tenv cx`, `ArrayT typ bd`] >> simp[]) >>
     conj_tac >- (drule_all_then ACCEPT_TAC for_storage_current_child_holds) >>
     conj_tac
     >- (`(mk_ptr (Lit slot) (slot_loc tr)).ptr_location = slot_loc tr /\
          eval_operand (mk_ptr (Lit slot) (slot_loc tr)).ptr_operand s0 = SOME slot /\
          op_taint tn0 (mk_ptr (Lit slot) (slot_loc tr)).ptr_operand = {}` by
           simp[mk_ptr_def, eval_operand_def, op_taint_def] >>
         `dead_lo_ok H0 (DF H0) lo cenv cx` by simp[] >>
         drule_all_then MATCH_ACCEPT_TAC for_storage_current_child_ptr) >>
     simp[Abbr `alen`, Abbr `ee`, get_storage_def]) >>
  drule_then strip_assume_tac for_storage_length_geometry >>
  `(case bd of
      Fixed cap => alen = cap /\ sd = sa /\ lvo = Lit (n2w cap)
    | Dynamic cap =>
      compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca (slot_loc tr)
        (mk_ptr (Lit slot) (slot_loc tr)).ptr_operand sa = (lvo,sd) /\
      lvo = Var (STRING #"%" (toString sa.cs_next_var)) /\ fn_has_code sa sd func /\
      (!x. not_fresh_at sa x ==> x <> STRING #"%" (toString sa.cs_next_var)) /\
      storage_holds cx tr (ArrayT typ bd)
        (PlaceR (StoragePlace tr slot (ArrayTV elem_tv bd))) slot ee s0 /\
      ptr_vv_ok cx (ArrayT typ bd)
        (PlaceR (StoragePlace tr slot (ArrayTV elem_tv bd)))
        (LocatedValue (ArrayT typ bd) (mk_ptr (Lit slot) (slot_loc tr))) ee G0 tn0 s0 /\
      (mk_ptr (Lit slot) (slot_loc tr)).ptr_location = slot_loc tr /\
      (mk_ptr (Lit slot) (slot_loc tr)).ptr_operand = Lit slot /\
      lookup_storage slot (get_storage cx ee tr) = n2w alen)` by
    ((Cases_on `bd` >> fs[Abbr `alen`, mk_ptr_def, slot_loc_def,
                        not_fresh_at_def] >> (metis_tac[Abbr `alen`, mk_ptr_def, slot_loc_def, not_fresh_at_def]))) >>
  `sa.cs_next_var <= sd.cs_next_var` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv sd` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sa` >> simp[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    fs[ret_pc_ok_def] >>
  `!x. lvo = Var x ==> x <> p` by
    (gen_tac >> strip_tac >>
     `not_fresh_at sd x` by (qpat_assum `!x. lvo = Var x ==> _` irule >> simp[]) >>
     fs[not_fresh_at_def]) >>
  (* The allocated loop cell is the first instruction after the saved
     length. The jump belongs to the same block but is outside this cut. *)
  qabbrev_tac `sdecl = sd with cs_next_var := sd.cs_next_var+1` >>
  qabbrev_tac `nb = type_memory_bytes cenv typ` >>
  qabbrev_tac `ai = mk_inst sd.cs_next_id ALLOCA [Lit (n2w nb)] [p]` >>
  qabbrev_tac `sc = sdecl with <|cs_next_id := sd.cs_next_id+1;
                                  cs_current_insts := sd.cs_current_insts ++ [ai]|>` >>
  `declare_local cenv id typ sd = (bc,sdecl)` by simp[Abbr `sdecl`] >>
  `emit_local_alloca bc id sdecl = ((),sc)` by
    simp[emit_local_alloca_def, emit_inst_def, fresh_id_def, emit_def,
         comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM,
         Abbr `sc`, Abbr `sdecl`, Abbr `ai`, Abbr `nb`] >>
  qabbrev_tac `dbb = <|bb_label := sd.cs_current_bb;
      bb_instructions := sd.cs_current_insts ++ [ai;mk_inst (sd.cs_next_id+1) JMP [Label entry] []]|>` >>
  `lookup_block sd.cs_current_bb func.fn_blocks = SOME dbb` by
    simp[Abbr `dbb`, Abbr `ai`, Abbr `nb`] >>
  `sc.cs_current_bb = sd.cs_current_bb /\ sc.cs_blocks = sd.cs_blocks /\
   sc.cs_current_insts = sd.cs_current_insts ++ [ai]` by
    simp[Abbr `sc`, Abbr `sdecl`] >>
  `fn_has_code sd sc func` by
    (simp[fn_has_code_def, emitted_blocks_def] >> qexists_tac `dbb` >>
     conj_tac
     >- ((qpat_assum `lookup_block sd.cs_current_bb func.fn_blocks = SOME dbb` mp_tac >>
         simp[] >> (metis_tac[]))) >>
     simp[Abbr `dbb`]) >>
  `get_instruction dbb (LENGTH sc.cs_current_insts) =
   SOME (mk_inst (sd.cs_next_id+1) JMP [Label entry] [])` by
    simp[Abbr `dbb`, get_instruction_def, EL_LENGTH_APPEND_1] >>
  `nb < 2**64` by
    (qpat_assum `stmt_exprs_ok cenv (For _ _ _ _ _)`
       (mp_tac o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [stmt_exprs_ok_def]) >>
     simp[Once allocLimitsTheory.alloc_limits_stmt_def, Abbr `nb`]) >>
  `type_memory_bytes cenv typ = 32 * type_slot_size elem_tv` by
    (irule (cj 2 for_storage_element_layout) >> qexistsl [`cx`,`env`,`ee`] >> simp[]) >>
  `nb = 32 * type_slot_size elem_tv` by simp[Abbr `nb`] >>
  `nb < 2**256` by
    (irule arithmeticTheory.LESS_TRANS >> qexists_tac `2**64` >> simp[]) >>
  `bound_length bd < 2**256` by
    (`bound_length bd < dimword (:256)` suffices_by simp[wordsTheory.dimword_def] >>
     drule typedMemoryCopyTheory.typed_copy_array_count_bound >> simp[]) >>
  qabbrev_tac `eid = sd.cs_next_id + 2` >>
  qabbrev_tac `bad = STRING #"%" (toString (sd.cs_next_var+2))` >>
  qabbrev_tac `good = STRING #"%" (toString (sd.cs_next_var+3))` >>
  qabbrev_tac `dyn = case bd of Fixed cap => F | Dynamic cap => T` >>
  qabbrev_tac `code = [mk_inst eid ASSIGN [Lit 0w] [idx]] ++
    (if dyn then [mk_inst (eid+1) GT [lvo;Lit (n2w (bound_length bd))] [bad];
                  mk_inst (eid+2) ISZERO [Var bad] [good];
                  mk_inst (eid+3) ASSERT [Var good] []] else [])` >>
  qabbrev_tac `eb = <|bb_label := entry;
    bb_instructions := code ++ [mk_inst (eid + LENGTH code) JMP [Label cond] []]|>` >>
  `lookup_block entry func.fn_blocks = SOME eb` by
    (Cases_on `bd` >> simp[Abbr `eb`, Abbr `code`, Abbr `eid`, Abbr `bad`,
                           Abbr `good`, Abbr `dyn`]) >>
  `eb.bb_instructions = code ++ [mk_inst (eid + LENGTH code) JMP [Label cond] []]` by
    simp[Abbr `eb`] >>
  qabbrev_tac `Written = if dyn then {idx;bad;good} else {idx}` >>
  `(!x. not_fresh_at sa x ==> x NOTIN Written) /\ p NOTIN Written /\
   (!x. lvo = Var x ==> x NOTIN Written) /\ (dyn ==> idx <> bad /\ idx <> good /\ bad <> good)` by
    (conj_tac
     >- (qx_gen_tac `x` >> strip_tac >>
         qpat_assum `not_fresh_at sa x` (strip_assume_tac o REWRITE_RULE [not_fresh_at_def]) >>
         Cases_on `dyn` >> simp[Abbr `Written`, Abbr `bad`, Abbr `good`] >>
         rpt conj_tac >> first_assum irule >> simp[]) >>
     conj_tac
     >- (Cases_on `dyn` >> simp[Abbr `Written`, Abbr `bad`, Abbr `good`]) >>
     conj_tac
     >- (qx_gen_tac `x` >> strip_tac >>
         `not_fresh_at sd x` by
           (qpat_assum `!x. lvo = Var x ==> not_fresh_at sd x` irule >> simp[]) >>
         pop_assum (strip_assume_tac o REWRITE_RULE [not_fresh_at_def]) >>
         Cases_on `dyn` >> simp[Abbr `Written`, Abbr `bad`, Abbr `good`] >>
         rpt conj_tac >> first_assum irule >> simp[]) >>
     simp[Abbr `bad`, Abbr `good`]) >>
  qabbrev_tac `explicit = gas_explicit_sites ctx shadow_ctx` >>
  qabbrev_tac `Fr = (\c ei s G tn.
    alloca_history func s /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa x ==>
       FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame cenv es sa s0 c ei s /\
    (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
       (!nm b sz'. local_region cenv es.scopes s0 nm b sz' ==> off+sz <= b \/ b+sz' <= off) /\
       off <= i /\ i < off+sz /\ i IN tn.t_mem ==> i IN tn0.t_mem))` >>
  qabbrev_tac `InvRaw = (\Sep dst H rs ei G tn s. ?k r.
    k <= alen /\ alen = LENGTH vs /\ alen <= bound_length bd /\
    vs = GENLIST (\j. PlaceR (StoragePlace tr
      ((case bd of Fixed cap => slot | Dynamic cap => slot+1w) +
       n2w (j * type_slot_size elem_tv)) elem_tv)) alen /\
    rs = DROP k vs /\ slot = n2w r /\
    MEM (StorageRoot tr r (ArrayTV elem_tv bd)) ei.storage_trace /\
    evaluate_type (get_tenv cx) typ = SOME elem_tv /\ well_formed_type_value elem_tv /\
    s.vs_current_bb = cond /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    lookup_var idx s = SOME (n2w k) /\
    FLOOKUP G idx = NONE /\ op_taint tn (Var idx) = {} /\
    eval_operand lvo s = SOME (n2w alen) /\ op_taint tn lvo = {} /\
    op_prov G lvo = NONE /\
    eval_operand (Lit slot) s = SOME slot /\ op_taint tn (Lit slot) = {} /\
    lookup_var p s = SOME dst /\ FLOOKUP s.vs_allocas sd.cs_next_id = SOME (w2n dst,nb) /\
    ptr_covers G tn p s nb /\ 32 * type_slot_size elem_tv <= nb /\
    w2n dst+nb < 2**256 /\ w2n dst+nb <= s.vs_alloca_next /\
    (!nm b sz. local_region cenv ei.scopes s nm b sz ==> w2n dst+nb <= b \/ b+sz <= w2n dst) /\
    lookup_scopes id ei.scopes = NONE /\
    expr_sim_inv cenv cx env ei /\ ce_locals_declared cenv env /\ locals_alloc_ok cenv env /\
    cenv_top_ext cenv cenv ei.scopes /\ stmt_state_rel H ctx func cenv cx ei s /\
    storage_well_formed_on cx ei (FST H) /\ ghost_inv_at (DF H) lo d cenv cx ei G tn s /\
    return_buf_frame d cenv sa s /\ ret_pc_ok cenv sa s /\
    Sep /\ (k <> 0 ==> body_stmts_full_ok cx body') /\ Fr cenv ei s G tn)` >>
  `?dst t G1 tn1. !H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s0,G0,tn0) [] (OK t,G1,tn1) /\
     InvRaw T dst H vs ee G1 tn1 t` by
    (qpat_assum `Abbrev (InvRaw = _)`
       (fn th => rewrite_tac[REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
     qpat_assum `Abbrev (Fr = _)`
       (fn th => rewrite_tac[REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
     CONV_TAC (DEPTH_CONV BETA_CONV) >> pure_rewrite_tac[AND_CLAUSES] >>
     drule_at_then (Pat `emit_local_alloca _ _ _ = _`) (irule)
       (CONV_RULE (REDEPTH_CONV (REWR_CONV LET_THM ORELSEC BETA_CONV))
          for_storage_array_initial_full) >>
     simp[GSYM CONJ_ASSOC] >>
     conj_tac
     >- (qpat_assum `!x. lvo = Var x ==> x <> p` mp_tac >> simp[]) >>
     conj_tac
     >- (qx_gen_tac `H` >> strip_tac >> qexists_tac `off` >>
         qpat_x_assum `Abbrev (Fr = _)`
           (fn th => rewrite_tac[REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
         BETA_TAC >>
         ASM_SIMP_TAC bool_ss [cenv_top_ext_refl, LESS_EQ_REFL, GSYM AND_IMP_INTRO]) >>
     conj_tac
     >- (qexistsl [`bad`,`dbb`,`eb`,`eid`,`entry`,`good`,`sd.cs_next_id+1`] >>
         conj_tac
         >- (qpat_x_assum `!x. lvo = Var x ==> x NOTIN Written` mp_tac >>
             Cases_on `dyn` >> simp[Abbr `Written`]) >>
         conj_tac
         >- (qpat_x_assum `!x. not_fresh_at sa x ==> x NOTIN Written` mp_tac >>
             Cases_on `dyn` >> simp[Abbr `Written`]) >>
         conj_tac
         >- (qpat_x_assum `p NOTIN Written` mp_tac >>
             Cases_on `dyn` >> simp[Abbr `Written`]) >>
         conj_tac
         >- (qpat_x_assum `eb.bb_instructions = _` mp_tac >> simp[Abbr `code`]) >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac
         >- (qpat_x_assum `lookup_block sd.cs_current_bb func.fn_blocks = SOME dbb` mp_tac >>
             simp[]) >>
         conj_tac
         >- (qpat_x_assum `get_instruction dbb (LENGTH sc.cs_current_insts) = _` mp_tac >>
             simp[arithmeticTheory.ADD1]) >>
         qpat_x_assum `dyn ==> idx <> bad /\ idx <> good /\ bad <> good` mp_tac >>
         Cases_on `dyn` >> simp[]) >>
     qexistsl [`ArrayT typ bd`, `STRING #"%" (toString sa.cs_next_var)`,
               `mk_ptr (Lit slot) (slot_loc tr)`, `sa`] >>
     simp[] >> gvs[]) >>
  qabbrev_tac `Inv = (\dst H rs ei G tn s.
    InvRaw (return_buf_sep d cenv ei s) dst H rs ei G tn s)` >>
  qpat_assum `Abbrev (InvRaw = _)` (fn raw =>
    qpat_x_assum `Abbrev (Inv = _)`
      (assume_tac o BETA_RULE o PURE_REWRITE_RULE
        [REWRITE_RULE [markerTheory.Abbrev_def] raw])) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s0,G0,tn0) [] (OK t,G1,tn1) /\
     Inv dst H vs ee G1 tn1 t` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_x_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _ /\ InvRaw T dst H vs ee G1 tn1 t`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `Abbrev (InvRaw = _)` (fn raw =>
       qpat_x_assum `InvRaw _ dst H vs ee G1 tn1 t`
         (strip_assume_tac o PURE_REWRITE_RULE [AND_CLAUSES] o BETA_RULE o
          PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] raw])) >>
     `!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) t` by
       (qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) [] (OK t,G1,tn1)`
          (mp_then (Pos hd) mp_tac return_buf_allocas_path) >>
        disch_then (qspecl_then [`sa`,`es`,`d`,`cenv`] mp_tac) >>
        qpat_assum `return_buf_frame d cenv sa s0` (fn frame =>
          qpat_assum `return_buf_sep d cenv es s0` (fn sep =>
            rewrite_tac [frame,sep]))) >>
     `valid_horizon cx st0 H es.storage_trace` by
       (qpat_assum `valid_horizon cx st0 H ee.storage_trace` mp_tac >>
        simp[NoAsms, Abbr `ee`] >>
        disch_then (ACCEPT_TAC o MATCH_MP valid_horizon_append)) >>
     qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     `return_buf_sep d cenv ee t` by
       (`!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w` by
          (qpat_assum `Abbrev (Fr = _)` (fn fr =>
             qpat_assum `Fr cenv ee t G1 tn1`
               (ACCEPT_TAC o cj 4 o BETA_RULE o PURE_REWRITE_RULE
                 [REWRITE_RULE [markerTheory.Abbrev_def] fr]))) >>
        `MAP FDOM ee.scopes = MAP FDOM es.scopes` by simp[Abbr `ee`] >>
        drule_all_then ACCEPT_TAC return_buf_sep_locals_kept) >>
     qpat_assum `Abbrev (Inv = _)`
       (fn th => pure_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
     BETA_TAC >>
     rename [`vs = DROP k vs`, `MEM (StorageRoot tr r (ArrayTV elem_tv bd)) ee.storage_trace`] >>
     qexistsl [`k`,`r`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _ /\ InvRaw T dst H vs ee G1 tn1 t` kall_tac >>
  qpat_x_assum `Abbrev (InvRaw = _)` kall_tac >>
  qabbrev_tac `Done = (\H ei G tn u. ?c.
    stmt_lands lctx sb (INL ()) u /\ ~u.vs_halted /\
    ~block_is_terminated sb /\ c = cenv /\
    cenv_top_ext cenv c ei.scopes /\ stmt_state_rel H ctx func c cx ei u /\
    storage_well_formed_on cx ei (FST H) /\ return_buf_frame d c sb u /\ return_buf_sep d c ei u /\
    ghost_inv_at (DF H) lo d c cx ei G tn u /\ Fr c ei u G tn)` >>
  qabbrev_tac `R = (\H ex ei gt r.
    (!tail. stmt_exit_ptr (RetQ H) (ei with gas_obs := tail) (INR ex) gt r) /\
    halt_exit H cx ei (INR ex) r /\
    (ctx_has_dalloca ctx ==> !u.
      (r = Halt u \/ ?ir. r = IntRet ir u) ==> allocas_below_fmp u))` >>
  qabbrev_tac `round = (\a. do v <- read_result cx a;
    push_scope_with_var id elem_tv v;
    finally (try (do eval_stmts cx body'; return F od)
                 handle_loop_exception) pop_scope od)` >>
  qabbrev_tac `next = (\rs b. if b then return () else eval_for cx elem_tv id body' rs)` >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `body_inv tops ctx cenv cx` (fn inv =>
       qpat_assum `MEM func ctx.ctx_functions` (fn member =>
         ACCEPT_TAC (MATCH_MP bodyFullIfExpReachTheory.body_inv_no_phi
           (CONJ inv member))))) >>
  sg `gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
       (eval_for cx elem_tv id body' vs) (ee,t,G1,tn1)
       (\H res ei G tn u. res = INL () /\ Done H ei G tn u)
       (\H res ei gt r. ?ex. res = INR ex /\ R H ex ei gt r)`
  >- suspend "rounds" >>
  suspend "prefix"
QED

Resume compile_for_storage_array_frag_full[rounds]:
  irule bodyFullForRoundsTheory.eval_for_rounds_full >>
  conj_tac
  >- (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _ /\ Inv dst H vs ee G1 tn1 t`
        (qspec_then `H0` (drule_then strip_assume_tac)) >>
      qpat_assum `Abbrev (Inv = _)` (fn inv =>
        qpat_x_assum `Inv dst _ vs ee G1 tn1 t`
          (strip_assume_tac o BETA_RULE o
           REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] inv])) >>
      first_assum ACCEPT_TAC) >>
  qexistsl [`\H rs ei G tn s. Inv dst H rs ei G tn s /\
              (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_no_wrap inst u)`,
            `next`, `stmt_res_ok lctx`, `round`] >>
  BETA_TAC >>
  conj_tac >- suspend "round_cons" >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_bool >>
      goal_assum (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_bool >> simp[]) >>
  conj_tac >- simp[Abbr `round`] >>
  conj_tac >- suspend "round_nil" >>
  conj_tac >- simp[Abbr `next`] >>
  conj_tac
  >- (qx_gen_tac `H` >> strip_tac >>
      qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _ /\ Inv dst H vs ee G1 tn1 t`
        (qspec_then `H` (drule_then strip_assume_tac)) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) [] (OK t,G1,tn1)`
        (mp_then (Pos hd) mp_tac bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_no_wrap) >>
      asm_rewrite_tac []) >>
  qpat_x_assum `gas_admissible (eval_stmt _ _) _ es` mp_tac >>
  simp[gasContextTheory.gas_admissible_def]
QED

Resume compile_for_storage_array_frag_full[round_nil]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> Inv dst H [] _ _ _ _ /\ _`
    (strip_assume_tac o SIMP_RULE bool_ss [IMP_CONJ_THM, FORALL_AND_THM]) >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> Inv dst H [] _ _ _ _` mp_tac >>
  map_every (fn q => qpat_assum q
    (fn th => pure_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] th]))
      [`Abbrev (Inv = _)`, `Abbrev (Done = _)`, `Abbrev (Fr = _)`] >>
  BETA_TAC >> strip_tac >>
  irule (CONV_RULE (REDEPTH_CONV (REWR_CONV LET_THM ORELSEC BETA_CONV))
    for_storage_array_nil_full) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[block_is_terminated_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qspecl_then [`cenv`, `lctx`, `ret_ty`,
          `For id typ (Array (TopLevelName (ArrayT typ bd) nid)) n body'`, `sa`]
        mp_tac (cj 1 compile_stmt_ci_mono) >> simp[ci_mono_def]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `lookup_block cond func.fn_blocks = SOME _`
    (fn th => qmatch_asmsub_abbrev_tac `lookup_block cond func.fn_blocks = SOME cb`) >>
  qexistsl [`cb`, `bd`, `bod`, `body'`, `cond`, `dst`, `dv`, `h-2`,
            `env`, `exit`, `id`, `idx`, `alen`, `lvo`, `nb`,
            `stmt_res_ok lctx`, `p`, `sd`, `slot`, `tr`, `typ`, `elem_tv`, `vs`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (Cases_on `bd` >> simp[not_fresh_at_def]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[Abbr `cb`, get_instruction_def] >>
  conj_tac
  >- (`h-2+1 = h-1` by (Cases_on `bd` >> simp[]) >>
      simp[Abbr `cb`, get_instruction_def]) >>
  first_assum ACCEPT_TAC
QED

Resume compile_for_storage_array_frag_full[round_cons]:
  rpt gen_tac >> strip_tac >>
  irule gas_outcome_full_initial_domain >>
  conj_tac
  >- (simp[Abbr `round`] >>
      irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_read_result, storage_trace_frame_ignore_bind,
           storage_trace_frame_state_updates, storage_trace_frame_finally,
           storage_trace_frame_try, storage_trace_frame_return,
           storage_trace_frame_loop_handler, storage_trace_frame_pop_scope,
           evaluate_storage_trace_frame]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  strip_tac >>
  rename1 `!H. valid_horizon cx st0 H ei.storage_trace ==>
               Inv dst H (a::rs) ei g tn s /\ _` >>
  qpat_assum `!H. valid_horizon cx st0 H ei.storage_trace ==>
                 Inv dst H (a::rs) ei g tn s /\ _`
    (strip_assume_tac o SIMP_RULE bool_ss [IMP_CONJ_THM, FORALL_AND_THM]) >>
  `!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_no_wrap inst u` by
    (qpat_assum `!H. valid_horizon cx st0 H ei.storage_trace ==>
                   !fn inst u. frag_reachable ctx func s fn inst u ==> _`
       (qspec_then `storage_trace_horizon ei.storage_trace` mp_tac) >>
     simp[GSYM storage_trace_domain_def]) >>
  irule bodyFullIfExpReachTheory.gas_outcome_full_post_path >>
  qexists_tac `\H res ee G1 tn1 t.
    ee.gas_obs = [] /\ ~t.vs_halted /\
    ?b. res = INL b /\ (b ==> Done H ee G1 tn1 t) /\
        (~b ==> Inv dst H rs ee G1 tn1 t)` >>
  BETA_TAC >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      rename1 `_ = INL b` >> qexists_tac `b` >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      strip_tac >> conj_tac
      >- (qpat_assum `~b ==> Inv dst _ _ _ _ _ _` irule >>
          first_assum ACCEPT_TAC) >>
      qpat_assum `gas_origin_ptr_path _ (s,g,tn) _ (OK _,_,_)`
        (mp_then (Pos hd) mp_tac bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_no_wrap) >>
      asm_rewrite_tac []) >>
  suspend "round_outcome"
QED

Resume compile_for_storage_array_frag_full[round_outcome]:
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> Inv dst H (_::_) _ _ _ _` mp_tac >>
  map_every (fn q => qpat_assum q
    (fn th => pure_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] th]))
      [`Abbrev (round = _)`, `Abbrev (Inv = _)`, `Abbrev (Done = _)`,
       `Abbrev (R = _)`, `Abbrev (Fr = _)`, `Abbrev (explicit = _)`] >>
  BETA_TAC >> strip_tac >>
  irule (CONV_RULE (REDEPTH_CONV (REWR_CONV LET_THM ORELSEC BETA_CONV))
    for_storage_array_round_full) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (`sa.cs_next_var <= sb.cs_next_var` by
        (qspecl_then [`cenv`, `lctx`, `ret_ty`,
           `For id typ (Array (TopLevelName (ArrayT typ bd) nid)) n body'`, `sa`]
           mp_tac (cj 1 compile_stmt_ci_mono) >> simp[ci_mono_def]) >>
      rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
      qexists_tac `sa` >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qpat_assum `(case bd of Fixed cap => alen = cap /\ _ | Dynamic cap => _)`
        mp_tac >> Cases_on `bd` >>
      simp_tac (srw_ss()) [] >> strip_tac >>
      qpat_assum `lvo = (_ : operand)` SUBST1_TAC >> simp[]) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- simp[block_is_terminated_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[not_fresh_at_def] >>
  conj_tac
  >- (irule vyperArithTheory.lt_dimword_256 >> qexists_tac `256` >>
      conj_tac >- (irule arithmeticTheory.LESS_EQ_LESS_TRANS >>
                   qexists_tac `bound_length bd` >>
                   conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qpat_assum `call_evaluation_safe cx (int_calls_stmt (For _ _ _ _ _))`
        (ACCEPT_TAC o MATCH_MP vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_right o
         REWRITE_RULE [vyperTypeCallGraphTheory.int_calls_stmt_def])) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  suspend "round_packet"
QED

Resume compile_for_storage_array_frag_full[round_packet]:
  `compile_stmt cenv lctx ret_ty
     (For id typ (Array (TopLevelName (ArrayT typ bd) nid)) n
       (MAP gas_shadow_stmt body')) shadow_sa = ((),shadow_sb)` by
    (qpat_assum `nid = (NONE,name)` SUBST_ALL_TAC >>
     qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt (For _ _ _ _ _)) shadow_sa = _`
       mp_tac >>
     simp[gas_shadow_stmt_def, gas_shadow_iterator_def, gas_shadow_expr_def,
          stmt_env_def, declare_stmt_local_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def] >>
     Cases_on `compile_stmt cenv lctx ret_ty
       (For id typ (Array (TopLevelName (ArrayT typ bd) (NONE,name))) n
         (MAP gas_shadow_stmt body')) shadow_sa` >> simp[]) >>
  `?shadow_sd.
      (if dyn then
         compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca
           (if tr then LocTransient else LocStorage) (Lit slot)
       else comp_return (Lit (n2w (bound_length bd)))) shadow_sa = (lvo,shadow_sd) /\
      gas_shadow_state sd shadow_sd` by
    (qabbrev_tac `load = if dyn then
         compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca
           (if tr then LocTransient else LocStorage) (Lit slot)
       else comp_return (Lit (n2w (bound_length bd)))` >>
     `gas_shadow_compiles load load` by
       (simp[Abbr `load`, NoAsms] >> COND_CASES_TAC >>
        simp[NoAsms, gas_shadow_compiles_return,
             gasShadowCompileContextTheory.gas_shadow_compiles_ptr_load]) >>
     qpat_x_assum `gas_shadow_compiles load load`
       (qspecl_then [`sa`,`shadow_sa`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `load sa = (lvo,sd)` (fn th => REWRITE_TAC [th, pairTheory.FST, pairTheory.SND]) >>
     namedCases_on `load shadow_sa` ["shadow_lvo shadow_sd"] >>
     simp[NoAsms]) >>
  qpat_assum `compile_stmt _ _ _ (For _ _ _ _ (MAP gas_shadow_stmt body'))
      shadow_sa = ((),shadow_sb)`
    (mp_then Any (qspecl_then [`tr`,`slot`] mp_tac) for_storage_array_stages) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (foldr (uncurry qx_choose_then) strip_assume_tac
    [`lvoS`,`sdS`,`bcS`,`entryS`,`condS`,`bodS`,`incrS`,`exitS`,`idxS`,
     `offoS`,`totoS`,`epoS`,`preS`,`copyS`,`bodyS`,`jumpS`]) >>
  `lvoS = lvo /\ sdS = shadow_sd` by
    (qpat_x_assum `(if _ then _ else _) shadow_sa = (lvoS,sdS)` mp_tac >>
     qpat_assum `Abbrev (dyn = _)` (fn dyn_th =>
       qpat_assum `(if dyn then _ else _) shadow_sa = (lvo,shadow_sd)`
         (fn load_th => rewrite_tac
            [REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] dyn_th] load_th,
             pairTheory.PAIR_EQ])) >>
     simp[NoAsms, EQ_SYM_EQ]) >>
  qpat_x_assum `lvoS = lvo` SUBST_ALL_TAC >>
  qpat_x_assum `sdS = shadow_sd` SUBST_ALL_TAC >>
  qpat_assum `(comp_bind (declare_local cenv id typ) _) shadow_sd = _`
    (fn th => qmatch_asmsub_abbrev_tac `prefix_compile shadow_sd = ^(rhs (concl th))`) >>
  `gas_shadow_compiles prefix_compile prefix_compile` by
    (qpat_assum `Abbrev (prefix_compile = _)`
       (pure_rewrite_tac o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `bd` >> simp[] >>
     rpt (FIRST
       [MATCH_MP_TAC gas_shadow_compiles_bind >> conj_tac,
        MATCH_MP_TAC gasShadowCompileBaseTheory.gas_shadow_compiles_ignore_bind >> conj_tac,
        gen_tac >> BETA_TAC]) >>
     simp[gas_shadow_compiles_return, gas_shadow_compiles_fresh_label,
          gas_shadow_compiles_fresh_var, gas_shadow_compiles_new_block,
          gas_shadow_compiles_emit_inst, gas_shadow_compiles_emit_void,
          gasShadowCompileContextTheory.gas_shadow_compiles_emit_op_same,
          gasShadowCompileStmtBaseTheory.gas_shadow_compiles_declare_local,
          gasShadowCompileStmtBaseTheory.gas_shadow_compiles_emit_local_alloca]) >>
  qpat_assum `compile_stmt _ _ _ (For _ _ _ _ body') sa = ((),sb)`
    (mp_then Any (qspecl_then [`tr`,`slot`] mp_tac) for_storage_array_stages) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (foldr (uncurry qx_choose_then) strip_assume_tac
    [`lvoA`,`sdA`,`bcA`,`entryA`,`condA`,`bodA`,`incrA`,`exitA`,`idxA`,
     `offoA`,`totoA`,`epoA`,`preA`,`copyA`,`bodyA`,`jumpA`]) >>
  `lvoA = lvo /\ sdA = sd` by
    (qpat_x_assum `(if _ then _ else _) sa = (lvoA,sdA)` mp_tac >>
     qpat_assum `Abbrev (dyn = _)` (fn dyn_th =>
       qpat_assum `(if dyn then _ else _) sa = (lvo,sd)`
         (fn load_th => rewrite_tac
            [REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] dyn_th] load_th,
             pairTheory.PAIR_EQ])) >>
     simp[NoAsms, EQ_SYM_EQ]) >>
  qpat_x_assum `lvoA = lvo` SUBST_ALL_TAC >>
  qpat_x_assum `sdA = sd` SUBST_ALL_TAC >>
  qpat_assum `(comp_bind (declare_local cenv id typ) _) sd = (_,preA)`
    (fn th => qpat_assum `Abbrev (prefix_compile = _)` (fn ab =>
       assume_tac (REWRITE_RULE [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] ab)] th))) >>
  `FST (prefix_compile sd) = FST (prefix_compile shadow_sd) /\
    gas_shadow_state (SND (prefix_compile sd)) (SND (prefix_compile shadow_sd))` by
    (qpat_assum `gas_shadow_compiles prefix_compile prefix_compile`
       (qspecl_then [`sd`,`shadow_sd`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then ACCEPT_TAC) >>
  qpat_assum `FST (prefix_compile sd) = _` mp_tac >>
  qpat_assum `prefix_compile sd = (_,preA)` (fn th => rewrite_tac [th]) >>
  qpat_assum `prefix_compile shadow_sd = (_,preS)` (fn th => rewrite_tac [th]) >>
  rewrite_tac[pairTheory.FST,pairTheory.PAIR_EQ] >>
  disch_then (map_every SUBST_ALL_TAC o map SYM o CONJUNCTS) >>
  `gas_shadow_state preA preS` by
    (qpat_assum `gas_shadow_state (SND (prefix_compile sd)) _` mp_tac >>
     qpat_assum `prefix_compile sd = (_,preA)` (fn th => rewrite_tac [th]) >>
     qpat_assum `prefix_compile shadow_sd = (_,preS)` (fn th => rewrite_tac [th]) >>
     rewrite_tac[pairTheory.SND]) >>
  qpat_assum `prefix_compile sd = (_,preA)`
    (fn th => qpat_assum `Abbrev (prefix_compile = _)` (fn ab =>
       assume_tac (REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] ab] th))) >>
  drule_all for_storage_array_prefix >> strip_tac >>
  `bcA = bc` by
    (qpat_assum `declare_local cenv id typ sd = (bcA,_)` mp_tac >>
     qpat_assum `declare_local cenv id typ sd = (bc,sdecl)`
       (fn th => rewrite_tac [th, pairTheory.PAIR_EQ]) >>
     disch_then (ACCEPT_TAC o SYM o CONJUNCT1)) >>
  `entryA = entry /\ condA = cond /\ bodA = bod /\
   incrA = incr /\ exitA = exit /\ idxA = idx /\ epoA = Var ep` by
    (Cases_on `bd` >> simp[Abbr `dyn`]) >>
  map_every (fn q => qpat_x_assum q SUBST_ALL_TAC)
    [`bcA = bc`,`entryA = entry`,`condA = cond`,`bodA = bod`,
     `incrA = incr`,`exitA = exit`,`idxA = idx`,`epoA = Var ep`] >>
  qabbrev_tac `copy_compile = compile_iter_elem_copy cenv (Var ep) (Var p)
    (elem_size_in_location cenv (if tr then LocTransient else LocStorage) typ)
    (if tr then LocTransient else LocStorage) T typ typ` >>
  `copy_compile preA = ((),copyA) /\ copy_compile preS = ((),copyS)` by
    (conj_tac
     >- (qpat_assum `_ preA = ((),copyA)` mp_tac >>
         qpat_assum `FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) nb)`
           (fn th => simp[NoAsms, th, Abbr `copy_compile`])) >>
     qpat_assum `_ preS = ((),copyS)` mp_tac >>
     qpat_assum `FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) nb)`
       (fn th => simp[NoAsms, th, Abbr `copy_compile`])) >>
  `gas_shadow_state copyA copyS` by
    (`gas_shadow_compiles copy_compile copy_compile` by
       simp[Abbr `copy_compile`,gasShadowCompileStmtOpsTheory.gas_shadow_compiles_iter_elem_copy] >>
     qpat_x_assum `gas_shadow_compiles copy_compile copy_compile`
       (qspecl_then [`preA`,`preS`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
     simp[]) >>
  namedCases_on `stmts_env bc (InLoop exit incr) ret_ty body' copyA`
    ["bcFinal bodyEndA"] >>
  `bodyEndA = bodyA` by
    (qpat_assum `compile_stmts _ _ _ body' copyA = _`
       (fn th => qpat_assum `stmts_env bc _ _ body' copyA = _`
          (fn env_th => ACCEPT_TAC (REWRITE_RULE
            [compile_stmts_env, env_th, pairTheory.SND, pairTheory.PAIR_EQ] th)))) >>
  qpat_x_assum `bodyEndA = bodyA` SUBST_ALL_TAC >>
  `stmts_env bc (InLoop exit incr) ret_ty (MAP gas_shadow_stmt body') copyS =
      (bcFinal,bodyS) /\ gas_shadow_state bodyA bodyS` by
    (namedCases_on `stmts_env bc (InLoop exit incr) ret_ty (MAP gas_shadow_stmt body') copyS`
       ["bcFinalS bodyEndS"] >>
     `bodyEndS = bodyS` by
       (qpat_assum `compile_stmts _ _ _ (MAP gas_shadow_stmt body') copyS = _`
          (fn th => qpat_assum `stmts_env bc _ _ (MAP gas_shadow_stmt body') copyS = _`
             (fn env_th => ACCEPT_TAC (REWRITE_RULE
               [compile_stmts_env, env_th, pairTheory.SND, pairTheory.PAIR_EQ] th)))) >>
     qpat_x_assum `bodyEndS = bodyS` SUBST_ALL_TAC >>
     qspecl_then [`body'`,`bc`,`InLoop exit incr`,`ret_ty`]
       (qspecl_then [`copyA`,`copyS`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def])
       gasShadowStmtEnvTheory.gas_shadow_stmts_env >> simp[EQ_SYM_EQ]) >>
  (* Split each code certificate at the cuts selected by its own compilation. *)
  `cs_extends sa preA` by
    (irule cs_extends_trans >> qexists_tac `sd` >> conj_tac
     >- (qpat_assum `ci_mono sa sd` (ACCEPT_TAC o cj 1 o REWRITE_RULE [ci_mono_def])) >>
     qpat_assum `preA.cs_blocks = _` (ACCEPT_TAC o MATCH_MP array_prefix_extends)) >>
  `cs_extends shadow_sa shadow_sd` by
    (qpat_assum `(if dyn then _ else _) shadow_sa = (lvo,shadow_sd)` mp_tac >>
     Cases_on `dyn`
     >- (simp[NoAsms] >> strip_tac >>
         qspecl_then [`cenv.ce_is_ctor`,`cenv.ce_imm_alloca`,
                     `if tr then LocTransient else LocStorage`,`Lit slot`,
                     `shadow_sa`] mp_tac ci_mono_compile_ptr_load >>
         qpat_assum `compile_ptr_load _ _ _ _ shadow_sa = _`
           (fn th => rewrite_tac [th, pairTheory.SND,ci_mono_def]) >> simp[]) >>
     simp[NoAsms,comp_return_def] >>
     disch_then (CONJUNCTS_THEN2 kall_tac (SUBST1_TAC o SYM)) >>
     simp[cs_extends_refl]) >>
  `cs_extends shadow_sa preS` by
    (irule cs_extends_trans >> qexists_tac `shadow_sd` >> simp[] >>
     qpat_assum `prefix_compile shadow_sd = (_,preS)`
       (fn th => qpat_assum `Abbrev (prefix_compile = _)` (fn ab =>
          mp_then Any mp_tac for_storage_array_prefix
            (REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] ab] th))) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     qpat_assum `preS.cs_blocks = _` (ACCEPT_TAC o MATCH_MP array_prefix_extends)) >>
  qabbrev_tac `stride = elem_size_in_location cenv
     (if tr then LocTransient else LocStorage) typ` >>
  `copyA = slot_copy_final preA (Var ep) (Var p) stride (if tr then TLOAD else SLOAD) /\
   copyS = slot_copy_final preS (Var ep) (Var p) stride (if tr then TLOAD else SLOAD)` by
    (qpat_assum `copy_compile preA = ((),copyA)` mp_tac >>
     qpat_assum `copy_compile preS = ((),copyS)` mp_tac >>
     Cases_on `tr` >>
     simp[NoAsms, Abbr `copy_compile`, Abbr `stride`, compile_iter_elem_copy_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def,
          compile_slot_to_memory_shape, EQ_SYM_EQ]) >>
  `cs_extends preA copyA /\ cs_extends preS copyS` by simp[slot_copy_extends] >>
  `ci_mono copyA bodyA /\ ci_mono copyS bodyS` by
    (qspecl_then [`bc`,`InLoop exit incr`,`ret_ty`,`body'`,`copyA`] mp_tac
       (cj 2 compile_stmt_ci_mono) >>
     qspecl_then [`bc`,`InLoop exit incr`,`ret_ty`,`MAP gas_shadow_stmt body'`,`copyS`] mp_tac
       (cj 2 compile_stmt_ci_mono) >> simp[]) >>
  `cs_extends bodyA jumpA /\ cs_extends bodyS jumpS` by
    (conj_tac
     >- (qpat_assum `emit_jmp_if_not_terminated incr bodyA = _`
           (ACCEPT_TAC o cj 4 o MATCH_MP array_body_backedge)) >>
     qpat_assum `emit_jmp_if_not_terminated incr bodyS = _`
       (ACCEPT_TAC o cj 4 o MATCH_MP array_body_backedge)) >>
  qpat_assum `_ jumpA = ((),sb)` (mp_then Any strip_assume_tac compile_for_array_suffix) >>
  qpat_assum `_ jumpS = ((),shadow_sb)` (mp_then Any strip_assume_tac compile_for_array_suffix) >>
  map_every (fn q => qpat_assum q
    (assume_tac o cj 1 o REWRITE_RULE [ci_mono_def]))
    [`ci_mono copyA bodyA`,`ci_mono copyS bodyS`] >>
  `fn_has_code sa preA func /\ fn_has_code preA copyA func /\
   fn_has_code copyA bodyA func /\ fn_has_code bodyA jumpA func /\
   fn_has_code jumpA sb func` by
    (irule array_stages_code >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `fn_has_code copyS bodyS shadow_func` by
    (`fn_has_code shadow_sa preS shadow_func /\ fn_has_code preS copyS shadow_func /\
      fn_has_code copyS bodyS shadow_func /\ fn_has_code bodyS jumpS shadow_func /\
      fn_has_code jumpS shadow_sb shadow_func` by
       (irule array_stages_code >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  namedCases_on `new_block incr jumpA` ["oldA siA"] >>
  namedCases_on `emit_op ADD [Var idx; Lit 1w] siA` ["nextA addA"] >>
  namedCases_on `emit_inst ASSIGN [nextA] [idx] addA` ["uA skA"] >>
  namedCases_on `emit_inst JMP [Label cond] [] skA` ["vA slA"] >>
  namedCases_on `new_block exit slA` ["exitOldA exitEndA"] >>
  `exitEndA = sb` by
    (qpat_assum `_ jumpA = ((),sb)` mp_tac >>
     qpat_assum `new_block incr jumpA = _` (fn nb =>
      qpat_assum `emit_op ADD _ siA = _` (fn add =>
       qpat_assum `emit_inst ASSIGN _ _ addA = _` (fn assign =>
        qpat_assum `emit_inst JMP _ _ skA = _` (fn jmp =>
         qpat_assum `new_block exit slA = _` (fn finish =>
          simp[NoAsms,comp_bind_def,comp_ignore_bind_def,comp_return_def,
               nb,add,assign,jmp,finish])))))) >>
  qpat_x_assum `exitEndA = sb` SUBST_ALL_TAC >>
  `siA.cs_current_bb = incr /\ siA.cs_current_insts = [] /\
   siA.cs_next_var = jumpA.cs_next_var` by
    (qpat_assum `new_block incr jumpA = _` mp_tac >>
     simp[NoAsms,new_block_def] >>
     disch_then (SUBST1_TAC o SYM o CONJUNCT2) >> simp[NoAsms]) >>
  qabbrev_tac `outA = STRING #"%" (toString jumpA.cs_next_var)` >>
  `nextA = Var outA` by
    (qpat_assum `emit_op ADD _ siA = _` (mp_tac o MATCH_MP placeMemoryCodeLayoutTheory.emit_op_next_var) >>
     simp[Abbr `outA`]) >>
  qpat_x_assum `nextA = Var outA` SUBST_ALL_TAC >>
  `uA = () /\ vA = ()` by simp[] >>
  qpat_x_assum `uA = ()` SUBST_ALL_TAC >>
  qpat_x_assum `vA = ()` SUBST_ALL_TAC >>
  `ci_mono jumpA siA /\ ci_mono siA addA /\ ci_mono addA skA /\
   ci_mono skA slA /\ ci_mono slA sb` by
    (qspecl_then [`incr`,`jumpA`] mp_tac ci_mono_new_block >>
     qspecl_then [`ADD`,`[Var idx; Lit 1w]`,`siA`] mp_tac ci_mono_emit_op >>
     qspecl_then [`ASSIGN`,`[Var outA]`,`[idx]`,`addA`] mp_tac ci_mono_emit_inst >>
     qspecl_then [`JMP`,`[Label cond]`,`[]`,`skA`] mp_tac ci_mono_emit_inst >>
     qspecl_then [`exit`,`slA`] mp_tac ci_mono_new_block >> simp[]) >>
  map_every (fn q => qpat_assum q
    (assume_tac o cj 1 o REWRITE_RULE [ci_mono_def]))
    [`ci_mono jumpA siA`,`ci_mono siA addA`,`ci_mono addA skA`,
     `ci_mono skA slA`,`ci_mono slA sb`] >>
  `fn_has_code siA slA func` by
    (`cs_extends siA slA` by
       (irule cs_extends_trans >> qexists_tac `addA` >> conj_tac
        >- first_assum ACCEPT_TAC >>
        irule cs_extends_trans >> qexists_tac `skA` >> simp[]) >>
     irule fn_has_code_mid >> simp[] >> qexistsl_tac [`sb`,`jumpA`] >> simp[]) >>
  `sd.cs_next_var + 1 < preA.cs_next_var` by
    (qpat_assum `preA.cs_next_var = _` mp_tac >> Cases_on `dyn` >> simp[]) >>
  `copyA.cs_next_var = preA.cs_next_var + 7 /\
   copyA.cs_next_id = preA.cs_next_id + 12 /\ copyA.cs_current_insts = []` by
    (qpat_assum `copyA = slot_copy_final _ _ _ _ _` SUBST1_TAC >> simp[slot_copy_final_def]) >>
  `sa.cs_next_id <= copyA.cs_next_id` by
    (qpat_assum `ci_mono sa sd` (mp_tac o cj 3 o REWRITE_RULE [ci_mono_def]) >>
     qpat_assum `preA.cs_next_id = _` mp_tac >>
     qpat_assum `h' = sd.cs_next_id + _` mp_tac >> Cases_on `dyn` >> simp[]) >>
  qpat_assum `ci_mono copyA bodyA` (assume_tac o cj 2 o REWRITE_RULE [ci_mono_def]) >>
  qpat_assum `emit_jmp_if_not_terminated incr bodyA = _`
    (assume_tac o cj 3 o MATCH_MP array_body_backedge) >>
  `sd.cs_next_var + 1 < copyA.cs_next_var` by
    (qpat_assum `copyA.cs_next_var = preA.cs_next_var + 7` SUBST1_TAC >>
     qpat_assum `sd.cs_next_var + 1 < preA.cs_next_var` mp_tac >> decide_tac) >>
  `copyA.cs_next_var <= siA.cs_next_var` by
    (qpat_assum `siA.cs_next_var = jumpA.cs_next_var` SUBST1_TAC >>
     qpat_assum `jumpA.cs_next_var = bodyA.cs_next_var` SUBST1_TAC >>
     first_assum ACCEPT_TAC) >>
  `local_ptrs_reserved bc sdecl` by (irule stmtSimPropsTheory.declare_local_reserved >> simp[] >>
    qexistsl_tac [`cenv`,`id`,`sd`,`typ`] >> simp[]) >>
  `sa.cs_next_var <= sd.cs_next_var` by
    (qpat_assum `ci_mono sa sd` (ACCEPT_TAC o cj 2 o REWRITE_RULE [ci_mono_def])) >>
  `sd.cs_next_var <= preA.cs_next_var /\ sd.cs_next_var <= copyA.cs_next_var /\
   sd.cs_next_var + 1 <= preA.cs_next_var /\ sd.cs_next_var + 1 <= copyA.cs_next_var` by
    (qpat_assum `sd.cs_next_var + 1 < preA.cs_next_var` mp_tac >>
     qpat_assum `sd.cs_next_var + 1 < copyA.cs_next_var` mp_tac >> decide_tac) >>
  `sdecl.cs_next_var = sd.cs_next_var + 1` by simp[NoAsms,Abbr `sdecl`] >>
  `local_ptrs_reserved bc preA /\ local_ptrs_reserved bc copyA /\
   local_ptrs_reserved cenv preA /\ local_ptrs_reserved cenv copyA` by
    (conj_tac
     >- (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >> qexists_tac `sdecl` >>
         conj_tac
         >- (qpat_assum `sdecl.cs_next_var = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
         first_assum ACCEPT_TAC) >>
     conj_tac
     >- (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >> qexists_tac `sdecl` >>
         conj_tac
         >- (qpat_assum `sdecl.cs_next_var = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
         first_assum ACCEPT_TAC) >>
     conj_tac >> irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sd` >> conj_tac >> first_assum ACCEPT_TAC) >>
  `sa.cs_next_var <= preA.cs_next_var /\ sa.cs_next_var <= copyA.cs_next_var` by
    (rpt conj_tac >> irule arithmeticTheory.LESS_EQ_TRANS >>
     qexists_tac `sd.cs_next_var` >> conj_tac >> first_assum ACCEPT_TAC) >>
  `!x. not_fresh_at sa x ==> not_fresh_at preA x /\ not_fresh_at copyA x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!x. lvo = Var x ==> not_fresh_at preA x /\ not_fresh_at copyA x` by
    (rpt gen_tac >> strip_tac >>
     `not_fresh_at sd x` by (first_assum irule >> first_assum ACCEPT_TAC) >>
     conj_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sd` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `sd.cs_next_var + 1 < siA.cs_next_var` by
    (irule arithmeticTheory.LESS_LESS_EQ_TRANS >> qexists_tac `copyA.cs_next_var` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `sd.cs_next_var <= jumpA.cs_next_var /\ sa.cs_next_var <= jumpA.cs_next_var /\
   sd.cs_next_var < jumpA.cs_next_var` by
    (qpat_assum `siA.cs_next_var = jumpA.cs_next_var` (SUBST1_TAC o SYM) >>
     qpat_assum `sd.cs_next_var + 1 < siA.cs_next_var` mp_tac >>
     qpat_assum `sa.cs_next_var <= sd.cs_next_var` mp_tac >> decide_tac) >>
  `not_fresh_at preA p /\ not_fresh_at preA idx /\ not_fresh_at copyA p /\
   not_fresh_at copyA idx /\ not_fresh_at siA idx` by
    (qpat_assum `p = STRING _ _` SUBST1_TAC >>
     qpat_assum `idx = STRING _ _` SUBST1_TAC >>
     qpat_assum `sd.cs_next_var + 1 < preA.cs_next_var` mp_tac >>
     qpat_assum `sd.cs_next_var + 1 < copyA.cs_next_var` mp_tac >>
     qpat_assum `sd.cs_next_var + 1 < siA.cs_next_var` mp_tac >>
     simp[NoAsms,not_fresh_at_def] >> decide_tac) >>
  `p <> outA /\ ~not_fresh_at sa outA` by
    (qpat_assum `p = STRING _ _` SUBST1_TAC >>
     qpat_assum `sd.cs_next_var < jumpA.cs_next_var` mp_tac >>
     qpat_assum `sa.cs_next_var <= jumpA.cs_next_var` mp_tac >>
     simp[NoAsms,Abbr `outA`,not_fresh_at_def] >> decide_tac) >>
  `!x. lvo = Var x ==> x <> idx /\ x <> outA` by
    (rpt gen_tac >> strip_tac >>
     `not_fresh_at sd x` by (qpat_assum `!x. lvo = Var x ==> not_fresh_at sd x`
                              irule >> first_assum ACCEPT_TAC) >>
     qpat_assum `not_fresh_at sd x` (strip_assume_tac o REWRITE_RULE [not_fresh_at_def]) >>
     conj_tac
     >- (qpat_assum `idx = STRING _ _` SUBST1_TAC >> first_assum irule >> decide_tac) >>
     simp[NoAsms,Abbr `outA`] >> first_assum irule >> first_assum ACCEPT_TAC) >>
  `FLOOKUP cenv.ce_vars id = NONE` by
    (Cases_on `FLOOKUP cenv.ce_vars id` >> simp[] >>
     `id IN FDOM env.var_types` by
       (qpat_assum `ce_locals_declared cenv env`
          (drule_then ACCEPT_TAC o REWRITE_RULE [ce_locals_declared_def])) >>
     fs[]) >>
  `same_frame cenv bc` by
    (drule_then irule bodySimDeclCasesTheory.declare_local_same_frame >> simp[]) >>
  `bc.ce_return_buf = cenv.ce_return_buf` by
    (qpat_assum `bc with <|ce_vars := _; ce_var_type := _; ce_dynarray_capacity := _|> = cenv`
       (mp_tac o AP_TERM ``\c. c.ce_return_buf``) >> simp[]) >>
  `!x sz. bc.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at copyA x` by
    (map_every qx_gen_tac [`rbuf`, `rcap`] >> strip_tac >>
     `cenv.ce_return_buf = SOME (PtrVar (Var rbuf) rcap)` by
       (qpat_assum `bc.ce_return_buf = cenv.ce_return_buf` (SUBST1_TAC o SYM) >>
        first_assum ACCEPT_TAC) >>
     `not_fresh_at sa rbuf` by
       (qpat_assum `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> _`
          (drule_then ACCEPT_TAC)) >>
     qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at preA x /\ not_fresh_at copyA x`
       (qspec_then `rbuf` mp_tac) >> simp[]) >>
  `!H. dead_lo_ok H (DF H) lo bc cx` by
    (qx_gen_tac `Hdead` >>
     qpat_assum `same_frame cenv bc`
       (fn th => rewrite_tac [dead_lo_ok_def, MATCH_MP bodyPtrDefsTheory.same_frame_is_ctor th]) >>
     qpat_assum `!H. dead_lo_ok H (DF H) lo cenv cx`
       (qspec_then `Hdead` (ACCEPT_TAC o REWRITE_RULE [dead_lo_ok_def]))) >>
  `body_inv tops ctx bc cx` by
    (irule body_inv_same_frame >> qexists_tac `cenv` >> simp[]) >>
  `supported_program tops` by
    (qpat_assum `body_inv tops ctx cenv cx`
       (mp_tac o REWRITE_RULE [bodySimTheory.body_inv_def]) >> simp[]) >>
  `supported_stmts tops bindings body'` by
    (drule_then ACCEPT_TAC supportedStmtsTheory.supported_loop_body_contract) >>
  `stmts_exprs_ok bc body'` by
    (drule_then assume_tac bodySimDeclCasesTheory.body_for_exprs_ok >>
     drule_all_then ACCEPT_TAC bodyExprPreFactsTheory.for_declare_stmts_exprs_ok) >>
  `!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) body' ==>
       occurs_abi_decode_target target tops` by
    (gen_tac >> strip_tac >> first_assum irule >>
     simp[supportedStmtTraverseTheory.supported_stmt_expr_exists_def]) >>
  `frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ bc ret_ty` by
    (qpat_assum `frame_ret_ok_full _ _ _ cenv _`
       (mk_asm "original_ret" o REWRITE_RULE [bodySimFullTheory.frame_ret_ok_full_def]) >>
     rewrite_tac[bodySimFullTheory.frame_ret_ok_full_def] >>
     rpt gen_tac >> strip_tac >> asm "original_ret" irule >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (irule same_frame_trans >> goal_assum $ drule_at Any >> simp[]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     goal_assum $ drule_at Any >> simp[]) >>
  qpat_assum `IS_SOME (type_stmts _ _ _)`
    (qx_choose_then `envBody` assume_tac o REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
  qexistsl_tac [`bc`,`bcFinal`,`bindings`,`envBody`,`exit`,`incr`,`stmt_res_ok lctx`,`outA`,
    `ret_ty`,`copyA`,`bodyA`,`shadow_func`,`copyS`,`bodyS`,
    `siA`,`jumpA`,`addA`,`skA`,`slA`,`tops`] >>
  simp[block_is_terminated_def, IgnAsm `copyA = slot_copy_final _ _ _ _ _`] >>
  rpt gen_tac >> strip_tac >>
  `stride = type_slot_size elem_tv` by
    (simp[Abbr `stride`] >> irule (cj 1 for_storage_element_layout) >>
     qexistsl_tac [`cx`,`env`,`ee`] >> simp[]) >>
  `compile_iter_elem_copy bc (Var ep) (Var p) (type_slot_size elem_tv)
     (slot_loc tr) T typ typ preA = ((),copyA)` by
    (qpat_assum `copyA = slot_copy_final _ _ _ _ _` SUBST1_TAC >>
     Cases_on `tr` >>
     simp[slot_loc_def,compile_iter_elem_copy_def,comp_ignore_bind_def,
          comp_bind_def,comp_return_def,compile_slot_to_memory_shape]) >>
  `MEM ai (fn_insts func)` by
    (irule compileAllocaProvenanceTheory.fn_has_code_current_member >>
     qexistsl_tac [`sd`,`sc`] >> simp[]) >>
  `ai.inst_opcode = ALLOCA /\ ai.inst_outputs = [p] /\ ai.inst_id = sd.cs_next_id` by
    simp[NoAsms,Abbr `ai`,mk_inst_def] >>
  qpat_assum `fn_has_code preA copyA func` mp_tac >>
  qpat_assum `copyA = slot_copy_final _ _ _ _ _`
    (fn th => rewrite_tac [th]) >>
  disch_then (strip_assume_tac o MATCH_MP slot_copy_lookup) >>
  qabbrev_tac `condBB = <|bb_label := cond;
    bb_instructions := [mk_inst (h-2) EQ [Var idx;lvo] [dv];
      mk_inst (h-1) JNZ [Var dv;Label exit;Label bod] []]|>` >>
  qabbrev_tac `headBB = <|bb_label := preA.cs_current_bb;
    bb_instructions := preA.cs_current_insts ++ slot_copy_init_insts preA|>` >>
  `0 < type_slot_size elem_tv` by
    (irule vyperTypeSystemTheory.assignable_type_slot_size_pos >>
     qexistsl_tac [`get_tenv cx`,`typ`] >>
     conj_tac
     >- first_assum ACCEPT_TAC >>
     qpat_assum `env_consistent env cx es`
       (mp_tac o REWRITE_RULE [vyperTypeInvariantsTheory.env_consistent_def,
                                vyperTypeInvariantsTheory.env_context_consistent_def]) >>
     strip_tac >> qpat_assum `env.type_defs = get_tenv cx` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  `alen < 2**256` by
    (irule arithmeticTheory.LESS_EQ_LESS_TRANS >> qexists_tac `bound_length bd` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `ee.gas_obs = es.gas_obs` by simp[NoAsms,Abbr `ee`] >>
  `ee with gas_obs := es.gas_obs = ee` by
    (qpat_assum `ee.gas_obs = es.gas_obs` (fn th => simp[NoAsms,GSYM th])) >>
  `eval_iterator cx (Array (TopLevelName (ArrayT typ bd) nid)) es = (INL vs,ee)` by
    (qpat_assum `nid = (NONE,name)` SUBST1_TAC >>
     qpat_assum `!tail. eval_iterator _ _ _ = _` (qspec_then `es.gas_obs` mp_tac) >>
     qpat_assum `compatible_bound bd alen` (fn bound =>
       qpat_assum `ee with gas_obs := es.gas_obs = ee` (fn tail_eq =>
         simp[NoAsms,bound,tail_eq]))) >>
  `body_for_full_ok cx elem_tv id body' vs` by
    (qpat_assum `!tenv s ty t s3 rs t3 s4 x t4. _ ==> body_for_full_ok _ _ _ _ _`
       (qspecl_then [`get_tenv cx`,`es`,`elem_tv`,`es`,`es`,`vs`,`ee`,`es`,`()`,`es`] mp_tac) >>
     impl_tac
     >- (qpat_assum `eval_iterator _ _ es = (INL vs,ee)` (fn it_th =>
         qpat_assum `evaluate_type (get_tenv cx) typ = SOME elem_tv` (fn ty_th =>
         qpat_assum `LENGTH vs = alen` (fn len_th =>
         qpat_assum `compatible_bound (Dynamic n) alen` (fn bnd_th =>
           simp[NoAsms,it_th,ty_th,len_th,bnd_th,lift_option_type_def,
                check_def,assert_def,vyperStateTheory.return_def]))))) >>
     disch_then ACCEPT_TAC) >>
  `type_memory_bytes cenv typ < 2**64` by
    (qpat_assum `nb < 2**64` mp_tac >> simp[NoAsms, Abbr `nb`]) >>
  `!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q sz. l = PtrVar q sz` by
    (qpat_assum `FLOOKUP cenv.ce_vars id = NONE` (fn th => simp[NoAsms,th])) >>
  `!x. not_fresh_at sa x ==> not_fresh_at preA x` by
    (qx_gen_tac `x` >> strip_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at preA x /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  `!x. lvo = Var x ==> not_fresh_at preA x` by
    (qx_gen_tac `x` >> strip_tac >>
     qpat_assum `!x. lvo = Var x ==> not_fresh_at preA x /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  `sa.cs_next_id <= ai.inst_id` by
    (qpat_assum `ci_mono sa sd` (mp_tac o cj 3 o REWRITE_RULE [ci_mono_def]) >>
     qpat_assum `ai.inst_id = sd.cs_next_id` SUBST1_TAC >> simp[NoAsms]) >>
  `condBB.bb_instructions = [mk_inst (h-2) EQ [Var idx;lvo] [dv];
      mk_inst (h-1) JNZ [Var dv;Label exit;Label bod] []]` by
    simp[NoAsms,Abbr `condBB`] >>

  `lookup_block bod func.fn_blocks = SOME headBB` by
    (qpat_assum `lookup_block preA.cs_current_bb func.fn_blocks = SOME _` mp_tac >>
     qpat_assum `preA.cs_current_bb = bod` (fn th => simp[NoAsms,Abbr `headBB`,th])) >>
  `!j. j < LENGTH preA.cs_current_insts ==>
       get_instruction headBB j = SOME (EL j preA.cs_current_insts)` by
    simp[NoAsms,Abbr `headBB`,get_instruction_def,EL_APPEND1] >>
  `compile_slot_to_memory (Var ep) (Var p) (type_slot_size elem_tv) (slot_loc tr) preA =
     (slot_copy_body preA,copyA)` by
    (qpat_assum `copyA = slot_copy_final _ _ _ _ _` SUBST1_TAC >>
     qpat_assum `stride = type_slot_size elem_tv` (fn th => rewrite_tac[th]) >>
     Cases_on `tr` >> simp[NoAsms,slot_loc_def,copyExecutionTheory.compile_slot_to_memory_shape]) >>
  `!lbl. lvo <> Label lbl` by
    (qpat_assum `if dyn then lvo = Var _ /\ _ else lvo = Lit _ /\ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `dyn` >> simp[] >> strip_tac >> simp[]) >>
  `!scs. lookup_scopes id scs = NONE ==> not_local_ptr bc (FEMPTY::scs) p` by
    (rpt strip_tac >> irule localPtrsPropsTheory.not_local_ptr_name_update >>
     qexistsl_tac [`cenv`,`id`] >>
     `bc.ce_imm_alloca = cenv.ce_imm_alloca` by
       (qpat_assum `bc with <|ce_vars := _; ce_var_type := _; ce_dynarray_capacity := _|> = cenv`
         (mp_tac o AP_TERM ``\c. c.ce_imm_alloca``) >> simp[NoAsms]) >>
     `~not_fresh_at sd p` by
       (qpat_assum `p = STRING _ _` SUBST1_TAC >> simp[NoAsms,not_fresh_at_def]) >>
     `not_local_ptr cenv (FEMPTY::scs) p` by
       (irule exprSimOperandsTheory.fresh_not_local_ptr >> qexists_tac `sd` >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `h' = h /\ ov' = ov /\ ep' = ep` by (Cases_on `bd` >> simp[Abbr `dyn`]) >>
  map_every (fn q => qpat_x_assum q SUBST_ALL_TAC) [`h' = h`,`ov' = ov`,`ep' = ep`] >>
  `preA.cs_current_insts =
       [mk_inst h MUL [Var idx;Lit (n2w (type_slot_size elem_tv))] [ov]] ++
       (if dyn then
          [mk_inst (h+1) ADD [Lit 1w;Var ov] [STRING #"%" (toString (sd.cs_next_var + 6))]]
        else []) ++
       [mk_inst (h + (if dyn then 2 else 1)) ADD
          [Lit slot;Var (if dyn then STRING #"%" (toString (sd.cs_next_var + 6)) else ov)] [ep]]` by
    (qpat_assum `preA.cs_current_insts = _` SUBST1_TAC >>
     qpat_assum `stride = type_slot_size elem_tv` SUBST1_TAC >>
     qpat_assum `totoA = _` SUBST1_TAC >> Cases_on `bd` >> simp[Abbr `dyn`]) >>
  `slot_copy_external preA (Var ep)` by
    (`not_fresh_at preA ep` by
       (simp[NoAsms,not_fresh_at_def] >>
        qpat_assum `ep = STRING _ _` SUBST1_TAC >>
        qpat_assum `preA.cs_next_var = _ + _` SUBST1_TAC >>
        Cases_on `bd` >> simp[Abbr `dyn`] >> decide_tac) >>
     qpat_assum `not_fresh_at preA ep`
       (mp_tac o REWRITE_RULE [not_fresh_at_def]) >>
     simp[NoAsms,slot_copy_external_def,slot_copy_var_def] >> metis_tac[arithmeticTheory.LESS_EQ_ADD]) >>
  `lookup_block preA.cs_current_bb func.fn_blocks = SOME
      <|bb_label := preA.cs_current_bb;
        bb_instructions := preA.cs_current_insts ++ slot_copy_init_insts preA|>` by
    (qpat_assum `lookup_block preA.cs_current_bb func.fn_blocks = SOME headBB` mp_tac >>
     simp[NoAsms,Abbr `headBB`]) >>
  `lookup_block (slot_copy_cond preA) func.fn_blocks = SOME
      <|bb_label := slot_copy_cond preA;
        bb_instructions := slot_copy_cond_insts preA (type_slot_size elem_tv)|>` by
    (qpat_assum `lookup_block (slot_copy_cond preA) _ = _` mp_tac >>
     qpat_assum `stride = type_slot_size elem_tv` (fn th => simp[NoAsms,th])) >>
  qabbrev_tac `headOut = if (case bd of Dynamic cap => T | Fixed cap => F)
                         then [dv;ov;STRING #"%" (toString (sd.cs_next_var + 6));ep]
                         else [dv;ov;ep]` >>
  `ALL_DISTINCT headOut /\ ~MEM idx headOut /\ ~MEM p headOut /\
   (!x. MEM x headOut ==> ~not_fresh_at sd x)` by
    (simp[NoAsms,Abbr `headOut`] >>
     map_every (fn q => qpat_assum q SUBST1_TAC)
       [`dv = STRING _ _`,`ov = STRING _ _`,`ep = STRING _ _`,
        `idx = STRING _ _`,`p = STRING _ _`] >>
     Cases_on `bd` >> simp[NoAsms,Abbr `dyn`,not_fresh_at_def] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     pop_assum SUBST1_TAC >> simp[]) >>
  `!x. MEM x headOut ==> ~not_fresh_at sa x` by
    (rpt strip_tac >>
     `not_fresh_at sd x` by
       (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
     qpat_assum `!x. MEM x headOut ==> ~not_fresh_at sd x` (qspec_then `x` mp_tac) >>
     qpat_assum `not_fresh_at sd x` mp_tac >>
     qpat_assum `MEM x headOut` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  `!x. lvo = Var x ==> ~MEM x headOut` by
    (rpt strip_tac >>
     `not_fresh_at sd x` by
       (qpat_assum `!x. lvo = Var x ==> not_fresh_at sd x` (drule_then ACCEPT_TAC)) >>
     qpat_assum `!x. MEM x headOut ==> ~not_fresh_at sd x` (qspec_then `x` mp_tac) >>
     qpat_assum `not_fresh_at sd x` mp_tac >>
     qpat_assum `MEM x headOut` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  rename1 `gas_admissible (eval_for cx elem_tv id body' (a'::rs'))
                          (stmt_res_ok lctx) head_es` >>
  namedCases_on `compile_expr cenv (ArrayT typ bd) (TopLevelName (ArrayT typ bd) nid) sa`
    ["iterPlace iterEnd"] >>
  qspecl_then [`DF`,`lo`,`d`,`ctx`,`func`,`cx`,`RetQ`,`lctx`,`cenv`,`es`,`sa`,`s0`,`G0`,`tn0`,
    `tr`,`slot`,`dst`,`elem_tv`,`typ`,`bd`,`vs`,`alen`,`nb`,`id`,`env`,`p`,`idx`,`cond`,`lvo`,`sd`,
    `body'`,`st0`,`explicit`,`PG`,`dv`,`ov`,`STRING #"%" (toString (sd.cs_next_var + 6))`,
    `ep`,`h`,`exit`,`bod`,`incr`,`condBB`,`headBB`,`preA`,`sdecl`,`bc`,`copyA`,`ai`,
    `cenv`,`ArrayT typ bd`,`ArrayT typ bd`,`nid`,`sa`,`iterPlace`,`iterEnd`]
    (mp_tac o BETA_RULE o REWRITE_RULE [LET_THM]) for_storage_array_head_full >>
  impl_tac >-
    (rpt conj_tac >>> SELECT_LT_THEN (first_assum ACCEPT_TAC) ALL_TAC
     >- (qpat_assum `preA.cs_current_insts = [_] ++ (if dyn then _ else _) ++ [_]` mp_tac >>
         Cases_on `bd` >> simp[NoAsms,Abbr `dyn`]) >>
     qpat_assum `Abbrev (headOut = _)`
       (fn th => rewrite_tac[GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
     first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then [`a'`,`rs'`,`head_es`,`s''`,`G`,`tn'`] mp_tac) >>
  BETA_TAC >>
  impl_tac >-
    (rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon cx st0 H head_es.storage_trace ==> ?k off. _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     qpat_assum `Abbrev (Fr = _)` (fn th =>
       disch_then (qx_choose_then `k` (qx_choose_then `off'`
         (strip_assume_tac o BETA_RULE o
          PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] th])))) >>
     qexistsl_tac [`k`,`off'`] >>
     rpt conj_tac >>> SELECT_LT_THEN (first_assum ACCEPT_TAC) ALL_TAC >>
     map_every (fn q => qpat_assum q (fn th => pure_rewrite_tac [th]))
       [`idx = STRING _ _`,`p = STRING _ _`,`cond = fresh_label_output _ _`,
        `slot = n2w off`,`nb = _`,`sd.cs_next_var = _`,
        `sd.cs_next_label = _`,`sd.cs_next_id = _`] >>
     pure_rewrite_tac [GSYM arithmeticTheory.ADD_ASSOC, wordsTheory.n2w_11] >>>
     SELECT_LT_THEN (first_assum ACCEPT_TAC) ALL_TAC >>>
     SELECT_LT_THEN (qpat_assum `LENGTH vs = alen` (ACCEPT_TAC o SYM)) ALL_TAC >>>
     SELECT_LT_THEN (qpat_assum `Abbrev (vs = _)`
       (ACCEPT_TAC o REWRITE_RULE [markerTheory.Abbrev_def])) ALL_TAC >>
     `w2n dst + 32 * type_slot_size elem_tv = 32 * type_slot_size elem_tv + w2n dst`
       by irule arithmeticTheory.ADD_COMM >>
     simp[NoAsms] >>> SELECT_LT_THEN (first_assum ACCEPT_TAC) ALL_TAC) >>
  disch_then (strip_assume_tac o CONJUNCT2) >>
  qpat_x_assum `gas_outcome_full _ _ _ _
    (bind (read_result cx a') _) (head_es,s'',G,tn') _ _`
    (mp_then Any irule gas_outcome_full_post_mono o PURE_REWRITE_RULE [ETA_THM]) >>
  reverse conj_tac >- simp[Abbr `R`] >>
  BETA_TAC >> rpt gen_tac >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`v`,`k`] >>
  simp_tac (srw_ss()) [NoAsms] >>
  rpt conj_tac >>> SELECT_LT_THEN (first_assum ACCEPT_TAC) ALL_TAC >>
  map_every (fn q => qpat_assum q (fn th => pure_once_rewrite_tac [GSYM th]))
    [`copyA = slot_copy_final preA (Var ep) (Var p) stride _`,
     `idx = STRING _ _`, `p = STRING _ _`, `sd.cs_next_id = _`, `nb = _`] >>
  rpt conj_tac >>> SELECT_LT_THEN (first_assum ACCEPT_TAC) ALL_TAC
  >- (qpat_assum `expr_sim_inv bc cx _ _`
        (mp_tac o cj 2 o REWRITE_RULE [exprSimHypsDefsTheory.expr_sim_inv_def]) >>
      simp[NoAsms,vyperTypeInvariantsTheory.state_well_typed_def,
           vyperTypeInvariantsTheory.scope_well_typed_def,FLOOKUP_UPDATE])
  >- (qpat_assum `Abbrev (Fr = _)`
        (fn th => pure_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
      BETA_TAC >> rpt conj_tac >> first_assum ACCEPT_TAC)
  >- (qpat_assum `t'.vs_inst_idx = LENGTH copyA.cs_current_insts` SUBST1_TAC >>
      qpat_assum `copyA.cs_current_insts = []` SUBST1_TAC >> simp[NoAsms]) >>>
  SELECT_LT_THEN
    (pure_once_rewrite_tac [arithmeticTheory.ADD_ASSOC] >>
     map_every (fn q => qpat_assum q (fn th => pure_once_rewrite_tac [GSYM th]))
      [`sd.cs_next_var = _`, `idx = STRING _ _`, `p = STRING _ _`] >>
     first_assum ACCEPT_TAC) ALL_TAC >>>
  SELECT_LT_THEN
    (qpat_assum `ai.inst_id = sd.cs_next_id` (fn th => pure_once_rewrite_tac [GSYM th]) >>
     first_assum ACCEPT_TAC) ALL_TAC
  >- (qpat_assum `stmt_state_rel H ctx func bc cx _ t'`
        (strip_assume_tac o MATCH_MP stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
      once_rewrite_tac [arithmeticTheory.ADD_COMM] >>
      irule alloca_site_registered_below >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexists_tac `ai.inst_id` >> first_assum ACCEPT_TAC)
  >- (qx_genl_tac [`nm`,`bOld`,`szOld`] >> disch_tac >>
      qpat_assum `stmt_state_rel H ctx func bc cx _ t'`
        (strip_assume_tac o SIMP_RULE (srw_ss()) [] o
         MATCH_MP stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
      qmatch_asmsub_abbrev_tac `local_ptrs_rel func bc (pushed::head_es.scopes) t'` >>
      `lookup_scopes id head_es.scopes = NONE` by
        (qpat_assum `!H. valid_horizon cx st0 H head_es.storage_trace ==> ?k off. _`
          (qspec_then `storage_trace_horizon head_es.storage_trace` mp_tac) >>
         impl_tac >- (qpat_assum `storage_trace_domain cx st0 head_es.storage_trace`
           (mp_tac o REWRITE_RULE [storage_trace_domain_def]) >> simp[NoAsms]) >>
         disch_then strip_assume_tac >> first_assum ACCEPT_TAC) >>
      qpat_x_assum `local_region cenv head_es.scopes t' nm bOld szOld`
        (strip_assume_tac o REWRITE_RULE [local_region_def]) >>
      `nm <> id` by
        (disch_then SUBST_ALL_TAC >>
         qpat_x_assum `lookup_scopes id head_es.scopes = SOME _` mp_tac >>
         qpat_x_assum `lookup_scopes id head_es.scopes = NONE` (fn th => simp[NoAsms,th])) >>
      `id <> nm` by (qpat_assum `nm <> id` mp_tac >> simp[NoAsms,EQ_SYM_EQ]) >>
      `FLOOKUP bc.ce_vars nm = FLOOKUP cenv.ce_vars nm` by
        (qpat_assum `!n. n <> id ==> FLOOKUP bc.ce_vars n = _` irule >> simp[]) >>
      `local_region bc (pushed::head_es.scopes) t' nm bOld szOld` by
        (simp[local_region_def,vyperStateTheory.lookup_scopes_def,Abbr `pushed`,FLOOKUP_UPDATE] >>
         goal_assum $ drule_at (Pat `lookup_scopes nm _ = SOME _`) >>
         goal_assum $ drule_at (Pat `FLOOKUP cenv.ce_vars nm = SOME _`) >> simp[]) >>
      `local_region bc (pushed::head_es.scopes) t' id (w2n dst) nb` by
        (rewrite_tac[local_region_def] >>
         qexistsl [`THE (FLOOKUP pushed id)`,`p`,`dst`] >>
         conj_tac >- simp[NoAsms,vyperStateTheory.lookup_scopes_def,Abbr `pushed`,FLOOKUP_UPDATE] >>
         rewrite_tac[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      qpat_assum `local_ptrs_rel func bc (pushed::head_es.scopes) t'`
        (qspecl_then [`id`,`nm`,`w2n dst`,`nb`,`bOld`,`szOld`] mp_tac o
         CONJUNCT2 o REWRITE_RULE [local_ptrs_rel_def]) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      simp[NoAsms,loweringStateRelDefsTheory.regions_disjoint_def] >>
      decide_tac)
  >- (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >>
      simp[NoAsms,arithmeticTheory.LESS_EQ_REFL] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rewrite_tac[ret_pc_ok_def] >> rpt gen_tac >> disch_tac >>
  qpat_assum `ret_pc_ok cenv sa s0`
    (drule_then strip_assume_tac o REWRITE_RULE [ret_pc_ok_def]) >>
  conj_tac >- first_assum ACCEPT_TAC >> qexists_tac `w` >>
  qpat_assum `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> _`
    (irule o SPEC_ALL) >> simp[]
QED

Resume compile_for_storage_array_frag_full[prefix]:
  qabbrev_tac `after_iter = (\rs.
    ignore_bind (check (compatible_bound (Dynamic n) (LENGTH rs)) "For too long")
      (eval_for cx elem_tv id body' rs))` >>
  `eval_stmt cx (For id typ (Array (TopLevelName (ArrayT typ bd) nid)) n body') =
   bind (eval_iterator cx (Array (TopLevelName (ArrayT typ bd) nid))) after_iter` by
    (simp[Once vyperInterpreterTheory.evaluate_def, Abbr `after_iter`, lift_option_type_def] >>
     simp[FUN_EQ_THM, bind_def, return_def]) >>
  pop_assum SUBST1_TAC >>
  irule gas_outcome_full_bind >> BETA_TAC >>
  conj_tac
  >- (gen_tac >> simp[NoAsms, Abbr `after_iter`] >>
      irule storage_trace_frame_ignore_bind >>
      simp[NoAsms, storage_trace_frame_checks, cj 4 evaluate_storage_trace_frame]) >>
  conj_tac
  >- (qx_genl_tac [`left`, `value`, `mid`, `t_mid`] >> rpt strip_tac >>
      irule gasExemptCertTheory.gas_exempt_cert_bind_results >>
      qexistsl [`mid`,`t_mid`,`value`] >> BETA_TAC >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_results >>
      first_assum ACCEPT_TAC) >>
  conj_tac >- simp[NoAsms, cj 3 evaluate_storage_trace_frame] >>
  irule gas_outcome_full_pure >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G1`,`ee`,`INL vs`,`t`,`tn1`] >>
  conj_tac >- simp[] >>
  qx_gen_tac `H` >> disch_tac >> BETA_TAC >>
  conj_tac
  >- (qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _`
        (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  `after_iter vs = eval_for cx elem_tv id body' vs` by
    (`compatible_bound (Dynamic n) (LENGTH vs)` by
       (qpat_assum `LENGTH vs = alen` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
     pop_assum (fn th => simp[NoAsms,th,Abbr `after_iter`,check_def,assert_def,
                              ignore_bind_def,bind_def,return_def,FUN_EQ_THM])) >>
  qexists_tac `vs` >> pop_assum (fn th => simp[NoAsms,th]) >>
  `gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
     (eval_for cx elem_tv id body' vs) (ee with gas_obs := [],t,G1,tn1)
     (\H res ei G tn u. res = INL () /\ Done H ei G tn u)
     (\H res ei gt r. ?ex. res = INR ex /\ R H ex ei gt r)` by
    (qpat_assum `gas_outcome_full _ _ _ _ (eval_for _ _ _ _ _) (ee,t,G1,tn1) _ _`
       mp_tac >>
     simp[NoAsms, gas_outcome_full_def, gasStorageTheory.gas_bad_storage_at_def,
          gasOutcomeInitialObsPtrTheory.gas_exempt_cert_initial_obs]) >>
  irule gas_outcome_full_post_mono >>
  qpat_assum `gas_outcome_full _ _ _ _ _ (ee with gas_obs := [],t,G1,tn1) _ _`
    (irule_at Any) >>
  conj_tac
  >- (simp[NoAsms, Abbr `Done`, Abbr `Fr`] >> rpt strip_tac >>
      first_assum (drule_all_then ACCEPT_TAC)) >>
  simp[NoAsms, Abbr `R`] >>
  POP_ASSUM_LIST kall_tac >> rpt gen_tac >>
  disch_then (qx_choose_then `ex` strip_assume_tac) >> gvs[]
  >> metis_tac[haltExitProjTheory.halt_exit_INR_type]
QED

Finalise compile_for_storage_array_frag_full
