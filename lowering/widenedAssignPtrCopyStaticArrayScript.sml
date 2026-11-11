(* Fixed-array typed-copy pointer execution. *)
Theory widenedAssignPtrCopyStaticArray
Ancestors
  widenedAssignPtrCopyOffsets assignBasePtrBytesPost assignBasePtrCopyPath
  placeTypedCopyRecursivePath typedCopyDomain typedMemoryCopy
  valueEncodingDefs valueEncoding valueEncodingProps vyperTyping
  vyperTypeExprSoundness vyperTypeABI compileEnv emitHelper contextProps
  bodyPtrDefs ptrDiscipline fragGasPathPtr fragExec
  words finite_map pred_set list arithmetic vyperTypeSystem vyperTypeArgFits
  vyperValue exprLoweringProps exprLowering context loweringStateRelDefs
  venomState venomExecSemantics venomInst

Theorem widened_assign_sarray_flat_counted:
  !cenv tenv ctx D PG de se dtv stv cap kvs a b dst src dw sw fn G tn s.
    type_memory_bytes cenv de = type_memory_size dtv /\
    type_memory_bytes cenv se = type_memory_size stv /\
    type_widens_to tenv se de /\
    evaluate_type tenv se = SOME stv /\ evaluate_type tenv de = SOME dtv /\
    type_memory_size dtv = type_memory_size stv /\
    ~is_abi_dynamic cenv.ce_struct_fields de /\
    val_wf (ArrayTV stv (Fixed cap)) (ArrayV (SArrayV kvs)) /\
    compile_copy_sarray_typed cenv dst de src se cap a = ((),b) /\
    eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
    (0 < cap * type_memory_size dtv ==>
      ?x. dst = Var x /\ ptr_covers G tn x s (cap * type_memory_size dtv)) /\
    (0 < cap * type_memory_size stv ==>
      ?x. src = Var x /\ ptr_covers G tn x s (cap * type_memory_size stv)) /\
    w2n dw + cap * type_memory_size dtv < dimword (:256) /\
    w2n sw + cap * type_memory_size stv < dimword (:256) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory (ArrayTV stv (Fixed cap)) (ArrayV (SArrayV kvs)) (w2n sw) m) /\
    fn_has_code a b fn /\ s.vs_current_bb = a.cs_current_bb /\
    s.vs_inst_idx = LENGTH a.cs_current_insts /\ ~s.vs_halted /\
    ~ctx_has_dalloca ctx ==>
    ?G' tn' t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
      t.vs_current_bb = b.cs_current_bb /\
      t.vs_inst_idx = LENGTH b.cs_current_insts /\ ~t.vs_halted /\
      (!m. mem_agree_outside tn'.t_mem t.vs_memory m ==>
        val_in_memory (ArrayTV dtv (Fixed cap)) (ArrayV (SArrayV kvs)) (w2n dw) m) /\
      typed_copy_state_frame a (w2n dw) (cap * type_memory_size dtv) s t /\
      (!x. lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
        op_taint tn' (Var x) = op_taint tn (Var x)) /\
      tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
      tn'.t_imm = tn.t_imm /\
      (!i. ~(w2n dw <= i /\ i < w2n dw + cap * type_memory_size dtv) ==>
        (i IN tn'.t_mem <=> i IN tn.t_mem))
Proof
  rpt gen_tac >> strip_tac >>
  `stv = dtv` by metis_tac[typed_copy_static_widening] >>
  qpat_x_assum `stv = dtv` SUBST_ALL_TAC >>
  `compile_copy_memory dst src (cap * type_memory_size dtv) a = ((),b)` by
    (qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_store_memory_typed_def]) >>
  Cases_on `cap * type_memory_size dtv = 0`
  >- (gvs[compile_copy_memory_def, comp_return_def] >>
      qexistsl_tac [`G`,`tn`,`s`] >> simp[cj 1 gas_path_ptr_rules] >>
      rpt strip_tac >> irule valueCopyTheory.val_in_memory_relocate >>
      simp[] >> qexistsl_tac [`w2n sw`,`0`,`m`] >>
      simp[mem_bytes_at_def, loweringPostsTheory.val_footprint_def,
           type_memory_size_def]) >>
  `0 < cap * type_memory_size dtv` by decide_tac >> gvs[eval_operand_def] >>
  `cap * type_memory_size dtv < dimword (:256)` by decide_tac >>
  `val_footprint (ArrayTV dtv (Fixed cap)) (ArrayV (SArrayV kvs)) <=
    cap * type_memory_size dtv` by
    simp[loweringPostsTheory.val_footprint_def, type_memory_size_def] >>
  `0 < cap * type_memory_size dtv` by simp[] >>
  drule_all (SRULE [] assign_base_copy_memory_robust_endpoint_ptr) >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  qpat_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  `b.cs_current_bb = a.cs_current_bb` by
    metis_tac[abiTuplePropsTheory.compile_copy_memory_extends, same_blocks_def] >>
  `eval_operand (Var x) s = SOME dw /\
   eval_operand (Var x') s = SOME sw /\
   eval_operand (Lit (n2w (cap * type_memory_size dtv))) s =
     SOME (n2w (cap * type_memory_size dtv):bytes32) /\
   w2n (n2w (cap * type_memory_size dtv):bytes32) = cap * type_memory_size dtv` by
    simp[eval_operand_def, w2n_n2w] >>
  qpat_assum `eval_operand (Var x) s = SOME dw`
    (mp_then Any mp_tac (SRULE [] assignTuplePtrLocalFixedCopyTheory.mcopy_operand_taint_frames_ptr)) >>
  disch_then (fn th => qpat_assum `eval_operand (Var x') s = SOME sw`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `eval_operand (Lit _) s = SOME _`
    (mp_then Any mp_tac th)) >>
  simp[] >> disch_then (qspecl_then [`tn`,`a.cs_next_id`] strip_assume_tac) >>
  simp[typed_copy_mcopy_state_frame, step_prov_def, set_prov_def, out_prov_def,
       mk_inst_def, DRESTRICT_UNIV, op_taint_def, lookup_var_def,
       mcopy_def, write_memory_with_expansion_def] >>
  qpat_x_assum `!i. ~(_ <= i) \/ ~(_ < _) ==> _` mp_tac >>
  simp[mk_inst_def, mcopy_def, write_memory_with_expansion_def]
QED
