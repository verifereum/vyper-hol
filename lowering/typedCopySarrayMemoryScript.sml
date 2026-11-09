(* Joint memory execution of fixed arrays. *)
Theory typedCopySarrayMemory
Ancestors
  typedCopyIndexMemory typedCopyPrimitiveMemory typedCopyDomain typedMemoryCopy
  fragExecMem context compileEnv emitHelper exprLoweringProps
  vyperTypeSystem vyperTypeArgFits vyperValue vyperTyping valueEncoding
  valueEncodingProofs loweringPosts words list arithmetic

Theorem typed_copy_sarray_bulk_frag_mem[local]:
  compile_copy_sarray_typed cenv dst dty src sty N sa = ((),sb) /\
  type_memory_bytes cenv dty = type_memory_bytes cenv sty /\
  ~is_abi_dynamic cenv.ce_struct_fields dty /\ type_memory_bytes cenv dty = ds /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ N * ds < dimword (:256) /\
  val_in_memory tv v (w2n sw) s.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= N * ds /\ N * ds <= type_memory_size tv /\
  w2n sw + N * ds <= s.vs_alloca_next /\
  w2n dw + N * ds <= s.vs_alloca_next ==>
  frag_exec_mem ctx sa sb (\u. u = s)
    (\t. val_in_memory tv v (w2n dw) t.vs_memory /\
         typed_copy_state_frame sa (w2n dw) (type_memory_size tv) s t) (\r. F)
Proof
  strip_tac >>
  qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def] >> strip_tac >>
  irule typed_copy_fixed_frag_mem >> simp[] >>
  qexistsl_tac [`sw`, `dst`, `N * ds`, `src`] >> simp[]
QED

Theorem typed_copy_sarray_cond_frag_mem[local]:
  compile_copy_sarray_typed cenv dst dty src sty N sa = ((),sb) /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ N < dimword (:256) /\
  w2n sw + N * type_memory_size stv < dimword (:256) /\
  w2n dw + N * type_memory_size dtv < dimword (:256) /\
  (w2n sw + N * type_memory_size stv <= w2n dw \/
   w2n dw + N * type_memory_size dtv <= w2n sw) /\
  w2n sw + N * type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + N * type_memory_size dtv <= s.vs_alloca_next /\
  type_memory_size tv = N * type_memory_size dtv /\
  ((type_memory_size dtv = type_memory_size stv /\
    ~is_abi_dynamic cenv.ce_struct_fields dty) ==>
    val_in_memory tv v (w2n sw) s.vs_memory /\ val_wf tv v /\
    val_footprint tv v <= N * type_memory_size dtv) /\
  (~(type_memory_size dtv = type_memory_size stv /\
     ~is_abi_dynamic cenv.ce_struct_fields dty) ==>
    (!i. i < N ==>
      (!dst src sa sb s dw sw.
        compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
        (!x. dst = Var x ==> not_fresh_at sa x) /\
        (!x. src = Var x ==> not_fresh_at sa x) /\
        eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
        val_in_memory stv (f i) (w2n sw) s.vs_memory /\
        w2n sw + type_memory_size stv < dimword (:256) /\
        w2n dw + type_memory_size dtv < dimword (:256) /\
        (w2n sw + type_memory_size stv <= w2n dw \/
         w2n dw + type_memory_size dtv <= w2n sw) /\
        w2n sw + type_memory_size stv <= s.vs_alloca_next /\
        w2n dw + type_memory_size dtv <= s.vs_alloca_next ==>
        frag_exec_mem ctx sa sb (\u. u = s)
          (\t. val_in_memory dtv (f i) (w2n dw) t.vs_memory /\
               typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t) (\r. F)) /\
      val_wf stv (f i) /\ val_wf dtv (f i) /\
      val_in_memory stv (f i) (w2n sw + i * type_memory_size stv) s.vs_memory) /\
    (!mem. (!i. i < N ==> val_in_memory dtv (f i)
      (w2n dw + i * type_memory_size dtv) mem) ==>
      val_in_memory tv v (w2n dw) mem)) ==>
  frag_exec_mem ctx sa sb (\u. u = s)
    (\t. val_in_memory tv v (w2n dw) t.vs_memory /\
      typed_copy_state_frame sa (w2n dw) (type_memory_size tv) s t) (\r. F)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `type_memory_size dtv = type_memory_size stv /\
            ~is_abi_dynamic cenv.ce_struct_fields dty`
  >- (irule typed_copy_sarray_bulk_frag_mem >> simp[] >>
      goal_assum (drule_at (Pat `compile_copy_sarray_typed _ _ _ _ _ _ _ = _`)) >>
      gvs[] >> decide_tac) >>
  `frag_exec_mem ctx sa sb (\u. u = s)
    (\t. (!i. i < N ==> val_in_memory dtv (f i)
       (w2n dw + i * type_memory_size dtv) t.vs_memory) /\
       typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) s t) (\r. F)` by
    (irule typed_copy_sarray_slow_frag_mem >> simp[] >>
     goal_assum (drule_at (Pat `compile_copy_sarray_typed _ _ _ _ _ _ _ = _`)) >>
     qexists_tac `stv` >> gvs[ADD_COMM] >> metis_tac[]) >>
  pop_assum (mp_then Any irule frag_exec_mem_conseq) >> simp[] >> metis_tac[]
QED

Theorem typed_copy_sarray_frag_mem[local]:
  compile_copy_sarray_typed cenv dst dty src sty N sa = ((),sb) /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs)) /\
  val_wf (ArrayTV stv (Fixed N)) (ArrayV (SArrayV kvs)) /\
  val_wf (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs)) /\
  (!i. i < N ==>
    !dst src sa sb s dw sw.
      compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
      (!x. dst = Var x ==> not_fresh_at sa x) /\
      (!x. src = Var x ==> not_fresh_at sa x) /\
      eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
      val_in_memory stv (case ALOOKUP kvs i of NONE => default_value stv | SOME v => v)
        (w2n sw) s.vs_memory /\
      w2n sw + type_memory_size stv < dimword (:256) /\
      w2n dw + type_memory_size dtv < dimword (:256) /\
      (w2n sw + type_memory_size stv <= w2n dw \/
       w2n dw + type_memory_size dtv <= w2n sw) /\
      w2n sw + type_memory_size stv <= s.vs_alloca_next /\
      w2n dw + type_memory_size dtv <= s.vs_alloca_next ==>
      frag_exec_mem ctx sa sb (\u. u = s)
        (\t. val_in_memory dtv
               (case ALOOKUP kvs i of NONE => default_value stv | SOME v => v)
               (w2n dw) t.vs_memory /\
             typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t) (\r. F)) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ N < dimword (:256) /\
  val_in_memory (ArrayTV stv (Fixed N)) (ArrayV (SArrayV kvs)) (w2n sw) s.vs_memory /\
  w2n sw + N * type_memory_size stv < dimword (:256) /\
  w2n dw + N * type_memory_size dtv < dimword (:256) /\
  (w2n sw + N * type_memory_size stv <= w2n dw \/
   w2n dw + N * type_memory_size dtv <= w2n sw) /\
  w2n sw + N * type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + N * type_memory_size dtv <= s.vs_alloca_next ==>
  frag_exec_mem ctx sa sb (\u. u = s)
    (\t. val_in_memory (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs))
       (w2n dw) t.vs_memory /\
      typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) s t) (\r. F)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `type_memory_size (ArrayTV dtv (Fixed N)) = N * type_memory_size dtv` by
    simp[type_memory_size_def] >>
  `frag_exec_mem ctx sa sb (\u. u = s)
    (\t. val_in_memory (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs))
       (w2n dw) t.vs_memory /\ typed_copy_state_frame sa (w2n dw)
       (type_memory_size (ArrayTV dtv (Fixed N))) s t) (\r. F)` suffices_by simp[] >>
  irule typed_copy_sarray_cond_frag_mem >> simp[] >>
  goal_assum (drule_at (Pat `compile_copy_sarray_typed _ _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`dtv`,
    `\i. case ALOOKUP kvs i of NONE => default_value stv | SOME v => v`, `stv`, `sw`] >>
  simp[] >> conj_tac
  >- (strip_tac >> drule_all typed_copy_sarray_representation >>
      strip_tac >> gvs[ADD_COMM] >> metis_tac[]) >>
  strip_tac >>
  `stv = dtv` by metis_tac[typed_copy_static_widening] >>
  qpat_x_assum `stv = dtv` (SUBST_ALL_TAC o SYM) >>
  simp[val_footprint_def, type_memory_size_def]
QED

Theorem typed_copy_sarray_entry_mem:
  !cenv tenv ctx de cap sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname, fty, sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty (ArrayT de (Fixed cap)) /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv (ArrayT de (Fixed cap)) = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    (!cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd <
        type_rank cenv.ce_struct_fields (ArrayT de (Fixed cap)) ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      !dst src sa sb s dw sw.
        compile_store_memory_typed cenv dst cd src cs sa = ((),sb) /\
        (!x. dst = Var x ==> not_fresh_at sa x) /\
        (!x. src = Var x ==> not_fresh_at sa x) /\
        eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
        val_in_memory cst cv (w2n sw) s.vs_memory /\
        w2n sw + type_memory_size cst < dimword (:256) /\
        w2n dw + type_memory_size cdt < dimword (:256) /\
        (w2n sw + type_memory_size cst <= w2n dw \/
         w2n dw + type_memory_size cdt <= w2n sw) /\
        w2n sw + type_memory_size cst <= s.vs_alloca_next /\
        w2n dw + type_memory_size cdt <= s.vs_alloca_next ==>
        frag_exec_mem ctx sa sb (\u. u = s)
          (\t. val_in_memory cdt cv (w2n dw) t.vs_memory /\
               typed_copy_state_frame sa (w2n dw) (type_memory_size cdt) s t) (\r. F)) ==>
    !dst src sa sb s dw sw.
      compile_store_memory_typed cenv dst (ArrayT de (Fixed cap)) src sty sa = ((),sb) /\
      (!x. dst = Var x ==> not_fresh_at sa x) /\
      (!x. src = Var x ==> not_fresh_at sa x) /\
      eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
      val_in_memory stv v (w2n sw) s.vs_memory /\
      w2n sw + type_memory_size stv < dimword (:256) /\
      w2n dw + type_memory_size dtv < dimword (:256) /\
      (w2n sw + type_memory_size stv <= w2n dw \/
       w2n dw + type_memory_size dtv <= w2n sw) /\
      w2n sw + type_memory_size stv <= s.vs_alloca_next /\
      w2n dw + type_memory_size dtv <= s.vs_alloca_next ==>
      frag_exec_mem ctx sa sb (\u. u = s)
        (\t. val_in_memory dtv v (w2n dw) t.vs_memory /\
             typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t) (\r. F)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all typed_copy_array_source >> strip_tac >> gvs[] >>
  `sb = Fixed cap` by
    (drule typed_copy_array_widening >> strip_tac >> gvs[]) >> gvs[] >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  `type_widens_to tenv se de` by
    (qpat_x_assum `type_widens_to _ _ _` mp_tac >>
     simp[type_widens_to_def, arg_type_fits_def, well_formed_type_def,
          evaluate_type_def] >> metis_tac[]) >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  `cap < dimword (:256)` by
    (qpat_x_assum `type_slot_size (ArrayTV tv' (Fixed cap)) < _` mp_tac >>
     simp[type_slot_size_def] >>
     `cap <= cap * type_slot_size tv'` by
       (Cases_on `type_slot_size tv'` >> gvs[MULT_CLAUSES]) >> decide_tac) >>
  `type_memory_bytes cenv de = type_memory_size tv' /\
   type_memory_bytes cenv se = type_memory_size tv` by
    (conj_tac >> irule typed_copy_memory_size >>
     qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  `default_value tv = default_value tv'` by
    metis_tac[typed_copy_default_widening] >>
  suspend "children"
QED

Resume typed_copy_sarray_entry_mem[children]:
  `!i. i < cap ==> !dst src sa sb s dw sw.
    compile_store_memory_typed cenv dst de src se sa = ((),sb) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
    val_in_memory tv (case ALOOKUP l i of NONE => default_value tv | SOME v => v)
      (w2n sw) s.vs_memory /\
    w2n sw + type_memory_size tv < dimword (:256) /\
    w2n dw + type_memory_size tv' < dimword (:256) /\
    (w2n sw + type_memory_size tv <= w2n dw \/
     w2n dw + type_memory_size tv' <= w2n sw) /\
    w2n sw + type_memory_size tv <= s.vs_alloca_next /\
    w2n dw + type_memory_size tv' <= s.vs_alloca_next ==>
    frag_exec_mem ctx sa sb (\u. u = s)
      (\t. val_in_memory tv' (case ALOOKUP l i of NONE => default_value tv | SOME v => v)
             (w2n dw) t.vs_memory /\
           typed_copy_state_frame sa (w2n dw) (type_memory_size tv') s t) (\r. F)` by
    (qx_gen_tac `i` >> strip_tac >>
     simp[ADD_COMM] >>
     qpat_x_assum `!cd cs cdt cst cv. _`
       (qspecl_then [`de`, `se`, `tv'`, `tv`,
         `case ALOOKUP l i of NONE => default_value tv' | SOME v => v`] mp_tac) >>
     simp[Once type_rank_def] >>
     (impl_tac >-
     (`val_wf tv (case ALOOKUP l i of NONE => default_value tv | SOME v => v)` by
       (irule typed_copy_sparse_lookup_wf >> qexists_tac `cap` >> fs[val_wf_def]) >>
     `val_wf tv' (case ALOOKUP l i of NONE => default_value tv | SOME v => v)` by
       (asm_rewrite_tac[] >> irule typed_copy_sparse_lookup_wf >>
        qexists_tac `cap` >> fs[val_wf_def]) >>
     Cases_on `ALOOKUP l i` >> gvs[]
     >- metis_tac[vyperTypingTheory.default_value_well_typed,
                 cj 1 vyperTypingTheory.evaluate_type_well_formed] >>
     metis_tac[valueEncodingProofsTheory.sparse_has_type_lookup])) >>
     disch_then MATCH_ACCEPT_TAC) >>
  suspend "execute"
QED

Resume typed_copy_sarray_entry_mem[execute]:
  rpt strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, is_word_type_def,
       is_bytestring_type_def] >> strip_tac >>
  (reverse (Cases_on `s.vs_inst_idx = LENGTH sa.cs_current_insts`)
   >- simp[frag_exec_mem_def]) >>
  simp[type_memory_size_def] >> irule typed_copy_sarray_frag_mem >>
  simp[value_has_type_def] >>
  (conj_tac >- gvs[type_memory_size_def, ADD_COMM]) >>
  (conj_tac >- gvs[type_memory_size_def, ADD_COMM]) >>
  goal_assum (drule_at (Pat `compile_copy_sarray_typed _ _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`tv`, `sw`, `tenv`] >>
  gvs[type_memory_size_def, value_has_type_def, ADD_COMM] >>
  qpat_x_assum `!i. i < cap ==> _` MATCH_ACCEPT_TAC
QED

Finalise typed_copy_sarray_entry_mem
