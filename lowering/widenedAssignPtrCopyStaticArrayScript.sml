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
  widenedAssignPtrIndexAssembly valueEncodingProofs placeMemoryTypedBase

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

Theorem widened_assign_typed_sarray_counted:
  !cenv tenv ctx D PG de cap sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
        sz = type_memory_size tv) fields) /\
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
      !a b dst src dw sw fn G tn s.
        compile_store_memory_typed cenv dst cd src cs a = ((),b) /\
        (!x. dst = Var x ==> not_fresh_at a x) /\
        (!x. src = Var x ==> not_fresh_at a x) /\
        eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
        op_taint tn dst = {} /\ op_taint tn src = {} /\
        (0 < type_memory_size cdt ==>
          ?x. dst = Var x /\ ptr_covers G tn x s (type_memory_size cdt)) /\
        (0 < type_memory_size cst ==>
          ?x. src = Var x /\ ptr_covers G tn x s (type_memory_size cst)) /\
        w2n dw + type_memory_size cdt < dimword (:256) /\
        w2n sw + type_memory_size cst < dimword (:256) /\
        (w2n dw + type_memory_size cdt <= w2n sw \/
         w2n sw + type_memory_size cst <= w2n dw) /\
        (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
          val_in_memory cst cv (w2n sw) m) /\
        fn_has_code a b fn /\ 
        s.vs_current_bb = a.cs_current_bb /\
        s.vs_inst_idx = LENGTH a.cs_current_insts /\ ~s.vs_halted /\
        ~ctx_has_dalloca ctx ==>
        ?G' tn' t.
          gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
          t.vs_current_bb = b.cs_current_bb /\
          t.vs_inst_idx = LENGTH b.cs_current_insts /\ ~t.vs_halted /\
          (!m. mem_agree_outside tn'.t_mem t.vs_memory m ==>
            val_in_memory cdt cv (w2n dw) m) /\
          typed_copy_state_frame a (w2n dw) (type_memory_size cdt) s t /\
          (!x. not_fresh_at a x ==>
            lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
            op_taint tn' (Var x) = op_taint tn (Var x)) /\
          tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
          tn'.t_imm = tn.t_imm /\
          (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size cdt) ==>
            (i IN tn'.t_mem <=> i IN tn.t_mem))) ==>
    !a b dst src dw sw fn G tn s.
      compile_store_memory_typed cenv dst (ArrayT de (Fixed cap)) src sty a = ((),b) /\
      (!x. dst = Var x ==> not_fresh_at a x) /\
      (!x. src = Var x ==> not_fresh_at a x) /\
      eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
      op_taint tn dst = {} /\ op_taint tn src = {} /\
      (0 < type_memory_size dtv ==>
        ?x. dst = Var x /\ ptr_covers G tn x s (type_memory_size dtv)) /\
      (0 < type_memory_size stv ==>
        ?x. src = Var x /\ ptr_covers G tn x s (type_memory_size stv)) /\
      w2n dw + type_memory_size dtv < dimword (:256) /\
      w2n sw + type_memory_size stv < dimword (:256) /\
      (w2n dw + type_memory_size dtv <= w2n sw \/
       w2n sw + type_memory_size stv <= w2n dw) /\
      (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        val_in_memory stv v (w2n sw) m) /\
      fn_has_code a b fn /\ 
      s.vs_current_bb = a.cs_current_bb /\
      s.vs_inst_idx = LENGTH a.cs_current_insts /\ ~s.vs_halted /\
      ~ctx_has_dalloca ctx ==>
      ?G' tn' t.
        gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
        t.vs_current_bb = b.cs_current_bb /\
        t.vs_inst_idx = LENGTH b.cs_current_insts /\ ~t.vs_halted /\
        (!m. mem_agree_outside tn'.t_mem t.vs_memory m ==>
          val_in_memory dtv v (w2n dw) m) /\
        typed_copy_state_frame a (w2n dw) (type_memory_size dtv) s t /\
        (!x. not_fresh_at a x ==>
          lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
          op_taint tn' (Var x) = op_taint tn (Var x)) /\
        tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
        (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size dtv) ==>
          (i IN tn'.t_mem <=> i IN tn.t_mem))
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
  rpt gen_tac >> strip_tac >> (
  `compile_copy_sarray_typed cenv dst de src se cap a = ((),b)` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_store_memory_typed_def, is_word_type_def,
          is_bytestring_type_def]) >>
  Cases_on `type_memory_size tv' = type_memory_size tv /\
            ~is_abi_dynamic cenv.ce_struct_fields de`
  >- (qpat_x_assum `type_memory_size tv' = _ /\ _` strip_assume_tac >>
      qpat_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _`
        (mp_then (Pos (el 9)) mp_tac widened_assign_sarray_flat_counted) >>
      disch_then (fn th => qpat_assum `evaluate_type tenv se = SOME tv`
        (mp_then Any mp_tac th)) >>
      disch_then (fn th => qpat_assum `evaluate_type tenv de = SOME tv'`
        (mp_then Any mp_tac th)) >>
      disch_then (fn th => qpat_assum `eval_operand dst s = SOME dw`
        (mp_then Any mp_tac th)) >>
      disch_then (fn th => qpat_assum `eval_operand src s = SOME sw`
        (mp_then Any mp_tac th)) >>
      disch_then (fn th => qpat_assum `!m. mem_agree_outside _ _ _ ==> _`
        (mp_then Any mp_tac th)) >>
      disch_then (fn th => qpat_assum `fn_has_code a b fn`
        (mp_then Any mp_tac th)) >>
      disch_then (qspecl_then [`ctx`,`D`,`PG`,`G`] mp_tac) >>
      (impl_tac >-
        (qpat_x_assum `!cd cs cdt cst cv. _` kall_tac >>
         qpat_x_assum `!name fields. _` kall_tac >>
         fs[type_memory_size_def])) >>
      strip_tac >>
      qpat_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
      qpat_x_assum `!cd cs cdt cst cv. _` kall_tac >>
      qpat_x_assum `!name fields. _` kall_tac >>
      fs[type_memory_size_def] >> metis_tac[]) >>
  qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  disch_tac >>
  namedCases_on `fresh_label "typed_sa_cond" a` ["hdr l1"] >> fs[] >>
  namedCases_on `fresh_label "typed_sa_body" l1` ["blabel l2"] >> fs[] >>
  namedCases_on `fresh_label "typed_sa_exit" l2` ["exit l3"] >> fs[] >>
  namedCases_on `fresh_var l3` ["counter init"] >> fs[] >>
  namedCases_on `emit_inst ASSIGN [Lit 0w] [counter] init` ["uu st0"] >> Cases_on `uu` >> fs[] >>
  namedCases_on `emit_inst JMP [Label hdr] [] st0` ["uu st1"] >> Cases_on `uu` >> fs[] >>
  namedCases_on `new_block hdr st1` ["u1 sth"] >> fs[] >>
  namedCases_on `emit_op LT [Var counter; Lit (n2w cap)] sth` ["lt h1"] >> fs[] >>
  namedCases_on `emit_op ISZERO [lt] h1` ["done stj"] >> fs[] >>
  namedCases_on `emit_inst JNZ [done; Label exit; Label blabel] [] stj` ["uu st2"] >> Cases_on `uu` >> fs[] >>
  namedCases_on `new_block blabel st2` ["u2 stb"] >> fs[] >>
  namedCases_on `emit_op MUL [Var counter; Lit (n2w (type_memory_size tv))] stb` ["so b1"] >> fs[] >>
  namedCases_on `emit_op MUL [Var counter; Lit (n2w (type_memory_size tv'))] b1` ["doff b2"] >> fs[] >>
  namedCases_on `emit_op ADD [src; so] b2` ["sp b3"] >> fs[] >>
  namedCases_on `emit_op ADD [dst; doff] b3` ["dp b4"] >> fs[] >>
  namedCases_on `compile_store_memory_typed cenv dp de sp se b4` ["uu b5"] >> Cases_on `uu` >> fs[] >>
  namedCases_on `emit_op ADD [Var counter; Lit 1w] b5` ["inc b6"] >> fs[] >>
  namedCases_on `emit_inst ASSIGN [inc] [counter] b6` ["uu ste"] >> Cases_on `uu` >> fs[] >>
  namedCases_on `emit_inst JMP [Label hdr] [] ste` ["uu st3"] >> Cases_on `uu` >> fs[] >>
  namedCases_on `new_block exit st3` ["u3 stx"] >> fs[] >>
  drule_all typed_copy_sarray_slow_layout >> strip_tac >>
  `?lv. lt = Var lv` by metis_tac[exprLoweringPropsTheory.emitted_insts_emit_op_local] >>
  `?dv. done = Var dv` by metis_tac[exprLoweringPropsTheory.emitted_insts_emit_op_local] >> gvs[] >>
  `!i. i < cap ==>
    val_wf tv (case ALOOKUP l i of NONE => default_value tv | SOME v => v) /\
    val_wf tv' (case ALOOKUP l i of NONE => default_value tv | SOME v => v)` by
    (gen_tac >> disch_tac >> conj_tac
     >- (irule typed_copy_sparse_lookup_wf >> qexists_tac `cap` >> fs[val_wf_def]) >>
     qpat_assum `default_value tv = default_value tv'` (fn th => rewrite_tac[th]) >>
     irule typed_copy_sparse_lookup_wf >> qexists_tac `cap` >> fs[val_wf_def]) >>
  `!i m. i < cap /\ mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv (case ALOOKUP l i of NONE => default_value tv | SOME v => v)
      (w2n sw + i * type_memory_size tv) m` by
    (rpt strip_tac >> irule typed_copy_sarray_element >> metis_tac[]) >>
  `ci_mono stb b1 /\ ci_mono b1 b2 /\ ci_mono b2 b3 /\
   ci_mono b3 b4 /\ ci_mono b4 b5 /\ ci_mono b5 b6 /\
   ci_mono b6 ste` by
    metis_tac[ci_mono_emit_op, ci_mono_emit_inst,
      cj 1 ci_mono_typed_memory_family, pairTheory.SND] >>
  `cs_extends a stb /\ cs_extends stb b1 /\ cs_extends b1 b2 /\
   cs_extends b2 b3 /\ cs_extends b3 b4 /\ cs_extends b4 b5 /\
   cs_extends b5 b6 /\ cs_extends b6 ste` by gvs[ci_mono_def] >>
  `cs_extends ste st3 /\ cs_extends st3 b` by
    (conj_tac
     >- (qpat_assum `emit_inst JMP _ _ ste = _`
           (mp_then Any mp_tac cs_extends_emit_inst) >> simp[]) >>
     qpat_assum `new_block exit st3 = _`
       (mp_then Any mp_tac cs_extends_new_block) >> simp[]) >>
  `cs_extends a b4` by metis_tac[cs_extends_trans] >>
  `cs_extends b5 b` by metis_tac[cs_extends_trans] >>
  `fn_has_code b4 b5 fn` by metis_tac[fn_has_code_mid] >>
  `?H tm t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    (!i m. i < cap /\ mem_agree_outside tm.t_mem t.vs_memory m ==>
      val_in_memory tv' (case ALOOKUP l i of NONE => default_value tv | SOME v => v)
        (w2n dw + i * type_memory_size tv') m) /\
    typed_copy_state_frame a (w2n dw) (cap * type_memory_size tv') s t /\
    (!x. not_fresh_at a x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + cap * type_memory_size tv') ==>
      (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts` by
    (qpat_assum `compile_store_memory_typed cenv dp de sp se b4 = _`
       (mp_then Any mp_tac widened_assign_index_loop_counted) >>
     disch_then (fn th => qpat_assum `emit_op MUL [Var counter; Lit (n2w (type_memory_size tv))] stb = _`
       (mp_then Any mp_tac th)) >>
     disch_then (fn th => qpat_assum `emit_op MUL [Var counter; Lit (n2w (type_memory_size tv'))] b1 = _`
       (mp_then Any mp_tac th)) >>
     disch_then (fn th => qpat_assum `emit_op LT _ sth = _` (mp_then Any mp_tac th)) >>
     disch_then (fn th => qpat_assum `emit_op ISZERO _ h1 = _` (mp_then Any mp_tac th)) >>
     disch_then (fn th => qpat_assum `emit_inst JNZ _ _ stj = _` (mp_then Any mp_tac th)) >>
     disch_then (fn th => qpat_assum `new_block blabel st2 = _` (mp_then Any mp_tac th)) >>
     disch_then (fn th => qpat_assum `new_block hdr st1 = _` (mp_then Any mp_tac th)) >>
     disch_then (fn th => qpat_assum `emit_inst JMP _ _ st0 = _` (mp_then Any mp_tac th)) >>
     disch_then (fn th => qpat_assum `emit_inst ASSIGN _ _ init = _` (mp_then Any mp_tac th)) >>
     disch_then (fn th => qpat_assum `emit_op ADD [src; so] b2 = _` (mp_then Any mp_tac th)) >>
     disch_then (fn th => qpat_assum `emit_op ADD [Var counter; Lit 1w] b5 = _` (mp_then Any mp_tac th)) >>
     disch_then (fn th => qpat_assum `emit_inst ASSIGN _ _ b6 = _` (mp_then Any mp_tac th)) >>
     disch_then (fn th => qpat_assum `emit_inst JMP _ _ ste = _` (mp_then Any mp_tac th)) >>
     disch_then (fn th => qpat_assum `new_block exit st3 = _` (mp_then Any mp_tac th)) >>
     disch_then ho_match_mp_tac >>
     qexistsl_tac [`sw`, `dst`] >>
     `op_taint tn (Lit (n2w cap)) = {}` by simp[op_taint_def] >>
     simp[eval_operand_def, op_prov_def, type_memory_size_def] >>
     reverse (rpt conj_tac)
     >- (rpt gen_tac >> strip_tac >>
         qpat_x_assum `!cd cs cdt cst cv. _`
           (qspecl_then [`de`,`se`,`tv'`,`tv`,
             `case ALOOKUP l i of NONE => default_value tv' | SOME v => v`] mp_tac) >>
         simp[type_rank_def] >>
         (impl_tac >-
           (simp[] >> conj_tac
            >- (qpat_assum `default_value tv = default_value tv'`
                  (fn th => rewrite_tac[GSYM th]) >>
                irule typed_memory_sparse_lookup_type >>
                conj_tac
                >- (qexistsl_tac [`se`,`tenv`] >> simp[]) >>
                qexists_tac `cap` >> simp[value_has_type_def]) >>
            conj_tac
            >- (irule typed_memory_sparse_lookup_type >>
                conj_tac
                >- (qexistsl_tac [`de`,`tenv`] >> simp[]) >>
                qexists_tac `cap` >> simp[value_has_type_def]) >>
            metis_tac[])) >>
         disch_then (fn th => qpat_assum
           `compile_store_memory_typed cenv dp de sp se b4 = _`
           (mp_then Any mp_tac th)) >>
         disch_then ho_match_mp_tac >>
         qexists_tac `bw` >> simp[] >>
         `ci_mono b3 b4` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
         `!x. dp = Var x ==> not_fresh_at b4 x` by
           (qpat_assum `emit_op ADD [dst; doff] b3 = _`
               (mp_then Any mp_tac typed_copy_emit_op_fresh) >> simp[]) >>
         `!x. sp = Var x ==> not_fresh_at b4 x` by
           metis_tac[typed_copy_emit_op_fresh, typed_copy_operand_fresh_mono] >>
         simp[]) >>
     fs[type_memory_size_def] >> metis_tac[]) >>
  qexistsl_tac [`H`,`tm`,`t`] >>
  simp[type_memory_size_def] >>
  rpt strip_tac >> irule typed_copy_sparse_prefix_complete >>
  simp[value_has_type_def, typed_copy_sparse_prefix_def] >>
  qpat_assum `default_value tv = default_value tv'`
    (fn th => rewrite_tac[GSYM th]) >> metis_tac[])
QED
