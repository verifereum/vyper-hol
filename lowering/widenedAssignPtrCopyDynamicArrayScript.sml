(* Conditional dynamic-array typed-copy pointer execution. *)
Theory widenedAssignPtrCopyDynamicArray
Ancestors
  widenedAssignPtrDynPrefix widenedAssignPtrDynBulkData
  widenedAssignPtrIndexAssembly widenedAssignPtrCopyStaticArray
  typedMemoryCopy representationCleanPtr assignTuplePtrLoadStep
  bodyPtrPrecompileBuiltinsArithmeticValue liveArrayTransportPtr valueEncodingDefs valueEncoding valueEncodingProps
  bodyPtrDefs ptrDiscipline words finite_map pred_set list arithmetic
  vyperTypeSystem vyperTypeArgFits vyperTyping vyperValue context
  exprLowering exprLoweringProps emitHelper compileEnv loweringStateRelDefs
  typedCopyDomain fragExec emitHelperProps venomExecSemantics venomState

Theorem widened_assign_robust_header_data_frame[local]:
  (!m. mem_agree_outside tn s.vs_memory m ==> mem_word_at off m = w) /\
  typed_copy_state_frame a (off+32) len s t /\
  (!i. ~(off+32 <= i /\ i < off+32+len) ==> (i IN tm <=> i IN tn)) ==>
  !m. mem_agree_outside tm t.vs_memory m ==> mem_word_at off m = w
Proof
  strip_tac >>
  `!i. off <= i /\ i < off+32 ==> i NOTIN tn` by
    metis_tac[robust_mem_word_at_clean] >>
  `!i. off <= i /\ i < off+32 ==> i NOTIN tm` by
    (rpt gen_tac >> disch_tac >>
     `~(off+32 <= i /\ i < off+32+len)` by decide_tac >> metis_tac[]) >>
  `mem_word_at off t.vs_memory = mem_word_at off s.vs_memory` by
    (gvs[typed_copy_state_frame_def, typed_copy_frame_def] >>
     simp[mem_word_at_def, GSYM mem_bytes_at_def]) >>
  rpt strip_tac >>
  `mem_word_at off m = mem_word_at off t.vs_memory` by
    (sym_tac >> irule clean_word_mem_agree >> qexists_tac `tm` >> simp[]) >>
  `mem_word_at off s.vs_memory = w` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >> simp[]
QED

Theorem widened_assign_typed_dynarray_counted:
  !cenv tenv ctx D PG de cap sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
        sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty (ArrayT de (Dynamic cap)) /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv (ArrayT de (Dynamic cap)) = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    (!cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd <
        type_rank cenv.ce_struct_fields (ArrayT de (Dynamic cap)) ==>
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
      compile_store_memory_typed cenv dst (ArrayT de (Dynamic cap)) src sty a = ((),b) /\
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
  `?scap. sb = Dynamic scap /\ scap <= cap` by
    (drule typed_copy_array_widening >> strip_tac >> gvs[]) >> gvs[] >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  `type_widens_to tenv se de` by
    (qpat_x_assum `type_widens_to _ _ _` mp_tac >>
     simp[type_widens_to_def, arg_type_fits_def, well_formed_type_def,
          evaluate_type_def] >> metis_tac[]) >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  `cap < dimword (:256)` by
    (qpat_x_assum `type_slot_size (ArrayTV tv' (Dynamic cap)) < _` mp_tac >>
     simp[type_slot_size_def] >>
     `cap <= cap * type_slot_size tv'` by
       (Cases_on `type_slot_size tv'` >> gvs[MULT_CLAUSES]) >> decide_tac) >>
  `type_memory_bytes cenv de = type_memory_size tv' /\
   type_memory_bytes cenv se = type_memory_size tv` by
    (conj_tac >> irule typed_copy_memory_size >>
     qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> disch_tac >> RULE_L_ASSUM_TAC CONJUNCTS >>
  `?dv sv. dst = Var dv /\ src = Var sv` by
    gvs[type_memory_size_def] >>
  gnvs[] >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, is_word_type_def,
       is_bytestring_type_def] >> strip_tac >>
  qpat_x_assum `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gnvs[]) >>
  rename1 `emit_op ADD [Var dv; Lit 32w] a6 = (dd,sa)` >>
  rename1 `emit_op ADD [Var sv; Lit 32w] a5 = (sd,a6)` >> disch_tac >>
  drule_all typed_copy_dyn_prefix_mono >> strip_tac >>
  `ci_mono sa b` by
    (qmatch_asmsub_abbrev_tac `suffix sa = ((),b)` >>
     `ci_mono sa (SND (suffix sa))` suffices_by gvs[] >>
     unabbrev_all_tac >> IF_CASES_TAC >>
     rpt (FIRST [irule ci_mono_bind, irule ci_mono_ignore_bind] >>
          rpt conj_tac >> rpt gen_tac >> BETA_TAC) >>
     simp[ci_mono_emit_op, ci_mono_emit_inst, ci_mono_new_block,
          ci_mono_fresh_label, ci_mono_fresh_var, ci_mono_comp_return,
          cj 1 ci_mono_typed_memory_family,
          compile_copy_memory_dynamic_def, ci_mono_emit_void]) >>
  `fn_has_code a sa fn` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  `?flag valid sdv ddv.
     too_long = Var flag /\ ok = Var valid /\ sd = Var sdv /\ dd = Var ddv` by
    metis_tac[emitted_insts_emit_op_local] >> gnvs[] >>
  `ptr_covers G tn sv s (32 + scap * type_memory_size tv) /\
   ptr_covers G tn dv s (32 + cap * type_memory_size tv') /\
   lookup_var sv s = SOME sw /\ lookup_var dv s = SOME dw /\
   w2n sw + 32 < dimword (:256) /\ w2n dw + 32 < dimword (:256) /\
   LENGTH l <= cap` by
    (fs[type_memory_size_def, eval_operand_def, typed_copy_dynarray_wf] >>
     decide_tac) >>
  Q.SUBGOAL_THEN
    `w2n sw + type_memory_size (ArrayTV tv (Dynamic scap)) <= w2n dw \/
      w2n dw + 32 <= w2n sw` assume_tac >-
    (fs[type_memory_size_def] >> decide_tac) >>
  qpat_assum `emit_op MLOAD _ a = _`
    (mp_then Any mp_tac widened_assign_dynarray_header_prefix_counted) >>
  ntac 16 (disch_then drule) >>
  disch_then (qspecl_then [`fn`,`ctx`,`PG`,`D`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `w2n (sw+32w) = w2n sw + 32 /\
   w2n (dw+32w) = w2n dw + 32` by
    (qpat_x_assum `w2n sw + 32 < _` mp_tac >>
     qpat_x_assum `w2n dw + 32 < _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w,
          wordsTheory.dimword_def]) >>
  `?K tk u.
    gas_path_ptr D 0 ctx fn PG H tm t 0 K tk (OK u) /\
    u.vs_current_bb = b.cs_current_bb /\
    u.vs_inst_idx = LENGTH b.cs_current_insts /\ ~u.vs_halted /\
    (!m. mem_agree_outside tk.t_mem u.vs_memory m ==>
      elems_in_memory l (w2n dw+32) tv' m) /\
    typed_copy_state_frame sa (w2n dw+32)
      (LENGTH l * type_memory_size tv') t u /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x t /\
      FLOOKUP K x = FLOOKUP H x /\ op_taint tk (Var x) = op_taint tm (Var x)) /\
    tk.t_stor = tm.t_stor /\ tk.t_trans = tm.t_trans /\ tk.t_imm = tm.t_imm /\
    (!i. ~(w2n dw+32 <= i /\
       i < w2n dw+32+LENGTH l*type_memory_size tv') ==>
       (i IN tk.t_mem <=> i IN tm.t_mem))` by
    (qpat_x_assum `(if _ then _ else _) sa = _` mp_tac >>
     IF_CASES_TAC
     >- suspend "bulk_data"
     >> suspend "recursive_data") >>
  suspend "landing"
QED

Resume widened_assign_typed_dynarray_counted[bulk_data]:
  qpat_x_assum `_ /\ de = se` strip_assume_tac >>
  `tv' = tv` by metis_tac[optionTheory.SOME_11] >> gnvs[] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gnvs[]) >> disch_tac >>
  rename1 `emit_op MUL _ sa = (count_op,sm)` >>
  `ci_mono sa sm /\ ci_mono sm b` by
    metis_tac[ci_mono_emit_op, ci_mono_compile_copy_memory_dynamic, pairTheory.SND] >>
  `fn_has_code sa sm fn /\ fn_has_code sm b fn` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  `op_taint tm (Var ddv) = {} /\ op_taint tm (Var sdv) = {}` by
    (qpat_assum `ptr_covers H tm ddv t _` mp_tac >>
     qpat_assum `ptr_covers H tm sdv t _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[ptr_covers_def, op_taint_def] >> metis_tac[]) >>
  `EVERY (val_wf tv) l` by
    (qpat_assum `val_wf (ArrayTV tv (Dynamic scap)) _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[val_wf_def, typed_copy_elems_wf_indexed, EVERY_EL]) >>
  `LENGTH l * type_memory_size tv < dimword (:256)` by
    (`LENGTH l * type_memory_size tv <= cap * type_memory_size tv` by
       simp[LESS_MONO_MULT] >>
     qpat_assum `type_memory_size (ArrayTV tv (Dynamic cap)) + _ < _` mp_tac >>
     pop_assum mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     pure_rewrite_tac[type_memory_size_def] >> decide_tac) >>
  `ptr_covers H tm ddv t (LENGTH l * type_memory_size tv)` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >>
     qexists_tac `cap * type_memory_size tv` >> simp[LESS_MONO_MULT]) >>
  qpat_assum `emit_op MUL _ sa = _`
    (mp_then Any mp_tac widened_assign_bulk_elements_counted) >>
  ntac 15 (disch_then drule) >>
  disch_then (qspecl_then [`PG`,`H`,`D`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexistsl_tac [`G'`,`tn'`,`t'`] >> gnvs[] >>
  rpt strip_tac >>
  qpat_x_assum `!i. i < _ \/ _ <= i ==> _` irule >> decide_tac
QED

Resume widened_assign_typed_dynarray_counted[recursive_data]:
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >> disch_tac >>
  namedCases_on `fresh_label "typed_dyn_cond" sa` ["hdr l1"] >> gnvs[] >>
  namedCases_on `fresh_label "typed_dyn_body" l1` ["blabel l2"] >> gnvs[] >>
  namedCases_on `fresh_label "typed_dyn_exit" l2` ["exit l3"] >> gnvs[] >>
  namedCases_on `fresh_var l3` ["counter init"] >> gnvs[] >>
  namedCases_on `emit_inst ASSIGN [Lit 0w] [counter] init` ["uu st0"] >> Cases_on `uu` >> gnvs[] >>
  namedCases_on `emit_inst JMP [Label hdr] [] st0` ["uu st1"] >> Cases_on `uu` >> gnvs[] >>
  namedCases_on `new_block hdr st1` ["u1 sth"] >> gnvs[] >>
  namedCases_on `emit_op LT [Var counter; length] sth` ["lt h1"] >> gnvs[] >>
  namedCases_on `emit_op ISZERO [lt] h1` ["done stj"] >> gnvs[] >>
  namedCases_on `emit_inst JNZ [done; Label exit; Label blabel] [] stj` ["uu st2"] >> Cases_on `uu` >> gnvs[] >>
  namedCases_on `new_block blabel st2` ["u2 stb"] >> gnvs[] >>
  namedCases_on `emit_op MUL [Var counter; Lit (n2w (type_memory_size tv))] stb` ["so b1"] >> gnvs[] >>
  namedCases_on `emit_op MUL [Var counter; Lit (n2w (type_memory_size tv'))] b1` ["doff b2"] >> gnvs[] >>
  namedCases_on `emit_op ADD [Var sdv; so] b2` ["sp b3"] >> gnvs[] >>
  namedCases_on `emit_op ADD [Var ddv; doff] b3` ["dp b4"] >> gnvs[] >>
  namedCases_on `compile_store_memory_typed cenv dp de sp se b4` ["uu b5"] >> Cases_on `uu` >> gnvs[] >>
  namedCases_on `emit_op ADD [Var counter; Lit 1w] b5` ["inc b6"] >> gnvs[] >>
  namedCases_on `emit_inst ASSIGN [inc] [counter] b6` ["uu ste"] >> Cases_on `uu` >> gnvs[] >>
  namedCases_on `emit_inst JMP [Label hdr] [] ste` ["uu st3"] >> Cases_on `uu` >> gnvs[] >>
  namedCases_on `new_block exit st3` ["u3 stx"] >> gnvs[] >>
  drule_all typed_copy_dynarray_slow_layout >> strip_tac >>
  `?lv. lt = Var lv` by metis_tac[emitted_insts_emit_op_local] >>
  `?donev. done = Var donev` by metis_tac[emitted_insts_emit_op_local] >> gnvs[] >>
  `fn_has_code sa b fn` by metis_tac[fn_has_code_split, ci_mono_def] >>
  `ci_mono stb b1 /\ ci_mono b1 b2 /\ ci_mono b2 b3 /\
   ci_mono b3 b4 /\ ci_mono b4 b5 /\ ci_mono b5 b6 /\ ci_mono b6 ste` by
    (qpat_x_assum `!cd cs cdt cst cv. _` kall_tac >>
     rpt conj_tac >> metis_tac[ci_mono_emit_op, ci_mono_emit_inst,
       cj 1 ci_mono_typed_memory_family, pairTheory.SND]) >>
  `cs_extends sa b4 /\ cs_extends b5 b` by
    (conj_tac
     >- (map_every (fn q => qpat_assum q mp_tac)
          [`ci_mono sa stb`, `ci_mono stb b1`, `ci_mono b1 b2`,
           `ci_mono b2 b3`, `ci_mono b3 b4`] >>
         POP_ASSUM_LIST (K all_tac) >> simp[ci_mono_def] >>
         metis_tac[cs_extends_trans]) >>
     qpat_assum `ci_mono b5 b6` mp_tac >>
     qpat_assum `ci_mono b6 ste` mp_tac >>
     qpat_assum `emit_inst JMP _ _ ste = _`
       (mp_then Any mp_tac cs_extends_emit_inst) >>
     qpat_assum `new_block exit st3 = _`
       (mp_then Any mp_tac cs_extends_new_block) >>
     POP_ASSUM_LIST (K all_tac) >> simp[ci_mono_def] >>
     metis_tac[cs_extends_trans]) >>
  `fn_has_code b4 b5 fn` by
    (qpat_assum `fn_has_code sa b fn` mp_tac >>
     qpat_assum `cs_extends sa b4` mp_tac >>
     qpat_assum `cs_extends b5 b` mp_tac >>
     qpat_assum `ci_mono b4 b5` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[ci_mono_def] >>
     metis_tac[fn_has_code_mid]) >>
  `!i. i < LENGTH l ==> val_wf tv (EL i l) /\ val_wf tv' (EL i l)` by
    (qpat_assum `val_wf (ArrayTV tv (Dynamic scap)) _` mp_tac >>
     qpat_assum `val_wf (ArrayTV tv' (Dynamic cap)) _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[val_wf_def, typed_copy_elems_wf_indexed] >> metis_tac[]) >>
  qpat_assum `compile_store_memory_typed cenv dp de sp se b4 = _`
    (mp_then Any mp_tac widened_assign_index_loop_counted) >>
  disch_then (fn th => qpat_assum `emit_op MUL _ stb = _` (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `emit_op MUL _ b1 = _` (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `emit_op LT _ sth = _` (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `emit_op ISZERO _ h1 = _` (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `emit_inst JNZ _ _ stj = _` (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `new_block blabel st2 = _` (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `new_block hdr st1 = _` (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `emit_inst JMP _ _ st0 = _` (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `emit_inst ASSIGN _ _ init = _` (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `emit_op ADD [Var sdv; so] b2 = _` (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `emit_op ADD [Var counter; Lit 1w] b5 = _` (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `emit_inst ASSIGN _ _ b6 = _` (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `emit_inst JMP _ _ ste = _` (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `new_block exit st3 = _` (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `emit_op ADD [Var ddv; doff] b3 = _` (mp_then Any mp_tac th)) >>
  disch_then (drule_at (Pat `eval_operand length _ = _`)) >>
  disch_then (drule_at (Pat `op_prov _ length = _`)) >>
  disch_then (drule_at (Pat `fn_has_code sa b fn`)) >>
  disch_then (qspecl_then [`tm`, `sw+32w`, `\i. EL i l`, `dw+32w`, `ctx`, `PG`, `D`] mp_tac) >>
  impl_tac
  >- (simp[eval_operand_def] >> reverse (rpt conj_tac)
      >- suspend "recursive_child"
      >~ [`!x. lop = Var x \/ spv = x \/ dpv = x ==> not_fresh_at sa x`] >-
         (rpt strip_tac >> gvs[])
      >- (qpat_assum `type_memory_size (ArrayTV tv' (Dynamic cap)) + w2n dw <= w2n sw \/ _` mp_tac >>
          qpat_assum `LENGTH l <= scap` mp_tac >> qpat_assum `scap <= cap` mp_tac >>
          POP_ASSUM_LIST (K all_tac) >> simp[type_memory_size_def] >> rpt strip_tac >>
          `LENGTH l * type_memory_size tv' <= cap * type_memory_size tv'` by simp[] >>
          `LENGTH l * type_memory_size tv <= scap * type_memory_size tv` by simp[] >> decide_tac)
      >- (qpat_assum `type_memory_size (ArrayTV tv' (Dynamic cap)) + w2n dw < _` mp_tac >>
          qpat_assum `LENGTH l <= scap` mp_tac >> qpat_assum `scap <= cap` mp_tac >>
          POP_ASSUM_LIST (K all_tac) >> simp[type_memory_size_def] >> rpt strip_tac >>
          `LENGTH l * type_memory_size tv' <= cap * type_memory_size tv'` by simp[] >> decide_tac)
      >- (qpat_assum `type_memory_size (ArrayTV tv (Dynamic scap)) + w2n sw < _` mp_tac >>
          qpat_assum `LENGTH l <= scap` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
          simp[type_memory_size_def] >> rpt strip_tac >>
          `LENGTH l * type_memory_size tv <= scap * type_memory_size tv` by simp[] >> decide_tac)
      >- (qpat_assum `!m. _ ==> elems_in_memory l _ tv m` mp_tac >>
          POP_ASSUM_LIST (K all_tac) >> pure_rewrite_tac[typed_copy_elems_indexed] >> rpt strip_tac >>
          `w2n sw + (i * type_memory_size tv + 32) =
           (w2n sw + 32) + i * type_memory_size tv` by decide_tac >> metis_tac[])
      >- (qpat_assum `ptr_covers H tm ddv t _` mp_tac >>
          qpat_assum `LENGTH l <= scap` mp_tac >> qpat_assum `scap <= cap` mp_tac >>
          POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
          `LENGTH l * type_memory_size tv' <= cap * type_memory_size tv'` by simp[] >>
          fs[ptr_covers_def] >>
          `LENGTH l * type_memory_size tv' <= cap * type_memory_size tv'` by simp[] >> decide_tac)
      >- (qpat_assum `ptr_covers H tm ddv t _` mp_tac >>
          POP_ASSUM_LIST (K all_tac) >> simp[ptr_covers_def, op_taint_def] >> metis_tac[])
      >> qpat_assum `ptr_covers H tm sdv t _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> simp[ptr_covers_def, op_taint_def] >> metis_tac[]) >>
  strip_tac >> suspend "recursive_result"
QED


Resume widened_assign_typed_dynarray_counted[recursive_child]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!cd cs cdt cst cv. _`
    (qspecl_then [`de`, `se`, `tv'`, `tv`, `EL j l`] mp_tac) >>
  simp[type_rank_def] >>
  (impl_tac >-
    (simp[] >>
     qpat_assum `all_have_type tv l` mp_tac >>
     qpat_assum `all_have_type tv' l` mp_tac >>
     qpat_assum `!i. i < LENGTH l ==> val_wf tv _ /\ _` mp_tac >>
     qpat_assum `j < LENGTH l` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[vyperTypingTheory.all_have_type_EVERY, listTheory.EVERY_EL] >> metis_tac[])) >>
  disch_then (fn th => qpat_assum
    `compile_store_memory_typed cenv dp de sp se b4 = _`
    (mp_then Any mp_tac th)) >>
  disch_then ho_match_mp_tac >> qexists_tac `bw` >> simp[] >>
  `!x. dp = Var x ==> not_fresh_at b4 x` by
    (qpat_assum `emit_op ADD [Var ddv; doff] b3 = _`
      (mp_then Any mp_tac typed_copy_emit_op_fresh) >> simp[]) >>
  `!x. sp = Var x ==> not_fresh_at b4 x` by
    metis_tac[typed_copy_emit_op_fresh, typed_copy_operand_fresh_mono] >>
  simp[]
QED

Resume widened_assign_typed_dynarray_counted[recursive_result]:
  qexistsl_tac [`H'`, `tm'`, `t'`] >>
  qpat_x_assum `!cd cs cdt cst cv. _` kall_tac >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> pure_rewrite_tac[typed_copy_elems_indexed] >>
      rpt strip_tac >>
      first_x_assum (qspecl_then [`i`, `m`] mp_tac) >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `!i. ~(_ /\ _) ==> _` (qspec_then `i` mp_tac) >>
  metis_tac[arithmeticTheory.ADD_ASSOC]
QED

Resume widened_assign_typed_dynarray_counted[landing]:
  qpat_x_assum `!cd cs cdt cst cv. _` kall_tac >>
  rename1 `gas_path_ptr D 0 ctx fn PG H tm t 0 KK tk (OK u)` >>
  qexistsl_tac [`KK`,`tk`,`u`] >>
  `LENGTH l * type_memory_size tv' <= cap * type_memory_size tv'` by
    simp[LESS_MONO_MULT] >>
  `!m. mem_agree_outside tk.t_mem u.vs_memory m ==>
    mem_word_at (w2n dw) m = n2w (LENGTH l)` by
    (rpt strip_tac >> irule widened_assign_robust_header_data_frame >>
     qexistsl_tac [`sa`,`LENGTH l * type_memory_size tv'`,`t`,`u`,`tk.t_mem`,`tm.t_mem`] >>
     simp[]) >>
  conj_tac
  >- metis_tac[fragGasPathPtrTheory.gas_path_ptr_then, ADD_CLAUSES] >>
  simp[type_memory_size_def] >>
  conj_tac
  >- (rpt strip_tac >> simp[Once val_in_memory_def]) >>
  conj_tac
  >- (irule typed_copy_state_frame_trans >> qexists_tac `t` >> conj_tac
      >- (irule typed_copy_state_frame_subinterval >>
          qexistsl_tac [`w2n dw`,`32`] >> simp[]) >>
      irule typed_copy_state_frame_subinterval >>
      qexistsl_tac [`w2n dw+32`,`LENGTH l * type_memory_size tv'`] >>
      conj_tac >- decide_tac >> conj_tac >- decide_tac >>
      irule typed_copy_state_frame_mono >> qexists_tac `sa` >> simp[]) >>
  rpt strip_tac >>
  `not_fresh_at sa x` by
    (irule exprOperandVarTheory.compiler_ci_mono_not_fresh >>
     qexists_tac `a` >> simp[]) >>
  metis_tac[]
QED

Finalise widened_assign_typed_dynarray_counted
