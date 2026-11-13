(* Actual-length recursive dynamic-array pointer copy. *)
Theory bodyPtrTypedCopyDynamicLoop
Ancestors bodyPtrTypedCopyDynamicEntry bodyPtrTypedCopyArrayIteration
  bodyPtrTypedCopyArrayFrame bodyPtrTypedCopyBoundary typedDynLoopStructure
  typedArrayLoopValues typedDynStoreProps vyperTypeValues vyperTypeSystem
  typedCopyStateFrame typedCopyLayoutPtr bodyPtrPopMemoryHeader
  dynCopyPrefixPath abiStaticLoopCode abiBytestringCode
  externalReturnCopyArrays normalizationPrefixPtr valueEncodingProps
  bodyPtrTypedCopyDynamicControl typedMemoryCopy externalEntryShape
  assignBasePtrStorageLayout typedArrayLoopCode venomExecSemantics
  bodyPtrTypedCopyArrayControl

Theorem typed_copy_dynamic_array_loop:
  !ce de se dc sc.
  (!dty sty. type_rank ce.ce_struct_fields dty <
      type_rank ce.ce_struct_fields (ArrayT de (Dynamic dc)) ==>
   !tenv dtv stv v dst src sa sb ctx fn D PG G tn s a b.
    acyclic_struct_metadata ce.ce_struct_fields /\
    sfields_tenv_consistent ce.ce_struct_fields tenv /\
    (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). sz = type_memory_bytes ce fty /\
        (!tv. evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv)) fields) /\
    type_widens_to tenv sty dty /\
    evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
    type_memory_bytes ce sty = type_memory_size stv /\
    type_memory_bytes ce dty = type_memory_size dtv /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    compile_store_memory_typed ce (Var dst) dty (Var src) sty sa = ((),sb) /\
    not_fresh_at sa dst /\ not_fresh_at sa src /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    ptr_covers G tn src s (type_memory_bytes ce sty) /\
    ptr_covers G tn dst s (type_memory_bytes ce dty) /\
    w2n a + type_memory_bytes ce sty < dimword(:256) /\
    w2n b + type_memory_bytes ce dty < dimword(:256) /\
    (type_memory_bytes ce sty <> 0 /\ type_memory_bytes ce dty <> 0 ==>
      w2n a + type_memory_bytes ce sty <= w2n b \/
      w2n b + type_memory_bytes ce dty <= w2n a) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory stv v (w2n a) m) /\
    fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\ ~ctx_has_dalloca ctx /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    cs_extends sa sb /\
    ?H tf sf.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK sf) /\
      sf.vs_current_bb = sb.cs_current_bb /\
      sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
      typed_copy_state_frame sa (w2n b) (type_memory_bytes ce dty) s sf /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      (!i. ~(w2n b <= i /\ i < w2n b + type_memory_bytes ce dty) ==>
        (i IN tf.t_mem <=> i IN tn.t_mem)) /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
        op_taint tf (Var p) = op_taint tn (Var p)) /\
      (!m. mem_agree_outside tf.t_mem sf.vs_memory m ==>
        val_in_memory dtv v (w2n b) m)) ==>
   !tenv dtv stv v dst src sa sb ctx fn D PG G tn s a b.
    ~(type_memory_bytes ce de = type_memory_bytes ce se /\ de = se) /\
    acyclic_struct_metadata ce.ce_struct_fields /\
    sfields_tenv_consistent ce.ce_struct_fields tenv /\
    (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). sz = type_memory_bytes ce fty /\
        (!tv. evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv)) fields) /\
    type_widens_to tenv (ArrayT se (Dynamic sc)) (ArrayT de (Dynamic dc)) /\
    evaluate_type tenv (ArrayT se (Dynamic sc)) = SOME stv /\
    evaluate_type tenv (ArrayT de (Dynamic dc)) = SOME dtv /\
    type_memory_bytes ce (ArrayT se (Dynamic sc)) = type_memory_size stv /\
    type_memory_bytes ce (ArrayT de (Dynamic dc)) = type_memory_size dtv /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    compile_store_memory_typed ce (Var dst) (ArrayT de (Dynamic dc))
      (Var src) (ArrayT se (Dynamic sc)) sa = ((),sb) /\
    not_fresh_at sa dst /\ not_fresh_at sa src /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    ptr_covers G tn src s (type_memory_bytes ce (ArrayT se (Dynamic sc))) /\
    ptr_covers G tn dst s (type_memory_bytes ce (ArrayT de (Dynamic dc))) /\
    w2n a + type_memory_bytes ce (ArrayT se (Dynamic sc)) < dimword(:256) /\
    w2n b + type_memory_bytes ce (ArrayT de (Dynamic dc)) < dimword(:256) /\
    (type_memory_bytes ce (ArrayT se (Dynamic sc)) <> 0 /\
     type_memory_bytes ce (ArrayT de (Dynamic dc)) <> 0 ==>
      w2n a + type_memory_bytes ce (ArrayT se (Dynamic sc)) <= w2n b \/
      w2n b + type_memory_bytes ce (ArrayT de (Dynamic dc)) <= w2n a) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory stv v (w2n a) m) /\
    fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\ ~ctx_has_dalloca ctx /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    cs_extends sa sb /\
    ?H tf sf.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK sf) /\
      sf.vs_current_bb = sb.cs_current_bb /\
      sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
      typed_copy_state_frame sa (w2n b) (type_memory_bytes ce (ArrayT de (Dynamic dc))) s sf /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      (!i. ~(w2n b <= i /\ i < w2n b + type_memory_bytes ce (ArrayT de (Dynamic dc))) ==>
        (i IN tf.t_mem <=> i IN tn.t_mem)) /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
        op_taint tf (Var p) = op_taint tn (Var p)) /\
      (!m. mem_agree_outside tf.t_mem sf.vs_memory m ==>
        val_in_memory dtv v (w2n b) m)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_assum `evaluate_type _ (ArrayT se _) = _`
    (mp_then Any strip_assume_tac evaluate_type_ArrayT_cases) >>
  qpat_assum `evaluate_type _ (ArrayT de _) = _`
    (mp_then Any strip_assume_tac evaluate_type_ArrayT_cases) >>
  gvs[] >>
  rename1 `value_has_type (ArrayTV dt (Dynamic dc)) v` >>
  rename1 `value_has_type (ArrayTV st (Dynamic sc)) v` >>
  `?vs. v = ArrayV (DynArrayV vs)` by
    (Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
     rename1 `ArrayV av` >> Cases_on `av` >>
     gvs[vyperTypingTheory.value_has_type_def]) >>
  gvs[] >>
  `dc < dimword(:256) /\ sc < dimword(:256)` by
    metis_tac[evaluate_type_dynarray_count_bound] >>
  `LENGTH vs <= dc /\ LENGTH vs <= sc` by
    gvs[vyperTypingTheory.value_has_type_def] >>
  `compile_copy_dynarray_typed ce (Var dst) de dc (Var src) se sa = ((),sb)` by
    metis_tac[compile_typed_dynarray_dispatch] >>
  `cs_extends sa sb` by metis_tac[typed_memory_family_labels, pairTheory.SND] >>
  simp[] >>
  drule_all (SIMP_RULE std_ss [] compile_copy_dynarray_loop_contains) >> strip_tac >>
  `!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem` by
    metis_tac[pop_robust_dynarray_header_clean] >>
  `mload (w2n a) s = n2w (LENGTH vs)` by
    (qpat_assum `!m. mem_agree_outside tn.t_mem _ _ ==> _`
      (qspec_then `s.vs_memory` mp_tac) >>
     simp_tac std_ss [bodyPtrDefsTheory.mem_agree_outside_def] >>
     disch_then (mp_then Any mp_tac placeDynLayoutTheory.place_dyn_memory_header) >>
     rewrite_tac[mem_word_at_eq_mload]) >>
  `ptr_covers G tn src s (32+sc*type_memory_size st) /\
   ptr_covers G tn dst s (32+dc*type_memory_size dt) /\
   w2n a+32+sc*type_memory_size st < dimword(:256) /\
   w2n b+32+dc*type_memory_size dt < dimword(:256)` by
    (gvs[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
  assume_tac typed_copy_dynamic_preamble_counted >>
  drule_all typed_copy_dynamic_entry_counted >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qpat_x_assum `!s ctx fn bb prefix suffix id src dst len too ok sp dp a b S T n cap G tn PG D. _` kall_tac >>
  qmatch_asmsub_abbrev_tac `fn_has_code prefix_cs (dynarray_copy_start ce (Var dst) de dc (Var src) se sa) fn` >>
  `lookup_block prefix_cs.cs_current_bb fn.fn_blocks = SOME
     <|bb_label := prefix_cs.cs_current_bb;
       bb_instructions := prefix_cs.cs_current_insts ++
         typed_array_loop_entry prefix_cs.cs_next_id prefix_cs.cs_next_var
           (fresh_label_output "typed_dyn_cond" sa.cs_next_label)|>` by
    (qpat_assum `fn_has_code prefix_cs (dynarray_copy_start _ _ _ _ _ _ _) fn`
       (mp_tac o REWRITE_RULE [fragExecTheory.fn_has_code_def]) >>
     simp[typedDynLoopCodeTheory.dynarray_copy_start_def,
       typedArrayLoopCodeTheory.typed_array_loop_start_def,
       Abbr `prefix_cs`, fragExecTheory.emitted_blocks_def] >>
     strip_tac >> qmatch_goalsub_abbrev_tac `SOME entry` >>
     qpat_x_assum `!bb. _ ==> lookup_block bb.bb_label fn.fn_blocks = SOME bb`
       (qspec_then `entry` mp_tac) >> simp[Abbr `entry`]) >>
  `gas_path_ptr D 0 ctx fn PG H tf u 0
    (DRESTRICT H (COMPL {compiler_var_name prefix_cs.cs_next_var 0}))
    (tf with t_var := tf.t_var |+ (compiler_var_name prefix_cs.cs_next_var 0,{}))
    (OK (jump_to (fresh_label_output "typed_dyn_cond" sa.cs_next_label)
       ((update_var (compiler_var_name prefix_cs.cs_next_var 0) 0w u)
          with vs_inst_idx := SUC u.vs_inst_idx)))` by
    (irule assign_base_storage_init_counted >> simp[] >>
     qexists_tac `prefix_cs.cs_next_id` >>
     simp[typed_array_loop_entry_def, venomInstTheory.get_instruction_def,
       listTheory.EL_APPEND_EQN, Abbr `prefix_cs`]) >>
  qabbrev_tac `loop_inv = \i K tk x.
    i <= LENGTH vs /\
    x.vs_current_bb = fresh_label_output "typed_dyn_cond" sa.cs_next_label /\
    x.vs_inst_idx = 0 /\ ~x.vs_halted /\
    lookup_var (compiler_var_name sa.cs_next_var 5) x = SOME (n2w i) /\
    FLOOKUP K (compiler_var_name sa.cs_next_var 5) = NONE /\
    op_taint tk (Var (compiler_var_name sa.cs_next_var 5)) = {} /\
    lookup_var (compiler_var_name sa.cs_next_var 0) x = SOME (n2w (LENGTH vs)) /\
    FLOOKUP K (compiler_var_name sa.cs_next_var 0) = NONE /\
    op_taint tk (Var (compiler_var_name sa.cs_next_var 0)) = {} /\
    lookup_var (compiler_var_name sa.cs_next_var 3) x = SOME (a+32w) /\
    lookup_var (compiler_var_name sa.cs_next_var 4) x = SOME (b+32w) /\
    ptr_covers K tk (compiler_var_name sa.cs_next_var 3) x
      (sc * type_memory_size st) /\
    ptr_covers K tk (compiler_var_name sa.cs_next_var 4) x
      (dc * type_memory_size dt) /\
    typed_copy_state_frame sa (w2n b)
      (type_memory_size (ArrayTV dt (Dynamic dc))) s x /\
    tk.t_stor = tn.t_stor /\ tk.t_trans = tn.t_trans /\ tk.t_imm = tn.t_imm /\
    (!z. ~(w2n b <= z /\ z < w2n b + type_memory_size (ArrayTV dt (Dynamic dc))) ==>
      (z IN tk.t_mem <=> z IN tn.t_mem)) /\
    (!p. not_fresh_at sa p ==>
      lookup_var p x = lookup_var p s /\ FLOOKUP K p = FLOOKUP G p /\
      op_taint tk (Var p) = op_taint tn (Var p)) /\
    (!m. mem_agree_outside tk.t_mem x.vs_memory m ==>
      mem_word_at (w2n b) m = n2w (LENGTH vs)) /\
    (!j. j < i ==> !m. mem_agree_outside tk.t_mem x.vs_memory m ==>
      val_in_memory dt (EL j vs) (w2n b + 32 + j * type_memory_size dt) m) /\
    (!j. j < LENGTH vs ==> !m. mem_agree_outside tk.t_mem x.vs_memory m ==>
      val_in_memory st (EL j vs) (w2n a + 32 + j * type_memory_size st) m)` >>
  `!K tk x. loop_inv (LENGTH vs) K tk x ==>
    !m. mem_agree_outside tk.t_mem x.vs_memory m ==>
      val_in_memory (ArrayTV dt (Dynamic dc)) (ArrayV (DynArrayV vs)) (w2n b) m` by
    (rpt gen_tac >> rewrite_tac[robust_dynarray_indexed] >>
     simp[Abbr `loop_inv`] >> strip_tac >> simp[]) >>
  `lookup_block (fresh_label_output "typed_dyn_cond" sa.cs_next_label) fn.fn_blocks =
    SOME <|bb_label := fresh_label_output "typed_dyn_cond" sa.cs_next_label;
      bb_instructions := typed_array_loop_header prefix_cs.cs_next_id prefix_cs.cs_next_var
        (fresh_label_output "typed_dyn_body" (sa.cs_next_label+1))
        (fresh_label_output "typed_dyn_exit" (sa.cs_next_label+2))
        (Var (compiler_var_name sa.cs_next_var 0))|>` by
    (qpat_assum `fn_has_code prefix_cs (dynarray_copy_start _ _ _ _ _ _ _) fn`
       (mp_tac o REWRITE_RULE [fragExecTheory.fn_has_code_def]) >>
     simp[typedDynLoopCodeTheory.dynarray_copy_start_def,
       typedArrayLoopCodeTheory.typed_array_loop_start_def,
       Abbr `prefix_cs`, fragExecTheory.emitted_blocks_def] >>
     strip_tac >> qmatch_goalsub_abbrev_tac `SOME header` >>
     qpat_x_assum `!bb. _ ==> lookup_block bb.bb_label fn.fn_blocks = SOME bb`
       (qspec_then `header` mp_tac) >> simp[Abbr `header`]) >>
  qabbrev_tac `loop_post = \K tk x.
    x.vs_current_bb = sb.cs_current_bb /\
    x.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~x.vs_halted /\
    typed_copy_state_frame sa (w2n b) (type_memory_size (ArrayTV dt (Dynamic dc))) s x /\
    tk.t_stor = tn.t_stor /\ tk.t_trans = tn.t_trans /\ tk.t_imm = tn.t_imm /\
    (!z. ~(w2n b <= z /\ z < w2n b + type_memory_size (ArrayTV dt (Dynamic dc))) ==>
      (z IN tk.t_mem <=> z IN tn.t_mem)) /\
    (!p. not_fresh_at sa p ==>
      lookup_var p x = lookup_var p s /\ FLOOKUP K p = FLOOKUP G p /\
      op_taint tk (Var p) = op_taint tn (Var p)) /\
    (!m. mem_agree_outside tk.t_mem x.vs_memory m ==>
      val_in_memory (ArrayTV dt (Dynamic dc)) (ArrayV (DynArrayV vs)) (w2n b) m)` >>
  `!K tk x. loop_inv (LENGTH vs) K tk x ==>
    ?L tl y. gas_path_ptr D 0 ctx fn PG K tk x 0 L tl (OK y) /\ loop_post L tl y` by
    (map_every qx_gen_tac [`kg`, `tk`, `x`] >> strip_tac >>
     `!m. mem_agree_outside tk.t_mem x.vs_memory m ==>
       val_in_memory (ArrayTV dt (Dynamic dc)) (ArrayV (DynArrayV vs)) (w2n b) m` by
       (qpat_assum `!K tk x. loop_inv _ _ _ _ ==> _` drule >> simp[]) >>
     qpat_x_assum `loop_inv _ _ _ _` mp_tac >>
     simp_tac (srw_ss()) [Abbr `loop_inv`] >> strip_tac >>
     `gas_path_ptr D 0 ctx fn PG kg tk x 0
       (DRESTRICT (DRESTRICT kg (COMPL {compiler_var_name sa.cs_next_var 6}))
         (COMPL {compiler_var_name sa.cs_next_var 7}))
       (tk with t_var := (tk.t_var |+ (compiler_var_name sa.cs_next_var 6,{}))
         |+ (compiler_var_name sa.cs_next_var 7,{}))
       (OK (jump_to (fresh_label_output "typed_dyn_exit" (sa.cs_next_label+2))
         (update_var (compiler_var_name sa.cs_next_var 7) 1w
           (update_var (compiler_var_name sa.cs_next_var 6) 0w x))))` by
       (irule (typed_copy_operand_test_counted |> Q.INST
          [`i` |-> `LENGTH (vs:value list)`, `n` |-> `LENGTH (vs:value list)`] |>
          SIMP_RULE std_ss [bool_to_word_def]) >>
        simp[Abbr `prefix_cs`, typed_array_loop_header_def] >>
        qexistsl_tac [`Var (compiler_var_name sa.cs_next_var 0)`,
          `fresh_label_output "typed_dyn_body" (sa.cs_next_label+1)`,
          `compiler_var_name sa.cs_next_var 5`, `sa.cs_next_id+9`, `vs`] >>
        gvs[venomStateTheory.eval_operand_def, compiler_var_name_def] >> decide_tac) >>
     goal_assum (drule_at Any) >>
     simp[Abbr `loop_post`, venomStateTheory.jump_to_def,
       venomStateTheory.update_var_def, typedDynLoopCodeTheory.dynarray_copy_finish_def] >>
     simp[typedArrayLoopCodeTheory.typed_array_loop_finish_def] >>
     `!p. not_fresh_at sa p ==>
       p <> compiler_var_name sa.cs_next_var 6 /\
       p <> compiler_var_name sa.cs_next_var 7` by
       (rpt strip_tac >>
        gvs[loweringStateRelDefsTheory.not_fresh_at_def, compiler_var_name_def]) >>
     qpat_x_assum `typed_copy_state_frame sa _ _ s x` mp_tac >>
     simp[typed_copy_state_frame_def, venomStateTheory.lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FLOOKUP_DRESTRICT,
       ptrDisciplineTheory.op_taint_def] >>
     gvs[venomStateTheory.lookup_var_def, ptrDisciplineTheory.op_taint_def] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  qabbrev_tac `child_cs = dynarray_copy_start ce (Var dst) de dc (Var src) se sa` >>
  qabbrev_tac `addr_cs = child_cs with cs_current_insts := []` >>
  `fn_has_code addr_cs child_cs fn` by
    (qpat_assum `fn_has_code prefix_cs child_cs fn`
       (strip_assume_tac o REWRITE_RULE [fragExecTheory.fn_has_code_def]) >>
     simp[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def,
       Abbr `addr_cs`]) >>
  `!i kg tk x. i < LENGTH vs /\ loop_inv i kg tk x ==>
    ?L tl y. gas_path_ptr D 0 ctx fn PG kg tk x 0 L tl (OK y) /\
      loop_inv (SUC i) L tl y` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `loop_inv _ _ _ _` mp_tac >>
     simp_tac (srw_ss()) [Abbr `loop_inv`] >> strip_tac >>
     `gas_path_ptr D 0 ctx fn PG kg tk x 0
       (DRESTRICT (DRESTRICT kg (COMPL {compiler_var_name sa.cs_next_var 6}))
         (COMPL {compiler_var_name sa.cs_next_var 7}))
       (tk with t_var := (tk.t_var |+ (compiler_var_name sa.cs_next_var 6,{}))
         |+ (compiler_var_name sa.cs_next_var 7,{}))
       (OK (jump_to (fresh_label_output "typed_dyn_body" (sa.cs_next_label+1))
         (update_var (compiler_var_name sa.cs_next_var 7) 0w
           (update_var (compiler_var_name sa.cs_next_var 6) 1w x))))` by
       (qpat_assum `i < LENGTH vs` (fn th =>
          irule (typed_copy_operand_test_counted |>
            Q.INST [`i` |-> `i:num`, `n` |-> `LENGTH (vs:value list)`] |>
            SIMP_RULE std_ss [bool_to_word_def, th])) >>
        simp[Abbr `prefix_cs`, typed_array_loop_header_def] >>
        qexistsl_tac [`Var (compiler_var_name sa.cs_next_var 0)`,
          `compiler_var_name sa.cs_next_var 5`,
          `fresh_label_output "typed_dyn_exit" (sa.cs_next_label+2)`, `sa.cs_next_id+9`] >>
        gvs[venomStateTheory.eval_operand_def, compiler_var_name_def] >> decide_tac) >>
     `type_memory_bytes ce se = type_memory_size st /\
      type_memory_bytes ce de = type_memory_size dt` by
       (qpat_assum `type_memory_bytes ce (ArrayT se _) = _` mp_tac >>
        qpat_assum `type_memory_bytes ce (ArrayT de _) = _` mp_tac >>
        simp_tac std_ss [compileEnvTheory.type_memory_bytes_def,
          valueEncodingTheory.type_memory_size_def, arithmeticTheory.EQ_MULT_LCANCEL] >>
        rpt strip_tac >> decide_tac) >>
     `i * type_memory_size st + type_memory_size st <= sc * type_memory_size st /\
      i * type_memory_size dt + type_memory_size dt <= dc * type_memory_size dt` by
       (conj_tac >> rewrite_tac[GSYM (cj 5 arithmeticTheory.MULT_CLAUSES)] >>
        irule arithmeticTheory.LESS_MONO_MULT >> decide_tac) >>
     `w2n (a+32w) = w2n a+32 /\ w2n (b+32w) = w2n b+32` by
       (conj_tac >> simp[wordsTheory.w2n_add_2]) >>
     qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG kg tk x 0 kt tt (OK xt)` >>
     `?ka ta xa.
       gas_path_ptr D 0 ctx fn PG kt tt xt 0 ka ta (OK xa) /\
       lookup_var (compiler_var_name sa.cs_next_var 10) xa =
         SOME (n2w (w2n (a+32w) + i * type_memory_size st)) /\
       lookup_var (compiler_var_name sa.cs_next_var 11) xa =
         SOME (n2w (w2n (b+32w) + i * type_memory_size dt)) /\
       ptr_covers ka ta (compiler_var_name sa.cs_next_var 10) xa (type_memory_size st) /\
       ptr_covers ka ta (compiler_var_name sa.cs_next_var 11) xa (type_memory_size dt) /\
       xa.vs_memory = xt.vs_memory /\ ta.t_mem = tt.t_mem /\
       ta.t_stor = tt.t_stor /\ ta.t_trans = tt.t_trans /\
       (!p. ~MEM p (MAP (compiler_var_name sa.cs_next_var) [8;9;10;11]) ==>
         lookup_var p xa = lookup_var p xt /\ FLOOKUP ka p = FLOOKUP kt p /\
         op_taint ta (Var p) = op_taint tt (Var p)) /\
       xa.vs_current_bb = child_cs.cs_current_bb /\
       xa.vs_inst_idx = LENGTH child_cs.cs_current_insts /\ ~xa.vs_halted /\
       (xa with <|vs_vars := xt.vs_vars; vs_inst_idx := xt.vs_inst_idx|>) = xt /\
       ta.t_imm = tt.t_imm` by
       (simp_tac std_ss [listTheory.MAP] >>
        irule typed_copy_loop_address_counted_frame_endpoint >>
        simp[Abbr `xt`, venomStateTheory.jump_to_def,
          venomStateTheory.update_var_def, compiler_var_name_def] >>
        qexistsl_tac [`sc * type_memory_size st`, `dc * type_memory_size dt`,
          `compiler_var_name sa.cs_next_var 5`, `compiler_var_name sa.cs_next_var 4`,
          `sa.cs_next_id+12`, `addr_cs`, `compiler_var_name sa.cs_next_var 3`] >>
        simp[Abbr `addr_cs`, Abbr `child_cs`,
          typedDynLoopCodeTheory.dynarray_copy_start_def,
          typedArrayLoopCodeTheory.typed_array_loop_start_def,
          typed_array_loop_addresses_def, Abbr `prefix_cs`,
          typedDynLoopCodeTheory.dyn_copy_prefix_state_def,
          compiler_var_name_def, compiler_var_names_def,
          venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
          Abbr `kt`, Abbr `tt`, ptrDisciplineTheory.op_taint_def,
          bodyPtrDefsTheory.ptr_covers_def,
          finite_mapTheory.FLOOKUP_DRESTRICT] >>
        conj_tac >- (POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[] >> decide_tac) >>
        qpat_assum `op_taint tk (Var (compiler_var_name _ 5)) = {}` mp_tac >>
        qpat_assum `lookup_var (compiler_var_name _ 5) x = _` mp_tac >>
        qpat_assum `lookup_var (compiler_var_name _ 4) x = _` mp_tac >>
        qpat_assum `lookup_var (compiler_var_name _ 3) x = _` mp_tac >>
        qpat_assum `ptr_covers kg tk (compiler_var_name _ 4) x _` mp_tac >>
        qpat_assum `ptr_covers kg tk (compiler_var_name _ 3) x _` mp_tac >>
        simp_tac std_ss [compiler_var_name_def, venomStateTheory.lookup_var_def,
          ptrDisciplineTheory.op_taint_def, bodyPtrDefsTheory.ptr_covers_def] >>
        simp[]) >>
     `type_widens_to tenv se de` by
       (qpat_assum `type_widens_to _ (ArrayT _ _) _` mp_tac >>
        simp_tac std_ss [type_widens_to_def, arg_type_fits_def,
          well_formed_type_def, vyperValueTheory.evaluate_type_def] >>
        qpat_assum `evaluate_type tenv de = SOME dt` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[AllCaseEqs()]) >>
     `value_has_type st (EL i vs) /\ value_has_type dt (EL i vs)` by
       (qpat_assum `value_has_type (ArrayTV st _) _` mp_tac >>
        qpat_assum `value_has_type (ArrayTV dt _) _` mp_tac >>
        simp_tac std_ss [vyperTypingTheory.value_has_type_def,
          vyperTypingTheory.all_have_type_EVERY, listTheory.EVERY_EL] >>
        metis_tac[]) >>
     `val_wf st (EL i vs) /\ val_wf dt (EL i vs)` by
       metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
     qpat_assum `!dty sty. _` (qspecl_then [`de`, `se`] mp_tac) >>
     simp_tac arith_ss [typedCopyDomainTheory.type_rank_def] >>
     disch_then (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
     disch_then (qspec_then `tenv` mp_tac) >>
     disch_then (drule_at (Pat `evaluate_type _ se = _`)) >>
     disch_then (drule_at (Pat `evaluate_type _ de = _`)) >>
     disch_then (drule_at (Pat `lookup_var (compiler_var_name _ 10) _ = _`)) >>
     disch_then (qspec_then `EL i vs` mp_tac) >>
     disch_then (drule_at (Pat `lookup_var (compiler_var_name _ 11) _ = _`)) >>
     asm_simp_tac std_ss [] >>
     disch_then (drule_at (Pat `ptr_covers _ _ (compiler_var_name _ 10) _ _`)) >>
     disch_then (drule_at (Pat `fn_has_code child_cs after _`)) >>
     simp_tac (srw_ss()) [] >>
     disch_then (qspecl_then [`ctx`, `D`, `PG`] mp_tac) >>
     impl_tac >-
       (asm_simp_tac std_ss [] >>
        `w2n a + 32 + i * type_memory_size st < dimword(:256) /\
         w2n b + 32 + i * type_memory_size dt < dimword(:256)` by decide_tac >>
        asm_simp_tac std_ss [arithmeticTheory.LESS_MOD] >>
        rpt conj_tac
        >- (first_assum ACCEPT_TAC)
        >- (simp[Abbr `child_cs`, typedDynLoopCodeTheory.dynarray_copy_start_def,
              typedArrayLoopCodeTheory.typed_array_loop_start_def,
              Abbr `prefix_cs`, typedDynLoopCodeTheory.dyn_copy_prefix_state_def,
              loweringStateRelDefsTheory.not_fresh_at_def, compiler_var_name_def])
        >- (simp[Abbr `child_cs`, typedDynLoopCodeTheory.dynarray_copy_start_def,
              typedArrayLoopCodeTheory.typed_array_loop_start_def,
              Abbr `prefix_cs`, typedDynLoopCodeTheory.dyn_copy_prefix_state_def,
              loweringStateRelDefsTheory.not_fresh_at_def, compiler_var_name_def])
        >- decide_tac
        >- decide_tac
        >- (qpat_x_assum `type_memory_size (ArrayTV st _) <> 0 /\ _ ==> _` mp_tac >>
            simp_tac std_ss [valueEncodingTheory.type_memory_size_def] >> decide_tac)
        >> qpat_assum `!j. j < LENGTH vs ==> _` (qspec_then `i` mp_tac) >>
           simp[Abbr `xt`, Abbr `tt`, venomStateTheory.jump_to_def,
             venomStateTheory.update_var_def, arithmeticTheory.ADD_ASSOC]) >>
     strip_tac >>
     `w2n a + 32 + i * type_memory_size st < dimword(:256) /\
      w2n b + 32 + i * type_memory_size dt < dimword(:256)` by decide_tac >>
     `!z. ~(w2n b + 32 + i * type_memory_size dt <= z /\
             z < w2n b + 32 + i * type_memory_size dt + type_memory_size dt) ==>
       mem_bytes_at z 1 sf.vs_memory = mem_bytes_at z 1 xa.vs_memory /\
       (z IN tf'.t_mem <=> z IN ta.t_mem)` by
       (qpat_assum `typed_copy_state_frame child_cs _ _ xa sf`
          (strip_assume_tac o REWRITE_RULE [typed_copy_state_frame_def, typed_copy_frame_def]) >>
        gen_tac >> disch_tac >> conj_tac
        >- (first_x_assum irule >> asm_simp_tac std_ss [arithmeticTheory.LESS_MOD] >> decide_tac)
        >> qpat_assum `!z. _ ==> (z IN tf'.t_mem <=> _)` irule >>
           asm_simp_tac std_ss [arithmeticTheory.LESS_MOD] >> decide_tac) >>
     `!j. j < LENGTH vs ==> val_wf dt (EL j vs) /\ val_wf st (EL j vs)` by
       (qpat_assum `value_has_type (ArrayTV st _) _` mp_tac >>
        qpat_assum `value_has_type (ArrayTV dt _) _` mp_tac >>
        simp_tac std_ss [vyperTypingTheory.value_has_type_def,
          vyperTypingTheory.all_have_type_EVERY, listTheory.EVERY_EL] >>
        metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf]) >>
     `!j. j < SUC i ==> !m. mem_agree_outside tf'.t_mem sf.vs_memory m ==>
       val_in_memory dt (EL j vs) (w2n b + 32 + j * type_memory_size dt) m` by
       (irule robust_indexed_prefix_advance >>
        qexistsl_tac [`ta.t_mem`, `xa.vs_memory`] >>
        asm_simp_tac std_ss [arithmeticTheory.LESS_MOD] >>
        conj_tac >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
        qpat_assum `!j. j < i ==> _` mp_tac >>
        simp[Abbr `xt`, Abbr `tt`, venomStateTheory.jump_to_def,
          venomStateTheory.update_var_def, arithmeticTheory.ADD_ASSOC]) >>
     FAIL_TAC "child destination prefix preserved") >>
  FAIL_TAC "loop iteration"
QED
