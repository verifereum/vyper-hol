Theory entryCreateBlueprintSelectedSuffix
Ancestors
  createSizeIndexedRun createSizeItinerary createSizeBlueprintExtent createSizePrefixReplay
  revertReasonCopyPtr instIdxIndep vyperCreate
  createOperandSizeReject entryCreateCheckedSum createSizeBlueprintKeywordReplay
  createCtorSegmentArrival dallocaCreateGeometry freshWrites ghostPcTransportPtr
  loweringShapeRules loweringStateRelDefs fragExec emitHelperProps exprLoweringProps builtinCreate
  venomInst venomState venomExecSemantics compileEnv context words list arithmetic
  rich_list

(* The observed edge sequence has no executor assumptions beyond its own band
   and endpoint facts. Bridge the indexed state to the straight-line runner. *)
Triviality selected_band_run:
  i <= k /\ k <= n /\
  (!r. r <= n ==> (Obs r).vs_current_bb = (C r).cs_current_bb /\
    (Obs r).vs_inst_idx = LENGTH (C r).cs_current_insts /\
    ?x. ctor_segment_fetch fn (Obs r) = SOME x /\ (C r).cs_next_id <= x.inst_id) /\
  (!r z. r <= z /\ z <= n ==> ci_mono (C r) (C z) /\ fn_has_code (C r) (C z) fn) /\
  (!r. r < n ==> create_expr_prefix (C r) (C (SUC r)) explicit ctx fn
                    (Obs r) (M r) (Obs (SUC r))) /\
  (C k).cs_current_bb = (C i).cs_current_bb /\
  (C k).cs_current_insts = (C i).cs_current_insts ++ emitted_insts (C i) (C k) /\
  EVERY (\inst. inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode)
    (emitted_insts (C i) (C k)) ==>
  run_inst_seq (emitted_insts (C i) (C k)) (Obs i) =
    OK ((Obs k) with vs_inst_idx := (Obs i).vs_inst_idx)
Proof
  strip_tac >>
  `i <= n` by decide_tac >>
  qpat_assum `!r. r <= n ==> _` (fn th =>
    map_every (fn idx => qspec_then idx mp_tac th >>
      (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac) [`i`,`k`]) >>
  `fn_has_code (C i) (C k) fn` by metis_tac[] >>
  qpat_x_assum `ctor_segment_fetch fn (Obs k) = SOME _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [ctor_segment_fetch_def,AllCaseEqs()]) >>
  irule create_indexed_straight_run >>
  rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE REFL_TAC)) >>
  rename1 `get_instruction bb (Obs k).vs_inst_idx = SOME last` >>
  qexistsl_tac [`C`,`ctx`,`bb`,`explicit`,`fn`,`last`,`M`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >- simp[] >>
  qx_gen_tac `r` >> strip_tac >>
  `r < n` by decide_tac >>
  qpat_assum `!x y. _ ==> ci_mono _ _ /\ _` (fn th =>
    map_every (fn is => qspecl_then is mp_tac th >> (impl_tac >- decide_tac) >>
      disch_then (strip_assume_tac o REWRITE_RULE[ci_mono_def]))
      [[`i`,`r`],[`SUC r`,`k`]]) >>
  qpat_assum `!z. z < n ==> create_expr_prefix _ _ _ _ _ _ _ _`
    (qspec_then `r` mp_tac) >> simp[]
QED

Triviality append_itinerary_coordinates:
  create_blueprint_append_itinerary target off code data len a app bufop sz /\
  n = h + LENGTH app /\
  (!i. i < LENGTH app ==> C (h+1+i) = EL i app) ==>
  ?m u v. C (h+1) = m /\ h+1 <= n /\
    emit_op ADD [code;len] a = (sz,m) /\
    compile_alloc_dynamic sz m = (bufop,u) /\
    emit_void EXTCODECOPY [target;bufop;off;code] u = ((),v) /\
    (if len = Lit 0w then C n = v else
       ?dest b. emit_op ADD [bufop;code] v = (dest,b) /\
                compile_copy_memory_dynamic dest data len b = ((),C n))
Proof
  Cases_on `len = Lit 0w` >>
  rw[create_blueprint_append_itinerary_def] >> gvs[]
  >- (rename1 `emit_void EXTCODECOPY _ u = ((),v)` >>
      `C (h+1) = m /\ C (h+3) = v` by
        (qpat_x_assum `!i. i < _ ==> _` (fn th =>
           map_every (fn t => qspec_then t (assume_tac o EVAL_RULE) th) [`0`,`2`]) >>
         simp[]) >>
      metis_tac[]) >>
  rename1 `compile_copy_memory_dynamic dest data len b = ((),vfinal)` >>
  `C (h+1) = m /\ C (h+5) = vfinal` by
    (qpat_x_assum `!i. i < _ ==> _` (fn th =>
       map_every (fn t => qspec_then t (assume_tac o EVAL_RULE) th) [`0`,`4`]) >>
     simp[]) >>
  metis_tac[]
QED

(* The check is straight-line and every output is fresh at its entry. *)
Triviality blueprint_check_code:
  compile_create_blueprint_check lit target off a = (code,b) ==>
  b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  EVERY (\ins. ins.inst_opcode <> INVOKE /\ ~is_terminator ins.inst_opcode)
    (emitted_insts a b) /\
  (!x. not_fresh_at a x ==> EVERY (\ins. ~MEM x ins.inst_outputs) (emitted_insts a b))
Proof
  Cases_on `lit` >>
  rw[compile_create_blueprint_check_def, comp_bind_def, comp_ignore_bind_def,
     comp_return_def, emit_op_eq, emit_void_eq] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC,DROP_LENGTH_APPEND] >>
  fs[mk_inst_def,is_terminator_def,not_fresh_at_def] >> metis_tac[LESS_EQ_ADD,LESS_EQ_REFL]
QED

Triviality blueprint_add_code:
  emit_op ADD [code;len] a = (sz,b) ==>
  b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  EVERY (\ins. ins.inst_opcode <> INVOKE /\ ~is_terminator ins.inst_opcode)
    (emitted_insts a b)
Proof
  rpt strip_tac >> drule emit_op_extends >>
  drule emitted_insts_emit_op >> simp[same_blocks_def,mk_inst_def,is_terminator_def]
QED

Triviality blueprint_post_add_code:
  compile_alloc_dynamic sz a = (bufop,u) /\
  emit_void EXTCODECOPY [target;bufop;off;code] u = ((),v) /\
  (if len = Lit 0w then b = v else
     ?dest c. emit_op ADD [bufop;code] v = (dest,c) /\
              compile_copy_memory_dynamic dest data len c = ((),b)) ==>
  b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  EVERY (\ins. ins.inst_opcode <> INVOKE /\ ~is_terminator ins.inst_opcode)
    (emitted_insts a b)
Proof
  Cases_on `len = Lit 0w` >>
  rw[compile_alloc_dynamic_def, compile_copy_memory_dynamic_def, emit_op_eq, emit_void_eq] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC,DROP_LENGTH_APPEND] >>
  simp[mk_inst_def,is_terminator_def]
QED

Triviality check_frame_length:
  compile_create_blueprint_check lit target off a = (code,b) /\
  run_inst_seq (emitted_insts a b) u = OK t /\
  t.vs_labels = u.vs_labels /\
  (!x. len = Var x ==> not_fresh_at a x) ==>
  eval_operand len t = eval_operand len u
Proof
  strip_tac >> drule blueprint_check_code >> strip_tac >>
  Cases_on `len` >> simp[eval_operand_def] >>
  irule run_inst_seq_non_output_lookup >> goal_assum (drule_at Any) >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Triviality reset_selected_run_entry:
  run_inst_seq xs u = OK (t with vs_inst_idx := u.vs_inst_idx) /\
  EVERY (\ins. ins.inst_opcode <> INVOKE /\ ~is_terminator ins.inst_opcode) xs ==>
  run_inst_seq xs (u with vs_inst_idx := k) = OK (t with vs_inst_idx := k)
Proof
  strip_tac >>
  `EVERY (\ins. ~is_terminator ins.inst_opcode) xs` by fs[EVERY_MEM] >>
  drule run_inst_seq_inst_idx >> simp[exec_result_map_def]
QED

Triviality blueprint_selected_bands:
  create_blueprint_append_itinerary target off code data len (C (j+4)) app bufop sz /\
  n = j+4+LENGTH app /\
  (!i. i < LENGTH app ==> C (j+5+i) = EL i app) /\
  compile_create_blueprint_check lit target off (C (j+3)) = (code,C (j+4)) /\
  (!i. i <= n ==> (Obs i).vs_current_bb = (C i).cs_current_bb /\
    (Obs i).vs_inst_idx = LENGTH (C i).cs_current_insts /\
    ?x. ctor_segment_fetch fn (Obs i) = SOME x /\ (C i).cs_next_id <= x.inst_id) /\
  (!i k. i <= k /\ k <= n ==> ci_mono (C i) (C k) /\ fn_has_code (C i) (C k) fn) /\
  (!i. i < n ==> create_expr_prefix (C i) (C (SUC i)) explicit ctx fn
                    (Obs i) (M i) (Obs (SUC i))) ==>
  emit_op ADD [code;len] (C (j+4)) = (sz,C (j+5)) /\
  ?ca cxcopy. compile_alloc_dynamic sz (C (j+5)) = (bufop,ca) /\
    emit_void EXTCODECOPY [target;bufop;off;code] ca = ((),cxcopy) /\
    (if len = Lit 0w then C n = cxcopy else
       ?dst cs. emit_op ADD [bufop;code] cxcopy = (dst,cs) /\
                compile_copy_memory_dynamic dst data len cs = ((),C n)) /\
    run_inst_seq (emitted_insts (C (j+3)) (C (j+4))) (Obs (j+3)) =
      OK ((Obs (j+4)) with vs_inst_idx := (Obs (j+3)).vs_inst_idx) /\
    run_inst_seq (emitted_insts (C (j+4)) (C (j+5))) (Obs (j+4)) =
      OK ((Obs (j+5)) with vs_inst_idx := (Obs (j+4)).vs_inst_idx) /\
    run_inst_seq (emitted_insts (C (j+5)) (C n))
      ((Obs (j+5)) with vs_inst_idx := (Obs (j+4)).vs_inst_idx) =
      OK ((Obs n) with vs_inst_idx := (Obs (j+4)).vs_inst_idx)
Proof
  strip_tac >>
  `j+4+1 = j+5` by decide_tac >>
  mp_tac (Q.INST [`h` |-> `j+4`,`C` |-> `C`,`n` |-> `n`,`a` |-> `C (j+4)`]
    append_itinerary_coordinates) >>
  qpat_assum `j+4+1 = j+5` (pure_rewrite_tac o single) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choosel_then [`m`,`ca`,`cxcopy`] strip_assume_tac) >>
  qpat_x_assum `C (j+5) = m` (SUBST_ALL_TAC o SYM) >>
  drule_then strip_assume_tac blueprint_check_code >>
  drule_then strip_assume_tac blueprint_add_code >>
  drule_all_then strip_assume_tac blueprint_post_add_code >>
  `!i k. i <= k /\ k <= n /\
     (C k).cs_current_bb = (C i).cs_current_bb /\
     (C k).cs_current_insts = (C i).cs_current_insts ++ emitted_insts (C i) (C k) /\
     EVERY (\ins. ins.inst_opcode <> INVOKE /\ ~is_terminator ins.inst_opcode)
       (emitted_insts (C i) (C k)) ==>
     run_inst_seq (emitted_insts (C i) (C k)) (Obs i) =
       OK ((Obs k) with vs_inst_idx := (Obs i).vs_inst_idx)` by
    (rpt gen_tac >> strip_tac >> irule selected_band_run >> simp[] >>
     qexistsl [`M`,`ctx`,`explicit`,`fn`,`n`] >> simp[]) >>
  map_every (fn coords =>
    qpat_assum `!i k. _ ==> run_inst_seq _ _ = _` (qspecl_then coords mp_tac) >>
    (impl_tac >- (simp[] >> decide_tac)) >> disch_tac)
    [[`j+3`,`j+4`],[`j+4`,`j+5`],[`j+5`,`n`]] >>
  drule_all reset_selected_run_entry >>
  disch_then (qspec_then `(Obs (j+4)).vs_inst_idx` assume_tac) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`ca`,`cxcopy`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Triviality lookup_blueprint_prefix:
  dest_create_args (CreateFromBlueprint F) hs xs = SOME ops /\
  ops.co_code_src = AddressCodeSource addr /\ ops.co_code_offset = SOME off /\
  (lookup_account addr a).code = (lookup_account addr b).code ==>
  blueprint_prefix_size hs lit xs a = blueprint_prefix_size hs lit xs b
Proof
  simp[blueprint_prefix_size_def]
QED

(* The literal branch exports the exact unwrapped size at the same CREATE
   cursor, not merely a modular inequality. The check result tests code,
   so this includes offsets in the signed-negative band. *)
Theorem blueprint_selected_suffix_extent:
  create_blueprint_append_itinerary target off code data len (C (j+4)) app bufop sz /\
  n = j+4+LENGTH app /\
  (!i. i < LENGTH app ==> C (j+5+i) = EL i app) /\
  compile_create_blueprint_check lit target off (C (j+3)) = (code,C (j+4)) /\
  (!i. i <= n ==> ~(Obs i).vs_halted /\ (Obs i).vs_current_bb = (C i).cs_current_bb /\
    (Obs i).vs_inst_idx = LENGTH (C i).cs_current_insts /\
    ?x. ctor_segment_fetch fn (Obs i) = SOME x /\ x.inst_opcode <> PHI /\
         (C i).cs_next_id <= x.inst_id) /\
  (!i k. i <= k /\ k <= n ==> ci_mono (C i) (C k) /\ fn_has_code (C i) (C k) fn) /\
  (!i. i < n ==> create_expr_prefix (C i) (C (SUC i)) explicit ctx fn
                    (Obs i) (M i) (Obs (SUC i))) /\
  eval_operand len (Obs j) = SOME (n2w (LENGTH payload)) /\
  w2n (n2w (LENGTH payload) : bytes32) < 2 ** 64 /\
  (!x. len = Var x ==> not_fresh_at (C j) x) /\
  (!x w. not_fresh_at (C j) x /\ lookup_var x (Obs j) = SOME w ==>
    lookup_var x (Obs (j+3)) = SOME w) /\
  eval_operand target (Obs (j+3)) = SOME aw /\
  eval_operand off (Obs (j+3)) = SOME ow /\
  (!x. off = Var x ==> not_fresh_at (C (j+3)) x) /\
  dest_create_args (CreateFromBlueprint F) hs xs = SOME ops /\
  ops.co_code_src = AddressCodeSource (w2w aw) /\ ops.co_code_offset = SOME (w2n ow) /\
  eval_operand sz (Obs n) = SOME w ==>
  (?cn. blueprint_prefix_size hs lit xs (Obs (j+3)).vs_accounts = SOME cn /\
        w2n w <= cn + LENGTH payload) /\
  (lit ==> ?cw. eval_operand code (Obs (j+4)) = SOME cw /\
    0 < w2n cw /\ w2n cw < 2 ** 255 /\
    w2n w = w2n cw + w2n (n2w (LENGTH payload) : bytes32))
Proof
  strip_tac >>
  `!i. i <= n ==> (Obs i).vs_current_bb = (C i).cs_current_bb /\
    (Obs i).vs_inst_idx = LENGTH (C i).cs_current_insts /\
    ?x. ctor_segment_fetch fn (Obs i) = SOME x /\ (C i).cs_next_id <= x.inst_id` by
    (qx_gen_tac `i` >> strip_tac >>
     qpat_assum `!k. k <= n ==> ~(Obs k).vs_halted /\ _`
       (qspec_then `i` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
     strip_tac >> rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     goal_assum (drule_at Any) >> simp[]) >>
  drule_all_then strip_assume_tac blueprint_selected_bands >>
  suspend "length"
QED

Resume blueprint_selected_suffix_extent[length]:
  `j+3 < n` by decide_tac >>
  `!i. j <= i /\ i <= j+3 ==> (Obs (SUC i)).vs_labels = (Obs i).vs_labels` by
    (gen_tac >> strip_tac >> `i <= n /\ i < n` by decide_tac >>
     qpat_assum `!k. k <= n ==> ~(Obs k).vs_halted /\ _`
       (qspec_then `i` (drule_then strip_assume_tac)) >>
     qpat_assum `!k. k < n ==> create_expr_prefix _ _ _ _ _ _ _ _`
       (qspec_then `i` (drule_then assume_tac)) >>
     drule_all create_prefix_labels >> simp[]) >>
  `(Obs (j+3)).vs_labels = (Obs j).vs_labels /\
    (Obs (j+4)).vs_labels = (Obs (j+3)).vs_labels` by
    (qpat_x_assum `!i. _ ==> (Obs (SUC i)).vs_labels = _`
       (fn th => POP_ASSUM_LIST (K all_tac) >>
         map_every (fn i => qspec_then i mp_tac th >>
           (impl_tac >- decide_tac) >>
           disch_then (assume_tac o SIMP_RULE (srw_ss()) [ADD1, GSYM ADD_ASSOC]))
           [`j`,`j+1`,`j+2`,`j+3`]) >>
     asm_rewrite_tac[]) >>
  `eval_operand len (Obs (j+3)) = SOME (n2w (LENGTH payload))` by
    (irule blueprint_eval_operand_frame >> qexistsl [`C j`,`Obs j`] >> simp[]) >>
  `!x. len = Var x ==> not_fresh_at (C (j+3)) x` by
    (`j <= j+3 /\ j+3 <= n` by decide_tac >>
     qpat_assum `!i k. _ ==> ci_mono _ _ /\ _` (qspecl_then [`j`,`j+3`] mp_tac) >>
     (impl_tac >- decide_tac) >> disch_then (strip_assume_tac o REWRITE_RULE[ci_mono_def]) >>
     gen_tac >> disch_tac >> irule not_fresh_at_mono >> qexists_tac `C j` >> simp[]) >>
  qabbrev_tac `chk = (Obs (j+4)) with vs_inst_idx := (Obs (j+3)).vs_inst_idx` >>
  `chk.vs_labels = (Obs (j+3)).vs_labels` by simp[Abbr `chk`] >>
  `eval_operand len (Obs (j+4)) = SOME (n2w (LENGTH payload))` by
    (drule_all check_frame_length >> simp[Abbr `chk`]) >>
  `eval_operand code (Obs (j+4)) = eval_operand code chk` by simp[Abbr `chk`] >>
  suspend "extent"
QED

Resume blueprint_selected_suffix_extent[extent]:
  qabbrev_tac `pre = (Obs (j+5)) with vs_inst_idx := (Obs (j+4)).vs_inst_idx` >>
  qabbrev_tac `final = (Obs n) with vs_inst_idx := (Obs (j+4)).vs_inst_idx` >>
  `eval_operand sz final = SOME w` by simp[Abbr `final`] >>
  conj_tac
  >- (drule_all_then strip_assume_tac
        (REWRITE_RULE[REFL_CLAUSE] (Q.INST [`accounts` |-> `s.vs_accounts`]
          create_blueprint_pre_dispatch_extent)) >>
      `w' = w` by metis_tac[optionTheory.SOME_11] >>
      goal_assum (drule_at Any) >> fs[]) >>
  strip_tac >>
  qpat_assum `lit` (fn th => qpat_x_assum `compile_create_blueprint_check lit _ _ _ = _`
    (assume_tac o REWRITE_RULE[th])) >>
  drule_all_then strip_assume_tac blueprint_literal_checked_sum >>
  drule_all_then strip_assume_tac create_blueprint_allocation_geometry >>
  rename1 `eval_operand code (Obs (j+4)) = SOME checked` >>
  qexists_tac `checked` >> gvs[]
QED

Finalise blueprint_selected_suffix_extent

Theorem blueprint_selected_suffix_reject:
  create_blueprint_append_itinerary target off code data len (C (j+4)) app bufop sz /\
  n = j+4+LENGTH app /\
  (!i. i < LENGTH app ==> C (j+5+i) = EL i app) /\
  compile_create_blueprint_check lit target off (C (j+3)) = (code,C (j+4)) /\
  (!i. i <= n ==> ~(Obs i).vs_halted /\ (Obs i).vs_current_bb = (C i).cs_current_bb /\
    (Obs i).vs_inst_idx = LENGTH (C i).cs_current_insts /\
    ?x. ctor_segment_fetch fn (Obs i) = SOME x /\ x.inst_opcode <> PHI /\
         (C i).cs_next_id <= x.inst_id) /\
  (!i k. i <= k /\ k <= n ==> ci_mono (C i) (C k) /\ fn_has_code (C i) (C k) fn) /\
  (!i. i < n ==> create_expr_prefix (C i) (C (SUC i)) explicit ctx fn
                    (Obs i) (M i) (Obs (SUC i))) /\
  eval_operand len (Obs j) = SOME (n2w (LENGTH payload)) /\
  w2n (n2w (LENGTH payload) : bytes32) < 2 ** 64 /\
  (!x. len = Var x ==> not_fresh_at (C j) x) /\
  (!x w. not_fresh_at (C j) x /\ lookup_var x (Obs j) = SOME w ==>
    lookup_var x (Obs (j+3)) = SOME w) /\
  eval_operand target (Obs (j+3)) = SOME aw /\
  eval_operand off (Obs (j+3)) = SOME ow /\
  (!x. off = Var x ==> not_fresh_at (C (j+3)) x) /\
  create_operand_layout (CreateFromBlueprint raw) hs vs = xs /\
  dest_create_args (CreateFromBlueprint raw) hs xs = SOME ops /\
  ops.co_code_src = AddressCodeSource (w2w aw) /\ ops.co_code_offset = SOME (w2n ow) /\
  (lookup_account (w2w aw) q.accounts).code =
    (lookup_account (w2w aw) (Obs (j+3)).vs_accounts).code /\
  lit = blueprint_literal_offset cx hs args /\
  create_arg_ctor_types (CreateFromBlueprint raw) hs (MAP expr_type args) = SOME ct /\
  (if raw then ops.co_ctor_args = [BytesV payload] else
     encode_create_ctor_args (get_tenv cx) ct ops.co_ctor_args = SOME payload) /\
  eval_create_operands cx (CreateFromBlueprint raw) hs rof (MAP expr_type args) lit vs q = (res,out) /\
  eval_operand sz (Obs n) = SOME w /\ 2 * max_code_size < w2n w ==>
  res = INR (Error (RuntimeError "create initcode too large"))
Proof
  strip_tac >>
  `dest_create_args (CreateFromBlueprint F) hs xs = SOME ops` by
    (pure_rewrite_tac[dest_create_args_def, vyperASTTheory.create_kind_case_def] >> BETA_TAC >>
     qpat_assum `dest_create_args (CreateFromBlueprint raw) hs xs = SOME ops`
       (ACCEPT_TAC o BETA_RULE o PURE_REWRITE_RULE[dest_create_args_def, vyperASTTheory.create_kind_case_def])) >>
  drule_all blueprint_selected_suffix_extent >>
  disch_then (strip_assume_tac o cj 1) >>
  drule_all_then assume_tac lookup_blueprint_prefix >>
  `blueprint_prefix_size hs lit xs q.accounts = SOME cn` by metis_tac[] >>
  `2 * max_code_size < cn + LENGTH payload` by decide_tac >>
  qpat_x_assum `lit = blueprint_literal_offset cx hs args` SUBST_ALL_TAC >>
  drule_all blueprint_operands_size_reject >>
  disch_then (qspec_then `rof` mp_tac) >> simp[pairTheory.PAIR_EQ]
QED
