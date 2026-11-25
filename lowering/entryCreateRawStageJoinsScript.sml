(* Scope geometry for the paired RawCreate itinerary. No execution of a
   successor stage is required to widen a focused or terminal left stage. *)
Theory entryCreateRawStageJoins
Ancestors
  entryCreateRegionLift entryCreatePendingScope entryCreateIntervalLayout
  createSizeOperandCode createSizeConcreteSnapshots createSizeResultCheckCode
  createSizePreparationCode createSizeCutCode createSizeCutRegion
  entryCreatePathScope entryCreateCompletedCut entryCreateFocusSpec
  createSizePrefixReplay bodySim fragExec compileEnv exprLowering builtinCreate
  emitHelper abiEncoderProps venomInst venomExecSemantics list pair arithmetic

Theorem raw_prefix_widen_right[local]:
  a.cs_next_id <= m.cs_next_id /\ create_expr_prefix m b E ctx fn t marks u ==>
  create_expr_prefix a b E ctx fn t marks u
Proof
  strip_tac >> irule create_expr_prefix_mono >>
  first_assum (irule_at Any) >>
  simp[create_prefix_step_def,frag_ids_def] >> metis_tac[LESS_EQ_TRANS]
QED

Theorem raw_full_scope_join[local]:
  a.cs_next_id <= m.cs_next_id /\ create_expr_prefix a b E ctx fn s left t /\
  create_operand_full_scope m b E ctx fn t right r ==>
  create_operand_full_scope a b E ctx fn s (left ++ right) r
Proof
  Cases_on `r` >> simp[create_operand_full_scope_def] >> strip_tac >>
  metis_tac[raw_prefix_widen_right,create_expr_prefix_append,APPEND_ASSOC]
QED

Theorem raw_create_scope_at_split:
  body_inv tops ctx ce cx /\ MEM fn ctx.ctx_functions /\
  create_cut_code {} a m /\ create_cut_code {} m b /\
  fn_has_code a b fn /\ create_layout a b ==>
  !s. create_operand_at a s ==>
    (!left t. create_expr_prefix a m E ctx fn s left t ==>
       create_expr_prefix a b E ctx fn s left t) /\
    (!left t right u. create_expr_prefix a m E ctx fn s left t /\
       create_expr_prefix m b E ctx fn t right u ==>
       create_expr_prefix a b E ctx fn s (left ++ right) u) /\
    (!marks. create_operand_focus_scope a m E ctx fn s marks ==>
       create_operand_focus_scope a b E ctx fn s marks) /\
    (!marks r. exit_result r /\ create_operand_full_scope a m E ctx fn s marks r ==>
       create_operand_full_scope a b E ctx fn s marks r) /\
    (!left t right. create_operand_full_scope a m E ctx fn s left (OK t) /\
       create_operand_focus_scope m b E ctx fn t right ==>
       create_operand_focus_scope a b E ctx fn s (left ++ right)) /\
    (!left t right r. create_operand_full_scope a m E ctx fn s left (OK t) /\
       create_operand_full_scope m b E ctx fn t right r ==>
       create_operand_full_scope a b E ctx fn s (left ++ right) r)
Proof
  strip_tac >>
  `cs_extends a m /\ cs_extends m b /\ a.cs_next_id <= m.cs_next_id /\
    m.cs_next_id <= b.cs_next_id` by fs[create_cut_code_def] >>
  drule_all fn_has_code_split >> strip_tac >>
  `!u. create_cut_region a m u /\ ~create_operand_at m u ==>
       ~create_operand_at b u` by metis_tac[create_layout_left_stop] >>
  rpt gen_tac >> strip_tac >>
  `create_cut_region a m s` by
    (fs[create_operand_at_def] >> metis_tac[create_cut_region_rules]) >>
  conj_asm1_tac >- metis_tac[create_left_prefix_lift_at] >>
  conj_tac >- metis_tac[raw_prefix_widen_right,create_expr_prefix_append] >>
  conj_tac >- metis_tac[create_left_focus_lift_at] >>
  conj_tac >- metis_tac[create_left_terminal_lift_at] >>
  reverse conj_tac
  >- (rpt gen_tac >> strip_tac >> irule raw_full_scope_join >>
      simp[] >> qexists_tac `m` >> simp[] >>
      qexists_tac `t` >> fs[create_operand_full_scope_def]) >>
  simp[create_operand_full_scope_def] >> rpt strip_tac >>
  `create_cut_region m b t` by metis_tac[create_cut_region_rules] >>
  irule create_operand_focus_scope_prepend >> qexists_tac `t` >>
  reverse conj_tac >- metis_tac[] >>
  irule create_operand_focus_scope_lift >> simp[] >>
  conj_tac >- (qexistsl_tac [`ce`,`cx`,`tops`] >> simp[]) >>
  qexistsl_tac [`m`,`b`] >> simp[] >>
  simp[create_prefix_step_def,frag_ids_def] >> metis_tac[LESS_EQ_TRANS]
QED

Theorem raw_ctor_args_cut_code[local]:
  !ctor ce a. create_cut_code {} a (SND (compile_create_ctor_args compile_expr ce ctor a))
Proof
  Induct >> simp[compile_create_ctor_args_def] >> rpt gen_tac >>
  irule create_cut_code_bind >> simp[create_operand_cut_code] >>
  irule create_cut_code_bind >> simp[create_vv_snapshot_cut_code] >>
  irule create_cut_code_bind >> simp[]
QED

Theorem raw_salt_cut_code[local]:
  compile_create_salt compile_expr ce salt a = (op,b) ==> create_cut_code {} a b
Proof
  Cases_on `salt` >> simp[compile_create_salt_def,comp_return_def,comp_bind_def] >>
  Cases_on `lower_value compile_expr ce (expr_type x) x a` >> simp[] >>
  metis_tac[cj 2 create_operand_cut_code,SND]
QED

Theorem raw_emit_cut_code[local]:
  create_cut_targets opc ops = [] /\ emit_op opc ops a = (op,b) ==>
  create_cut_code {} a b
Proof
  strip_tac >> `create_cut_code {} a (SND (emit_op opc ops a))` by
    (irule create_cut_code_emit_op >> simp[]) >> metis_tac[SND]
QED

Theorem raw_dispatch_cut_code[local]:
  compile_create_dispatch init_op size_op v salt rof a = (op,b) ==> create_cut_code {} a b
Proof
  Cases_on `salt` >> simp[compile_create_dispatch_def,comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  irule create_cut_code_join >> qexists_tac `cs'` >>
  (reverse conj_tac >- metis_tac[create_result_check_cut_code,SND]) >>
  irule raw_emit_cut_code >> goal_assum (drule_at Any) >> simp[create_cut_targets_def]
QED

Theorem raw_cut_chain[local]:
  !cuts a. LIST_REL (create_cut_code {}) (FRONT (a::cuts)) cuts ==>
    !i j. i <= j /\ j <= LENGTH cuts ==>
      create_cut_code {} (EL i (a::cuts)) (EL j (a::cuts))
Proof
  Induct >- simp[] >> simp[FRONT_CONS] >> rpt gen_tac >> strip_tac >>
  qpat_assum `!a. _` (drule_then assume_tac) >>
  Cases_on `j` >- simp[] >> Cases_on `i` >> simp[] >> strip_tac
  >- (irule create_cut_code_join >> qexists_tac `h` >> simp[] >>
      rename1 `j0 <= LENGTH cuts` >>
      `create_cut_code {} (EL 0 (h::cuts)) (EL j0 (h::cuts))` by
        (qpat_assum `!i j. i <= j /\ _ ==> _` irule >> simp[]) >> fs[EL]) >>
  qpat_assum `!i j. i <= j /\ _ ==> _` irule >> simp[]
QED

Theorem raw_cut_chain_split[local]:
  LIST_REL (create_cut_code {}) (FRONT (sa::cuts)) cuts /\
  LAST (sa::cuts) = sb /\ fn_has_code sa sb fn /\ create_layout sa sb /\
  i <= j /\ j <= k /\ k <= LENGTH cuts ==>
  create_cut_code {} (EL i (sa::cuts)) (EL j (sa::cuts)) /\
  create_cut_code {} (EL j (sa::cuts)) (EL k (sa::cuts)) /\
  fn_has_code (EL i (sa::cuts)) (EL k (sa::cuts)) fn /\
  create_layout (EL i (sa::cuts)) (EL k (sa::cuts))
Proof
  strip_tac >> drule raw_cut_chain >> strip_tac >>
  `EL (LENGTH cuts) (sa::cuts) = sb` by fs[LAST_EL] >>
  `cs_extends sa (EL i (sa::cuts))` by
    (first_x_assum (qspecl_then [`0`,`i`] mp_tac) >>
     simp[create_cut_code_def] >> decide_tac) >>
  `cs_extends (EL k (sa::cuts)) sb` by
    (first_x_assum (qspecl_then [`k`,`LENGTH cuts`] mp_tac) >>
     simp[create_cut_code_def]) >>
  `create_cut_code {} (EL i (sa::cuts)) (EL k (sa::cuts))` by
    (first_x_assum irule >> decide_tac) >>
  `cs_extends (EL i (sa::cuts)) (EL k (sa::cuts))` by fs[create_cut_code_def] >>
  rpt conj_tac
  >- (first_x_assum irule >> decide_tac)
  >- (first_x_assum irule >> decide_tac)
  >- metis_tac[fn_has_code_mid]
  >- metis_tac[create_layout_subinterval]
QED

(* The optional list contains the actual argument-evaluation and ABI
   preparation cursors, not any states reached during their execution. *)
Theorem raw_stage_cut_code[local]:
  compile_expr ce (expr_type code) code sa = (vv,a) /\
  compile_create_snapshot ce vv (lowered_value_type ce code) a = (root,b) /\
  emit_op MLOAD [root] b = (len,c) /\
  emit_op ADD [root;Lit 32w] c = (data,d) /\
  lower_value compile_expr ce (expr_type amount) amount e = (v,f) /\
  compile_create_salt compile_expr ce salt f = (sp,g) /\
  compile_create_dispatch bufop total_op v sp rof g = (result,sb) /\
  (if ctor = [] then e = d /\ mids = [] else
     ?vals buf dst args_len r i j k m tys cap.
       mids = [r;i;j;k;m] /\
       compile_create_ctor_args compile_expr ce ctor d = (vals,r) /\
       compile_alloc_buffer cap r = (buf,i) /\
       compile_copy_memory_dynamic buf.buf_operand data len i = ((),j) /\
       emit_op ADD [buf.buf_operand;len] j = (dst,k) /\
       compile_abi_encode_values_to_buf ce dst (ZIP (vals,tys)) k = (args_len,m) /\
       emit_op ADD [len;args_len] m = (total_op,e)) ==>
  let cuts = [a;b;c;d] ++ mids ++ [e;f;g;sb] in
  LIST_REL (create_cut_code {}) (FRONT (sa::cuts)) cuts
Proof
  simp[] >> strip_tac >>
  `create_cut_code {} sa a` by metis_tac[cj 1 create_operand_cut_code,SND] >>
  `create_cut_code {} a b` by metis_tac[create_bytecode_snapshot_cut_code,SND] >>
  `create_cut_code {} b c` by
    (irule raw_emit_cut_code >> goal_assum (drule_at Any) >> simp[create_cut_targets_def]) >>
  `create_cut_code {} c d` by
    (irule raw_emit_cut_code >> goal_assum (drule_at Any) >> simp[create_cut_targets_def]) >>
  `create_cut_code {} e f` by metis_tac[cj 2 create_operand_cut_code,SND] >>
  `create_cut_code {} f g` by metis_tac[raw_salt_cut_code] >>
  `create_cut_code {} g sb` by metis_tac[raw_dispatch_cut_code] >>
  Cases_on `ctor = []` >> gvs[FRONT_CONS] >> rpt conj_tac
  >- metis_tac[raw_ctor_args_cut_code,SND]
  >- metis_tac[createSizeCutOpensTheory.create_alloc_buffer_cut_code,SND]
  >- (`create_cut_code {} i (SND (compile_copy_memory_dynamic buf.buf_operand data len i))` by
        (pure_rewrite_tac[contextTheory.compile_copy_memory_dynamic_def] >>
         irule create_cut_code_emit_void >> simp[create_cut_targets_def]) >>
      metis_tac[SND])
  >- (irule raw_emit_cut_code >> goal_assum (drule_at Any) >> simp[create_cut_targets_def])
  >- metis_tac[createSizeEncodeCodeTheory.create_encode_values_cut_code,SND]
  >- (irule raw_emit_cut_code >> goal_assum (drule_at Any) >> simp[create_cut_targets_def])
QED

(* The ordinary half of raw_create_compile_cuts supplies these equations.
   A triple can span several stages: for example, bytecode and preparation
   may be joined before embedding the constructor scope. *)
Theorem raw_create_stage_scope_joins:
  body_inv tops ctx ce cx /\ MEM fn ctx.ctx_functions /\
  fn_has_code sa sb fn /\ create_layout sa sb /\
  compile_expr ce (expr_type code) code sa = (vv,a) /\
  compile_create_snapshot ce vv (lowered_value_type ce code) a = (root,b) /\
  emit_op MLOAD [root] b = (len,c) /\
  emit_op ADD [root;Lit 32w] c = (data,d) /\
  lower_value compile_expr ce (expr_type amount) amount e = (v,f) /\
  compile_create_salt compile_expr ce salt f = (sp,g) /\
  compile_create_dispatch bufop total_op v sp rof g = (result,sb) /\
  (if ctor = [] then e = d /\ mids = [] else
     ?vals buf dst args_len r i j k m tys cap.
       mids = [r;i;j;k;m] /\
       compile_create_ctor_args compile_expr ce ctor d = (vals,r) /\
       compile_alloc_buffer cap r = (buf,i) /\
       compile_copy_memory_dynamic buf.buf_operand data len i = ((),j) /\
       emit_op ADD [buf.buf_operand;len] j = (dst,k) /\
       compile_abi_encode_values_to_buf ce dst (ZIP (vals,tys)) k = (args_len,m) /\
       emit_op ADD [len;args_len] m = (total_op,e)) ==>
  let cuts = [a;b;c;d] ++ mids ++ [e;f;g;sb] in
  !i j k. i <= j /\ j <= k /\ k <= LENGTH cuts ==>
    let x = EL i (sa::cuts); m = EL j (sa::cuts); z = EL k (sa::cuts) in
    !s. create_operand_at x s ==>
      (!left t. create_expr_prefix x m E ctx fn s left t ==>
         create_expr_prefix x z E ctx fn s left t) /\
      (!left t right u. create_expr_prefix x m E ctx fn s left t /\
         create_expr_prefix m z E ctx fn t right u ==>
         create_expr_prefix x z E ctx fn s (left ++ right) u) /\
      (!marks. create_operand_focus_scope x m E ctx fn s marks ==>
         create_operand_focus_scope x z E ctx fn s marks) /\
      (!marks r. exit_result r /\ create_operand_full_scope x m E ctx fn s marks r ==>
         create_operand_full_scope x z E ctx fn s marks r) /\
      (!left t right. create_operand_full_scope x m E ctx fn s left (OK t) /\
         create_operand_focus_scope m z E ctx fn t right ==>
         create_operand_focus_scope x z E ctx fn s (left ++ right)) /\
      (!left t right r. create_operand_full_scope x m E ctx fn s left (OK t) /\
         create_operand_full_scope m z E ctx fn t right r ==>
         create_operand_full_scope x z E ctx fn s (left ++ right) r)
Proof
  simp_tac std_ss [LET_THM] >> strip_tac >>
  `LIST_REL (create_cut_code {})
     (FRONT (sa::([a;b;c;d] ++ mids ++ [e;f;g;sb])))
     ([a;b;c;d] ++ mids ++ [e;f;g;sb])` by
    (irule (SIMP_RULE std_ss [LET_THM] raw_stage_cut_code) >>
     rpt (goal_assum (drule_at Any))) >>
  qabbrev_tac `cuts = [a;b;c;d] ++ mids ++ [e;f;g;sb]` >>
  `LAST (sa::cuts) = sb` by simp[Abbr `cuts`, LAST_CONS_cond, LAST_APPEND_CONS] >>
  ntac 3 gen_tac >> strip_tac >>
  drule_all raw_cut_chain_split >> strip_tac >>
  gen_tac >> strip_tac >>
  drule_all raw_create_scope_at_split >> disch_then (qspec_then `E` ACCEPT_TAC)
QED
