(* Interpret the prepared caller arguments at the selected package layout. *)
Theory bodySelectedStageEntryArgsMods
Ancestors
  bodyIntCallStagePacketMods intCallCallee entryArgPtrs vyperCall
  vyperTypeBindArguments vyperTypeInvariants calldataReconstruction
  memoryValueEncoding loweringStateRelDefs venomInst pair rich_list

val stage_row = ``intcall_stage_ops_mods (lo,func) cenv cx sa
    (s3,es1 with scopes := prev,t,G,tn) (pin : (string # num # num) option)
    (ops,ws,vals,ptys,pflags)``;
val row_align = ``bind_arguments (get_tenv cx) args vals = SOME penv /\
    ptys = MAP SND args /\ MAP FST params = MAP FST args /\
    MAP SND params = (pflags : bool list) /\ ALL_DISTINCT (MAP FST args)``;
val slots = ``!i tv. i < LENGTH params /\
    evaluate_type (get_tenv cx) (EL i ptys) = SOME tv ==>
    ?off sz. FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) /\
      type_memory_size tv <= sz /\
      (SND (EL i params) ==> 32 <= sz /\ is_word_type (EL i ptys)) /\
      (~SND (EL i params) ==> sz <= type_memory_size tv)``;

Theorem selected_stage_row_shape[local]:
  ^stage_row /\ ^row_align ==>
  LENGTH params = LENGTH args /\ LENGTH params = LENGTH ops /\
  LENGTH params = LENGTH ws /\ LENGTH params = LENGTH vals /\
  ALL_DISTINCT (MAP FST params) /\ FDOM penv = set (MAP FST params) /\
  (!i. i < LENGTH params ==> FST (EL i params) = FST (EL i args) /\
    SND (EL i params) = EL i pflags /\ SND (EL i args) = EL i ptys)
Proof
  strip_tac >> drule_then assume_tac bind_arguments_fdom >>
  qpat_x_assum `intcall_stage_ops_mods _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [intcall_stage_ops_mods_def]) >>
  `LENGTH params = LENGTH args` by
    (qpat_assum `MAP FST params = MAP FST args` (mp_tac o AP_TERM ``LENGTH : string list -> num``) >> simp[]) >>
  `LENGTH args = LENGTH ops` by
    (drule_then mp_tac bind_arguments_length >> asm_rewrite_tac[]) >>
  asm_rewrite_tac[] >> gen_tac >> disch_tac >>
  `i < LENGTH args` by simp[] >>
  rpt conj_tac
  >- (qpat_assum `MAP FST params = MAP FST args` (mp_tac o AP_TERM ``EL (i:num) : string list -> string``) >> simp[EL_MAP])
  >- (qpat_assum `MAP SND params = pflags` (mp_tac o AP_TERM ``EL (i:num) : bool list -> bool``) >> simp[EL_MAP]) >>
  simp[EL_MAP]
QED

val borrowed_row = ``?b cap inst.
    op_prov G (EL i ops) = SOME (b,cap) /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (b,cap) /\
    lo <= b /\ b + cap <= t.vs_alloca_next /\ b <= w2n (EL i ws) /\
    w2n (EL i (ws : bytes32 list)) + sz <= b + cap /\
    (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
      memory_value_rel tv (EL i vals) (w2n (EL i ws)) mem) /\
    (case pin of NONE => T | SOME (rb:string,pb,pk) =>
       b + cap <= pb \/ pb + pk <= b)``;

Theorem selected_borrowed_stage_row[local]:
  ^stage_row /\ i < LENGTH ops /\ ~EL i pflags /\
  evaluate_type (get_tenv cx) (EL i ptys) = SOME tv /\ sz <= type_memory_size tv ==>
  ^borrowed_row
Proof
  strip_tac >> qpat_x_assum `intcall_stage_ops_mods _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [intcall_stage_ops_mods_def]) >>
  qpat_x_assum `!j. j < LENGTH ops /\ _ ==> _`
    (qspec_then `i` mp_tac) >> (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choosel_then [`b`,`cap`,`aid`] strip_assume_tac) >>
  qpat_x_assum `!j rt. _ /\ evaluate_type _ _ = SOME rt ==> _`
    (qspecl_then [`i`,`tv`] mp_tac) >> (impl_tac >- asm_rewrite_tac[]) >>
  simp_tac bool_ss [] >> strip_tac >>
  qpat_x_assum `~EL i pflags ==> _` (drule_then strip_assume_tac) >>
  `b' = b /\ cap' = cap` by fs[] >>
  qpat_x_assum `b' = b` SUBST_ALL_TAC >> qpat_x_assum `cap' = cap` SUBST_ALL_TAC >>
  qexistsl_tac [`b`,`cap`,`inst`] >> simp[] >>
  gen_tac >> disch_tac >> irule val_in_memory_memory_value_rel >> simp[]
QED

Theorem selected_staged_slots[local]:
  ^stage_row /\ ^row_align /\ ^slots ==>
  !i. i < LENGTH params ==>
    ?tv off sz en. evaluate_type (get_tenv cx) (EL i ptys) = SOME tv /\
      FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) /\
      FLOOKUP penv (FST (EL i params)) = SOME en /\
      en.type = tv /\ en.value = EL i vals /\
      type_memory_size tv <= sz /\ val_wf tv (EL i vals) /\
      (SND (EL i params) ==> 32 <= sz /\
        !b m. mem_word_at b m = EL i ws ==> memory_value_rel tv (EL i vals) b m) /\
      (~SND (EL i params) ==> ^borrowed_row)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  gen_tac >> disch_tac >> drule_all_then strip_assume_tac selected_stage_row_shape >>
  `i < LENGTH args /\ i < LENGTH ops` by simp[] >>
  qpat_x_assum `!i. i < LENGTH params ==> FST _ = _ /\ _`
    (drule_then strip_assume_tac) >>
  drule_all_then strip_assume_tac bind_arguments_lookup_index >>
  rename1 `evaluate_type _ (SND (EL i args)) = SOME tv` >>
  `evaluate_type (get_tenv cx) (EL i ptys) = SOME tv` by
    (qpat_assum `SND (EL i args) = EL i ptys` (pure_once_rewrite_tac o single o SYM) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `!i tv. _ /\ evaluate_type _ _ = SOME tv ==> ?off sz. _`
    (drule_all_then strip_assume_tac) >>
  `val_wf tv (EL i vals)` by (irule bind_arguments_memory_wf >> rpt (goal_assum (drule_at Any))) >>
  qexistsl_tac [`tv`,`off`,`sz`,`<|assignable := T; type := tv; value := EL i vals; popped := []|>`] >>
  simp[] >> conj_tac
  >- (disch_tac >> rpt gen_tac >> disch_tac >>
      `is_word_type (EL i ptys)` by fs[] >>
      qpat_assum `intcall_stage_ops_mods _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [intcall_stage_ops_mods_def]) >>
      qpat_x_assum `!j rt. _ /\ evaluate_type _ _ = SOME rt ==> _`
        (qspecl_then [`i`,`tv`] mp_tac) >> (impl_tac >- asm_rewrite_tac[]) >>
      strip_tac >> irule val_in_memory_memory_value_rel >> simp[] >>
      irule calldata_word_representation >> simp[] >>
      qexistsl_tac [`get_tenv cx`,`EL i ptys`] >> asm_rewrite_tac[]) >>
  disch_tac >>
  `sz <= type_memory_size tv` by fs[] >>
  drule_all_then (mp_tac) selected_borrowed_stage_row >>
  simp_tac (srw_ss()) [arithmeticTheory.ADD_COMM]
QED

Theorem selected_stage_disjoint_shrink[local]:
  loweringStateRelDefs$regions_disjoint b cap c len /\
  b <= x /\ x + sz <= b + cap /\ c <= y /\ y + sy <= c + len ==>
  loweringStateRelDefs$regions_disjoint x sz y sy
Proof
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem selected_stage_distinct_rows[local]:
  ^stage_row /\ i < LENGTH ops /\ j < LENGTH ops /\ i <> j /\
  ~EL i pflags /\ ~EL j pflags /\
  op_prov G (EL i ops) = SOME (b,cap) /\ op_prov G (EL j ops) = SOME (c,len) ==>
  loweringStateRelDefs$regions_disjoint b cap c len
Proof
  strip_tac >> qpat_x_assum `intcall_stage_ops_mods _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [intcall_stage_ops_mods_def]) >>
  Cases_on `i < j`
  >- (first_x_assum (qspecl_then [`i`,`j`,`b`,`cap`,`c`,`len`] mp_tac) >> asm_rewrite_tac[]) >>
  `j < i` by decide_tac >>
  first_x_assum (qspecl_then [`j`,`i`,`c`,`len`,`b`,`cap`] mp_tac) >> asm_rewrite_tac[] >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def, DISJ_COMM]
QED

(* Work with index equalities so none of the row reasoning depends on
   whether the actual INVOKE has a hidden return operand. *)
val indexed_args = ``!i. i < LENGTH (params : (string # bool) list) ==>
    EL (idx + i) (arg_ops : operand list) = EL i ops /\
    EL (idx + i) (argv : bytes32 list) = EL i ws``;
val covered_args = ``!i off sz. i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) ==>
    ?b cap inst. op_prov G (EL (idx + i) arg_ops) = SOME (b,cap) /\
      MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      FLOOKUP t.vs_allocas inst.inst_id = SOME (b,cap) /\
      b <= w2n (EL (idx + i) (argv : bytes32 list)) /\
      w2n (EL (idx + i) argv) + sz <= b + cap``;

val borrowed_slots = ``!i off sz. i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) ==>
    ?b cap inst. op_prov G (EL i ops) = SOME (b,cap) /\
      MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      FLOOKUP t.vs_allocas inst.inst_id = SOME (b,cap) /\
      b <= w2n (EL i (ws : bytes32 list)) /\ w2n (EL i ws) + sz <= b + cap /\
      (case pin of NONE => T | SOME (rb:string,pb,pk) =>
         b + cap <= pb \/ pb + pk <= b)``;

Theorem selected_stage_borrowed_slots[local]:
  ^stage_row /\ ^row_align /\ ^slots ==> ^borrowed_slots
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  mp_tac selected_staged_slots >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!i. i < LENGTH params ==> ?tv off sz en. _` (drule_then strip_assume_tac) >>
  qpat_assum `~SND (EL i params) ==> _` (drule_then strip_assume_tac) >>
  `sz' = sz` by fs[] >> qpat_x_assum `sz' = sz` SUBST_ALL_TAC >>
  qexistsl_tac [`b`,`cap`,`inst`] >> asm_rewrite_tac[]
QED

Theorem selected_stage_internal_args[local]:
  ^stage_row /\ ^row_align /\ ^slots /\ ^indexed_args /\
  idx + LENGTH params <= LENGTH argv /\ LENGTH argv < dimword (:256) /\
  mem_agree_outside tn.t_mem t.vs_memory mem ==>
  internal_args_rel ce params penv idx argv t.vs_alloca_next mem
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all_then strip_assume_tac selected_stage_row_shape >>
  mp_tac selected_staged_slots >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac >>
  pure_rewrite_tac[internal_args_rel_def] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >> conj_tac
  >- (gen_tac >> disch_tac >>
      qpat_assum `!i. i < LENGTH params ==> ?tv off sz en. _` (drule_then strip_assume_tac) >>
      qexistsl_tac [`off`,`sz`,`en`] >> simp[] >>
      Cases_on `EL i pflags` >> simp[] >>
      `~SND (EL i params)` by simp[] >>
      qpat_assum `~SND (EL i params) ==> _` (drule_then strip_assume_tac) >>
      simp[] >> decide_tac) >>
  rpt gen_tac >> strip_tac >>
  mp_tac selected_stage_borrowed_slots >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac >>
  qpat_assum `^borrowed_slots` (qspecl_then [`i`,`offi`,`szi`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choosel_then [`b`,`cap`,`bi`] strip_assume_tac) >>
  qpat_assum `^borrowed_slots` (qspecl_then [`j`,`offj`,`szj`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choosel_then [`c`,`len`,`ci`] strip_assume_tac) >>
  `~EL i pflags /\ ~EL j pflags` by
    (qpat_assum `MAP SND params = pflags` (pure_once_rewrite_tac o single o SYM) >>
     simp[EL_MAP]) >>
  `i < LENGTH ops /\ j < LENGTH ops` by simp[] >>
  `loweringStateRelDefs$regions_disjoint b cap c len` by
    (mp_tac selected_stage_distinct_rows >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  simp[] >> irule selected_stage_disjoint_shrink >>
  qexistsl_tac [`b`,`c`,`cap`,`len`] >> simp[]
QED

val sret_pin = ``has_rb ==> ?pb pk. pin = SOME (rb:string,pb,pk) /\
    FLOOKUP G rb = SOME (pb,pk) /\ op_taint tn (Var rb) = {} /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (pb,pk) /\
    w2n (rbw : bytes32) = pb /\ lo <= pb /\ pb + pk <= t.vs_alloca_next /\
    type_memory_size rtv = rbs /\ rbs <= pk``;

val sret_slot = ``?pb pk. op_prov G (HD arg_ops) = SOME (pb,pk) /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (pb,pk) /\
    pb <= w2n (HD (argv : bytes32 list)) /\
    w2n (HD argv) + type_memory_size rtv <= pb + pk /\
    pb + pk <= t.vs_alloca_next /\ lo <= pb``;

val sret_separation = ``!i off sz. i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) ==>
    loweringStateRelDefs$regions_disjoint (w2n (HD (argv : bytes32 list)))
      (type_memory_size rtv) (w2n (EL (1 + i) argv)) sz``;

val entered_args = ``arg_ops = (if has_rb then Var rb::ops else ops) /\
    argv = (if has_rb then (rbw : bytes32)::ws else ws)``;

Theorem selected_stage_indices[local]:
  ^entered_args /\ LENGTH params = LENGTH ws ==>
  let idx = if has_rb then 1 else 0 in
  ^indexed_args /\ idx + LENGTH params <= LENGTH argv
Proof
  Cases_on `has_rb` >> simp[GSYM arithmeticTheory.SUC_ONE_ADD, EL]
QED

Theorem selected_stage_sret[local]:
  has_rb /\ ^sret_pin /\ ^entered_args /\ ^borrowed_slots ==>
  ^sret_slot /\ ^sret_separation
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_assum `has_rb ==> ?pb pk. _` (drule_then strip_assume_tac) >>
  conj_tac
  >- (qexistsl_tac [`pb`,`pk`] >> simp[ptrDisciplineTheory.op_prov_def]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `^borrowed_slots` (qspecl_then [`i`,`off`,`sz`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choosel_then [`b`,`cap`,`inst`] strip_assume_tac) >>
  simp[GSYM arithmeticTheory.SUC_ONE_ADD, EL] >> irule selected_stage_disjoint_shrink >>
  qexistsl_tac [`pb`,`b`,`pk`,`cap`] >>
  qpat_x_assum `case pin of NONE => T | SOME _ => _` mp_tac >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def, DISJ_COMM]
QED

Theorem selected_stage_entry_arg_row[local]:
  ^stage_row /\ ^row_align /\ ^slots /\ ^entered_args /\ ^sret_pin /\
  LENGTH argv < dimword (:256) ==>
  let idx = if has_rb then 1 else 0 in
  (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
    internal_args_rel ce params penv idx argv t.vs_alloca_next mem) /\
  ^covered_args /\ EVERY (\op. op_taint tn op = {}) arg_ops /\
  (!n en. FLOOKUP penv n = SOME en ==> value_has_type en.type en.value) /\
  (has_rb ==> ^sret_slot /\ ^sret_separation)
Proof
  pure_rewrite_tac[LET_THM] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all_then strip_assume_tac selected_stage_row_shape >>
  qabbrev_tac `idx = if has_rb then 1 else 0` >> CONV_TAC BETA_CONV >>
  `^indexed_args /\ idx + LENGTH params <= LENGTH argv` by
    (simp[Abbr `idx`] >> mp_tac selected_stage_indices >> simp[LET_THM]) >>
  mp_tac selected_stage_borrowed_slots >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      mp_tac selected_stage_internal_args >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `^borrowed_slots` (qspecl_then [`i`,`off`,`sz`] mp_tac) >>
      (impl_tac >- asm_rewrite_tac[]) >>
      disch_then (qx_choosel_then [`b`,`cap`,`inst`] strip_assume_tac) >>
      qexistsl_tac [`b`,`cap`,`inst`] >> simp[]) >>
  conj_tac
  >- (qpat_assum `intcall_stage_ops_mods _ _ _ _ _ _ _` mp_tac >>
      simp_tac (srw_ss()) [intcall_stage_ops_mods_def] >> strip_tac >>
      Cases_on `has_rb` >> fs[] >>
      qpat_assum `has_rb ==> ?pb pk. _` (drule_then strip_assume_tac) >> simp[]) >>
  conj_tac
  >- (drule bind_arguments_scope_well_typed_from_success >>
      rewrite_tac[scope_well_typed_def] >> disch_tac >>
      rpt gen_tac >> disch_tac >> first_x_assum (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  disch_tac >> mp_tac selected_stage_sret >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC
QED

(* The argument row is the actual supplied/default concatenation. *)
Theorem selected_stage_entry_args_mods:
  let ops = supplied ++ dfl in
  ^stage_row /\ ^row_align /\ ^slots /\ ^entered_args /\ ^sret_pin /\
  LENGTH argv < dimword (:256) ==>
  let idx = if has_rb then 1 else 0 in
  (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
    internal_args_rel ce params penv idx argv t.vs_alloca_next mem) /\
  ^covered_args /\ EVERY (\op. op_taint tn op = {}) arg_ops /\
  (!n en. FLOOKUP penv n = SOME en ==> value_has_type en.type en.value) /\
  (has_rb ==> ^sret_slot /\ ^sret_separation)
Proof
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  MATCH_ACCEPT_TAC selected_stage_entry_arg_row
QED
