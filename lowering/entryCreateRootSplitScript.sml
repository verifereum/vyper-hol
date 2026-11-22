(* Static dispatch geometry is used only after the selected native visit
   identifies the caller fetch.  A pending INVOKE is handled separately. *)
Theory entryCreateRootSplit
Ancestors
  entryCreateFocusSpec createSizeItinerary createSizePrefixCuts
  createSizeResultCheckCode createResultTail compilerInstructionSuffix
  exprSimSend builtinCreate loweringShapeRules exprLoweringProps
  emitHelper fragExec compileEnv context abiEncoderProps loweringShapeDefs
  createSizeCutCode stmtLoweringMono localPtrsProps venomInst venomExecSemantics
  venomRunBounded createSizeCutRegion createSizePrefixReplay entryCreateOperandReplay
  bodySim fragGasOrigin relation pred_set list rich_list pair arithmetic

Theorem create_result_check_admin[local]:
  compile_check_create_result created rof sd = (result,sb) /\
  fn_has_code sd sb fn /\ fn_inst_ids_distinct fn /\
  MEM i (fn_insts fn) /\ i.inst_id IN frag_ids sd sb ==>
  ~MEM i.inst_opcode [CREATE; CREATE2; INVOKE]
Proof
  Cases_on `rof` >>
  simp[compile_check_create_result_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_label_def, emit_inst_def, new_block_def,
       emit_op_def, emit_void_def, compile_alloc_buffer_def, fresh_id_def,
       fresh_var_def, emit_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  TRY (qsuff_tac `~MEM i.inst_opcode [CREATE;CREATE2;INVOKE]`
        >- simp[] >>
       irule (BETA_RULE (Q.INST [`P` |-> `\i. ~MEM i.inst_opcode [CREATE;CREATE2;INVOKE]`]
         added_insts_function_property)) >>
       qexistsl_tac [`fn`,`sd`,`sb`] >>
       gvs[cs_extends_def, added_insts_def, state_insts_def, all_blocks_def,
           frag_ids_def, MAP_APPEND, FLAT_APPEND, mk_inst_def] >>
       `!a b. a + b - (a + (b + 1)) = 0` by decide_tac >>
       simp[DROP_APPEND, DROP_LENGTH_TOO_LONG, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
       rpt strip_tac >> decide_tac >> NO_TAC) >>
  gvs[frag_ids_def]
QED

(* The compiler cut at the outer emit is fixed before inspecting the hit.
   All interesting instructions in the band are earlier, or are that emit. *)
Theorem create_dispatch_owned_band[local]:
  ci_mono sa sc /\ emit_op opc ops sc = (created,sd) /\
  MEM opc [CREATE;CREATE2] /\
  compile_check_create_result created rof sd = (result,sb) /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn ==>
  ?inst bb.
    lookup_block sc.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sc.cs_current_insts) = SOME inst /\
    inst.inst_id = sc.cs_next_id /\ inst.inst_opcode = opc /\
    inst.inst_id IN frag_ids sa sb /\
    (!j. MEM j (fn_insts fn) /\ j.inst_id IN frag_ids sa sb /\
         MEM j.inst_opcode [CREATE;CREATE2;INVOKE] ==>
       j.inst_id IN frag_ids sa sc \/ j = inst)
Proof
  strip_tac >> drule_then strip_assume_tac added_insts_emit_op >>
  `create_cut_code {} sd sb` by metis_tac[create_result_check_cut_code,SND] >>
  `cs_extends sa sc /\ cs_extends sc sd /\ cs_extends sd sb /\
   sc.cs_next_id IN frag_ids sa sb` by
    fs[ci_mono_def, create_cut_code_def, frag_ids_def] >>
  `fn_has_code sc sd fn /\ fn_has_code sd sb fn` by
    metis_tac[fn_has_code_mid,fn_has_code_split,cs_extends_trans] >>
  qmatch_asmsub_abbrev_tac `added_insts sc sd = [dispatch]` >>
  `MEM dispatch (fn_insts fn) /\ dispatch.inst_id = sc.cs_next_id /\
   dispatch.inst_opcode = opc` by
    (reverse (rpt conj_tac)
     >- simp[Abbr `dispatch`,mk_inst_def]
     >- simp[Abbr `dispatch`,mk_inst_def] >>
     irule added_insts_function_member >> qexistsl_tac [`sc`,`sd`] >> simp[Abbr `dispatch`]) >>
  `!j. MEM j (fn_insts fn) /\ j.inst_id IN frag_ids sa sb /\
      MEM j.inst_opcode [CREATE;CREATE2;INVOKE] ==>
      j.inst_id IN frag_ids sa sc \/ j = dispatch` by
    (rpt strip_tac >> Cases_on `j.inst_id < sc.cs_next_id`
     >- (disj1_tac >> fs[frag_ids_def]) >>
     Cases_on `j.inst_id = sc.cs_next_id`
     >- (disj2_tac >> metis_tac[fn_inst_ids_distinct_inj]) >>
     `j.inst_id IN frag_ids sd sb` by (fs[frag_ids_def] >> decide_tac) >>
     drule_all create_result_check_admin >> simp[]) >>
  qexists_tac `dispatch` >> simp[] >>
  drule emit_op_facts >> strip_tac >>
  qpat_x_assum `fn_has_code sc sd fn`
    (strip_assume_tac o REWRITE_RULE[fn_has_code_def]) >>
  fs[get_instruction_def, IS_PREFIX_APPEND, Abbr `dispatch`] >>
  qexists_tac `bb` >> gvs[EL_APPEND_EQN]
QED

(* A native caller edge, including its whole returned child trace, changes
   bands only by reaching the compile-time cut. *)
Theorem create_native_step_in_band[local]:
  body_inv tops ctx ce cx /\ MEM fn ctx.ctx_functions /\
  create_cut_code {} a b /\ fn_has_code a b fn /\
  create_cut_region a b u /\ ~create_operand_at b u /\
  create_operand_native_step sa sb explicit ctx fn p (d,k,u,left) (d',k',v,all) ==>
  create_operand_native_step a b explicit ctx fn p (d,k,u,left) (d',k',v,all) /\
  create_cut_region a b v
Proof
  simp[create_operand_native_step_def, create_operand_fetch_def,
       create_operand_at_def, LET_THM] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `create_prefix_step sa sb explicit ctx fn u ms v` >>
  `gas_origin_edge F explicit ctx fn u ms (OK v)` by
    fs[create_prefix_step_def] >>
  `create_prefix_step a b explicit ctx fn u ms v /\ create_cut_region a b v` by
    (irule operand_cut_region_edge >> goal_assum (drule_at Any) >> metis_tac[]) >>
  simp[] >> gvs[create_prefix_step_def]
QED

Theorem create_native_step_off[local]:
  create_operand_native_step sa sb explicit ctx fn p (d,k,u,left) (d',k',v,all) ==>
  ~create_operand_at sb u
Proof
  rw[create_operand_native_step_def, create_operand_fetch_def, LET_THM]
QED

Theorem create_native_prefix_bands[local]:
  !x y. RTC (create_operand_native_step sa sb explicit ctx fn p) x y ==>
  !d k s d' k' u left.
    x = (d,k,s,[]) /\ y = (d',k',u,left) /\ create_operand_at sa s /\
    body_inv tops ctx ce cx /\ MEM fn ctx.ctx_functions /\
    create_cut_code {} sa sc /\ fn_has_code sa sc fn /\
    create_cut_code {} sc sb /\ fn_has_code sc sb fn ==>
    (RTC (create_operand_native_step sa sc explicit ctx fn p) x y /\
     create_cut_region sa sc u) \/ create_cut_region sc sb u
Proof
  ho_match_mp_tac RTC_INDUCT_RIGHT1 >> conj_tac
  >- (simp[create_operand_at_def] >> metis_tac[create_cut_region_rules]) >>
  simp_tac bool_ss [FORALL_PROD] >> rpt strip_tac >> gvs[] >>
  rename1 `create_operand_native_step sa sb explicit ctx fn p (dc,kc,c,pre) (dv,kv,v,all)` >>
  drule create_native_step_off >> strip_tac
  >- (Cases_on `create_operand_at sc c`
      >- (`create_cut_region sc sb c` by
            metis_tac[create_cut_region_rules,create_operand_at_def] >>
          disj2_tac >> metis_tac[create_native_step_in_band]) >>
      disj1_tac >>
      `create_operand_native_step sa sc explicit ctx fn p (dc,kc,c,pre) (dv,kv,v,all) /\
       create_cut_region sa sc v` by (irule create_native_step_in_band >> simp[] >> metis_tac[]) >>
      simp[] >> metis_tac[RTC_TRANS,RTC_SINGLE]) >>
  disj2_tac >> metis_tac[create_native_step_in_band]
QED

Theorem create_fetch_in_band[local]:
  create_cut_code {} a b /\ fn_has_code a b fn /\
  create_cut_region a b u /\ ~create_operand_at b u /\
  create_operand_fetch sa sb fn u inst ==>
  create_operand_fetch a b fn u inst
Proof
  rw[create_operand_fetch_def] >>
  `u.vs_current_bb <> b.cs_current_bb \/ u.vs_inst_idx <> LENGTH b.cs_current_insts` by
    metis_tac[create_operand_at_def] >>
  metis_tac[create_cut_region_rules]
QED

Theorem create_interior_visit_bands[local]:
  body_inv tops ctx ce cx /\ MEM fn ctx.ctx_functions /\
  create_cut_code {} sa sc /\ fn_has_code sa sc fn /\
  create_cut_code {} sc sb /\ fn_has_code sc sb fn /\
  create_interior_visit sa sb explicit ctx fn (p,d,k) s (before,hit,after) ==>
  create_interior_visit sa sc explicit ctx fn (p,d,k) s (before,hit,after) \/
  ?dc kc u left inst.
    create_expr_prefix sa sb explicit ctx fn s (create_cut_marks explicit left) u /\
    create_operand_fetch sc sb fn u inst /\
    let visit = ((p,dc,inst.inst_id),fn,inst,u) in
      (before = left /\ hit = visit) \/
      (?inside suffix. before = left ++ visit::inside /\
        trace_step p dc kc ctx fn inst u = inside ++ hit::suffix)
Proof
  simp_tac bool_ss [create_interior_visit_def,LET_THM] >>
  disch_then (map_every
    (fn th => if is_exists (concl th) then
       qx_choosel_then [`dc`,`kc`,`u`,`left`,`inst`] (map_every assume_tac o CONJUNCTS) th
       else assume_tac th) o CONJUNCTS) >>
  `(RTC (create_operand_native_step sa sc explicit ctx fn p) (d,k,s,[]) (dc,kc,u,left) /\
    create_cut_region sa sc u /\ ~create_operand_at sc u) \/ create_cut_region sc sb u` by
    (Cases_on `create_operand_at sc u`
     >- (disj2_tac >> metis_tac[cj 1 create_cut_region_rules,create_operand_at_def]) >>
     simp[] >> irule create_native_prefix_bands >> simp[] >> metis_tac[])
  >- (disj1_tac >> qexistsl_tac [`dc`,`kc`,`u`,`left`,`inst`] >>
      simp[] >> metis_tac[create_fetch_in_band]) >>
  disj2_tac >> qexistsl_tac [`dc`,`kc`,`u`,`left`,`inst`] >> simp[] >>
  conj_tac >- (irule create_operand_native_prefix >>
               rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `~create_operand_at sb u` by fs[create_operand_fetch_def] >>
  metis_tac[create_fetch_in_band]
QED
