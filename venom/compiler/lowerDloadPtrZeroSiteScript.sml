(* Concrete zero-size-site witness for the frozen LowerDload contract. *)
Theory lowerDloadPtrZeroSite
Ancestors
  o1PassContract lowerDloadPtrPrimitives lowerDloadDefs ptrDiscipline

Definition zs_fn_def:
  zs_fn = mk_raw_function "main"
    [<| bb_label := "main"; bb_instructions :=
      [mk_inst 0 ALLOCA [Lit 0w] ["p"];
       mk_inst 1 DLOAD [Lit 0w] ["d"];
       mk_inst 2 ALLOCA [Lit 0w] ["q"];
       mk_inst 3 EQ [Var "p"; Var "q"] ["c"];
       mk_inst 4 STOP [] []] |>]
End

Definition zs_ctx_def:
  zs_ctx = mk_venom_context [zs_fn] (SOME "main")
End

Definition zs_vs_def:
  zs_vs = (init_venom_state "main") with
    vs_labels := FEMPTY |+ ("code_end", 0w)
End

Theorem zs_state_ok:
  o1_run_state_ok zs_vs
Proof
  simp[o1_run_state_ok_def, unitTransformDefsTheory.o1_initial_state_ok_def,
       code_layout_valid_def, zs_vs_def, venomStateTheory.init_venom_state_def,
       finite_mapTheory.FLOOKUP_UPDATE, wordsTheory.dimword_def]
QED

Theorem zs_no_opaque:
  (!x. ~unitShapeDefs$gas_var zs_fn x) /\
  (!x. ~unitShapeDefs$retpc_var zs_fn x)
Proof
  simp[unitShapeDefsTheory.gas_var_def, unitShapeDefsTheory.retpc_var_def] >>
  conj_tac >> irule unitShapeDefsTheory.copy_phi_var_no_seed >>
  simp[zs_fn_def, venomInstTheory.mk_raw_function_def,
       venomInstTheory.fn_insts_def, venomInstTheory.fn_insts_blocks_def,
       venomInstTheory.mk_inst_def] >> rpt strip_tac >> gvs[]
QED

Theorem zs_shape:
  o1_ctx_shape zs_ctx
Proof
  simp[o1_ctx_shape_def, zs_ctx_def, venomInstTheory.mk_venom_context_def,
       o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def,
       unitShapeDefsTheory.opaque_use_ok_def, zs_no_opaque] >>
  EVAL_TAC >> rpt strip_tac >> gvs[]
QED

Theorem zs_pointer_use_step:
  pointerConfinedDefs$pointer_use_step zs_fn vars = []
Proof
  EVAL_TAC
QED

Theorem zs_pointer_derived:
  FINITE roots ==>
  pointerConfinedDefs$pointer_derived_vars zs_fn roots = roots
Proof
  simp[pointerConfinedDefsTheory.pointer_derived_vars_def,
       pointerConfinedDefsTheory.pointer_use_vars_def,
       pointerConfinedDefsTheory.pointer_use_step_step_def,
       zs_pointer_use_step] >>
  simp[Once WhileTheory.OWHILE_THM] >>
  simp[Once WhileTheory.OWHILE_THM] >>
  simp[pred_setTheory.EXTENSION, listTheory.MEM_SET_TO_LIST]
QED

Theorem zs_ptr_roots:
  ptr_roots (\nm. {}) zs_fn = {"p"; "q"}
Proof
  simp[ptr_roots_def, pointerConfinedDefsTheory.alloca_roots_def,
       zs_fn_def, venomInstTheory.mk_raw_function_def,
       venomInstTheory.fn_insts_def, venomInstTheory.fn_insts_blocks_def,
       venomInstTheory.mk_inst_def, venomInstTheory.inst_output_def,
       pred_setTheory.EXTENSION, DISJ_IMP_THM, FORALL_AND_THM,
       RIGHT_AND_OVER_OR, EXISTS_OR_THM]
QED

Theorem zs_fn_ptr_ok:
  fn_ptr_ok (\nm. {}) zs_fn
Proof
  simp[fn_ptr_ok_def, fn_pv_def, zs_ptr_roots, zs_pointer_derived,
       pointerConfinedDefsTheory.affine_pointer_ops_def,
       pointerConfinedDefsTheory.phi_pv_all_var_def] >>
  EVAL_TAC >> rpt strip_tac >> gvs[ptr_use_ok_def]
QED

Theorem zs_static_premises:
  callee_first ["main"] zs_ctx.ctx_functions /\
  fixed_region_reserved 0 zs_ctx /\ ~ctx_has_dalloca zs_ctx /\
  fmp_free_ctx zs_ctx /\
  EVERY (\fn. fn.fn_eom = NONE) zs_ctx.ctx_functions /\
  reserved_intervals_wf zs_ctx.ctx_global_reserved /\
  ctx_dload_count zs_ctx = 1
Proof
  simp[callee_first_def, fixed_region_reserved_def, ctx_has_dalloca_def,
       fmp_free_ctx_def, ctx_dload_count_def,
       zs_ctx_def, venomInstTheory.mk_venom_context_def] >>
  EVAL_TAC >> rpt strip_tac >> gvs[]
QED

Theorem all_dead_wf:
  dead_wf <|d_stor := (\a st. UNIV); d_trans := (\a st. UNIV);
            d_imm := (\im. UNIV); d_ret := (\r. UNIV)|>
Proof
  simp[dead_wf_def]
QED

Theorem all_dead_taint_within:
  taint_within
    <|d_stor := (\a st. UNIV); d_trans := (\a st. UNIV);
      d_imm := (\im. UNIV); d_ret := (\r. UNIV)|> ctx vs
Proof
  simp[taint_within_def]
QED

Definition zs_unit_def:
  zs_unit = <|cu_context := zs_ctx; cu_data_segment := []|>
End

Definition zs_supply_def:
  zs_supply = irSupply$init_ir_supply zs_unit
End

Definition zs_out_def:
  zs_out =
    let ft = lower_dload_function_supply zs_supply zs_fn in
    <|fpo_function := FST ft; fpo_label_map := [];
      fpo_supply := (SND ft) with
        irs_used_labels := "code_end" :: (SND ft).irs_used_labels|>
End

Theorem zs_pass_step:
  fn_pass_step rpolicy (CFP_Simple VP_LowerDload)
    zs_unit zs_supply zs_fn zs_out
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[]
QED

Definition zs_target_def:
  zs_target = zs_ctx with ctx_functions := [zs_out.fpo_function]
End

Theorem zs_stage:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload)
    (\C fn observed. T) zs_ctx zs_target
Proof
  simp[ctx_pass_stage_def, zs_target_def, zs_ctx_def,
       venomInstTheory.mk_venom_context_def] >>
  qexistsl [`zs_unit`, `zs_supply`, `zs_out`] >>
  simp[zs_pass_step, zs_unit_def, zs_ctx_def,
       venomInstTheory.mk_venom_context_def]
QED

(* Exact source trace, including the two ghost maps. *)
Definition zs_trace_def:
  (zs_trace 0 = (FEMPTY, entry_taint, zs_vs)) /\
  (zs_trace (SUC n) =
    let (G,tn,s) = zs_trace n in
    let inst = EL n (fn_insts zs_fn) in
    let s' = case step_inst 0 zs_ctx inst s of OK t => t | _ => s in
    (step_prov [] G inst s', step_taint inst s s' tn,
     s' with vs_inst_idx := SUC n))
End

Theorem zs_trace_index:
  !n. n < 5 ==> (SND (SND (zs_trace n))).vs_inst_idx = n
Proof
  rpt strip_tac >>
  `n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4` by decide_tac >>
  gvs[] >> EVAL_TAC
QED

Theorem zs_trace_active:
  !n inst. n < 5 ==>
  (active_inst zs_fn inst (SND (SND (zs_trace n))) <=>
   inst = EL n (fn_insts zs_fn))
Proof
  rpt strip_tac >>
  `n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4` by decide_tac >>
  gvs[] >> EVAL_TAC >> simp[EQ_SYM_EQ]
QED

Theorem zs_trace_opcode:
  !n. n < 5 ==>
  (EL n (fn_insts zs_fn)).inst_opcode <> INVOKE /\
  (is_terminator (EL n (fn_insts zs_fn)).inst_opcode <=> n = 4)
Proof
  gen_tac >> disch_tac >>
  `n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4` by decide_tac >>
  gvs[] >> EVAL_TAC
QED

Theorem zs_trace_step:
  !n fuel. n < 4 ==>
  step_inst fuel zs_ctx (EL n (fn_insts zs_fn)) (SND (SND (zs_trace n))) =
    OK ((SND (SND (zs_trace (SUC n)))) with vs_inst_idx := n)
Proof
  rpt strip_tac >>
  `n = 0 \/ n = 1 \/ n = 2 \/ n = 3` by decide_tac >>
  gvs[] >>
  simp[venomExecSemanticsTheory.step_inst_non_invoke,
       zs_fn_def, venomInstTheory.mk_raw_function_def,
       venomInstTheory.fn_insts_def, venomInstTheory.fn_insts_blocks_def,
       venomInstTheory.mk_inst_def] >> EVAL_TAC
QED

Theorem zs_entry_facts:
  lookup_function "main" [zs_fn] = SOME zs_fn /\
  fn_entry_label zs_fn = SOME "main" /\
  (!s. enters_block zs_fn
    (zs_vs with <|vs_prev_bb := NONE; vs_current_bb := "main";
                 vs_inst_idx := 0|>) s <=> s = zs_vs)
Proof
  EVAL_TAC >> simp[venomExecSemanticsTheory.eval_phis_def,
    venomExecSemanticsTheory.phi_prefix_length_def]
QED

Theorem zs_trace_stop:
  !fuel s'. step_inst fuel zs_ctx (EL 4 (fn_insts zs_fn))
    (SND (SND (zs_trace 4))) <> OK s'
Proof
  gen_tac >>
  simp[venomExecSemanticsTheory.step_inst_non_invoke,
       zs_fn_def, venomInstTheory.mk_raw_function_def,
       venomInstTheory.fn_insts_def, venomInstTheory.fn_insts_blocks_def,
       venomInstTheory.mk_inst_def] >> EVAL_TAC >> simp[]
QED

Theorem zs_frame_trace:
  !vs0 ctx stk PG G tn fn inst s.
    frame_reachable vs0 ctx stk PG G tn fn inst s ==>
    vs0 = zs_vs ==> ctx = zs_ctx ==>
    ?n. n < 5 /\ stk = [] /\ PG = [] /\ fn = zs_fn /\
        inst = EL n (fn_insts zs_fn) /\ (G,tn,s) = zs_trace n
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt strip_tac >> gvs[] >>
      gvs[zs_ctx_def, venomInstTheory.mk_venom_context_def, zs_entry_facts] >>
      qexists_tac `0` >> simp[zs_trace_def] >>
      mp_tac (Q.SPECL [`0`, `inst`] zs_trace_active) >>
      simp[zs_trace_def])
  >- (rpt gen_tac >> strip_tac >> rpt strip_tac >> gvs[] >>
      `n < 4` by (drule zs_trace_opcode >> gvs[] >> decide_tac) >>
      drule zs_trace_step >> disch_then (qspec_then `fuel` mp_tac) >>
      simp[] >> strip_tac >>
      qpat_x_assum `(G,tn,s) = _` (assume_tac o SYM) >> fs[] >>
      `n < 5` by decide_tac >>
      `s.vs_inst_idx = n` by (drule zs_trace_index >> simp[]) >>
      fs[] >> qexists_tac `SUC n` >>
      conj_tac >- decide_tac >>
      `step_inst 0 zs_ctx (EL n (fn_insts zs_fn)) s = OK s'` by
        metis_tac[venomExecSemanticsTheory.step_inst_non_invoke] >>
      `zs_trace (SUC n) =
        (step_prov [] G (EL n (fn_insts zs_fn)) s',
         step_taint (EL n (fn_insts zs_fn)) s s' tn,
         s' with vs_inst_idx := SUC n)` by simp[Once zs_trace_def] >>
      reverse conj_tac >- simp[] >>
      `SUC n < 5` by decide_tac >>
      drule zs_trace_active >> disch_then (qspec_then `inst'` mp_tac) >> simp[])
  >- (rpt gen_tac >> strip_tac >> rpt strip_tac >> gvs[] >>
      drule zs_trace_opcode >> simp[] >> strip_tac >> gvs[] >>
      qpat_x_assum `(G,tn,s) = _` (assume_tac o SYM) >>
      qspec_then `fuel` mp_tac zs_trace_stop >> simp[] >> strip_tac >> gvs[])
  >- (rpt gen_tac >> strip_tac >> rpt strip_tac >> gvs[] >>
      drule zs_trace_opcode >> gvs[])
  >> rpt gen_tac >> strip_tac >> rpt strip_tac >> gvs[]
QED

Theorem zs_trace_safe:
  !n. n < 5 ==>
    access_ok 0 (FST (zs_trace n)) zs_fn (EL n (fn_insts zs_fn))
      (SND (SND (zs_trace n))) /\
    taint_ok zs_fn (FST (SND (zs_trace n))) (EL n (fn_insts zs_fn))
      (SND (SND (zs_trace n))) /\
    allocas_from 0 (SND (SND (zs_trace n)))
Proof
  gen_tac >> disch_tac >>
  `n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4` by decide_tac >>
  gvs[] >> EVAL_TAC >> simp[finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[] >> Cases_on `op = Var "p"` >> gvs[] >>
  Cases_on `op = Var "q"` >> gvs[]
QED

Theorem zs_ptr_discipline:
  ptr_discipline 0 zs_ctx zs_vs
Proof
  simp[ptr_discipline_def] >> qexists_tac `(\nm. {})` >>
  conj_tac
  >- simp[zs_ctx_def, venomInstTheory.mk_venom_context_def, zs_fn_ptr_ok] >>
  rpt gen_tac >> strip_tac >> drule zs_frame_trace >> simp[] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `(G,tn,s) = _` (assume_tac o SYM) >>
  drule zs_trace_safe >> simp[zs_static_premises]
QED

Theorem zs_raw_frame:
  !vs0 ctx fn inst s.
    raw_reachable vs0 ctx fn inst s ==>
    vs0 = zs_vs ==> ctx = zs_ctx ==>
    ?G tn. frame_reachable zs_vs zs_ctx [] [] G tn fn inst s
Proof
  ho_match_mp_tac contextRawReachableTheory.raw_reachable_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt strip_tac >> gvs[] >>
      metis_tac[frame_reachable_entry])
  >- (rpt gen_tac >> strip_tac >> rpt strip_tac >> gvs[] >>
      drule zs_frame_trace >> simp[] >> strip_tac >> gvs[] >>
      drule zs_trace_opcode >> strip_tac >>
      metis_tac[frame_reachable_next])
  >- (rpt gen_tac >> strip_tac >> rpt strip_tac >> gvs[] >>
      metis_tac[frame_reachable_block])
  >> rpt gen_tac >> strip_tac >> rpt strip_tac >> gvs[] >>
  drule zs_frame_trace >> simp[] >> strip_tac >> gvs[] >>
  drule zs_trace_opcode >> gvs[]
QED

Theorem zs_trace_mem:
  !n. n < 5 ==>
    raw_mem_ok zs_ctx zs_fn (EL n (fn_insts zs_fn)) (SND (SND (zs_trace n))) /\
    dload_offset_ok zs_ctx zs_fn (EL n (fn_insts zs_fn)) (SND (SND (zs_trace n))) /\
    dload_headroom_ok zs_ctx zs_fn (EL n (fn_insts zs_fn)) (SND (SND (zs_trace n)))
Proof
  gen_tac >> disch_tac >>
  `n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4` by decide_tac >>
  gvs[] >> EVAL_TAC >>
  `dimindex (:256) = 256` by CONV_TAC fcpLib.INDEX_CONV >>
  simp[wordsTheory.dimword_def, venomStateTheory.eval_operand_def]
QED

Theorem zs_mem_invs:
  mem_inv raw_mem_ok zs_ctx zs_vs /\
  mem_inv dload_offset_ok zs_ctx zs_vs /\
  mem_inv dload_headroom_ok zs_ctx zs_vs
Proof
  simp[unitMemInvTheory.mem_inv_raw_reachable] >>
  `?name fn lbl. zs_ctx.ctx_entry = SOME name /\
     lookup_function name zs_ctx.ctx_functions = SOME fn /\
     fn_entry_label fn = SOME lbl` by
    (qexistsl_tac [`"main"`, `zs_fn`, `"main"`] >>
     simp[zs_ctx_def, venomInstTheory.mk_venom_context_def, zs_entry_facts]) >>
  simp[] >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
  drule zs_raw_frame >> simp[] >> strip_tac >>
  drule zs_frame_trace >> simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum `(G,tn,s) = _` (assume_tac o SYM) >>
  drule zs_trace_mem >> simp[]
QED

Theorem zs_src_inv:
  o1_src_inv
    <|d_stor := (\a st. UNIV); d_trans := (\a st. UNIV);
      d_imm := (\im. UNIV); d_ret := (\r. UNIV)|> zs_ctx zs_vs
Proof
  simp[o1_src_inv_def, zs_static_premises, zs_mem_invs,
       all_dead_taint_within] >>
  qexists_tac `0` >> simp[zs_static_premises, zs_ptr_discipline]
QED

Definition zt_trace_def:
  (zt_trace 0 = (FEMPTY, entry_taint, zs_vs)) /\
  (zt_trace (SUC n) =
    let (G,tn,s) = zt_trace n in
    let inst = EL n (fn_insts zs_out.fpo_function) in
    let s' = case step_inst 0 zs_target inst s of OK t => t | _ => s in
    (step_prov [] G inst s', step_taint inst s s' tn,
     s' with vs_inst_idx := SUC n))
End

Theorem zt_entry_facts:
  zs_target.ctx_entry = SOME "main" /\
  lookup_function "main" zs_target.ctx_functions = SOME zs_out.fpo_function /\
  fn_entry_label zs_out.fpo_function = SOME "main" /\
  enters_block zs_out.fpo_function
    (zs_vs with <|vs_prev_bb := NONE; vs_current_bb := "main";
                 vs_inst_idx := 0|>) zs_vs /\
  active_inst zs_out.fpo_function (EL 0 (fn_insts zs_out.fpo_function)) zs_vs
Proof
  EVAL_TAC >> simp[venomExecSemanticsTheory.eval_phis_def,
    venomExecSemanticsTheory.phi_prefix_length_def]
QED

Theorem zt_step_facts:
  !n. n < 6 ==>
    let (G,tn,s) = zt_trace n in
    let inst = EL n (fn_insts zs_out.fpo_function) in
    ?s'. s.vs_inst_idx = n /\ active_inst zs_out.fpo_function inst s /\
         ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
         step_inst 0 zs_target inst s = OK s' /\
         active_inst zs_out.fpo_function
           (EL (SUC n) (fn_insts zs_out.fpo_function))
           (s' with vs_inst_idx := SUC n)
Proof
  gen_tac >> disch_tac >>
  `n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5` by decide_tac >>
  gvs[] >> EVAL_TAC >> simp[]
QED

Theorem zt_reachable:
  !n. n <= 6 ==>
    frame_reachable zs_vs zs_target [] [] (FST (zt_trace n))
      (FST (SND (zt_trace n))) zs_out.fpo_function
      (EL n (fn_insts zs_out.fpo_function)) (SND (SND (zt_trace n)))
Proof
  Induct
  >- (simp[zt_trace_def] >>
      mp_tac zt_entry_facts >> simp[] >>
      metis_tac[frame_reachable_entry]) >>
  strip_tac >> `n < 6` by decide_tac >>
  `n <= 6` by decide_tac >> first_x_assum drule >> strip_tac >>
  drule zt_step_facts >>
  Cases_on `zt_trace n` >> Cases_on `r` >> fs[] >> strip_tac >>
  simp[zt_trace_def] >> metis_tac[frame_reachable_next]
QED

Theorem zt_bad_eq:
  ~access_ok 0 (FST (zt_trace 6)) zs_out.fpo_function
    (EL 6 (fn_insts zs_out.fpo_function)) (SND (SND (zt_trace 6)))
Proof
  EVAL_TAC >>
  `dimindex (:256) = 256` by CONV_TAC fcpLib.INDEX_CONV >>
  simp[finite_mapTheory.FLOOKUP_UPDATE, wordsTheory.dimword_def]
QED

Theorem zt_not_ptr_discipline:
  ~ptr_discipline 0 zs_target zs_vs
Proof
  simp[ptr_discipline_def] >> rpt strip_tac >>
  mp_tac (Q.SPEC `6` zt_reachable) >> simp[] >> strip_tac >>
  disj2_tac >> goal_assum (drule_at Any) >> simp[zt_bad_eq]
QED

Theorem lower_dload_stage_ptr_counterexample:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload)
    (\C fn observed. T) zs_ctx zs_target /\
  dead_wf <|d_stor := (\a st. UNIV); d_trans := (\a st. UNIV);
            d_imm := (\im. UNIV); d_ret := (\r. UNIV)|> /\
  o1_ctx_shape zs_ctx /\ o1_run_state_ok zs_vs /\
  o1_src_inv <|d_stor := (\a st. UNIV); d_trans := (\a st. UNIV);
               d_imm := (\im. UNIV); d_ret := (\r. UNIV)|> zs_ctx zs_vs /\
  callee_first ["main"] zs_ctx.ctx_functions /\
  fixed_region_reserved 0 zs_ctx /\ ptr_discipline 0 zs_ctx zs_vs /\
  ~ptr_discipline 0 zs_target zs_vs
Proof
  simp[zs_stage, all_dead_wf, zs_shape, zs_state_ok, zs_src_inv,
       zs_static_premises, zs_ptr_discipline, zt_not_ptr_discipline]
QED
