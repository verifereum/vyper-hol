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
