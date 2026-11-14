Theory bodyFullBopWordSuffix
Ancestors
  bodyFullBopWordSuccess bodyFullBopWordAbort bodyFullGhostFrame
  bodyPtrBopTypedSource bodyPtrBopScalarRun bodyPtrBopScalarDispatch
  bodySimFull gasOutcomeFullCompose exprBopSimProps exprSimSource
  wordArgsPtr ptrDiscipline bodyPtrDefs loweringPosts exprSimWordArgs

Theorem bop_word_suffix_inputs[local]:
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  ptr_val_ok cx (expr_type e1) v1 x G1 tn1 t /\
  ptr_val_ok cx (expr_type e2) v2 y G2 tn2 u /\
  is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
  ghost_kept_at lo cenv mid s1 G1 tn1 t G2 tn2 /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) ==>
  op_prov G2 x = NONE /\ op_taint tn2 x = {} /\
  op_prov G2 y = NONE /\ op_taint tn2 y = {}
Proof
  strip_tac >>
  `op_prov G2 x = op_prov G1 x /\ op_taint tn2 x = op_taint tn1 x` by
    (Cases_on `x` >> gvs[op_prov_def, op_taint_def, ghost_kept_at_def]) >>
  gvs[ptr_val_ok_def]
QED

(* The raw joint scalar path fixes ghosts and the endpoint before H.
   Its continuation is responsible for the original expression's post. *)
Theorem bop_word_suffix_joint_outcome[local]:
  bop <> In /\ bop <> NotIn /\ well_typed_binop ann bop t1 t2 /\
  compile_binop bop x y ty bl el sa = (op,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\
  op_prov G y = NONE /\ op_taint tn y = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ allocas_from lo s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  storage_trace_domain cx st0 es.storage_trace /\
  ((?v t. bop_result cx ann bop tys v1 v2 es = INL v /\ word_value v /\
      run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand op t = SOME (val_to_w256 v)) \/
   (?m t. bop_result cx ann bop tys v1 v2 es = INR (Error (RuntimeError m)) /\
      run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)) /\
  (!H v t G' tn'. valid_horizon cx st0 H es.storage_trace /\
      bop_result cx ann bop tys v1 v2 es = INL v /\ word_value v /\
      run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand op t = SOME (val_to_w256 v) /\
      op_prov G' op = NONE /\ op_taint tn' op = {} /\
      tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
      tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
      (!z. not_fresh_at sa z ==> FLOOKUP G' z = FLOOKUP G z /\
          FLOOKUP tn'.t_var z = FLOOKUP tn.t_var z) ==>
      Q H (INL v) (es with gas_obs := []) G' tn'
        (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (\ee. (bop_result cx ann bop tys v1 v2 ee, ee)) (es,s,G,tn) Q
    (\H res ee gt r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?B. bop_scalar_seq {z | not_fresh_at sa z}
      ({x;y} UNION IMAGE Lit UNIV) (emitted_insts sa sb) B /\ op IN B` by
    (irule bop_scalar_binop_certificate >> simp[] >>
     goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
     metis_tac[]) >>
  `!a. a IN ({x;y} UNION IMAGE Lit UNIV) ==>
    op_prov G a = NONE /\ op_taint tn a = {}` by
    metis_tac[bop_scalar_binop_input_clean] >>
  qpat_x_assum `(?v t. _) \/ _` strip_assume_tac
  >- suspend "success" >> suspend "abort"
QED

Resume bop_word_suffix_joint_outcome[success]:
  drule_all bop_word_scalar_success_joint >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  irule gas_outcome_full_intro >>
  qexistsl_tac [`G'`, `es`, `[]`,
    `OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))`,
    `INL v`, `tn'`] >>
  simp[] >> rpt strip_tac >>
  qpat_x_assum `!H v t G' tn'. _` (qspecl_then [`H`, `v`, `t`, `G'`, `tn'`] mp_tac) >>
  simp[]
QED

Resume bop_word_suffix_joint_outcome[abort]:
  drule_all bop_word_scalar_abort_joint >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  irule gas_outcome_full_intro >>
  qexistsl_tac [`G'`, `es`, `[]`,
    `Abort Revert_abort (t with vs_inst_idx := j)`, `INR (Error (RuntimeError m))`, `tn'`] >>
  simp[exprSimDefsTheory.expr_exit_def, fragExecTheory.exit_result_def] >> metis_tac[]
QED
Finalise bop_word_suffix_joint_outcome
