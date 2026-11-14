(* Ordered mixed-target suffix, abstract over the successful head boundary.
   I sees gas-reset source states, exactly as recursive continuations do. *)
Theory tupleAssignImmutableDeploySuffix
Ancestors
  tuplePlaceSuffixOpen tuplePlaceSuffixCode tuplePlaceHeadOpen
  tuplePlaceHeadGas tuplePlaceSource tuplePlaceHead
  stmtSimForRounds tupleTargetStoreProps vyperInterpreter vyperState
  stmtLowering compileEnv loweringStateRelDefs fragGasMode fragGasPath exprSimHypsDefs
  vyperTypeDefaults list rich_list

Theorem tuple_mixed_suffix_from_heads:
  !ctx func cenv cx env gs tys ltys ltvs vs elems w lo I.
  LIST_REL (\g t. well_typed_atarget env g t) gs tys /\
  EVERY (\g. ?bt. g = BaseTarget bt) gs /\
  LENGTH ltys = LENGTH tys /\
  (!i es sp sa sb s0 bt r next Q.
    i < LENGTH tys /\ EL i gs = BaseTarget bt /\
    expr_sim_inv cenv cx env es /\ ~block_is_terminated sp /\
    tuple_place_head ctx func cenv cx es lo sp tys ltys ltvs vs elems w i s0 /\
    I i (es with gas_obs := []) sp s0 /\
    compile_get_target_ptr compile_expr cenv bt sp = (r,sa) /\
    (let dst = FST r; loc_opt = FST (SND r); dst_ty_opt = SND (SND r);
         loc = case loc_opt of SOME l => l | NONE => LocMemory;
         dty = case dst_ty_opt of SOME (ValPT t) => t | _ => EL i ltys
     in (if is_word_type (EL i ltys) then
           if is_word_type dty then
             compile_store_at_loc cenv.ce_imm_alloca dst (EL i elems) loc_opt
           else emit_void INVALID []
         else compile_assign_value cenv dst loc (EL i elems) (is_word_type dty)
           NONE dty (EL i ltys) (type_memory_bytes cenv dty)) sa) = ((),sb) /\
    fn_has_code sp sa func /\ fn_has_code sa sb func /\
    sp.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sb.cs_next_var /\
    (!ff t. ~block_is_terminated sb /\ expr_sim_inv cenv cx env ff /\
      tuple_place_head ctx func cenv cx ff lo sb tys ltys ltvs vs elems w (SUC i) t /\
      I (SUC i) (ff with gas_obs := []) sb t /\
      (!x v. not_fresh_at sp x /\ lookup_var x s0 = SOME v ==> lookup_var x t = SOME v) /\
      (!id entry. FLOOKUP s0.vs_allocas id = SOME entry ==>
        FLOOKUP t.vs_allocas id = SOME entry) /\
      alloca_frame cenv es sp s0 cenv ff t ==>
      gas_outcome F (cx_tops cx) (ctx,func) next (ff with gas_obs := [],t)
        (\(res : unit + exception) ee u. Q res ee u)
        (\res ee r. expr_exit res r)) ==>
    gas_outcome F (cx_tops cx) (ctx,func)
      (bind (eval_target_place cx bt)
        (\p. ignore_bind (write_place cx p (EL i vs)) next)) (es,s0) Q
      (\res ee r. expr_exit res r)) ==>
  !i es sp sf s0.
    i <= LENGTH tys /\ expr_sim_inv cenv cx env es /\ ~block_is_terminated sp /\
    tuple_place_head ctx func cenv cx es lo sp tys ltys ltvs vs elems w i s0 /\
    I i (es with gas_obs := []) sp s0 /\
    compile_tuple_store_all cenv (DROP i ltys) (DROP i gs) (DROP i elems) sp = ((),sf) /\
    fn_has_code sp sf func ==>
    gas_outcome F (cx_tops cx) (ctx,func)
      (assign_tuple_target_list cx (DROP i gs) (DROP i vs)) (es,s0)
      (\res ff t. res = INL () /\ expr_sim_inv cenv cx env ff /\ ~block_is_terminated sf /\
        tuple_place_head ctx func cenv cx ff lo sf tys ltys ltvs vs elems w (LENGTH tys) t /\
        I (LENGTH tys) (ff with gas_obs := []) sf t /\
        (!x v. not_fresh_at sp x /\ lookup_var x s0 = SOME v ==> lookup_var x t = SOME v) /\
        (!id entry. FLOOKUP s0.vs_allocas id = SOME entry ==>
          FLOOKUP t.vs_allocas id = SOME entry) /\
        alloca_frame cenv es sp s0 cenv ff t)
      (\res ff r. expr_exit res r)
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH gs = LENGTH tys` by fs[LIST_REL_EL_EQN] >>
  gen_tac >> measureInduct_on `LENGTH tys - i` >>
  rpt gen_tac >> strip_tac >>
  `LENGTH elems = LENGTH tys /\ LENGTH vs = LENGTH tys` by
    fs[tuple_place_head_def, values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
  Cases_on `i = LENGTH tys`
  >- (gvs[] >>
      `DROP (LENGTH tys) ltys = [] /\ DROP (LENGTH tys) gs = [] /\
       DROP (LENGTH tys) elems = [] /\ DROP (LENGTH tys) vs = []` by simp[] >>
      fs[DROP_LENGTH_TOO_LONG, Once compile_tuple_store_all_def,
         compileEnvTheory.comp_return_def] >>
      simp[DROP_LENGTH_TOO_LONG, Once evaluate_def] >>
      irule gas_outcome_return_path >>
      qexists `s0` >> simp[] >>
      conj_tac >- (irule stmtSimDefsTheory.alloca_frame_same >> simp[]) >>
      fs[tuple_place_head_def, gas_marked_path_def] >>
      metis_tac[gas_path_rules]) >>
  `i < LENGTH tys` by decide_tac >>
  `?bt. EL i gs = BaseTarget bt` by fs[EVERY_EL] >>
  drule_all tuple_place_suffix_code_parts >> strip_tac >>
  `DROP i gs = BaseTarget bt :: DROP (SUC i) gs` by simp[DROP_CONS_EL] >>
  `DROP i vs = EL i vs :: DROP (SUC i) vs` by simp[DROP_CONS_EL] >>
  asm_rewrite_tac[Once evaluate_def] >>
  simp[Once evaluate_def, ignore_bind_def, bind_assoc] >>
  qpat_x_assum `!i es sp sa sb s0 bt r next Q. _`
    (irule o SRULE [ignore_bind_def]) >>
  simp[] >> qexistsl [`r`,`sa`,`sb`,`sp`] >> simp[] >>
  reverse conj_tac >- fs[LET_THM] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!y. _ ==> _` (qspec_then `SUC i` mp_tac) >>
  simp[] >>
  disch_then (qspecl_then [`ff with gas_obs := []`,`sb`,`sf`,`t`] mp_tac) >>
  `tuple_place_head ctx func cenv cx (ff with gas_obs := []) lo sb
    tys ltys ltvs vs elems w (SUC i) t` by
    (qpat_x_assum `tuple_place_head _ _ _ _ ff _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[tuple_place_head_def, tuplePlacePrefixCertTheory.tuple_place_snapshot_def,
          exprSimWordArgsTheory.stmt_state_rel_gas_obs]) >>
  simp[] >> disch_tac >>
  irule exprSimMemDefsTheory.gas_outcome_post_mono >>
  goal_assum (drule_at Any) >>
  rpt gen_tac >> BETA_TAC >> strip_tac >> simp[] >>
  reverse conj_tac
  >- (irule stmtSimDefsTheory.alloca_frame_trans >>
      qexistsl [`cenv`, `ff`, `t`, `sb`] >>
      simp[stmtSimDefsTheory.alloca_frame_gas_obs] >> decide_tac) >>
  rpt gen_tac >> strip_tac >>
  `not_fresh_at sb x` by
    (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  metis_tac[]
QED
