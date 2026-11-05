Theory bodyPtrBopHashCompare
Ancestors
  bodyPtrBopCompareSuffix bodyPtrBopHashSuffix bodyPtrBopCompareCompile
  fragGasPathPtr compileEnv codegenRel exprLoweringProps venomState
  arithmetic exprSimDefs bodyPtrDefs emitHelperProps

Theorem bop_hash_compare_ptr:
  compile_bytestring_hash (Var p) sc = (h1,sd) /\
  compile_bytestring_hash (Var r) sd = (h2,se) /\
  (bop = Eq \/ bop = NotEq) /\
  compile_compare bop h1 h2 ty se = (op,sf) /\
  not_fresh_at sc p /\ not_fresh_at sc r /\ local_ptrs_reserved cenv sc /\
  fn_has_code sc sf fn /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx ty1 sa1 sb1 es v1 (Var p) s /\
  expr_val_at cenv cx ty2 sa2 sb2 es v2 (Var r) s /\
  ptr_val_ok cx ty1 v1 (Var p) G tn s /\
  ptr_val_ok cx ty2 v2 (Var r) G tn s /\
  evaluate_type (get_tenv cx) ty1 = SOME tv1 /\ ~is_word_type ty1 /\
  evaluate_type (get_tenv cx) ty2 = SOME tv2 /\ ~is_word_type ty2 /\
  lookup_var p s = SOME w1 /\ lookup_var r s = SOME w2 /\
  ((?bs. v1 = BytesV bs /\ LENGTH bs < dimword(:256) /\
      tv1 <> BaseTV AddressT /\ (!k. tv1 <> BaseTV (BytesT (Fixed k)))) \/
   (?str. v1 = StringV str /\ LENGTH str < dimword(:256))) /\
  ((?bs. v2 = BytesV bs /\ LENGTH bs < dimword(:256) /\
      tv2 <> BaseTV AddressT /\ (!k. tv2 <> BaseTV (BytesT (Fixed k)))) \/
   (?str. v2 = StringV str /\ LENGTH str < dimword(:256))) /\
  run_inst_seq (emitted_insts sc sf) s = OK t ==>
  ?G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := LENGTH sf.cs_current_insts)) /\
    op_prov G' op = NONE /\ op_taint tn' op = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    (!x. not_fresh_at sc x ==>
      FLOOKUP G' x = FLOOKUP G x /\ FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  imp_res_tac bop_hash_compile_layout >>
  `inst_extends sc se /\ cs_extends sc se` by
    metis_tac[inst_extends_trans, cs_extends_trans] >>
  drule_all bop_compare_suffix_run_split >> strip_tac >>
  drule_all bop_hash_pair_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule_all bop_hash_pair_readonly >> strip_tac >>
  `u.vs_current_bb = se.cs_current_bb /\ ~u.vs_halted` by
    (qpat_x_assum `(u with vs_vars := _) = s` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  drule_all (GEN_ALL (SIMP_RULE (srw_ss()) []
    (Q.INST [`s` |-> `v with vs_inst_idx := LENGTH se.cs_current_insts`,
             `t` |-> `w with vs_inst_idx := LENGTH se.cs_current_insts`,
             `sc` |-> `se`, `sd` |-> `sf`]
      (SPEC_ALL bop_compile_compare_ptr)))) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `!x. not_fresh_at sc x ==> not_fresh_at se x` by fs[not_fresh_at_def] >>
  qexistsl_tac [`G''`, `tn''`] >> simp[] >>
  irule (SIMP_RULE (srw_ss()) []
    (Q.INST [`n` |-> `0`, `m` |-> `0`] (SPEC_ALL gas_path_ptr_then))) >>
  qexistsl_tac [`G'`, `u with vs_inst_idx := LENGTH se.cs_current_insts`, `tn'`] >>
  gvs[ADD_ASSOC]
QED
