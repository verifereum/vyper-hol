Theory bodyMembershipArrayIndexLoadMods
Ancestors
  bodyFullBopRestWordLoads bodyFullBopRestWordCtor bodyPtrBopInLoopContract
  bodyPtrBopInElementLoad fragGasOriginPtrLoop builtinProps
  context compileEnv venomState ptrDiscipline finite_map words

(* Bound choice shifts the fresh address name, but not the executed prefix length. *)
Theorem membership_index_address[local]:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm loc) bound is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!x. arr = Var x ==> not_fresh_at sa x) /\
  delta = (if 0 < skip then 1 else 0) /\
  q = (if IS_SOME bound then 2 else 0) /\
  src = "%" ++ toString (sa.cs_next_var+4+q+delta) /\
  addr = bw+n2w (skip+stride*i) /\
  (!H. guard H ==>
    membership_loop_frame sa G0 T0 s0 Gs Ts s /\
    membership_loop_registers sa i 0w Gs Ts s /\
    ~s.vs_halted /\ allocas_from lo s /\
    s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
    s.vs_inst_idx = 0 /\ eval_operand arr s0 = SOME bw /\ op_taint T0 arr = {}) ==>
  ?p Gp Tp. !H. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,Gs,Ts) [] (OK p,Gp,Tp) /\
    membership_loop_frame sa G0 T0 s0 Gp Tp p /\
    membership_loop_registers sa i 0w Gp Tp p /\
    ~p.vs_halted /\ allocas_from lo p /\
    p.vs_current_bb = s.vs_current_bb /\ p.vs_inst_idx = 2+delta /\
    lookup_var src p = SOME addr /\
    FLOOKUP Gp src = op_prov G0 arr /\ op_taint Tp (Var src) = {}
Proof
  strip_tac >> Cases_on `bound` >>
  FULL_SIMP_TAC std_ss [optionTheory.IS_SOME_DEF, arithmeticTheory.ADD_0] >>
  rpt BasicProvers.VAR_EQ_TAC
  >- (irule rest_word_membership_runtime_address_operand_joint_const >>
      simp[] >> conj_tac
      >- (gen_tac >> disch_tac >> first_x_assum drule >> simp[]) >>
      metis_tac[]) >>
  irule rest_word_membership_runtime_address_operand_joint_bounded_const >>
  simp[] >> conj_tac
  >- (gen_tac >> disch_tac >> first_x_assum drule >> simp[]) >>
  metis_tac[]
QED

Theorem membership_index_raw_load[local]:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm loc) bound is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ (ctx_has_dalloca ctx ==> allocas_below_fmp p) /\
  loc <> LocCalldata /\
  delta = (if 0 < skip then 1 else 0) /\
  q = (if IS_SOME bound then 2 else 0) /\
  src = "%" ++ toString (sa.cs_next_var+4+q+delta) /\
  dst = "%" ++ toString (sa.cs_next_var+5+q+delta) /\
  (loc = LocMemory ==> w2n addr + 32 <= p.vs_alloca_next) /\
  (loc = LocCode ==> w2n addr <= LENGTH p.vs_data_section) /\
  (!H. guard H ==>
    membership_loop_frame sa G0 T0 s0 Gp Tp p /\
    membership_loop_registers sa i 0w Gp Tp p /\
    ~p.vs_halted /\ allocas_from lo p /\
    p.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
    p.vs_inst_idx = 2+delta /\ lookup_var src p = SOME addr /\
    op_taint Tp (Var src) = {} /\
    (loc = LocMemory ==> ptr_covers Gp Tp src p 32 /\ mem_word_taint Tp.t_mem (w2n addr) = {}) /\
    (loc = LocStorage ==> key_taint Tp.t_stor addr = {}) /\
    (loc = LocTransient ==> key_taint Tp.t_trans addr = {})) ==>
  ?t Gt Tt. !H. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (p,Gp,Tp) [] (OK t,Gt,Tt) /\
    membership_loop_frame sa G0 T0 s0 Gt Tt t /\
    membership_loop_registers sa i 0w Gt Tt t /\
    ~t.vs_halted /\ allocas_from lo t /\
    t.vs_current_bb = p.vs_current_bb /\ t.vs_inst_idx = 3+delta /\
    lookup_var dst t = SOME (ptr_load_val F loc addr p) /\
    FLOOKUP Gt dst = NONE /\ op_taint Tt (Var dst) = {}
Proof
  strip_tac >>
  Cases_on `bound` >> Cases_on `loc` >>
  FULL_SIMP_TAC std_ss [optionTheory.IS_SOME_DEF, data_location_distinct,
    arithmeticTheory.ADD_0, ptr_load_val_def, LET_THM] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  FULL_SIMP_TAC std_ss [arithmeticTheory.ADD_0]
  >- (irule rest_word_membership_memory_read_joint_const >>
      simp[] >> conj_tac >- (gen_tac >> disch_tac >> first_x_assum drule >> simp[]) >> metis_tac[])
  >- (irule (Q.INST [`tr` |-> `F`] rest_word_membership_slot_read_joint_const
             |> PURE_REWRITE_RULE [COND_CLAUSES]) >>
      simp[] >> conj_tac >- (gen_tac >> disch_tac >> first_x_assum drule >> simp[]) >> metis_tac[])
  >- (irule (Q.INST [`tr` |-> `T`] rest_word_membership_slot_read_joint_const
             |> PURE_REWRITE_RULE [COND_CLAUSES]) >>
      simp[] >> conj_tac >- (gen_tac >> disch_tac >> first_x_assum drule >> simp[]) >> metis_tac[])
  >- (irule rest_word_membership_code_read_joint_const >> simp[] >> conj_tac
      >- (qexists_tac `addr` >> simp[] >> gen_tac >> disch_tac >> first_x_assum drule >> simp[]) >>
      metis_tac[])
  >- (irule rest_word_membership_memory_read_joint_bounded_const >>
      simp[] >> conj_tac >- (gen_tac >> disch_tac >> first_x_assum drule >> simp[]) >> metis_tac[])
  >- (irule (Q.INST [`tr` |-> `F`] rest_word_membership_slot_read_joint_bounded_const
             |> PURE_REWRITE_RULE [COND_CLAUSES]) >>
      simp[] >> conj_tac >- (gen_tac >> disch_tac >> first_x_assum drule >> simp[]) >> metis_tac[])
  >- (irule (Q.INST [`tr` |-> `T`] rest_word_membership_slot_read_joint_bounded_const
             |> PURE_REWRITE_RULE [COND_CLAUSES]) >>
      simp[] >> conj_tac >- (gen_tac >> disch_tac >> first_x_assum drule >> simp[]) >> metis_tac[]) >>
  irule rest_word_membership_code_read_joint_bounded_const >> simp[] >> conj_tac
  >- (qexists_tac `addr` >> simp[] >> gen_tac >> disch_tac >> first_x_assum drule >> simp[]) >>
  metis_tac[]
QED

Theorem membership_index_read_frame[local]:
  membership_loop_frame sa G0 T0 s0 Gp Tp p ==>
  p.vs_alloca_next = s0.vs_alloca_next /\ p.vs_data_section = s0.vs_data_section /\
  Tp.t_mem = T0.t_mem /\ Tp.t_stor = T0.t_stor /\ Tp.t_trans = T0.t_trans /\
  ptr_load_val F loc addr p = ptr_load_val F loc addr s0
Proof
  simp[membership_loop_frame_def] >> strip_tac >>
  qpat_x_assum `p = _` (fn th => once_rewrite_tac[th]) >>
  Cases_on `loc` >> simp[ptr_load_val_def, mload_def, sload_def, tload_def,
    contract_storage_def, contract_transient_def]
QED

Theorem membership_index_nonctor_load[local]:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm loc) bound is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!x. arr = Var x ==> not_fresh_at sa x) /\ loc <> LocCalldata /\
  eval_operand arr s0 = SOME bw /\ op_taint T0 arr = {} /\
  addr = bw+n2w (skip+stride*i) /\ value = ptr_load_val F loc addr s0 /\
  delta = (if 0 < skip then 1 else 0) /\ q = (if IS_SOME bound then 2 else 0) /\
  src = "%" ++ toString (sa.cs_next_var+4+q+delta) /\
  dst = "%" ++ toString (sa.cs_next_var+5+q+delta) /\
  (loc = LocMemory ==>
    w2n addr + 32 <= s0.vs_alloca_next /\ mem_word_taint T0.t_mem (w2n addr) = {} /\
    !x p Gp Tp. membership_loop_frame sa G0 T0 s0 Gp Tp p /\
      lookup_var x p = SOME addr /\ FLOOKUP Gp x = op_prov G0 arr /\
      op_taint Tp (Var x) = {} ==> ptr_covers Gp Tp x p 32) /\
  (loc = LocStorage ==> key_taint T0.t_stor addr = {}) /\
  (loc = LocTransient ==> key_taint T0.t_trans addr = {}) /\
  (loc = LocCode ==> w2n addr <= LENGTH s0.vs_data_section) /\
  (!H. guard H ==>
    membership_loop_frame sa G0 T0 s0 Gs Ts s /\
    membership_loop_registers sa i 0w Gs Ts s /\
    ~s.vs_halted /\ allocas_from lo s /\
    s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
    s.vs_inst_idx = 0) ==>
  ?t Gt Tt. !H. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,Gs,Ts) [] (OK t,Gt,Tt) /\
    membership_loop_frame sa G0 T0 s0 Gt Tt t /\
    membership_loop_registers sa i 0w Gt Tt t /\
    ~t.vs_halted /\ allocas_from lo t /\
    t.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\ t.vs_inst_idx = 2+delta+1 /\
    eval_operand (Var dst) t = SOME value /\
    op_prov Gt (Var dst) = NONE /\ op_taint Tt (Var dst) = {}
Proof
  strip_tac >> Cases_on `?H. guard H`
  >- suspend "has_horizon" >>
  qexistsl_tac [`s`,`Gs`,`Ts`] >> gvs[]
QED

Resume membership_index_nonctor_load[has_horizon]:
  qpat_x_assum `?H. guard H` strip_assume_tac >>
  `membership_loop_frame sa G0 T0 s0 Gs Ts s` by
    (qpat_assum `!H. guard H ==> membership_loop_frame _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (drule membership_loop_frame_allocas_below_fmp >> simp[]) >>
  `?p Gp Tp. !H. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,Gs,Ts) [] (OK p,Gp,Tp) /\
    membership_loop_frame sa G0 T0 s0 Gp Tp p /\
    membership_loop_registers sa i 0w Gp Tp p /\
    ~p.vs_halted /\ allocas_from lo p /\
    p.vs_current_bb = s.vs_current_bb /\ p.vs_inst_idx = 2+delta /\
    lookup_var src p = SOME addr /\
    FLOOKUP Gp src = op_prov G0 arr /\ op_taint Tp (Var src) = {}` by
    (irule membership_index_address >> simp[] >>
     qpat_assum `compile_array_membership_loop _ _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
     qexists_tac `bw` >> simp[] >>
     gen_tac >> disch_tac >> first_x_assum drule >> simp[]) >>
  qpat_assum `!H. guard H ==> gas_origin_ptr_path _ (s,_,_) _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp p` by
    (drule membership_loop_frame_allocas_below_fmp >> simp[]) >>
  qpat_assum `membership_loop_frame _ _ _ _ _ _ p` (mp_then Any mp_tac membership_index_read_frame) >>
  disch_then (qspecl_then [`loc`,`addr`] strip_assume_tac) >>
  `?t gout tout. !H. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (p,Gp,Tp) [] (OK t,gout,tout) /\
    membership_loop_frame sa G0 T0 s0 gout tout t /\
    membership_loop_registers sa i 0w gout tout t /\
    ~t.vs_halted /\ allocas_from lo t /\
    t.vs_current_bb = p.vs_current_bb /\ t.vs_inst_idx = 3+delta /\
    lookup_var dst t = SOME (ptr_load_val F loc addr p) /\
    FLOOKUP gout dst = NONE /\ op_taint tout (Var dst) = {}` by suspend "read" >>
  qexistsl_tac [`t`,`gout`,`tout`] >> gen_tac >> disch_tac >>
  qpat_assum `!H. guard H ==> gas_origin_ptr_path _ (p,_,_) _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. guard H ==> gas_origin_ptr_path _ (s,_,_) _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. guard H ==> membership_loop_frame _ _ _ _ _ _ s /\ _`
    (drule_then strip_assume_tac) >>
  simp[eval_operand_def, op_prov_def] >>
  irule gas_origin_ptr_path_trans >> goal_assum (drule_at Any) >> simp[]
QED

Resume membership_index_nonctor_load[read]:
  irule membership_index_raw_load >> simp[] >> conj_tac
  >- (strip_tac >> gvs[]) >>
  conj_tac >- (strip_tac >> gvs[]) >>
  qpat_assum `compile_array_membership_loop _ _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
  simp[] >> gen_tac >> disch_tac >>
  qpat_assum `!H. guard H ==> membership_loop_frame _ _ _ _ _ _ s /\ _`
    (drule_then strip_assume_tac) >>
  gvs[] >> strip_tac >> gvs[] >>
  qpat_assum `!x p Gp Tp. _ ==> ptr_covers _ _ _ _ _` irule >> simp[]
QED
Finalise membership_index_nonctor_load

(* The loop entry is s0 (the header landing for a dynamic array); s is the
   reached iteration body, not a recompilation or replay of the array child. *)
Theorem membership_array_index_load_mods:
  compile_array_membership_loop needle (vv_operand vv) len
    (elem_size_in_location cenv loc ety) skip
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc) bound is_in sa = (op,sb) /\
  loc = (case vv_location vv of NONE => LocMemory | SOME l => l) /\
  skip = (if IS_SOME bound then word_scale loc else 0) /\
  fn_has_code sa sb fn /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\ loc <> LocCalldata /\
  (!H. guard H ==> eval_operand (vv_operand vv) s0 = SOME bw /\ op_taint T0 (vv_operand vv) = {}) /\
  (!H i. guard H /\ i < LENGTH ws ==>
    let addr = bw+n2w (skip+elem_size_in_location cenv loc ety*i) in
    ptr_load_val cenv.ce_is_ctor loc addr s0 = EL i ws /\
    (loc = LocMemory ==>
      w2n addr + 32 <= s0.vs_alloca_next /\ mem_word_taint T0.t_mem (w2n addr) = {} /\
      !x p Gp Tp. membership_loop_frame sa G0 T0 s0 Gp Tp p /\
        lookup_var x p = SOME addr /\ FLOOKUP Gp x = op_prov G0 (vv_operand vv) /\
        op_taint Tp (Var x) = {} ==> ptr_covers Gp Tp x p 32) /\
    (loc = LocStorage ==> key_taint T0.t_stor addr = {}) /\
    (loc = LocTransient ==> key_taint T0.t_trans addr = {}) /\
    (loc = LocCode /\ ~cenv.ce_is_ctor ==> w2n addr <= LENGTH s0.vs_data_section) /\
    (loc = LocCode /\ cenv.ce_is_ctor ==>
      w2n addr + 32 <= lo /\ mem_word_taint T0.t_mem (w2n addr) = {})) /\
  (cenv.ce_is_ctor /\ loc = LocCode ==>
    (!ib x. cenv.ce_imm_alloca = SOME ib /\ ib = Var x ==> not_fresh_at sa x) /\
    !H. guard H ==> ~s0.vs_halted /\ allocas_from lo s0 /\ lo <= s0.vs_alloca_next /\
      op_prov G0 (vv_operand vv) = NONE /\
      !ib. cenv.ce_imm_alloca = SOME ib ==> eval_operand ib s0 = SOME 0w /\
        op_prov G0 ib = NONE /\ op_taint T0 ib = {}) ==>
  !i s Gs Ts. i < LENGTH ws /\
    (!H. guard H ==>
      membership_loop_frame sa G0 T0 s0 Gs Ts s /\
      membership_loop_registers sa i 0w Gs Ts s /\
      ~s.vs_halted /\ allocas_from lo s /\
      s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
      s.vs_inst_idx = 0) ==>
    ?t Gt Tt. !H. guard H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,Gs,Ts) [] (OK t,Gt,Tt) /\
      membership_loop_frame sa G0 T0 s0 Gt Tt t /\
      membership_loop_registers sa i 0w Gt Tt t /\
      ~t.vs_halted /\ allocas_from lo t /\
      t.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
      t.vs_inst_idx = 2+(if 0 < skip then 1 else 0)+
        (if cenv.ce_is_ctor /\ loc = LocCode /\ IS_SOME cenv.ce_imm_alloca then 2 else 1) /\
      eval_operand (Var ("%" ++ toString (sa.cs_next_var+4+
        (if IS_SOME bound then 2 else 0)+(if 0 < skip then 1 else 0)+
        (if cenv.ce_is_ctor /\ loc = LocCode /\ IS_SOME cenv.ce_imm_alloca then 2 else 1)))) t = SOME (EL i ws) /\
      op_prov Gt (Var ("%" ++ toString (sa.cs_next_var+4+
        (if IS_SOME bound then 2 else 0)+(if 0 < skip then 1 else 0)+
        (if cenv.ce_is_ctor /\ loc = LocCode /\ IS_SOME cenv.ce_imm_alloca then 2 else 1)))) = NONE /\
      op_taint Tt (Var ("%" ++ toString (sa.cs_next_var+4+
        (if IS_SOME bound then 2 else 0)+(if 0 < skip then 1 else 0)+
        (if cenv.ce_is_ctor /\ loc = LocCode /\ IS_SOME cenv.ce_imm_alloca then 2 else 1)))) = {}
Proof
  disch_tac >> pop_assum (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `loc = (case _ of _ => _ | _ => _)` kall_tac >>
  qpat_x_assum `skip = _` kall_tac >>
  Cases_on `cenv.ce_is_ctor /\ loc = LocCode`
  >- suspend "constructor" >>
  suspend "runtime"
QED

Resume membership_array_index_load_mods[constructor]:
  qpat_x_assum `cenv.ce_is_ctor /\ loc = LocCode` strip_assume_tac >>
  qpat_x_assum `loc = LocCode` SUBST_ALL_TAC >>
  FULL_SIMP_TAC std_ss [data_location_distinct, LET_THM, ptr_load_val_def] >>
  rpt gen_tac >> strip_tac >>
  irule rest_word_membership_ctor_load_joint_const >> simp[] >> conj_tac
  >- first_assum ACCEPT_TAC >>
  qpat_assum `compile_array_membership_loop _ _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
  qexistsl_tac [`bw`,`\j. bw + n2w (skip + elem_size_in_location cenv LocCode ety * j)`] >>
  simp[] >> conj_tac >- (Cases_on `bound` >> simp[]) >>
  gen_tac >> disch_tac >>
  qpat_assum `!h. guard h ==> ~s0.vs_halted /\ _` (drule_then strip_assume_tac) >>
  qpat_assum `!h. guard h ==> eval_operand _ _ = _ /\ _` (drule_then strip_assume_tac) >>
  simp[] >> qx_gen_tac `j` >> disch_tac >>
  qpat_assum `!h j. guard h /\ j < LENGTH ws ==> _`
    (qspecl_then [`H`,`j`] mp_tac) >> simp[]
QED

Resume membership_array_index_load_mods[runtime]:
  `(if cenv.ce_is_ctor /\ loc = LocCode /\ IS_SOME cenv.ce_imm_alloca
    then 2 else 1:num) = 1` by
    (IF_CASES_TAC >> fs[]) >>
  `compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc =
   compile_ptr_load F cenv.ce_imm_alloca loc /\
   ptr_load_val cenv.ce_is_ctor loc = ptr_load_val F loc` by
    (qpat_x_assum `~(cenv.ce_is_ctor /\ loc = LocCode)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `loc` >>
     simp[FUN_EQ_THM, compile_ptr_load_def, ptr_load_val_def]) >>
  FULL_SIMP_TAC std_ss [LET_THM] >>
  rpt gen_tac >> strip_tac >> Cases_on `?H. guard H`
  >- (qpat_x_assum `?H. guard H` strip_assume_tac >>
      qpat_assum `!h. guard h ==> eval_operand _ _ = _ /\ _` (drule_then strip_assume_tac) >>
      qpat_assum `!h j. guard h /\ j < LENGTH ws ==> _`
        (qspecl_then [`H`,`i`] mp_tac) >> ASM_SIMP_TAC std_ss [] >> strip_tac >>
      irule membership_index_nonctor_load >> simp[] >> conj_tac
      >- first_assum ACCEPT_TAC >>
      qpat_assum `compile_array_membership_loop _ _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
      qexists_tac `bw` >> gvs[] >>
      strip_tac >> gvs[]) >>
  qexistsl_tac [`s`,`Gs`,`Ts`] >> gvs[]
QED
Finalise membership_array_index_load_mods
