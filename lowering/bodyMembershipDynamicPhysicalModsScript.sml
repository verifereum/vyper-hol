(* Execute the dynamic header once and use its reached state for the search. *)
Theory bodyMembershipDynamicPhysicalMods
Ancestors
  bodyMembershipArrayDynamicRunMods bodyMembershipArrayHeaderMods
  bodyMembershipHeaderReadFrameMods
  bodyMembershipArrayIndexLoadMods externalEntryShape
  bodyPtrBopInBoundedLayout fragFuelExprHelpers

Theorem membership_dynamic_physical_mods:
  loc = (case vv_location vv of NONE => LocMemory | SOME l => l) /\
  loc <> LocCalldata /\
  bd = Dynamic cap /\ LENGTH ws <= cap /\ cap < dimword (:256) /\
  compile_var_array_membership cenv needle vv (ArrayT ety bd) is_in sm = (out,ct) /\
  fn_has_code sm ct fn /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (!x. needle = Var x \/ vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!ib x. cenv.ce_imm_alloca = SOME ib /\ ib = Var x ==> not_fresh_at sm x) /\
  (?H. guard H) /\
  (!H. guard H ==> ~u.vs_halted /\ allocas_from lo u /\
    u.vs_current_bb = sm.cs_current_bb /\ u.vs_inst_idx = LENGTH sm.cs_current_insts /\
    eval_operand needle u = SOME needleword /\
    op_prov Gu needle = NONE /\ op_taint Tu needle = {}) /\
  lo <= u.vs_alloca_next /\
  eval_operand (vv_operand vv) u = SOME w /\ op_taint Tu (vv_operand vv) = {} /\
  (if cenv.ce_is_ctor /\ loc = LocCode then
     w2n w + 32 <= lo /\ mem_word_taint Tu.t_mem (w2n w) = {} /\
     mload (w2n w) u = n2w (LENGTH ws)
   else case loc of
     LocMemory => (?x. vv_operand vv = Var x /\ ptr_covers Gu Tu x u 32) /\
       w2n w + 32 <= u.vs_alloca_next /\ mem_word_taint Tu.t_mem (w2n w) = {} /\
       mload (w2n w) u = n2w (LENGTH ws)
   | LocStorage => key_taint Tu.t_stor w = {} /\ sload w u = n2w (LENGTH ws)
   | LocTransient => key_taint Tu.t_trans w = {} /\ tload w u = n2w (LENGTH ws)
   | LocCode => w2n w <= LENGTH u.vs_data_section /\
       word_of_bytes T (0w:bytes32)
         (TAKE 32 (DROP (w2n w) u.vs_data_section ++ REPLICATE 32 0w)) = n2w (LENGTH ws)
   | _ => F) /\
  (!i. i < LENGTH ws ==>
    let addr = w + n2w (word_scale loc + elem_size_in_location cenv loc ety * i) in
    ptr_load_val cenv.ce_is_ctor loc addr u = EL i ws /\
    (loc = LocMemory ==>
      w2n addr + 32 <= u.vs_alloca_next /\ mem_word_taint Tu.t_mem (w2n addr) = {} /\
      !x p Gp Tp. lookup_var x p = SOME addr /\ FLOOKUP Gp x = op_prov Gu (vv_operand vv) /\
        op_taint Tp (Var x) = {} ==> ptr_covers Gp Tp x p 32) /\
    (loc = LocStorage ==> key_taint Tu.t_stor addr = {}) /\
    (loc = LocTransient ==> key_taint Tu.t_trans addr = {}) /\
    (loc = LocCode /\ ~cenv.ce_is_ctor ==> w2n addr <= LENGTH u.vs_data_section) /\
    (loc = LocCode /\ cenv.ce_is_ctor ==>
      w2n addr + 32 <= lo /\ mem_word_taint Tu.t_mem (w2n addr) = {})) /\
  (cenv.ce_is_ctor /\ loc = LocCode ==>
    op_prov Gu (vv_operand vv) = NONE /\
    !ib. cenv.ce_imm_alloca = SOME ib ==>
      eval_operand ib u = SOME 0w /\ op_prov Gu ib = NONE /\ op_taint Tu ib = {}) ==>
  ?q Gt Tt. !H. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (u,Gu,Tu) [] (OK q,Gt,Tt) /\
    membership_loop_frame sm Gu Tu u Gt Tt q /\
    eval_operand out q = SOME
      (bool_to_word (if is_in then MEM needleword ws else ~MEM needleword ws)) /\
    op_prov Gt out = NONE /\ op_taint Tt out = {} /\
    ~q.vs_halted /\ allocas_from lo q /\
    q.vs_current_bb = ct.cs_current_bb /\
    q.vs_inst_idx = LENGTH ct.cs_current_insts
Proof
  disch_tac >> pop_assum (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `bd = Dynamic cap` SUBST_ALL_TAC >>
  `?len sl sh Gh Th.
    compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc (vv_operand vv) sm = (len,sl) /\
    compile_array_membership_loop needle (vv_operand vv) len
      (elem_size_in_location cenv loc ety) (word_scale loc)
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc) (SOME cap) is_in sl = (out,ct) /\
    (!H. guard H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (u,Gu,Tu) [] (OK sh,Gh,Th) /\
      membership_loop_frame sm Gu Tu u Gh Th sh /\
      eval_operand len sh = SOME (n2w (LENGTH ws)) /\
      op_prov Gh len = NONE /\ op_taint Th len = {} /\
      ~sh.vs_halted /\ allocas_from lo sh /\ sh.vs_current_bb = sl.cs_current_bb /\
      sh.vs_inst_idx = LENGTH sl.cs_current_insts /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp sh) /\
      eval_operand needle sh = eval_operand needle u /\
      op_prov Gh needle = op_prov Gu needle /\ op_taint Th needle = op_taint Tu needle /\
      eval_operand (vv_operand vv) sh = eval_operand (vv_operand vv) u /\
      op_prov Gh (vv_operand vv) = op_prov Gu (vv_operand vv) /\
      op_taint Th (vv_operand vv) = op_taint Tu (vv_operand vv))` by suspend "header" >>
  suspend "search"
QED

Resume membership_dynamic_physical_mods[header]:
  irule membership_array_header_mods >>
  conj_tac >-
    (qexists_tac `w` >> gen_tac >> disch_tac >>
     qpat_assum `!H. guard H ==> ~u.vs_halted /\ _`
       (drule_then strip_assume_tac) >>
     qpat_x_assum `loc = case _ of _ => _ | _ => _` kall_tac >>
     Cases_on `cenv.ce_is_ctor /\ loc = LocCode` >> fs[]) >>
  asm_rewrite_tac[]
QED

Resume membership_dynamic_physical_mods[search]:
  `sm.cs_next_var <= sl.cs_next_var` by
    (drule exprSafeOperandBuiltinsTheory.compile_ptr_load_next_var >> simp[]) >>
  `cs_extends sm sl` by
    (mp_tac externalEntryShapeTheory.compile_ptr_load_labels >>
     disch_then (qspecl_then
       [`cenv.ce_is_ctor`,`cenv.ce_imm_alloca`,`loc`,`vv_operand vv`,`sm`,`\l. T`] mp_tac) >>
     simp[]) >>
  `cs_extends sl ct` by
    (drule bodyPtrBopInBoundedLayoutTheory.membership_bounded_loop_extends >> simp[]) >>
  `fn_has_code sl ct fn` by (drule_all fragExecTheory.fn_has_code_split >> simp[]) >>
  `!x. len = Var x ==> not_fresh_at sl x` by
    (drule fragFuelExprHelpersTheory.compile_ptr_load_var >>
     simp[loweringStateRelDefsTheory.not_fresh_at_def, fragFuelTheory.var_below_def]) >>
  `membership_loop_frame sm Gu Tu u Gh Th sh /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp sh)` by
    (qpat_assum `?H. guard H` strip_assume_tac >>
     qpat_assum `!H. guard H ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by metis_tac[] >>
  drule_all_then strip_assume_tac membership_header_read_frame_mods >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sl x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sm` >> metis_tac[]) >>
  `!ib x. cenv.ce_imm_alloca = SOME ib /\ ib = Var x ==> not_fresh_at sl x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sm` >> metis_tac[]) >>
  irule membership_array_dynamic_run_mods >>
  qpat_assum `compile_var_array_membership _ _ _ _ _ _ = _` (irule_at Any) >>
  qexistsl_tac [`sl`,`sh`,`len`,`cap`,`Th`,`Gh`] >>
  qpat_assum `loc = case _ of _ => _ | _ => _` (once_rewrite_tac o single o SYM) >>
  simp_tac bool_ss [] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "guarded_header" >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "callback" >>
  asm_rewrite_tac[]
QED

Resume membership_dynamic_physical_mods[guarded_header]:
  gen_tac >> disch_tac >>
  qpat_assum `!H. guard H ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. guard H ==> ~u.vs_halted /\ _`
    (drule_then strip_assume_tac) >>
  asm_rewrite_tac[]
QED

Resume membership_dynamic_physical_mods[callback]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `loc = case _ of _ => _ | _ => _` (fn th =>
    irule (SIMP_RULE std_ss [SYM th, optionTheory.IS_SOME_DEF, COND_CLAUSES]
      (Q.INST [`skip` |-> `word_scale loc`, `bound` |-> `SOME cap`]
        membership_array_index_load_mods))) >>
  qpat_assum `compile_array_membership_loop _ _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
  qexists_tac `w` >>
  qpat_x_assum `loc = case _ of _ => _ | _ => _` kall_tac >>
  ntac 5 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >-
    (disch_tac >> conj_tac >- metis_tac[] >>
     gen_tac >> disch_tac >>
     qpat_assum `!H. guard H ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_x_assum `op_prov Gh (vv_operand vv) = op_prov Gu (vv_operand vv)` kall_tac >>
     qpat_assum `cenv.ce_is_ctor /\ loc = LocCode ==> op_prov Gh _ = NONE /\ _`
       mp_tac >> simp[]) >>
  conj_tac >-
    (gen_tac >> qx_gen_tac `j` >> strip_tac >>
     qpat_assum `!j. j < LENGTH ws ==> let addr = _ in ptr_load_val _ _ addr sh = _ /\ _`
       (qspec_then `j` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac pure_ss [LET_THM] >> metis_tac[]) >>
  asm_rewrite_tac[]
QED

Finalise membership_dynamic_physical_mods
