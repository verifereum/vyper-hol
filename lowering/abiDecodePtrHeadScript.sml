(* Scalar underflow checks for relative dynamic-member positions. *)
Theory abiDecodePtrHead
Ancestors
  abiDecodePtrRead abiDecodePtrPrims abiDecoderGuard bodyPtrBopScalarCompile
  emitHelper emitHelperProps exprLoweringProps compileEnv list pred_set
  bodyPtrBopScalarSeq abiEncoder bodyPtrBopHashSuffix fragExec
  abiDecodePtrScalarReplay abiDecodePtrLoadReplay abiDecodePtrPosition
  abiDecodePtrNormalized assignTuplePtrLocalBytesCopy
  stmtReasonLitFragMemory words arithmetic
  stateFrame fragExecPtr fragGasSeqPtr venomExecSemantics exprSimAccounts rich_list ptrDiscipline
  venomState finite_map abiDecodePtrMemberFrame bodyPtrDefs venomInst instIdxIndep

Theorem abi_decode_ge_guard_scalar:
  abi_decode_ge_guard a b sa = ((),sb) /\ a IN A /\ b IN A /\
  (!x. x IN R ==> not_fresh_at sa x) ==>
  ?B. bop_scalar_seq R A (emitted_insts sa sb) B
Proof
  simp[abi_decode_ge_guard_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rename1 `emit_op LT [a;b] sa = (underflow,c1)` >>
  rename1 `emit_op ISZERO [underflow] c1 = (ok,c2)` >>
  `bop_scalar_seq R A (emitted_insts sa c2)
     (ok INSERT underflow INSERT A)` by
    (irule bop_scalar_seq_emit_iszero >> simp[] >>
     qexistsl_tac [`c1`, `LT`, `[a;b]`] >> simp[]) >>
  `bop_scalar_seq R (ok INSERT underflow INSERT A)
     (emitted_insts c2 sb) (ok INSERT underflow INSERT A)` by
    (irule bop_scalar_seq_emit_assert >> simp[] >> metis_tac[]) >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  `emitted_insts sa c2 = emitted_insts sa c1 ++ emitted_insts c1 c2` by
    (irule emitted_insts_append >> simp[]) >>
  `emitted_insts sa sb = emitted_insts sa c2 ++ emitted_insts c2 sb` by
    (irule emitted_insts_append >> asm_rewrite_tac[APPEND_ASSOC]) >>
  asm_rewrite_tac[] >> metis_tac[bop_scalar_seq_append]
QED

(* Success is conditional on the unsigned guard, not on ABI validity. *)
Theorem abi_decode_ge_guard_success_ptr:
  abi_decode_ge_guard a b sa = ((),sb) /\
  eval_operand a s = SOME va /\ eval_operand b s = SOME vb /\
  w2n vb <= w2n va /\ fresh_vars_wrt sa s /\
  op_prov G a = NONE /\ op_prov G b = NONE /\
  op_taint tn a = {} /\ op_taint tn b = {} /\ ~ctx_has_dalloca ctx /\
  (!x. x IN R ==> not_fresh_at sa x) ==>
  ?t G' tn'. run_inst_seq (emitted_insts sa sb) s = OK t /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s G' tn' /\
    fresh_vars_wrt sb t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x IN R ==> FLOOKUP G' x = FLOOKUP G x /\
                      FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >> drule_all abi_decode_ge_guard_sequence >> strip_tac >>
  `?B. bop_scalar_seq R {a;b} (emitted_insts sa sb) B` by
    (irule abi_decode_ge_guard_scalar >> simp[] >> metis_tac[]) >>
  `!op. op IN {a;b} ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    (simp[] >> metis_tac[]) >>
  drule_all bop_scalar_seq_run >>
  disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`t`, `G'`, `tn'`] >> simp[]
QED

(* The actual-position ADD and its optional underflow guard are wholly scalar.
   This certificate says nothing about whether the guard succeeds. *)
Theorem abi_decode_position_suffix_scalar:
  emit_op ADD [pos;offset] sa = (actual,mid) /\
  (if hi = Lit 0w then sb = mid
   else abi_decode_ge_guard actual pos mid = ((),sb)) /\
  pos IN A /\ offset IN A /\
  (!x. x IN R ==> not_fresh_at sa x) ==>
  ?B. bop_scalar_seq R A (emitted_insts sa sb) B /\ actual IN B
Proof
  strip_tac >>
  `bop_scalar_seq R A (emitted_insts sa mid) (actual INSERT A)` by
    (irule bop_scalar_seq_emit_op >> simp[] >>
     qexistsl_tac [`ADD`, `[pos;offset]`] >> simp[]) >>
  Cases_on `hi = Lit 0w`
  >- (gvs[] >> qexists_tac `actual INSERT A` >> simp[]) >>
  `abi_decode_ge_guard actual pos mid = ((),sb)` by gvs[] >>
  `!x. x IN R ==> not_fresh_at mid x` by
    (drule emitted_insts_emit_op >> strip_tac >> fs[not_fresh_at_def] >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `?B. bop_scalar_seq R (actual INSERT A) (emitted_insts mid sb) B` by
    (irule abi_decode_ge_guard_scalar >> simp[] >> metis_tac[]) >>
  `actual IN B` by
    (drule bodyPtrBopScalarCompileTheory.bop_scalar_seq_available >>
     simp[SUBSET_DEF]) >>
  imp_res_tac emit_op_extends >>
  drule abi_decode_ge_guard_shape >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa mid ++ emitted_insts mid sb` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  qexists_tac `B` >> simp[] >> irule bop_scalar_seq_append >>
  qexists_tac `actual INSERT A` >> simp[]
QED

Theorem abi_decode_getelemptr_dynamic_split:
  compile_getelemptr_abi pos T off MLOAD (Var src) hi sa = (v,sb) ==>
  ?head c1 addr c2 offset c3 mid.
    emit_op ADD [pos; Lit (n2w off)] sa = (head,c1) /\
    compile_abi_dec_addr (Var src) head c1 = (addr,c2) /\
    emit_op MLOAD [addr] c2 = (offset,c3) /\
    emit_op ADD [pos;offset] c3 = (v,mid) /\
    (if hi = Lit 0w then sb = mid
     else abi_decode_ge_guard v pos mid = ((),sb))
Proof
  Cases_on `hi = Lit 0w` >>
  simp[compile_getelemptr_abi_def, abi_decode_ge_guard_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem abi_decode_getelemptr_success_ptr:
  compile_getelemptr_abi pos T off MLOAD (Var src) hi sa = (v,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  abi_decode_ptr_window G tn s src b h /\ not_fresh_at sa src /\
  (!x. pos = Var x ==> not_fresh_at sa x) /\
  eval_operand pos s = SOME z /\ op_prov G pos = NONE /\ op_taint tn pos = {} /\
  p = w2n (z + n2w off) /\ p+32 <= h /\ w2n b+h < dimword(:256) /\
  run_inst_seq (emitted_insts sa sb) s = OK u ==>
  ?out G' tn'. v = Var out /\ not_fresh_at sb out /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s G' tn' /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G' tn'
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    lookup_var out u = SOME (z + mload (w2n b+p) s) /\
    op_prov G' v = NONE /\ op_taint tn' v = {} /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    state_frame u = state_frame s /\ u.vs_memory = s.vs_memory /\
    u.vs_allocas = s.vs_allocas /\ u.vs_accounts = s.vs_accounts /\
    u.vs_transient = s.vs_transient /\ u.vs_call_ctx = s.vs_call_ctx /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule abi_decode_getelemptr_dynamic_split >> strip_tac >>
  suspend "phases"
QED

Resume abi_decode_getelemptr_success_ptr[phases]:
  `emit_op ADD [Var src;head] c1 = (addr,c2)` by
    fs[compile_abi_dec_addr_def] >>
  `cs_extends sa c1 /\ sa.cs_next_var <= c1.cs_next_var /\
   cs_extends c1 c2 /\ c1.cs_next_var <= c2.cs_next_var /\
   cs_extends c2 c3 /\ c2.cs_next_var <= c3.cs_next_var /\
   cs_extends c3 mid /\ c3.cs_next_var <= mid.cs_next_var` by
    metis_tac[emit_op_extends_next_var] >>
  `cs_extends mid sb /\ mid.cs_next_var <= sb.cs_next_var /\
   inst_extends mid sb /\ same_blocks mid sb` by
    (Cases_on `hi = Lit 0w` >> gvs[]
     >- simp[cs_extends_refl, inst_extends_refl, same_blocks_def] >>
     fs[abi_decode_ge_guard_def, comp_bind_def] >>
     rpt (pairarg_tac >> gvs[]) >>
     imp_res_tac emit_op_extends_next_var >>
     imp_res_tac emitted_insts_emit_void >>
     imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
     imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
     `inst_extends mid sb` by metis_tac[inst_extends_trans] >>
     `same_blocks mid sb` by metis_tac[same_blocks_trans] >>
     conj_tac
     >- (irule cs_extends_same_block >>
         qpat_x_assum `same_blocks mid sb` mp_tac >>
         qpat_x_assum `inst_extends mid sb` mp_tac >>
         simp[same_blocks_def, inst_extends_def, IS_PREFIX_APPEND]) >>
     simp[] >> decide_tac) >>
  imp_res_tac inst_extends_emit_op >>
  `inst_extends sa c1 /\ inst_extends c1 c3 /\ inst_extends c3 sb` by
    metis_tac[inst_extends_trans] >>
  `emitted_insts sa sb = emitted_insts sa c1 ++
     emitted_insts c1 c3 ++ emitted_insts c3 sb` by
    (fs[inst_extends_def] >>
     metis_tac[emitted_insts_append, APPEND_ASSOC]) >>
  `bop_scalar_seq {x | not_fresh_at sa x} {pos; Lit (n2w off)}
    (emitted_insts sa c1) (head INSERT {pos; Lit (n2w off)})` by
    (irule bop_scalar_seq_emit_op >> simp[] >>
     qexistsl_tac [`ADD`, `[pos; Lit (n2w off)]`] >> simp[]) >>
  `?B. bop_scalar_seq {x | not_fresh_at c3 x} {pos;offset}
    (emitted_insts c3 sb) B /\ v IN B` by
    (irule abi_decode_position_suffix_scalar >> simp[] >> metis_tac[]) >>
  `emitted_insts c1 c3 = emitted_insts c1 c2 ++ emitted_insts c2 c3` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa c1) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c1 c3) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c3 sb)` by
    (imp_res_tac bop_scalar_seq_opcodes >>
     qpat_assum `emit_op ADD [Var src;head] c1 = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     qpat_assum `emit_op MLOAD [addr] c2 = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     fs[EVERY_MEM, is_terminator_def, mk_inst_def] >>
     rpt strip_tac >> gvs[is_terminator_def]) >>
  `?s1. s1.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts sa c1) /\
    run_inst_seq (emitted_insts sa c1) s = OK (s1 with vs_inst_idx := s.vs_inst_idx) /\
    run_inst_seq (emitted_insts c1 c3 ++ emitted_insts c3 sb) s1 =
      OK (u with vs_inst_idx := s1.vs_inst_idx)` by
    (irule abi_decode_run_split_normalized >> simp[] >>
     qpat_x_assum `run_inst_seq (emitted_insts sa sb) s = _` mp_tac >> simp[]) >>
  `?s2. s2.vs_inst_idx = s1.vs_inst_idx + LENGTH (emitted_insts c1 c3) /\
    run_inst_seq (emitted_insts c1 c3) s1 = OK (s2 with vs_inst_idx := s1.vs_inst_idx) /\
    run_inst_seq (emitted_insts c3 sb) s2 = OK (u with vs_inst_idx := s2.vs_inst_idx)` by
    (drule_all abi_decode_run_split_normalized >> simp[]) >>
  `s1.vs_inst_idx = LENGTH c1.cs_current_insts /\
   s2.vs_inst_idx = LENGTH c3.cs_current_insts` by
    (qpat_x_assum `inst_extends sa c1` mp_tac >>
     qpat_x_assum `inst_extends c1 c3` mp_tac >>
     qpat_x_assum `s1.vs_inst_idx = _` mp_tac >>
     qpat_x_assum `s2.vs_inst_idx = _` mp_tac >>
     qpat_x_assum `s.vs_inst_idx = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[inst_extends_def] >>
     rpt strip_tac >> fs[]) >>
  suspend "head_add"
QED

Resume abi_decode_getelemptr_success_ptr[head_add]:
  `cs_extends c1 sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa c1 func` by metis_tac[fn_has_code_split] >>
  `same_blocks sa c1` by metis_tac[emit_op_extends] >>
  `!op. op IN {pos; Lit (n2w off)} ==>
    op_prov G op = NONE /\ op_taint tn op = {}` by
    (rpt strip_tac >> gvs[op_prov_def, op_taint_def]) >>
  drule_all abi_decode_scalar_compile_replay_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `inst_seq_ptr D 0 ctx func PG G tn
    (emitted_insts sa c1) s H tm` >>
  `s1.vs_memory = s.vs_memory /\ s1.vs_halted = s.vs_halted /\
   s1.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `s1 = s with <|vs_vars := _; vs_inst_idx := _|>` mp_tac >>
     simp[venom_state_component_equality]) >>
  `abi_decode_ptr_window H tm s1 src b h` by
    (qpat_x_assum `!x. x IN {x | not_fresh_at sa x} ==> _`
       (qspec_then `src` mp_tac) >>
     simp[] >> strip_tac >>
     gvs[abi_decode_ptr_window_def, ptr_covers_def, op_taint_def]) >>
  `eval_operand head s1 = SOME (n2w p)` by
    (drule_all buffer_emit_add_run >> strip_tac >>
     qpat_assum `emit_op ADD [pos; Lit (n2w off)] sa = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     qpat_x_assum `s with vs_vars := _ = s1 with vs_inst_idx := _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[venom_state_component_equality] >> rpt strip_tac >>
     qpat_x_assum `_ |+ _ = s1.vs_vars` (SUBST1_TAC o SYM) >> simp[FLOOKUP_UPDATE]) >>
  suspend "load_replay"
QED

Resume abi_decode_getelemptr_success_ptr[load_replay]:
  `fn_has_code c1 c3 func` by metis_tac[fn_has_code_split, cs_extends_trans] >>
  `~s1.vs_halted /\ s1.vs_current_bb = c1.cs_current_bb /\ op_taint tm head = {}` by
    (fs[same_blocks_def] >> metis_tac[IN_INSERT]) >>
  drule_all abi_decode_relative_load_success_replay_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  suspend "suffix"
QED

Resume abi_decode_getelemptr_success_ptr[suffix]:
  `~s2.vs_halted /\ s2.vs_current_bb = c3.cs_current_bb /\
   s2.vs_memory = s1.vs_memory /\
   lookup_var out s2 = SOME (mload (w2n b+p) s1)` by
    (fs[lookup_var_def]) >>
  `op_prov H pos = NONE /\ op_taint tm pos = {}` by
    (qpat_x_assum `!op. op IN {head; _; _} ==> _`
       (qspec_then `pos` mp_tac) >> simp[NoAsms]) >>
  `op_prov G'' pos = NONE /\ op_taint tn'' pos = {}` by
    (Cases_on `pos` >> simp[op_prov_def, op_taint_def] >>
     rename1 `FLOOKUP G'' var = NONE` >>
     `not_fresh_at c1 var` by
       (fs[not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
     qpat_x_assum `!x. not_fresh_at c1 x ==> _`
       (qspec_then `var` mp_tac) >>
     qpat_x_assum `op_prov H (Var var) = NONE` mp_tac >>
     qpat_x_assum `op_taint tm (Var var) = {}` mp_tac >>
     simp[NoAsms, op_prov_def, op_taint_def] >>
     qpat_x_assum `not_fresh_at c1 var` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> metis_tac[]) >>
  `!op. op IN {pos;offset} ==> op_prov G'' op = NONE /\ op_taint tn'' op = {}` by
    (simp[] >> metis_tac[]) >>
  `fn_has_code c3 sb func /\ same_blocks c3 sb` by
    (imp_res_tac emit_op_extends >>
     metis_tac[fn_has_code_split, cs_extends_trans, same_blocks_trans]) >>
  qabbrev_tac `un = u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `un.vs_inst_idx = LENGTH sb.cs_current_insts /\
   run_inst_seq (emitted_insts c3 sb) s2 = OK (un with vs_inst_idx := s2.vs_inst_idx)` by
    simp[Abbr `un`] >>
  drule_all abi_decode_scalar_compile_replay_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  suspend "compose"
QED

Resume abi_decode_getelemptr_success_ptr[compose]:
  qmatch_asmsub_abbrev_tac `inst_seq_ptr D 0 ctx func PG G'' tn''
    (emitted_insts c3 sb) s2 Hfinal tk` >>
  `un.vs_inst_idx = s2.vs_inst_idx + LENGTH (emitted_insts c3 sb)` by
    (qpat_x_assum `inst_extends c3 sb` mp_tac >>
     qpat_x_assum `s2.vs_inst_idx = LENGTH _` mp_tac >>
     qpat_x_assum `un.vs_inst_idx = LENGTH _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[inst_extends_def] >>
     rpt strip_tac >> fs[]) >>
  `inst_seq_ptr D 0 ctx func PG G tn
     (emitted_insts sa c1 ++ emitted_insts c1 c3) s G'' tn'' /\
   run_inst_seq (emitted_insts sa c1 ++ emitted_insts c1 c3) s =
     OK (s2 with vs_inst_idx := s.vs_inst_idx) /\
   s2.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts sa c1 ++ emitted_insts c1 c3)` by
    (qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ (emitted_insts c3 sb) _ _ _` kall_tac >>
     drule_all inst_seq_ptr_append_normalized >> simp[] >> metis_tac[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
    (emitted_insts sa c1 ++ emitted_insts c1 c3)` by simp[] >>
  `inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s Hfinal tk` by
    (qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ (emitted_insts sa c1) _ _ _` kall_tac >>
     qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ (emitted_insts c1 c3) _ _ _` kall_tac >>
     drule_all inst_seq_ptr_append_normalized >> strip_tac >>
     qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ (_ ++ _) _ _ _` mp_tac >> simp[APPEND_ASSOC]) >>
  suspend "export"
QED

Resume abi_decode_getelemptr_success_ptr[export]:
  `!x. not_fresh_at sa x ==> not_fresh_at c1 x /\ not_fresh_at c3 x` by
    (fs[not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum drule >> simp[] >> decide_tac) >>
  `eval_operand pos s2 = SOME z` by
    (Cases_on `pos`
     >- fs[eval_operand_def]
     >- (rename1 `eval_operand (Var x) s = SOME z` >>
         `not_fresh_at sa x /\ not_fresh_at c1 x` by metis_tac[] >>
         qpat_x_assum `!x. x IN {x | not_fresh_at sa x} ==> _`
           (qspec_then `x` mp_tac) >>
         qpat_x_assum `!x. not_fresh_at c1 x ==> _`
           (qspec_then `x` mp_tac) >>
         qpat_x_assum `eval_operand (Var x) s = SOME z` mp_tac >>
         qpat_x_assum `not_fresh_at sa x` mp_tac >>
         qpat_x_assum `not_fresh_at c1 x` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >>
         simp[eval_operand_def, lookup_var_def]) >>
     qpat_x_assum `s1 = s with <|vs_vars := _; vs_inst_idx := _|>` mp_tac >>
     qpat_x_assum `state_frame (s2 with vs_inst_idx := _) = state_frame s1` mp_tac >>
     qpat_x_assum `eval_operand _ s = SOME z` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[venom_state_component_equality, state_frame_def, eval_operand_def]) >>
  `eval_operand offset s2 = SOME (mload (w2n b+p) s1)` by
    simp[eval_operand_def] >>
  drule_all abi_decode_position_suffix_result >> strip_tac >>
  suspend "values"
QED

Resume abi_decode_getelemptr_success_ptr[values]:
  qexistsl_tac [`out'`, `Hfinal`, `tk`] >>
  `lookup_var out' u = SOME (z + mload (w2n b+p) s)` by
    (qpat_x_assum `lookup_var out' (_ with vs_inst_idx := _) = _` mp_tac >>
     qpat_x_assum `s1.vs_memory = s.vs_memory` mp_tac >>
     simp[lookup_var_def, mload_def, Abbr `un`]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (qpat_x_assum `emitted_insts sa sb = _` (fn th => rewrite_tac[th]) >>
     asm_rewrite_tac[EVERY_APPEND]) >>
  `u.vs_inst_idx = s.vs_inst_idx` by
    (drule run_inst_seq_inst_idx >>
     disch_then (qspecl_then [`s`, `s.vs_inst_idx`] mp_tac) >>
     qpat_x_assum `run_inst_seq (emitted_insts sa sb) s = OK u` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[exec_result_map_def, venom_state_component_equality]) >>
  `u.vs_memory = s.vs_memory /\ state_frame u = state_frame s /\
   ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
   u.vs_allocas = s.vs_allocas /\ u.vs_accounts = s.vs_accounts /\
   u.vs_transient = s.vs_transient /\ u.vs_call_ctx = s.vs_call_ctx` by
    (qpat_x_assum `un = s2 with <|vs_vars := _; vs_inst_idx := _|>` mp_tac >>
     qpat_x_assum `s1 = s with <|vs_vars := _; vs_inst_idx := _|>` mp_tac >>
     qpat_x_assum `state_frame (s2 with vs_inst_idx := _) = state_frame s1` mp_tac >>
     qpat_x_assum `s2.vs_current_bb = c3.cs_current_bb` mp_tac >>
     qpat_x_assum `same_blocks c3 sb` mp_tac >>
     qpat_x_assum `~s2.vs_halted` mp_tac >>
     qpat_x_assum `u.vs_inst_idx = s.vs_inst_idx` mp_tac >>
     simp[Abbr `un`, NoAsms] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[ state_frame_def, same_blocks_def, venom_state_component_equality] >>
     metis_tac[]) >>
  simp[] >> suspend "finish_exports"
QED

Resume abi_decode_getelemptr_success_ptr[finish_exports]:
  reverse conj_tac
  >- (conj_tac
      >- (qpat_x_assum `state_frame u = state_frame s` mp_tac >>
          qpat_x_assum `u.vs_current_bb = sb.cs_current_bb` mp_tac >>
          qpat_x_assum `s.vs_current_bb = sa.cs_current_bb` mp_tac >>
          POP_ASSUM_LIST (K ALL_TAC) >> simp[state_frame_def] >> metis_tac[]) >>
      rpt strip_tac >>
      `not_fresh_at c1 x /\ not_fresh_at c3 x` by metis_tac[] >>
      qpat_x_assum `!x. x IN {x | not_fresh_at sa x} ==> _`
        (qspec_then `x` mp_tac) >>
      qpat_x_assum `!x. not_fresh_at c1 x ==> _`
        (qspec_then `x` mp_tac) >>
      qpat_x_assum `!x. x IN {x | not_fresh_at c3 x} ==> _`
        (qspec_then `x` mp_tac) >>
      simp[Abbr `un`, lookup_var_def, op_taint_def] >> metis_tac[]) >>
  suspend "gas_export"
QED

Resume abi_decode_getelemptr_success_ptr[gas_export]:
  `inst_extends sa sb /\ same_blocks sa sb` by
    metis_tac[inst_extends_trans, same_blocks_trans, emit_op_extends] >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
   sb.cs_current_bb = sa.cs_current_bb` by
    (qpat_x_assum `inst_extends sa sb` mp_tac >>
     qpat_x_assum `same_blocks sa sb` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[inst_extends_def, same_blocks_def]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (drule_all fn_has_code_code >> simp[] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb) /\
   EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    (imp_res_tac bop_scalar_seq_opcodes >>
     qpat_assum `emit_op ADD [Var src;head] c1 = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     qpat_assum `emit_op MLOAD [addr] c2 = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     fs[EVERY_CONJ]) >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (fs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  drule_all run_inst_seq_gas_path_ptr >>
  simp[Abbr `un`] 
QED

Finalise abi_decode_getelemptr_success_ptr
