(* The checked scalar prefix starts at the JMP immediately after ALLOCA. *)
Theory bodyForRangeCheckedStartMods
Ancestors
  bodyForRangeHeaderMods bodyForRangeRouteMods bodyForRangeScalarFrameMods
  bodyFullForRange stmtSimForRange exprLoweringProps fragGasOriginPtrLoop
  gasOutcomeFullPostMods haltExitProj venomState venomInst integer_word
  bodyFullIfExpReach exprSimProps bodyFullShared allocaHistory
  fragGasOriginPtr ptrDiscipline words rich_list fragExec venomInstProps
  augAssignPtrScalarCertificate venomMemDefs vyperTypeSystem
  bodyPtrDefs vyperState vyperInterpreter gasOutcomeFullMods bodyFullPostsMods
  bodyFullPredsMods loweringPosts bodyMemoryDefs stmtSimDefs compileEnv
  localPtrsProps freshWrites loweringStateRelDefs vyperStorageTrace bodyBranchCellFrameMods
  exprSimHypsDefs vyperStorageFootprint vyperStorageBackend finite_map bodySimFull stmtSimProps

Theorem checked_path_append[local]:
  gas_origin_ptr_path C (s,G,tn) [] (OK u,G1,tn1) /\
  gas_origin_ptr_path C (u,G1,tn1) [] (r,G2,tn2) ==>
  gas_origin_ptr_path C (s,G,tn) [] (r,G2,tn2)
Proof
  strip_tac >>
  qpat_assum `gas_origin_ptr_path _ _ _ (OK _,_,_)`
    (mp_then (Pos hd) mp_tac gas_origin_ptr_path_append) >> simp[] >>
  disch_then irule >> first_assum ACCEPT_TAC
QED

Theorem checked_scalar_available[local]:
  (!l. op <> Label l) ==> scalar_available {x | op = Var x \/ q = Var x} op
Proof
  Cases_on `op` >> simp[scalar_available_def]
QED

Theorem checked_scalar_available_right[local]:
  (!l. op <> Label l) ==> scalar_available {x | q = Var x \/ op = Var x} op
Proof
  Cases_on `op` >> simp[scalar_available_def]
QED

Theorem checked_scalar_path[local]:
  lookup_block sA.vs_current_bb func.fn_blocks = SOME pre_bb /\
  get_instruction pre_bb sA.vs_inst_idx = SOME (mk_inst jmp_id JMP [Label entry_lbl] []) /\
  lookup_block entry_lbl func.fn_blocks = SOME
    <|bb_label := entry_lbl;
      bb_instructions :=
        [mk_inst i ASSIGN [op1] [cv];
         mk_inst (i+1) SUB [op2;op1] [rv];
         mk_inst (i+2) (if is_signed_type fty then SGT else GT) [op1;op2] [g1];
         mk_inst (i+3) ISZERO [Var g1] [z1];
         mk_inst (i+4) ASSERT [Var z1] [];
         mk_inst (i+5) GT [Var rv;Lit (n2w bound)] [g2];
         mk_inst (i+6) ISZERO [Var g2] [z2];
         mk_inst (i+7) ASSERT [Var z2] [];
         mk_inst (i+8) ADD [op1;Var rv] [ev];
         mk_inst (i+9) JMP [Label cond_lbl] []]|> /\
  ~sA.vs_halted /\ allocas_from lo sA /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp sA) /\
  eval_operand op1 sA = SOME (i2w n1) /\ eval_operand op2 sA = SOME (i2w n2) /\
  (!l. op1 <> Label l /\ op2 <> Label l) /\
  ALL_DISTINCT [cv;rv;g1;z1;g2;z2;ev] /\
  (!x. op1 = Var x \/ op2 = Var x ==>
       ~MEM x [cv;rv;g1;z1;g2;z2;ev] /\
       op_prov GA (Var x) = NONE /\ op_taint tnA (Var x) = {}) /\
  is_int_type fty /\ evaluate_type (get_tenv cx) fty = SOME tyv /\
  value_has_type tyv (IntV n1) /\ value_has_type tyv (IntV n2) /\
  bound < dimword (:256) ==>
  if n2 < n1 \/ bound < Num (n2 - n1) then
    ?t G tn. !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
                  (sA,GA,tnA) [] (Abort Revert_abort t,G,tn)
  else
    ?t G tn. (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
                  (sA,GA,tnA) [] (OK t,G,tn)) /\
      n1 <= n2 /\ Num (n2 - n1) < dimword (:256) /\ Num (n2 - n1) <= bound /\
      t = jump_to cond_lbl (jump_to entry_lbl (sA with vs_vars := t.vs_vars)) /\
      lookup_var cv t = SOME (i2w n1) /\ lookup_var ev t = SOME (i2w n2) /\
      op_prov G (Var cv) = NONE /\ op_taint tn (Var cv) = {} /\
      op_prov G (Var ev) = NONE /\ op_taint tn (Var ev) = {} /\
      (!x. ~MEM x [cv;rv;g1;z1;g2;z2;ev] ==>
        lookup_var x t = lookup_var x sA /\ FLOOKUP G x = FLOOKUP GA x /\
        op_taint tn (Var x) = op_taint tnA (Var x)) /\
      tn.t_mem = tnA.t_mem /\ tn.t_stor = tnA.t_stor /\
      tn.t_trans = tnA.t_trans /\ tn.t_imm = tnA.t_imm
Proof
  strip_tac >>
  qabbrev_tac `s = jump_to entry_lbl sA` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (sA,GA,tnA) [] (OK s,GA,tnA)` by
    (gen_tac >> simp[Abbr `s`] >> irule jmp_origin_ptr_path >> simp[] >>
     qexists `jmp_id` >> simp[]) >>
  qabbrev_tac `A = {x | op1 = Var x \/ op2 = Var x}` >>
  qabbrev_tac `cmp = if is_signed_type fty then SGT else GT` >>
  qmatch_asmsub_abbrev_tac
    `lookup_block entry_lbl _ = SOME <|bb_label := entry_lbl; bb_instructions := fullcode|>` >>
  qabbrev_tac `code = TAKE 9 fullcode` >>
  `MEM cmp [SGT;GT] /\ scalar_available A op1 /\ scalar_available A op2 /\
   (!x. op1 = Var x \/ op2 = Var x ==> ~MEM x [cv;rv;g1;z1;g2;z2;ev])` by
    (conj_tac >- (Cases_on `is_signed_type fty` >> simp[Abbr `cmp`]) >>
     conj_tac >- (simp[Abbr `A`] >> irule checked_scalar_available >> metis_tac[]) >>
     conj_tac >- (simp[Abbr `A`] >> irule checked_scalar_available_right >> metis_tac[]) >>
     gen_tac >> disch_tac >> qpat_assum `!x. op1 = Var x \/ op2 = Var x ==> _`
       (qspec_then `x` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> simp[]) >>
  `eval_operand op1 s = SOME (i2w n1) /\ eval_operand op2 s = SOME (i2w n2)` by
    (conj_tac
     >- (Cases_on `op1` >> fs[Abbr `s`, eval_operand_def, lookup_var_def, jump_to_def]) >>
     Cases_on `op2` >> fs[Abbr `s`, eval_operand_def, lookup_var_def, jump_to_def]) >>
  qabbrev_tac `bad1 = if cmp = SGT then word_gt (i2w n1 : bytes32) (i2w n2)
                       else w2n (i2w n1 : bytes32) > w2n (i2w n2 : bytes32)` >>
  qabbrev_tac `bad2 = (w2n (i2w n2 - i2w n1 : bytes32) > w2n (n2w bound : bytes32))` >>
  qabbrev_tac `u1 = update_var cv (i2w n1) s` >>
  qabbrev_tac `u2 = update_var rv (i2w n2-i2w n1) u1` >>
  qabbrev_tac `u3 = update_var g1 (bool_to_word bad1) u2` >>
  qabbrev_tac `u4 = update_var z1 (bool_to_word (bool_to_word bad1 = 0w)) u3` >>
  qabbrev_tac `u5 = update_var g2 (bool_to_word bad2) u4` >>
  qabbrev_tac `u6 = update_var z2 (bool_to_word (bool_to_word bad2 = 0w)) u5` >>
  qabbrev_tac `u7 = update_var ev (i2w n1+(i2w n2-i2w n1)) u6` >>
  `scalar_code A code /\ run_inst_seq_mem_ok code s /\
   run_inst_seq code s =
     (if bad1 then Abort Revert_abort (revert_state (set_returndata [] u4))
      else if bad2 then Abort Revert_abort (revert_state (set_returndata [] u6))
      else OK u7) /\
   lookup_var cv u7 = SOME (i2w n1) /\ lookup_var ev u7 = SOME (i2w n2) /\
   (!x. ~MEM x [cv;rv;g1;z1;g2;z2;ev] ==> lookup_var x u7 = lookup_var x s)` by
    (mp_tac (range_checked_scalar_run |> SPEC_ALL |>
       Q.INST [`a` |-> `i2w n1 : bytes32`, `b` |-> `i2w n2 : bytes32`]) >>
     (impl_tac >- asm_rewrite_tac[]) >>
     simp[Abbr `code`, Abbr `fullcode`, Abbr `u7`, Abbr `u6`, Abbr `u5`,
          Abbr `u4`, Abbr `u3`, Abbr `u2`, Abbr `u1`, Abbr `bad1`, Abbr `bad2`,
          WORD_SUB_ADD2]) >>
  suspend "lift"
QED

Resume checked_scalar_path[lift]:
  `?G tn j.
    (!D. inst_seq_ptr D 0 ctx func PG GA tnA code s G tn) /\
    (!v. ~MEM v (FLAT (MAP (\i. i.inst_outputs) code)) ==>
      FLOOKUP G v = FLOOKUP GA v /\ FLOOKUP tn.t_var v = FLOOKUP tnA.t_var v /\
      op_taint tn (Var v) = op_taint tnA (Var v)) /\
    tn.t_mem = tnA.t_mem /\ tn.t_stor = tnA.t_stor /\
    tn.t_trans = tnA.t_trans /\ tn.t_imm = tnA.t_imm /\
    (!t. run_inst_seq code s = OK t ==>
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,GA,tnA) [] (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code),G,tn)) /\
      (!v. v IN A UNION BIGUNION (set (MAP (\i. set i.inst_outputs) code)) ==>
        op_prov G (Var v) = NONE /\ op_taint tn (Var v) = {})) /\
    (!a t. run_inst_seq code s = Abort a t ==>
      !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,GA,tnA) [] (Abort a (t with vs_inst_idx := j),G,tn))` by
    (`!v. v IN A ==> op_prov GA (Var v) = NONE /\ op_taint tnA (Var v) = {}` by
       (simp[Abbr `A`] >> gen_tac >> disch_tac >>
        qpat_assum `!x. op1 = Var x \/ op2 = Var x ==> _ /\ _`
          (qspec_then `v` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> simp[]) >>
     `~s.vs_halted /\ allocas_from lo s /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s)` by
       (pure_rewrite_tac[allocas_from_def, allocas_below_fmp_def] >>
        simp[Abbr `s`, jump_to_def] >> conj_tac >-
          (qpat_assum `allocas_from lo sA` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
        qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp sA`
          (ACCEPT_TAC o REWRITE_RULE [allocas_below_fmp_def])) >>
     irule range_scalar_joint_lift >> asm_rewrite_tac[] >>
     qexists `<|bb_label := entry_lbl; bb_instructions := fullcode|>` >>
     simp[Abbr `s`, jump_to_def, Abbr `code`, Abbr `fullcode`,
          rich_listTheory.IS_PREFIX_APPEND]) >>
  `bad1 = (n2 < n1) /\
   (n1 <= n2 ==> Num (n2 - n1) < dimword (:256) /\
     (bad2 = (bound < Num (n2 - n1))))` by
    (`(if is_signed_type fty then word_gt (i2w n1 : bytes32) (i2w n2)
         else w2n (i2w n1 : bytes32) > w2n (i2w n2 : bytes32)) = (n2 < n1) /\
       (n1 <= n2 ==> Num (n2 - n1) < dimword (:256) /\
         w2n (i2w n2 - i2w n1 : bytes32) = Num (n2 - n1))` by
       (irule range_end_words >> simp[] >> qexistsl [`get_tenv cx`, `tyv`] >> simp[]) >>
     simp[Abbr `bad1`, Abbr `bad2`, Abbr `cmp`, w2n_n2w, arithmeticTheory.LESS_MOD] >>
     Cases_on `is_signed_type fty` >> fs[]) >>
  Cases_on `n2 < n1` >- suspend "abort" >>
  `n1 <= n2` by fs[GSYM integerTheory.INT_NOT_LT] >>
  Cases_on `bound < Num (n2 - n1)` >- suspend "abort" >>
  suspend "success"
QED

Resume checked_scalar_path[abort]:
  markerLib.RESUME_TAC >>
  `?v. run_inst_seq code s = Abort Revert_abort v` by fs[] >>
  rename1 `run_inst_seq code s = Abort Revert_abort v` >>
  simp[] >> qexistsl [`v with vs_inst_idx := j`, `G`, `tn`] >>
  gen_tac >> irule checked_path_append >> qexistsl [`GA`, `tnA`, `s`] >> simp[] >>
  qpat_assum `!a t. run_inst_seq code s = Abort a t ==> _` irule >>
  first_assum ACCEPT_TAC
QED

Resume checked_scalar_path[success]:
  qpat_assum `n1 <= n2 ==> _` (drule_then strip_assume_tac) >>
  `run_inst_seq code s = OK u7` by fs[] >>
  `s.vs_inst_idx + LENGTH code = 9` by
    simp[Abbr `code`, Abbr `fullcode`, Abbr `s`, jump_to_def] >>
  qpat_assum `!t. run_inst_seq code s = OK t ==> _` (drule_then strip_assume_tac) >>
  qabbrev_tac `pre = u7 with vs_inst_idx := 9` >>
  qabbrev_tac `fin = jump_to cond_lbl pre` >>
  `pre = (jump_to entry_lbl (sA with vs_vars := u7.vs_vars)) with vs_inst_idx := 9` by
    simp[Abbr `pre`, Abbr `u7`, Abbr `u6`, Abbr `u5`, Abbr `u4`,
         Abbr `u3`, Abbr `u2`, Abbr `u1`, Abbr `s`, update_var_def, jump_to_def] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (pre,G,tn) [] (OK fin,G,tn)` by
    (gen_tac >> simp[Abbr `fin`] >> irule jmp_origin_ptr_path >>
     simp[jump_to_def] >> conj_tac >-
       (qexists `i+9` >> simp[get_instruction_def, Abbr `fullcode`]) >>
     pure_rewrite_tac[allocas_from_def, allocas_below_fmp_def] >> simp[] >>
     conj_tac >-
       (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp sA`
         (ACCEPT_TAC o REWRITE_RULE[allocas_below_fmp_def])) >>
     qpat_assum `allocas_from lo sA` (ACCEPT_TAC o REWRITE_RULE[allocas_from_def])) >>
  `!x. lookup_var x fin = lookup_var x u7 /\ lookup_var x s = lookup_var x sA` by
    simp[lookup_var_def, jump_to_def, Abbr `fin`, Abbr `s`] >>
  `FLAT (MAP (\i. i.inst_outputs) code) = [cv;rv;g1;z1;g2;z2;ev]` by
    simp[Abbr `code`, Abbr `fullcode`, mk_inst_def] >>
  `cv IN A UNION BIGUNION (set (MAP (\i. set i.inst_outputs) code)) /\
   ev IN A UNION BIGUNION (set (MAP (\i. set i.inst_outputs) code))` by
    (simp[Abbr `code`, Abbr `fullcode`, mk_inst_def] >> conj_tac
     >- (disj2_tac >> qexists `{cv}` >> simp[]) >>
     disj2_tac >> qexists `{ev}` >> simp[]) >>
  simp[] >> qexistsl [`fin`, `G`, `tn`] >>
  conj_tac >-
    (gen_tac >> irule checked_path_append >> qexistsl [`GA`, `tnA`, `s`] >>
     conj_tac >- first_assum irule >>
     irule checked_path_append >> qexistsl [`G`, `tn`, `pre`] >>
     reverse conj_tac >- first_assum irule >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,GA,tnA) [] (OK (u7 with vs_inst_idx := _),_,_)`
       (qspec_then `D` mp_tac) >>
     qpat_assum `s.vs_inst_idx + LENGTH code = 9` (pure_rewrite_tac o single) >>
     qpat_assum `Abbrev (pre = _)` (pure_rewrite_tac o single o REWRITE_RULE[markerTheory.Abbrev_def]) >>
     qpat_assum `pre = _` (pure_rewrite_tac o single) >> simp[]) >>
  `fin = jump_to cond_lbl (jump_to entry_lbl (sA with vs_vars := fin.vs_vars))` by
    simp[Abbr `fin`, jump_to_def] >>
  `op_prov G (Var cv) = NONE /\ op_taint tn (Var cv) = {} /\
   op_prov G (Var ev) = NONE /\ op_taint tn (Var ev) = {}` by
    (qpat_assum `!v. v IN A UNION _ ==> _`
       (fn th => qspec_then `cv` mp_tac th >> qspec_then `ev` mp_tac th) >> simp[]) >>
  simp[GSYM arithmeticTheory.NOT_LESS] >> gen_tac >> strip_tac >>
  qpat_assum `!v. ~MEM v (FLAT (MAP _ code)) ==> _`
    (qspec_then `x` mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> simp[]
QED

Finalise checked_scalar_path

Theorem checked_source_inv_gas_obs[local]:
  expr_sim_inv_mods mods cenv cx env (es with gas_obs := obs) <=>
  expr_sim_inv_mods mods cenv cx env es
Proof
  simp[expr_sim_inv_mods_def]
QED

(* Both failing guards produce the same target exit. The source replay
   carries the precise RuntimeError, and no gas exemption is involved. *)
Theorem checked_error_outcome[local]:
  ~s.vs_halted /\
  (!tail. source (ea with gas_obs := tail) = (INR (Error (RuntimeError msg)),ea with gas_obs := tail)) /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (Abort Revert_abort t,G1,tn1)) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source (ea,s,G,tn) Q
    (\H res ee gt r. ?ex. res = INR ex /\
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt r) /\
      halt_exit H cx ee (INR ex) r /\
      (ctx_has_dalloca ctx ==>
       !u. r = Halt u \/ (?ir. r = IntRet ir u) ==> allocas_below_fmp u))
Proof
  strip_tac >> irule gas_outcome_full_mods_exit >> simp[] >>
  qexistsl [`G1`, `ea`, `Abort Revert_abort t`, `INR (Error (RuntimeError msg))`, `tn1`] >>
  simp[exit_result_def, stmt_exit_ptr_def, exprSimDefsTheory.expr_exit_def,
       halt_exit_not_halt]
QED

Theorem range_checked_start_mods:
  lookup_block sA.vs_current_bb func.fn_blocks = SOME pre_bb /\
  get_instruction pre_bb sA.vs_inst_idx = SOME (mk_inst jmp_id JMP [Label entry_lbl] []) /\
  lookup_block entry_lbl func.fn_blocks = SOME
    <|bb_label := entry_lbl;
      bb_instructions :=
        [mk_inst i ASSIGN [op1] [cv];
         mk_inst (i+1) SUB [op2;op1] [rv];
         mk_inst (i+2) (if is_signed_type fty then SGT else GT) [op1;op2] [g1];
         mk_inst (i+3) ISZERO [Var g1] [z1];
         mk_inst (i+4) ASSERT [Var z1] [];
         mk_inst (i+5) GT [Var rv;Lit (n2w bound)] [g2];
         mk_inst (i+6) ISZERO [Var g2] [z2];
         mk_inst (i+7) ASSERT [Var z2] [];
         mk_inst (i+8) ADD [op1;Var rv] [ev];
         mk_inst (i+9) JMP [Label cond_lbl] []]|> /\
  ~sA.vs_halted /\ allocas_from lo sA /\
  eval_operand op1 sA = SOME (i2w n1) /\ eval_operand op2 sA = SOME (i2w n2) /\
  (!l. op1 <> Label l /\ op2 <> Label l) /\
  ALL_DISTINCT [p;cv;rv;g1;z1;g2;z2;ev] /\
  (!x. op1 = Var x \/ op2 = Var x ==> not_fresh_at st x) /\
  (!x. op1 = Var x \/ op2 = Var x ==>
       op_prov GA (Var x) = NONE /\ op_taint tnA (Var x) = {}) /\
  (!x. MEM x [cv;rv;g1;z1;g2;z2;ev] ==> ~not_fresh_at st x) /\
  sa.cs_next_var <= st.cs_next_var /\ st.cs_next_var <= sb0.cs_next_var /\
  local_ptrs_reserved cenv st /\
  (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at st x) /\
  (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at st x) /\
  is_int_type fty /\ evaluate_type (get_tenv cx) fty = SOME tyv /\
  value_has_type tyv (IntV n1) /\ value_has_type tyv (IntV n2) /\
  bound < dimword (:256) /\
  lookup_var p sA = SOME w /\ FLOOKUP sA.vs_allocas aid = SOME (w2n w,sz) /\
  ptr_covers GA tnA p sA sz /\
  ret_pc_ok cenv sa sA /\ return_buf_frame d cenv st sA /\ return_buf_sep d cenv ea sA /\
  body_const_cells_agree_mods mods cx env ea /\ expr_sim_inv_mods mods cenv cx env ea /\
  lookup_scopes id ea.scopes = NONE /\ storage_trace_domain cx st0 ea.storage_trace /\
  (!H. valid_horizon cx st0 H ea.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ea sA /\ immutable_frame_mods func cenv cx ea sA /\
    storage_well_formed_on cx ea (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ea GA tnA sA) /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!fn inst u. frag_reachable ctx func sA fn inst u ==> dalloca_fmp_headroom inst u) /\
  range_outer_frame_mods ctx func cenv sa es0 s0 G0 tn0 ea GA tnA sA ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (range_counter_source n1 n2 bound) (ea,sA,GA,tnA)
    (\H res ee G tn t. ?rs. res = INL rs /\
      range_header_mods mods DF lo d ctx func cenv cx env id tyv st0
        sa sb0 es0 s0 G0 tn0 n1 n2 bound cond_lbl cv ev p aid sz w H rs ee G tn t)
    (\H res ee gt r. ?ex. res = INR ex /\
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt r) /\
      halt_exit H cx ee (INR ex) r /\
      (ctx_has_dalloca ctx ==>
       !u. r = Halt u \/ (?ir. r = IntRet ir u) ==> allocas_below_fmp u))
Proof
  strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp sA` by fs[range_outer_frame_mods_def] >>
  `!x. op1 = Var x \/ op2 = Var x ==>
       ~MEM x [cv;rv;g1;z1;g2;z2;ev] /\
       op_prov GA (Var x) = NONE /\ op_taint tnA (Var x) = {}` by
    (gen_tac >> disch_tac >>
     `not_fresh_at st x` by
       (qpat_assum `!x. op1 = Var x \/ op2 = Var x ==> not_fresh_at st x`
         irule >> first_assum ACCEPT_TAC) >>
     conj_tac >- (CCONTR_TAC >> metis_tac[]) >>
     qpat_assum `!x. op1 = Var x \/ op2 = Var x ==> op_prov _ _ = _ /\ _`
       irule >> first_assum ACCEPT_TAC) >>
  `ALL_DISTINCT [cv;rv;g1;z1;g2;z2;ev] /\ ~MEM p [cv;rv;g1;z1;g2;z2;ev]` by fs[] >>
  drule_all checked_scalar_path >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
  Cases_on `n2 < n1` >- suspend "error" >>
  Cases_on `bound < Num (n2 - n1)` >- suspend "error" >>
  suspend "header"
QED

Resume range_checked_start_mods[error]:
  markerLib.RESUME_TAC >> simp[] >>
  disch_then (qx_choosel_then [`t`,`G`,`tn`] assume_tac) >>
  irule checked_error_outcome >> simp[range_counter_source_cases, raise_def] >>
  qexistsl [`G`,`t`,`tn`] >> first_assum ACCEPT_TAC
QED

Resume range_checked_start_mods[header]:
  asm_rewrite_tac[OR_CLAUSES, COND_CLAUSES] >>
  disch_then (qx_choosel_then [`t`,`G`,`tn`] strip_assume_tac) >>
  irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl [`G`, `ea`, `INL (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1)))`, `t`, `tn`] >>
  conj_tac >- simp[range_counter_source_cases, return_def] >>
  qx_gen_tac `H` >> disch_tac >> conj_tac >- first_assum irule >>
  qexists `GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1))` >> simp[] >>
  qabbrev_tac `ee = ea with gas_obs := []` >>
  qpat_assum `!H. valid_horizon cx st0 H ea.storage_trace ==> _` (drule_then strip_assume_tac) >>
  `t.vs_current_bb = cond_lbl /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
   t.vs_memory = sA.vs_memory /\ t.vs_data_section = sA.vs_data_section /\
   t.vs_allocas = sA.vs_allocas /\ t.vs_alloca_next = sA.vs_alloca_next /\
   t.vs_call_ctx = sA.vs_call_ctx /\ t.vs_accounts = sA.vs_accounts /\
   t.vs_transient = sA.vs_transient /\ t.vs_immutables = sA.vs_immutables /\
   t.vs_fmp = sA.vs_fmp /\ t.vs_initial_fmp = sA.vs_initial_fmp` by
    (qpat_assum `t = jump_to _ _` SUBST1_TAC >> simp[jump_to_def]) >>
  `!x. not_fresh_at st x ==> lookup_var x t = lookup_var x sA /\
       FLOOKUP G x = FLOOKUP GA x /\ op_taint tn (Var x) = op_taint tnA (Var x)` by
    (gen_tac >> disch_tac >> qpat_assum `!x. ~MEM x _ ==> lookup_var x t = _ /\ _` irule >>
     qpat_assum `!x. MEM x _ ==> ~not_fresh_at st x` (qspec_then `x` mp_tac) >>
     simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x sA /\
       FLOOKUP G x = FLOOKUP GA x /\ op_taint tn (Var x) = op_taint tnA (Var x)` by
    (gen_tac >> disch_tac >> first_x_assum irule >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists `sa` >> simp[]) >>
  `lookup_var p t = SOME w /\ ptr_covers G tn p t sz` by
    (qpat_assum `!x. ~MEM x _ ==> lookup_var x t = _ /\ _` (qspec_then `p` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     pure_rewrite_tac[ptr_covers_def] >>
     qpat_assum `ptr_covers GA tnA p sA sz` (mp_tac o PURE_REWRITE_RULE[ptr_covers_def]) >> simp[]) >>
  `!name x z. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var x) z) ==> not_fresh_at st x` by
    (rpt strip_tac >> qpat_assum `local_ptrs_reserved _ _`
       (strip_assume_tac o REWRITE_RULE[local_ptrs_reserved_def]) >>
     qpat_assum `!n1 n2 p sz1 sz2. FLOOKUP cenv.ce_vars n1 = _ ==> _`
       (drule_then (qspecl_then [`name`,`z`] mp_tac)) >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx ee t` by suspend "relation" >>
  qpat_x_assum `t = jump_to _ _` kall_tac >>
  `ee.scopes = ea.scopes /\ ee.storage_trace = ea.storage_trace /\ ee.immutables = ea.immutables` by
    simp[Abbr `ee`] >>
  `body_const_cells_agree_mods mods cx env ee /\ expr_sim_inv_mods mods cenv cx env ee` by
    simp[Abbr `ee`, checked_source_inv_gas_obs] >>
  `storage_well_formed_on cx ee (FST H)` by
    (`!b. get_storage cx ee b = get_storage cx ea b` by (Cases >> simp[Abbr `ee`, get_storage_def]) >>
     pure_rewrite_tac[storage_well_formed_on_def] >> simp[] >>
     qpat_assum `storage_well_formed_on cx ea _`
       (ACCEPT_TAC o PURE_REWRITE_RULE[storage_well_formed_on_def])) >>
  irule range_header_init_mods >> simp[] >> suspend "frames"
QED

Resume range_checked_start_mods[relation]:
  simp[Abbr `ee`, stmt_state_rel_start_gas_obs] >>
  qpat_assum `t = jump_to _ _` SUBST1_TAC >>
  pure_rewrite_tac[stmt_state_rel_jump_to] >> irule stmt_state_rel_vars_frame >> simp[] >>
  `!x. not_fresh_at st x ==> lookup_var x (sA with vs_vars := t.vs_vars) = lookup_var x sA` by
    (gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at st x ==> lookup_var x t = _ /\ _`
       (qspec_then `x` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
     qpat_assum `t = jump_to _ _` (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
     simp[lookup_var_def, jump_to_def]) >>
  conj_tac >- (rpt strip_tac >> first_x_assum irule >> metis_tac[]) >>
  rpt strip_tac >> first_x_assum irule >> metis_tac[local_ptrs_reserved_imm_base]
QED

Resume range_checked_start_mods[frames]:
  `immutable_frame_mods func cenv cx ee t` by
    (irule immutable_frame_mods_exterior_frame >>
     goal_assum (drule_at (Pat `immutable_frame_mods _ _ _ _ _`)) >> qexists `st` >> simp[]) >>
  `ret_pc_ok cenv sa t` by
    (irule ret_pc_ok_frame >> goal_assum (drule_at (Pat `ret_pc_ok _ _ _`)) >> simp[]) >>
  `return_buf_frame d cenv sb0 t` by
    (irule return_buf_frame_frame >>
     goal_assum (drule_at (Pat `return_buf_frame _ _ _ _`)) >> simp[]) >>
  `!name b z. local_region cenv ee.scopes t name b z <=> local_region cenv ea.scopes sA name b z` by
    (simp[] >> rpt gen_tac >> irule local_region_lookup_cong >> rpt strip_tac >>
     rename1 `lookup_var x t = lookup_var x sA` >>
     qpat_assum `!x. not_fresh_at st x ==> _ /\ _` (qspec_then `x` mp_tac) >>
     (impl_tac >- metis_tac[]) >> simp[]) >>
  `return_buf_sep d cenv ee t` by suspend "separation" >>
  `ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t` by
    (irule ghost_inv_at_mods_exterior_frame >>
     goal_assum (drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)) >> qexists `st` >> simp[]) >>
  `!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u` by
    (qpat_assum `!D. gas_origin_ptr_path _ _ _ (OK t,_,_)`
       (qspec_then `DF H` (mp_then (Pos hd) mp_tac gas_origin_ptr_path_dalloca_fmp_headroom)) >>
     qpat_assum `!fn inst u. frag_reachable ctx func sA fn inst u ==> _`
       (pure_rewrite_tac o single o EQT_INTRO) >> simp[]) >>
  `range_outer_frame_mods ctx func cenv sa es0 s0 G0 tn0 ee G tn t` by suspend "outer" >>
  simp[] >> first_assum ACCEPT_TAC
QED

Resume range_checked_start_mods[separation]:
  `!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) t` by
    (rpt strip_tac >> gvs[return_buf_sep_def, allocas_from_def] >> first_assum ACCEPT_TAC) >>
  irule return_buf_sep_transport >> simp[] >>
  qexistsl [`cenv`,`ea`,`sA`] >> simp[]
QED

Resume range_checked_start_mods[outer]:
  qhdtm_x_assum `range_outer_frame_mods` mp_tac >>
  simp[range_outer_frame_mods_def] >> strip_tac >>
  `alloca_frame cenv es0 sa s0 cenv ee t` by
    (pure_rewrite_tac[alloca_frame_def] >>
     qpat_assum `t.vs_memory = sA.vs_memory` (pure_rewrite_tac o single) >>
     qpat_assum `!name b z. local_region cenv ee.scopes t name b z <=> _`
       (pure_rewrite_tac o single) >>
     qpat_assum `alloca_frame _ _ _ _ _ _ sA`
       (ACCEPT_TAC o PURE_REWRITE_RULE[alloca_frame_def])) >>
  `alloca_history func t` by
    (irule alloca_history_jump >> simp[] >> qexists `sA` >> simp[]) >>
  `allocas_below_fmp t = allocas_below_fmp sA` by simp[allocas_below_fmp_def] >>
  simp[] >> first_assum ACCEPT_TAC
QED

Finalise range_checked_start_mods
