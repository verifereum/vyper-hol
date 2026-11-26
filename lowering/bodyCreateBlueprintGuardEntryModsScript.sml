Theory bodyCreateBlueprintGuardEntryMods
Ancestors
  bodyFullCreateHeld externalEntryShape fragExec fragGasOriginPtr
  bodyPtrBytestringBuiltinsExternalSlice stmtFragPtr dallocaBounds
  builtinCreate vyperCreate words venomState venomInst venomLayout
  bodyPtrDefs ptrDiscipline loweringShapeDefs list

(* The guard either reverts or establishes every input of the append cut. *)
Theorem blueprint_guard_append_entry:
  compile_create_blueprint_check lit target off sa = (code,sm) /\
  compile_create_blueprint_append target amount sop off code args_ptr cnt rof sm = (result,sb) /\
  fn_has_code sa sb func /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  MEM func ctx.ctx_functions /\
  gas_origin_ptr_path (D0,lo,explicit0,ctx,func,PG) (s0,G0,tn0) marks (OK s,G,tn) /\
  (!fn i v. contextRawReachable$frag_reachable ctx func s0 fn i v ==> dalloca_fmp_headroom i v) /\
  ctx_has_dalloca ctx /\ allocas_below_fmp s /\ allocas_from lo s /\
  s.vs_alloca_next <= w2n s.vs_fmp /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand target s = SOME aw /\ op_taint tn target = {} /\
  eval_operand off s = SOME ow /\ op_taint tn off = {} /\ op_prov G off = NONE /\
  code_bytes = (lookup_account (w2w aw) s.vs_accounts).code /\ LENGTH code_bytes <= 24576 /\
  eval_operand cnt s = SOME (n2w (LENGTH args)) /\ op_taint tn cnt = {} /\ op_prov G cnt = NONE /\
  LENGTH args < 2 ** 64 /\
  (!x. MEM (Var x) [target;off;args_ptr;cnt;amount] \/ sop = SOME (Var x) ==> not_fresh_at sa x) /\
  (cnt <> Lit 0w ==>
    ?q a. args_ptr = Var q /\ lookup_var q s = SOME a /\ ptr_covers G tn q s (LENGTH args) /\
      (args = [] \/ w2n a + LENGTH args <= s.vs_alloca_next) /\
      (!i. w2n a <= i /\ i < w2n a + LENGTH args ==> i NOTIN tn.t_mem) /\
      read_memory (w2n a) (LENGTH args) s = args) ==>
  let n = blueprint_copy_size (w2n ow) code_bytes;
      pref = take_pad_0 (blueprint_copy_size (w2n ow) code_bytes) (DROP (w2n ow) code_bytes) in
  if (if lit then blueprint_size_ok n else w2n ow < LENGTH code_bytes) then
    ?u Gu tu.
      (cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
       (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu)) /\
       (u = s with <|vs_vars := u.vs_vars; vs_inst_idx := LENGTH sm.cs_current_insts|>) /\
       tu.t_mem = tn.t_mem /\ tu.t_stor = tn.t_stor /\ tu.t_trans = tn.t_trans /\ tu.t_imm = tn.t_imm /\
       (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
         FLOOKUP Gu x = FLOOKUP G x /\ op_taint tu (Var x) = op_taint tn (Var x))) /\
      (compile_create_blueprint_append target amount sop off code args_ptr cnt rof sm = (result,sb) /\
       fn_has_code sm sb func /\
       (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
       MEM func ctx.ctx_functions /\
       gas_origin_ptr_path (D0,lo,explicit0,ctx,func,PG) (s0,G0,tn0) marks (OK u,Gu,tu) /\
       (!fn i v. contextRawReachable$frag_reachable ctx func s0 fn i v ==> dalloca_fmp_headroom i v) /\
       ctx_has_dalloca ctx /\ allocas_below_fmp u /\ allocas_from lo u /\
       u.vs_alloca_next <= w2n u.vs_fmp /\
       ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\ u.vs_inst_idx = LENGTH sm.cs_current_insts /\
       eval_operand target u = SOME aw /\ op_taint tu target = {} /\
       eval_operand off u = SOME ow /\ op_taint tu off = {} /\
       take_pad_0 (LENGTH pref) (DROP (w2n ow) (lookup_account (w2w aw) u.vs_accounts).code) = pref /\
       eval_operand code u = SOME (n2w (LENGTH pref)) /\
       eval_operand cnt u = SOME (n2w (LENGTH args)) /\
       op_taint tu code = {} /\ op_taint tu cnt = {} /\
       op_prov Gu code = NONE /\ op_prov Gu cnt = NONE /\
       (!x. MEM (Var x) [target;off;code;args_ptr;cnt] ==> not_fresh_at sm x) /\
       (cnt <> Lit 0w ==>
         ?q a. args_ptr = Var q /\ lookup_var q u = SOME a /\ ptr_covers Gu tu q u (LENGTH args) /\
           (args = [] \/ w2n a + LENGTH args <= u.vs_alloca_next) /\
           (!i. w2n a <= i /\ i < w2n a + LENGTH args ==> i NOTIN tu.t_mem) /\
           read_memory (w2n a) (LENGTH args) u = args) /\
       LENGTH pref + LENGTH args < dimword (:256) /\
       venomLayout$ceil32 (LENGTH pref + LENGTH args) <= 2 ** 255 + 2 ** 64)
  else ?t H z. !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (Abort Revert_abort t,H,z)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> simp[NoAsms] >>
  `cs_extends sa sm` by
    metis_tac[compile_create_blueprint_check_labels,pairTheory.SND] >>
  `cs_extends sm sb` by
    metis_tac[compile_create_blueprint_append_labels,pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `!x. off = Var x ==> not_fresh_at sa x` by
    (rpt strip_tac >> first_x_assum irule >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by simp[] >>
  drule_all create_blueprint_check_path >> simp[NoAsms] >>
  qabbrev_tac `n = blueprint_copy_size (w2n ow) code_bytes` >>
  qabbrev_tac `good = if lit then blueprint_size_ok n else w2n ow < LENGTH code_bytes` >>
  Cases_on `good` >> simp[NoAsms] >- suspend "success" >>
  disch_then (qspec_then `PG` ACCEPT_TAC)
QED

Resume blueprint_guard_append_entry[success]:
  disch_then (qspec_then `PG` (qx_choosel_then [`u`,`Gu`,`tu`]
    (map_every assume_tac o CONJUNCTS))) >>
  `u.vs_labels = s.vs_labels /\ u.vs_fmp = s.vs_fmp /\ u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_allocas = s.vs_allocas /\ u.vs_accounts = s.vs_accounts /\
   u.vs_initial_fmp = s.vs_initial_fmp /\ u.vs_memory = s.vs_memory /\
   ~u.vs_halted /\ u.vs_inst_idx = LENGTH sm.cs_current_insts /\
   allocas_from lo u /\ allocas_below_fmp u` by
    (qpat_assum `u = _ with <|vs_vars := _; vs_inst_idx := _|>`
       (PURE_ONCE_REWRITE_TAC o single) >>
     fs[allocas_from_def,allocas_below_fmp_def] >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
    eval_operand op u = eval_operand op s /\ op_prov Gu op = op_prov G op /\
    op_taint tu op = op_taint tn op` by
    (match_mp_tac reserved_operand_ghost_frame >> simp[]) >>
  `!x. MEM (Var x) [target;off;args_ptr;cnt] ==> not_fresh_at sa x` by
    (gen_tac >> disch_tac >>
     qpat_assum `!x. MEM (Var x) _ \/ _ ==> not_fresh_at sa x` irule >>
     fs[] >> metis_tac[]) >>
  `!op. MEM op [target;off;args_ptr;cnt] ==>
    eval_operand op u = eval_operand op s /\ op_prov Gu op = op_prov G op /\
    op_taint tu op = op_taint tn op` by
    (gen_tac >> strip_tac >> first_x_assum irule >> metis_tac[]) >>
  `eval_operand target u = SOME aw /\ eval_operand off u = SOME ow /\
   eval_operand cnt u = SOME (n2w (LENGTH args)) /\ op_prov Gu cnt = NONE /\
   op_taint tu target = {} /\ op_taint tu off = {} /\ op_taint tu cnt = {}` by
    (rpt conj_tac >> metis_tac[MEM]) >>
  suspend "saved"
QED

Resume blueprint_guard_append_entry[saved]:
  `cnt <> Lit 0w ==>
    ?q a. args_ptr = Var q /\ lookup_var q u = SOME a /\ ptr_covers Gu tu q u (LENGTH args) /\
      (args = [] \/ w2n a + LENGTH args <= u.vs_alloca_next) /\
      (!i. w2n a <= i /\ i < w2n a + LENGTH args ==> i NOTIN tu.t_mem) /\
      read_memory (w2n a) (LENGTH args) u = args` by
    (disch_tac >>
     qpat_assum `cnt <> Lit 0w ==> _`
       (drule_then (qx_choosel_then [`q`,`a`] (map_every assume_tac o CONJUNCTS))) >>
     `not_fresh_at sa q` by metis_tac[MEM] >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x u = _ /\ _`
       (drule_then strip_assume_tac) >>
     `ptr_covers Gu tu q u (LENGTH args)` by
       (rewrite_tac[ptr_covers_def] >>
        map_every (fn pat => qpat_assum pat (PURE_ONCE_REWRITE_TAC o single))
          [`lookup_var q u = _`, `FLOOKUP Gu q = _`, `op_taint tu (Var q) = _`] >>
        qpat_assum `ptr_covers G tn q s _` (ACCEPT_TAC o REWRITE_RULE[ptr_covers_def])) >>
     `read_memory (w2n a) (LENGTH args) u = args` by
       (rewrite_tac[read_memory_def] >>
        qpat_assum `u.vs_memory = s.vs_memory` SUBST1_TAC >>
        qpat_assum `read_memory _ _ s = args` (ACCEPT_TAC o REWRITE_RULE[read_memory_def])) >>
     qexistsl [`q`,`a`] >> simp[IgnAsm `u = _`] >>
     qpat_assum `args = [] \/ _` mp_tac >> simp[NoAsms,arithmeticTheory.ADD_COMM]) >>
  `gas_origin_ptr_path (D0,lo,explicit0,ctx,func,PG) (s0,G0,tn0) marks (OK u,Gu,tu)` by
    (`gas_origin_ptr_path (D0,lo,explicit0,ctx,func,PG) (s0,G0,tn0) (marks ++ []) (OK u,Gu,tu)`
       suffices_by simp[] >>
     drule gas_origin_ptr_path_append >> disch_then irule >> simp[] >> first_assum MATCH_ACCEPT_TAC) >>
  suspend "finish"
QED

Resume blueprint_guard_append_entry[finish]:
  qabbrev_tac `prefix = take_pad_0 n (DROP (w2n ow) code_bytes)` >>
  `LENGTH prefix = n` by simp[Abbr `prefix`] >>
  `take_pad_0 (LENGTH prefix) (DROP (w2n ow) (lookup_account (w2w aw) u.vs_accounts).code) = prefix` by
    simp[Abbr `prefix`,IgnAsm `u = _`] >>
  `!x. MEM (Var x) [target;off;code;args_ptr;cnt] ==> not_fresh_at sm x` by
    (simp[MEM] >> metis_tac[not_fresh_at_mono,MEM]) >>
  `n + LENGTH args < dimword (:256)` by
    (qpat_assum `n < _` mp_tac >> qpat_assum `LENGTH args < _` mp_tac >>
     simp[NoAsms, wordsTheory.dimword_def] >> decide_tac) >>
  `venomLayout$ceil32 (n + LENGTH args) <= 2 ** 255 + 2 ** 64` by
    (qspecl_then [`n + LENGTH args`,`2 ** 250 + 2 ** 59`] mp_tac
       (GEN_ALL ceil32_le_multiple) >>
     (impl_tac >-
       (qpat_assum `n < _` mp_tac >>
        qpat_assum `LENGTH args < _` mp_tac >>
        simp[NoAsms] >> decide_tac)) >>
     simp[NoAsms]) >>
  qexistsl [`u`,`Gu`,`tu`] >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[IgnAsm `u = _`])
  >- (qpat_assum `Abbrev (prefix = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
      qpat_assum `code_bytes = _` SUBST1_TAC >> REFL_TAC)
  >- (qpat_assum `cnt <> Lit 0w ==> ?q a. _ /\ lookup_var q u = _ /\ _` mp_tac >>
      qpat_assum `u.vs_alloca_next = s.vs_alloca_next` SUBST1_TAC >>
      qpat_assum `tu.t_mem = tn.t_mem` SUBST1_TAC >> simp[NoAsms]) >>
  qpat_assum `venomLayout$ceil32 (n + LENGTH args) <= _` (ACCEPT_TAC o SRULE [])
QED

Finalise blueprint_guard_append_entry
