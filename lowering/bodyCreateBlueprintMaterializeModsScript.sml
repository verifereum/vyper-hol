(* The instruction-only blueprint append, stopping before dispatch. *)
Theory bodyCreateBlueprintMaterializeMods
Ancestors
  bodyFullCreateHeld[qualified] bodyCreateBlueprintAddMods[qualified]
  bodyCreateDynamicExtcodecopyMods[qualified] bodyCreateDallocaCutMods[qualified]
  bodyFullDynamicBuffer[qualified] dallocaCreateGeometry[qualified]
  bodyPtrMakeArrayEmission[qualified] emitHelperProps[qualified]
  externalEntryShape[qualified] exprSimAccounts[qualified] stmtSimAugAssignPlace[qualified]
  loweringShapeRules[qualified] stmtFragPtr[qualified] fragExec[qualified]
  fragGasOriginPtr[qualified] evmStepSim[qualified] memoryReadProps[qualified]
  builtinCreate compileEnv loweringStateRelDefs venomExecSemantics venomState venomInst
  codegenRel contextCodegenRel context emitHelper bodyPtrDefs ptrDiscipline memSafeRun
  unitTransformDefs venomMemDefs venomMemProps words finite_map list arithmetic

Theorem blueprint_materialize_no_phi:
  compile_create_blueprint_append target amount sop off code args_ptr cnt rof sa = (result,sb) /\
  fn_has_code sa sb func /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  MEM func ctx.ctx_functions /\
  gas_origin_ptr_path (D0,lo,explicit0,ctx,func,PG) (s0,G0,tn0) marks (OK s,G,tn) /\
  (!fn i v. contextRawReachable$frag_reachable ctx func s0 fn i v ==> dalloca_fmp_headroom i v) /\
  ctx_has_dalloca ctx /\ allocas_below_fmp s /\ allocas_from lo s /\
  s.vs_alloca_next <= w2n s.vs_fmp /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand target s = SOME aw /\ op_taint tn target = {} /\
  eval_operand off s = SOME ow /\ op_taint tn off = {} /\
  take_pad_0 (LENGTH prefix) (DROP (w2n ow) (lookup_account (w2w aw) s.vs_accounts).code) = prefix /\
  eval_operand code s = SOME (n2w (LENGTH prefix)) /\
  eval_operand cnt s = SOME (n2w (LENGTH args)) /\
  op_taint tn code = {} /\ op_taint tn cnt = {} /\
  op_prov G code = NONE /\ op_prov G cnt = NONE /\
  (!x. MEM (Var x) [target;off;code;args_ptr;cnt] ==> not_fresh_at sa x) /\
  (cnt <> Lit 0w ==>
    ?q a. args_ptr = Var q /\ lookup_var q s = SOME a /\ ptr_covers G tn q s (LENGTH args) /\
      (args = [] \/ w2n a + LENGTH args <= s.vs_alloca_next) /\
      (!i. w2n a <= i /\ i < w2n a + LENGTH args ==> i NOTIN tn.t_mem) /\
      read_memory (w2n a) (LENGTH args) s = args) /\
  LENGTH prefix + LENGTH args < dimword (:256) /\
  venomLayout$ceil32 (LENGTH prefix + LENGTH args) <= 2 ** 255 + 2 ** 64 ==>
  ?sc p size t H z.
    compile_create_dispatch (Var p) size amount sop rof sc = (result,sb) /\
    fn_has_code sc sb func /\ cs_extends sa sc /\ sa.cs_next_var <= sc.cs_next_var /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,H,z)) /\
    ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\ t.vs_inst_idx = LENGTH sc.cs_current_insts /\
    (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx;
              vs_memory := s.vs_memory; vs_fmp := s.vs_fmp|>) = s /\
    lookup_var p t = SOME s.vs_fmp /\ ptr_covers H z p t (LENGTH prefix + LENGTH args) /\
    eval_operand size t = SOME (n2w (LENGTH prefix + LENGTH args)) /\ op_taint z size = {} /\
    (!x. Var x = size \/ x = p ==> not_fresh_at sc x) /\
    w2n s.vs_initial_fmp <= w2n s.vs_fmp /\
    w2n t.vs_fmp = w2n s.vs_fmp + venomLayout$ceil32 (LENGTH prefix + LENGTH args) /\
    w2n s.vs_fmp + LENGTH prefix + LENGTH args <= LENGTH t.vs_memory /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    read_memory (w2n s.vs_fmp) (LENGTH prefix + LENGTH args) t = prefix ++ args /\
    (!j k. j+k <= w2n s.vs_fmp ==> read_memory j k t = read_memory j k s) /\
    (!i. w2n s.vs_fmp <= i /\ i < w2n s.vs_fmp + LENGTH prefix + LENGTH args ==> i NOTIN z.t_mem) /\
    (!i. i < w2n s.vs_fmp /\ i IN z.t_mem ==> i IN tn.t_mem) /\
    z.t_stor = tn.t_stor /\ z.t_trans = tn.t_trans /\ z.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint z (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule dallocaCreateGeometryTheory.create_blueprint_create_prefix >>
  disch_then (qx_choosel_then [`tot_op`,`sm`,`buf`,`sn`,`se`,`sc`,`created`,`sd`]
    (map_every assume_tac o CONJUNCTS)) >>
  `compile_create_dispatch buf tot_op amount sop rof sc = (result,sb)` by
    (Cases_on `sop` >> fs[compile_create_dispatch_def,comp_bind_def]) >>
  `cs_extends sc sb` by
    (qspecl_then [`buf`,`tot_op`,`amount`,`sop`,`rof`,`sc`] mp_tac
       externalEntryShapeTheory.compile_create_dispatch_labels >> simp[]) >>
  suspend "layout"
QED

Resume blueprint_materialize_no_phi[layout]:
  qpat_x_assum `compile_alloc_dynamic _ _ = _`
    (assume_tac o REWRITE_RULE [compile_alloc_dynamic_def]) >>
  `cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn se /\ cs_extends se sc /\
   sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var /\
   sn.cs_next_var <= se.cs_next_var /\ se.cs_next_var <= sc.cs_next_var` by
    (Cases_on `cnt = Lit 0w` >> gvs[cs_extends_refl] >>
     RULE_ASSUM_TAC (REWRITE_RULE [compile_copy_memory_dynamic_def]) >>
     imp_res_tac exprSimAccountsTheory.emit_op_extends_next_var >>
     imp_res_tac stmtSimAugAssignPlaceTheory.aug_place_emit_void_grows >>
     imp_res_tac (cj 3 emitHelperPropsTheory.emitted_insts_emit_void) >>
     fs[] >> rpt conj_tac >> TRY decide_tac >>
     irule cs_extends_trans >> first_assum (irule_at Any) >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func /\ fn_has_code sn se func /\
   fn_has_code se sc func /\ fn_has_code sc sb func` by
    (ntac 4 (imp_res_tac cs_extends_trans) >>
     rpt conj_tac >> irule fragExecTheory.fn_has_code_mid >>
     qpat_assum `fn_has_code sa sb func` (irule_at Any) >>
     simp[cs_extends_refl]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by simp[] >>
  drule_all bodyCreateBlueprintAddModsTheory.blueprint_add_path_physical >>
  disch_then (qspec_then `PG` (qx_choosel_then [`tot_var`,`u`,`Gu`,`tu`]
    (map_every assume_tac o CONJUNCTS))) >>
  suspend "total"
QED

Resume blueprint_materialize_no_phi[total]:
  qabbrev_tac `N = LENGTH prefix + LENGTH args` >>
  qabbrev_tac `B = w2n s.vs_fmp` >>
  `eval_operand tot_op u = SOME (n2w N)` by
    simp[Abbr `N`,IgnAsm `u = _`,word_add_n2w] >>
  `w2n (n2w N:bytes32) = N` by fs[w2n_n2w] >>
  `w2n (n2w (LENGTH prefix):bytes32) = LENGTH prefix` by
    (fs[Abbr `N`,IgnAsm `prefix = _`,w2n_n2w] >> decide_tac) >>
  `~u.vs_halted /\ u.vs_inst_idx = LENGTH sm.cs_current_insts /\
   allocas_from lo u /\ allocas_below_fmp u /\ u.vs_fmp = s.vs_fmp /\
   u.vs_initial_fmp = s.vs_initial_fmp /\ u.vs_alloca_next = s.vs_alloca_next` by
    (fs[update_var_def,allocas_from_def,allocas_below_fmp_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `gas_origin_ptr_path (D0,lo,explicit0,ctx,func,PG) (s0,G0,tn0) marks (OK u,Gu,tu)` by
    metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append,APPEND_NIL] >>
  drule_all bodyPtrMakeArrayEmissionTheory.emit_op_fetch_boundary >>
  disch_then (qx_choosel_then [`p`,`bb`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `buf = Var p` SUBST_ALL_TAC >>
  qabbrev_tac `i = mk_inst sm.cs_next_id DALLOCA [tot_op] [p]` >>
  `i.inst_opcode = DALLOCA /\ i.inst_operands = [tot_op] /\ i.inst_outputs = [p]` by
    simp[Abbr `i`,mk_inst_def] >>
  `venomLayout$ceil32 (w2n (n2w N:bytes32)) <= 2 ** 255 + 2 ** 64` by
    asm_rewrite_tac[] >>
  drule_all (Q.INST [`s` |-> `u`, `inst` |-> `i`,
    `n` |-> `w2n (n2w N:bytes32)`] bodyCreateDallocaCutModsTheory.create_dalloca_cut_bound_no_phi) >>
  strip_tac >>
  drule_all (Q.INST [`s` |-> `u`, `tn` |-> `tu`]
    bodyFullDynamicBufferTheory.dalloca_origin_region_exact) >>
  disch_then (qspecl_then [`PG`,`Gu`]
    (qx_choosel_then [`v`,`Gv`,`tv`] (map_every assume_tac o CONJUNCTS))) >>
  suspend "allocated"
QED

Resume blueprint_materialize_no_phi[allocated]:
  `not_fresh_at sn p` by
    (drule (cj 4 emitHelperPropsTheory.emitted_insts_emit_op) >>
     simp[loweringShapeRulesTheory.fresh_output_props]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
  `!x. not_fresh_at sa x ==> lookup_var x v = lookup_var x s /\
     FLOOKUP Gv x = FLOOKUP G x /\ op_taint tv (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     `x <> p /\ x <> tot_var` by metis_tac[] >>
     qpat_assum `!x. x <> p ==> _` (drule_then strip_assume_tac) >>
     qpat_assum `!x. x <> tot_var ==> _` (drule_then strip_assume_tac) >>
     simp[IgnAsm `v = _`,IgnAsm `u = _`]) >>
  `v.vs_labels = s.vs_labels /\ v.vs_accounts = s.vs_accounts /\
   v.vs_memory = s.vs_memory /\ v.vs_initial_fmp = s.vs_initial_fmp /\
   v.vs_alloca_next = s.vs_alloca_next /\ allocas_from lo v` by
    (fs[update_var_def,allocas_from_def] >> first_assum ACCEPT_TAC) >>
  `!x. (!p. x = Var p ==> not_fresh_at sa p) ==>
     eval_operand x v = eval_operand x s /\ op_taint tv x = op_taint tn x /\
     op_prov Gv x = op_prov G x` by
    (Cases >> simp[eval_operand_def,op_taint_def,op_prov_def,IgnAsm `v = _`,IgnAsm `u = _`] >>
     rpt strip_tac >> first_x_assum drule >> simp[op_taint_def]) >>
  `eval_operand target v = SOME aw /\ eval_operand off v = SOME ow /\
   eval_operand code v = SOME (n2w (LENGTH prefix)) /\
   eval_operand cnt v = SOME (n2w (LENGTH args)) /\
   op_taint tv target = {} /\ op_taint tv off = {} /\
   op_taint tv code = {} /\ op_taint tv cnt = {} /\ op_prov Gv code = NONE` by
    (qpat_assum `!x. (!p. x = Var p ==> _) ==> _`
       (fn th => map_every (fn a => qspec_then a mp_tac th) [`target`,`off`,`code`,`cnt`]) >>
     qpat_assum `!x. MEM (Var x) _ ==> _` (mp_tac o SIMP_RULE bool_ss [MEM]) >>
     simp[IgnAsm `v = _`,IgnAsm `u = _`] >> metis_tac[]) >>
  `w2n s.vs_initial_fmp <= B` by
    (qpat_assum `allocas_below_fmp s` (mp_tac o REWRITE_RULE [allocas_below_fmp_def]) >>
     simp[Abbr `B`]) >>
  `w2n v.vs_fmp = B + venomLayout$ceil32 N` by
    (qpat_assum `w2n v.vs_fmp = _` mp_tac >>
     simp[Abbr `B`,IgnAsm `v = _`,IgnAsm `u = _`]) >>
  `N <= venomLayout$ceil32 N` by simp[venomLayoutTheory.ceil32_ge] >>
  `LENGTH prefix <= N` by simp[Abbr `N`] >>
  `B + LENGTH prefix <= w2n v.vs_fmp /\ B + N <= w2n v.vs_fmp` by decide_tac >>
  `ptr_covers Gv tv p v (w2n (n2w (LENGTH prefix):bytes32))` by
    (qpat_assum `ptr_covers Gv tv p v _` (mp_tac o REWRITE_RULE [ptr_covers_def]) >>
     simp[ptr_covers_def,IgnAsm `prefix = _`,IgnAsm `v = _`,IgnAsm `u = _`] >>
     decide_tac) >>
  suspend "copy_code"
QED

Resume blueprint_materialize_no_phi[copy_code]:
  `eval_operand (Var p) v = SOME s.vs_fmp` by
    simp[eval_operand_def,IgnAsm `v = _`,IgnAsm `u = _`] >>
  `v.vs_current_bb = sn.cs_current_bb /\ v.vs_inst_idx = LENGTH sn.cs_current_insts` by
    simp[IgnAsm `v = _`,IgnAsm `u = _`] >>
  `w2n v.vs_initial_fmp <= w2n s.vs_fmp /\
   w2n s.vs_fmp + w2n (n2w (LENGTH prefix):bytes32) <= w2n v.vs_fmp` by
    simp[GSYM markerTheory.Abbrev_def,IgnAsm `prefix = _`,IgnAsm `v = _`,IgnAsm `u = _`,Abbr `B`] >>
  drule_all bodyCreateDynamicExtcodecopyModsTheory.create_dynamic_extcodecopy_path_physical >>
  disch_then (qspec_then `PG` mp_tac) >>
  simp[IgnAsm `v = _`,IgnAsm `u = _`,evmStepSimTheory.take_pad_replicate] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `y = write_memory_with_expansion B prefix v with vs_inst_idx := LENGTH se.cs_current_insts` >>
  qabbrev_tac `ty = tv with t_mem := tv.t_mem DIFF {i | B <= i /\ i < B + LENGTH prefix}` >>
  suspend "written"
QED

Resume blueprint_materialize_no_phi[written]:
  `y.vs_current_bb = se.cs_current_bb /\ y.vs_inst_idx = LENGTH se.cs_current_insts /\
   ~y.vs_halted /\ y.vs_fmp = v.vs_fmp /\ y.vs_initial_fmp = s.vs_initial_fmp /\
   y.vs_allocas = v.vs_allocas /\ y.vs_alloca_next = s.vs_alloca_next /\
   y.vs_labels = v.vs_labels /\ (!x. lookup_var x y = lookup_var x v)` by
    simp[Abbr `y`,write_memory_with_expansion_def,lookup_var_def,IgnAsm `v = _`,IgnAsm `u = _`] >>
  `!x. op_taint ty x = op_taint tv x` by (Cases >> simp[Abbr `ty`,op_taint_def]) >>
  `allocas_from lo y /\ allocas_below_fmp y` by
    metis_tac[allocas_from_def,allocas_below_fmp_def] >>
  `B + LENGTH prefix <= LENGTH y.vs_memory /\ LENGTH s.vs_memory <= LENGTH y.vs_memory` by
    simp[Abbr `y`,LENGTH_write_memory_with_expansion,MAX_DEF,IgnAsm `v = _`,IgnAsm `u = _`] >>
  `!j k. read_memory j k y = read_memory j k (write_memory_with_expansion B prefix v)` by
    simp[Abbr `y`,read_memory_def,IgnAsm `v = _`,IgnAsm `u = _`] >>
  `read_memory B (LENGTH prefix) y = prefix` by
    simp[memoryReadPropsTheory.read_memory_write_self,IgnAsm `prefix = _`] >>
  `!j k. j+k <= B ==> read_memory j k y = read_memory j k s` by
    (rpt strip_tac >>
     qpat_assum `!j k. read_memory j k y = _` (PURE_ONCE_REWRITE_TAC o single) >>
     simp[memoryReadPropsTheory.read_memory_write_disjoint] >>
     simp[read_memory_def,IgnAsm `v = _`,IgnAsm `u = _`]) >>
  `!i. i < B /\ i IN ty.t_mem ==> i IN tn.t_mem` by
    (simp[Abbr `ty`,IgnAsm `u = _`,IgnAsm `v = _`] >>
     rpt strip_tac >> decide_tac) >>
  suspend "args"
QED

Resume blueprint_materialize_no_phi[args]:
  `!x. not_fresh_at sa x ==> lookup_var x y = lookup_var x s /\
        FLOOKUP Gv x = FLOOKUP G x /\ op_taint ty (Var x) = op_taint tn (Var x)` by
    metis_tac[] >>
  `cnt <> Lit 0w ==>
    ?q a. args_ptr = Var q /\ lookup_var q y = SOME a /\ ptr_covers Gv ty q y (LENGTH args) /\
       (args = [] \/ w2n a + LENGTH args <= y.vs_alloca_next) /\
       (!i. w2n a <= i /\ i < w2n a + LENGTH args ==> i NOTIN ty.t_mem) /\
       read_memory (w2n a) (LENGTH args) y = args` by
    (disch_tac >> qpat_assum `cnt <> Lit 0w ==> _` drule >>
     disch_then (qx_choosel_then [`q`,`a`] (map_every assume_tac o CONJUNCTS)) >>
     `not_fresh_at sa q` by metis_tac[MEM] >>
     `lookup_var q y = SOME a /\ ptr_covers Gv ty q y (LENGTH args)` by
       (qpat_assum `!x. not_fresh_at sa x ==> lookup_var x y = _ /\ _` (drule_then strip_assume_tac) >>
        qpat_assum `ptr_covers G tn q s _` (mp_tac o REWRITE_RULE [ptr_covers_def]) >>
        simp[ptr_covers_def,IgnAsm `v = _`,IgnAsm `u = _`]) >>
     qexistsl [`q`,`a`] >> simp[IgnAsm `prefix = _`,IgnAsm `v = _`,IgnAsm `u = _`] >>
     Cases_on `args = []` >- simp[read_memory_def] >>
     `w2n a + LENGTH args <= s.vs_alloca_next` by
       (qpat_assum `args = [] \/ _` mp_tac >>
        qpat_assum `args <> []` (fn th => simp[NoAsms,th])) >>
     `w2n a + LENGTH args <= B` by decide_tac >>
     conj_tac >- (disj2_tac >> decide_tac) >>
     conj_tac >- (rpt strip_tac >> rename1 `j IN ty.t_mem` >>
        `j < B` by decide_tac >>
        qpat_assum `!i. i < B /\ i IN ty.t_mem ==> _` (drule_all_then assume_tac) >>
        qpat_assum `!i. w2n a <= i /\ i < _ ==> i NOTIN tn.t_mem` (qspec_then `j` mp_tac) >>
        simp[] >> decide_tac) >>
     simp[memoryReadPropsTheory.read_memory_write_disjoint,IgnAsm `prefix = _`,
          IgnAsm `v = _`,IgnAsm `u = _`] >>
     qpat_assum `read_memory (w2n a) (LENGTH args) s = args` mp_tac >>
     qpat_assum `v.vs_memory = s.vs_memory` (fn th => simp[NoAsms,read_memory_def,th])) >>
  `ptr_covers Gv ty p y (LENGTH prefix + LENGTH args)` by
    (qpat_assum `ptr_covers Gv tv p v (w2n (n2w N))` (mp_tac o REWRITE_RULE [ptr_covers_def]) >>
     simp[ptr_covers_def,Abbr `N`,IgnAsm `prefix = _`,IgnAsm `v = _`,IgnAsm `u = _`]) >>
  `!x. MEM (Var x) [Var p;args_ptr;cnt] ==> not_fresh_at se x` by
    (simp[] >> metis_tac[stmtFragPtrTheory.not_fresh_at_mono,MEM]) >>
  `!x. eval_operand x y = eval_operand x v` by
    (Cases >> simp[eval_operand_def,IgnAsm `u = _`,IgnAsm `v = _`]) >>
  `lookup_var p y = SOME s.vs_fmp /\ eval_operand code y = SOME (n2w (LENGTH prefix)) /\
   op_prov Gv code = NONE /\ op_taint ty code = {} /\
   eval_operand cnt y = SOME (n2w (LENGTH args)) /\ op_taint ty cnt = {}` by
    simp[IgnAsm `prefix = _`,IgnAsm `u = _`,IgnAsm `v = _`] >>
  `w2n y.vs_initial_fmp <= w2n s.vs_fmp /\
   w2n s.vs_fmp + LENGTH prefix + LENGTH args <= w2n y.vs_fmp /\
   w2n s.vs_fmp + LENGTH prefix <= LENGTH y.vs_memory /\
   read_memory (w2n s.vs_fmp) (LENGTH prefix) y = prefix` by
    (simp[Abbr `N`,Abbr `B`,IgnAsm `prefix = _`,IgnAsm `u = _`,IgnAsm `v = _`] >>
     qspec_then `LENGTH args + LENGTH prefix` mp_tac (GEN_ALL venomLayoutTheory.ceil32_ge) >> decide_tac) >>
  `LENGTH prefix + LENGTH args < dimword (:256)` by simp[Abbr `N`,IgnAsm `prefix = _`] >>
  drule_all bodyFullCreateHeldTheory.create_blueprint_args_append_path >>
  disch_then (qspec_then `PG` (qx_choosel_then [`t`,`H`,`z`] (map_every assume_tac o CONJUNCTS))) >>
  suspend "finish"
QED

Resume blueprint_materialize_no_phi[finish]:
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (v,Gv,tv) [] (OK y,Gv,ty)` by
    simp[Abbr `ty`,IgnAsm `prefix = _`,IgnAsm `u = _`,IgnAsm `v = _`] >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,H,z)` by
    (rpt gen_tac >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) [] _`
         (qspecl_then [`D`,`explicit`] mp_tac) >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (u,Gu,tu) [] _`
         (qspecl_then [`D`,`explicit`] mp_tac) >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (v,Gv,tv) [] (OK y,Gv,ty)`
         (qspecl_then [`D`,`explicit`] mp_tac) >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (y,Gv,ty) [] _`
         (qspecl_then [`D`,`explicit`] mp_tac) >>
     POP_ASSUM_LIST kall_tac >> metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append,APPEND]) >>
  `t = y with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx; vs_memory := t.vs_memory|>` by
    (qpat_assum `_ with <|vs_vars := y.vs_vars; vs_inst_idx := y.vs_inst_idx; vs_memory := y.vs_memory|> = y`
       (mp_tac o AP_TERM ``\st. st with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx;
                                            vs_memory := t.vs_memory|>``) >> simp[NoAsms]) >>
  `(t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx;
             vs_memory := s.vs_memory; vs_fmp := s.vs_fmp|>) = s` by
    (qpat_assum `t = _ with <|vs_vars := _; vs_inst_idx := _; vs_memory := _|>`
       (PURE_ONCE_REWRITE_TAC o single) >>
     qpat_assum `Abbrev (y = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_assum `v = update_var _ _ _ with vs_inst_idx := _` (PURE_ONCE_REWRITE_TAC o single) >>
     qpat_assum `u = update_var _ _ _ with vs_inst_idx := _` (PURE_ONCE_REWRITE_TAC o single) >>
     simp[NoAsms,write_memory_with_expansion_def,update_var_def]) >>
  `~t.vs_halted /\ t.vs_fmp = v.vs_fmp` by
    (qpat_assum `t = _ with <|vs_vars := _; vs_inst_idx := _; vs_memory := _|>`
       (PURE_ONCE_REWRITE_TAC o single) >> simp[IgnAsm `t = _`]) >>
  suspend "results"
QED

Resume blueprint_materialize_no_phi[results]:
  `sn.cs_next_var <= sc.cs_next_var /\ sm.cs_next_var <= se.cs_next_var /\
   sm.cs_next_var <= sc.cs_next_var /\ sa.cs_next_var <= se.cs_next_var /\
   sa.cs_next_var <= sc.cs_next_var` by
    (map_every (fn a => qpat_assum a mp_tac)
       [`sa.cs_next_var <= sm.cs_next_var`, `sm.cs_next_var <= sn.cs_next_var`,
        `sn.cs_next_var <= se.cs_next_var`, `se.cs_next_var <= sc.cs_next_var`] >>
     POP_ASSUM_LIST kall_tac >> decide_tac) >>
  `not_fresh_at se p /\ not_fresh_at sc p /\ not_fresh_at se tot_var /\
   not_fresh_at sc tot_var` by
    (rpt conj_tac >> irule stmtFragPtrTheory.not_fresh_at_mono >>
     TRY (qexists `sn` >> simp[] >> NO_TAC) >> qexists `sm` >> simp[]) >>
  `eval_operand tot_op t = SOME (n2w N) /\ op_taint z tot_op = {}` by
    (qpat_assum `tot_op = Var tot_var` SUBST_ALL_TAC >>
     `tot_var <> p` by metis_tac[] >>
     qpat_assum `!x. not_fresh_at se x ==> _` (qspec_then `tot_var` (drule_then strip_assume_tac)) >>
     qpat_assum `!x. x <> p ==> _` (qspec_then `tot_var` (drule_then strip_assume_tac)) >>
     qpat_assum `eval_operand (Var tot_var) u = SOME (n2w N)`
        (assume_tac o REWRITE_RULE [eval_operand_def]) >>
     simp[eval_operand_def,IgnAsm `t = _`,IgnAsm `u = _`,IgnAsm `v = _`,IgnAsm `prefix = _`]) >>
  `lookup_var p t = SOME s.vs_fmp /\ ptr_covers H z p t N` by
    (qpat_assum `!x. not_fresh_at se x ==> _` (qspec_then `p` (drule_then strip_assume_tac)) >>
     qpat_assum `ptr_covers Gv ty p y (LENGTH prefix + LENGTH args)`
       (mp_tac o REWRITE_RULE [ptr_covers_def]) >>
     simp[ptr_covers_def,Abbr `N`,IgnAsm `t = _`,IgnAsm `u = _`,IgnAsm `v = _`,IgnAsm `prefix = _`]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint z (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     `not_fresh_at se x` by metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
     qpat_assum `!x. not_fresh_at se x ==> _` (qspec_then `x` (drule_then strip_assume_tac)) >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x y = _ /\ _`
       (qspec_then `x` (drule_then strip_assume_tac)) >>
     simp[IgnAsm `t = _`,IgnAsm `u = _`,IgnAsm `v = _`]) >>
  qexistsl [`sc`,`p`,`tot_op`,`t`,`H`,`z`] >>
  `cs_extends sa sc` by metis_tac[cs_extends_trans] >>
  `!x. Var x = tot_op \/ x = p ==> not_fresh_at sc x` by metis_tac[operand_11] >>
  `!i. B <= i /\ i < B + LENGTH prefix + LENGTH args ==> i NOTIN z.t_mem` by
    (qpat_assum `z.t_mem = _` (PURE_ONCE_REWRITE_TAC o single) >>
     qpat_assum `Abbrev (B = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qx_gen_tac `j` >>
     simp[NoAsms,Abbr `ty`,Abbr `B`,pred_setTheory.IN_DIFF] >>
     POP_ASSUM_LIST kall_tac >>
     Cases_on `j IN tv.t_mem` >> simp[] >> decide_tac) >>
  `!i. i < B /\ i IN z.t_mem ==> i IN tn.t_mem` by
    (qx_gen_tac `j` >>
     qpat_assum `z.t_mem = _` (PURE_ONCE_REWRITE_TAC o single) >>
     qpat_assum `!i. i < B /\ i IN ty.t_mem ==> i IN tn.t_mem` (qspec_then `j` mp_tac) >>
     simp[NoAsms,pred_setTheory.IN_DIFF,CONJ_ASSOC]) >>
  `!j k. j+k <= B ==> read_memory j k t = read_memory j k s` by
    (rpt strip_tac >>
     qpat_assum `!j k. j+k <= w2n s.vs_fmp ==> read_memory j k t = _`
       (qspecl_then [`j`,`k`] mp_tac) >>
     qpat_assum `!j k. j+k <= B ==> read_memory j k y = read_memory j k s`
       (qspecl_then [`j`,`k`] mp_tac) >>
     simp[IgnAsm `t = _`,IgnAsm `v = _`,IgnAsm `u = _`,Abbr `B`]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[IgnAsm `t = _`,IgnAsm `u = _`,IgnAsm `v = _`,IgnAsm `prefix = _`,Abbr `B`,Abbr `N`,Abbr `ty`] >>
  TRY decide_tac >>
  qpat_assum `s.vs_inst_idx = _` (fn pc =>
     qpat_assum `t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx;
                        vs_memory := s.vs_memory; vs_fmp := s.vs_fmp|> = s`
       (mp_tac o REWRITE_RULE [pc])) >> simp[NoAsms]
QED

Finalise blueprint_materialize_no_phi
