(* Uniform array element traversal with body-aware child stores. *)
Theory bodyMemArrayAdapters
Ancestors
  bodyMemArrayHeader bodyMemAggregateTraversal exprSimAggregateLayout exprSimAggregateLoops
  gasOutcome gasSummary valueEncoding vyperTypeABI exprLowering compileEnv
  exprSimDefs exprSimMemDefs loweringPosts venomState venomMemDefs
  stmtSimProps stmtSimDeclCompose exprBopSimProps exprLoweringProps
  emitHelperProps loweringSlice fragGasMode bodyDeclMemoryCompose fragExec

Theorem aggregate_make_array_elems_body_sim_mem:
  !args ce cx env elem_ty tv header idx off sa out sb es func inst x b asz s0 ctx tops st0.
  EVERY (\e. arg_type_fits (expr_type e) elem_ty) args /\
  EVERY (\e. elem_ty = expr_type e \/
    is_bytestring_type elem_ty /\ is_bytestring_type (expr_type e)) args /\
  evaluate_type (get_tenv cx) elem_ty = SOME tv /\
  type_memory_bytes ce elem_ty = type_memory_size tv /\
  off = (if header then 32 else 0) + idx * type_memory_size tv /\
  compile_make_array_elems compile_expr ce args elem_ty
    (type_memory_bytes ce elem_ty) header (Var x) idx sa = (out,sb) /\
  expr_sim_inv ce cx env es /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st) /\
  body_inv tops ctx ce cx /\ body_exprs_mem_ok cx args /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
  (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  off + LENGTH args * type_memory_size tv <= asz /\ b + asz < dimword (:256) /\
  (ce.ce_is_ctor ==>
   !name itv iv io.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
     regions_disjoint io (type_memory_size itv) (b+off)
       (LENGTH args * type_memory_size tv)) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s0 /\
    storage_well_formed_on cx es (FST H)) /\ alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  out = Var x /\
  gas_outcome T (cx_tops cx) (ctx,func) cx st0 (eval_exprs cx args) (es,s0)
    (\H res es' r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es' /\
      stmt_state_rel H ctx func ce cx es' r /\
      storage_well_formed_on cx es' (FST H) /\
      elems_in_memory vs (b+off) tv r.vs_memory /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
        lookup_var z r = SOME w) /\
      (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
        FLOOKUP r.vs_allocas aid = SOME a) /\
      (!p n. b <= p /\ p+n <= b+asz /\
        (p+n <= b+off \/ b+off+LENGTH args * type_memory_size tv <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
        aid < sa.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
        (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
          p+n <= lo \/ lo+sz <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      locals_kept ce es es' s0 r /\ alloca_history func r /\
      s0.vs_alloca_next <= r.vs_alloca_next /\
      (~EXISTS expr_has_effect args ==>
        (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
          mem_bytes_at lb lsz r.vs_memory = mem_bytes_at lb lsz s0.vs_memory) /\
        !p n. (p + n <= b \/ b + asz <= p) /\
          (!i c sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
             sa.cs_next_id <= i.inst_id /\
             FLOOKUP r.vs_allocas i.inst_id = SOME (c,sz) ==>
             regions_disjoint p n c sz) ==>
          mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory))
    (\H res es' exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`args`, `idx`] (Q.INST [`cfn` |-> `compile_expr`,
    `buf` |-> `Var x`] compile_make_array_elems_as_tuple)) >>
  strip_tac >>
  `OPT_MMAP (evaluate_type (get_tenv cx)) (REPLICATE (LENGTH args) elem_ty) =
     SOME (REPLICATE (LENGTH args) tv)` by
    (Q.SPEC_TAC (`LENGTH args`, `n`) >> Induct >> gvs[rich_listTheory.REPLICATE]) >>
  `LIST_REL (\t e. arg_type_fits (expr_type e) t)
     (REPLICATE (LENGTH args) elem_ty) args` by
    gvs[listTheory.LIST_REL_EL_EQN, rich_listTheory.EL_REPLICATE, listTheory.EVERY_EL] >>
  `LIST_REL (\t e. t = expr_type e \/
     is_bytestring_type t /\ is_bytestring_type (expr_type e))
     (REPLICATE (LENGTH args) elem_ty) args` by
    gvs[listTheory.LIST_REL_EL_EQN, rich_listTheory.EL_REPLICATE, listTheory.EVERY_EL] >>
  `compile_make_tuple compile_expr ce args (REPLICATE (LENGTH args) elem_ty)
     (Var x) off sa = (out,sb)` by
    (gvs[] >> metis_tac[]) >>
  qspecl_then [`st0`, `args`, `REPLICATE (LENGTH args) elem_ty`, `ce`, `cx`,
               `env`, `off`, `sa`, `out`, `sb`, `es`,
               `REPLICATE (LENGTH args) tv`, `func`, `inst`, `x`, `b`, `asz`,
               `s0`, `ctx`, `tops`] mp_tac aggregate_make_tuple_body_sim_mem >>
  pure_rewrite_tac[exprSimAggregateEncodingTheory.type_memory_size_list_replicate] >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> gvs[])) >>
  strip_tac >> conj_tac >- asm_rewrite_tac[] >>
  irule struct_gas_outcome_post >> goal_assum (drule_at Any) >>
  BETA_TAC >> rpt strip_tac >>
  `!vs n p. tuple_in_memory vs (REPLICATE n tv) p r.vs_memory ==>
            elems_in_memory vs p tv r.vs_memory` by
    (Induct >> Cases >>
     simp[valueEncodingDefsTheory.val_in_memory_def, rich_listTheory.REPLICATE] >>
     metis_tac[]) >>
  qexists_tac `vs` >> asm_rewrite_tac[] >> metis_tac[]
QED

Theorem array_header_frames[local]:
  32 + extent <= asz /\ sa.cs_next_id <= sm.cs_next_id /\
  sh = (mstore b w s0 with vs_inst_idx := SUC s0.vs_inst_idx) /\
  (!p n. p+n <= b \/ b+32 <= p ==>
    mem_bytes_at p n sh.vs_memory = mem_bytes_at p n s0.vs_memory) /\
  (!p n. b <= p /\ p+n <= b+asz /\
    (p+n <= b+32 \/ b+32+extent <= p) ==>
    mem_bytes_at p n r.vs_memory = mem_bytes_at p n sh.vs_memory) /\
  (!aid p n. FLOOKUP sh.vs_allocas aid = SOME (p,n) /\
    aid < sm.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
    (!name lo sz. local_region ce es.scopes sh name lo sz ==>
      p+n <= lo \/ lo+sz <= p) ==>
    mem_bytes_at p n r.vs_memory = mem_bytes_at p n sh.vs_memory) ==>
  (!p n. b <= p /\ p+n <= b+asz /\
    (p+n <= b \/ b+32+extent <= p) ==>
    mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
  (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
    aid < sa.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
    (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
      p+n <= lo \/ lo+sz <= p) ==>
    mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory)
Proof
  strip_tac >> conj_tac
  >- (rpt strip_tac >>
      `mem_bytes_at p n r.vs_memory = mem_bytes_at p n sh.vs_memory` by
        (qpat_x_assum `!p n. b <= p /\ _ ==> _` irule >> simp[] >> decide_tac) >>
      `mem_bytes_at p n sh.vs_memory = mem_bytes_at p n s0.vs_memory` by
        (qpat_x_assum `!p n. _ \/ _ ==> _` irule >> decide_tac) >> simp[]) >>
  rpt strip_tac >>
  `mem_bytes_at p n r.vs_memory = mem_bytes_at p n sh.vs_memory` by
    (qpat_x_assum `!aid p n. _ ==> _` irule >>
     conj_tac
     >- (simp[mstore_def, loweringStateRelDefsTheory.local_region_def, lookup_var_def] >>
         gvs[loweringStateRelDefsTheory.local_region_def, lookup_var_def]) >>
     conj_tac >- (qexists_tac `aid` >> simp[mstore_def] >> decide_tac) >>
     simp[]) >>
  `mem_bytes_at p n sh.vs_memory = mem_bytes_at p n s0.vs_memory` by
    (qpat_x_assum `!p n. _ \/ _ ==> _` irule >> decide_tac) >> simp[]
QED

Theorem array_header_success_post:
  sm.cs_next_var = sa.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  32 + LENGTH args * type_memory_size tv <= asz /\
  sh = (mstore b (n2w (LENGTH args)) s0 with vs_inst_idx := SUC s0.vs_inst_idx) /\
  locals_kept ce es es s0 sh /\ mem_word_at b sh.vs_memory = n2w (LENGTH args) /\
  local_ptrs_reserved ce sa /\
  (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
     b + asz <= lb \/ lb + lsz <= b) /\
  (!p n. p+n <= b \/ b+32 <= p ==>
    mem_bytes_at p n sh.vs_memory = mem_bytes_at p n s0.vs_memory) ==>
  !H res es' r.
  (?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
    r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es' /\
    stmt_state_rel H ctx func ce cx es' r /\
    storage_well_formed_on cx es' (FST H) /\
    elems_in_memory vs (b+32) tv r.vs_memory /\
    (!z w. not_fresh_at sm z /\ lookup_var z sh = SOME w ==>
      lookup_var z r = SOME w) /\
    (!aid a. FLOOKUP sh.vs_allocas aid = SOME a ==>
      FLOOKUP r.vs_allocas aid = SOME a) /\
    (!p n. b <= p /\ p+n <= b+asz /\
      (p+n <= b+32 \/ b+32+LENGTH args * type_memory_size tv <= p) ==>
      mem_bytes_at p n r.vs_memory = mem_bytes_at p n sh.vs_memory) /\
    (!aid p n. FLOOKUP sh.vs_allocas aid = SOME (p,n) /\
      aid < sm.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
      (!name lo sz. local_region ce es.scopes sh name lo sz ==>
        p+n <= lo \/ lo+sz <= p) ==>
      mem_bytes_at p n r.vs_memory = mem_bytes_at p n sh.vs_memory) /\
    locals_kept ce es es' sh r /\ alloca_history func r /\
    sh.vs_alloca_next <= r.vs_alloca_next /\
    (~EXISTS expr_has_effect args ==>
      (!n lb lsz. local_region ce es.scopes sh n lb lsz ==>
        mem_bytes_at lb lsz r.vs_memory = mem_bytes_at lb lsz sh.vs_memory) /\
      !p n. (p + n <= b \/ b + asz <= p) /\
        (!i c sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
           sm.cs_next_id <= i.inst_id /\
           FLOOKUP r.vs_allocas i.inst_id = SOME (c,sz) ==>
           regions_disjoint p n c sz) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n sh.vs_memory)) ==>
  (?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
    r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es' /\
    stmt_state_rel H ctx func ce cx es' r /\
    storage_well_formed_on cx es' (FST H) /\
    elems_in_memory vs (b+32) tv r.vs_memory /\
    mem_word_at b r.vs_memory = n2w (LENGTH args) /\
    (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
      lookup_var z r = SOME w) /\
    (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
      FLOOKUP r.vs_allocas aid = SOME a) /\
    (!p n. b <= p /\ p+n <= b+asz /\
      (p+n <= b \/ b+32+LENGTH args * type_memory_size tv <= p) ==>
      mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
    (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
      aid < sa.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
      (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
        p+n <= lo \/ lo+sz <= p) ==>
      mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
    locals_kept ce es es' s0 r /\ alloca_history func r /\
    s0.vs_alloca_next <= r.vs_alloca_next /\
    (~EXISTS expr_has_effect args ==>
      (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
        mem_bytes_at lb lsz r.vs_memory = mem_bytes_at lb lsz s0.vs_memory) /\
      !p n. (p + n <= b \/ b + asz <= p) /\
        (!i c sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
           sa.cs_next_id <= i.inst_id /\
           FLOOKUP r.vs_allocas i.inst_id = SOME (c,sz) ==>
           regions_disjoint p n c sz) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all array_header_frames >> strip_tac >>
  `mem_bytes_at b 32 r.vs_memory = mem_bytes_at b 32 sh.vs_memory` by
    (qpat_x_assum `!p n. b <= p /\ _ ==> _` irule >> simp[] >> decide_tac) >>
  `mem_word_at b r.vs_memory = n2w (LENGTH args)` by
    metis_tac[abiStaticAggregatePropsTheory.mem_word_at_bytes] >>
  `!name lo sz. local_region ce es.scopes sh name lo sz <=>
                local_region ce es.scopes s0 name lo sz` by
    (rpt gen_tac >> simp[loweringStateRelDefsTheory.local_region_def] >>
     gvs[lookup_var_def, mstore_def]) >>
  `!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
     lookup_var z sh = SOME w` by
    simp[mstore_def, lookup_var_def] >>
  `locals_kept ce es es' s0 r` by
    (irule exprBopSimPropsTheory.locals_kept_trans >>
     qexistsl_tac [`es`, `sa`, `sh`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `~EXISTS expr_has_effect args ==>
      (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
        mem_bytes_at lb lsz r.vs_memory = mem_bytes_at lb lsz s0.vs_memory) /\
      !p n. (p + n <= b \/ b + asz <= p) /\
        (!i c sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
           sa.cs_next_id <= i.inst_id /\
           FLOOKUP r.vs_allocas i.inst_id = SOME (c,sz) ==>
           regions_disjoint p n c sz) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory` by
    (strip_tac >>
     qpat_x_assum `~EXISTS expr_has_effect args ==> _` (drule_then strip_assume_tac) >>
     irule exprSimAggregateChildrenTheory.aggregate_pure_frame_trans >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`es`, `sm`, `sh`] >> rpt conj_tac >>
     TRY (first_assum ACCEPT_TAC) >> TRY (rewrite_tac[] >> NO_TAC) >>
     rpt strip_tac
     >- (qpat_x_assum `!p n. p+n <= b \/ b+32 <= p ==> _` irule >>
         qpat_x_assum `!n lb lsz. local_region ce es.scopes s0 n lb lsz ==> _ \/ _`
           drule >> decide_tac) >>
     qpat_x_assum `!p n. p+n <= b \/ b+32 <= p ==> _` irule >> decide_tac) >>
  qexists_tac `vs` >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> qpat_x_assum `!z w. _ ==> _` irule >>
      gvs[loweringStateRelDefsTheory.not_fresh_at_def, mstore_def, lookup_var_def]) >>
  gvs[mstore_def] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem aggregate_make_array_body_sim_mem:
  !args ce cx env elem_ty tv stride header sa out sb es func inst x b asz s0 ctx tops st0.
  EVERY (\e. arg_type_fits (expr_type e) elem_ty) args /\
  EVERY (\e. elem_ty = expr_type e \/
    is_bytestring_type elem_ty /\ is_bytestring_type (expr_type e)) args /\
  evaluate_type (get_tenv cx) elem_ty = SOME tv /\
  stride = type_memory_size tv /\
  type_memory_bytes ce elem_ty = type_memory_size tv /\
  compile_make_array compile_expr ce args elem_ty stride header (Var x) sa = (out,sb) /\
  expr_sim_inv ce cx env es /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st) /\
  body_inv tops ctx ce cx /\ body_exprs_mem_ok cx args /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
  (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  (if header then 32 else 0) + LENGTH args * type_memory_size tv <= asz /\
  b + asz < dimword (:256) /\
  (ce.ce_is_ctor ==>
   !name itv iv io.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
     regions_disjoint io (type_memory_size itv) b
       ((if header then 32 else 0) + LENGTH args * type_memory_size tv)) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s0 /\
    storage_well_formed_on cx es (FST H)) /\ alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  out = Var x /\
  gas_outcome T (cx_tops cx) (ctx,func) cx st0 (eval_exprs cx args) (es,s0)
    (\H res es' r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es' /\
      stmt_state_rel H ctx func ce cx es' r /\
      storage_well_formed_on cx es' (FST H) /\
      elems_in_memory vs (b+(if header then 32 else 0)) tv r.vs_memory /\
      (header ==> mem_word_at b r.vs_memory = n2w (LENGTH args)) /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
        lookup_var z r = SOME w) /\
      (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
        FLOOKUP r.vs_allocas aid = SOME a) /\
      (!p n. b <= p /\ p+n <= b+asz /\
        (p+n <= b \/ b+(if header then 32 else 0)+LENGTH args * type_memory_size tv <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
        aid < sa.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
        (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
          p+n <= lo \/ lo+sz <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      locals_kept ce es es' s0 r /\ alloca_history func r /\
      s0.vs_alloca_next <= r.vs_alloca_next /\
      (~EXISTS expr_has_effect args ==>
        (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
          mem_bytes_at lb lsz r.vs_memory = mem_bytes_at lb lsz s0.vs_memory) /\
        !p n. (p + n <= b \/ b + asz <= p) /\
          (!i c sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
             sa.cs_next_id <= i.inst_id /\
             FLOOKUP r.vs_allocas i.inst_id = SOME (c,sz) ==>
             regions_disjoint p n c sz) ==>
          mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory))
    (\H res es' exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit)
Proof
  rpt gen_tac >> strip_tac >> reverse (Cases_on `header`)
  >- (gvs[compile_make_array_def, comp_ignore_bind_def, comp_bind_def,
          comp_return_def] >>
      mp_tac (SRULE [] (Q.INST [`header` |-> `F`, `idx` |-> `0`, `off` |-> `0`]
        (SPEC_ALL aggregate_make_array_elems_body_sim_mem))) >>
      (impl_tac >- (gvs[] >> metis_tac[])) >> simp[]) >>
  gvs[compile_make_array_def, comp_ignore_bind_def, comp_bind_def, AllCaseEqs()] >>
  Cases_on `emit_void MSTORE [Var x; Lit (n2w (LENGTH args))] sa` >>
  rename1 `emit_void MSTORE _ sa = (u,sm)` >> Cases_on `u` >> gvs[] >>
  `ci_mono sa sm` by metis_tac[ci_mono_emit_void, pairTheory.SND] >>
  `ci_mono sm sb` by
    (mp_tac (Q.SPECL [`args`, `0`] (Q.INST [`header` |-> `T`,
       `cfn` |-> `compile_expr`, `buf` |-> `Var x`]
       compile_make_array_elems_as_tuple)) >>
     strip_tac >> gvs[] >>
     metis_tac[ci_mono_compile_make_tuple_cfn, compile_expr_ci_mono, pairTheory.SND]) >>
  `cs_extends sa sm /\ cs_extends sm sb` by gvs[ci_mono_def] >>
  drule_all fn_has_code_split >> strip_tac >>
  qabbrev_tac `sh = mstore b (n2w (LENGTH args)) s0 with
    vs_inst_idx := SUC s0.vs_inst_idx` >>
  `32 <= asz /\ not_local_ptr ce es.scopes x` by (simp[] >> decide_tac) >>
  `out = Var x` by
    (mp_tac (Q.SPECL [`args`, `0`] (Q.INST [`header` |-> `T`,
       `cfn` |-> `compile_expr`, `buf` |-> `Var x`]
       compile_make_array_elems_as_tuple)) >>
     strip_tac >> gvs[] >> metis_tac[exprOperandVarTheory.compiler_make_tuple_result]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  (* Off the trace's domain the run is a bad-storage one; on it, the header
     store runs at the domain's own horizon and every other horizon follows
     by the fields the store keeps. *)
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      irule gasStorageTheory.gas_bad_storage_at_initial >>
      simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
  `?H0. valid_horizon cx st0 H0 es.storage_trace` by
    metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `stmt_state_rel H0 ctx func ce cx es s0` by metis_tac[] >>
  `!name lo sz. local_region ce es.scopes s0 name lo sz ==>
      b + asz <= lo \/ lo + sz <= b` by
    (rpt strip_tac >>
     drule_all (SRULE [] (Q.INST [`off` |-> `0`, `n` |-> `asz`, `r` |-> `s0`]
       aggregate_alloca_slice_excludes_local)) >> decide_tac) >>
  drule array_header_mem_entry >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _.vs_allocas _ = SOME (_,_)`)) >>
  disch_then (qspec_then `sh` mp_tac) >>
  (impl_tac >-
    (simp[Abbr `sh`] >> rpt strip_tac >> first_x_assum drule_all >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac)) >> strip_tac >>
  `sh.vs_accounts = s0.vs_accounts /\ sh.vs_transient = s0.vs_transient /\
   sh.vs_requests = s0.vs_requests /\ sh.vs_call_ctx = s0.vs_call_ctx` by
    simp[Abbr `sh`, mstore_def] >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func ce cx es sh /\
     storage_well_formed_on cx es (FST H)` by
    (rpt strip_tac >> res_tac >> asm_rewrite_tac[] >>
     metis_tac[exprLoweringPropsTheory.stmt_state_rel_fields_transport]) >>
  mp_tac (Q.INST [`header` |-> `T`, `idx` |-> `0`, `off` |-> `32`,
     `sa` |-> `sm`, `s0` |-> `sh`] (SPEC_ALL aggregate_make_array_elems_body_sim_mem)) >>
  (impl_tac >-
    (simp[] >> rpt strip_tac >> first_x_assum drule_all >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac)) >>
  strip_tac >>
  irule bodyDeclMemoryComposeTheory.gas_outcome_zero_prefix_mem >>
  qexists_tac `sh` >> conj_tac >- fs[gas_marked_path_def] >>
  drule struct_gas_outcome_post >> disch_then irule >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >> rpt gen_tac >> strip_tac >>
  `!n lb lsz. local_region ce es.scopes s0 n lb lsz ==> asz + b <= lb \/ lb + lsz <= b` by
    (rpt strip_tac >>
     qpat_assum `!name lo sz. local_region ce es.scopes s0 name lo sz ==> b + asz <= lo \/ _`
       (drule_then mp_tac) >> decide_tac) >>
  pure_rewrite_tac [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  irule (SRULE [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
    array_header_success_post) >>
  drule array_header_emit_entry >>
  disch_then (qspecl_then [`x`, `ce`] strip_assume_tac) >>
  simp[] >> conj_tac >- first_assum ACCEPT_TAC >> conj_tac
  >- (qexists_tac `sm` >>
      gvs[Abbr `sh`, AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  gvs[Abbr `sh`, AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
