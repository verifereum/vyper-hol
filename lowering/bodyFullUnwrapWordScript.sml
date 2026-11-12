(* unwrap_value's word loads on one joint path at every valid horizon: one
   MLOAD, SLOAD, TLOAD or DLOAD, or the constructor's immutable load from
   memory.  Each case runs its load once at the trace's own horizon with no
   dead bytes, then holds at every valid horizon. *)
Theory bodyFullUnwrapWord
Ancestors
  bodyFullUnwrapRun fragGasOriginPtrDead exprPtrCtorImmStore
  bodyFieldMemoryProps exprPtrUnwrapLoadSegment slotCopyExecution
  instMemFrontier fragExecMem exprPtrUnwrapCode exprPtrCodeCopySegments
  bodyImmutableUnwrapMemory immutableCopyExecution memSafeRun
  exprPtrUnwrapMarked fragGasOriginPtr fragGasSeqPtr
  bodyPtrEnvBuiltinsEdges bodyPtrDefs loweringPosts exprSimMemDefs
  exprPtrCtorCodeLoad exprSimUnwrap exprSimUnwrapProps representationCleanPtr
  assignTuplePtrLoadStep stateFrame exprSimProps exprSimCopy
  exprLowering compileEnv context emitHelperProps venomState finite_map
  exprPtrUnwrapLoad exprPtrUnwrapStorage emitHelper venomExecSemantics
  venomInst freshWrites exprLoweringProps ptrDiscipline vyperStorageFootprint
  arithmetic list rich_list pred_set

(* vv_post at the compile_expr state, held at the later unwrap state. *)
val VV_MONO_TAC =
  rpt strip_tac >> gvs[]
  >>~- ([`FLOOKUP _.vs_allocas aid = SOME (b,sz)`],
        disj1_tac >> qexistsl [`aid`, `b`, `sz`] >> gvs[] >> metis_tac[]) >>
  metis_tac[];

val VV_POST_WIDEN_TAC =
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_def]) >>
  rewrite_tac[vv_post_def] >> asm_rewrite_tac[] >>
  conj_tac
  >- (qpat_x_assum `vv_at _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[vv_at_def, expr_val_at_def] >> VV_MONO_TAC) >>
  strip_tac >>
  qpat_x_assum `_ ==> vv_own _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_own_def, expr_val_own_def] >> VV_MONO_TAC;

(* The trace's own horizon H0, the posts at the unwrap state for every
   horizon, and their instances at H0. *)
val H0_TAC =
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
     ee.storage_trace` by fs[storage_trace_domain_def] >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post H ctx func cenv cx e es sa sb s0 ee tv (LocatedValue t p) s` by
    (rpt strip_tac >>
     qpat_x_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> VV_POST_WIDEN_TAC) >>
  `vv_post H0 ctx func cenv cx e es sa sb s0 ee tv (LocatedValue t p) s` by
    (first_assum (qspec_then `H0` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  `ghost_inv_at (DF H0) lo d cenv cx ee G tn s` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H0` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  `sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id` by
    decide_tac >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists `sm` >> simp[]) >>
  `!q. not_fresh_at sm q ==> not_fresh_at sb q` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `sm` >> simp[]) >>
  `!q. not_fresh_at sa q ==> not_fresh_at sb q` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `!x. vv_operand (LocatedValue t p) = Var x ==> not_fresh_at sb x` by
    (rpt strip_tac >>
     qpat_x_assum `!q. not_fresh_at sm q ==> _` irule >>
     qpat_x_assum `!x. vv_operand _ = Var x ==> not_fresh_at sm x` irule >>
     first_assum ACCEPT_TAC);

(* A word value's type is the expression's own: the type at the forcing
   is the lowered value type, a word, hence (premise) the expression type. *)
val WORD_TYPES_TAC =
  `is_word_type (post_value_type cenv e)` by
    (qpat_assum `is_word_type t` mp_tac >>
     qpat_x_assum `t = _` (fn th => REWRITE_TAC [th] >> assume_tac th)) >>
  `is_word_type (expr_type e)` by
    (qpat_assum `is_word_type (post_value_type _ _) ==> _` irule >>
     first_assum ACCEPT_TAC) >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_word >> first_assum ACCEPT_TAC) >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME rty` by
    (qpat_assum `evaluate_type _ (post_value_type _ _) = SOME rty` mp_tac >>
     qpat_assum `post_value_type _ _ = expr_type _`
       (fn th => REWRITE_TAC [th]));

(* A path at the empty dead set, the register transport of the ghosts, and
   a word's 32 stored bytes, inlined: the pieces state no generic lemma. *)
val D0_Q =
  `<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {};
      d_ret := K {} |>`;

val REG_Q =
  `!D G' tn' t'.
     ghost_inv_at D lo d cenv cx ee G tn s /\ local_ptrs_reserved cenv sa /\
     (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
             not_fresh_at sa x) /\
     (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
             not_fresh_at sa x) /\
     (!x. not_fresh_at sa x ==>
          lookup_var x t' = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
          op_taint tn' (Var x) = op_taint tn (Var x)) /\
     t'.vs_memory = s.vs_memory /\ tn'.t_mem = tn.t_mem /\
     t'.vs_call_ctx = s.vs_call_ctx /\ t'.vs_accounts = s.vs_accounts /\
     t'.vs_transient = s.vs_transient /\ t'.vs_immutables = s.vs_immutables /\
     t'.vs_allocas = s.vs_allocas /\ t'.vs_alloca_next = s.vs_alloca_next /\
     tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
     tn'.t_imm = tn.t_imm ==>
     ghost_inv_at D lo d cenv cx ee G' tn' t'`;

val REG_TAC =
  rpt (pop_assum kall_tac) >> rpt gen_tac >>
  simp[ghost_inv_at_def, local_ptrs_reserved_def, stor_taint_ok_at_def,
       allocas_from_def] >> rpt strip_tac
  >- (gvs[ptr_covers_def] >> metis_tac[])
  >- metis_tac[]
  >- (Cases_on `d` >- gvs[return_buf_ptr_def] >>
      PairCases_on `x` >> gvs[return_buf_ptr_def, ptr_covers_def] >>
      metis_tac[])
  >> metis_tac[];

val BCL_Q =
  `!imm (arg:operand) (la:compile_state) (r:operand) (lb:compile_state)
     (ls:venom_state) (la0:bytes32).
     compile_imm_load_word T imm arg la = (r,lb) /\
     eval_operand arg ls = SOME la0 /\ w2n la0 + 32 <= ls.vs_alloca_next /\
     (!region. imm = SOME region ==> eval_operand region ls = SOME 0w) ==>
     run_inst_seq_mem_ok (emitted_insts la lb) ls`;

val BCL_TAC =
  rpt (pop_assum kall_tac) >> rpt gen_tac >>
  Cases_on `imm` >> simp[contextTheory.compile_imm_load_word_def] >> strip_tac
  >- (drule emitted_insts_emit_op >> strip_tac >>
      simp[run_inst_seq_mem_ok_last, below_frontier_ILOAD] >>
      simp[inst_dload_in_section_def, mk_inst_def]) >>
  gvs[comp_bind_def] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op ADD _ la = (addr, s1)` >>
  drule emitted_insts_emit_op >> strip_tac >>
  qpat_x_assum `emit_op ILOAD _ _ = _` assume_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `emitted_insts la lb = emitted_insts la s1 ++ emitted_insts s1 lb` by
    (irule emitted_insts_append >> simp[]) >>
  gvs[run_inst_seq_mem_ok_cons, run_inst_seq_mem_ok_last] >> rpt conj_tac >>
  TRY (irule below_frontier_no_ranges >> simp[mk_inst_def] >> NO_TAC) >>
  TRY (simp[inst_dload_in_section_def, mk_inst_def] >> NO_TAC) >>
  gvs[step_inst_base_opcode_eqs, exec_pure2_def, mk_inst_def] >>
  gvs[unitTransformDefsTheory.inst_mem_below_frontier_def,
      contextCodegenRelTheory.source_memory_read_ranges_def,
      codegenRelTheory.source_memory_write_ranges_def,
      inst_dload_in_section_def,
      eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
      wordsTheory.WORD_ADD_0];

val WORD_SIZE_Q =
  `!wt tenv wtv (wv:value). is_word_type wt /\ evaluate_type tenv wt = SOME wtv ==>
     val_store_size wtv wv = 32`;

val WORD_SIZE_TAC =
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  drule_all word_tv_memory_size >> strip_tac >>
  Cases_on `wt` >> gvs[is_word_type_def]
  >- (rename1 `BaseT bt` >> Cases_on `bt` >> gvs[is_word_type_def] >>
      TRY (rename1 `BytesT bd` >> Cases_on `bd` >> gvs[is_word_type_def]) >>
      gvs[vyperValueTheory.evaluate_type_def] >>
      Cases_on `wv` >> simp[val_store_size_def]) >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  Cases_on `wv` >> simp[val_store_size_def];

(* The per-horizon block at the chosen endpoint: the path from the empty
   dead set, the post, and the transported ghosts. *)
val PER_H_TAC =
  gen_tac >> strip_tac >> rpt conj_tac
  >- (irule gas_origin_ptr_path_from_no_dead >> first_assum ACCEPT_TAC)
  >- (qpat_x_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
        (qspec_then `H` mp_tac) >>
      impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  qpat_x_assum `!D G' tn' t'. ghost_inv_at _ _ _ _ _ _ _ _ _ /\ _ ==> _` irule >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> res_tac >> res_tac >> simp[];

(* A memory word is forced by one MLOAD. *)
Theorem unwrap_memory_word_origin_ptr:
  vv = LocatedValue t p /\ p.ptr_location = LocMemory /\ is_word_type t /\
  compile_expr cenv ty e sa = (vv,sm) /\
  (is_word_type (post_value_type cenv e) ==> is_word_type (expr_type e)) /\
  sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
  unwrap_value cenv vv sb = (op,sc) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
    ~is_word_type (post_value_type cenv e) ==>
    type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
    type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post H ctx func cenv cx e es sa sm s0 ee tv vv s /\
     ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
  (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv e) ==>
    ptr_buf_ok cenv e op0 G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e p.ptr_operand G s) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?val. read_result cx tv ee = (INL val, ee) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                eval_operand (vv_operand vv) s = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
                       val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?v z G' tn'.
    read_result cx tv ee = (INL v, ee) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
         (s, G, tn) [] (OK z, G', tn') /\
       expr_post H ctx func cenv cx e es sa sc s0 ee v op z /\
       ghost_inv_at (DF H) lo d cenv cx ee G' tn' z) /\
    (~is_word_type (post_value_type cenv e) ==>
     vv_at cenv cx (post_value_type cenv e) sa sc ee tv
       (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z) /\
    expr_store_bound cx (expr_type e) v op z /\
    z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
    s0.vs_alloca_next <= z.vs_alloca_next /\
    ptr_val_ok cx (post_value_type cenv e) v op G' tn' z /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G' z) /\
    (~is_word_type (post_value_type cenv e) ==>
     !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
            eval_operand op z = SOME w ==>
            type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    ghost_kept_at lo cenv es sa Gi ti s0 G' tn' /\
    (!x. not_fresh_at sb x ==>
         lookup_var x z = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)) /\
    wb_frame cenv ee ee sb s z /\
    ghost_kept_at lo cenv ee sb G tn s G' tn'
Proof
  strip_tac >> qpat_x_assum `vv = _` SUBST_ALL_TAC >> H0_TAC >>
  drule_all unwrap_memory_word_input >> strip_tac >>
  WORD_TYPES_TAC >>
  `emit_op MLOAD [Var src] sb = (op,sc)` by
    gvs[unwrap_value_def, compile_ptr_load_def] >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sc.cs_current_bb = sb.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  qabbrev_tac `out = STRING #"%" (toString sb.cs_next_var)` >>
  qabbrev_tac `inst = mk_inst sb.cs_next_id MLOAD [Var src] [out]` >>
  qabbrev_tac `u = update_var out (mload (w2n w) s) s` >>
  `run_inst_seq [inst] s = OK u` by
    simp[run_inst_seq_def, Abbr `inst`, Abbr `u`, step_inst_base_opcode_eqs,
         mk_inst_def, exec_read1_def, eval_operand_def] >>
  `!q. not_fresh_at sb q ==> q <> out` by
    (simp[not_fresh_at_def, Abbr `out`] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `allocas_from lo s` by fs[ghost_inv_at_def] >>
  qspecl_then [`not_fresh_at sb`, `u`, `out`, `sb.cs_next_id`, `func`, `src`, D0_Q]
    mp_tac (Q.GENL [`P`, `t`, `out`, `id`, `fn`, `p`, `D`] ctor_mload_segment) >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  `inst_seq_ptr ^(Parse.Term D0_Q) lo ctx func PG G tn [inst] s Gf tnf` by
    (first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >>
     `s with vs_inst_idx := s.vs_inst_idx = s` by
       simp[venom_state_component_equality] >>
     simp[]) >>
  WORD_SIZE_Q by WORD_SIZE_TAC >>
  `val_store_size rty v = 32` by
    (first_x_assum irule >> qexistsl [`get_tenv cx`, `expr_type e`] >> simp[]) >>
  `w2n w + 32 <= s.vs_alloca_next` by
    (qpat_x_assum `vv_store_bound _ _ _ _ _ _ _`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [vv_store_bound_def]) >>
     disch_then (qspecl_then [`t`, `Var src`, `v`, `rty`, `w`] mp_tac) >>
     gvs[]) >>
  `run_inst_seq_mem_ok [inst] s` by
    metis_tac[body_word_load_prefix_mem_ok] >>
  qspecl_then [`[inst]`, `sb`, `sc`, `s`, `u`, `G`, `tn`, `Gf`, `tnf`]
    mp_tac (Q.INST [`D` |-> D0_Q] emitted_origin_ptr_path) >>
  impl_tac
  >- simp[Abbr `inst`, mk_inst_def, is_terminator_def] >>
  strip_tac >>
  `alloca_inv s` by
    (qpat_x_assum `vv_post H0 _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[vv_post_def, stmt_state_rel_def]) >>
  `alloca_history func (u with vs_inst_idx := LENGTH sc.cs_current_insts)` by
    metis_tac[body_word_load_history] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     expr_post H ctx func cenv cx e es sa sc s0 ee v op
       (u with vs_inst_idx := LENGTH sc.cs_current_insts)` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     qpat_x_assum `vv_post H0 _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
     drule unwrap_mload_post >>
     disch_then (qspecl_then [`w`, `v`, `sc`, `op`] mp_tac) >>
     simp[Abbr `u`, Abbr `out`, ADD1]) >>
  `mem_word_taint tn.t_mem (w2n w) = {}` by
    (simp[mem_word_taint_def, EXTENSION] >> rpt strip_tac >>
     CCONTR_TAC >> fs[] >>
     qpat_x_assum `!i. w2n w <= i /\ _ ==> _` (qspec_then `w2n w + x` mp_tac) >>
     simp[]) >>
  REG_Q by REG_TAC >>
  TRY (qunabbrev_tac `u`) >>
  qexistsl [`v`,
            `update_var out (mload (w2n w) s) s with vs_inst_idx := LENGTH sc.cs_current_insts`,
            `Gf`, `tnf`] >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- PER_H_TAC
  >- simp[]
  >- simp[expr_store_bound_word]
  >- fs[update_var_def]
  >- simp[]
  >- first_assum ACCEPT_TAC
  >- fs[update_var_def]
  >- fs[update_var_def]
  >- (irule ptr_val_ok_word >> fs[])
  >- simp[]
  >- simp[]
  >- (irule ghost_kept_at_clean_suffix >> simp[] >>
      metis_tac[SUBSET_REFL])
  >- (rpt strip_tac >> res_tac >>
      simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE])
  >- (simp[wb_frame_def, update_var_def, locals_kept_mem] >>
      rpt strip_tac >> res_tac >>
      fs[lookup_var_def, FLOOKUP_UPDATE])
  >> (irule ghost_kept_at_clean_suffix >>
  qexistsl [`G`, `tn`] >> simp[ghost_kept_at_def] >>
  metis_tac[SUBSET_REFL])
QED

(* A storage or transient word is forced by one SLOAD or TLOAD. *)
Theorem unwrap_slot_word_origin_ptr:
  vv = LocatedValue t p /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  is_word_type t /\
  compile_expr cenv ty e sa = (vv,sm) /\
  (is_word_type (post_value_type cenv e) ==> is_word_type (expr_type e)) /\
  sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
  unwrap_value cenv vv sb = (op,sc) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
    ~is_word_type (post_value_type cenv e) ==>
    type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
    type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post H ctx func cenv cx e es sa sm s0 ee tv vv s /\
     ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
  (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv e) ==>
    ptr_buf_ok cenv e op0 G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e p.ptr_operand G s) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?val. read_result cx tv ee = (INL val, ee) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                eval_operand (vv_operand vv) s = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
                       val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?v z G' tn'.
    read_result cx tv ee = (INL v, ee) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
         (s, G, tn) [] (OK z, G', tn') /\
       expr_post H ctx func cenv cx e es sa sc s0 ee v op z /\
       ghost_inv_at (DF H) lo d cenv cx ee G' tn' z) /\
    (~is_word_type (post_value_type cenv e) ==>
     vv_at cenv cx (post_value_type cenv e) sa sc ee tv
       (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z) /\
    expr_store_bound cx (expr_type e) v op z /\
    z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
    s0.vs_alloca_next <= z.vs_alloca_next /\
    ptr_val_ok cx (post_value_type cenv e) v op G' tn' z /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G' z) /\
    (~is_word_type (post_value_type cenv e) ==>
     !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
            eval_operand op z = SOME w ==>
            type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    ghost_kept_at lo cenv es sa Gi ti s0 G' tn' /\
    (!x. not_fresh_at sb x ==>
         lookup_var x z = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)) /\
    wb_frame cenv ee ee sb s z /\
    ghost_kept_at lo cenv ee sb G tn s G' tn'
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  qpat_x_assum `vv = _` SUBST_ALL_TAC >> H0_TAC >>
  `?tr. p.ptr_location = slot_loc tr` by
    (simp[slot_loc_def] >> metis_tac[]) >>
  drule_all unwrap_storage_word_input >> strip_tac >>
  WORD_TYPES_TAC >>
  `emit_op (if tr then TLOAD else SLOAD) [p.ptr_operand] sb = (op,sc)` by
    (Cases_on `tr` >> gvs[slot_loc_def, unwrap_value_def, compile_ptr_load_def]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sc.cs_current_bb = sb.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  qabbrev_tac `out = STRING #"%" (toString sb.cs_next_var)` >>
  qabbrev_tac `inst = mk_inst sb.cs_next_id (if tr then TLOAD else SLOAD)
                        [p.ptr_operand] [out]` >>
  `!q. not_fresh_at sb q ==> q <> out` by
    (simp[not_fresh_at_def, Abbr `out`] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `allocas_from lo s` by fs[ghost_inv_at_def] >>
  qspecl_then [`if tr then TLOAD else SLOAD`, `p.ptr_operand`, `a`,
               `sb.cs_next_id`, `out`, `func`, D0_Q]
    mp_tac (Q.GENL [`load`, `arg`, `key`, `id`, `out`, `fn`, `D`]
              copy_slot_load_segment) >>
  impl_tac >- (Cases_on `tr` >> simp[]) >>
  disch_then (qx_choosel_then [`Gf`, `tnf`, `u`] strip_assume_tac) >>
  `step_inst_base inst s = OK u` by
    (qpat_x_assum `run_inst_seq _ s = OK u` mp_tac >> qunabbrev_tac `inst` >>
     qmatch_goalsub_abbrev_tac `run_inst_seq [i0] s` >>
     simp[run_inst_seq_def] >> Cases_on `step_inst_base i0 s` >> simp[]) >>
  `Gf = step_prov PG G inst u /\ tnf = step_taint inst s u tn` by
    (qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[inst_seq_ptr_def, Abbr `inst`]) >>
  `slot_copy_word (if tr then TLOAD else SLOAD) s a =
     if tr then tload a s else sload a s` by
    (Cases_on `tr` >> simp[slot_copy_word_def]) >>
  `run_inst_seq_mem_ok [inst] s` by
    (simp[run_inst_seq_mem_ok_last, Abbr `inst`] >> conj_tac
     >- (irule below_frontier_no_ranges >> Cases_on `tr` >> simp[mk_inst_def])
     >> Cases_on `tr` >> simp[inst_dload_in_section_def, mk_inst_def]) >>
  qspecl_then [`[inst]`, `sb`, `sc`, `s`, `u`, `G`, `tn`, `Gf`, `tnf`]
    mp_tac (Q.INST [`D` |-> D0_Q] emitted_origin_ptr_path) >>
  impl_tac
  >- (simp[Abbr `inst`, mk_inst_def] >> Cases_on `tr` >>
      simp[is_terminator_def]) >>
  strip_tac >>
  `alloca_inv s` by
    (qpat_x_assum `vv_post H0 _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[vv_post_def, stmt_state_rel_def]) >>
  `alloca_history func (u with vs_inst_idx := LENGTH sc.cs_current_insts)` by
    (qspecl_then [`[inst]`, `sb`, `sc`, `s`, `u`] mp_tac
       emitted_alloca_history >>
     simp[Abbr `inst`, mk_inst_def] >> Cases_on `tr` >>
     simp[is_terminator_def]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     expr_post H ctx func cenv cx e es sa sc s0 ee v op
       (u with vs_inst_idx := LENGTH sc.cs_current_insts)` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     qpat_x_assum `vv_post H0 _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
     drule unwrap_storage_word_post >>
     disch_then (qspecl_then [`v`, `tr`, `sc`, `op`, `a`] mp_tac) >>
     simp[Abbr `out`, ADD1]) >>
  REG_Q by REG_TAC >>
  qexistsl [`v`, `u with vs_inst_idx := LENGTH sc.cs_current_insts`,
            `Gf`, `tnf`] >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- PER_H_TAC
  >- simp[]
  >- simp[expr_store_bound_word]
  >- fs[update_var_def]
  >- simp[]
  >- first_assum ACCEPT_TAC
  >- fs[update_var_def]
  >- fs[update_var_def]
  >- (irule ptr_val_ok_word >> simp[] >> conj_tac
      >- (Cases_on `tr` >> fs[])
      >> irule step_prov_out_none >>
      simp[Abbr `inst`, mk_inst_def] >>
      irule out_prov_other_none >> Cases_on `tr` >> simp[mk_inst_def])
  >- simp[]
  >- simp[]
  >- (irule ghost_kept_at_clean_suffix >> simp[] >>
      metis_tac[SUBSET_REFL])
  >- (rpt strip_tac >> res_tac >>
      simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE])
  >- (simp[wb_frame_def, update_var_def, locals_kept_mem] >>
      rpt strip_tac >> res_tac >>
      fs[lookup_var_def, FLOOKUP_UPDATE])
  >> (irule ghost_kept_at_clean_suffix >>
  qexistsl [`G`, `tn`] >> simp[ghost_kept_at_def] >>
  metis_tac[SUBSET_REFL])
QED

(* An immutable word is forced by DLOAD, or in a constructor by ILOAD. *)
Theorem unwrap_code_word_origin_ptr:
  vv = LocatedValue t p /\ p.ptr_location = LocCode /\ is_word_type t /\
  compile_expr cenv ty e sa = (vv,sm) /\
  (is_word_type (post_value_type cenv e) ==> is_word_type (expr_type e)) /\
  sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
  unwrap_value cenv vv sb = (op,sc) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
    ~is_word_type (post_value_type cenv e) ==>
    type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
    type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post H ctx func cenv cx e es sa sm s0 ee tv vv s /\
     ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
  (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv e) ==>
    ptr_buf_ok cenv e op0 G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e p.ptr_operand G s) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?val. read_result cx tv ee = (INL val, ee) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                eval_operand (vv_operand vv) s = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
                       val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?v z G' tn'.
    read_result cx tv ee = (INL v, ee) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
         (s, G, tn) [] (OK z, G', tn') /\
       expr_post H ctx func cenv cx e es sa sc s0 ee v op z /\
       ghost_inv_at (DF H) lo d cenv cx ee G' tn' z) /\
    (~is_word_type (post_value_type cenv e) ==>
     vv_at cenv cx (post_value_type cenv e) sa sc ee tv
       (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z) /\
    expr_store_bound cx (expr_type e) v op z /\
    z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
    s0.vs_alloca_next <= z.vs_alloca_next /\
    ptr_val_ok cx (post_value_type cenv e) v op G' tn' z /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G' z) /\
    (~is_word_type (post_value_type cenv e) ==>
     !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
            eval_operand op z = SOME w ==>
            type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    ghost_kept_at lo cenv es sa Gi ti s0 G' tn' /\
    (!x. not_fresh_at sb x ==>
         lookup_var x z = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)) /\
    wb_frame cenv ee ee sb s z /\
    ghost_kept_at lo cenv ee sb G tn s G' tn'
Proof
  strip_tac >> qpat_x_assum `vv = _` SUBST_ALL_TAC >> H0_TAC >>
  drule_all vv_post_code_source >> strip_tac >>
  WORD_TYPES_TAC >>
  `stmt_state_rel H0 ctx func cenv cx ee s` by
    (qpat_assum `vv_post H0 _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[vv_post_def]) >>
  REG_Q by REG_TAC >>
  reverse (Cases_on `cenv.ce_is_ctor`) >- suspend "runtime" >>
  `compile_imm_load_word T cenv.ce_imm_alloca p.ptr_operand sb = (op,sc)` by
    gvs[unwrap_value_def, compile_ptr_load_def] >>
  `op_taint tn p.ptr_operand = {} /\ op_prov G p.ptr_operand = NONE` by
    fs[ptr_vv_ok_def] >>
  `type_memory_size rty = 32` by metis_tac[word_tv_memory_size] >>
  `w2n a + 32 <= lo /\
   !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory rty v (w2n a) mem` by
    (qpat_x_assum `cenv.ce_is_ctor /\ _ ==> _` mp_tac >>
     simp[vv_location_def, vv_operand_def] >> strip_tac >> gvs[] >>
     first_x_assum (qspecl_then [`rty`, `a`] mp_tac) >> simp[]) >>
  `mem_word_taint tn.t_mem (w2n a) = {}` by
    (`!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
            mem_word_at (w2n a) mem = typed_val_to_w256 rty v` by
       metis_tac[val_in_memory_word_type] >>
     drule robust_mem_word_at_clean >> strip_tac >>
     simp[mem_word_taint_def, EXTENSION] >> rpt strip_tac >>
     CCONTR_TAC >> fs[] >>
     qpat_x_assum `!i. w2n a <= i /\ _ ==> _` (qspec_then `w2n a + x` mp_tac) >>
     simp[]) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `!region. cenv.ce_imm_alloca = SOME region ==>
     eval_operand region s = SOME 0w /\ copy_old_operand sb region /\
     op_taint tn region = {} /\ op_prov G region = NONE` by
    (gen_tac >> strip_tac >>
     `immutable_base_zero cenv s` by fs[stmt_state_rel_def] >>
     fs[immutable_base_zero_alt] >> first_x_assum drule >>
     Cases_on `region` >>
     simp[eval_operand_def, lookup_var_def, copy_old_operand_def,
          op_taint_def, op_prov_def] >>
     strip_tac >> conj_tac
     >- metis_tac[local_ptrs_reserved_imm_base] >>
     `lo <> 0` by decide_tac >>
     fs[ghost_inv_at_def, op_taint_def, op_prov_def]) >>
  qspecl_then [`cenv.ce_imm_alloca`, `p.ptr_operand`, `sb`, `op`, `sc`,
               D0_Q, `lo`, `ctx`, `func`, `PG`, `G`, `tn`, `s`, `a`]
    mp_tac (Q.GENL [`imm`, `arg`, `sa`, `op`, `sb`, `D`, `lo`, `ctx`, `fn`,
                    `PG`, `G`, `tn`, `s`, `a`] code_copy_ctor_load) >>
  impl_tac >- fs[copy_old_operand_def, vv_operand_def] >>
  disch_then (qx_choosel_then [`Gf`, `tnf`, `u`] strip_assume_tac) >>
  `run_inst_seq (emitted_insts sb sc) s = OK u /\
   sc.cs_current_insts = sb.cs_current_insts ++ emitted_insts sb sc /\
   (!x. not_fresh_at sb x ==> lookup_var x u = lookup_var x s)` by
    fs[copy_runtime_frame_def] >>
  `sc.cs_current_bb = sb.cs_current_bb /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
              ~is_terminator i.inst_opcode) (emitted_insts sb sc)` by
    (qpat_x_assum `compile_imm_load_word T _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `cenv.ce_imm_alloca` >> strip_tac
     >- (gvs[compile_imm_load_word_def] >> drule emitted_insts_emit_op >>
         strip_tac >>
         gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
             comp_ignore_bind_def, comp_return_def, emit_def, mk_inst_def,
             is_terminator_def]) >>
     drule compile_imm_load_word_ctor_result >> strip_tac >>
     simp[emitted_insts_def, DROP_APPEND, mk_inst_def, is_terminator_def] >>
     gvs[compile_imm_load_word_def, emit_op_def, comp_bind_def, fresh_var_def,
         fresh_id_def, comp_ignore_bind_def, comp_return_def, emit_def]) >>
  `state_frame u = state_frame s` by
    (qpat_x_assum `run_inst_seq (emitted_insts sb sc) s = OK u` mp_tac >>
     qpat_x_assum `compile_imm_load_word T _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `cenv.ce_imm_alloca` >> rpt strip_tac
     >- (gvs[compile_imm_load_word_def] >> drule emitted_insts_emit_op >>
         strip_tac >>
         gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
             exec_read1_def, AllCaseEqs(), update_var_def, state_frame_def]) >>
     drule compile_imm_load_word_ctor_result >> strip_tac >>
     gvs[emitted_insts_def, DROP_APPEND, run_inst_seq_def,
         step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def, exec_pure2_def,
         AllCaseEqs(), update_var_def, state_frame_def]) >>
  `u.vs_memory = s.vs_memory /\ u.vs_current_bb = s.vs_current_bb /\
   u.vs_halted = s.vs_halted /\ u.vs_allocas = s.vs_allocas /\
   u.vs_alloca_next = s.vs_alloca_next /\ u.vs_call_ctx = s.vs_call_ctx /\
   u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
   u.vs_immutables = s.vs_immutables` by
    fs[state_frame_def, venom_state_component_equality] >>
  `inst_seq_ptr ^(Parse.Term D0_Q) lo ctx func PG G tn (emitted_insts sb sc) s Gf tnf` by
    (first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >>
     `s with vs_inst_idx := s.vs_inst_idx = s` by
       simp[venom_state_component_equality] >>
     simp[]) >>
  `w2n a + 32 <= s.vs_alloca_next` by decide_tac >>
  BCL_Q by BCL_TAC >>
  `run_inst_seq_mem_ok (emitted_insts sb sc) s` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  qspecl_then [`emitted_insts sb sc`, `sb`, `sc`, `s`, `u`, `G`, `tn`,
               `Gf`, `tnf`] mp_tac (Q.INST [`D` |-> D0_Q] emitted_origin_ptr_path) >>
  impl_tac >- fs[] >> strip_tac >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `alloca_history func (u with vs_inst_idx := LENGTH sc.cs_current_insts)` by
    (qspecl_then [`emitted_insts sb sc`, `sb`, `sc`, `s`, `u`] mp_tac
       emitted_alloca_history >>
     fs[EVERY_MEM]) >>
  `!x n. eval_operand x (u with vs_inst_idx := n) = eval_operand x u /\
         lookup_var x (u with vs_inst_idx := n) = lookup_var x u` by
    (Cases >> simp[eval_operand_def, lookup_var_def]) >>
  `?tvt. evaluate_type (get_tenv cx) t = SOME tvt /\
         mload (w2n a) s = typed_val_to_w256 tvt v` by
    metis_tac[immutable_holds_iload] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     expr_post H ctx func cenv cx e es sa sc s0 ee v op
       (u with vs_inst_idx := LENGTH sc.cs_current_insts)` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     `stmt_state_rel H ctx func cenv cx ee s` by
       (qpat_assum `vv_post H _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
        simp[vv_post_def]) >>
     `stmt_state_rel H ctx func cenv cx ee
        (u with vs_inst_idx := LENGTH sc.cs_current_insts)` by
       (irule stmt_state_rel_old_vars_frame_ptr >>
        qexistsl [`s`, `sb`] >>
        fs[state_frame_def, venom_state_component_equality]) >>
     qpat_x_assum `vv_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_then (Pos last) mp_tac vv_post_read_result) >>
     disch_then (drule_then assume_tac) >>
     qspecl_then [`func`, `cenv`, `cx`, `e`, `es`, `sa`, `sb`, `sc`, `s0`,
                  `ee`, `v`, `t`, `p`, `op`, `s`,
                  `u with vs_inst_idx := LENGTH sc.cs_current_insts`,
                  `mload (w2n a) s`, `ctx`]
       mp_tac expr_post_of_vv_post_load_physical >>
     impl_tac >- gvs[immutable_copy_read_def] >>
     simp[]) >>
  qexistsl [`v`, `u with vs_inst_idx := LENGTH sc.cs_current_insts`,
            `Gf`, `tnf`] >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- PER_H_TAC
  >- simp[]
  >- simp[expr_store_bound_word]
  >- fs[update_var_def]
  >- simp[]
  >- first_assum ACCEPT_TAC
  >- fs[update_var_def]
  >- fs[update_var_def]
  >- (irule ptr_val_ok_word >> fs[])
  >- simp[]
  >- simp[]
  >- (irule ghost_kept_at_clean_suffix >> simp[] >>
      metis_tac[SUBSET_REFL])
  >- metis_tac[]
  >- (simp[wb_frame_def, locals_kept_mem] >> metis_tac[])
  >> irule ghost_kept_at_clean_suffix >>
  qexistsl [`G`, `tn`] >> simp[ghost_kept_at_def] >>
  metis_tac[SUBSET_REFL]
QED

Resume unwrap_code_word_origin_ptr[runtime]:
  `emit_op DLOAD [p.ptr_operand] sb = (op,sc)` by
    gvs[unwrap_value_def, compile_ptr_load_def, compile_imm_load_word_def] >>
  `op_taint tn p.ptr_operand = {}` by fs[ptr_vv_ok_def] >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sc.cs_current_bb = sb.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  qabbrev_tac `out = STRING #"%" (toString sb.cs_next_var)` >>
  qabbrev_tac `inst = mk_inst sb.cs_next_id DLOAD [p.ptr_operand] [out]` >>
  qabbrev_tac `u = update_var out (immutable_copy_read F a s) s` >>
  `run_inst_seq [inst] s = OK u` by
    simp[run_inst_seq_def, Abbr `inst`, Abbr `u`, step_inst_base_opcode_eqs,
         mk_inst_def, exec_read1_def, immutable_copy_read_def] >>
  `!q. not_fresh_at sb q ==> q <> out` by
    (simp[not_fresh_at_def, Abbr `out`] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `allocas_from lo s` by fs[ghost_inv_at_def] >>
  qspecl_then [`not_fresh_at sb`, `u`, `out`, `sb.cs_next_id`, `func`,
               `p.ptr_operand`, D0_Q]
    mp_tac (Q.GENL [`P`, `t`, `out`, `id`, `fn`, `arg`, `D`]
              code_copy_load_segment) >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  `inst_seq_ptr ^(Parse.Term D0_Q) lo ctx func PG G tn [inst] s Gf tnf` by
    (first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >>
     `s with vs_inst_idx := s.vs_inst_idx = s` by
       simp[venom_state_component_equality] >>
     simp[]) >>
  `w2n a + type_memory_size rty <= LENGTH s.vs_data_section` by
    (irule runtime_immutable_data_section >> simp[] >> metis_tac[]) >>
  `run_inst_seq_mem_ok [inst] s` by
    (simp[run_inst_seq_mem_ok_last, Abbr `inst`] >> conj_tac
     >- (irule below_frontier_no_ranges >> simp[mk_inst_def])
     >> simp[inst_dload_in_section_def, mk_inst_def]) >>
  qspecl_then [`[inst]`, `sb`, `sc`, `s`, `u`, `G`, `tn`, `Gf`, `tnf`]
    mp_tac (Q.INST [`D` |-> D0_Q] emitted_origin_ptr_path) >>
  impl_tac
  >- simp[Abbr `inst`, mk_inst_def, is_terminator_def] >>
  strip_tac >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `alloca_history func (u with vs_inst_idx := LENGTH sc.cs_current_insts)` by
    (qspecl_then [`[inst]`, `sb`, `sc`, `s`, `u`] mp_tac
       emitted_alloca_history >>
     simp[Abbr `inst`, mk_inst_def, is_terminator_def]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     expr_post H ctx func cenv cx e es sa sc s0 ee v op
       (u with vs_inst_idx := LENGTH sc.cs_current_insts)` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     qpat_x_assum `vv_post H0 _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
     drule unwrap_code_word_post >>
     disch_then (qspecl_then [`v`, `sc`, `op`, `a`] mp_tac) >>
     simp[Abbr `u`, Abbr `out`, ADD1, immutable_copy_read_def]) >>
  TRY (qunabbrev_tac `u`) >>
  qexistsl [`v`,
            `update_var out (immutable_copy_read F a s) s with vs_inst_idx := LENGTH sc.cs_current_insts`,
            `Gf`, `tnf`] >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- PER_H_TAC
  >- simp[]
  >- simp[expr_store_bound_word]
  >- fs[update_var_def]
  >- simp[]
  >- first_assum ACCEPT_TAC
  >- fs[update_var_def]
  >- fs[update_var_def]
  >- (irule ptr_val_ok_word >> fs[])
  >- simp[]
  >- simp[]
  >- (irule ghost_kept_at_clean_suffix >> simp[] >>
      metis_tac[SUBSET_REFL])
  >- (rpt strip_tac >> res_tac >>
      simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE])
  >- (simp[wb_frame_def, update_var_def, locals_kept_mem] >>
      rpt strip_tac >> res_tac >>
      fs[lookup_var_def, FLOOKUP_UPDATE])
  >> (irule ghost_kept_at_clean_suffix >>
  qexistsl [`G`, `tn`] >> simp[ghost_kept_at_def] >>
  metis_tac[SUBSET_REFL])
QED

Finalise unwrap_code_word_origin_ptr
