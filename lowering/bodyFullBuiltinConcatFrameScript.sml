(* The actual four-instruction Concat prefix on the joint path. *)
Theory bodyFullBuiltinConcatFrame
Ancestors
  bodyFullBuiltinConcatAdd bodyFullBuiltinConcatZero loweringShapeDefs fragGasOriginPtrLoop
  assignTuplePtrLocalBytesCopy
  bodyFullAllocaFresh bodyFullGhostFrame bodyFullUnwrapRun
  bodyPtrBytestringBuiltinsWindowGhost exprSimConcatShapeRun
  wordArgsPtr fragGasSeqPtr fragExec instSeqPtrLo
  loweringHalt emitHelperProps exprLoweringProps venomMemProps finite_map pred_set

Theorem concat_prefix_full:
  compile_alloc_buffer bsz sa = (buf,s1) /\
  emit_op ADD [buf.buf_operand; Lit 32w] s1 = (data_operand,s2) /\
  compile_alloc_buffer 64 s2 = (ob,s3) /\
  emit_void MSTORE [ob.buf_operand; Lit 0w] s3 = (u,s4) /\
  fn_has_code sa s4 func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ 32 <= bsz /\ bsz < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ stmt_state_rel (H0:(bool # bytes32 # type_value) list # num list) ctx func cenv cx es s /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  return_buf_frame d cenv sa s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t G' tn' bv dp oq B ow.
    buf.buf_operand = Var bv /\ data_operand = Var dp /\ ob.buf_operand = Var oq /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    t.vs_current_bb = s4.cs_current_bb /\
    t.vs_inst_idx = LENGTH s4.cs_current_insts /\ ~t.vs_halted /\
    alloca_history func t /\ allocas_from lo t /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    not_fresh_at s4 bv /\ not_fresh_at s4 dp /\ not_fresh_at s4 oq /\
    lookup_var bv t = SOME (n2w B) /\
    lookup_var dp t = SOME (n2w (B+32)) /\ lookup_var oq t = SOME ow /\
    ptr_covers G' tn' bv t bsz /\ ptr_covers G' tn' dp t (bsz-32) /\
    ptr_covers G' tn' oq t 64 /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (B,bsz) /\
    FLOOKUP t.vs_allocas (sa.cs_next_id+2) = SOME (w2n ow,64) /\
    lo <= B /\ lo <= w2n ow /\ B+bsz < dimword (:256) /\
    B+bsz <= t.vs_alloca_next /\ w2n ow+64 < dimword (:256) /\
    w2n ow+64 <= t.vs_alloca_next /\ regions_disjoint B bsz (w2n ow) 64 /\
    mload (w2n ow) t = 0w /\
    (!i. w2n ow <= i /\ i < w2n ow+32 ==> i NOTIN tn'.t_mem) /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==> FLOOKUP t.vs_allocas aid = SOME e) /\
    (!name b len. local_region cenv es.scopes s name b len ==>
      regions_disjoint B bsz b len /\ regions_disjoint (w2n ow) 64 b len) /\
    (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint B bsz b len /\ regions_disjoint (w2n ow) 64 b len) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!p n. p+n <= w2n ow \/ w2n ow+32 <= p ==>
      mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory) /\
    return_buf_frame d cenv s4 t /\
    (!(H:(bool # bytes32 # type_value) list # num list).
      stmt_state_rel H ctx func cenv cx es s ==> stmt_state_rel H ctx func cenv cx es t) /\
    (!D. ghost_inv_at D lo d cenv cx es G tn s ==> ghost_inv_at D lo d cenv cx es G' tn' t) /\
    ghost_kept_at lo cenv es sa G tn s G' tn'
Proof
  strip_tac >>
  `cs_extends sa s1 /\ cs_extends s1 s2 /\
   cs_extends s2 s3 /\ cs_extends s3 s4` by
    (rpt conj_tac
     >- metis_tac[compile_alloc_buffer_extends]
     >- metis_tac[exprSimAccountsTheory.emit_op_extends_next_var]
     >- metis_tac[compile_alloc_buffer_extends] >>
     gvs[emitHelperTheory.emit_void_def, GSYM emitHelperTheory.emit_inst_def] >>
     metis_tac[cs_extends_emit_inst]) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
   fn_has_code s2 s3 func /\ fn_has_code s3 s4 func` by
    metis_tac[fn_has_code_split, compileEnvTheory.cs_extends_trans] >>
  drule_all (INST_TYPE [``:'a`` |-> ``:256``, ``:'b`` |-> ``:256``]
    alloc_buffer_origin_ptr_path) >>
  disch_then (qspecl_then [`tn`, `explicit`, `PG`, `G`] strip_assume_tac) >>
  suspend "allocated"
QED

Resume concat_prefix_full[allocated]:
  rename1 `lookup_var bv t1 = SOME bw` >>
  rename1 `ptr_covers G1 tn1 bv t1 bsz` >>
  `!D. ghost_inv_at D lo d cenv cx es G tn s ==>
       ghost_inv_at D lo d cenv cx es G1 tn1 t1` by
    (rpt strip_tac >>
     drule_all (Q.INST [`sa` |-> `sa`, `H` |-> `H0`,
       `ctx` |-> `ctx`, `func` |-> `func`, `e` |-> `w2n bw + bsz`]
       bodyFullAllocaFreshTheory.alloc_buffer_ghost_inv_at) >> simp[]) >>
  drule_all concat_prefix_code >> strip_tac >>
  `stmt_state_rel H0 ctx func cenv cx es t1` by
    (first_assum irule >> first_assum ACCEPT_TAC) >>
  `~t1.vs_halted` by
    (qpat_x_assum `t1 with <| vs_vars := _; vs_allocas := _;
      vs_alloca_next := _; vs_inst_idx := _ |> = s`
       (mp_tac o Q.AP_TERM `\z:venom_state. z.vs_halted`) >> simp[]) >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  `w2n bw+32 < dimword (:256)` by decide_tac >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x)` by
    (conj_tac >> rpt gen_tac >> strip_tac >>
     irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists `sa` >> simp[] >> metis_tac[]) >>
  `emit_op ADD [Var bv; Lit 32w] s1 = (data_operand,s2)` by
    metis_tac[] >>
  drule_all concat_data_add_fresh_full >>
  disch_then (qspecl_then [`explicit`, `d`, `PG`] strip_assume_tac) >>
  rename1 `ptr_covers G2 tn2 dp t2 (bsz-32)` >>
  `local_ptrs_reserved cenv s2` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  `stmt_state_rel H0 ctx func cenv cx es t2` by
    (first_assum irule >> first_assum ACCEPT_TAC) >>
  `lo <= t2.vs_alloca_next` by
    (qpat_assum `t2 with <|vs_vars := _; vs_inst_idx := _|> = t1`
      (mp_tac o Q.AP_TERM `\z:venom_state. z.vs_alloca_next`) >> simp[]) >>
  `64 < dimword (:256)` by simp[wordsTheory.dimword_def] >>
  drule_all (Q.INST [`n` |-> `64`] (INST_TYPE
    [``:'a`` |-> ``:256``, ``:'b`` |-> ``:256``]
    alloc_buffer_origin_ptr_path)) >>
  disch_then (qspecl_then [`tn2`, `explicit`, `PG`, `G2`] strip_assume_tac) >>
  rename1 `lookup_var oq t3 = SOME ow` >>
  rename1 `ptr_covers G3 tn3 oq t3 64` >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s2 x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s2 x)` by
    (conj_tac >> rpt gen_tac >> strip_tac >>
     irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists `sa` >> simp[] >> metis_tac[]) >>
  `!D. ghost_inv_at D lo d cenv cx es G2 tn2 t2 ==>
       ghost_inv_at D lo d cenv cx es G3 tn3 t3` by
    (rpt strip_tac >>
     drule_all (Q.INST [`sa` |-> `s2`, `H` |-> `H0`,
       `ctx` |-> `ctx`, `func` |-> `func`, `e` |-> `w2n ow + 64`]
       bodyFullAllocaFreshTheory.alloc_buffer_ghost_inv_at) >> simp[]) >>
  suspend "zero"
QED

Resume concat_prefix_full[zero]:
  `stmt_state_rel H0 ctx func cenv cx es t3` by
    (first_assum irule >> first_assum ACCEPT_TAC) >>
  `alloca_inv t3` by
    (qpat_assum `stmt_state_rel H0 ctx func cenv cx es t3` mp_tac >>
     pure_rewrite_tac[stmt_state_rel_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `lo <= w2n ow` by
    (qpat_assum `allocas_from lo t3`
       (mp_tac o REWRITE_RULE [ptrDisciplineTheory.allocas_from_def]) >>
     disch_then (qspecl_then [`s2.cs_next_id`, `w2n ow`, `64`] mp_tac) >>
     simp[]) >>
  `~t3.vs_halted` by
    (qpat_x_assum `t3 with <|vs_vars := _; vs_allocas := _;
      vs_alloca_next := _; vs_inst_idx := _|> = t2`
      (mp_tac o Q.AP_TERM `\z:venom_state. z.vs_halted`) >> simp[]) >>
  `emit_void MSTORE [Var oq; Lit 0w] s3 = (u,s4)` by metis_tac[] >>
  drule_all concat_offset_zero_full >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK t,G3,tn')` by
    (gen_tac >> irule gas_origin_ptr_path_trans >>
     qexistsl [`G1`, `t1`, `tn1`] >>
     conj_tac >- first_assum MATCH_ACCEPT_TAC >>
     irule gas_origin_ptr_path_trans >>
     qexistsl [`G2`, `t2`, `tn2`] >>
     conj_tac >- first_assum MATCH_ACCEPT_TAC >>
     irule gas_origin_ptr_path_trans >>
     qexistsl [`G3`, `t3`, `tn3`] >>
     conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  suspend "frames"
QED

Resume concat_prefix_full[frames]:
  qpat_assum `t2 with <|vs_vars := _; vs_inst_idx := _|> = t1`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [venomStateTheory.venom_state_component_equality]) >>
  qpat_assum `t1 with <|vs_vars := _; vs_allocas := _;
    vs_alloca_next := _; vs_inst_idx := _|> = s`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [venomStateTheory.venom_state_component_equality]) >>
  qpat_assum `t3 with <|vs_vars := _; vs_allocas := _;
    vs_alloca_next := _; vs_inst_idx := _|> = t2`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [venomStateTheory.venom_state_component_equality]) >>
  qpat_assum `t with <|vs_memory := _; vs_inst_idx := _|> = t3`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [venomStateTheory.venom_state_component_equality]) >>
  `not_fresh_at s2 bv /\ not_fresh_at s4 bv /\
   not_fresh_at s4 dp /\ not_fresh_at s4 oq` by
    (conj_tac >- (irule loweringShapeDefsTheory.not_fresh_at_mono >>
       qexists `s1` >> simp[]) >>
     conj_tac >- (irule loweringShapeDefsTheory.not_fresh_at_mono >>
       qexists `s1` >> simp[]) >>
     conj_tac >- (irule loweringShapeDefsTheory.not_fresh_at_mono >>
       qexists `s2` >> simp[]) >>
     irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists `s3` >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at s1 x /\ not_fresh_at s2 x` by
    (rpt strip_tac >>
     irule loweringShapeDefsTheory.not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `!x. not_fresh_at sa x ==>
     lookup_var x t = lookup_var x s /\ FLOOKUP G3 x = FLOOKUP G x /\
     op_taint tn' (Var x) = op_taint tn (Var x)` by
    (gen_tac >> strip_tac >>
     `not_fresh_at s1 x /\ not_fresh_at s2 x` by metis_tac[] >>
     qpat_assum `!x. not_fresh_at sa x ==> _ /\ _ /\ _`
       (qspec_then `x` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
     qpat_assum `!x. not_fresh_at s1 x ==> _ /\ _ /\ _`
       (qspec_then `x` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
     qpat_assum `!x. not_fresh_at s2 x ==> _ /\ _ /\ _`
       (qspec_then `x` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
     gvs[venomStateTheory.lookup_var_def, ptrDisciplineTheory.op_taint_def]) >>
  `!x. not_fresh_at s2 x ==>
     lookup_var x t = lookup_var x t2 /\ FLOOKUP G3 x = FLOOKUP G2 x /\
     op_taint tn' (Var x) = op_taint tn2 (Var x)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!x. not_fresh_at s2 x ==> _ /\ _ /\ _`
       (qspec_then `x` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
     gvs[venomStateTheory.lookup_var_def, ptrDisciplineTheory.op_taint_def]) >>
  `ptr_covers G3 tn' bv t bsz /\ ptr_covers G3 tn' dp t (bsz-32) /\
   ptr_covers G3 tn' oq t 64` by
    (rpt conj_tac
     >- (irule decoderGhostFramePtrTheory.ptr_covers_frame >>
         qexistsl [`G2`, `t2`, `tn2`] >> simp[])
     >- (irule decoderGhostFramePtrTheory.ptr_covers_frame >>
         qexistsl [`G2`, `t2`, `tn2`] >> simp[]) >>
     irule decoderGhostFramePtrTheory.ptr_covers_frame >>
     qexistsl [`G3`, `t3`, `tn3`] >>
     gvs[venomStateTheory.lookup_var_def, ptrDisciplineTheory.op_taint_def]) >>
  suspend "separation"
QED

Resume concat_prefix_full[separation]:
  `FLOOKUP t2.vs_allocas sa.cs_next_id = SOME (w2n bw,bsz)` by metis_tac[] >>
  `FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n bw,bsz)` by metis_tac[] >>
  `regions_disjoint (w2n ow) 64 (w2n bw) bsz` by
    (qpat_assum `!aid b len. aid < s2.cs_next_id /\ _ ==> _`
       (qspecl_then [`sa.cs_next_id`, `w2n bw`, `bsz`] mp_tac) >> simp[]) >>
  `lo <= w2n bw` by
    (qpat_assum `allocas_from lo t1`
       (mp_tac o REWRITE_RULE [ptrDisciplineTheory.allocas_from_def]) >>
     disch_then (qspecl_then [`sa.cs_next_id`, `w2n bw`, `bsz`] mp_tac) >> simp[]) >>
  `!name b len. local_region cenv es.scopes t1 name b len <=>
     local_region cenv es.scopes s name b len` by
    (rw[loweringStateRelDefsTheory.local_region_def] >>
     fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
  `!name b len. local_region cenv es.scopes t3 name b len <=>
     local_region cenv es.scopes s name b len` by
    (rw[loweringStateRelDefsTheory.local_region_def] >>
     fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[venomStateTheory.lookup_var_def]) >>
  `regions_disjoint (w2n bw) bsz (w2n ow) 64` by
    (qpat_assum `regions_disjoint (w2n ow) 64 (w2n bw) bsz` mp_tac >>
     pure_rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
  `lookup_var bv t = SOME bw /\ lookup_var dp t = SOME (n2w (w2n bw+32)) /\
   lookup_var oq t = SOME ow` by
    (gvs[venomStateTheory.lookup_var_def] >> metis_tac[]) >>
  `(!name b len. local_region cenv es.scopes s name b len ==>
     regions_disjoint (w2n bw) bsz b len /\ regions_disjoint (w2n ow) 64 b len) /\
   (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
     regions_disjoint (w2n bw) bsz b len /\ regions_disjoint (w2n ow) 64 b len)` by
    (conj_tac >> rpt gen_tac >> strip_tac
     >- metis_tac[] >>
     `aid < s2.cs_next_id` by simp[] >> metis_tac[]) >>
  suspend "transport"
QED

Resume concat_prefix_full[transport]:
  qpat_x_assum `t = mstore _ _ _ with vs_inst_idx := _` (mk_asm "store_endpoint") >>
  qexistsl [`t`, `G3`, `tn'`, `bv`, `dp`, `oq`, `w2n bw`, `ow`] >>
  simp[wordsTheory.n2w_w2n] >>
  conj_tac >- (qpat_assum `buf.buf_operand = Var bv` mp_tac >>
    qpat_assum `buf.buf_operand = Var (STRING _ _)` SUBST1_TAC >> simp[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (rpt gen_tac >> strip_tac >>
    qpat_assum `!p n. _ ==> mem_bytes_at p n t.vs_memory = _`
      (qspecl_then [`p`, `n`] mp_tac) >> simp[]) >>
  conj_tac >- suspend "return" >>
  conj_tac >- suspend "source" >>
  conj_tac >- suspend "ghost" >>
  suspend "kept"
QED

Resume concat_prefix_full[return]:
  Cases_on `d` >- (qpat_x_assum `return_buf_frame _ _ sa s` mp_tac >>
    pure_rewrite_tac[loweringPostsTheory.return_buf_frame_def] >> simp[]) >>
  PairCases_on `x` >>
  qpat_x_assum `return_buf_frame _ _ sa s` mp_tac >>
  simp[loweringPostsTheory.return_buf_frame_def] >> strip_tac >>
  qexistsl [`x`, `slot_size`] >> simp[] >>
  irule loweringShapeDefsTheory.not_fresh_at_mono >>
  qexists `sa` >> simp[]
QED

Resume concat_prefix_full[source]:
  rpt strip_tac >>
  `stmt_state_rel H ctx func cenv cx es t3` by
    (qpat_assum `!H'. stmt_state_rel H' _ _ _ _ _ t2 ==> _` irule >>
     qpat_assum `!H. stmt_state_rel H _ _ _ _ _ t1 ==> _` irule >>
     qpat_assum `!H'. stmt_state_rel H' _ _ _ _ _ s ==> _` irule >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `!H cenv cx es. _` irule >> simp[] >>
  `MEM (mk_inst (sa.cs_next_id+2) ALLOCA [Lit 64w]
    [STRING #"%" (toString (sa.cs_next_var+2))]) (fn_insts func)` by
    (irule compileAllocaProvenanceTheory.fn_has_code_current_member >>
     qexistsl [`sa`, `s4`] >> simp[]) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es
    (mstore (w2n ow) 0w t3)` by
    (irule loweringSliceTheory.immutables_rel_mstore_alloca >>
     reverse conj_tac >- metis_tac[exprLoweringPropsTheory.stmt_state_rel_def,
       loweringStateRelDefsTheory.state_rel_def] >>
     qexistsl [`w2n ow`, `func`, `mk_inst (sa.cs_next_id+2) ALLOCA [Lit 64w]
       [STRING #"%" (toString (sa.cs_next_var+2))]`, `64`] >>
     simp[venomInstTheory.mk_inst_def] >>
     metis_tac[exprLoweringPropsTheory.stmt_state_rel_def,
       loweringStateRelDefsTheory.state_rel_def]) >>
  qpat_x_assum `immutables_rel _ _ _ _ _ (mstore _ _ _)` mp_tac >>
  asm "store_endpoint" (fn th => simp[NoAsms, th,
    loweringStateRelDefsTheory.immutables_rel_def]) >>
  metis_tac[]
QED

Resume concat_prefix_full[ghost]:
  rpt strip_tac >>
  `ghost_inv_at D lo d cenv cx es G1 tn1 t1` by
    (first_assum irule >> first_assum ACCEPT_TAC) >>
  `ghost_inv_at D lo d cenv cx es G2 tn2 t2` by metis_tac[] >>
  `ghost_inv_at D lo d cenv cx es G3 tn3 t3` by
    (first_assum irule >> first_assum ACCEPT_TAC) >>
  `local_ptrs_reserved cenv s3` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s3 x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s3 x)` by
    (conj_tac >> rpt gen_tac >> strip_tac >>
     irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists `sa` >> simp[] >> metis_tac[]) >>
  `local_ptrs_rel func cenv es.scopes t3` by
    metis_tac[stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def] >>
  irule (Q.INST [`sa` |-> `s3`, `fn` |-> `func`, `s` |-> `t3`,
    `es` |-> `es`, `tn` |-> `tn3`] ghost_inv_at_local_window_transport) >>
  simp[] >> conj_tac
  >- (`stor_taint_ok_at D tn3 t3` by
        metis_tac[bodyPtrDefsTheory.ghost_inv_at_def] >>
      qpat_x_assum `stor_taint_ok_at D tn3 t3` mp_tac >>
      simp[bodyPtrDefsTheory.stor_taint_ok_at_def]) >>
  qexistsl [`G3`, `es`, `func`, `s3`, `t3`, `tn3`] >>
  simp[venomStateTheory.lookup_var_def, ptrDisciplineTheory.op_taint_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `regions_disjoint (w2n ow) 64 b len` by metis_tac[] >>
      qpat_assum `!p n. _ ==> mem_bytes_at p n t.vs_memory = _`
        (qspecl_then [`b`, `len`] mp_tac) >>
      (impl_tac >- (qpat_x_assum `regions_disjoint (w2n ow) 64 b len` mp_tac >>
        pure_rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac)) >>
      simp[]) >>
  rpt strip_tac >> `~(s.vs_alloca_next <= i)` by decide_tac >>
  `~(t1.vs_alloca_next <= i)` by decide_tac >> metis_tac[]
QED

Resume concat_prefix_full[kept]:
  `alloca_inv s` by metis_tac[stmt_state_rel_def] >>
  `!aid off sz. FLOOKUP s.vs_allocas aid = SOME (off,sz) ==>
     off + sz <= s.vs_alloca_next` by
    (qpat_assum `alloca_inv s` mp_tac >>
     pure_rewrite_tac[venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.alloca_next_valid_def] >> metis_tac[]) >>
  `!name b sz. local_region cenv es.scopes s name b sz ==>
     b + sz <= s.vs_alloca_next` by
    metis_tac[bodyMemoryDefsTheory.body_local_region_frontier] >>
  `ghost_kept_at lo cenv es sa G tn s G tn` by
    simp[wordArgsPtrTheory.ghost_kept_at_refl] >>
  `ghost_kept_at lo cenv es sa G tn s G1 tn1` by
    (irule (Q.INST [`s` |-> `s`, `e` |-> `w2n (bw:bytes32)+bsz`]
      alloc_buffer_ghost_kept_at) >>
     qexistsl [`G`, `bsz`, `bw`, `s`, `tn`] >> simp[] >> metis_tac[]) >>
  `ghost_kept_at lo cenv es sa G tn s G2 tn2` by
    (irule ghost_kept_at_clean_suffix >> qexistsl [`G1`, `tn1`] >>
     simp[] >> metis_tac[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at s2 x` by
    (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists `sa` >> simp[]) >>
  `ghost_kept_at lo cenv es sa G tn s G3 tn3` by
    (irule (Q.INST [`e` |-> `w2n (ow:bytes32)+64`]
      alloc_buffer_ghost_kept_at) >>
     qexistsl [`G2`, `ow`, `t2`, `tn2`] >> simp[] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  irule ghost_kept_at_clean_suffix >> qexistsl [`G3`, `tn3`] >>
  simp[ptrDisciplineTheory.op_taint_def, pred_setTheory.DIFF_SUBSET]
QED

Finalise concat_prefix_full

Theorem concat_suffix_full:
  emit_op MLOAD [Var ov] sa = (fo,sm) /\
  emit_void MSTORE [Var bv;fo] sm = (u,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  not_fresh_at sa ov /\ not_fresh_at sa bv /\
  lookup_var ov s = SOME ow /\ lookup_var bv s = SOME (n2w B) /\
  ptr_covers G tn ov s 32 /\ ptr_covers G tn bv s bsz /\
  32 <= bsz /\ B+bsz < dimword (:256) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (B,bsz) /\
  w2n ow+32 <= s.vs_alloca_next /\ B+32 <= s.vs_alloca_next /\
  mload (w2n ow) s = n2w k /\ k < dimword (:256) /\
  (!i. w2n ow <= i /\ i < w2n ow+32 ==> i NOTIN tn.t_mem) /\
  stmt_state_rel (H0:(bool # bytes32 # type_value) list # num list) ctx func cenv cx es s /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\ lo <= B /\
  return_buf_frame d cenv sa s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!name b len. local_region cenv es.scopes s name b len ==>
    regions_disjoint B 32 b len) ==>
  ?t G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    t = (mstore B (n2w k) (update_var (STRING #"%" (toString sa.cs_next_var)) (n2w k) s)
      with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    mload B t = n2w k /\ ptr_covers G' tn' bv t bsz /\
    (!i. B <= i /\ i < B+32 ==> i NOTIN tn'.t_mem) /\
    tn'.t_mem SUBSET tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    alloca_history func t /\ allocas_from lo t /\ return_buf_frame d cenv sb t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!p n. p+n <= B \/ B+32 <= p ==>
      mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory) /\
    (!(H:(bool # bytes32 # type_value) list # num list).
      stmt_state_rel H ctx func cenv cx es s ==> stmt_state_rel H ctx func cenv cx es t) /\
    (!D. ghost_inv_at D lo d cenv cx es G tn s ==> ghost_inv_at D lo d cenv cx es G' tn' t) /\
    ghost_kept_at lo cenv es sa G tn s G' tn'
Proof
  strip_tac >> Cases_on `u` >>
  drule_all concat_suffix_code >> strip_tac >>
  `fo = Var (STRING #"%" (toString sa.cs_next_var))` by simp[] >>
  qpat_x_assum `fo = _` SUBST_ALL_TAC >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  drule_all assignTuplePtrLocalBytesCopyTheory.mload_clean_seq_ptr >>
  disch_then (qspecl_then [`ARB`, `func`, `PG`, `sa.cs_next_id`, `out`] strip_assume_tac) >>
  rename1 `inst_seq_ptr ARB 0 ctx func PG G tn _ s Gf tnf` >>
  rename1 `run_inst_seq _ s = OK sf` >>
  `!D. inst_seq_ptr D 0 ctx func PG G tn
      [mk_inst sa.cs_next_id MLOAD [Var ov] [out]] s Gf tnf` by
    (gen_tac >> drule_all assignTuplePtrLocalBytesCopyTheory.mload_clean_seq_ptr >>
     disch_then (qspecl_then [`D`, `func`, `PG`, `sa.cs_next_id`, `out`] strip_assume_tac) >>
     gvs[inst_seq_ptr_def]) >>
  `!x. not_fresh_at sa x ==> x <> out` by
    simp[Abbr `out`, loweringStateRelDefsTheory.not_fresh_at_def] >>
  `bv <> out` by metis_tac[] >>
  `FLOOKUP Gf bv = FLOOKUP G bv /\ op_taint tnf (Var bv) = op_taint tn (Var bv)` by metis_tac[] >>
  `lookup_var bv sf = SOME (n2w B) /\ ptr_covers Gf tnf bv sf bsz` by
    (simp[bodyPtrDefsTheory.ptr_covers_def, venomStateTheory.lookup_var_def,
       venomStateTheory.update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
     gvs[bodyPtrDefsTheory.ptr_covers_def, venomStateTheory.lookup_var_def]) >>
  `ptr_covers Gf tnf bv sf 32` by
    (fs[bodyPtrDefsTheory.ptr_covers_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.ADD_MONO_LESS_EQ]) >>
  qabbrev_tac `ss = sf with vs_inst_idx := s.vs_inst_idx+1` >>
  `ptr_covers Gf tnf bv ss 32 /\
   eval_operand (Var bv) ss = SOME (n2w B) /\
   eval_operand (Var out) ss = SOME (n2w k)` by
    (simp[Abbr `ss`, venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
      bodyPtrDefsTheory.ptr_covers_def, venomStateTheory.update_var_def,
      finite_mapTheory.FLOOKUP_UPDATE] >>
     gvs[venomStateTheory.lookup_var_def]) >>
  drule_all wordLoadStorePtrTheory.ifexp_copy_store_phase >>
  disch_then (qspecl_then [`sa.cs_next_id+1`, `func`, `PG`, `ARB`] strip_assume_tac) >>
  `B < dimword (:256)` by decide_tac >>
  `w2n (n2w B : bytes32) = B` by simp[] >>
  `!D. inst_seq_ptr D 0 ctx func PG Gf tnf
      [mk_inst (sa.cs_next_id+1) MSTORE [Var bv;Var out] []] ss Gf tn'` by
    (gen_tac >> drule_all wordLoadStorePtrTheory.ifexp_copy_store_phase >>
     disch_then (qspecl_then [`sa.cs_next_id+1`, `func`, `PG`, `D`] strip_assume_tac) >>
     gvs[inst_seq_ptr_def]) >>
  `!D. inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s Gf tn'` by
    (gen_tac >> simp[] >>
     irule (SRULE [listTheory.APPEND] (Q.SPEC
       `[mk_inst sa.cs_next_id MLOAD [Var ov] [out]]`
       assignTuplePtrLocalBytesCopyTheory.inst_seq_ptr_append_run)) >>
     simp[venomInstTheory.is_terminator_def] >>
     qexistsl [`Gf`, `tnf`] >> simp[Abbr `ss`] >> metis_tac[]) >>
  drule_all concat_suffix_run >> strip_tac >>
  `step_inst_base (mk_inst sa.cs_next_id MLOAD [Var ov] [out]) s = OK sf` by
    (qpat_x_assum `run_inst_seq [_] s = OK sf` mp_tac >>
     simp[run_inst_seq_def, AllCaseEqs()]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (simp[fragExecMemTheory.run_inst_seq_mem_ok_cons,
       unitTransformDefsTheory.inst_mem_below_frontier_def,
       memSafeRunTheory.inst_dload_in_section_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def,
       codegenRelTheory.fixed_source_write_range_def,
       venomStateTheory.eval_operand_def] >>
     simp[fragExecMemTheory.run_inst_seq_mem_ok_last,
       unitTransformDefsTheory.inst_mem_below_frontier_def,
       memSafeRunTheory.inst_dload_in_section_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def,
       codegenRelTheory.fixed_source_write_range_def,
       venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
       venomStateTheory.update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
     gvs[venomStateTheory.lookup_var_def]) >>
  qabbrev_tac `raw = mstore B (n2w k) (update_var out (n2w k) s)` >>
  `run_inst_seq (emitted_insts sa sb) s = OK raw` by
    simp[Abbr `raw`, Abbr `out`] >>
  `!D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s Gf tn'` by
    (gen_tac >> irule inst_seq_ptr_zero_to_lo >>
     simp[] >> qexists `D` >> simp[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (raw with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tn')` by
    (gen_tac >> irule bodyFullUnwrapRunTheory.emitted_origin_ptr_path >>
     simp[] >> qexistsl [`emitted_insts sa sb`, `sa`] >>
     gvs[venomInstTheory.is_terminator_def, venomInstTheory.mk_inst_def]) >>
  `alloca_inv s` by metis_tac[stmt_state_rel_def] >>
  `alloca_history func (raw with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule emitted_alloca_history >>
     simp[] >> qexistsl [`emitted_insts sa sb`, `s`, `sa`] >>
     gvs[venomInstTheory.is_terminator_def, venomInstTheory.mk_inst_def]) >>
  `tn'.t_mem = tn.t_mem DIFF {i | B <= i /\ i < B+32}` by simp[] >>
  qabbrev_tac `fin = raw with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `fin.vs_allocas = s.vs_allocas /\ fin.vs_alloca_next = s.vs_alloca_next /\
   fin.vs_current_bb = sb.cs_current_bb /\
   fin.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~fin.vs_halted` by
    simp[Abbr `fin`, Abbr `raw`, venomStateTheory.mstore_def,
      venomStateTheory.update_var_def] >>
  `!x. not_fresh_at sa x ==> lookup_var x fin = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)` by
    (rpt gen_tac >> strip_tac >> `x <> out` by metis_tac[] >>
     simp[Abbr `fin`, Abbr `raw`, venomStateTheory.mstore_def,
       venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, ptrDisciplineTheory.op_taint_def] >>
     qpat_x_assum `!p. p <> out ==> _` (qspec_then `x` mp_tac) >>
     simp[ptrDisciplineTheory.op_taint_def]) >>
  qexistsl [`fin`, `Gf`, `tn'`] >>
  simp[Abbr `fin`, GSYM markerTheory.Abbrev_def] >>
  conj_tac >- (simp[Once venomStateTheory.mload_def] >>
    rewrite_tac[GSYM (SRULE [] venomStateTheory.mload_def)] >>
    metis_tac[venomStateTheory.mload_def, Abbr `raw`,
      venomMemPropsTheory.mload_mstore_same]) >>
  conj_tac >- (simp[Abbr `raw`, bodyPtrDefsTheory.ptr_covers_def,
    venomStateTheory.mstore_def, venomStateTheory.update_var_def,
    venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
    ptrDisciplineTheory.op_taint_def] >>
    gvs[bodyPtrDefsTheory.ptr_covers_def, venomStateTheory.lookup_var_def,
      ptrDisciplineTheory.op_taint_def]) >>
  conj_tac >- (simp[Abbr `raw`, ptrDisciplineTheory.allocas_from_def,
    venomStateTheory.mstore_def, venomStateTheory.update_var_def] >>
    metis_tac[ptrDisciplineTheory.allocas_from_def]) >>
  conj_tac >- suspend "suffix_return" >>
  conj_tac >- suspend "suffix_memory" >>
  conj_tac >- suspend "suffix_source" >>
  conj_tac >- suspend "suffix_ghost" >>
  suspend "suffix_kept"
QED

Resume concat_suffix_full[suffix_return]:
  Cases_on `d` >- (gvs[loweringPostsTheory.return_buf_frame_def]) >>
  PairCases_on `x` >>
  qpat_x_assum `return_buf_frame _ _ sa s` mp_tac >>
  simp[loweringPostsTheory.return_buf_frame_def] >> strip_tac >>
  qexistsl [`x`, `slot_size`] >>
  `not_fresh_at sb x` by
    (irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists `sa` >> simp[]) >>
  simp[Abbr `raw`, venomStateTheory.mstore_def,
    venomStateTheory.update_var_def, venomStateTheory.lookup_var_def,
    finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[venomStateTheory.lookup_var_def]
QED

Resume concat_suffix_full[suffix_memory]:
  rpt gen_tac >> disch_tac >>
  `mem_bytes_at p n (mstore B (n2w k) (update_var out (n2w k) s)).vs_memory =
   mem_bytes_at p n (update_var out (n2w k) s).vs_memory` by
    (irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
       fs[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  pop_assum mp_tac >>
  simp[Abbr `raw`, venomStateTheory.update_var_def]
QED

Resume concat_suffix_full[suffix_source]:
  rpt strip_tac >> simp[exprLoweringPropsTheory.stmt_state_rel_inst_idx] >>
  `not_local_ptr cenv es.scopes out` by
    (irule exprSimOperandsTheory.fresh_not_local_ptr >>
     qexists `sa` >> simp[] >> metis_tac[]) >>
  `stmt_state_rel H ctx func cenv cx es (update_var out (n2w k) s)` by
    metis_tac[exprLoweringPropsTheory.stmt_state_rel_update_var] >>
  simp[Abbr `raw`, venomMemPropsTheory.mstore_eq_write_mem] >>
  irule exprSimPrecompilesTheory.write_memory_stmt_state_rel >> simp[] >>
  conj_tac >- (rpt strip_tac >>
    `local_region cenv es.scopes s name b sz` by
      metis_tac[revertReasonPrefixPtrTheory.local_region_update_nonlocal] >>
    `regions_disjoint B 32 b sz` by metis_tac[] >>
    fs[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es
    (mstore B (n2w k) (update_var out (n2w k) s))` by
    (irule loweringSliceTheory.immutables_rel_mstore_alloca >>
     reverse conj_tac >- metis_tac[exprLoweringPropsTheory.stmt_state_rel_def,
       loweringStateRelDefsTheory.state_rel_def] >>
     qexistsl [`B`, `func`, `inst`, `bsz`] >>
     simp[venomStateTheory.update_var_def] >>
     qpat_x_assum `stmt_state_rel H ctx func cenv cx es (update_var _ _ s)` mp_tac >>
     simp[exprLoweringPropsTheory.stmt_state_rel_def,
       loweringStateRelDefsTheory.state_rel_def, venomStateTheory.update_var_def]) >>
  pop_assum mp_tac >>
  simp[venomMemPropsTheory.mstore_eq_write_mem]
QED

Resume concat_suffix_full[suffix_ghost]:
  rpt strip_tac >>
  `local_ptrs_rel func cenv es.scopes s` by
    metis_tac[exprLoweringPropsTheory.stmt_state_rel_def,
      loweringStateRelDefsTheory.state_rel_def] >>
  irule (Q.INST [`sa` |-> `sa`, `fn` |-> `func`, `s` |-> `s`,
    `es` |-> `es`, `tn` |-> `tn`] ghost_inv_at_local_window_transport) >>
  simp[] >>
  conj_tac >- simp[Abbr `raw`, venomStateTheory.update_var_def, venomStateTheory.mstore_def] >>
  conj_tac >- (simp[Abbr `raw`, ptrDisciplineTheory.allocas_from_def,
    venomStateTheory.update_var_def, venomStateTheory.mstore_def] >>
    metis_tac[ptrDisciplineTheory.allocas_from_def]) >>
  conj_tac >- (qpat_x_assum `ghost_inv_at D lo d cenv cx es G tn s` mp_tac >>
    simp[bodyPtrDefsTheory.ghost_inv_at_def, bodyPtrDefsTheory.stor_taint_ok_at_def, Abbr `raw`,
      venomStateTheory.update_var_def, venomStateTheory.mstore_def]) >>
  qexistsl [`G`, `es`, `func`, `s`, `sa`, `tn`] >>
  simp[] >>
  conj_tac >- (rpt strip_tac >>
    qpat_x_assum `!x. not_fresh_at sa x ==> _` drule >> simp[]) >>
  conj_tac >- (rpt strip_tac >>
    `regions_disjoint B 32 b len` by metis_tac[] >>
    `mem_bytes_at b len (mstore B (n2w k) (update_var out (n2w k) s)).vs_memory =
     mem_bytes_at b len (update_var out (n2w k) s).vs_memory` by
      (irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
       fs[loweringStateRelDefsTheory.regions_disjoint_def]) >>
    pop_assum mp_tac >> simp[Abbr `raw`, venomStateTheory.update_var_def]) >>
  `regions_disjoint B 32 0 lo` by
    simp[loweringStateRelDefsTheory.regions_disjoint_def] >>
  `mem_bytes_at 0 lo (mstore B (n2w k) (update_var out (n2w k) s)).vs_memory =
   mem_bytes_at 0 lo (update_var out (n2w k) s).vs_memory` by
    (irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
       fs[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  pop_assum mp_tac >> simp[Abbr `raw`, venomStateTheory.update_var_def]
QED

Resume concat_suffix_full[suffix_kept]:
  simp[bodyPtrDefsTheory.ghost_kept_at_def]
QED

Finalise concat_suffix_full
