(* Shared same-witness storage materialization proof, with caller-specific
   final assertions and existential assembly. No theorem registration here. *)
structure bodyPtrStorageSingleProofLib =
struct
open HolKernel boolLib bossLib
open bodyPtrIfExpMaterializeSingleTheory bodyPtrIfExpStorageSupplierTheory
  bodyPtrIfExpStorageAllocationTheory bodyPtrIfExpStorageSourceTheory
  compileEnvTheory loweringStateRelDefsTheory emitHelperTheory
  bodyPtrIfExpStorageAllocationFrameTheory bodyPtrIfExpSingleCopyPostTheory
  bodyPtrIfExpActiveCopyPostTheory bodyPtrIfExpAllocSourceTheory
  valueEncodingTypingTheory bodyPtrIfExpBytesInputsTheory
  loweringPostsTheory venomStateTheory finite_mapTheory loweringHaltTheory

fun start single_code =
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`) ifexp_storage_arm_source >>
  simp[] >> disch_then drule_all >> strip_tac >>
  drule_at (Pat `compile_ensure_in_memory _ _ _ _ _ _ _ = _`) single_code >>
  simp[] >> disch_then drule >> strip_tac >>
  `compile_alloc_buffer 32 sb = (buf,cs)` by simp[] >>
  drule_at (Pat `compile_alloc_buffer _ _ = _`) ifexp_copy_allocation_start >>
  simp[wordsTheory.dimword_def] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule_at (Pat `step_inst_base _ _ = _`)
    (SRULE [] (Q.INST [`n` |-> `1`] ifexp_copy_allocation_loop_bounds)) >>
  simp[] >> disch_then drule_all >> strip_tac;

fun execute load_step g = (
  qmatch_asmsub_abbrev_tac `ptr_covers Gb tb out u 32` >>
  drule_at (Pat `step_inst_base _ _ = _`)
    (SRULE [] (Q.INST [`n` |-> `32`] bodyPtrIfExpAllocSourceTheory.alloca_step_contracts)) >>
  simp[wordsTheory.dimword_def] >> strip_tac >>
  `tb.t_stor = tn.t_stor /\ tb.t_trans = tn.t_trans` by
    simp[Abbr `tb`, decoderGhostFramePtrTheory.step_taint_nonmemory_frame, venomInstTheory.mk_inst_def] >>
  `not_fresh_at cs out` by
    (drule compile_alloc_buffer_parts >> simp[] >> metis_tac[]) >>
  `lookup_var out u = SOME d` by gvs[venomStateTheory.eval_operand_def] >>
  qabbrev_tac `r = u with vs_inst_idx := LENGTH cs.cs_current_insts` >>
  qabbrev_tac `opc = if pp.ptr_location = LocStorage then SLOAD else TLOAD` >>
  qabbrev_tac `w = lookup_storage p (if pp.ptr_location = LocStorage
    then contract_storage s else contract_transient s)` >>
  `MEM opc [SLOAD;TLOAD]` by
    (Cases_on `pp.ptr_location = LocStorage` >> simp[Abbr `opc`]) >>
  `step_inst_base (mk_inst cs.cs_next_id opc [pp.ptr_operand]
    [STRING #"%" (toString cs.cs_next_var)]) r =
    OK (update_var (STRING #"%" (toString cs.cs_next_var)) w r)` by
    (`eval_operand pp.ptr_operand r = SOME p` by simp[Abbr `r`] >>
     drule_at (Pat `eval_operand _ r = _`) load_step >>
     disch_then (qspecl_then [`STRING #"%" (toString cs.cs_next_var)`, `opc`, `cs.cs_next_id`] mp_tac) >>
     Cases_on `pp.ptr_location = LocStorage` >>
     simp[Abbr `r`, Abbr `opc`, Abbr `w`,
       venomStateTheory.sload_def, venomStateTheory.tload_def,
       venomStateTheory.contract_storage_def, venomStateTheory.contract_transient_def]) >>
  ` (do loaded <- emit_op opc [pp.ptr_operand];
       emit_void MSTORE [Var out;loaded] od) cs = ((),sd)` by metis_tac[] >>
  `eval_operand pp.ptr_operand r = SOME p /\ lookup_var out r = SOME d /\
   ptr_covers Gb tb out r 32 /\ ~r.vs_halted /\
   r.vs_current_bb = cs.cs_current_bb /\ r.vs_inst_idx = LENGTH cs.cs_current_insts` by
    (fs[venomStateTheory.lookup_var_def] >> simp[Abbr `r`, venomStateTheory.lookup_var_def]) >>
  drule_at (Pat `step_inst_base _ r = _`) ifexp_materialize_single_path >>
  disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac)) g;

fun frames g = (
  `out' <> out` by metis_tac[] >>
  drule_at (Pat `G2 = _`) ifexp_materialize_single_effect >>
  disch_then drule_all >> disch_then (qspec_then `LENGTH sd.cs_current_insts` strip_assume_tac) >>
  `!x. not_fresh_at sa x ==> x <> out'` by
    (drule compile_alloc_buffer_parts >> strip_tac >>
     metis_tac[loweringShapeDefsTheory.not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS]) >>
  `ghost_inv rty ce cx ee Gb tb r` by simp[Abbr `r`] >>
  `eval_operand (Var out) s1 = SOME d` by
    (qpat_x_assum `s1 = _` SUBST1_TAC >>
     simp[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
       venomStateTheory.update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
     metis_tac[venomStateTheory.lookup_var_def]) >>
  `!name entry b sz z. lookup_scopes name ee.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var b) sz) /\ lookup_var b s1 = SOME z ==>
    val_wf entry.type entry.value /\
    (w2n z+type_memory_size entry.type <= w2n d \/ w2n d+32 <= w2n z)` by
    (rpt strip_tac >>
     `b <> out'` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
     `lookup_var b r = SOME z` by
       (qpat_x_assum `lookup_var b s1 = _` mp_tac >>
        qpat_x_assum `s1 = _` SUBST1_TAC >>
        simp[venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
          finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]) >>
     qpat_x_assum `!name entry v sz w. _` drule_all >> simp[]) >>
  `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!name p len. local_region ce es.scopes s0 name p len ==> off+sz <= p \/ p+len <= off) ==>
    off+sz <= w2n d \/ w2n d+32 <= off` by metis_tac[] >>
  `!name b len. local_region ce es.scopes s0 name b len ==>
    b+len <= w2n d \/ w2n d+32 <= b` by metis_tac[arithmeticTheory.ADD_COMM] >>
  drule_at (Pat `tn2 = _`) ifexp_materialize_single_frames >> disch_then drule_all >>
  disch_then (qspec_then `LENGTH sd.cs_current_insts` strip_assume_tac)) g;

fun robust single_robust g = (
  `u' = mstore (w2n d) (lookup_storage p
    (if pp.ptr_location = LocStorage then contract_storage s else contract_transient s)) s1` by
    simp[Abbr `w`] >>
  drule_at (Pat `u' = mstore _ (lookup_storage _ _) _`) single_robust >>
  disch_then (drule_at (Pat `decode_value _ _ _ = _`)) >> simp[] >>
  disch_then (qspecl_then [`if pp.ptr_location = LocStorage then tn.t_stor else tn.t_trans`,
    `tb.t_mem`] assume_tac) >>
  `!m. mem_agree_outside tn2.t_mem u'.vs_memory m ==> val_in_memory tvt v (w2n d) m` by
    (gen_tac >> disch_tac >> first_x_assum irule >>
     Cases_on `pp.ptr_location = LocStorage` >> simp[Abbr `opc`, arithmeticTheory.ADD_COMM] >>
     qpat_x_assum `mem_agree_outside tn2.t_mem _ m` mp_tac >>
     qpat_x_assum `tn2.t_mem = _` SUBST1_TAC >>
     qpat_x_assum `u' = mstore _ w s1` SUBST1_TAC >> simp[arithmeticTheory.ADD_COMM]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G2 tn2
    (OK (u' with vs_inst_idx := LENGTH sd.cs_current_insts))` by
    (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] fragGasPathPtrTheory.gas_path_ptr_then)) >>
     qexistsl_tac [`Gb`, `r`, `tb`] >> conj_tac
     >- (qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn _ _ Gb tb _` mp_tac >> simp[Abbr `r`]) >>
     first_assum ACCEPT_TAC) >>
  `eval_operand (Var out) (u' with vs_inst_idx := LENGTH sd.cs_current_insts) = SOME d` by
    (qpat_x_assum `lookup_var out u' = _` mp_tac >>
     simp[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def]) >>
  `~u'.vs_halted` by
    simp[venomStateTheory.mstore_def, venomStateTheory.write_memory_with_expansion_def,
      venomStateTheory.update_var_def]) g;

fun ordinary g = (
  `local_ptrs_reserved ce sb` by metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `stmt_state_rel ctx fn ce cx ee s` by fs[loweringPostsTheory.vv_post_def] >>
  `!x. not_fresh_at sb x ==> x <> out'` by
    (drule compile_alloc_buffer_parts >> strip_tac >>
     metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]) >>
  `u' with vs_inst_idx := LENGTH sd.cs_current_insts =
   (mstore (w2n d) w (update_var out' w (u with vs_inst_idx := LENGTH cs.cs_current_insts)))
     with vs_inst_idx := LENGTH sd.cs_current_insts` by
    (qpat_x_assum `s1 = _` SUBST_ALL_TAC >>
     simp[Abbr `r`, venomStateTheory.mstore_def, venomStateTheory.update_var_def]) >>
  drule_at (Pat `t = (mstore _ _ _) with vs_inst_idx := _`) ifexp_storage_single_allocation_frame >>
  disch_then drule_all >> strip_tac) g;

val semantic =
  drule_all ifexp_arm_annotation_typed >> strip_tac >>
  `val_wf tvt v /\ val_footprint tvt v <= 32` by
    (metis_tac[value_has_type_val_wf, exprSimPropsTheory.val_footprint_le, optionTheory.SOME_11]) >>
  `val_in_memory tvt v (w2n d) u'.vs_memory` by
    (qpat_x_assum `!m. mem_agree_outside tn2.t_mem _ m ==> _`
       (qspec_then `u'.vs_memory` mp_tac) >> simp[bodyPtrDefsTheory.mem_agree_outside_def]) >>
  `!x. not_fresh_at cs x ==> x <> out'` by
    (qpat_x_assum `out' = _` SUBST1_TAC >> simp[not_fresh_at_def]) >>
  drule_at (Pat `t = (mstore _ _ _) with vs_inst_idx := _`)
    (Q.INST [`cs` |-> `cs`] ifexp_single_copy_frame) >> disch_then drule_all >> strip_tac >>
  `cs.cs_next_id <= sd.cs_next_id` by
    (qpat_x_assum `(do loaded <- emit_op _ _; _ od) cs = _` mp_tac >> rpt (pop_assum kall_tac) >>
     simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[]);

val post =
  `tv = tvt` by metis_tac[optionTheory.SOME_11] >>
  `!x. not_fresh_at cs x ==> x <> out'` by
    (qpat_x_assum `out' = _` SUBST1_TAC >> simp[not_fresh_at_def]) >>
  `~is_word_type (expr_type e) ==>
    expr_post ctx fn ce cx e es sa sd s0 ee v dst
      (u' with vs_inst_idx := LENGTH sd.cs_current_insts)` by
    (strip_tac >> irule ifexp_single_allocated_copy_post >>
     conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`buf`, `cs`, `d`, `LENGTH cs.cs_current_insts`,
       `LENGTH sd.cs_current_insts`, `out`, `raw`, `s`, `sb`, `out'`, `tvt`,
       `u`, `LocatedValue tag pp`, `w`] >>
     qpat_x_assum `eval_operand (Var out) (u' with vs_inst_idx := _) = SOME d` mp_tac >>
     qpat_x_assum `val_in_memory tvt v (w2n d) u'.vs_memory` mp_tac >> simp[not_fresh_at_def]);

val assemble =
  qexistsl_tac [`d`, `u' with vs_inst_idx := LENGTH sd.cs_current_insts`, `G2`, `tn2`] >>
  simp[NoAsms] >>
  conj_tac >- (pure_rewrite_tac[venomStateTheory.eval_operand_def] >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qpat_x_assum `ptr_covers G2 tn2 out _ 32` mp_tac >> simp[NoAsms]) >>
  conj_tac >- (qpat_x_assum `ghost_inv rty ce cx ee G2 tn2 _` mp_tac >> simp[NoAsms]) >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (rpt gen_tac >> strip_tac >>
    qpat_x_assum `!name pos len. local_region _ _ _ _ _ _ ==> _` drule_all >> decide_tac) >>
  rule_assum_tac (SIMP_RULE (srw_ss()) []) >>
  rpt conj_tac >> asm_rewrite_tac [] >>
  qpat_x_assum `~is_word_type _ ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >> simp[];
end
