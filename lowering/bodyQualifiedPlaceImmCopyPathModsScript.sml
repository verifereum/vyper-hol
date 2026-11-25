(* Execute the nonword LocCode store after the saved operand is unwrapped. *)
Theory bodyQualifiedPlaceImmCopyPathMods
Ancestors
  bodyAssignLocalPlaceRoutesMods bodyFullImmutablePathStore bodySlotCopyNormalizeMods
  immutableAssignStore immutableAssignOpen immutableAssignRepresentation
  immutableBytestringPath exprSimCopy exprLoweringProps
  fragGasOriginPtrLoop freshWrites
  venomState typedMemoryCopy stmtLowering compileEnv ptrDiscipline
  bodyFullShared bodyFullShadowBodyInv bodyFullPostsMods bodyPtrDefs bodySimFull
  fragGasOriginPtr stmtSimDefs fragExec valueTypingMemoryProps
  loweringPosts loweringStateRelDefs words finite_map stmtLoweringMono gasOriginPtrLabels
  arithmetic list venomWf bodyMemoryDefs


val bounds =
  ``copy_old_operand sa dst /\ eval_operand dst s = SOME (n2w dest) /\
    op_taint tn dst = {} /\ op_prov G dst = NONE /\
    dest + type_memory_size dtv <= lo /\ lo <= s.vs_alloca_next /\
    lo < dimword (:256) /\
    (!base. cenv.ce_imm_alloca = SOME base ==> eval_operand base s = SOME 0w /\
       copy_old_operand sa base /\ op_taint tn base = {} /\ op_prov G base = NONE) /\
    allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    fn_has_code sa sb func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts``;

val source =
  ``not_fresh_at sa xs /\ lookup_var xs s = SOME (n2w a) /\
    ptr_covers G tn xs s (type_memory_size stv) /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory stv v a mem) /\
    lo <= a /\ a + type_memory_size stv < dimword (:256) /\
    a + type_memory_size stv <= s.vs_alloca_next``;

val value_types =
  ``type_widens_to (get_tenv cx) sty dty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\ value_has_type stv v /\
    value_has_type dtv v``;

val run_post =
  ``?q Gf tf. immutable_path_store_post (lo,explicit,ctx,func,PG) dest dtv v
      sa sb (s,G,tn) (q,Gf,tf)``;

Theorem imm_copy_flat[local]:
  compile_assign_value cenv dst LocCode (Var xs) F loc dty sty
      (type_memory_size dtv) sa = ((),sb) /\
  (sty = dty \/ is_bytestring_type dty) /\ 0 < type_memory_size dtv /\
  ^value_types /\ ^source /\ ^bounds ==>
  ^run_post
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `eval_operand (Var xs) s = SOME (n2w a)` by simp[eval_operand_def] >>
  Cases_on `is_bytestring_type dty`
  >- (drule_all_then assume_tac typed_copy_bytestring_source >>
      `compile_store_immutable_bytestring cenv.ce_imm_alloca (Var xs) dst sa = ((),sb)` by
        fs[compile_assign_value_def,comp_bind_def,comp_return_def] >>
      `!base. cenv.ce_imm_alloca = SOME base ==> eval_operand base s = SOME 0w /\
          op_taint tn base = {} /\ op_prov G base = NONE` by
        (rpt strip_tac >> first_x_assum drule >> simp[]) >>
      `!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x` by
        (rpt strip_tac >>
         qpat_assum `!base. cenv.ce_imm_alloca = SOME base ==> _`
           (drule_then strip_assume_tac) >> fs[copy_old_operand_def]) >>
      drule_at (Pat `compile_store_immutable_bytestring _ _ _ _ = _`)
        body_assign_immutable_bytes_path_store >>
      disch_then irule >> simp[] >> qexistsl_tac [`a`,`cx`,`dty`,`stv`,`sty`] >> simp[]) >>
  `sty = dty` by fs[] >>
  qpat_x_assum `sty = dty` SUBST_ALL_TAC >>
  `stv = dtv` by fs[] >>
  qpat_x_assum `stv = dtv` SUBST_ALL_TAC >>
  drule_at (Pat `compile_assign_value _ _ LocCode (Var xs) F _ _ _ _ sa = _`)
    immutable_path_store_fixed >>
  disch_then irule >> simp[] >> qexists_tac `a` >> simp[]
QED

val normalize_ready =
  ``stmt_state_rel (H0 : (bool # bytes32 # type_value) list # num list) ctx func cenv cx es s /\
    local_ptrs_reserved cenv sa /\ fn_inst_ids_distinct func /\ alloca_history func s /\
    expr_val_at cenv cx sty start sa es v (Var xs) s /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
       ALL_DISTINCT (MAP FST fields) /\
       EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
         sz = type_memory_size tv) fields) /\
    (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
    (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x)``;

val cut_post =
  ``?sm u Gu tu q Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu)) /\
    immutable_path_store_post (lo,explicit,ctx,func,PG) dest dtv v sm sb (u,Gu,tu) (q,Gf,tf) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK q,Gf,tf)) /\
    (!H : (bool # bytes32 # type_value) list # num list.
       stmt_state_rel H ctx func cenv cx es s ==> stmt_state_rel H ctx func cenv cx es u) /\
    (immutable_frame_mods func cenv cx es s ==> immutable_frame_mods func cenv cx es u) /\
    (!D d. ghost_inv_at_mods D lo d cenv cx es G tn s ==>
       ghost_inv_at_mods D lo d cenv cx es Gu tu u) /\
    (!d. return_buf_frame d cenv sa s ==> return_buf_frame d cenv sm u) /\
    (!d. return_buf_frame d cenv sa s /\ return_buf_sep d cenv es s ==>
       return_buf_sep d cenv es u) /\
    (local_ptrs_reserved cenv sa ==> local_ptrs_reserved cenv sm) /\
    (alloca_history func s ==> alloca_history func u) /\
    allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    fn_has_code sm sb func /\ ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts /\
    (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==> FLOOKUP u.vs_allocas aid = SOME ent) /\
    s.vs_alloca_next <= u.vs_alloca_next /\
    sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sb.cs_next_var /\
    (!x. not_fresh_at sa x ==> not_fresh_at sm x /\ lookup_var x u = lookup_var x s) /\
    alloca_frame cenv es sa s cenv es u /\ ghost_kept_at lo cenv es sa G tn s Gu tu /\
    ~block_is_terminated sb``;

Theorem imm_copy_compiler_cuts[local]:
  compile_assign_value cenv dst LocCode (Var xs) F loc dty sty n sa = ((),sb) /\
  dty <> sty /\ ~is_bytestring_type dty /\ fn_has_code sa sb func ==>
  ?buf sl sm. compile_alloc_buffer n sa = (buf,sl) /\
    compile_store_memory_typed cenv buf.buf_operand dty (Var xs) sty sl = ((),sm) /\
    compile_assign_value cenv dst LocCode buf.buf_operand F loc dty dty n sm = ((),sb) /\
    fn_has_code sa sl func /\ fn_has_code sl sm func /\ fn_has_code sm sb func /\
    sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sb.cs_next_var
Proof
  strip_tac >> drule_all_then strip_assume_tac immutable_assign_normalized_compile >>
  `compile_assign_value cenv dst LocCode buf.buf_operand F loc dty dty n sm = ((),sb)` by
    (qpat_assum `(if _ then _ else _) sm = ((),sb)` mp_tac >>
     qpat_assum `~is_bytestring_type dty` (fn nb =>
       simp[NoAsms,nb,compile_assign_value_def,comp_bind_def,comp_return_def])) >>
  `ci_mono sa mid` by metis_tac[ci_mono_compile_alloc_buffer,pairTheory.SND] >>
  `ci_mono mid sm` by metis_tac[cj 1 ci_mono_typed_memory_family,pairTheory.SND] >>
  `ci_mono sm sb` by metis_tac[cj 1 ci_mono_stmt_helpers,pairTheory.SND] >>
  qexistsl_tac [`buf`,`mid`,`sm`] >> fs[ci_mono_def] >>
  `cs_extends sa sm` by metis_tac[cs_extends_trans] >>
  drule_all_then strip_assume_tac fn_has_code_split >>
  `fn_has_code sa mid func /\ fn_has_code mid sm func` by metis_tac[fn_has_code_split] >>
  simp[] >> decide_tac
QED

Theorem imm_copy_operand_at_cut[local]:
  u.vs_labels = s.vs_labels /\
  (!x. not_fresh_at sa x ==> not_fresh_at sm x /\ lookup_var x u = lookup_var x s /\
     FLOOKUP Gu x = FLOOKUP G x /\ op_taint tu (Var x) = op_taint tn (Var x)) ==>
  !op. copy_old_operand sa op ==>
    copy_old_operand sm op /\ eval_operand op u = eval_operand op s /\
    op_prov Gu op = op_prov G op /\ op_taint tu op = op_taint tn op
Proof
  strip_tac >> Cases >> simp[copy_old_operand_def,op_prov_def,eval_operand_def] >>
  rpt strip_tac >> fs[op_taint_def]
QED

Theorem imm_copy_join_paths[local]:
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu)) /\
  immutable_path_store_post (lo,explicit,ctx,func,PG) dest dtv v sm sb (u,Gu,tu) (q,Gf,tf) ==>
  !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK q,Gf,tf)
Proof
  simp[immutable_path_store_post_def] >> strip_tac >> gen_tac >>
  irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gu`,`u`,`tu`] >> simp[]
QED

Theorem imm_copy_normalized[local]:
  compile_assign_value cenv dst LocCode (Var xs) F loc dty sty
    (type_memory_size dtv) sa = ((),sb) /\
  dty <> sty /\ ~is_bytestring_type dty /\ 0 < type_memory_size dtv /\
  ^value_types /\ ^source /\ ^bounds /\ ^normalize_ready ==>
  ^cut_post
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (qx_choosel_then [`buf`,`sl`,`sm`] strip_assume_tac) imm_copy_compiler_cuts >>
  `~is_word_type sty` by (strip_tac >> drule_all return_source_word_widens_eq >> simp[]) >>
  `~is_bytestring_type sty` by (strip_tac >> drule_all type_widens_from_bytestring >> simp[]) >>
  `type_memory_size dtv < dimword (:256)` by decide_tac >>
  `w2n (n2w a : bytes32) = a` by (simp[w2n_n2w,LESS_MOD] >> decide_tac) >>
  `val_wf stv v /\ val_wf dtv v` by simp[value_has_type_memory_wf] >>
  `~block_is_terminated sb` by drule_then ACCEPT_TAC immutable_assign_loccode_open >>
  mp_tac (Q.INST [`sm` |-> `sl`,`sb` |-> `sm`,`sw` |-> `n2w a : bytes32`]
    (SPEC_ALL slot_copy_normalize_ready_mods)) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[]])) >>
  disch_then (qx_choosel_then [`u`,`root`,`b`,`Gu`,`tu`] strip_assume_tac) >>
  `u.vs_labels = s.vs_labels` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK u,Gu,tu)`
       (qspec_then `D` (irule o MATCH_MP gas_origin_ptr_path_preserves_labels))) >>
  mp_tac (SPEC_ALL imm_copy_operand_at_cut) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (mk_asm "operands") >>
  `?q Gf tf. immutable_path_store_post (lo,explicit,ctx,func,PG) dest dtv v
                 sm sb (u,Gu,tu) (q,Gf,tf)` by suspend "store" >>
  `!d. return_buf_frame d cenv sa s /\ return_buf_sep d cenv es s ==>
       return_buf_sep d cenv es u` by suspend "sep" >>
  drule_all_then assume_tac imm_copy_join_paths >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  qexistsl_tac [`sm`,`u`,`Gu`,`tu`,`q`,`Gf`,`tf`] >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[]]
QED

Resume imm_copy_normalized[store]:
  `copy_old_operand sm dst /\ eval_operand dst u = SOME (n2w dest) /\
   op_taint tu dst = {} /\ op_prov Gu dst = NONE` by
    (asm "operands" (qspec_then `dst` mp_tac) >> simp[]) >>
  `!base. cenv.ce_imm_alloca = SOME base ==> eval_operand base u = SOME 0w /\
     copy_old_operand sm base /\ op_taint tu base = {} /\ op_prov Gu base = NONE` by
    (qx_gen_tac `base_op` >> disch_tac >>
     qpat_assum `!base. cenv.ce_imm_alloca = SOME base ==> _`
       (drule_then strip_assume_tac) >>
     asm "operands" (qspec_then `base_op` mp_tac) >> simp[]) >>
  `eval_operand (Var root) u = SOME (n2w b)` by simp[eval_operand_def] >>
  `compile_assign_value cenv dst LocCode (Var root) F loc dty dty
     (type_memory_size dtv) sm = ((),sb)` by metis_tac[] >>
  drule_at (Pat `compile_assign_value _ _ LocCode (Var root) F _ _ _ _ sm = _`)
    immutable_path_store_fixed >>
  disch_then irule >> simp[] >> qexists_tac `b` >> simp[]
QED

Resume imm_copy_normalized[sep]:
  rpt strip_tac >>
  `!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) u` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK u,Gu,tu)`
       (qspec_then `D` assume_tac) >>
     mp_tac (Q.INST [`t` |-> `u`, `marks` |-> `[]`, `G'` |-> `Gu`, `tn'` |-> `tu`]
       (SPEC_ALL return_buf_allocas_path)) >> simp[]) >>
  irule return_buf_sep_transport >> simp[] >> qexistsl_tac [`cenv`,`es`,`s`] >> simp[] >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by simp[] >>
  `!n b sz. local_region cenv es.scopes u n b sz <=> local_region cenv es.scopes s n b sz` by
    (irule copy_buffer_local_region_frame >> qexists_tac `sa` >> simp[]) >> simp[]
QED
Finalise imm_copy_normalized[local]

(* The input machine state is at sa, after the actual delayed unwrap.
   The prefix is empty for a flat/bytestring copy. For a layout change,
   sm and u are the compiler and machine boundaries after normalization;
   the immutable writeback must use the post starting at those boundaries. *)
Theorem qualified_place_imm_copy_path_mods:
  assign_place_store_code_mods cenv e (SOME vv) (dst,SOME LocCode,SOME (ValPT dty))
    st = ((),sb) /\ unwrap_value cenv vv st = (Var xs,sa) /\
  sty = lowered_value_type cenv e /\ ~is_word_type dty /\
  type_memory_bytes cenv dty = type_memory_size dtv /\ assignable_type (get_tenv cx) sty /\
  ^value_types /\ ^source /\ ^bounds /\
  (dty <> sty /\ ~is_bytestring_type dty ==> ^normalize_ready) ==>
  ^cut_post
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `compile_assign_value cenv dst LocCode (Var xs) F (vv_location vv) dty sty
     (type_memory_size dtv) sa = ((),sb)` by
    (qpat_x_assum `assign_place_store_code_mods _ _ _ _ _ = _` mp_tac >>
     simp[assign_place_store_code_mods_def,comp_bind_def]) >>
  drule_all_then strip_assume_tac immutable_assign_widened_memory_positive >>
  Cases_on `dty <> sty /\ ~is_bytestring_type dty`
  >- (qpat_x_assum `_ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _` mp_tac >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      qpat_x_assum `dty <> sty /\ ~is_bytestring_type dty` strip_assume_tac >>
      mp_tac (Q.INST [`loc` |-> `vv_location vv`] (SPEC_ALL imm_copy_normalized)) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then ACCEPT_TAC) >>
  (Q.SUBGOAL_THEN `sty = dty \/ is_bytestring_type dty` assume_tac >-
    (qpat_x_assum `~(dty <> sty /\ ~is_bytestring_type dty)` mp_tac >> simp[EQ_SYM_EQ])) >>
  `~block_is_terminated sb` by drule_then ACCEPT_TAC immutable_assign_loccode_open >>
  `ci_mono sa sb` by metis_tac[cj 1 ci_mono_stmt_helpers,pairTheory.SND] >>
  `sa.cs_next_var <= sb.cs_next_var` by fs[ci_mono_def] >>
  mp_tac (Q.INST [`loc` |-> `vv_location vv`] (SPEC_ALL imm_copy_flat)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`q`,`Gf`,`tf`] assume_tac) >>
  qpat_assum `immutable_path_store_post _ _ _ _ _ _ _ _`
    (assume_tac o cj 1 o REWRITE_RULE [immutable_path_store_post_def]) >>
  qexistsl_tac [`sa`,`s`,`G`,`tn`,`q`,`Gf`,`tf`] >>
  simp[cj 1 gas_origin_ptr_path_rules,alloca_frame_def,ghost_kept_at_def] >>
  rpt gen_tac >> strip_tac >> first_assum ACCEPT_TAC
QED
