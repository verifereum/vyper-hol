(* Allocation exclusion and invariant consumers for destination copies. *)
Theory annAssignPtrDestinationFrame
Ancestors
 annAssignPtrDestination annAssignPtrExterior annAssignPtrScratch
 exprSimProps exprLoweringProps localPtrsProps compileEnv loweringStateRelDefs venomState
 valueEncodingProps robustCopyTransportPtr ptrDiscipline finite_map pred_set
 list venomMemProofs valueEncodingProofs loweringPosts venomMemDefs

Theorem annassign_alloca_window_excludes_locals_ptr:
 !ctx func cenv cx es s inst p b sz k.
 stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
 MEM inst (fn_insts func) /\ inst.inst_outputs = [p] /\
 not_local_ptr cenv es.scopes p /\
 FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\ k <= sz ==>
 !name lo nsz i. local_region cenv es.scopes s name lo nsz /\
 lo <= i /\ i < lo+nsz ==> ~(b <= i /\ i < b+k)
Proof
 rpt gen_tac >> strip_tac >>
 `alloca_inv s /\ local_ptrs_rel func cenv es.scopes s` by
   fs[stmt_state_rel_def, state_rel_def] >>
 rpt gen_tac >> strip_tac >>
 drule_all local_ptrs_rel_alloca_disjoint >>
 simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem annassign_local_ptrs_exterior_ptr:
 !func cenv scopes s mem writes.
 local_ptrs_rel func cenv scopes s /\
 (!name b sz i. local_region cenv scopes s name b sz /\
    b <= i /\ i < b+sz ==> i NOTIN writes) /\
 (!i. i NOTIN writes ==> mem_bytes_at i 1 mem = mem_bytes_at i 1 s.vs_memory) ==>
 local_ptrs_rel func cenv scopes (s with vs_memory := mem)
Proof
 rpt gen_tac >> strip_tac >> irule local_ptrs_rel_frame >>
 qexists `s` >> simp[lookup_var_def] >>
 reverse conj_tac >- (rpt strip_tac >> gvs[]) >>
 rpt gen_tac >> strip_tac >>
 irule val_in_memory_footprint_agree >> simp[] >>
 qexists `s.vs_memory` >> simp[] >>
 irule LIST_EQ >> simp[] >> rpt strip_tac >>
 rename1 `j < val_footprint entry.type entry.value` >>
 `local_region cenv scopes s name (w2n w) sz` by
   (simp[local_region_def, lookup_var_def] >> metis_tac[]) >>
 `val_footprint entry.type entry.value <= sz` by
   (drule val_footprint_le >> decide_tac) >>
 `w2n w+j NOTIN writes` by
   (qpat_x_assum `!name b sz i. _` irule >>
    qexistsl [`w2n w`,`name`,`sz`] >> simp[] >> decide_tac) >>
 `mem_bytes_at (w2n w+j) 1 mem = mem_bytes_at (w2n w+j) 1 s.vs_memory` by metis_tac[] >>
 pop_assum mp_tac >> simp[LIST_EQ_REWRITE, EL_mem_bytes_at]
QED

Theorem annassign_state_memory_exterior_ptr:
 !ctx func cenv cx es s mem writes.
 stmt_state_rel ctx func cenv cx es s /\ ~cenv.ce_is_ctor /\
 (!name b sz i. local_region cenv es.scopes s name b sz /\
    b <= i /\ i < b+sz ==> i NOTIN writes) /\
 (!i. i NOTIN writes ==> mem_bytes_at i 1 mem = mem_bytes_at i 1 s.vs_memory) ==>
 stmt_state_rel ctx func cenv cx es (s with vs_memory := mem)
Proof
 rpt gen_tac >> strip_tac >>
 `local_ptrs_rel func cenv es.scopes (s with vs_memory := mem)` by
   (irule annassign_local_ptrs_exterior_ptr >>
    conj_tac >- (qexists `writes` >> asm_rewrite_tac[]) >>
    fs[stmt_state_rel_def, state_rel_def]) >>
 `state_rel func cenv cx es (s with vs_memory := mem)` by
   (irule state_rel_frame >> simp[] >> qexistsl [`es`,`s`] >> simp[] >>
    fs[stmt_state_rel_def, state_rel_def, immutables_rel_def] >>
    asm_rewrite_tac[]) >>
 qpat_x_assum `!name b sz i. _` kall_tac >>
 qpat_x_assum `!i. i NOTIN writes ==> _` kall_tac >>
 fs[stmt_state_rel_def, alloca_inv_def, allocas_non_overlapping_def,
    alloca_next_valid_def, alloca_room_def, pending_alloca_size_def,
    fmp_room_def, immutable_alloca_sep_def, immutable_decl_sep_def, immutable_base_zero_alt,
    lookup_var_def] >> asm_rewrite_tac[]
QED

Theorem annassign_state_vars_exterior_ptr:
 !ctx func cenv cx es s sf writes.
 stmt_state_rel ctx func cenv cx es s /\ ~cenv.ce_is_ctor /\
 (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
            vs_inst_idx := s.vs_inst_idx|>) = s /\
 (!name b sz i. local_region cenv es.scopes s name b sz /\
    b <= i /\ i < b+sz ==> i NOTIN writes) /\
 (!i. i NOTIN writes ==> mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
 (!name entry p sz. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    lookup_var p sf = lookup_var p s) /\
 (!p. cenv.ce_imm_alloca = SOME (Var p) ==> lookup_var p sf = lookup_var p s) ==>
 stmt_state_rel ctx func cenv cx es sf
Proof
 rpt gen_tac >> strip_tac >>
 `stmt_state_rel ctx func cenv cx es (s with vs_memory := sf.vs_memory)` by
   (irule annassign_state_memory_exterior_ptr >>
    conj_tac >- (qexists `writes` >> asm_rewrite_tac[]) >> simp[]) >>
 `stmt_state_rel ctx func cenv cx es
    ((s with vs_memory := sf.vs_memory) with vs_vars := sf.vs_vars)` by
   (irule stmt_state_rel_vars_frame >> asm_rewrite_tac[] >>
    simp[lookup_var_def] >> rpt strip_tac >>
    first_x_assum drule_all >> simp[lookup_var_def] >>
    fs[venom_state_component_equality]) >>
 `sf = ((s with vs_memory := sf.vs_memory) with vs_vars := sf.vs_vars)
          with vs_inst_idx := sf.vs_inst_idx` by
   (qpat_x_assum `(_ with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|>) = _`
      mp_tac >> simp[venom_state_component_equality]) >>
 metis_tac[stmt_state_rel_inst_idx]
QED

Theorem annassign_alloca_window_excludes_older_ptr:
 !s s0 sa inst b sz k.
 alloca_inv s /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
 k <= sz /\ sa.cs_next_id <= inst.inst_id /\
 (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
              FLOOKUP s.vs_allocas aid = SOME entry) ==>
 !aid off nsz i. FLOOKUP s0.vs_allocas aid = SOME (off,nsz) /\
 aid < sa.cs_next_id /\ off <= i /\ i < off+nsz ==>
 ~(b <= i /\ i < b+k)
Proof
 rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
 `FLOOKUP s.vs_allocas aid = SOME (off,nsz)` by metis_tac[] >>
 `aid <> inst.inst_id` by decide_tac >>
 fs[alloca_inv_def, allocas_non_overlapping_def] >>
 first_x_assum (qspecl_then [`aid`,`inst.inst_id`,`off`,`nsz`,`b`,`sz`] mp_tac) >>
 simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem annassign_allocated_destination_invariants_ptr:
 !ctx func cenv cx es d s sf G tn Gf tnf sa G0 tn0 s0 inst p b sz k st.
 stmt_state_rel ctx func cenv cx es s /\ ~cenv.ce_is_ctor /\
 ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es sa G0 tn0 s0 G tn /\
 fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\
 inst.inst_outputs = [p] /\ not_local_ptr cenv es.scopes p /\
 FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\ k <= sz /\
 sa.cs_next_id <= inst.inst_id /\
 (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
              FLOOKUP s.vs_allocas aid = SOME entry) /\
 (!n lo nsz. local_region cenv es.scopes s0 n lo nsz ==>
              local_region cenv es.scopes s n lo nsz) /\
 (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
            vs_inst_idx := s.vs_inst_idx|>) = s /\
 tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
 (!q. not_fresh_at st q ==> lookup_var q sf = lookup_var q s /\
       FLOOKUP Gf q = FLOOKUP G q /\ op_taint tnf (Var q) = op_taint tn (Var q)) /\
 (!q. not_fresh_at sa q ==> not_fresh_at st q) /\
 (!name entry q nsz. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var q) nsz) ==> not_fresh_at st q) /\
 (!q nsz. cenv.ce_return_buf = SOME (PtrVar (Var q) nsz) ==> not_fresh_at st q) /\
 (!q nsz. cenv.ce_return_pc = SOME (PtrVar (Var q) nsz) ==> not_fresh_at st q) /\
 (!q. cenv.ce_imm_alloca = SOME (Var q) ==> not_fresh_at st q) /\
 (!i. ~(b <= i /\ i < b+k) ==>
    mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tnf.t_mem <=> i IN tn.t_mem)) ==>
 stmt_state_rel ctx func cenv cx es sf /\ ghost_inv d cenv cx es Gf tnf sf /\
 ghost_kept cenv es sa G0 tn0 s0 Gf tnf
Proof
 rpt gen_tac >> strip_tac >>
 `!name lo nsz i. local_region cenv es.scopes s name lo nsz /\
    lo <= i /\ i < lo+nsz ==> ~(b <= i /\ i < b+k)` by
   (rpt gen_tac >> strip_tac >>
    drule_all annassign_alloca_window_excludes_locals_ptr >> simp[]) >>
 `!aid off nsz i. FLOOKUP s0.vs_allocas aid = SOME (off,nsz) /\
    aid < sa.cs_next_id /\ off <= i /\ i < off+nsz ==>
    ~(b <= i /\ i < b+k)` by
   (rpt gen_tac >> strip_tac >>
    `alloca_inv s` by fs[stmt_state_rel_def] >>
    drule_all annassign_alloca_window_excludes_older_ptr >> simp[]) >>
 conj_tac
 >- (irule annassign_state_vars_exterior_ptr >> simp[] >>
     qexistsl [`s`,`{i | b <= i /\ i < b+k}`] >>
     simp[] >> conj_tac >- (rpt strip_tac >> metis_tac[]) >>
     conj_tac >- (rpt strip_tac >> metis_tac[]) >>
     fs[venom_state_component_equality]) >>
 conj_tac
 >- (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`) annassign_ghost_vars_exterior_ptr >>
     disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
     disch_then irule >> asm_rewrite_tac[] >> rpt conj_tac
     >- (rpt strip_tac >> metis_tac[])
     >- (rpt strip_tac >> metis_tac[])
     >- (rpt strip_tac >> metis_tac[])
     >- (qexists `{i | b <= i /\ i < b+k}` >> simp[] >>
         rpt strip_tac >> metis_tac[]) >>
     fs[venom_state_component_equality]) >>
 irule annassign_ghost_kept_vars_exterior_ptr >>
 qexistsl [`G`,`tn`,`{i | b <= i /\ i < b+k}`] >> simp[] >> metis_tac[]
QED

Theorem annassign_allocated_store_memory_path_ptr:
 !ctx func PG cenv cx es d G tn s st sb ty sty src dst a b len k tv v
  sa G0 tn0 s0 inst sz.
 compile_store_memory cenv (Var src) (Var dst) ty sty st = ((),sb) /\
 fn_has_code st sb func /\ ~is_word_type ty /\
 (sty = ty \/ is_bytestring_type ty) /\
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
 not_fresh_at st src /\ not_fresh_at st dst /\
 lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
 k < dimword (:256) /\ ptr_covers G tn src s k /\ ptr_covers G tn dst s k /\
 (if is_bytestring_type ty then
    k = 32 + 32 * ((len + 31) DIV 32) /\ mload (w2n a) s = n2w len /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem)
  else k = type_memory_bytes cenv ty) /\
 val_wf tv v /\ val_footprint tv v <= k /\
 (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v (w2n a) m) /\
 stmt_state_rel ctx func cenv cx es s /\ ~cenv.ce_is_ctor /\
 ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es sa G0 tn0 s0 G tn /\
 fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\
 inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [dst] /\
 not_local_ptr cenv es.scopes dst /\
 FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n b,sz) /\ k <= sz /\
 sa.cs_next_id <= inst.inst_id /\
 (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
              FLOOKUP s.vs_allocas aid = SOME entry) /\
 (!n lo nsz. local_region cenv es.scopes s0 n lo nsz ==>
              local_region cenv es.scopes s n lo nsz) /\
 (!q. not_fresh_at sa q ==> not_fresh_at st q) /\
 (!name entry q nsz. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var q) nsz) ==> not_fresh_at st q) /\
 (!q nsz. cenv.ce_return_buf = SOME (PtrVar (Var q) nsz) ==> not_fresh_at st q) /\
 (!q nsz. cenv.ce_return_pc = SOME (PtrVar (Var q) nsz) ==> not_fresh_at st q) /\
 (!q. cenv.ce_imm_alloca = SOME (Var q) ==> not_fresh_at st q) ==>
 ?Gf tnf sf.
 gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
 sf.vs_current_bb = sb.cs_current_bb /\ sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
 ~sf.vs_halted /\
 (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
            vs_inst_idx := s.vs_inst_idx|>) = s /\
 tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
 (!q. not_fresh_at st q ==> lookup_var q sf = lookup_var q s /\
       FLOOKUP Gf q = FLOOKUP G q /\ op_taint tnf (Var q) = op_taint tn (Var q)) /\
 (!i. ~(w2n b <= i /\ i < w2n b+k) ==>
    mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
 (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==> val_in_memory tv v (w2n b) m) /\
 stmt_state_rel ctx func cenv cx es sf /\ ghost_inv d cenv cx es Gf tnf sf /\
 ghost_kept cenv es sa G0 tn0 s0 Gf tnf
Proof
 rpt gen_tac >> strip_tac >> (
 drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`) annassign_store_memory_path_ptr >>
 disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
 disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
 disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
 disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
 disch_then (drule_at (Pat `~ctx_has_dalloca _`)) >>
 disch_then (drule_at (Pat `if _ then _ else _`)) >>
 disch_then (drule_at (Pat `val_wf _ _`)) >>
 disch_then (qspecl_then [`cx_dead cx`,`PG`] mp_tac) >>
 (impl_tac >- (asm_rewrite_tac[] >> simp[])) >> strip_tac >>
 `stmt_state_rel ctx func cenv cx es sf /\ ghost_inv d cenv cx es Gf tnf sf /\
  ghost_kept cenv es sa G0 tn0 s0 Gf tnf` by
   (drule_all annassign_allocated_destination_invariants_ptr >> simp[]) >>
 qexistsl [`Gf`,`tnf`,`sf`] >> asm_rewrite_tac[])
QED
