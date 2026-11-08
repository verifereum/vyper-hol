(* The counted destination copy followed by logical scope insertion.
   The allocation's full capacity (sz), not just the copied footprint (k),
   is retained through the old-variable frame. *)
Theory annAssignPtrDeclarationPost
Ancestors
 annAssignPtrDestinationFrame annAssignPtrStore annAssignPtrBytestring

Theorem annassign_copied_declaration_path_ptr:
 !ctx func PG cenv cx es d G tn s st sb ty sty src dst a b len k entry
  sa G0 tn0 s0 inst sz sc rest id.
 compile_store_memory cenv (Var src) (Var dst) ty sty st = ((),sb) /\
 fn_has_code st sb func /\ ~is_word_type ty /\
 (sty = ty \/ is_bytestring_type ty) /\
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
 not_fresh_at st src /\ not_fresh_at st dst /\
 lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
 k < dimword (:256) /\ ptr_covers G tn src s k /\ ptr_covers G tn dst s k /\
 ptr_covers G tn dst s sz /\
 (if is_bytestring_type ty then
    k = 32 + 32 * ((len + 31) DIV 32) /\ mload (w2n a) s = n2w len /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem)
  else k = type_memory_bytes cenv ty) /\
 val_wf entry.type entry.value /\ val_footprint entry.type entry.value <= k /\
 (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory entry.type entry.value (w2n a) m) /\
 stmt_state_rel ctx func cenv cx es s /\ ~cenv.ce_is_ctor /\
 ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es sa G0 tn0 s0 G tn /\
 fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\
 inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [dst] /\
 not_local_ptr cenv es.scopes dst /\
 FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n b,sz) /\ k <= sz /\
 sa.cs_next_id <= inst.inst_id /\
 (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==>
             FLOOKUP s.vs_allocas aid = SOME ent) /\
 (!n lo nsz. local_region cenv es.scopes s0 n lo nsz ==>
             local_region cenv es.scopes s n lo nsz) /\
 (!q. not_fresh_at sa q ==> not_fresh_at st q) /\
 (!name ent q nsz. lookup_scopes name es.scopes = SOME ent /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var q) nsz) ==> not_fresh_at st q) /\
 (!q nsz. cenv.ce_return_buf = SOME (PtrVar (Var q) nsz) ==> not_fresh_at st q) /\
 (!q nsz. cenv.ce_return_pc = SOME (PtrVar (Var q) nsz) ==> not_fresh_at st q) /\
 (!q. cenv.ce_imm_alloca = SOME (Var q) ==> not_fresh_at st q) /\
 es.scopes = sc :: rest /\
 FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var dst) sz) ==>
 ?Gf tnf sf.
 gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
 sf.vs_current_bb = sb.cs_current_bb /\ sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
 ~sf.vs_halted /\
 stmt_state_rel ctx func cenv cx es sf /\
 ghost_inv d cenv cx es Gf tnf sf /\
 ghost_kept cenv es sa G0 tn0 s0 Gf tnf /\
 ptr_covers Gf tnf dst sf sz /\ lookup_var dst sf = SOME b /\
 (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
      val_in_memory entry.type entry.value (w2n b) m) /\
 ghost_inv d cenv cx (es with scopes := (sc |+ (id,entry)) :: rest) Gf tnf sf /\
 (!q. not_fresh_at st q ==> lookup_var q sf = lookup_var q s) /\
 sf.vs_allocas = s.vs_allocas
Proof
 rpt gen_tac >> strip_tac >> (
 qspecl_then [`ctx`, `func`, `PG`, `cenv`, `cx`, `es`, `d`, `G`, `tn`, `s`,
   `st`, `sb`, `ty`, `sty`, `src`, `dst`, `a`, `b`, `len`, `k`,
   `entry.type`, `entry.value`, `sa`, `G0`, `tn0`, `s0`, `inst`, `sz`]
   mp_tac annassign_allocated_store_memory_path_ptr >>
 (impl_tac >- (asm_rewrite_tac[] >> simp[])) >> strip_tac >>
 `lookup_var dst sf = SOME b /\ FLOOKUP Gf dst = FLOOKUP G dst /\
  op_taint tnf (Var dst) = op_taint tn (Var dst)` by metis_tac[] >>
 `ptr_covers Gf tnf dst sf sz` by
   (irule annassign_ptr_covers_frame_ptr >> qexistsl [`G`,`s`,`tn`] >> simp[]) >>
 `ghost_inv d cenv cx (es with scopes := (sc |+ (id,entry)) :: rest) Gf tnf sf` by
   (irule annassign_ghost_scope_update_ptr >> simp[] >>
    rpt strip_tac >> gvs[] >> first_x_assum drule >> simp[]) >>
 qexistsl [`Gf`,`tnf`,`sf`] >> asm_rewrite_tac[] >>
 fs[venomStateTheory.venom_state_component_equality])
QED
