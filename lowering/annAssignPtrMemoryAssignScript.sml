(* Scope insertion uses the already-established memory layout at the same
   endpoint; no independently chosen S1 execution is identified with it. *)
Theory annAssignPtrMemoryAssign
Ancestors
 annAssignPtrMemoryStageFrame annAssignPtrDeclarationPost stmtSimDeclStore
 exprLoweringProps compileEnv valueEncoding finite_map

Theorem annassign_memory_scope_state_ptr:
 !ctx func cenv cx es s id p sz w inst v tv sc rest assignable.
 stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
 es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
 FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
 not_local_ptr cenv es.scopes p /\ lookup_var p s = SOME w /\
 MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
 FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
 type_memory_size tv <= sz /\ val_wf tv v /\
 val_in_memory tv v (w2n w) s.vs_memory ==>
 stmt_state_rel ctx func cenv cx
   (es with scopes := (sc |+ (id, <|assignable := assignable; type := tv;
                                  value := v; popped := []|>)) :: rest) s
Proof
 rpt gen_tac >> strip_tac >>
 irule stmt_state_rel_declare_memory >>
 `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es s` by
   fs[stmt_state_rel_def, state_rel_def] >>
 simp[] >> qexistsl [`inst`,`s`,`w`] >> simp[] >>
 qpat_x_assum `not_local_ptr _ _ _` mp_tac >> simp[]
QED

Theorem annassign_memory_destination_declaration_ptr:
 !ctx func PG cenv cx es d G tn s st sb ty sty src dst a b len k tv v
  sa G0 tn0 s0 inst sz sc rest id assignable.
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
 val_wf tv v /\ val_footprint tv v <= k /\
 (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v (w2n a) m) /\
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
 FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var dst) sz) /\
 lookup_scopes id es.scopes = NONE /\ type_memory_size tv <= sz ==>
 ?Gf tnf sf.
 gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
 sf.vs_current_bb = sb.cs_current_bb /\ sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
 ~sf.vs_halted /\
 stmt_state_rel ctx func cenv cx es sf /\
 ghost_inv d cenv cx es Gf tnf sf /\
 ghost_kept cenv es sa G0 tn0 s0 Gf tnf /\
 ptr_covers Gf tnf dst sf sz /\ lookup_var dst sf = SOME b /\
 (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
      val_in_memory tv v (w2n b) m) /\
 ghost_inv d cenv cx
   (es with scopes := (sc |+ (id,<|assignable := assignable; type := tv;
                                 value := v; popped := []|>)) :: rest) Gf tnf sf /\
 stmt_state_rel ctx func cenv cx
   (es with scopes := (sc |+ (id,<|assignable := assignable; type := tv;
                                 value := v; popped := []|>)) :: rest) sf /\
 (!q. not_fresh_at st q ==> lookup_var q sf = lookup_var q s) /\
 sf.vs_allocas = s.vs_allocas
Proof
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 drule_all (annassign_copied_declaration_path_ptr |> SPEC_ALL |>
   Q.INST [`entry` |-> `<|assignable := assignable; type := tv;
                         value := v; popped := []|>`] |> SRULE []) >>
 disch_then (qspecl_then [`assignable`,`PG`] strip_assume_tac) >>
 `val_in_memory tv v (w2n b) sf.vs_memory` by
   (first_x_assum (qspec_then `sf.vs_memory` mp_tac) >>
    simp[bodyPtrDefsTheory.mem_agree_outside_def]) >>
 `stmt_state_rel ctx func cenv cx
   (es with scopes := (sc |+ (id,<|assignable := assignable; type := tv;
                                 value := v; popped := []|>)) :: rest) sf` by
   (irule annassign_memory_scope_state_ptr >> simp[] >>
    qexists `inst` >> gvs[]) >>
 qexistsl [`Gf`,`tnf`,`sf`] >> asm_rewrite_tac[]
QED
