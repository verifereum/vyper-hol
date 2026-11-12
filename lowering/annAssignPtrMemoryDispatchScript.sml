(* The original location tag selects staging, not the unwrapped operand's
   representation. Both branches finish at their own counted endpoint. *)
Theory annAssignPtrMemoryDispatch
Ancestors annAssignPtrMemoryContinuation stmtLowering
 annAssignPtrMemorySource annAssignPtrMemoryWindow annAssignPtrMemoryAssign
 valueTypingMemoryProps bodyPtrDefs compileEnv loweringStateRelDefs

Theorem annassign_memory_assignment_location_ptr:
 !ctx func cenv cx es sa sb p cap w aid src a sty dty bytes
  s0 d PG G0 tn0 t ea eb tv dtv stv v inst sc rest id loc fr.
 compile_assign_value cenv (Var p) LocMemory (Var src) F loc
   dty sty bytes sa = ((),sb) /\
 (sty = dty \/ is_bytestring_type dty) /\
 0 < type_memory_bytes cenv sty /\ type_memory_bytes cenv sty < dimword (:256) /\
 fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
 stmt_state_rel ctx func cenv cx es s0 /\ ghost_inv d cenv cx es G0 tn0 s0 /\
 local_ptrs_reserved cenv sa /\ not_fresh_at sa p /\ not_fresh_at sa src /\
 (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
 (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
 ~s0.vs_halted /\ ~ctx_has_dalloca ctx /\
 s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
 expr_val_at cenv cx t ea eb es v (Var src) s0 /\
 evaluate_type (get_tenv cx) t = SOME tv /\ ~is_word_type t /\
 evaluate_type (get_tenv cx) dty = SOME dtv /\
 (t = dty \/ is_bytestring_type t /\ is_bytestring_type dty) /\
 value_has_type dtv v /\
 lookup_var src s0 = SOME a /\ ptr_covers G0 tn0 src s0 (type_memory_bytes cenv sty) /\
 val_wf tv v /\ val_footprint tv v <= type_memory_bytes cenv sty /\
 (!m. mem_agree_outside tn0.t_mem s0.vs_memory m ==> val_in_memory tv v (w2n a) m) /\
 lookup_var p s0 = SOME w /\ ptr_covers G0 tn0 p s0 cap /\
 FLOOKUP s0.vs_allocas aid = SOME (w2n w,cap) /\
 MEM inst (fn_insts func) /\ inst.inst_id = aid /\
 inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\ fr.cs_next_id <= aid /\
 fr.cs_next_id <= sa.cs_next_id /\
 (!q. not_fresh_at fr q ==> not_fresh_at sa q) /\
 not_local_ptr cenv es.scopes p /\ ~cenv.ce_is_ctor /\
 es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
 FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\
 ~is_word_type dty /\
 (sty = dty \/ is_bytestring_type sty /\ is_bytestring_type dty) /\
 evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv v /\
 type_memory_size stv = type_memory_bytes cenv sty /\
 type_memory_size dtv = type_memory_bytes cenv dty /\ type_memory_size dtv <= cap ==>
 ?sf Gf tnf.
 gas_path_ptr (cx_dead cx) 0 ctx func PG G0 tn0 s0 0 Gf tnf (OK sf) /\
 sf.vs_current_bb = sb.cs_current_bb /\ sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
 ~sf.vs_halted /\
 stmt_state_rel ctx func cenv cx
   (es with scopes := (sc |+ (id,<|assignable := T; type := dtv;
                                 value := v; popped := []|>)) :: rest) sf /\
 ghost_inv d cenv cx
   (es with scopes := (sc |+ (id,<|assignable := T; type := dtv;
                                 value := v; popped := []|>)) :: rest) Gf tnf sf /\
 ghost_kept cenv es fr G0 tn0 s0 Gf tnf /\
 (!q. not_fresh_at fr q ==> lookup_var q sf = lookup_var q s0) /\
 ptr_covers Gf tnf p sf cap
Proof
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 Cases_on `loc = SOME LocMemory`
 >- (pop_assum SUBST_ALL_TAC >>
     qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `sa`, `sb`, `p`, `cap`,
       `w`, `aid`, `src`, `a`, `sty`, `dty`, `bytes`, `s0`, `d`, `PG`,
       `G0`, `tn0`, `t`, `ea`, `eb`, `tv`, `dtv`, `stv`, `v`, `inst`, `sc`,
       `rest`, `id`, `fr`] mp_tac annassign_memory_assignment_declaration_ptr >>
     asm_rewrite_tac[]) >>
 qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
 simp[compile_assign_value_def] >> disch_tac >>
 `!m. mem_agree_outside tn0.t_mem s0.vs_memory m ==>
       val_in_memory dtv v (w2n a) m` by
   metis_tac[annassign_robust_layout_transfer_ptr] >>
 `type_memory_bytes cenv dty <= cap` by metis_tac[] >>
 drule_all annassign_memory_copy_window_ptr >>
 disch_then (qx_choosel_then [`k`,`len`] strip_assume_tac) >>
 `val_wf dtv v` by metis_tac[value_has_type_memory_wf] >>
 `ghost_kept cenv es fr G0 tn0 s0 G0 tn0` by simp[ghost_kept_def] >>
 `(!name ent q nsz. lookup_scopes name es.scopes = SOME ent /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var q) nsz) ==> not_fresh_at sa q) /\
  (!q. cenv.ce_imm_alloca = SOME (Var q) ==> not_fresh_at sa q)` by
   (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
 `FLOOKUP s0.vs_allocas inst.inst_id = SOME (w2n w,cap) /\
  fr.cs_next_id <= inst.inst_id` by simp[] >>
 drule_all (annassign_memory_destination_declaration_ptr |> SPEC_ALL |>
   Q.INST [`sa` |-> `fr`, `st` |-> `sa`, `s` |-> `s0`] |> SRULE []) >>
 disch_then (qspecl_then [`T`,`PG`] (qx_choosel_then [`Gf`,`tnf`,`sf`] strip_assume_tac)) >>
 qexistsl [`sf`,`Gf`,`tnf`] >> asm_rewrite_tac[] >> metis_tac[]
QED
