(* Strengthen the postcondition of the constructed MCOPY fragment, retaining
   its same run and every original postcondition. *)
Theory bodyIntCallMcopyFrame
Ancestors
  bodyIntCallWriteFrame bodyIntCallValueWindow exprSimBufferStore fragExec
  exprLoweringProps compileEnv

Theorem mcopy_alloca_local_framed_frag:
  !ctx func cenv cx es sa sb s inst p dw sw src sz alloc_sz tv v.
    emit_void MCOPY [Var p; src; Lit (n2w sz)] sa = ((), sb) /\
    lookup_var p s = SOME dw /\ eval_operand src s = SOME sw /\
    sz < dimword (:256) /\ sz <= alloc_sz /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    not_local_ptr cenv es.scopes p /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n dw, alloc_sz) /\
    val_in_memory tv v (w2n sw) s.vs_memory /\ val_wf tv v /\
    val_footprint tv v <= sz ==>
    frag_exec ctx sa sb (\t. t = s)
      (\t. stmt_state_rel ctx func cenv cx es t /\
           val_in_memory tv v (w2n dw) t.vs_memory /\
           (!q. lookup_var q t = lookup_var q s) /\
           t.vs_allocas = s.vs_allocas /\
           LENGTH s.vs_memory <= LENGTH t.vs_memory /\
           (!a k. a + k <= w2n dw \/ w2n dw + sz <= a ==>
                mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory) /\
           (!n b k. local_region cenv es.scopes s n b k ==>
                mem_bytes_at b k t.vs_memory = mem_bytes_at b k s.vs_memory) /\
           (!n b k tv' v' ptr.
                local_region cenv es.scopes s n b k /\
                val_in_memory tv' v' ptr s.vs_memory /\ val_wf tv' v' /\
                b <= ptr /\ ptr + val_footprint tv' v' <= b + k ==>
                val_in_memory tv' v' ptr t.vs_memory)) (\r. F)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all mcopy_alloca_framed_frag >> strip_tac >>
  drule_at (Pos hd) frag_exec_conseq >>
  disch_then irule >> simp[] >> gen_tac >> strip_tac >>
  gvs[] >> conj_tac
  >- (qpat_x_assum `!a k. _` ACCEPT_TAC) >>
  conj_asm1_tac
  >- (rpt gen_tac >> strip_tac >>
      `alloca_inv s /\ local_ptrs_rel func cenv es.scopes s` by
        fs[stmt_state_rel_def, state_rel_def] >>
      irule allocated_write_local_bytes >>
      qpat_assum `FLOOKUP _ _ = SOME _` (irule_at Any) >>
      qpat_assum `local_region _ _ _ _ _ _` (irule_at Any) >>
      qexistsl [`p`, `sz`, `func`, `w2n dw`] >> simp[arithmeticTheory.ADD_COMM] >>
      qpat_x_assum `!a k. _` ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  irule val_in_memory_window_agree >>
  qpat_assum `val_in_memory _ _ _ s.vs_memory` (irule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  qpat_x_assum `!n b k. local_region _ _ _ _ _ _ ==> _` drule >> simp[]
QED
