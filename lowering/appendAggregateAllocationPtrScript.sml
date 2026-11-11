(* Allocate destination storage independently of the source representation type. *)
Theory appendAggregateAllocationPtr
Ancestors annAssignPtrSetup annAssignPtrScratch bodyPtrDefs compileEnv
  loweringPosts venomState venomInst finite_map words

Theorem append_aggregate_allocation_ptr:
 !ctx func cenv cx es st st1 p sz s0 sa d PG G0 tn0
   t ea eb v src tv a k.
 emit_inst ALLOCA [Lit (n2w sz)] [p] st = ((),st1) /\
 stmt_state_rel ctx func cenv cx es s0 /\ fn_inst_ids_distinct func /\
 MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)] [p]) (fn_insts func) /\
 not_local_ptr cenv es.scopes p /\ sz < dimword (:256) /\
 ~not_fresh_at sa p /\
 (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> x <> p) /\
 (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> x <> p) /\
 fn_has_code st st1 func /\ ~s0.vs_halted /\ ~ctx_has_dalloca ctx /\
 s0.vs_current_bb = st.cs_current_bb /\
 s0.vs_inst_idx = LENGTH st.cs_current_insts /\
 ghost_inv d cenv cx es G0 tn0 s0 /\
 expr_val_at cenv cx t ea eb es v (Var src) s0 /\
 evaluate_type (get_tenv cx) t = SOME tv /\ ~is_word_type t /\
 lookup_var src s0 = SOME a /\ src <> p /\ val_wf tv v /\
 ptr_covers G0 tn0 src s0 k /\
 (!m. mem_agree_outside tn0.t_mem s0.vs_memory m ==>
      val_in_memory tv v (w2n a) m) ==>
 ?s1 w G1 tn1.
 gas_path_ptr (cx_dead cx) 0 ctx func PG G0 tn0 s0 0 G1 tn1 (OK s1) /\
 stmt_state_rel ctx func cenv cx es s1 /\
 ghost_inv d cenv cx es G1 tn1 s1 /\
 ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
 ptr_covers G1 tn1 p s1 sz /\
 lookup_var p s1 = SOME w /\
 FLOOKUP s1.vs_allocas st.cs_next_id = SOME (w2n w,sz) /\
 w2n w + sz < dimword (:256) /\
 (!op. op <> Var p ==> eval_operand op s1 = eval_operand op s0) /\
 s1.vs_memory = s0.vs_memory /\
 (!x. x <> p ==> lookup_var x s1 = lookup_var x s0) /\
 (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
                FLOOKUP s1.vs_allocas aid = SOME entry) /\
 ~s1.vs_halted /\ s1.vs_current_bb = st1.cs_current_bb /\
 s1.vs_inst_idx = LENGTH st1.cs_current_insts /\
 (?u. step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)] [p]) s0 = OK u /\
     s1 = u with vs_inst_idx := SUC s0.vs_inst_idx /\
     G1 = step_prov PG G0 (mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)] [p]) u /\
     tn1 = step_taint (mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)] [p]) s0 u tn0) /\
 lookup_var src s1 = SOME a /\ ptr_covers G1 tn1 src s1 k /\
 (!m. mem_agree_outside tn1.t_mem s1.vs_memory m ==>
      val_in_memory tv v (w2n a) m)
Proof
 rpt gen_tac >> strip_tac >>
 drule_all annassign_setup_ptr >>
 disch_then (qspec_then `PG` strip_assume_tac) >>
 drule_all annassign_alloca_source_transport_ptr >>
 disch_then (qspec_then `PG` strip_assume_tac) >>
 qexistsl_tac [`s1`, `w`, `G1`, `tn1`] >>
 gvs[ptr_covers_def, lookup_var_def] >>
 metis_tac[]
QED
