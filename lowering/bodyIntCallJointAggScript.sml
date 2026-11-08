(* Seam 2 joint induction step: aggregate constructors and memory subplaces. *)
Theory bodyIntCallJointAgg
Ancestors
  bodyIntCallJointContract loweringPosts exprSimWordArgs
  compileEnv stmtSimProps bodyMemoryDefs freshWrites

(* The continuation uses the standard write-back frame, so its composition
   and old-allocation interface are shared with other expression proofs. *)
Theorem intcall_expr_cont_frame:
  intcall_expr_cont fp ce env es sa s ee sb u <=>
  intcall_joint_res fp ce env ee sb u /\ ~u.vs_halted /\
  u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts /\
  s.vs_alloca_next <= u.vs_alloca_next /\
  wb_frame ce es sa s u
Proof
  simp[intcall_expr_cont_def, wb_frame_def] >> metis_tac[]
QED

Theorem intcall_expr_cont_trans:
  intcall_joint_res fp ce env es sa s /\
  intcall_expr_cont fp ce env es sa s em sm t /\
  intcall_expr_cont fp ce env em sm t ee sb u /\
  MAP FDOM es.scopes = MAP FDOM em.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id ==>
  intcall_expr_cont fp ce env es sa s ee sb u
Proof
  simp[intcall_expr_cont_frame] >> rpt strip_tac >>
  `wb_frame ce es sa s u` by
    (irule wb_frame_trans >>
     gvs[intcall_joint_res_def] >> metis_tac[]) >>
  simp[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

(* Transport the fixed-source resources across an operational suffix.  The
   state relation is supplied at that suffix's actual counted endpoint. *)
Theorem intcall_joint_res_frame:
  intcall_frame_ok fp /\
  intcall_joint_res fp ce env es sa s /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es u /\
  sa.cs_next_var <= sb.cs_next_var /\
  s.vs_alloca_next <= u.vs_alloca_next /\
  allocas_above fp.jc_lo u /\
  (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
         lookup_var x u = SOME w) /\
  (!a k. fp.jc_prot a k ==>
     mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory) /\
  (!op. fp.jc_reserved op ==> eval_operand op u = eval_operand op s) /\
  (!n b k. local_region ce es.scopes u n b k ==>
           local_region ce es.scopes s n b k) ==>
  intcall_joint_res fp ce env es sb u
Proof
  rpt strip_tac >>
  `local_ptrs_reserved ce sb` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     gvs[intcall_joint_res_def] >> metis_tac[]) >>
  `ret_pc_ok ce sb u` by
    (irule ret_pc_ok_frame >>
     gvs[intcall_joint_res_def] >> metis_tac[]) >>
  `return_buf_frame fp.jc_rb ce sb u` by
    (irule return_buf_frame_frame >>
     gvs[intcall_joint_res_def] >> metis_tac[]) >>
  `fp.jc_reserved fp.jc_rpc` by
    fs[intcall_frame_ok_def] >>
  gvs[intcall_joint_res_def] >>
  conj_tac
  >- (rpt strip_tac >> irule not_fresh_at_mono >>
      qexists_tac `sa` >> simp[]) >>
  conj_tac
  >- metis_tac[] >>
  gvs[]
QED

(* L-agg (C1.3.14.2.3), a step of the induction on expr_size: tuple
   literals (MakeArray NONE), array literals (MakeArray (SOME _)), struct
   literals, attributes and subscripts (every place_type case: tuple and
   struct literal-index, ValPT array, MapPT), given the producers of every
   smaller expression. *)
Theorem intcall_aggregate_producer_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  ((?a t n args. e = Builtin a (MakeArray t n) args) \/
   (?a nm fields. e = StructLit a nm fields) \/
   (?a base fld. e = Attribute a base fld) \/
   (?a base idx. e = Subscript a base idx)) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  cheat
QED
