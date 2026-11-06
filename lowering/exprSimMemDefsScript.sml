(* Memory-counted expression judgments retain allocation history. *)
Theory exprSimMemDefs
Ancestors
  exprSimDefs exprSimProps loweringPosts gasOutcome gasContext allocaHistory
  exprLowering compileEnv loweringSlice vyperInterpreter vyperState venomState

(* A memory-backed result lies below the allocation frontier with its
   bytestring data rounded up to whole words, which is how much a copy of
   it reads.  A zero-size read passes the memory check at any pointer, so
   it needs no bound. *)
Definition expr_store_bound_def:
  expr_store_bound cx t v op s <=>
    !tv w. evaluate_type (get_tenv cx) t = SOME tv /\ ~is_word_type t /\
           eval_operand op s = SOME w ==>
           val_store_size tv v = 0 \/
           w2n w + val_store_size tv v <= s.vs_alloca_next
End

(* The same for a value_vv held in memory: a located one, or a stack value
   of non-word type, whose operand points at its data.  t is the
   expression's type and lt its lowered value type (lowered_value_type).
   The whole region at lt also lies below the frontier, since a staging
   copy reads that type's full size, not just the value's footprint. *)
Definition vv_store_bound_def:
  vv_store_bound cx t lt es tv vv s <=>
    (!vt op v tvt w.
      ((?p. vv = LocatedValue vt p /\ p.ptr_location = LocMemory /\
            p.ptr_operand = op) \/
       ((?t'. vv = StackValue t' op) /\ ~is_word_type t)) /\
      read_result cx tv es = (INL v, es) /\
      evaluate_type (get_tenv cx) t = SOME tvt /\
      eval_operand op s = SOME w ==>
      val_store_size tvt v = 0 \/
      w2n w + val_store_size tvt v <= s.vs_alloca_next) /\
    (!vt op tvt w.
      ((?p. vv = LocatedValue vt p /\ p.ptr_location = LocMemory /\
            p.ptr_operand = op) \/
       ((?t'. vv = StackValue t' op) /\ ~is_word_type t)) /\
      evaluate_type (get_tenv cx) lt = SOME tvt /\
      eval_operand op s = SOME w ==>
      type_memory_size tvt = 0 \/
      w2n w + type_memory_size tvt <= s.vs_alloca_next)
End

Theorem expr_store_bound_word:
  is_word_type t ==> expr_store_bound cx t v op s
Proof
  simp[expr_store_bound_def]
QED

Theorem expr_store_bound_none:
  expr_store_bound cx NoneT v (Lit 0w) s
Proof
  simp[expr_store_bound_def, vyperValueTheory.evaluate_type_def,
       eval_operand_def] >>
  Cases_on `v` >>
  simp[val_store_size_def, valueEncodingTheory.type_memory_size_def]
QED

Theorem vv_store_bound_stack_word:
  is_word_type t ==> vv_store_bound cx t lt es tv (StackValue t' op) s
Proof
  simp[vv_store_bound_def]
QED

(* A stack value's operand inherits the expression's store bound; the
   lowered type needs no room when the expression's type is a word, or when
   the lowered type has zero size. *)
Theorem vv_store_bound_stack_value:
  expr_store_bound cx t v op s /\
  (~is_word_type t ==>
   !tvt. evaluate_type (get_tenv cx) lt = SOME tvt ==> type_memory_size tvt = 0) ==>
  vv_store_bound cx t lt es (Value v) (StackValue t' op) s
Proof
  rw[vv_store_bound_def, expr_store_bound_def, read_result_def, return_def]
QED

Theorem vv_store_bound_nonmem:
  p.ptr_location <> LocMemory ==>
  vv_store_bound cx t lt es tv (LocatedValue vt p) s
Proof
  simp[vv_store_bound_def]
QED

Definition expr_sim_mem_def:
  expr_sim_mem ctx func cenv cx ty e es <=>
    !sa sb op s0.
      lower_value compile_expr cenv ty e sa = (op, sb) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\
      gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
      stmt_state_rel ctx func cenv cx es s0 /\
      alloca_history func s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome T (cx_tops cx) (ctx, func)
        (bind (eval_expr cx e) (read_result cx)) (es, s0)
        (\res ee t. ?v. res = INL v /\
          expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
          expr_store_bound cx (expr_type e) v op t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
        (\res ee r. expr_exit res r)
End

Definition expr_vv_sim_mem_def:
  expr_vv_sim_mem ctx func cenv cx ty e es <=>
    !sa sb vv s0.
      compile_expr cenv ty e sa = (vv, sb) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\
      gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
      stmt_state_rel ctx func cenv cx es s0 /\
      alloca_history func s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome T (cx_tops cx) (ctx, func) (eval_expr cx e) (es, s0)
        (\res ee t. ?tv. res = INL tv /\
          vv_post ctx func cenv cx e es sa sb s0 ee tv vv t /\
          vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
        (\res ee r. expr_exit res r)
End

Theorem gas_outcome_post_mono:
  gas_outcome m tops p src st Q R /\ (!res ee t. Q res ee t ==> Q' res ee t) ==>
  gas_outcome m tops p src st Q' R
Proof
  PairCases_on `p` >> PairCases_on `st` >>
  rw[gas_outcome_def, gasSummaryTheory.gas_summary_at_def] >>
  qexists_tac `marks` >> metis_tac[]
QED

(* A word-typed result's store bound holds vacuously, so a proof of the
   judgment's other conjuncts suffices. *)
Theorem expr_sim_mem_word_outcome:
  is_word_type (expr_type e) /\
  gas_outcome m tops p src st
    (\res ee t. ?v. res = INL v /\
       expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
       t.vs_current_bb = bb /\ t.vs_inst_idx = n /\
       alloca_history func t /\ a <= t.vs_alloca_next) R ==>
  gas_outcome m tops p src st
    (\res ee t. ?v. res = INL v /\
       expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
       expr_store_bound cx (expr_type e) v op t /\
       t.vs_current_bb = bb /\ t.vs_inst_idx = n /\
       alloca_history func t /\ a <= t.vs_alloca_next) R
Proof
  strip_tac >> irule gas_outcome_post_mono >>
  first_x_assum (irule_at Any) >> simp[] >>
  metis_tac[expr_store_bound_word]
QED

(* A memory pointer with room below the frontier for its whole type bounds
   the value it points at, and a zero-size type needs no room. *)
Theorem vv_store_bound_capacity:
  vv_post ctx func cenv cx e es sa sb s0 es' tv (LocatedValue vt p) t /\
  vt = expr_type e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME ftv /\
  eval_operand p.ptr_operand t = SOME fw /\
  (type_memory_size ftv = 0 \/
   w2n fw + type_memory_size ftv <= t.vs_alloca_next) ==>
  vv_store_bound cx (expr_type e) (expr_type e) es' tv (LocatedValue vt p) t
Proof
  rw[vv_store_bound_def, vv_post_def, vv_at_def] >> gvs[] >>
  imp_res_tac val_store_size_le >> decide_tac
QED

Theorem expr_store_bound_capacity:
  expr_post ctx func cenv cx e es sa sb s0 es' v op t /\
  (!tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
        ~is_word_type (expr_type e) ==>
        ?w. eval_operand op t = SOME w /\
            (type_memory_size tv = 0 \/
             w2n w + type_memory_size tv <= t.vs_alloca_next)) ==>
  expr_store_bound cx (expr_type e) v op t
Proof
  rw[expr_store_bound_def, expr_post_def, expr_val_at_def] >>
  qpat_x_assum `!tv. _ ==> val_wf _ _ /\ _` (qspec_then `tv` mp_tac) >>
  qpat_x_assum `!tv. _ ==> ?w. _` (qspec_then `tv` mp_tac) >>
  simp[] >> rpt strip_tac >> gvs[] >>
  drule val_store_size_le >> decide_tac
QED
