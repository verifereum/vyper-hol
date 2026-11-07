Theory bodyPtrBopInLoopContract
Ancestors bodyPtrBopInLoopCode bodyPtrDefs fragGasPathPtr ptrDiscipline
  venomState finite_map words

(* These three packages avoid duplicating the old-name/nonvariable frame,
   mutable scalar registers and universally quantified checked prefix in
   each loop branch. They introduce no new execution semantics. *)
Definition membership_loop_frame_def:
  membership_loop_frame sa G0 tn0 s0 G tn (s:venom_state) <=>
    (!x. not_fresh_at sa x ==>
      lookup_var x s = lookup_var x s0 /\
      FLOOKUP G x = FLOOKUP G0 x /\
      op_taint tn (Var x) = op_taint tn0 (Var x)) /\
    tn.t_mem = tn0.t_mem /\ tn.t_stor = tn0.t_stor /\
    tn.t_trans = tn0.t_trans /\ tn.t_imm = tn0.t_imm /\
    s = s0 with <|vs_vars := s.vs_vars; vs_current_bb := s.vs_current_bb;
      vs_prev_bb := s.vs_prev_bb; vs_inst_idx := s.vs_inst_idx|>
End

Definition membership_loop_registers_def:
  membership_loop_registers sa i (r:bytes32) G tn s <=>
    lookup_var ("%" ++ toString (sa.cs_next_var+1)) s = SOME (n2w i) /\
    lookup_var ("%" ++ toString sa.cs_next_var) s = SOME r /\
    op_prov G (Var ("%" ++ toString (sa.cs_next_var+1))) = NONE /\
    op_prov G (Var ("%" ++ toString sa.cs_next_var)) = NONE /\
    op_taint tn (Var ("%" ++ toString (sa.cs_next_var+1))) = {} /\
    op_taint tn (Var ("%" ++ toString sa.cs_next_var)) = {}
End

Definition membership_load_contract_def:
  membership_load_contract D ctx fn PG sa skip is_ctor imm loc
      (ws:bytes32 list) G0 tn0 s0 <=>
    !i G tn s. i < LENGTH ws /\
      membership_loop_frame sa G0 tn0 s0 G tn s /\
      membership_loop_registers sa i 0w G tn s /\
      s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
      s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
      ?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
        membership_loop_frame sa G0 tn0 s0 G' tn' t /\
        membership_loop_registers sa i 0w G' tn' t /\
        t.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
        t.vs_inst_idx = 2 + (if 0 < skip then 1 else 0) +
          (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) /\
        ~t.vs_halted /\
        eval_operand (Var ("%" ++ toString (sa.cs_next_var+4+
          (if 0 < skip then 1 else 0) +
          (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))) t =
          SOME (EL i ws) /\
        op_prov G' (Var ("%" ++ toString (sa.cs_next_var+4+
          (if 0 < skip then 1 else 0) +
          (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))) = NONE /\
        op_taint tn' (Var ("%" ++ toString (sa.cs_next_var+4+
          (if 0 < skip then 1 else 0) +
          (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1)))) = {}
End

Theorem membership_loop_frame_refl[simp]:
  membership_loop_frame sa G tn s G tn s
Proof
  simp[membership_loop_frame_def]
QED

Theorem membership_loop_frame_trans:
  membership_loop_frame sa G0 tn0 s0 G1 tn1 s1 /\
  membership_loop_frame sa G1 tn1 s1 G2 tn2 s2 ==>
  membership_loop_frame sa G0 tn0 s0 G2 tn2 s2
Proof
  simp[membership_loop_frame_def] >> rpt strip_tac >>
  gvs[] >>
  qpat_x_assum `s2 = _` (fn th => once_rewrite_tac[th]) >>
  qpat_x_assum `s1 = _` (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem membership_loop_frame_operand:
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  (!x. op = Var x ==> not_fresh_at sa x) ==>
  eval_operand op s = eval_operand op s0 /\
  op_prov G op = op_prov G0 op /\ op_taint tn op = op_taint tn0 op
Proof
  Cases_on `op` >> simp[eval_operand_def, op_prov_def] >>
  simp[membership_loop_frame_def] >> rpt strip_tac >>
  gvs[op_taint_def] >>
  qpat_x_assum `s = _` (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem membership_loop_registers_pc:
  membership_loop_registers sa i r G tn
    (s with <|vs_current_bb := lbl; vs_prev_bb := prev; vs_inst_idx := pc|>) <=>
  membership_loop_registers sa i r G tn s
Proof
  simp[membership_loop_registers_def, lookup_var_def]
QED

Theorem membership_loop_registers_untouched:
  membership_loop_registers sa i r G tn s /\
  lookup_var ("%" ++ toString (sa.cs_next_var+1)) t =
    lookup_var ("%" ++ toString (sa.cs_next_var+1)) s /\
  lookup_var ("%" ++ toString sa.cs_next_var) t =
    lookup_var ("%" ++ toString sa.cs_next_var) s /\
  (!x. x = "%" ++ toString (sa.cs_next_var+1) \/
       x = "%" ++ toString sa.cs_next_var ==>
       FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) ==>
  membership_loop_registers sa i r G' tn' t
Proof
  simp[membership_loop_registers_def, op_prov_def] >> metis_tac[]
QED

Theorem membership_loop_contract_init:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G tn s G' tn' t /\
    membership_loop_registers sa 0 0w G' tn' t /\ ~t.vs_halted /\
    t.vs_current_bb = fresh_label_output "in_cond" (sa.cs_next_label+1) /\
    t.vs_inst_idx = 0
Proof
  strip_tac >> drule membership_compiled_loop_init >>
  simp[] >>
  disch_then drule_all >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] mp_tac) >>
  strip_tac >> qexistsl_tac [`G'`, `tn'`, `t`] >>
  simp[membership_loop_frame_def, membership_loop_registers_def, op_prov_def] >>
  metis_tac[]
QED

Theorem membership_load_contract_empty[simp]:
  membership_load_contract D ctx fn PG sa skip is_ctor imm loc [] G tn s
Proof
  simp[membership_load_contract_def]
QED

Theorem membership_loop_frame_ghost_kept:
  membership_loop_frame sa G0 tn0 s0 G tn s ==>
  ghost_kept cenv es sa G0 tn0 s0 G tn
Proof
  simp[membership_loop_frame_def, ghost_kept_def] >> metis_tac[]
QED

(* The callback's endpoint is exactly the compiler's EQ suffix, at both
   loader widths. This does not claim that a representation supplies it. *)
Theorem membership_load_endpoint_compare:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\
  t.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
  t.vs_inst_idx = 2 + (if 0 < skip then 1 else 0) +
    (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) /\
  delta = (if 0 < skip then 1 else 0) /\
  width = (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) ==>
  ?bb. lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
    DROP t.vs_inst_idx bb.bb_instructions =
      [mk_inst (sa.cs_next_id+8+delta+width) EQ
         [Var ("%" ++ toString (sa.cs_next_var+4+delta+width));needle]
         ["%" ++ toString (sa.cs_next_var+5+delta+width)];
       mk_inst (sa.cs_next_id+9+delta+width) JNZ
         [Var ("%" ++ toString (sa.cs_next_var+5+delta+width));
          Label (fresh_label_output "in_found" (sa.cs_next_label+3));
          Label (fresh_label_output "in_incr" (sa.cs_next_label+4))] []]
Proof
  strip_tac >> drule_all membership_compiled_compare_lookup >>
  strip_tac >> gvs[] >> goal_assum (drule_at Any) >> simp[]
QED

(* Restriction changes only which variable names must be preserved. *)
Theorem membership_loop_frame_restrict:
  membership_loop_frame late G0 tn0 s0 G tn s /\
  (!x. not_fresh_at early x ==> not_fresh_at late x) ==>
  membership_loop_frame early G0 tn0 s0 G tn s
Proof
  simp[membership_loop_frame_def] >> metis_tac[]
QED

Theorem membership_loop_frame_source:
  membership_loop_frame early Gs tns ss Gh tnh sh /\
  membership_loop_frame late Gh tnh sh G tn s /\
  (!x. not_fresh_at early x ==> not_fresh_at late x) ==>
  membership_loop_frame early Gs tns ss G tn s
Proof
  metis_tac[membership_loop_frame_restrict, membership_loop_frame_trans]
QED
