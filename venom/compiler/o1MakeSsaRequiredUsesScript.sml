Theory o1MakeSsaRequiredUses
Ancestors o1MakeSsaClosure unitShapeDefs list pred_set

Definition retpc_reachable_required_def:
  retpc_reachable_required fn y <=>
    (?i front. MEM i (fn_insts fn) /\ MEM i.inst_opcode [RET;RETFMP;DRET] /\
       i.inst_operands = front ++ [Var y]) \/
    (?i x. MEM i (fn_insts fn) /\ i.inst_opcode = PHI /\
       MEM (Var x) i.inst_operands /\ retpc_var fn x /\
       MEM (Var y) i.inst_operands)
End

Definition retpc_full_required_def:
  retpc_full_required fn y <=>
    ?i x. MEM i (fn_insts fn) /\ i.inst_opcode = PHI /\
      MEM x i.inst_outputs /\ retpc_var fn x /\ MEM (Var y) i.inst_operands
End

Theorem retpc_required_escape:
  (!x B. required x /\ cp_bad_set RETPC_PARAM fn B ==> x NOTIN B) ==>
  !x. required x ==> retpc_var fn x
Proof
  simp[retpc_var_def] >> metis_tac[copy_phi_var_bad_set]
QED

Theorem retpc_required_certificate:
  (!i. MEM i (fn_insts (reachable_fn g)) /\
       MEM i.inst_opcode [RET;RETFMP;DRET] ==>
       ?front x. i.inst_operands = front ++ [Var x]) /\
  (!x B. retpc_reachable_required (reachable_fn g) x /\
     cp_bad_set RETPC_PARAM (reachable_fn g) B ==> x NOTIN B) /\
  (!x B. retpc_full_required g x /\ cp_bad_set RETPC_PARAM g B ==> x NOTIN B) /\
  (!i x. MEM i (fn_insts g) /\ MEM x i.inst_outputs /\ retpc_var g x ==>
     i.inst_opcode = RETPC_PARAM \/
     (i.inst_opcode = ASSIGN /\ ?y. i.inst_operands = [Var y] /\ retpc_var g y) \/
     (i.inst_opcode = PHI /\ ?y. MEM (Var y) i.inst_operands /\ retpc_var g y)) /\
  (!i j x. MEM i (fn_insts g) /\ MEM j (fn_insts g) /\
     MEM x i.inst_outputs /\ MEM x j.inst_outputs /\ retpc_var g x ==> i = j)
  ==> retpc_shape_ok g
Proof
  strip_tac >>
  `!x. retpc_reachable_required (reachable_fn g) x ==> retpc_var (reachable_fn g) x` by
    (ho_match_mp_tac retpc_required_escape >> simp[]) >>
  `!x. retpc_full_required g x ==> retpc_var g x` by
    (ho_match_mp_tac retpc_required_escape >> simp[]) >>
  qpat_x_assum `!x B. retpc_reachable_required _ _ /\ _ ==> _` kall_tac >>
  qpat_x_assum `!x B. retpc_full_required _ _ /\ _ ==> _` kall_tac >>
  pure_rewrite_tac[retpc_shape_ok_def] >> rpt conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!i. MEM i _ /\ MEM _ _ ==> _` drule >>
      simp[] >> strip_tac >> qexistsl_tac [`front`,`x`] >> simp[] >>
      first_x_assum irule >> simp[retpc_reachable_required_def] >>
      disj1_tac >> qexistsl_tac [`inst`,`front`] >> gvs[])
  >- (rpt strip_tac >>
      qpat_x_assum `!x. retpc_reachable_required _ _ ==> _` irule >>
      simp[retpc_reachable_required_def] >> disj2_tac >> metis_tac[])
  >- (rpt strip_tac >>
      qpat_x_assum `!i x. MEM i _ /\ MEM x _ /\ _ ==> _` drule_all >>
      strip_tac >> simp[] >> conj_tac
      >- (qexists_tac `y` >> simp[]) >>
      rpt strip_tac >>
      qpat_x_assum `!x. retpc_full_required _ _ ==> _` irule >>
      simp[retpc_full_required_def] >> metis_tac[])
  >> metis_tac[]
QED

(* Actual-run interface audit (no actual-run escape assertion is made here).

   Consumer                          Naming boundary                 Missing premise
   reachable return, visited block  actual_final_operand_name      last_name escapes B
   full PHI pair, patched source    actual_phi_slot_name           source-path last_name escapes B
   full PHI pair, no patch event    actual_phi_slot_unchanged      original spelling escapes B
   reachable PHI pair               same slot boundaries, then     escape in reachable_fn,
                                   reachable_inst filtering       NOT merely in full function

   actual_phi_slot_name requires a real visit e with label p and q in
   e.sve_succs. It does not license patching an arbitrary original pair.
   It gives last_name x x on path_pairs through the source's full block.
   actual_phi_slot_unchanged instead requires absence of every such event,
   and preserves x. An original writer may have been renamed, so unchanged
   x does not by itself supply a copy_phi_var witness. Inserted PHI slots
   need insertion provenance in addition to these slot-retention equations.

   actual_final_operand_name applies only to non-PHI operands of visited
   instructions, with valid indices. Its prefix includes ancestor output
   pairs and only TAKE i output pairs in the local block. Default x and
   a fresh last-name representative both still need directed seed escape.
   Unvisited instructions require a separate unchanged-block boundary.

   Important correction to the proposed C1.1 guidance: reachable_preds_def
   filters by BOTH fn_reachable fn p AND fn_cfg_edge fn p q. Therefore
   reachable_fn removes original nonpredecessor pairs even when their source
   label is reachable. Full-function writer obligations do retain these
   pairs. Any reachable escape proof must transport seeds/writers through
   this stronger filter; a full-function closure witness is insufficient.

   The certificate above is conditional. Neither naming equations, reverse
   ownership, nor unique writers prove its two no-bad-set premises. Those
   actual-run obligations, and transport across simplify_current_phis,
   remain open. *)
