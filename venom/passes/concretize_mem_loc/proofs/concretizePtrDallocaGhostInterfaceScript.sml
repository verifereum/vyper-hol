Theory concretizePtrDallocaGhostInterface
Ancestors
  concretizePtrPrefixLedger concretizePtrChronologicalHistory
  ptrDiscipline venomState venomInst finite_map pred_set list

(* The existing paired sample compares content, not the two ghost states.
   These definitions isolate the additional induction interface.  Runtime G
   is deliberately distinct from the activation-ownership map TG. *)
Definition ptr_dalloca_ghost_vars_def:
  ptr_dalloca_ghost_vars G V s Gt Vt t <=>
    (!v. op_taint (entry_taint with t_var := Vt) (Var v) SUBSET
         op_taint (entry_taint with t_var := V) (Var v)) /\
    (!v site. FLOOKUP Gt v = SOME site ==>
      FLOOKUP G v = SOME site /\ lookup_var v s = lookup_var v t)
End

(* live selects current activation owners, not all historical births.
   No total or injective relocation is assumed: dead sites can overlap.
   Fixed and dynamic bytes use identity, live static owners use the ledger. *)
Definition ptr_dalloca_ghost_compare_def:
  ptr_dalloca_ghost_compare lo dyn registry births live G tn s Gt tnt t <=>
    ptr_dalloca_ghost_vars G tn.t_var s Gt tnt.t_var t /\
    tnt.t_stor SUBSET tn.t_stor /\
    tnt.t_trans SUBSET tn.t_trans /\
    tnt.t_imm SUBSET tn.t_imm /\
    (!i. (i < lo \/ dyn <= i) /\ i IN tnt.t_mem ==> i IN tn.t_mem) /\
    (!token aid k x y.
      live token aid /\
      ptr_ledger_owned_byte registry births token aid k x y /\
      y IN tnt.t_mem ==> x IN tn.t_mem)
End

(* Saved caller ghosts and parameter ghosts are needed at call/return,
   even though only the active frame carries memory/storage taint. *)
Definition ptr_dalloca_ghost_sample_def:
  ptr_dalloca_ghost_sample lo dyn registry births live a at <=>
    ptr_dalloca_ghost_compare lo dyn registry births live
      a.po_prov a.po_taint a.po_state at.po_prov at.po_taint at.po_state /\
    LIST_REL (\p pt. !site. pt = SOME site ==> p = SOME site)
      a.po_params at.po_params /\
    LIST_REL (\f ft.
      ptr_dalloca_ghost_vars f.cf_prov f.cf_tvar f.cf_state
        ft.cf_prov ft.cf_tvar ft.cf_state /\
      LIST_REL (\p pt. !site. pt = SOME site ==> p = SOME site)
        f.cf_params ft.cf_params) a.po_stack at.po_stack
End

Theorem ptr_dalloca_ghost_root:
  ptr_dalloca_ghost_sample lo dyn registry births live
    (ptr_observe [] [] FEMPTY entry_taint fn inst s)
    (ptr_observe [] [] FEMPTY entry_taint fnt instt t)
Proof
  simp[ptr_dalloca_ghost_sample_def, ptr_dalloca_ghost_compare_def,
       ptr_dalloca_ghost_vars_def, ptr_observe_def, entry_taint_def,
       op_taint_def]
QED

Theorem ptr_dalloca_literal_prov:
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [Lit pos] ==>
  out_prov PG G inst s = NONE
Proof
  simp[out_prov_def, first_prov_def, op_prov_def]
QED

Theorem ptr_dalloca_fresh_bytes:
  t.vs_allocas = FEMPTY /\ t'.vs_allocas = t.vs_allocas /\
  s.vs_fmp = t.vs_fmp /\ s'.vs_fmp = t'.vs_fmp ==>
  new_site_bytes t t' =
    {i | w2n t.vs_fmp <= i /\ i < w2n t'.vs_fmp} /\
  new_site_bytes t t' SUBSET new_site_bytes s s'
Proof
  simp[new_site_bytes_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem ptr_dalloca_ghost_vars:
  ptr_dalloca_ghost_compare lo dyn registry births live G tn s Gt tnt t ==>
  ptr_dalloca_ghost_vars G tn.t_var s Gt tnt.t_var t
Proof simp[ptr_dalloca_ghost_compare_def] >> metis_tac[]
QED

Theorem ptr_dalloca_ghost_prov:
  ptr_dalloca_ghost_vars G V s Gt Vt t /\ FLOOKUP Gt v = SOME site ==>
  FLOOKUP G v = SOME site /\ lookup_var v s = lookup_var v t
Proof simp[ptr_dalloca_ghost_vars_def]
QED

Theorem ptr_dalloca_ghost_var_taint:
  ptr_dalloca_ghost_vars G V s Gt Vt t ==>
  op_taint (entry_taint with t_var := Vt) (Var v) SUBSET
  op_taint (entry_taint with t_var := V) (Var v)
Proof simp[ptr_dalloca_ghost_vars_def]
QED

Theorem ptr_dalloca_ghost_storage:
  ptr_dalloca_ghost_compare lo dyn registry births live G tn s Gt tnt t ==>
  tnt.t_stor SUBSET tn.t_stor /\ tnt.t_trans SUBSET tn.t_trans /\
  tnt.t_imm SUBSET tn.t_imm
Proof simp[ptr_dalloca_ghost_compare_def] >> metis_tac[]
QED

Theorem ptr_dalloca_ghost_identity_byte:
  ptr_dalloca_ghost_compare lo dyn registry births live G tn s Gt tnt t /\
  (i < lo \/ dyn <= i) /\ i IN tnt.t_mem ==> i IN tn.t_mem
Proof simp[ptr_dalloca_ghost_compare_def] >> metis_tac[]
QED

Theorem ptr_dalloca_ghost_live_byte:
  ptr_dalloca_ghost_compare lo dyn registry births live G tn s Gt tnt t /\
  live token aid /\ ptr_ledger_owned_byte registry births token aid k x y /\
  y IN tnt.t_mem ==> x IN tn.t_mem
Proof simp[ptr_dalloca_ghost_compare_def] >> metis_tac[]
QED
