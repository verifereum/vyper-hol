Theory concretizePtrCallAncestry
Ancestors
  ptrDiscipline venomExecSemantics venomInst list rich_list finite_map

Definition ptr_call_ancestry_def:
  (ptr_call_ancestry PG [] <=> !site. ~MEM (SOME site) PG) /\
  (ptr_call_ancestry PG (f::stk) <=>
    f.cf_inst.inst_opcode = INVOKE /\
    (!site. MEM (SOME site) PG ==>
      ?v. MEM (Var v) f.cf_inst.inst_operands /\
          FLOOKUP f.cf_prov v = SOME site) /\
    ptr_call_ancestry f.cf_params stk)
End

Theorem ptr_invoke_imported_provenance:
  decode_invoke inst = SOME (nm,ops) /\
  MEM (SOME site) (MAP (op_prov G) ops) ==>
  ?v. MEM (Var v) inst.inst_operands /\ FLOOKUP G v = SOME site
Proof
  simp[MEM_MAP] >> rpt strip_tac >>
  Cases_on `y` >> gvs[op_prov_def] >>
  gvs[decode_invoke_def, AllCaseEqs()] >> metis_tac[listTheory.MEM]
QED

Theorem ptr_frame_call_ancestry:
  !vs0 ctx stk PG G tn fn inst s.
    frame_reachable vs0 ctx stk PG G tn fn inst s ==>
    ptr_call_ancestry PG stk
Proof
  ho_match_mp_tac frame_reachable_ind >>
  simp[ptr_call_ancestry_def] >> rpt strip_tac >>
  metis_tac[ptr_invoke_imported_provenance]
QED

Theorem ptr_call_ancestry_empty:
  ptr_call_ancestry PG [] ==> ~MEM (SOME site) PG
Proof
  simp[ptr_call_ancestry_def]
QED

Theorem ptr_call_ancestry_import:
  ptr_call_ancestry PG (f::stk) /\ MEM (SOME site) PG ==>
  ?v. MEM (Var v) f.cf_inst.inst_operands /\ FLOOKUP f.cf_prov v = SOME site
Proof
  simp[ptr_call_ancestry_def]
QED

Theorem ptr_call_ancestry_tail:
  ptr_call_ancestry PG (f::stk) ==> ptr_call_ancestry f.cf_params stk
Proof
  simp[ptr_call_ancestry_def]
QED

Theorem ptr_call_ancestry_saved:
  !stk PG n. ptr_call_ancestry PG stk /\ n < LENGTH stk ==>
  ptr_call_ancestry (EL n stk).cf_params (DROP (SUC n) stk)
Proof
  Induct >> simp[ptr_call_ancestry_def] >> rpt gen_tac >>
  Cases_on `n` >> simp[] >> metis_tac[]
QED

Theorem ptr_frame_no_entry_import:
  frame_reachable vs0 ctx [] PG G tn fn inst s ==> ~MEM (SOME site) PG
Proof
  metis_tac[ptr_frame_call_ancestry, ptr_call_ancestry_empty]
QED
