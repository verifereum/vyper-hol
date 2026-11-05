Theory concretizePtrComparisonProbe
Ancestors concretizePtrComparisonTransport concretizePtrPrefixProbe
  concretizePtrAllocationOwnership concretizeMemLocDefs venomExecSemantics
  venomState venomInst venomWf ptrDiscipline words list finite_map
Libs wordsLib

Definition ptr_cmp_source_def:
  ptr_cmp_source sizes = ptr_probe_fn
    [mk_inst 10 ALLOCA [Lit (EL 0 sizes)] ["p"];
     mk_inst 11 ALLOCA [Lit (EL 1 sizes)] ["q"];
     mk_inst 12 ALLOCA [Lit (EL 2 sizes)] ["r"];
     mk_inst 13 EQ [Var "p"; Var "q"] ["eq"];
     mk_inst 14 LT [Var "p"; Var "q"] ["lt"];
     mk_inst 15 GT [Var "p"; Var "q"] ["gt"];
     mk_inst 16 STOP [] []]
End

Definition ptr_cmp_layout_def:
  ptr_cmp_layout sizes = concretize_function_fuel_in_context 100
    (mk_venom_context [ptr_cmp_source sizes] (SOME "probe")) []
    (ptr_cmp_source sizes)
End

Theorem ptr_cmp_zero_layout:
  OPTION_MAP (\fn. fn.fn_mems_used) (ptr_cmp_layout [0w;0w;32w]) =
    SOME [(Allocation 10,0,0); (Allocation 11,0,0); (Allocation 12,0,32)]
Proof
  EVAL_TAC
QED

Theorem ptr_cmp_mixed_layouts:
  MAP (\sizes. OPTION_MAP (\fn. fn.fn_mems_used) (ptr_cmp_layout sizes))
    [[0w;32w;0w]; [32w;0w;0w]] =
    [SOME [(Allocation 10,0,0); (Allocation 11,0,32); (Allocation 12,0,0)];
     SOME [(Allocation 10,0,32); (Allocation 11,0,0); (Allocation 12,0,0)]]
Proof
  EVAL_TAC
QED

(* Execute actual instructions, ignoring only the block cursor. *)
Definition ptr_cmp_exec_def:
  (ptr_cmp_exec [] s = SOME s) /\
  (ptr_cmp_exec (i::is) s =
    case step_inst 0 (mk_venom_context [] NONE) i s of
      OK t => ptr_cmp_exec is t | _ => NONE)
End

Definition ptr_cmp_results_def:
  ptr_cmp_results fn s = OPTION_MAP
    (\t. MAP (\v. lookup_var v t) ["p";"q";"r";"eq";"lt";"gt"])
    (ptr_cmp_exec (TAKE 6 (fn_insts fn))
      (s with <| vs_vars := FEMPTY; vs_allocas := FEMPTY; vs_alloca_next := 64 |>))
End

Theorem ptr_cmp_operational_decisions:
  MAP (\sizes. (ptr_cmp_results (ptr_cmp_source sizes) s,
    OPTION_BIND (ptr_cmp_layout sizes) (\fn. ptr_cmp_results fn s)))
    [[0w;0w;32w]; [0w;32w;0w]; [32w;0w;0w]] =
    [(SOME [SOME 64w; SOME 64w; SOME 64w; SOME 1w; SOME 0w; SOME 0w],
      SOME [SOME 0w; SOME 0w; SOME 0w; SOME 1w; SOME 0w; SOME 0w]);
     (SOME [SOME 64w; SOME 64w; SOME 96w; SOME 1w; SOME 0w; SOME 0w],
      SOME [SOME 0w; SOME 0w; SOME 0w; SOME 1w; SOME 0w; SOME 0w]);
     (SOME [SOME 64w; SOME 96w; SOME 96w; SOME 0w; SOME 1w; SOME 0w],
      SOME [SOME 0w; SOME 0w; SOME 0w; SOME 1w; SOME 0w; SOME 0w])]
Proof
  EVAL_TAC
QED

Definition ptr_cmp_live_source_def:
  ptr_cmp_live_source = ptr_probe_fn
    [mk_inst 20 ALLOCA [Lit 32w] ["r"];
     mk_inst 21 ALLOCA [Lit 0w] ["p"];
     mk_inst 22 ALLOCA [Lit 0w] ["q"];
     mk_inst 23 EQ [Var "p"; Var "q"] ["eq"];
     mk_inst 24 LT [Var "p"; Var "q"] ["lt"];
     mk_inst 25 GT [Var "p"; Var "q"] ["gt"];
     mk_inst 26 MSTORE [Var "r"; Lit 42w] [];
     mk_inst 27 STOP [] []]
End

Definition ptr_cmp_live_target_def:
  ptr_cmp_live_target = concretize_function_fuel_in_context 100
    (mk_venom_context [ptr_cmp_live_source] (SOME "probe")) [] ptr_cmp_live_source
End

Theorem ptr_cmp_live_zero_births:
  (OPTION_MAP (\fn. fn.fn_mems_used) ptr_cmp_live_target,
   ptr_cmp_results ptr_cmp_live_source s,
   OPTION_BIND ptr_cmp_live_target (\fn. ptr_cmp_results fn s)) =
    (SOME [(Allocation 20,0,32); (Allocation 21,0,0); (Allocation 22,0,0)],
     SOME [SOME 96w; SOME 96w; SOME 64w; SOME 1w; SOME 0w; SOME 0w],
     SOME [SOME 0w; SOME 0w; SOME 0w; SOME 1w; SOME 0w; SOME 0w])
Proof
  EVAL_TAC
QED

Definition ptr_cmp_at_def:
  ptr_cmp_at x y s = s with vs_vars :=
    FEMPTY |+ ("p",x) |+ ("q",y)
End

Definition ptr_cmp_ops_def:
  ptr_cmp_ops =
    [mk_inst 30 EQ [Var "p"; Var "q"] ["eq"];
     mk_inst 31 LT [Var "p"; Var "q"] ["lt"];
     mk_inst 32 GT [Var "p"; Var "q"] ["gt"]]
End

Definition ptr_cmp_at_results_def:
  ptr_cmp_at_results x y s = OPTION_MAP
    (\t. MAP (\v. lookup_var v t) ["eq";"lt";"gt"])
    (ptr_cmp_exec ptr_cmp_ops (ptr_cmp_at x y s))
End

Theorem ptr_cmp_closed_endpoint_decisions:
  ptr_cmp_at_results 64w 96w s = SOME [SOME 0w; SOME 1w; SOME 0w] /\
  ptr_cmp_at_results 0w 32w s = SOME [SOME 0w; SOME 1w; SOME 0w] /\
  ptr_cmp_at_results 96w 64w s = SOME [SOME 0w; SOME 0w; SOME 1w] /\
  ptr_cmp_at_results 32w 0w s = SOME [SOME 0w; SOME 0w; SOME 1w] /\
  ptr_cmp_at_results 96w 96w s = SOME [SOME 1w; SOME 0w; SOME 0w] /\
  ptr_cmp_at_results 0w 0w s = SOME [SOME 1w; SOME 0w; SOME 0w] /\
  0 + 32 < dimword (:256) /\ 0 + 0 < dimword (:256)
Proof
  EVAL_TAC
QED

Theorem ptr_cmp_common_site_access:
  EVERY (\i. access_ok lo (FEMPTY |+ ("p",(64,32)) |+ ("q",(64,32)))
    fn i (ptr_cmp_at 64w 96w s)) ptr_cmp_ops /\
  EVERY (\i. access_ok lo (FEMPTY |+ ("p",(64,32)) |+ ("q",(64,32)))
    fn i (ptr_cmp_at 96w 64w s)) ptr_cmp_ops /\
  EVERY (\i. access_ok lo (FEMPTY |+ ("p",(96,0)) |+ ("q",(96,0)))
    fn i (ptr_cmp_at 96w 96w s)) ptr_cmp_ops
Proof
  simp[ptr_cmp_ops_def, access_ok_def, mk_inst_def,
    contextCodegenRelTheory.source_memory_read_ranges_def,
    codegenRelTheory.source_memory_write_ranges_def,
    ptr_cmp_at_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  EVAL_TAC
QED

Theorem ptr_cmp_live_birth_records:
  OPTION_MAP (\t. MAP (FLOOKUP t.vs_allocas) [20;21;22])
    (ptr_cmp_exec (TAKE 3 (fn_insts ptr_cmp_live_source))
      (s with <| vs_vars := FEMPTY; vs_allocas := FEMPTY; vs_alloca_next := 64 |>)) =
    SOME [SOME (64,32); SOME (96,0); SOME (96,0)] /\
  EVERY inst_wf (fn_insts ptr_cmp_live_source) /\
  EVERY (\sizes. EVERY inst_wf (fn_insts (ptr_cmp_source sizes)))
    [[0w;0w;32w]; [0w;32w;0w]; [32w;0w;0w]]
Proof
  EVAL_TAC
QED
