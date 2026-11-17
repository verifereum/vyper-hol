Theory concretizePtrDallocaRuntimeCall
Ancestors
  concretizePtrDallocaGhostInterface venomExecSemantics venomState venomInst
  ptrDiscipline tupleLoadProps finite_map list pred_set

Theorem ptr_dalloca_call_operand:
  ptr_dalloca_ghost_vars G V s Gout Vt t /\
  (!v site. FLOOKUP Gout v = SOME site ==> FLOOKUP TG v = NONE) /\
  (!v site. FLOOKUP TG v = NONE /\ FLOOKUP G v = SOME site ==>
     FLOOKUP Gout v = SOME site) ==>
  (!site. op_prov Gout op = SOME site ==>
     op_prov G op = SOME site /\ op_prov TG op = NONE /\
     eval_operand op s = eval_operand op t) /\
  (!site. op_prov TG op = NONE /\ op_prov G op = SOME site ==>
     op_prov Gout op = SOME site)
Proof
  Cases_on `op` >> simp[op_prov_def, eval_operand_def,
    ptr_dalloca_ghost_vars_def] >> metis_tac[]
QED

Theorem ptr_dalloca_call_args:
  ptr_dalloca_ghost_vars G V s Gout Vt t /\
  (!v site. FLOOKUP Gout v = SOME site ==> FLOOKUP TG v = NONE) /\
  (!v site. FLOOKUP TG v = NONE /\ FLOOKUP G v = SOME site ==>
     FLOOKUP Gout v = SOME site) /\
  eval_operands ops s = SOME args /\ eval_operands ops t = SOME argst ==>
  LENGTH args = LENGTH ops /\ LENGTH argst = LENGTH ops /\
  (!k site. k < LENGTH ops ==>
    (EL k (MAP (op_prov Gout) ops) = SOME site ==>
      EL k (MAP (op_prov G) ops) = SOME site /\
      EL k (MAP (op_prov TG) ops) = NONE /\ EL k args = EL k argst) /\
    (EL k (MAP (op_prov TG) ops) = NONE /\
      EL k (MAP (op_prov G) ops) = SOME site ==>
      EL k (MAP (op_prov Gout) ops) = SOME site))
Proof
  strip_tac >>
  `LENGTH args = LENGTH ops /\ LENGTH argst = LENGTH ops` by
    metis_tac[eval_operands_length] >> simp[] >>
  rpt strip_tac >> fs[listTheory.EL_MAP] >>
  drule_all ptr_dalloca_call_operand >>
  disch_then (qspec_then `EL k ops` mp_tac) >>
  `eval_operand (EL k ops) s = SOME (EL k args)` by
    metis_tac[eval_operands_index] >>
  `eval_operand (EL k ops) t = SOME (EL k argst)` by
    metis_tac[eval_operands_index] >>
  gvs[listTheory.EL_MAP] >> strip_tac >> metis_tac[]
QED

(* Call entry resets only variable ghosts. Persistent taint is deliberately
   not constrained here. The block-entry phase is a separate contract. *)
Theorem ptr_dalloca_runtime_call:
  ptr_dalloca_ghost_vars G V s Gout Vt t /\
  (!v site. FLOOKUP Gout v = SOME site ==> FLOOKUP TG v = NONE) /\
  (!v site. FLOOKUP TG v = NONE /\ FLOOKUP G v = SOME site ==>
     FLOOKUP Gout v = SOME site) /\
  eval_operands ops s = SOME args /\ eval_operands ops t = SOME argst /\
  setup_callee fn args s = SOME cs /\
  setup_callee fnt argst t = SOME cst ==>
  LENGTH (MAP (op_prov TG) ops) = LENGTH (MAP (op_prov G) ops) /\
  LENGTH (MAP (op_prov G) ops) = LENGTH (MAP (op_prov Gout) ops) /\
  LENGTH cs.vs_params = LENGTH ops /\ LENGTH cst.vs_params = LENGTH ops /\
  (!k site. k < LENGTH ops ==>
    (EL k (MAP (op_prov Gout) ops) = SOME site ==>
      EL k (MAP (op_prov G) ops) = SOME site /\
      EL k (MAP (op_prov TG) ops) = NONE /\
      EL k cs.vs_params = EL k cst.vs_params) /\
    (EL k (MAP (op_prov TG) ops) = NONE /\
      EL k (MAP (op_prov G) ops) = SOME site ==>
      EL k (MAP (op_prov Gout) ops) = SOME site)) /\
  ptr_dalloca_ghost_vars FEMPTY FEMPTY cs FEMPTY FEMPTY cst /\
  (!v site. FLOOKUP FEMPTY v = SOME site ==> FLOOKUP FEMPTY v = NONE) /\
  (!v site. FLOOKUP FEMPTY v = NONE /\ FLOOKUP FEMPTY v = SOME site ==>
     FLOOKUP FEMPTY v = SOME site)
Proof
  strip_tac >> drule_all ptr_dalloca_call_args >>
  imp_res_tac setup_callee_frame >>
  simp[ptr_dalloca_ghost_vars_def, op_taint_def, entry_taint_def]
QED

(* Zip ownership snapshots with source frames, never with numerical ghosts.
   Keeping the parameter values in this saved relation is essential on return. *)
Theorem ptr_dalloca_runtime_call_saved:
  ptr_dalloca_ghost_vars G V s Gout Vt t /\
  (!v site. FLOOKUP Gout v = SOME site ==> FLOOKUP TG v = NONE) /\
  (!v site. FLOOKUP TG v = NONE /\ FLOOKUP G v = SOME site ==>
     FLOOKUP Gout v = SOME site) /\
  LENGTH PT = LENGTH PG /\ LENGTH PG = LENGTH PGt /\
  LENGTH s.vs_params = LENGTH PG /\ LENGTH t.vs_params = LENGTH PGt /\
  (!k site. k < LENGTH PG ==>
    (EL k PGt = SOME site ==> EL k PG = SOME site /\ EL k PT = NONE /\
      EL k s.vs_params = EL k t.vs_params) /\
    (EL k PT = NONE /\ EL k PG = SOME site ==> EL k PGt = SOME site)) /\
  LENGTH saved = LENGTH stk /\
  LIST_REL (\((pt,tg),f) ft.
    ptr_dalloca_ghost_vars f.cf_prov f.cf_tvar f.cf_state
      ft.cf_prov ft.cf_tvar ft.cf_state /\
    (!v site. FLOOKUP ft.cf_prov v = SOME site ==> FLOOKUP tg v = NONE) /\
    (!v site. FLOOKUP tg v = NONE /\ FLOOKUP f.cf_prov v = SOME site ==>
       FLOOKUP ft.cf_prov v = SOME site) /\
    LENGTH pt = LENGTH f.cf_params /\ LENGTH f.cf_params = LENGTH ft.cf_params /\
    LENGTH f.cf_state.vs_params = LENGTH f.cf_params /\
    LENGTH ft.cf_state.vs_params = LENGTH ft.cf_params /\
    (!k site. k < LENGTH f.cf_params ==>
      (EL k ft.cf_params = SOME site ==>
        EL k f.cf_params = SOME site /\ EL k pt = NONE /\
        EL k f.cf_state.vs_params = EL k ft.cf_state.vs_params) /\
      (EL k pt = NONE /\ EL k f.cf_params = SOME site ==>
        EL k ft.cf_params = SOME site))) (ZIP (saved,stk)) stkt ==>
  LENGTH ((PT,TG)::saved) = LENGTH
    (<| cf_fn := fn; cf_inst := callinst; cf_state := s;
        cf_params := PG; cf_prov := G; cf_tvar := V |> :: stk) /\
  LIST_REL (\((pt,tg),f) ft.
    ptr_dalloca_ghost_vars f.cf_prov f.cf_tvar f.cf_state
      ft.cf_prov ft.cf_tvar ft.cf_state /\
    (!v site. FLOOKUP ft.cf_prov v = SOME site ==> FLOOKUP tg v = NONE) /\
    (!v site. FLOOKUP tg v = NONE /\ FLOOKUP f.cf_prov v = SOME site ==>
       FLOOKUP ft.cf_prov v = SOME site) /\
    LENGTH pt = LENGTH f.cf_params /\ LENGTH f.cf_params = LENGTH ft.cf_params /\
    LENGTH f.cf_state.vs_params = LENGTH f.cf_params /\
    LENGTH ft.cf_state.vs_params = LENGTH ft.cf_params /\
    (!k site. k < LENGTH f.cf_params ==>
      (EL k ft.cf_params = SOME site ==>
        EL k f.cf_params = SOME site /\ EL k pt = NONE /\
        EL k f.cf_state.vs_params = EL k ft.cf_state.vs_params) /\
      (EL k pt = NONE /\ EL k f.cf_params = SOME site ==>
        EL k ft.cf_params = SOME site)))
    (ZIP (((PT,TG)::saved),
      (<| cf_fn := fn; cf_inst := callinst; cf_state := s;
          cf_params := PG; cf_prov := G; cf_tvar := V |> :: stk)))
    (<| cf_fn := fnt; cf_inst := invt; cf_state := t;
        cf_params := PGt; cf_prov := Gout; cf_tvar := Vt |> :: stkt)
Proof
  simp[]
QED
