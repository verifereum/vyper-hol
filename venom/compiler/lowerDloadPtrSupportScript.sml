Theory lowerDloadPtrSupport
Ancestors
  ptrDiscipline lowerDloadPtrClosure lowerDloadPtrStatic execEquivParamBase
  pointerConfinedDefs venomInst mem2varBlockSimHelpers o1PassContract
  ctxLookupAgreeHelpers finite_map pred_set list

(* Dynamic provenance cannot occur at a statically unsupported operand. *)
Theorem op_prov_outside_support:
  FDOM G SUBSET V /\ (!v. op = Var v ==> v NOTIN V) ==>
  op_prov G op = NONE
Proof
  Cases_on `op` >> simp[op_prov_def] >>
  metis_tac[FLOOKUP_DEF, SUBSET_DEF]
QED

(* This interface covers both the output update and output killing case.
   FDOM_DRESTRICT is the existing general domain law; no duplicate of it
   is introduced. *)
Theorem set_prov_support:
  FDOM G SUBSET V /\
  (!v site. outs = [v] /\ p = SOME site ==> v IN V) ==>
  FDOM (set_prov G outs p) SUBSET V
Proof
  strip_tac >> Cases_on `outs` >- simp[set_prov_def, FDOM_DRESTRICT] >>
  rename1 `set_prov G (v::rest) p` >> Cases_on `rest` >> Cases_on `p` >>
  simp[set_prov_def, FDOM_DRESTRICT, SUBSET_DEF] >> metis_tac[SUBSET_DEF]
QED

(* PARAM cannot manufacture provenance at an unmarked or out-of-range slot. *)
Theorem out_prov_param_supported:
  inst.inst_opcode = PARAM /\ inst.inst_operands = [Lit idx] /\
  (!k. k < LENGTH PG /\ EL k PG <> NONE ==> k IN positions) /\
  out_prov PG G inst s' <> NONE ==> w2n idx IN positions
Proof
  strip_tac >> gvs[out_prov_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem first_prov_supported:
  FDOM G SUBSET V /\ first_prov G ops <> NONE ==>
  ?v. MEM (Var v) ops /\ v IN V
Proof
  Induct_on `ops` >> simp[first_prov_def] >> rpt strip_tac >>
  Cases_on `op_prov G h` >> gvs[] >- metis_tac[] >>
  Cases_on `h` >> gvs[op_prov_def] >>
  qexists `s` >> gvs[FLOOKUP_DEF, SUBSET_DEF]
QED

Theorem out_prov_supported:
  MEM inst (fn_insts fn) /\ FDOM G SUBSET fn_pv P fn /\
  (!k. k < LENGTH PG /\ EL k PG <> NONE ==> k IN P fn.fn_name) /\
  inst.inst_outputs = [v] /\ out_prov PG G inst s' <> NONE ==>
  v IN fn_pv P fn
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode = ALLOCA \/ inst.inst_opcode = DALLOCA \/
            inst.inst_opcode = PARAM`
  >- (`v IN ptr_roots P fn` by
        (gvs[ptr_roots_def, alloca_roots_def, inst_output_def]
         >- (disj1_tac >> disj1_tac >> qexists `inst` >> simp[])
         >- (disj1_tac >> disj2_tac >> qexists `inst` >> simp[]) >>
         Cases_on `inst.inst_operands` >> gvs[out_prov_def] >>
         rename1 `inst.inst_operands = arg::rest` >>
         Cases_on `rest` >> gvs[] >> Cases_on `arg` >> gvs[] >>
         disj2_tac >> qexistsl [`inst`, `c`] >> simp[] >> metis_tac[]) >>
      simp[fn_pv_def] >>
      metis_tac[roots_in_pointer_derived_vars, FINITE_ptr_roots]) >>
  gvs[out_prov_def, AllCaseEqs()] >>
  drule_all first_prov_supported >> strip_tac >>
  gvs[fn_pv_def] >> irule pointer_derived_vars_edge >>
  simp[FINITE_ptr_roots] >> qexistsl [`inst`, `v'`] >>
  simp[is_pointer_preserving_op_def]
QED

Theorem step_prov_supported:
  MEM inst (fn_insts fn) /\ FDOM G SUBSET fn_pv P fn /\
  (!k. k < LENGTH PG /\ EL k PG <> NONE ==> k IN P fn.fn_name) ==>
  FDOM (step_prov PG G inst s') SUBSET fn_pv P fn
Proof
  strip_tac >> simp[step_prov_def] >> irule set_prov_support >>
  simp[] >> metis_tac[out_prov_supported, optionTheory.NOT_NONE_SOME]
QED

Theorem phi_prov_supported:
  MEM inst (fn_insts fn) /\ inst.inst_opcode = PHI /\
  FDOM G0 SUBSET fn_pv P fn /\ inst.inst_outputs = [v] /\
  phi_prov prev G0 inst <> NONE ==> v IN fn_pv P fn
Proof
  strip_tac >> Cases_on `prev` >> gvs[phi_prov_def] >>
  Cases_on `resolve_phi x inst.inst_operands` >> gvs[] >>
  rename1 `op_prov G0 op <> NONE` >>
  `MEM op inst.inst_operands` by metis_tac[resolve_phi_MEM] >>
  Cases_on `op` >> gvs[op_prov_def] >>
  `s IN fn_pv P fn` by gvs[FLOOKUP_DEF, SUBSET_DEF] >>
  gvs[fn_pv_def] >> irule pointer_derived_vars_edge >>
  simp[FINITE_ptr_roots] >> qexistsl [`inst`, `s`] >>
  simp[is_pointer_preserving_op_def]
QED

Theorem phis_prov_supported:
  FDOM G0 SUBSET fn_pv P fn /\
  (!inst. MEM inst xs ==> MEM inst (fn_insts fn)) ==>
  FDOM (phis_prov prev G0 xs) SUBSET fn_pv P fn
Proof
  Induct_on `xs` >> simp[phis_prov_def] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  `FDOM (phis_prov prev G0 xs) SUBSET fn_pv P fn` by metis_tac[] >>
  irule set_prov_support >> simp[] >>
  rpt strip_tac >> irule phi_prov_supported >>
  qexistsl [`G0`, `h`, `prev`] >> simp[] >> metis_tac[]
QED

Theorem entry_prov_supported:
  FDOM G SUBSET fn_pv P fn ==>
  FDOM (entry_prov fn s G) SUBSET fn_pv P fn
Proof
  strip_tac >> simp[entry_prov_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  irule phis_prov_supported >> simp[] >>
  `MEM x fn.fn_blocks` by
    metis_tac[lookup_block_def, FIND_MEM] >>
  simp[fn_pv_def] >> rpt strip_tac >>
  simp[fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]
QED

Theorem invoke_prov_supported:
  fn_ptr_ok P caller /\ MEM callinst (fn_insts caller) /\
  callinst.inst_opcode = INVOKE /\ decode_invoke callinst = SOME (nm,ops) /\
  FDOM G SUBSET fn_pv P caller ==>
  !k. k < LENGTH (MAP (op_prov G) ops) /\
      EL k (MAP (op_prov G) ops) <> NONE ==> k IN P nm
Proof
  strip_tac >>
  `ptr_use_ok P (fn_pv P caller) callinst` by metis_tac[fn_ptr_ok_def] >>
  gvs[ptr_use_ok_def] >> rpt strip_tac >> gvs[EL_MAP] >>
  Cases_on `EL k ops` >> gvs[op_prov_def] >>
  `s IN fn_pv P caller` by gvs[FLOOKUP_DEF, SUBSET_DEF] >>
  metis_tac[]
QED

Theorem frame_reachable_prov_supported:
  !vs0 C stk PG G tn fn inst s.
    frame_reachable vs0 C stk PG G tn fn inst s ==>
    !P. (!f. MEM f C.ctx_functions ==> fn_ptr_ok P f) ==>
      MEM fn C.ctx_functions /\
      FDOM G SUBSET fn_pv P fn /\
      (!k. k < LENGTH PG /\ EL k PG <> NONE ==> k IN P fn.fn_name) /\
      (!f. MEM f stk ==>
        MEM f.cf_fn C.ctx_functions /\
        FDOM f.cf_prov SUBSET fn_pv P f.cf_fn /\
        (!k. k < LENGTH f.cf_params /\ EL k f.cf_params <> NONE ==>
             k IN P f.cf_fn.fn_name))
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> drule venomInstTheory.lookup_function_MEM >>
      rpt strip_tac >> gvs[])
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume frame_reachable_prov_supported[next]:
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `MEM inst (fn_insts fn)` by
    (qpat_assum `active_inst fn inst s`
       (mp_then (Pos last) mp_tac EVERY_active_inst) >>
     disch_then (qspec_then `\i. MEM i (fn_insts fn)` mp_tac) >>
     simp[EVERY_MEM]) >>
  simp[] >> irule step_prov_supported >> simp[]
QED
Resume frame_reachable_prov_supported[block]:
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  simp[] >> irule entry_prov_supported >> simp[]
QED
Resume frame_reachable_prov_supported[call]:
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `MEM fn' C.ctx_functions` by metis_tac[venomInstTheory.lookup_function_MEM] >>
  `fn'.fn_name = nm` by metis_tac[lookup_function_selected_name] >>
  `MEM inst (fn_insts fn)` by
    (qpat_assum `active_inst fn inst s`
       (mp_then (Pos last) mp_tac EVERY_active_inst) >>
     disch_then (qspec_then `\i. MEM i (fn_insts fn)` mp_tac) >>
     simp[EVERY_MEM]) >>
  `fn_ptr_ok P fn` by metis_tac[] >>
  `!k. k < LENGTH (MAP (op_prov G) ops) /\
       EL k (MAP (op_prov G) ops) <> NONE ==> k IN P nm` by
    (drule invoke_prov_supported >>
     disch_then (qspecl_then [`ops`, `nm`, `inst`, `G`] mp_tac) >> simp[]) >>
  simp[] >> rpt strip_tac >> gvs[]
QED
Resume frame_reachable_prov_supported[ret]:
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `MEM f.cf_fn C.ctx_functions /\ FDOM f.cf_prov SUBSET fn_pv P f.cf_fn /\
   (!k. k < LENGTH f.cf_params /\ EL k f.cf_params <> NONE ==>
        k IN P f.cf_fn.fn_name)` by metis_tac[MEM] >>
  simp[FDOM_DRESTRICT] >> gvs[SUBSET_DEF] >> metis_tac[]
QED
Finalise frame_reachable_prov_supported
