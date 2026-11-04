Theory lowerDloadPtrSupport
Ancestors
  ptrDiscipline lowerDloadPtrClosure finite_map pred_set list

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
