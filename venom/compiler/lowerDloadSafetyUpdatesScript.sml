(* Selected provenance updates read from a fixed source snapshot. *)
Theory lowerDloadSafetyUpdates
Ancestors
  lowerDloadSafetyValues lowerDloadSafetyRelation lowerDloadSafetyKernel
  ptrDiscipline unitShapeDefs venomState venomExecSemantics execEquivParamBase
  finite_map pred_set list

Theorem ld_erase_set_prov:
  ld_erase A o_f set_prov H outs q =
  set_prov (ld_erase A o_f H) outs (OPTION_MAP (ld_erase A) q)
Proof
  Cases_on `q` >> Cases_on `outs` >>
  simp[set_prov_def, fmap_eq_flookup, FLOOKUP_o_f, FLOOKUP_DRESTRICT] >>
  Cases_on `t` >>
  simp[set_prov_def, fmap_eq_flookup, FLOOKUP_o_f, FLOOKUP_UPDATE,
       FLOOKUP_DRESTRICT] >> gen_tac >>
  IF_CASES_TAC >> simp[]
QED

Theorem ld_vars_param:
  ld_vars P A f /\ j < LENGTH f.lf_src.vs_params ==>
  ld_wordrel A (if j < LENGTH f.lf_Q then EL j f.lf_Q else NONE)
    (EL j f.lf_src.vs_params) (EL j f.lf_tgt.vs_params)
Proof
  simp[ld_vars_def]
QED

Theorem ld_erase_op_prov:
  op_prov (ld_erase A o_f H) op = OPTION_MAP (ld_erase A) (op_prov H op)
Proof
  Cases_on `op` >> simp[op_prov_def, FLOOKUP_o_f] >>
  Cases_on `FLOOKUP H s` >> simp[]
QED

Theorem ld_erase_phi_prov:
  phi_prov prev (ld_erase A o_f H) inst =
  OPTION_MAP (ld_erase A) (phi_prov prev H inst)
Proof
  Cases_on `prev` >> simp[phi_prov_def] >>
  Cases_on `resolve_phi x inst.inst_operands` >> simp[ld_erase_op_prov]
QED

Theorem ld_erase_phis_prov:
  ld_erase A o_f phis_prov prev H insts =
  phis_prov prev (ld_erase A o_f H) insts
Proof
  Induct_on `insts` >> simp[phis_prov_def] >> gen_tac >>
  IF_CASES_TAC >> simp[ld_erase_set_prov, ld_erase_phi_prov]
QED

Theorem ld_set_prov_domain:
  FDOM (set_prov H outs q) =
  if LENGTH outs = 1 /\ IS_SOME q then set outs UNION FDOM H
  else FDOM H DIFF set outs
Proof
  Cases_on `q` >> Cases_on `outs` >>
  simp[set_prov_def, FDOM_DRESTRICT, EXTENSION] >>
  Cases_on `t` >> simp[set_prov_def, FDOM_DRESTRICT, EXTENSION] >> metis_tac[]
QED

Theorem ld_vars_write:
  ld_vars P A f /\ MEM v (fn_ir_vars f.lf_fn) /\
  (!a. q = SOME a ==> v IN fn_pv P f.lf_fn) /\
  (!u. u <> v ==> FLOOKUP tv u = FLOOKUP f.lf_tv u) /\
  (~retpc_var f.lf_fn v ==>
    case q of SOME a => ld_wordrel A (SOME a) x y
    | NONE => word_agree_except
        (case FLOOKUP tv v of NONE => {} | SOME m => m) x y) ==>
  ld_vars P A
    (f with <| lf_src := f.lf_src with vs_vars := f.lf_src.vs_vars |+ (v,x);
               lf_tgt := f.lf_tgt with vs_vars := f.lf_tgt.vs_vars |+ (v,y);
               lf_H := set_prov f.lf_H [v] q; lf_tv := tv |> )
Proof
  strip_tac >>
  qpat_x_assum `ld_vars P A f` mp_tac >>
  simp[ld_vars_def, ld_set_prov_domain, FDOM_DRESTRICT,
       SUBSET_DEF, FLOOKUP_UPDATE] >> strip_tac >>
  rpt conj_tac
  >- (simp[fmap_eq_flookup, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
      gen_tac >> IF_CASES_TAC >> gvs[] >>
      first_x_assum (mp_tac o Q.AP_TERM `\m. FLOOKUP m x'`) >>
      simp[FLOOKUP_DRESTRICT])
  >- metis_tac[]
  >- (Cases_on `q` >> simp[] >> metis_tac[])
  >- (Cases_on `q` >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> Cases_on `v' = v` >>
  Cases_on `q` >> gvs[set_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  metis_tac[]
QED

Theorem ld_vars_operand_agree:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  tn.t_var = f.lf_tv /\
  eval_operand op f.lf_src = SOME x /\
  eval_operand op f.lf_tgt = SOME y /\
  (!v. op = Var v ==> ~retpc_var f.lf_fn v) ==>
  case op_prov f.lf_H op of
    SOME a => ld_wordrel A (SOME a) x y
  | NONE => word_agree_except (op_taint tn op) x y
Proof
  Cases_on `op` >>
  simp[op_prov_def, op_taint_def, eval_operand_def, lookup_var_def] >>
  strip_tac >> gvs[ld_word_agree_empty] >>
  drule_all ld_vars_value >> simp[]
QED

Theorem ld_phi_input_nonopaque:
  MEM inst (fn_insts fn) /\ inst.inst_opcode = PHI /\
  MEM out inst.inst_outputs /\ ~retpc_var fn out /\
  MEM (Var v) inst.inst_operands ==>
  ~retpc_var fn v
Proof
  simp[retpc_var_def] >> metis_tac[copy_phi_var_phi]
QED

Theorem ld_vars_phi_snapshot:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  f.lf_src.vs_prev_bb = f.lf_tgt.vs_prev_bb /\ tn.t_var = f.lf_tv /\
  MEM inst (fn_insts f.lf_fn) /\ inst.inst_opcode = PHI /\
  eval_one_phi f.lf_src inst = SOME (out,x) /\
  eval_one_phi f.lf_tgt inst = SOME (out,y) /\ ~retpc_var f.lf_fn out ==>
  case phi_prov f.lf_src.vs_prev_bb f.lf_H inst of
    SOME a => ld_wordrel A (SOME a) x y
  | NONE => word_agree_except (phi_taint f.lf_src.vs_prev_bb tn inst) x y
Proof
  simp[eval_one_phi_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  simp[phi_prov_def, phi_taint_def] >>
  irule ld_vars_operand_agree >> simp[] >>
  metis_tac[ld_phi_input_nonopaque, resolve_phi_MEM, MEM]
QED
