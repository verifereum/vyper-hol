(* Static origin invariants.  Agreement is deliberately restricted to the
   allocated supply, and stack coverage includes keys as well as values. *)
Theory makeSsaOriginInvariant
Ancestors
  makeSsaCurrentProps makeSsaCurrentDefs venomInst list alist

Definition origin_agrees_def:
  origin_agrees s (orig:string -> string) orig' <=>
    !v. MEM v s.irs_used_vars ==> orig' v = orig v
End

Definition origin_coherent_def:
  origin_coherent (orig:string -> string) stacks <=>
    !k ns u. MEM (k,ns) stacks /\ MEM u ns ==> orig u = orig k
End

Definition origin_stacks_covered_def:
  origin_stacks_covered s stacks <=>
    !k ns. MEM (k,ns) stacks ==>
      MEM k s.irs_used_vars /\ !u. MEM u ns ==> MEM u s.irs_used_vars
End

Definition origin_ordinary_def:
  origin_ordinary fn orig i <=>
    ?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode <> PHI /\
      i.inst_id = inst.inst_id /\ i.inst_opcode = inst.inst_opcode /\
      MAP orig i.inst_outputs = inst.inst_outputs /\
      MAP (\op. case op of Var u => Var (orig u) | _ => op)
        i.inst_operands = inst.inst_operands
End

Definition origin_phi_def:
  origin_phi fn orig i <=>
    ?w inst. i.inst_outputs = [w] /\ MEM inst (fn_insts fn) /\
      MEM (orig w) inst.inst_outputs /\
      (i.inst_opcode = ASSIGN ==> ?u. i.inst_operands = [Var u]) /\
      (!op. MEM op i.inst_operands ==> ?x. op = Var x \/ op = Label x) /\
      !u. MEM (Var u) i.inst_operands ==>
        orig u = orig w \/
        (inst.inst_opcode = PHI /\ MEM (Var (orig u)) inst.inst_operands)
End

Definition origin_before_cleanup_def:
  origin_before_cleanup fn orig i <=>
    origin_ordinary fn orig i \/
    (i.inst_opcode = PHI /\ origin_phi fn orig i)
End

Definition origin_after_cleanup_def:
  origin_after_cleanup fn orig i <=>
    origin_ordinary fn orig i \/
    (i.inst_opcode = NOP /\ i.inst_outputs = [] /\ i.inst_operands = []) \/
    ((i.inst_opcode = PHI \/ i.inst_opcode = ASSIGN) /\ origin_phi fn orig i)
End

Definition origin_inst_covered_def:
  origin_inst_covered s i <=>
    (!v. MEM v i.inst_outputs ==> MEM v s.irs_used_vars) /\
    (!v. MEM (Var v) i.inst_operands ==> MEM v s.irs_used_vars)
End

Theorem origin_agrees_refl:
  origin_agrees s orig orig
Proof
  simp[origin_agrees_def]
QED

Theorem origin_agrees_trans:
  origin_agrees s orig orig' /\ origin_agrees s orig' orig'' ==>
  origin_agrees s orig orig''
Proof
  simp[origin_agrees_def]
QED

Theorem origin_agrees_restrict:
  ssa_supply_extends s s' /\ origin_agrees s' orig orig' ==>
  origin_agrees s orig orig'
Proof
  simp[ssa_supply_extends_def, origin_agrees_def] >> metis_tac[]
QED

Theorem origin_coherent_transport:
  origin_agrees s orig orig' /\ origin_stacks_covered s stacks /\
  origin_coherent orig stacks ==> origin_coherent orig' stacks
Proof
  simp[origin_agrees_def, origin_stacks_covered_def, origin_coherent_def] >>
  metis_tac[]
QED

Theorem origin_stacks_covered_extends:
  ssa_supply_extends s s' /\ origin_stacks_covered s stacks ==>
  origin_stacks_covered s' stacks
Proof
  simp[ssa_supply_extends_def, origin_stacks_covered_def] >> metis_tac[]
QED

Theorem origin_stacks_values_covered:
  origin_stacks_covered s stacks ==> ssa_stacks_covered s stacks
Proof
  simp[origin_stacks_covered_def, ssa_stacks_covered_def,
       ssa_vars_covered_def, EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]
QED

Theorem origin_map_outputs_agree:
  origin_agrees s orig orig' /\ origin_inst_covered s i ==>
  MAP orig' i.inst_outputs = MAP orig i.inst_outputs
Proof
  rpt strip_tac >> irule MAP_CONG >>
  gvs[origin_agrees_def, origin_inst_covered_def]
QED

Theorem origin_map_operands_agree:
  origin_agrees s orig orig' /\ origin_inst_covered s i ==>
  MAP (\op. case op of Var u => Var (orig' u) | _ => op) i.inst_operands =
  MAP (\op. case op of Var u => Var (orig u) | _ => op) i.inst_operands
Proof
  rpt strip_tac >> irule MAP_CONG >> simp[] >> rpt strip_tac >> Cases_on `x` >>
  gvs[origin_agrees_def, origin_inst_covered_def]
QED

Theorem origin_ordinary_transport:
  origin_agrees s orig orig' /\ origin_inst_covered s i /\
  origin_ordinary fn orig i ==> origin_ordinary fn orig' i
Proof
  rpt strip_tac >>
  drule_all origin_map_outputs_agree >>
  drule_all origin_map_operands_agree >>
  rpt strip_tac >> gvs[origin_ordinary_def] >> metis_tac[]
QED

Theorem origin_phi_transport:
  origin_agrees s orig orig' /\ origin_inst_covered s i /\
  origin_phi fn orig i ==> origin_phi fn orig' i
Proof
  simp[origin_phi_def, origin_inst_covered_def, origin_agrees_def] >>
  rpt strip_tac >> qexistsl [`w`, `inst`] >> gvs[]
QED

Theorem origin_before_cleanup_transport:
  origin_agrees s orig orig' /\ origin_inst_covered s i /\
  origin_before_cleanup fn orig i ==> origin_before_cleanup fn orig' i
Proof
  simp[origin_before_cleanup_def] >>
  metis_tac[origin_ordinary_transport, origin_phi_transport]
QED

Theorem origin_after_cleanup_transport:
  origin_agrees s orig orig' /\ origin_inst_covered s i /\
  origin_after_cleanup fn orig i ==> origin_after_cleanup fn orig' i
Proof
  simp[origin_after_cleanup_def] >>
  metis_tac[origin_ordinary_transport, origin_phi_transport]
QED

Theorem origin_latest_current_name:
  origin_coherent orig (SND rs) ==>
  orig (latest_current_name rs v) = orig v
Proof
  PairCases_on `rs` >> simp[latest_current_name_def] >>
  rpt CASE_TAC >> gvs[origin_coherent_def] >>
  imp_res_tac ALOOKUP_MEM >> metis_tac[MEM]
QED

Theorem origin_coherent_push:
  origin_coherent orig stacks /\ orig name = orig v ==>
  origin_coherent orig
    ((v,name::(case ALOOKUP stacks v of SOME ns => ns | NONE => [])) ::
      FILTER (\(k,_). k <> v) stacks)
Proof
  Cases_on `ALOOKUP stacks v` >>
  simp[origin_coherent_def, MEM_FILTER] >> rpt strip_tac >>
  gvs[] >> imp_res_tac ALOOKUP_MEM >> metis_tac[]
QED

Theorem origin_covered_push:
  origin_stacks_covered s stacks /\
  MEM v s.irs_used_vars /\ MEM name s.irs_used_vars ==>
  origin_stacks_covered s
    ((v,name::(case ALOOKUP stacks v of SOME ns => ns | NONE => [])) ::
      FILTER (\(k,_). k <> v) stacks)
Proof
  Cases_on `ALOOKUP stacks v` >>
  simp[origin_stacks_covered_def, MEM_FILTER] >> rpt strip_tac >>
  gvs[] >> imp_res_tac ALOOKUP_MEM >> metis_tac[]
QED

Theorem origin_push_current_name:
  origin_coherent orig (SND rs) /\
  origin_stacks_covered s (SND rs) /\ MEM v s.irs_used_vars /\
  push_current_name s rs v = (rs',s',name) ==>
  ?orig'. origin_agrees s orig orig' /\ orig' name = orig v /\
    origin_coherent orig' (SND rs') /\
    origin_stacks_covered s' (SND rs') /\ ssa_supply_extends s s'
Proof
  PairCases_on `rs` >>
  simp[push_current_name_def] >>
  Cases_on `ALOOKUP rs0 v`
  >- (simp[] >> rpt strip_tac >> gvs[] >> qexists_tac `orig` >>
      simp[origin_agrees_refl, ssa_supply_extends_refl,
           origin_coherent_push, origin_covered_push]) >>
  Cases_on `x = 0`
  >- (simp[] >> rpt strip_tac >> gvs[] >> qexists_tac `orig` >>
      simp[origin_agrees_refl, ssa_supply_extends_refl,
           origin_coherent_push, origin_covered_push]) >>
  simp[] >> pairarg_tac >> simp[] >> rpt strip_tac >> gvs[] >>
  `ssa_supply_extends s s'` by metis_tac[fresh_ir_var_extends] >>
  drule irSupplyTheory.fresh_ir_var_contract >> strip_tac >>
  qpat_x_assum `name = STRCAT _ _` kall_tac >>
  qabbrev_tac `neworig = (\u. if u = name then orig v else orig u)` >>
  `origin_agrees s orig neworig` by
    (simp[origin_agrees_def, Abbr `neworig`] >> metis_tac[]) >>
  `neworig name = orig v` by simp[Abbr `neworig`] >>
  `neworig v = orig v` by
    (gvs[origin_agrees_def]) >>
  `origin_coherent neworig rs1` by metis_tac[origin_coherent_transport] >>
  `origin_stacks_covered s' rs1` by metis_tac[origin_stacks_covered_extends] >>
  qexists_tac `neworig` >> simp[] >>
  conj_tac
  >- (irule origin_coherent_push >> simp[]) >>
  irule origin_covered_push >> simp[]
QED

Theorem origin_before_cleanup_list_transport:
  origin_agrees s orig orig' /\ EVERY (origin_inst_covered s) insts /\
  EVERY (origin_before_cleanup fn orig) insts ==>
  EVERY (origin_before_cleanup fn orig') insts
Proof
  simp[EVERY_MEM] >> metis_tac[origin_before_cleanup_transport]
QED

Theorem origin_after_cleanup_list_transport:
  origin_agrees s orig orig' /\ EVERY (origin_inst_covered s) insts /\
  EVERY (origin_after_cleanup fn orig) insts ==>
  EVERY (origin_after_cleanup fn orig') insts
Proof
  simp[EVERY_MEM] >> metis_tac[origin_after_cleanup_transport]
QED
