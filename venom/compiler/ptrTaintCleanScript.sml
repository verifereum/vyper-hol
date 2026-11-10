(* SSA allocation roots carry no variable taint, including suspended frames. *)
Theory ptrTaintClean
Ancestors
  ptrDiscipline venomWfProps venomExecProps finite_map list pred_set

Definition alloca_taint_clean_def:
  alloca_taint_clean fn tv <=>
    !ai root m. MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\
      ai.inst_outputs = [root] /\ FLOOKUP tv root = SOME m ==> m = {}
End

Theorem alloca_taint_clean_empty[simp]:
  alloca_taint_clean fn FEMPTY
Proof
  simp[alloca_taint_clean_def]
QED

Theorem alloca_taint_clean_restrict:
  alloca_taint_clean fn tv ==> alloca_taint_clean fn (DRESTRICT tv keys)
Proof
  simp[alloca_taint_clean_def, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem set_var_taint_lookup:
  ~MEM root outs ==>
  FLOOKUP (set_var_taint tv outs m) root = FLOOKUP tv root
Proof
  Cases_on `outs` >- simp[set_var_taint_def, FLOOKUP_DRESTRICT] >>
  Cases_on `t` >> simp[set_var_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED

Theorem out_taint_alloca:
  inst.inst_opcode = ALLOCA ==> out_taint tn inst s = {}
Proof
  strip_tac >> simp[out_taint_def] >>
  Cases_on `inst.inst_operands` >- simp[] >>
  Cases_on `t` >- (Cases_on `eval_operand h s` >> simp[]) >>
  Cases_on `t'` >> Cases_on `eval_operand h s` >> simp[]
QED

Theorem alloca_taint_clean_step:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ alloca_taint_clean fn tn.t_var ==>
  alloca_taint_clean fn (step_taint inst s s' tn).t_var
Proof
  strip_tac >> simp[alloca_taint_clean_def] >> rpt strip_tac >>
  Cases_on `MEM root inst.inst_outputs`
  >- (`inst = ai` by
        (fs[venomInstTheory.fn_insts_def] >>
         metis_tac[ssa_outputs_same_inst, MEM]) >>
      gvs[step_taint_def, set_var_taint_def, FLOOKUP_UPDATE, out_taint_alloca]) >>
  fs[step_taint_def, set_var_taint_lookup] >>
  metis_tac[alloca_taint_clean_def]
QED

Theorem alloca_taint_clean_other_outputs:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ inst.inst_opcode <> ALLOCA /\
  alloca_taint_clean fn tv ==>
  alloca_taint_clean fn (set_var_taint tv inst.inst_outputs m)
Proof
  strip_tac >> simp[alloca_taint_clean_def] >> rpt strip_tac >>
  `~MEM root inst.inst_outputs` by
    (strip_tac >> `inst = ai` by
       (fs[venomInstTheory.fn_insts_def] >>
        metis_tac[ssa_outputs_same_inst, MEM]) >> gvs[]) >>
  fs[set_var_taint_lookup] >> metis_tac[alloca_taint_clean_def]
QED

Theorem alloca_taint_clean_phis:
  !insts. ssa_form fn /\ EVERY (\i. MEM i (fn_insts fn)) insts /\
  alloca_taint_clean fn tn.t_var ==>
  alloca_taint_clean fn (phis_taint prev tn insts)
Proof
  Induct >> simp[phis_taint_def] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> gvs[] >>
  irule alloca_taint_clean_other_outputs >> simp[] >> metis_tac[]
QED

Theorem alloca_taint_clean_entry:
  ssa_form fn /\ alloca_taint_clean fn tn.t_var ==>
  alloca_taint_clean fn (entry_taint_vars fn s tn).t_var
Proof
  strip_tac >> simp[entry_taint_vars_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  irule alloca_taint_clean_phis >> simp[EVERY_MEM] >> rpt strip_tac >>
  `MEM x fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  simp[venomInstTheory.fn_insts_def] >>
  metis_tac[unitShapeDefsTheory.MEM_fn_insts_blocks]
QED

Theorem frame_reachable_alloca_taint_clean:
  !vs C stk PG G tn fn inst s.
  frame_reachable vs C stk PG G tn fn inst s ==>
  EVERY ssa_form C.ctx_functions ==>
  ssa_form fn /\ alloca_taint_clean fn tn.t_var /\
  EVERY (\f. ssa_form f.cf_fn /\ alloca_taint_clean f.cf_fn f.cf_tvar) stk
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- (rpt strip_tac >> simp[entry_taint_def] >>
      metis_tac[venomInstTheory.lookup_function_MEM, EVERY_MEM])
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      `ssa_form fn /\ alloca_taint_clean fn tn.t_var /\
       EVERY (\f. ssa_form f.cf_fn /\ alloca_taint_clean f.cf_fn f.cf_tvar) stk` by
        metis_tac[] >> simp[] >>
      irule alloca_taint_clean_step >> simp[] >>
      fs[contextCodegenRelTheory.active_inst_def, venomInstTheory.fn_insts_def] >>
      metis_tac[unitShapeDefsTheory.MEM_fn_insts_blocks, EL_MEM])
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      metis_tac[alloca_taint_clean_entry])
  >- (rpt gen_tac >> strip_tac >> strip_tac >> simp[] >>
      metis_tac[venomInstTheory.lookup_function_MEM, EVERY_MEM]) >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  gvs[] >> metis_tac[alloca_taint_clean_restrict]
QED

Theorem alloca_taint_clean_operand:
  alloca_taint_clean fn tn.t_var /\ MEM ai (fn_insts fn) /\
  ai.inst_opcode = ALLOCA /\ ai.inst_outputs = [root] ==>
  op_taint tn (Var root) = {}
Proof
  strip_tac >> simp[op_taint_def] >> Cases_on `FLOOKUP tn.t_var root` >>
  simp[] >> metis_tac[alloca_taint_clean_def]
QED

Theorem frame_reachable_alloca_root_clean:
  EVERY ssa_form C.ctx_functions /\
  frame_reachable vs C stk PG G tn fn inst s /\ MEM ai (fn_insts fn) /\
  ai.inst_opcode = ALLOCA /\ ai.inst_outputs = [root] ==>
  op_taint tn (Var root) = {}
Proof
  metis_tac[frame_reachable_alloca_taint_clean, alloca_taint_clean_operand]
QED

Theorem frame_reachable_saved_alloca_root_clean:
  EVERY ssa_form C.ctx_functions /\
  frame_reachable vs C stk PG G tn fn inst s /\ MEM f stk /\
  MEM ai (fn_insts f.cf_fn) /\ ai.inst_opcode = ALLOCA /\
  ai.inst_outputs = [root] ==>
  (case FLOOKUP f.cf_tvar root of NONE => {} | SOME m => m) = {}
Proof
  strip_tac >> drule frame_reachable_alloca_taint_clean >> simp[] >>
  strip_tac >> fs[EVERY_MEM] >>
  `alloca_taint_clean f.cf_fn f.cf_tvar` by metis_tac[] >>
  Cases_on `FLOOKUP f.cf_tvar root` >> simp[] >>
  metis_tac[alloca_taint_clean_def]
QED
