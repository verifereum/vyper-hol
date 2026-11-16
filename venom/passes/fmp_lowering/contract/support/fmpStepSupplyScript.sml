(* Allocation boundaries for structural lowering proofs. *)
Theory fmpStepSupply
Ancestors
  irSupply dretDesugarProofs arithmetic list

(* Occurrence-sensitive, half-open allocation intervals. *)
Definition ir_id_interval_def:
  ir_id_interval (lo:num) hi ids <=>
    lo <= hi /\ ALL_DISTINCT ids /\
    EVERY (\id. lo <= id /\ id < hi) ids
End

Theorem ir_id_interval_empty:
  ir_id_interval n n []
Proof
  simp[ir_id_interval_def]
QED

Theorem ir_id_interval_singleton:
  ir_id_interval n (SUC n) [n]
Proof
  simp[ir_id_interval_def]
QED

Theorem ir_id_interval_member:
  ir_id_interval lo hi ids /\ MEM id ids ==> lo <= id /\ id < hi
Proof
  simp[ir_id_interval_def, EVERY_MEM] >> metis_tac[]
QED

Theorem ir_id_interval_append:
  ir_id_interval lo mid xs /\ ir_id_interval mid hi ys ==>
  ir_id_interval lo hi (xs ++ ys)
Proof
  simp[ir_id_interval_def] >> rpt strip_tac
  >- (irule all_distinct_append_fresh >> simp[] >>
      gvs[EVERY_MEM] >> rpt strip_tac >>
      first_x_assum drule >> strip_tac >>
      first_x_assum drule >> decide_tac)
  >- (gvs[EVERY_MEM] >> rpt strip_tac >>
      first_x_assum drule >> decide_tac)
  >> gvs[EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> decide_tac
QED

Theorem ir_supply_old_id_bound:
  ir_supply_inst_ok s /\ MEM id s.irs_used_inst_ids ==>
  id < s.irs_next_inst
Proof
  simp[ir_supply_inst_ok_def, EVERY_MEM]
QED

Theorem ir_id_interval_old_disjoint:
  ir_supply_inst_ok s /\ ir_id_interval s.irs_next_inst hi ids ==>
  EVERY (\id. ~MEM id s.irs_used_inst_ids) ids
Proof
  simp[ir_supply_inst_ok_def, ir_id_interval_def, EVERY_MEM] >>
  rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> decide_tac
QED

Theorem fresh_inst_id_interval:
  fresh_inst_id s = (id,s') ==>
  ir_id_interval s.irs_next_inst s'.irs_next_inst [id]
Proof
  simp[fresh_inst_id_def] >> strip_tac >> gvs[ir_id_interval_singleton]
QED

Theorem fresh_ir_label_inst_ok:
  ir_supply_inst_ok s /\ fresh_ir_label s = (v,s') ==>
  ir_supply_inst_ok s'
Proof
  strip_tac >> drule fresh_ir_label_contract >> strip_tac >>
  gvs[ir_supply_inst_ok_def]
QED

Theorem fn_ir_vars_member:
  MEM v (fn_ir_vars fn) <=>
  ?bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    (MEM v inst.inst_outputs \/ MEM v (inst_uses inst))
Proof
  simp[fn_ir_vars_def, block_ir_vars_def, inst_ir_vars_def,
       MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[]
QED

Theorem fn_ir_vars_unit_coverage:
  MEM fn unit.cu_context.ctx_functions /\ MEM v (fn_ir_vars fn) ==>
  MEM v (unit_ir_vars unit)
Proof
  simp[unit_ir_vars_def, MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem fresh_ir_var_outside_function:
  EVERY (\v. MEM v s.irs_used_vars) (fn_ir_vars fn) /\
  fresh_ir_var s = (v,s') ==>
  ~MEM v (fn_ir_vars fn)
Proof
  strip_tac >> drule fresh_ir_var_contract >> strip_tac >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem fn_ir_vars_coverage_extends:
  EVERY (\v. MEM v s.irs_used_vars) (fn_ir_vars fn) /\
  dret_supply_extends s s' ==>
  EVERY (\v. MEM v s'.irs_used_vars) (fn_ir_vars fn)
Proof
  simp[dret_supply_extends_def, EVERY_MEM] >> metis_tac[MEM_APPEND]
QED
