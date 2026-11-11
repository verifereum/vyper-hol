Theory o1MakeSsaOpaqueShape
Ancestors o1MakeSsaRetpcTransport o1ContractMakeSsaPtrOk unitShapeDefs
  o1PassContract list

Theorem mssa_gas_origin_forward:
  !g v. gas_var g v ==> !orig fn.
  (!i. MEM i (fn_insts g) ==> mssa_inst_origin orig fn i) ==>
  gas_var fn (orig v)
Proof
  simp[gas_var_def] >> Induct_on `copy_phi_var` >> rpt strip_tac >> gvs[]
  >- (qpat_x_assum `!i. MEM i _ ==> mssa_inst_origin _ _ _` drule >>
      pure_rewrite_tac[mssa_inst_origin_def] >> strip_tac >> gvs[] >>
      metis_tac[copy_phi_var_rules, MEM_MAP]) >>
  rename1 `copy_phi_var GAS g u` >>
  `copy_phi_var GAS fn (orig u)` by
    (first_x_assum irule >> simp[]) >>
  qpat_x_assum `!i. MEM i _ ==> mssa_inst_origin _ _ _` drule >>
  pure_rewrite_tac[mssa_inst_origin_def] >> strip_tac >> gvs[]
  >- (`MEM (orig v) inst'.inst_outputs` by metis_tac[MEM_MAP] >>
      irule (cj 2 copy_phi_var_rules) >> metis_tac[]) >>
  metis_tac[cj 3 copy_phi_var_rules]
QED

Theorem mssa_opaque_origin:
  (!i. MEM i (fn_insts g) ==> mssa_inst_origin orig fn i) /\
  opaque_use_ok fn ==> opaque_use_ok g
Proof
  strip_tac >> simp[opaque_use_ok_def] >> rpt strip_tac >>
  `retpc_var fn (orig x)` by (irule mssa_retpc_origin_forward >> metis_tac[]) >>
  `mssa_inst_origin orig fn inst` by metis_tac[] >>
  qpat_x_assum `mssa_inst_origin _ _ _` mp_tac >>
  pure_rewrite_tac[mssa_inst_origin_def] >> strip_tac >> gvs[retpc_use_ok_def] >>
  `MEM (Var (orig x)) inst'.inst_operands` by
    (qpat_x_assum `MAP _ inst.inst_operands = _` (SUBST1_TAC o SYM) >>
     simp[MEM_MAP] >> qexists `Var x` >> simp[]) >>
  drule_all opaque_use_ok_retpc_use >>
  simp[retpc_use_ok_def] >> strip_tac >> gvs[] >>
  gvs[MAP_EQ_APPEND] >> rpt strip_tac >>
  qpat_x_assum `~MEM _ (MAP _ _)` mp_tac >>
  simp[MEM_MAP] >> qexists `Var x` >> simp[]
QED

Theorem mssa_dalloca_origin:
  (!i. MEM i (fn_insts g) ==> mssa_inst_origin orig fn i) /\
  (!i x. MEM i (fn_insts fn) /\ i.inst_opcode = DALLOCA /\
    MEM x i.inst_outputs ==> ~gas_var fn x /\ ~retpc_var fn x) ==>
  !i x. MEM i (fn_insts g) /\ i.inst_opcode = DALLOCA /\
    MEM x i.inst_outputs ==> ~gas_var g x /\ ~retpc_var g x
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `mssa_inst_origin orig fn i` by metis_tac[] >>
  `~gas_var fn (orig x) /\ ~retpc_var fn (orig x)` by
    (qpat_x_assum `mssa_inst_origin _ _ _` mp_tac >>
     pure_rewrite_tac[mssa_inst_origin_def] >> strip_tac >> gvs[] >>
     `MEM (orig x) inst.inst_outputs` by metis_tac[MEM_MAP] >>
     metis_tac[]) >>
  metis_tac[mssa_gas_origin_forward, mssa_retpc_origin_forward]
QED

Theorem make_ssa_current_fn_opaque_use_ok:
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\ opaque_use_ok fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (g,s') ==> opaque_use_ok g
Proof
  strip_tac >> drule_all mssa_origin >> strip_tac >>
  irule mssa_opaque_origin >> metis_tac[]
QED

Theorem make_ssa_current_fn_dalloca_exclusions:
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (g,s') /\
  (!i x. MEM i (fn_insts fn) /\ i.inst_opcode = DALLOCA /\
    MEM x i.inst_outputs ==> ~gas_var fn x /\ ~retpc_var fn x) ==>
  !i x. MEM i (fn_insts g) /\ i.inst_opcode = DALLOCA /\
    MEM x i.inst_outputs ==> ~gas_var g x /\ ~retpc_var g x
Proof
  strip_tac >> drule_all mssa_origin >> strip_tac >>
  rpt gen_tac >> strip_tac >> irule mssa_dalloca_origin >> metis_tac[]
QED
