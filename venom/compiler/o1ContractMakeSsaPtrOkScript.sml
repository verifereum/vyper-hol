(*
 * The syntactic half of MakeSSA's pointer discipline: the pass keeps
 * fn_ptr_ok P, of the function and of its reachable part.
 *)
Theory o1ContractMakeSsaPtrOk
Ancestors
  ptrDiscipline pointerConfinedDefs pointerConfinedProps unitShapeDefs
  venomInst venomWf cfgWf o1PassContract makeSsaCurrentDefs makeSsaCurrentProps
  makeSsaCurrentCfg makeSsaCurrentOrigin makeSsaCurrentWfSsa
  makeSsaCurrentInputOk makeSsaCurrentNonDegenerate

Definition mssa_inst_origin_def:
  mssa_inst_origin orig fn inst' <=>
    (?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode <> PHI /\
       inst'.inst_id = inst.inst_id /\
       inst'.inst_opcode = inst.inst_opcode /\
       MAP orig inst'.inst_outputs = inst.inst_outputs /\
       MAP (\op. case op of Var u => Var (orig u) | _ => op)
         inst'.inst_operands = inst.inst_operands) \/
    (inst'.inst_opcode = NOP /\ inst'.inst_outputs = [] /\
       inst'.inst_operands = []) \/
    ((inst'.inst_opcode = PHI \/ inst'.inst_opcode = ASSIGN) /\
     ?w inst. inst'.inst_outputs = [w] /\ MEM inst (fn_insts fn) /\
       MEM (orig w) inst.inst_outputs /\
       (inst'.inst_opcode = ASSIGN ==> ?u. inst'.inst_operands = [Var u]) /\
       (!op. MEM op inst'.inst_operands ==> ?x. op = Var x \/ op = Label x) /\
       !u. MEM (Var u) inst'.inst_operands ==>
         orig u = orig w \/
         (inst.inst_opcode = PHI /\ MEM (Var (orig u)) inst.inst_operands))
End

Theorem mssa_origin:
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') ==>
  ?orig. !inst. MEM inst (fn_insts fn') ==> mssa_inst_origin orig fn inst
Proof
  strip_tac >> rewrite_tac[mssa_inst_origin_def] >>
  irule make_ssa_current_fn_origin >>
  gvs[make_ssa_input_ok_def] >> metis_tac[]
QED

Theorem mssa_wf_ssa:
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') ==> wf_ssa fn'
Proof
  strip_tac >> irule make_ssa_current_fn_wf_ssa >>
  gvs[make_ssa_input_ok_def] >> metis_tac[]
QED

Theorem mssa_no_entry_edge:
  wf_function fn /\ first_block_no_preds fn /\
  make_ssa_current_fn s fn = (fn',s') /\
  fn_entry_label fn' = SOME entry ==> !l. ~fn_cfg_edge fn' l entry
Proof
  strip_tac >>
  `ALL_DISTINCT (fn_labels fn)` by gvs[wf_function_def] >>
  drule_all make_ssa_current_fn_cfg >> strip_tac >>
  gvs[fn_entry_label_def, entry_block_def, AllCaseEqs()] >>
  gvs[first_block_no_preds_def, listTheory.EVERY_MEM, fn_cfg_edge_def] >>
  metis_tac[]
QED

Theorem mssa_phi_output:
  (!i. MEM i (fn_insts fn') ==> mssa_inst_origin orig fn i) /\
  MEM inst (fn_insts fn') /\ inst.inst_opcode = PHI ==>
  ?w. inst.inst_outputs = [w]
Proof
  strip_tac >> first_x_assum drule >>
  simp[mssa_inst_origin_def] >> metis_tac[]
QED

Theorem mssa_entry_no_phi:
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') /\
  MEM bb fn'.fn_blocks /\ fn_entry_label fn' = SOME bb.bb_label ==>
  !inst. MEM inst bb.bb_instructions ==> inst.inst_opcode <> PHI
Proof
  strip_tac >>
  `?orig. !inst. MEM inst (fn_insts fn') ==> mssa_inst_origin orig fn inst` by
    (irule mssa_origin >> metis_tac[]) >>
  drule_all make_ssa_current_fn_input_ok >> strip_tac >>
  drule_all make_ssa_current_fn_phis_non_degenerate >> strip_tac >>
  `!l. ~fn_cfg_edge fn' l bb.bb_label` by
    (irule mssa_no_entry_edge >> metis_tac[]) >>
  rpt strip_tac >>
  `MEM inst (fn_insts fn')` by
    (simp[fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  `?w. inst.inst_outputs = [w]` by
    (irule mssa_phi_output >> metis_tac[]) >>
  gvs[fn_phis_non_degenerate_def] >> metis_tac[]
QED

Theorem mssa_root_output:
  fn_inst_wf fn /\ mssa_inst_origin orig fn inst' /\
  (inst'.inst_opcode = ALLOCA \/ inst'.inst_opcode = DALLOCA \/
   inst'.inst_opcode = PARAM) ==>
  ?w. inst'.inst_outputs = [w]
Proof
  simp[mssa_inst_origin_def] >> rpt strip_tac >>
  gvs[fn_inst_wf_def, listTheory.EVERY_MEM,
      fn_insts_def, MEM_fn_insts_blocks_iff] >>
  first_x_assum drule_all >> simp[inst_wf_def] >>
  strip_tac >>
  `LENGTH inst'.inst_outputs = 1` by metis_tac[listTheory.LENGTH_MAP] >>
  Cases_on `inst'.inst_outputs` >> gvs[] >>
  rename1 `LENGTH rest = 0` >> Cases_on `rest` >> gvs[]
QED

(* Why it holds.  make_ssa_current_fn_origin gives orig, from fn' vars to
   fn vars: each instruction of fn' is a renamed non-PHI of fn (same
   opcode and id, outputs and Var operands mapped by orig), a NOP, or a
   PHI/ASSIGN whose output w is a renamed output of some instruction of fn
   and whose Var operands u have orig u = orig w or are operands of the
   input PHI defining orig w.

   Forward: v' IN pointer_derived_vars fn' R' ==> orig v' IN
   pointer_derived_vars fn R, for R' = ptr_roots P fn', alloca_roots fn',
   and ptr_roots P fn' DIFF alloca_roots fn' against the matching R of fn
   (pointer_use_vars_least).  For the last one, a DALLOCA or pointer PARAM
   output of fn is a pointer, so fn_ptr_ok's definition clause on fn puts
   it outside alloca_roots fn.

   Backward: a variable v' of fn' with orig v' IN fn_pv P fn is in
   fn_pv P fn'.  By induction on where v' is defined, ordered by the
   shortest CFG distance of its block from the entry, then by its index:
   fn_defs_reach_uses fn' and all_reachable fn' (make_ssa_current_fn_input_ok)
   put a definition of each operand earlier on a shortest path (a PHI
   operand's at the end of the predecessor the shortest path comes
   through, fn_phis_cover_preds fn').  The definition of v' is, by fn's
   definition clause, a root (and a root of fn'), or pointer-preserving
   with a pointer operand; a PHI or ASSIGN of the second kind has only
   pointer operands (fn's clause and phi_pv_all_var fn), and has at least
   one (ASSIGN: origin; PHI: make_ssa_current_fn_phis_non_degenerate, and
   no PHI sits in the entry block: its pairs are CFG edges into the block,
   make_ssa_current_fn_cfg, first_block_no_preds).

   Then each conjunct of fn_ptr_ok P fn' follows from fn's: per
   instruction through orig and forward inclusion; the LT/GT/EQ exemption
   and phi_pv_all_var need backward inclusion; the definition clause on
   fn' follows from SSA (wf_ssa fn', make_ssa_current_fn_wf_ssa: one
   definition per variable) and fn' pv being the least closure.

   Every Var operand of a PHI of fn' sits in a (Label, Var) pair whose
   label is a CFG edge into its block: wf_ssa fn' gives phi_edge_uses_wf,
   hence phi_well_formed (phi_well_formed_var_pair).  So the backward
   induction reaches every PHI operand, and with all_reachable fn'
   filter_phi_ops drops nothing: reachable_fn fn' = fn'. *)
Theorem make_ssa_current_fn_ptr_ok:
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') /\ fn_ptr_ok P fn ==>
  fn_ptr_ok P fn' /\ fn_ptr_ok P (reachable_fn fn')
Proof
  cheat
QED
