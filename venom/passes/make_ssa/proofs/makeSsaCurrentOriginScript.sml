(*
 * MakeSSA (make_ssa_current_fn) only renames: there is a map orig from
 * output variables to input variables under which every output
 * instruction is an input non-PHI with the same id, or comes from a PHI
 * (inserted or carried over, possibly simplified to an ASSIGN or a NOP)
 * that defines a renamed copy of an input variable.
 *)
Theory makeSsaCurrentOrigin
Ancestors
  makeSsaCurrentDefs venomWf cfgWf venomInst irSupply unitShapeDefs
  o1PassContract

Theorem make_ssa_current_fn_origin:
  fn_defs_reach_uses fn /\ fn_phi_operands_single_def fn /\
  fn_phis_cover_preds fn /\
  (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
     inst.inst_opcode = PHI ==>
     ALL_DISTINCT (MAP FST (phi_pairs inst.inst_operands)) /\
     !l v. MEM (l,v) (phi_pairs inst.inst_operands) ==>
       fn_cfg_edge fn l bb.bb_label) /\
  fn_phi_outputs_single_def fn /\ fn_phis_non_degenerate fn /\
  all_reachable fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') ==>
  ?orig.
    !inst'. MEM inst' (fn_insts fn') ==>
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
Proof
  cheat
QED
