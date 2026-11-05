(*
 * Where MakeSSA puts each input instruction: the block of the same label
 * in its output, shifted by the number of instructions the block gained.
 *
 * MakeSSA only prepends PHIs to a block, renames instructions in place
 * and, when its input had PHIs, rearranges the leading PHI prefix into
 * the PHIs that stay PHIs followed by the collapsed ASSIGN/NOP copies.
 * So every instruction from the input's first non-PHI on sits d places
 * later in the output block, d = LENGTH out - LENGTH in, with its opcode,
 * id and output count; and between the output's own PHI prefix and the
 * shifted input prefix there are only ASSIGNs and NOPs.
 *)
Theory makeSsaCurrentLockstepShape
Ancestors
  makeSsaCurrentProps makeSsaCurrentDefs o1PassContract unitShapeDefs
  venomWf venomExecSemantics irSupply venomInst list

Theorem make_ssa_current_fn_block_shape:
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') /\
  lookup_block l fn.fn_blocks = SOME bb ==>
  ?bb'. lookup_block l fn'.fn_blocks = SOME bb' /\
    LENGTH bb.bb_instructions <= LENGTH bb'.bb_instructions /\
    phi_prefix_length bb'.bb_instructions <=
      phi_prefix_length bb.bb_instructions +
      (LENGTH bb'.bb_instructions - LENGTH bb.bb_instructions) /\
    (!j. phi_prefix_length bb'.bb_instructions <= j /\
         j < phi_prefix_length bb.bb_instructions +
             (LENGTH bb'.bb_instructions - LENGTH bb.bb_instructions) ==>
         (EL j bb'.bb_instructions).inst_opcode = ASSIGN \/
         (EL j bb'.bb_instructions).inst_opcode = NOP) /\
    !k. phi_prefix_length bb.bb_instructions <= k /\
        k < LENGTH bb.bb_instructions ==>
        (EL (k + (LENGTH bb'.bb_instructions - LENGTH bb.bb_instructions))
            bb'.bb_instructions).inst_opcode =
          (EL k bb.bb_instructions).inst_opcode /\
        (EL (k + (LENGTH bb'.bb_instructions - LENGTH bb.bb_instructions))
            bb'.bb_instructions).inst_id =
          (EL k bb.bb_instructions).inst_id /\
        LENGTH (EL (k + (LENGTH bb'.bb_instructions -
                         LENGTH bb.bb_instructions))
                   bb'.bb_instructions).inst_outputs =
          LENGTH (EL k bb.bb_instructions).inst_outputs
Proof
  cheat
QED

Theorem make_ssa_current_fn_lookup_block_rev:
  wf_function fn /\ make_ssa_current_fn s fn = (fn',s') /\
  lookup_block l fn'.fn_blocks = SOME bb' ==>
  ?bb. lookup_block l fn.fn_blocks = SOME bb
Proof
  cheat
QED
