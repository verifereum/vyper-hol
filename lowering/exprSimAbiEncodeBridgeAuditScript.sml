(* Bounded audit of the frozen counted-path bridge. *)
Theory exprSimAbiEncodeBridgeAudit
Ancestors
  exprSimAbiEncodeEntryControl exprSimAbiGasBridge builtinAbi fragExec

Theorem encode_entry_alias_not_frag_gas_free:
  ~frag_gas_free (enc_entry_alias_owner st) (enc_entry_alias_final st)
Proof
  simp[frag_gas_free_def, emitted_blocks_def,
    enc_entry_alias_owner_def, encode_entry_exit_alias_position,
    encode_entry_exit_alias_blocks] >> EVAL_TAC
QED

(* Whole wrapper: allocation and final length store do not reserve labels. *)
Definition enc_audit_owner_def:
  enc_audit_owner st = st with
    <|cs_next_var := 0; cs_next_id := 0; cs_next_label := 0;
      cs_blocks := []; cs_current_bb := fresh_label_output "enc_dyn_exit" 2;
      cs_current_insts := []|>
End

Definition enc_audit_final_def:
  enc_audit_final st = SND
    (lower_abi_encode F NONE (Lit 0w)
      (AbiDynArray AbiPrimWord 32 32 F) 64 (enc_audit_owner st))
End

Theorem encode_wrapper_alias_not_frag_gas_free:
  ~frag_gas_free (enc_audit_owner st) (enc_audit_final st)
Proof
  EVAL_TAC
QED

Definition enc_audit_embedded_owner_def:
  enc_audit_embedded_owner st = enc_audit_owner st with
    cs_current_insts := (enc_audit_final ARB).cs_current_insts
End

Definition enc_audit_embedded_final_def:
  enc_audit_embedded_final st = SND
    (lower_abi_encode F NONE (Lit 0w)
      (AbiDynArray AbiPrimWord 32 32 F) 64 (enc_audit_embedded_owner st))
End

Definition enc_audit_func_def:
  enc_audit_func st fn = fn with fn_blocks :=
    emitted_blocks (enc_audit_embedded_owner st) (enc_audit_embedded_final st)
End

Theorem encode_wrapper_embedded_alias:
  fn_has_code (enc_audit_embedded_owner st) (enc_audit_embedded_final st)
    (enc_audit_func st fn) /\
  fn_inst_ids_distinct (enc_audit_func st fn) /\
  ~frag_gas_free (enc_audit_embedded_owner st) (enc_audit_embedded_final st)
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem encode_wrapper_alias_final_label:
  (enc_audit_embedded_final st).cs_current_bb =
    (enc_audit_embedded_owner st).cs_current_bb /\
  MEM (enc_audit_embedded_final st).cs_current_bb
    (MAP (\bb. bb.bb_label)
      (emitted_blocks (enc_audit_embedded_owner st) (enc_audit_embedded_final st)))
Proof
  EVAL_TAC
QED

(* Bridge-premise ledger (exprSimAbiGasBridge, lines 66--88):
   sa/sb are the states before/after lower_abi_encode, not only an inner loop.

   - cs_extends: compiler shape obligation, independent of label freshness.
   - frag_gas_free: NOT universally supplyable.  The whole-wrapper witness
     above has exact fn_has_code and distinct instruction IDs, yet its final
     label is an emitted block label.  Allocation/ADD and the final length
     MSTORE do not prevent this.  The separate no-Label-sa operand requirement
     also must be supplied; opcode-freedom alone is insufficient.
   - uniform fn' premise: requires an encoder result for EVERY fn' satisfying
     exact code embedding, distinct IDs, non-STOP instruction inclusion in fn,
     and the endpoint PHI condition.  Each such application must supply its
     own resource/registration hypotheses, not assume fn'=fn.  The exported
     window_strong_result includes abi_encoder_extend_sim, whose definition
     contains abi_decode_sim and variable-extension stability, not a path.
   - Q returndata stability: must be proved for the selected postcondition;
     the bridge does not provide it from an arbitrary encoder postcondition.
   - fn_has_code / distinct IDs for fn: available at the expression boundary;
     neither implies frag_gas_free (checked above).
   - endpoint PHI condition: requires equal block lists, a nonempty final
     instruction list, or a PHI-free endpoint block.  The wrapper's final
     MSTORE gives a nonempty list, but fn' still requires PHI-freedom when
     blocks differ.
   - initial nonhaltedness and PC: ordinary operand endpoint obligations.

   frag_exec_gas_path instead needs frag_exec, the SAME frag_gas_free,
   cs_extends, returndata stability, a no-Halt exit predicate, exact embedding,
   endpoint PHI alternative, and P/PC/nonhaltedness.  It does not avoid this
   witness, and abi_decode_sim is not itself frag_exec.

   Missing interface: a counted-path encoder result applicable in the actual
   function without the two alias exclusions of frag_gas_free (or an actual-
   function finite execution trace from which that path follows).  No such
   replacement is proved here, in accordance with TASK's frozen-contract rule.
   These are counterexamples to unconditional bridge-premise supplyability,
   NOT counterexamples to compile_abi_encode_case.
 *)
