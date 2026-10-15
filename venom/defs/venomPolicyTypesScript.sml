(*
 * Pipeline-neutral compiler policy types.
 *
 * This theory deliberately sits above Venom IR and code generation.
 *)

Theory venomPolicyTypes

Datatype:
  dispatch_strategy = Linear | Sparse | Dense
End

Datatype:
  evm_capability = CapPush0 | CapMcopy | CapTransientStorage | CapBlobOps
End

Type target_capabilities = ``:evm_capability -> bool``

Definition target_capabilities_wf_def:
  target_capabilities_wf caps <=>
    (caps CapMcopy ==> caps CapPush0) /\
    (caps CapTransientStorage ==> caps CapPush0) /\
    (caps CapBlobOps ==> caps CapPush0)
End

(* Every capability enabled. All four capabilities are Cancun-era features,
   so this target is fork-neutral from Cancun onward. The EVM semantics used
   by the correctness proofs (Verifereum) model Osaka; Osaka's only new opcode
   (CLZ) is not in Venom or the assembler table and has no capability yet. *)
Definition all_capabilities_def:
  all_capabilities = (K T : target_capabilities)
End

Datatype:
  final_assembly_policy = FAP_Preserve | FAP_Optimize
End

Datatype:
  compiler_policy = <| cpol_target : target_capabilities |>
End

Theorem all_capabilities_wf:
  target_capabilities_wf all_capabilities
Proof
  simp [target_capabilities_wf_def, all_capabilities_def]
QED
