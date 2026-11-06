(* The deployment bytecode fits the assembler's 2-byte label pushes.
 * TOP-LEVEL: deploy_bc_size_bounded (admitted until proved).
 * It closes from asm_symbols_ok, which bounds SUM (MAP asm_inst_size asm)
 * below 65536 in codegen_assembly, once the codegen branch's change to
 * codegen_assembly reaches this branch's base.
 *)
Theory ctorDeployInitcodeAsm
Ancestors
  ctorDeployDefs

Theorem deploy_bc_size_bounded:
  !policy tops deploy_bc runtime_bc arts.
    deploy_phases policy tops (deploy_bc, runtime_bc) arts ==>
    LENGTH deploy_bc < 65536
Proof
  cheat
QED
