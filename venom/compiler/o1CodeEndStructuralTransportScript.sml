Theory o1CodeEndStructuralTransport
Ancestors
  o1CodeEndSimplifyCfgTransport o1CodeEndSueTransport
  o1CodeEndCfgNormTransport list

(* SimplifyCFG alone needs the protected-use invariant.  Keeping the guard
   explicit lets the pipeline join discharge it from its stage4 producer. *)
Theorem code_end_structural_stage_contracts:
  !n. MEM n [5; 6; 8] ==>
    o1_stage_contract rpolicy D (EL n o1_fn_passes)
      (o1_walk_view rpolicy n) (o1_pre n)
      (\C s. o1_inv D n C s /\ code_end_offset_ok (raw_reachable s) C /\
        (n = 5 ==> EVERY (\f. !x i.
          code_end_var f x /\ MEM i (fn_insts f) /\
          MEM (Var x) i.inst_operands ==>
          i.inst_opcode = ASSIGN \/ i.inst_opcode = CODECOPY)
          C.ctx_functions))
      (\C s. o1_inv D (n + 1) C s /\ code_end_offset_ok (raw_reachable s) C /\
        (n = 5 ==> EVERY (\f. !x i.
          code_end_var f x /\ MEM i (fn_insts f) /\
          MEM (Var x) i.inst_operands ==>
          i.inst_opcode = ASSIGN \/ i.inst_opcode = CODECOPY)
          C.ctx_functions))
Proof
  simp[MEM] >> rpt strip_tac >> gvs[] >>
  metis_tac[simplify_cfg_code_end_run_contract,
            sue_code_end_run_contract, cfg_norm_code_end_run_contract]
QED
