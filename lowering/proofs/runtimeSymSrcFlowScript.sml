Theory runtimeSymSrcFlow
Ancestors
  codegenSymRel

(* Without a labelled seed, copying cannot create a code_end pointer. *)
Theorem code_end_var_has_seed:
  !fn x. code_end_var fn x ==>
    ?inst. MEM inst (fn_insts fn) /\
           MEM (Label "code_end") inst.inst_operands
Proof
  Induct_on `code_end_var` >> rpt strip_tac >>
  metis_tac[listTheory.MEM]
QED

Theorem code_end_var_seed_free:
  (!inst. MEM inst (fn_insts fn) ==>
          ~MEM (Label "code_end") inst.inst_operands) ==>
  ~code_end_var fn x
Proof
  metis_tac[code_end_var_has_seed]
QED

Theorem label_flow_ok_seed_free:
  (!fn inst. MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) ==>
    ~MEM (Label "code_end") inst.inst_operands /\
    inst.inst_opcode <> CODESIZE /\
    (inst.inst_opcode = CODECOPY ==>
     ?dst sz. inst.inst_operands = [dst; Label "runtime_begin"; sz])) ==>
  label_flow_ok ctx
Proof
  rw[codegenSymRelTheory.label_flow_ok_def] >>
  metis_tac[code_end_var_seed_free]
QED
