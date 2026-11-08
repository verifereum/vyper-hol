(* Input conditions for allocation-free internal-call inlining.
   Calls and scalar memory effects remain supported. Allocation relocation
   requires a separate contract for the larger target frame footprint. *)
Theory functionInlinerContract
Ancestors
  functionInlinerDefs callLayoutDefs unitShapeDefs fcgDefs
  venomWf venomInst list relation words

Definition inliner_input_ok_def:
  inliner_input_ok ctx <=>
    ctx_wf ctx /\ wf_invoke_targets ctx /\
    EVERY (\fn.
      wf_function fn /\ fn_inst_wf fn /\
      canonical_param_prefix fn /\ opaque_use_ok fn /\ retpc_shape_ok fn /\
      first_block_no_preds fn /\
      LENGTH (fn_entry_insts fn) < dimword (:256) /\
      ~isPREFIX "inl" fn.fn_name /\
      EVERY (\bb. ~isPREFIX "inl" bb.bb_label) fn.fn_blocks /\
      EVERY (\inst.
        ~MEM inst.inst_opcode [ALLOCA; DALLOCA; DRET; SETFMP] /\
        label_positions_ok inst /\
        EVERY (\v. ~isPREFIX "inl" v) inst.inst_outputs /\
        EVERY (\op. case op of Var v => ~isPREFIX "inl" v | _ => T)
          inst.inst_operands /\
        (inst.inst_opcode = INVOKE ==>
          ALL_DISTINCT inst.inst_outputs /\
          EVERY (\op. !v. op = Var v ==> ~MEM v inst.inst_outputs)
            (TL inst.inst_operands)))
        (fn_insts fn)) ctx.ctx_functions /\
    (!fn other. MEM fn ctx.ctx_functions /\ MEM other ctx.ctx_functions /\
       fn.fn_name <> other.fn_name ==>
       ~MEM other.fn_name (fn_labels fn)) /\
    (!entry fn inst args.
       ctx.ctx_entry = SOME entry /\ MEM fn ctx.ctx_functions /\
       MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE ==>
       inst.inst_operands <> Label entry::args) /\
    (?rank : string -> num.
       !caller callee.
         MEM callee (fcg_get_callees (fcg_analyze ctx) caller) ==>
         rank callee < rank caller)
End
