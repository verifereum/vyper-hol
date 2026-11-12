Theory o1LowerDloadSuppliedSegmentTransport
Ancestors
  o1LowerDloadSuppliedSegmentExec o1LowerDloadSuppliedSegmentControl
  o1LowerDloadSuppliedSegmentInputs o1LowerDloadSuppliedSegmentEnvironment
  o1LowerDloadScratchExtension o1LowerDloadScratchMemory
  o1LowerDloadJointRangeCopy o1LowerDloadRangeTransport
  o1LowerDloadJointRelation o1LowerDloadOccurrence ptrDiscipline
  o1PassContract memLocDefs codegenRel venomExecSemantics words finite_map list
  unitShapeDefs venomState irSupply lowerDloadDefs o1LowerDloadShared
  o1LowerDloadEnvironment pred_set

Theorem ld_joint_dloadbytes_destination:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = DLOADBYTES /\ inst.inst_operands = [dst;src;sz] /\
  eval_operand dst s = SOME p /\ eval_operand src s = SOME x /\
  eval_operand sz s = SOME z ==>
  ?q. eval_operand dst t = SOME q /\
    (w2n z = 0 \/ (w2n p=w2n q /\ (w2n p+w2n z<=lo \/
       dyn_floor C vs<=w2n p /\ w2n p+w2n z<=dimword (:256))) \/
     (?id b c k j. FLOOKUP sites id = SOME (b,c,k) /\
       j + w2n z <= k /\ w2n p = b+j /\ w2n q = c+j))
Proof
  (* P4a in progress *) cheat
QED

Theorem ld_joint_supply_dloadbytes_transport:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = DLOADBYTES /\ inst.inst_operands = [dst;src;sz] /\
  inst.inst_outputs = [] /\ step_inst fuel C inst s = OK s1 /\
  eval_operand dst s = SOME p /\ eval_operand src s = SOME x /\
  eval_operand sz s = SOME z /\
  fresh_ir_var u = (bv,u1) /\ lower_dload_inst_supply u inst = (es,u') /\
  ~MEM bv (fn_ir_vars fn) /\ dst <> Var bv /\ sz <> Var bv /\
  code_layout_valid t /\
  w2n x + (LENGTH t.vs_code - LENGTH t.vs_data_section) < dimword(:256) ==>
  ?q. eval_operand dst t = SOME q /\
    let t2 = update_var bv (x + n2w (LENGTH t.vs_code - LENGTH t.vs_data_section)) t;
        t3 = write_memory_with_expansion (w2n q)
          (TAKE (w2n z) (DROP (w2n x) t.vs_data_section ++ REPLICATE (w2n z) 0w)) t2
    in LENGTH es = 2 /\ step_inst fuel C' (EL 0 es) t = OK t2 /\
       step_inst fuel C' (EL 1 es) t2 = OK t3 /\
       ld_env_agree sites fn (occurrence_step a HP H inst s1)
         (step_taint inst s s1 tn) s1 t3 /\
       ld_memory_agree sites lo (step_taint inst s s1 tn).t_mem
         s1.vs_memory t3.vs_memory /\
       ld_dyn_agree (dyn_floor C vs) (step_taint inst s s1 tn).t_mem
         s1.vs_memory t3.vs_memory
Proof
  (* P4a in progress *) cheat
QED

Theorem ld_joint_supply_dload_transport:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  inst.inst_opcode = DLOAD /\ inst.inst_operands = [off] /\
  inst.inst_outputs = [out] /\ step_inst fuel C inst s = OK s1 /\
  eval_operand off s = SOME x /\
  fresh_ir_var u = (av,u1) /\ fresh_ir_var u1 = (bv,u2) /\
  lower_dload_inst_supply u inst = (es,u') /\ off <> Var av /\
  ~MEM av (fn_ir_vars fn) /\ ~MEM bv (fn_ir_vars fn) /\
  code_layout_valid t /\
  w2n x + (LENGTH t.vs_code - LENGTH t.vs_data_section) < dimword(:256) /\
  ((FLOOKUP t.vs_allocas (EL 0 es).inst_id = NONE /\ b = t.vs_alloca_next) \/
   FLOOKUP t.vs_allocas (EL 0 es).inst_id = SOME (b,32)) /\
  b+32 < dimword(:256) /\
  ld_joint_geometry sites X1 lo owners /\
  FLOOKUP X1 key = SOME ((EL 0 es).inst_id,b) ==>
  let t1 = update_var av (n2w b)
        (if FLOOKUP t.vs_allocas (EL 0 es).inst_id = NONE then
           t with <|vs_allocas := t.vs_allocas |+ ((EL 0 es).inst_id,(b,32));
                    vs_alloca_next := t.vs_alloca_next+32|>
         else t);
      t2 = update_var bv (x + n2w (LENGTH t.vs_code - LENGTH t.vs_data_section)) t1;
      bs = TAKE 32 (DROP (w2n x) t.vs_data_section ++ REPLICATE 32 0w);
      t3 = write_memory_with_expansion b bs t2;
      t4 = update_var out (word_of_bytes T (0w:bytes32) bs) t3
  in LENGTH es = 4 /\
     step_inst fuel C' (EL 0 es) t = OK t1 /\
     step_inst fuel C' (EL 1 es) t1 = OK t2 /\
     step_inst fuel C' (EL 2 es) t2 = OK t3 /\
     step_inst fuel C' (EL 3 es) t3 = OK t4 /\
     ld_env_agree sites fn (occurrence_step a HP H inst s1)
       (step_taint inst s s1 tn) s1 t4 /\
     ld_memory_agree sites lo (step_taint inst s s1 tn).t_mem
       s1.vs_memory t4.vs_memory /\
     ld_dyn_agree (dyn_floor C vs) (step_taint inst s s1 tn).t_mem
       s1.vs_memory t4.vs_memory
Proof
  (* P4a in progress *) cheat
QED
