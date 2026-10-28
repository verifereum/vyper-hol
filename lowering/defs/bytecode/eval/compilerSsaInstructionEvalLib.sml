(* TOP-LEVEL: configure. Compose instruction renaming from checked operand
   and output results while keeping the supply and rename state opaque. *)
structure compilerSsaInstructionEvalLib = struct
  open HolKernel boolLib
  fun head name = prim_mk_const {Thy="makeSsaCurrentDefs",Name=name}
  val inst_head = head "rename_current_inst"
  val outputs_head = head "rename_current_outputs"
  val operands_head = head "rename_current_operands"
  val children_head = head "rename_current_children"
  val blocks_head = head "rename_current_blocks"
  val insts_head = head "rename_current_block_insts"
  fun call operator args = boolSyntax.list_mk_icomb (operator,args)
  fun field value name = Parse.Term [QUOTE "(",ANTIQUOTE value,QUOTE (")." ^ name)]

  fun inst_result current = let
    val [supply,state,inst] = snd (strip_comb current)
    val supply_var = genvar (type_of supply)
    val state_var = genvar (type_of state)
    val inst_var = genvar (type_of inst)
    val opcode = computeLib.EVAL_CONV (field inst "inst_opcode")
    val outputs = computeLib.EVAL_CONV (field inst "inst_outputs")
    val output_result = compilerPassEvalLib.checked_call
      (call outputs_head [supply,state,rhs (concl outputs)])
    val (next_state,tail) = pairSyntax.dest_pair (rhs (concl output_result))
    val (next_supply,next_outputs) = pairSyntax.dest_pair tail
    val next_state_var = genvar (type_of next_state)
    val next_supply_var = genvar (type_of next_supply)
    val next_outputs_var = genvar (type_of next_outputs)
    val output_value = pairSyntax.mk_pair (next_state_var,
      pairSyntax.mk_pair (next_supply_var,next_outputs_var))
    val premises = [mk_eq (field inst_var "inst_opcode",rhs (concl opcode)),
      mk_eq (field inst_var "inst_outputs",rhs (concl outputs)),
      mk_eq (call outputs_head [supply_var,state_var,rhs (concl outputs)],output_value)]
    val facts = [opcode,outputs,output_result]
    val replacements = [supply_var |-> supply,state_var |-> state,inst_var |-> inst,
      next_state_var |-> next_state,next_supply_var |-> next_supply,
      next_outputs_var |-> next_outputs]
    val phi = prim_mk_const {Thy="venomInst",Name="PHI"}
    val (premises,facts,replacements) =
      if same_const (rhs (concl opcode)) phi then (premises,facts,replacements)
      else let
        val operands = computeLib.EVAL_CONV (field inst "inst_operands")
        val renamed = compilerPassEvalLib.checked_call
          (call operands_head [state,rhs (concl operands)])
        val operands_var = genvar (type_of (rhs (concl renamed)))
      in (premises @ [mk_eq (field inst_var "inst_operands",rhs (concl operands)),
            mk_eq (call operands_head [state_var,rhs (concl operands)],operands_var)],
          facts @ [operands,renamed],
          replacements @ [operands_var |-> rhs (concl renamed)]) end
    val schema = simpLib.SIMP_CONV (bossLib.srw_ss ())
      (DB.fetch "makeSsaCurrentDefs" "rename_current_inst_def" ::
       boolTheory.LET_THM :: pairTheory.pair_case_thm :: map ASSUME premises)
      (call inst_head [supply_var,state_var,inst_var])
    val guarded = List.foldr (fn (p,th) => DISCH p th) schema premises
    val concrete = INST replacements guarded
    val composed = List.foldl (fn (fact,th) => MP th fact) concrete facts
    val updated = Conv.RAND_CONV (Conv.RAND_CONV computeLib.EVAL_CONV)
      (rhs (concl composed))
  in TRANS composed updated end

  fun children_result current = let
    val clauses = CONJUNCTS (SPEC_ALL
      (DB.fetch "makeSsaCurrentDefs" "rename_current_blocks_def"))
    val [supply,counters,stacks,blocks,successors,children] = snd (strip_comb current)
  in if listSyntax.is_nil children then Conv.REWR_CONV (List.nth (clauses,1)) current
    else let
      val (child,rest) = listSyntax.dest_cons children
      val block_result = compilerPassEvalLib.checked_call
        (call blocks_head [supply,pairSyntax.mk_pair (counters,stacks),
          blocks,successors,child])
      val (next_counters,tail) = pairSyntax.dest_pair (rhs (concl block_result))
      val (next_supply,next_blocks) = pairSyntax.dest_pair tail
      val values = [supply,counters,stacks,blocks,successors,child,rest,
        next_counters,next_supply,next_blocks]
      val variables = map (genvar o type_of) values
      val [sv,cv,tv,bv,mv,chv,rv,ncv,nsv,nbv] = variables
      val premise = mk_eq
        (call blocks_head [sv,pairSyntax.mk_pair (cv,tv),bv,mv,chv],
         pairSyntax.mk_pair (ncv,pairSyntax.mk_pair (nsv,nbv)))
      val source = call children_head [sv,cv,tv,bv,mv,listSyntax.mk_cons (chv,rv)]
      val unfolded = Conv.REWR_CONV (List.nth (clauses,2)) source
      val selected = simpLib.SIMP_CONV (bossLib.srw_ss ())
        [ASSUME premise,boolTheory.LET_THM,pairTheory.pair_case_thm]
        (rhs (concl unfolded))
      val concrete = INST (ListPair.map (fn (v,x) => v |-> x) (variables,values))
        (DISCH premise (TRANS unfolded selected))
      val composed = MP concrete block_result
      val remaining = compilerPassEvalLib.checked_call (rhs (concl composed))
    in TRANS composed remaining end
  end

  fun insts_result current = let
    val clauses = CONJUNCTS (SPEC_ALL
      (DB.fetch "makeSsaCurrentDefs" "rename_current_block_insts_def"))
    val [supply,state,instructions] = snd (strip_comb current)
  in if listSyntax.is_nil instructions then Conv.REWR_CONV (hd clauses) current
    else let
      val (inst,rest) = listSyntax.dest_cons instructions
      val first = compilerPassEvalLib.checked_call (call inst_head [supply,state,inst])
      val (state1,tail1) = pairSyntax.dest_pair (rhs (concl first))
      val (supply1,inst1) = pairSyntax.dest_pair tail1
      val remaining = compilerPassEvalLib.checked_call
        (call insts_head [supply1,state1,rest])
      val (state2,tail2) = pairSyntax.dest_pair (rhs (concl remaining))
      val (supply2,rest2) = pairSyntax.dest_pair tail2
      val values = [supply,state,inst,rest,state1,supply1,inst1,state2,supply2,rest2]
      val variables = map (genvar o type_of) values
      val [sv,rv,iv,tv,r1v,s1v,i1v,r2v,s2v,t2v] = variables
      val premises = [mk_eq (call inst_head [sv,rv,iv],
          pairSyntax.mk_pair (r1v,pairSyntax.mk_pair (s1v,i1v))),
        mk_eq (call insts_head [s1v,r1v,tv],
          pairSyntax.mk_pair (r2v,pairSyntax.mk_pair (s2v,t2v)))]
      val unfolded = Conv.REWR_CONV (List.nth (clauses,1))
        (call insts_head [sv,rv,listSyntax.mk_cons (iv,tv)])
      val selected = simpLib.SIMP_CONV (bossLib.srw_ss ())
        (boolTheory.LET_THM :: pairTheory.pair_case_thm :: map ASSUME premises)
        (rhs (concl unfolded))
      val guarded = List.foldr (fn (p,th) => DISCH p th)
        (TRANS unfolded selected) premises
      val concrete = INST (ListPair.map (fn (v,x) => v |-> x) (variables,values)) guarded
    in MP (MP concrete first) remaining end
  end

  fun warm_step goal =
    (case !compilerPassEvalLib.pending of
      current::_ => if List.exists (same_const (fst (strip_comb current)))
          [children_head,insts_head] then let
        val operator = fst (strip_comb current)
        val certificate = evalCompilerBytecodeLib.timed_evaluation operator
          "checked SSA traversal composition"
          (fn () => if same_const operator children_head then children_result current
            else insts_result current)
        val () = if aconv (lhs (concl certificate)) current then ()
          else raise Fail "SSA child traversal changed its original call"
        val () = evalCompilerBytecodeLib.register_compile_eval certificate
        val () = compilerPassEvalLib.equations := Redblackmap.insert
          (!compilerPassEvalLib.equations,current,certificate)
        val () = evalCompilerBytecodeLib.pending_stage_values :=
          (NONE,certificate) :: !evalCompilerBytecodeLib.pending_stage_values
        val () = compilerPassEvalLib.pending := tl (!compilerPassEvalLib.pending)
      in Tactical.ALL_TAC goal end
      else compilerSupplyInputsEvalLib.warm_step goal
    | [] => compilerSupplyInputsEvalLib.warm_step goal)
    handle evalCompilerBytecodeLib.PlannerBoundary child =>
      (compilerPassEvalLib.pending := child :: !compilerPassEvalLib.pending;
       Tactical.ALL_TAC goal)

  fun configure () = let
    val entries = [(outputs_head,3),(operands_head,2)]
    val () = compilerPassEvalLib.extend_phases entries
      [(inst_head,inst_result)] [(inst_head,[outputs_head,operands_head])]
  in app compilerPassEvalLib.install_indexed_head entries end
end
