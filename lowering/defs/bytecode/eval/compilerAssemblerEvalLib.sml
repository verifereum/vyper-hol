(* TOP-LEVEL: warm_slice. Compose the original fixed-width assembler from
   its checked label offsets and individual instruction encodings. *)
structure compilerAssemblerEvalLib = struct
  open HolKernel boolLib
  fun head name = prim_mk_const {Thy="symbolResolve",Name=name}
  val assemble_head = head "assemble"
  val offsets_head = head "compute_label_offsets"
  val encode_head = head "encode_inst"
  type work = {offsets:thm,remaining:term list}
  val work : (term,work) Redblackmap.dict ref =
    ref (Redblackmap.mkDict Term.compare)
  val encodings : (term,thm) Redblackmap.dict ref =
    ref (Redblackmap.mkDict Term.compare)

  fun encode_result current = let
    val [offsets,instruction] = snd (strip_comb current)
    val symbolic = genvar (type_of offsets)
    val call = list_mk_comb (encode_head,[symbolic,instruction])
    val unfolded = Conv.FIRST_CONV (map Conv.REWR_CONV
      (CONJUNCTS (SPEC_ALL (DB.fetch "symbolResolve" "encode_inst_def")))) call
    val concrete = INST [symbolic |-> offsets] unfolded
    fun lookups expression =
      if finite_mapSyntax.is_flookup expression then
        compilerContextPlannerEvalLib.lookup_result expression
      else if type_of expression = type_of offsets then REFL expression
      else if is_comb expression then Conv.COMB2_CONV (lookups,lookups) expression
      else if is_abs expression then Conv.ABS_CONV lookups expression
      else REFL expression
    val observed = lookups (rhs (concl concrete))
    val result = computeLib.EVAL_CONV (rhs (concl observed))
  in TRANS concrete (TRANS observed result) end

  fun checked_encoding current =
    case Redblackmap.peek (!encodings,current) of
      SOME theorem => theorem
    | NONE => raise Fail "assembler instruction encoding is not prepared"

  fun assemble_result current offsets_eq = let
    val assembly = rand current
    val (pc,offsets) = pairSyntax.dest_pair (rhs (concl offsets_eq))
    val asm_var = genvar (type_of assembly)
    val pc_var = genvar (type_of pc)
    val offsets_var = genvar (type_of offsets)
    val premise = mk_eq (mk_comb (offsets_head,asm_var),
      pairSyntax.mk_pair (pc_var,offsets_var))
    val unfolded = Conv.REWR_CONV (DB.fetch "symbolResolve" "assemble_def")
      (mk_comb (assemble_head,asm_var))
    val selected = simpLib.SIMP_CONV (bossLib.srw_ss ())
      [ASSUME premise,boolTheory.LET_THM] (rhs (concl unfolded))
    val schema = INST [asm_var |-> assembly,pc_var |-> pc,offsets_var |-> offsets]
      (DISCH premise (TRANS unfolded selected))
    val concrete = MP schema offsets_eq
    val mapped = Conv.RAND_CONV (listLib.MAP_CONV checked_encoding)
      (rhs (concl concrete))
    val flattened = computeLib.EVAL_CONV (rhs (concl mapped))
  in TRANS concrete (TRANS mapped flattened) end

  fun assemble_step current goal =
    case Redblackmap.peek (!work,current) of
      NONE => let
        val assembly = rand current
        val (instructions,_) = listSyntax.dest_list assembly
        val offsets = evalCompilerBytecodeLib.timed_evaluation offsets_head
          "assembler label offsets" (fn () => computeLib.EVAL_CONV
            (mk_comb (offsets_head,assembly)))
        val () = work := Redblackmap.insert
          (!work,current,{offsets=offsets,remaining=instructions})
      in Tactical.ALL_TAC goal end
    | SOME {offsets,remaining=[]} =>
        compilerExternalPlannerEvalLib.composed_step
          (fn term => assemble_result term offsets) current goal
    | SOME {offsets,remaining=instruction::rest} => let
        val (_,labels) = pairSyntax.dest_pair (rhs (concl offsets))
        val call = list_mk_comb (encode_head,[labels,instruction])
        val () = case Redblackmap.peek (!encodings,call) of SOME _ => ()
          | NONE => let
              val equation = evalCompilerBytecodeLib.timed_evaluation encode_head
                "assembler instruction encoding" (fn () => encode_result call)
            in encodings := Redblackmap.insert (!encodings,call,equation) end
        val () = work := Redblackmap.insert
          (!work,current,{offsets=offsets,remaining=rest})
      in Tactical.ALL_TAC goal end

  fun warm_step goal =
    case !compilerPlannerEvalLib.pending of
      current::_ => if same_const (fst (strip_comb current)) assemble_head then
          assemble_step current goal
        else compilerAssemblyEvalLib.warm_step goal
    | [] => compilerAssemblyEvalLib.warm_step goal

  fun warm_slice goal = let
    val started = Time.now ()
    fun advance remaining goal =
      if remaining = 0 orelse
          Time.- (Time.now (),started) >= Time.fromReal 0.005 then
        Tactical.ALL_TAC goal
      else Tactical.THEN (warm_step,advance (remaining - 1)) goal
  in advance 8 goal end
end
