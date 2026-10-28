(* Select instruction-tail metadata before inserting large literal payloads. *)
structure compilerPlanMetadataEvalLib = struct
  open HolKernel boolLib

  fun cached expression = List.exists
    (fn theorem => aconv expression (lhs (concl theorem)))
    (!compilerInstructionPlannerEvalLib.argument_certificates)

  fun remember expression theorem =
    if aconv expression (lhs (concl theorem)) then
      compilerTraversalPlannerEvalLib.remember theorem
    else raise Fail "instruction metadata control did not match its original term"

  fun prepare_liveness checked expression rest = if cached expression then () else let
    val (_,yes,no) = boolSyntax.dest_cond expression
    val yes_variable = genvar (type_of yes)
    val no_variable = genvar (type_of no)
    val empty_list = listSyntax.mk_list ([],listSyntax.dest_list_type (type_of rest))
    val (small_rest,replacements) = if listSyntax.is_nil rest then (empty_list,[])
      else let
        val (next,tail) = listSyntax.dest_cons rest
        val next_variable = genvar (type_of next)
        val tail_variable = genvar (type_of tail)
      in (listSyntax.mk_cons (next_variable,tail_variable),
          [next_variable |-> next,tail_variable |-> tail]) end
    val small = boolSyntax.mk_cond
      (mk_eq (small_rest,empty_list),yes_variable,no_variable)
    val selected = INST
      ((yes_variable |-> yes) :: (no_variable |-> no) :: replacements)
      (computeLib.EVAL_CONV small)
    val () = if aconv expression (lhs (concl selected)) then ()
      else raise Fail "unrecognized instruction liveness conditional"
    val result = checked (rhs (concl selected))
  in remember expression (TRANS selected result) end

  fun prepare_terminator expression rest = if cached expression then () else let
    val (operator,arguments) = strip_comb expression
    val () = if length arguments = 3 andalso aconv (hd arguments) rest then ()
      else raise Fail "unrecognized instruction terminator case"
    val (small_rest,replacements) = if listSyntax.is_nil rest then (rest,[])
      else let
        val (next,tail) = listSyntax.dest_cons rest
        val variable = genvar (type_of tail)
      in (listSyntax.mk_cons (next,variable),[variable |-> tail]) end
    val small = boolSyntax.list_mk_icomb (operator,small_rest :: tl arguments)
    val result = INST replacements (computeLib.EVAL_CONV small)
  in remember expression result end
end
