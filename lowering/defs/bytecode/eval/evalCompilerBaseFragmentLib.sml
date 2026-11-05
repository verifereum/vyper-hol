(* Run each existing proof phase on a closed query, retaining the surrounding
   compiler goal only once. The final validation yields an ordinary equality;
   its fresh result variable is discharged by reflexivity, not an axiom. *)
structure evalCompilerBaseFragmentLib = struct
open HolKernel Parse boolLib bossLib
open evalCompilerBaseLib

type fragment = {query : term, variable : term, current : goal,
                 validations : validation list}
val base_fragment = ref (NONE : fragment option)

fun base_fragment_open name g = let
  val () = if Option.isSome (!base_fragment) then
      raise Fail "previous Base fragment remains open" else ()
  val query = find_term (flow_call name) (lhs (snd g))
  val () = if List.null (free_vars query) then ()
      else raise Fail "Base fragment query is not closed"
  val variable = genvar (type_of query)
  val current = ([],mk_eq(query,variable))
  val () = base_fragment := SOME
    {query=query,variable=variable,current=current,validations=[]}
in ALL_TAC g end

fun base_fragment_step tactic g ctxt = let
  val {query,variable,current,validations} = valOf (!base_fragment)
  val (goals,validate) = tactic current ctxt
  val next = case goals of [next] => next
    | _ => raise Fail "Base fragment phase must retain one goal"
  val () = if aconv (rhs (snd next)) variable then ()
      else raise Fail "Base fragment result variable changed"
  val () = base_fragment := SOME
    {query=query,variable=variable,current=next,
     validations=validate::validations}
in ALL_TAC g ctxt end

fun base_fragment_finish g = let
  val {query,variable,current,validations} = valOf (!base_fragment)
  val result = lhs (snd current)
  val () = if List.null (fst current) andalso List.null (free_vars result)
      andalso not (aconv result query) then ()
    else raise Fail "Base fragment has unresolved data or no progress"
  val equation = List.foldl (fn (validate,th) => validate [th])
    (ASSUME (snd current)) validations
  val specialized = INST [variable |-> result] equation
  val checked = PROVE_HYP (REFL result) specialized
  val () = if List.null (hyp checked) andalso
      aconv (concl checked) (mk_eq(query,result)) then ()
    else raise Fail "Base fragment equality did not close"
  val () = base_fragment := NONE
in CONV_TAC (LAND_CONV (base_first_conv (aconv query) (K checked))) g end
end
