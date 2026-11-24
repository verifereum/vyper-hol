(* Shared statement syntax for a registration rule with a layout witness. *)
structure groupedEndpointIntroLib =
struct
open HolKernel boolLib bossLib
open compileEnvTheory groupedRuntimeEndpointTheory

val (registered_inputs,registered_endpoint) =
  boolSyntax.dest_imp (concl (SPEC_ALL grouped_registered_body_endpoint));
val (endpoint_const,endpoint_args) = strip_comb registered_endpoint;
val registered_vars = free_vars registered_inputs;
fun named_var name =
  valOf (List.find (fn v => fst (dest_var v) = name) registered_vars);
val start = named_var "sa";
val finish = named_var "final";

val layout = ``\a b. cs_extends a b /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks b))``;
val D = mk_var ("D", type_of layout);
val E = mk_var ("E", type_of endpoint_const);

fun intro d e =
  let
    val premise = boolSyntax.mk_conj
      (registered_inputs, list_mk_comb (d,[start,finish]));
    val result = list_mk_comb (e,endpoint_args);
  in
    boolSyntax.list_mk_forall
      (registered_vars, boolSyntax.mk_imp (premise,result))
  end;
end
