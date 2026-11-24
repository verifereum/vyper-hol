(* Selected grouped route, retaining the two concrete early-exit obligations. *)
Theory entryCreateGroupedDefaultRoute
Ancestors
  groupedDefaultCallRoute

Theorem grouped_default_selected_route_cases:
  ^(concl grouped_default_route_elim)
Proof
  ACCEPT_TAC grouped_default_route_elim
QED
