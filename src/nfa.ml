(** Non-Deterministic Finite Automatons without ε-transitions *)

(* Partially stolen from https://github.com/yallop/ocaml-re-nfa *)

module State = Enfa.State
module StateMap = Enfa.StateMap
module StateSet = Enfa.StateSet

type t = {
  states : StateSet.t ;
  initial : State.t ;
  transitions : transition StateMap.t ;
  final : StateSet.t ;
}
and transition = StateSet.t Atom.Map.t

let add_state a s = { a with states = StateSet.add s a.states }
let new_state a name =
  let s = State.gen name in
  add_state a s, s

let add_transition a st (c,st') =
  let a = add_state (add_state a st) st' in
  let transitions =
    StateMap.update st (fun x ->
        let t = CCOption.get_or x ~default:Atom.Map.empty in
        let f = function
          | None -> Some (StateSet.singleton st')
          | Some sts -> Some (StateSet.add st' sts)
        in
        Some (Atom.Map.update c f t))
      a.transitions
  in
  { a with transitions }

let create init_name = 
  let st = State.gen init_name in
  let a =
    let initial = st in
    let states = StateSet.singleton initial in
    let transitions = StateMap.empty in
    let final = StateSet.empty in
    { states ; initial ; transitions ; final }
  in
  a, st

let cardinal nfa = StateSet.cardinal nfa.states

let is_initial nfa state = State.compare state nfa.initial = 0

let is_final nfa state = StateSet.mem state nfa.final

let states nfa = StateSet.to_seq nfa.states

let transitions nfa = 
  StateMap.to_seq nfa.transitions
  |> OSeq.flat_map (fun (p, tr) ->
      Atom.Map.to_seq tr
      |> OSeq.flat_map (fun (c, qs) -> 
          StateSet.to_seq qs
          |> OSeq.map (fun q -> (p, c, q))
        )
    )

(** Conversion *)

let filter_alphabet f { states ; initial ; transitions ; final } =
  let transitions =
    transitions
    |> StateMap.map (fun t ->
        t
        |> Atom.Map.to_seq
        |> Seq.map (fun (c, x) ->
            let c' = if f c then Atom.Eps.A c else Atom.Eps.Eps in
            (c', x))
        |> Atom.EpsMap.of_seq
      )
  in    
  {Enfa. states ; initial ; transitions ; final }

let as_enfa a = filter_alphabet (fun _ -> true) a

(** Exports *)

let pp ppf a =
  Enfa.pp ppf (as_enfa a)
[@@ocaml.toplevel_printer]

let dot a = Enfa.Dot.open_digraph @@ Enfa.Dot.digraph @@ as_enfa a

