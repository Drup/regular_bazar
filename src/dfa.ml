module State : sig
  type t
  val pp : t Fmt.t
  val gen : unit -> t
  val compare : t -> t -> int
  val id : t -> int
end = struct
  type t = int
  let pp fmt x = Fmt.pf fmt "'%i" x
  let gen =
    let r = ref 0 in
    fun () ->
      incr r ;
      !r
  let compare = CCInt.compare
  let id x = x
end
module StateMap = CCMap.Make(State)
module StateSet = CCSet.Make(State)

type t = {
  states : StateSet.t ;
  initial : State.t ;
  transitions : transition StateMap.t ;
  final : StateSet.t ;
}
and transition = State.t Atom.Map.t

let add_state a s = { a with states = StateSet.add s a.states }
let new_state a =
  let s = State.gen () in
  add_state a s, s

let add_transition a st (c,st') =
  let transitions =
    StateMap.update st (fun x ->
        let t = CCOption.get_or x ~default:Atom.Map.empty in
        Some (Atom.Map.add c st' t))
      a.transitions
  in
  { a with transitions }

let create () = 
  let st = State.gen () in
  let a =
    let initial = st in
    let states = StateSet.singleton initial in
    let transitions = StateMap.empty in
    let final = StateSet.empty in
    { states ; initial ; transitions ; final }
  in
  a, st

let pp ppf { initial; states; transitions; final; _ } =
  let pp_trans ppf code next =
    Fmt.pf ppf "%c → %a@," code State.pp next
  in
  let pp_transtbl ppf st =
    let transtbl = StateMap.get st transitions in
    Fmt.pf ppf "@[<v2>%a:%s %s@ "
      State.pp st
      (if st = initial then " start" else "")
      (if StateSet.mem st final then "end" else "")
    ;
    CCOption.iter (Atom.Map.iter (pp_trans ppf)) transtbl;
    Fmt.pf ppf "@]@,"
  in 
  let pp fmt a =
    StateSet.iter (fun i -> pp_transtbl fmt i) a
  in
  Fmt.pf ppf "@ @[<v>%a@]" pp states
[@@ocaml.toplevel_printer]
