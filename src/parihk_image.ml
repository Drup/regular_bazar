
module PB = struct
  
  type var = V of string
  
  type 'a t =
    | And : bool t list -> bool t
    | Or : bool t list -> bool t
    | Equal : int t * int t -> bool t
    | Less : int t * int t -> bool t
    | Var : var -> int t
    | Exist : var list * 'a t -> 'a t
    | Int : int -> int t
    | Sum : int t list -> int t

  let flatten_with f l =
    let rec aux acc = function
      | [] -> List.rev acc
      | h :: t ->
        match f h with
        | Some l -> aux (l@acc) t
        | None -> aux (h::acc) t
    in
    aux [] l
  
  let andl = function
    | [x] -> x
    | l -> And (flatten_with (function And l -> Some l | _ -> None) l)
  let ands l = andl @@ OSeq.to_list l
  let orl = function
    | [x] -> x
    | l -> Or (flatten_with (function Or l -> Some l | _ -> None) l)
  let ors l = orl @@ OSeq.to_list l
  let suml = function
    | [] -> Int 0
    | [x] -> x
    | l -> Sum (flatten_with (function Sum l -> Some l | _ -> None) l)
  let sums l = suml @@ OSeq.to_list l
  let equal a b = Equal (a, b)
  let less a b = Less (a, b)
  
  let i x = Int x
  let var =
    let r = ref 0 in
    fun s -> V (Fmt.str "%s%i" s (CCRef.get_then_incr r))
  let varf fmt = Fmt.kstr var fmt
  let vars f it = Iter.map (fun s -> var @@ f s) it
  let exist ~base f = let v = var base in Exist ([v], f v)
  let exists f seq0 k =
    let rec aux vars seq = match seq () with
      | Seq.Nil ->
        let l = List.map snd vars in
        Exist (l, k @@ OSeq.of_list @@ List.map (fun (x,v) -> (x, Var v)) vars)
      | Cons (x, seq) ->
        let base = f x in
        let v = var base in
        aux ((x,v)::vars) seq
    in
    aux [] seq0

  module FV = CCSet.Make(String)
  let rec free_vars : type a. a t -> FV.t = function
    | Var V v -> FV.singleton v
    | Int _ -> FV.empty
    | Exist (l, f) ->
      List.fold_left (fun fv (V v) -> FV.remove v fv) (free_vars f) l
    | Equal (f1, f2) | Less (f1, f2) ->
      FV.union (free_vars f1) (free_vars f2)
    | And l | Or l ->
      List.fold_left (fun fv f -> FV.union fv @@ free_vars f) FV.empty l
     | Sum l ->
      List.fold_left (fun fv f -> FV.union fv @@ free_vars f) FV.empty l
  
  let rec pp : type a . a t Fmt.t = fun fmt -> function
    | And l -> Fmt.pf fmt "@[(and %a)@]" Fmt.(list ~sep:(any "@ ") pp_parens) l
    | Or l -> Fmt.pf fmt "@[(or %a)@]" Fmt.(list ~sep:(any "@ ") pp_parens) l
    | Sum l -> Fmt.pf fmt "@[(+ %a)@]" Fmt.(list ~sep:(any "@ ") pp_parens) l
    | Var V v -> Fmt.pf fmt "%s" v
    | Int i -> Fmt.int fmt i
    | Equal (x,y) -> Fmt.pf fmt "(= %a %a)" pp_parens x pp_parens y
    | Less (x,y) -> Fmt.pf fmt "(< %a %a)" pp_parens x pp_parens y
    | Exist (l, f) ->
      let decl fmt (V v) = Fmt.pf fmt "(%s Int)" v in
      Fmt.pf fmt "@[<2>(exists (%a)@ %a)@]"
        (Fmt.list ~sep:Fmt.sp decl) l pp_parens f
      
  and pp_parens : type a . a t Fmt.t = fun fmt x -> match x with
    | Int _ | Var _ | Exist _ -> pp fmt x
    | _ -> pp fmt x

  let dump fmt f =
    FV.iter (fun s ->
        Fmt.pf fmt "(declare-const %s Int)@." s
      ) (free_vars f);
    Fmt.pf fmt "@[(assert@ %a)@]" pp f
  
  module Op = struct
    let (&&@) a b = andl [a;b]
    let (||@) a b = orl [a;b]
    let (+@) a b = suml [a;b]
    let (=@) a b = Equal (a,b)
    let (<@) a b = Less (a,b)
  end
end

open PB.Op


let consistent_flow (nfa: Nfa.t) z_vars transition_vars =
  let z_constraints = 
    let z_vars_final, z_vars_nonfinal =
      z_vars
      |> OSeq.to_list
      |> List.partition (fun (st,_) -> Nfa.is_final nfa st)
      (* OSeq.partition (fun (st,_) -> Nfa.is_final nfa st) z_vars *)
    in
    let sum_vars l = PB.suml (List.map snd l) in
    (sum_vars z_vars_final =@ PB.i 1) &&@
    (sum_vars z_vars_nonfinal =@ PB.i 0) &&@
    PB.ands @@ OSeq.map (fun (_,x) -> (PB.i 0 =@ x) ||@ (x =@ PB.i 1)) z_vars
  in

  let in_tbl = Hashtbl.create 17 in
  let out_tbl = Hashtbl.create 17 in
  OSeq.iter (fun ((p,_a,q), x_paq) ->
      CCHashtbl.add_list in_tbl q x_paq;
      CCHashtbl.add_list out_tbl p x_paq;
    )
    transition_vars;
  let flow_formula =
    z_vars
    |> OSeq.map (fun (st, z_var) ->
        let inv = PB.suml @@ CCHashtbl.get_or ~default:[] in_tbl st in
        let outv = PB.suml @@ CCHashtbl.get_or ~default:[] out_tbl st in
        if Nfa.is_initial nfa st then
          inv =@ outv +@ z_var +@ (PB.i ~-1)
        else
          inv =@ outv +@ z_var
      )
    |> PB.ands
  in
  flow_formula &&@ z_constraints

let connected_flow (nfa: Nfa.t) u_vars transition_vars =
  let get_u_var =
    let u_tbl = CCHashtbl.of_seq u_vars in
    fun k -> Hashtbl.find u_tbl k
  in
  let pos_u_formula =
    u_vars
    |> OSeq.map (fun (st, u_var) ->
        if Nfa.is_initial nfa st then
          PB.i 0 =@ u_var
        else
          PB.i 0 <@ u_var
      )
    |> PB.ands
  in
  let connected_formula =
    transition_vars
    |> OSeq.map (fun ((p, _a, q), x_paq) ->
        let u_p = get_u_var p and u_q = get_u_var q in
        (x_paq =@ PB.i 0) ||@ (u_p <@ u_q) ||@ (u_q <@ u_p)
      )
    |> PB.ands
  in
  pos_u_formula &&@ connected_formula

let make (nfa: Nfa.t) =
  PB.exists (fun _ -> "x") (Nfa.transitions nfa) @@ fun transition_vars ->
  PB.exists
    (fun st -> Fmt.str "z%i-" @@ Nfa.State.id st) (Nfa.states nfa)
  @@ fun z_vars ->
  PB.exists
    (fun st -> Fmt.str "u%i-" @@ Nfa.State.id st) (Nfa.states nfa)
  @@ fun u_vars ->
  let def_semilinear =
    let by_letters =
      OSeq.group_by (module Atom) ~project:(fun ((_,c,_),_) -> c) transition_vars
    in
    let (let+) x f = OSeq.map f x in
    let conj = 
      let+ (a, tr_vars_a) = by_letters in
      let v_a = PB.varf "%a" Atom.pp a in
      let sum_a =
        List.map (fun (_,v) -> v) tr_vars_a
      in
      (Var v_a =@ PB.suml sum_a) &&@
      (PB.i (-1) <@ PB.Var v_a)
    in
    PB.ands conj
  in
  consistent_flow nfa z_vars transition_vars &&@
  connected_flow nfa u_vars transition_vars &&@
  def_semilinear

let test re =
  let re = Parser.parse re in
  let a = Antimirrov_deriv.make re in
  Fmt.epr "Automaton:@.%a@." Nfa.pp a;
  let f = make a in
  Fmt.epr "Formula:@.%a@." PB.dump f;
  Nfa.dot a;
  a, f
