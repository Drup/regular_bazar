(** Antimirov derivatives, aka partial derivatives

    Based on 
    *Partial derivatives of an extended regular expression*
    Pascal Caron, Jean-Marc Champarnaud, Ludovic Mignot

    Shuffling:
    *Partial Derivative Automaton for Regular Expressions with Shuffle*
    by Sabine Broda, António Machiavelo, Nelma Moreira, and Rogério Reis
*)

open Regex.Infix

(** Maps to a union of intersection of regexs *)
type deriv = Regex.SetSet.t Atom.Map.t

let rec has_epsilon = function
  | Regex.Epsilon -> true
  | Atom _ -> false
  | Concat el ->
    List.for_all has_epsilon el
  | Alt el ->
    Regex.Set.exists has_epsilon el
  | Rep (0, _, _) -> true
  | Rep (_, _, _) -> false
  | Inter el ->
    Regex.Set.for_all has_epsilon el
  | Shuffle (e1, e2) -> has_epsilon e1 && has_epsilon e2


let apply (l : deriv) f : deriv =
  let f ures =
    Regex.SetSet.map (fun ires ->
        let re =
          f @@ Regex.inter @@ Regex.Set.to_list ires
        in
        Regex.Set.singleton re)
      ures
  in
  Atom.Map.map f l

let suffix (l : deriv) re0 : deriv =
  apply l @@ fun r -> Regex.concat [r; re0]

let union : deriv -> deriv -> deriv =
  Atom.Map.union
    (fun _c res1 res2 -> Some (Regex.SetSet.union res1 res2))

let inter : deriv -> deriv -> deriv =
  Atom.Map.merge @@ fun _c res1 res2 -> match res1, res2 with
  | Some res1, Some res2 ->
    OSeq.product
      (Regex.SetSet.to_seq res1)
      (Regex.SetSet.to_seq res2)
    |> OSeq.map (fun (x,y) -> Regex.Set.union x y)
    |> Regex.SetSet.of_seq
    |> CCOption.some
  | Some _, None | None, Some _ -> Some (Regex.SetSet.empty)
  | None, None -> None

let shuffleR (l: deriv) reR : deriv =
  apply l @@ fun r -> r %%% reR

let shuffleL reL (l: deriv) : deriv =
  apply l @@ fun r -> reL %%% r  

let rec deriv : Regex.t -> deriv = function
  | Regex.Epsilon -> Atom.Map.empty
  | Atom a ->
    let res = Regex.SetSet.singleton @@ Regex.Set.singleton Regex.epsilon in
    Atom.Map.singleton a res
  | Concat el ->
    let rec aux = function
      | [] -> Atom.Map.empty
      | e :: t ->
        let h = suffix (deriv e) (Regex.concat t) in
        if has_epsilon e
        then union h (aux t)
        else h
    in
    aux el
  | Alt el ->
    Regex.Set.fold (fun e s -> union s (deriv e)) el Atom.Map.empty
  | Rep (i, None, e) ->
    suffix (deriv e) (Regex.rep (max 0 (i-1)) None e)
  | Rep (i, Some j, e) ->
    suffix (deriv e) (Regex.rep (max 0 (i-1)) (Some (max 0 (j-1))) e)
  | Inter el ->
    let e0 = Regex.Set.choose el in
    let el = Regex.Set.remove e0 el in
    Regex.Set.fold (fun e s -> inter s (deriv e)) el (deriv e0)
  | Shuffle (e1, e2) ->
    let m1 = shuffleR (deriv e1) e2 in
    let m2 = shuffleL e1 (deriv e2) in
    union m1 m2

(** DFA construction *)

type state = { fa : Nfa.t ; re2state : Nfa.State.t Regex.Map.t }

let add_state a re =
  let fa, v = Nfa.new_state a.fa (Regex.to_string re) in
  let a = {fa; re2state = Regex.Map.add re v a.re2state } in
  a, v

let has_state a re = Regex.Map.find_opt re a.re2state

let add_transition a st (c,st') =
  { a with fa = Nfa.add_transition a.fa st (c, st') }

let rec goto st0 c re a =
  match has_state a re with
  | Some st ->
    add_transition a st0 (c, st)
  | None ->
    let a, st = add_state a re in
    let a = add_transition a st0 (c, st) in
    explore a (st, re)

and explore a (st, re) =
  let ds = deriv re in
  let f c res = Regex.SetSet.fold (fun ire -> goto st c (Regex.Inter ire)) res in
  Atom.Map.fold f ds a

let make re =
  let fa, st = Nfa.create (Regex.to_string re) in
  let a =
    let re2state = Regex.Map.singleton re st in
    { fa ; re2state }
  in
  let a = explore a (st, re) in
  let final =
    Regex.Map.fold
      (fun re st set -> if has_epsilon re then Nfa.StateSet.add st set else set)
      a.re2state
      Dfa.StateSet.empty
  in
  { a.fa with final }


let test re =
  let re = Parser.parse re in
  let a = make re in
  Fmt.epr "Automaton:@.%a" Nfa.pp a;
  Nfa.dot a;
  a


(*
   Copyright (C) 2020 Gabriel Radanne <drupyog@zoho.com>

   This library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2 of the License, or (at your option) any later version.

   This library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with this library; if not, write to the Free Software
   Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA
*)
