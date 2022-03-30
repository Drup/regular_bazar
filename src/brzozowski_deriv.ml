(** Brzozowski derivatives, in all shapes and forms

    Most operations: 
    *Regular-expression derivatives reexamined*
    by Owens, S., Reppy, J., Turon, A

    Shuffling:
    *Derivatives for Regular Shuffle Expressions*
    by Martin Sulzmann and Peter Thiemann
*)

(** Derivatives *)

module AMap = Atom.Map
open Regex.Infix

type deriv = Regex.t AMap.t

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

let suffix (l : deriv) re : deriv =
  let f re_c = Regex.concat [re_c; re] in
  AMap.map f l

let union : deriv -> deriv -> deriv =
  AMap.union
    (fun _c re1 re2 -> Some (re1 ||| re2))

let inter : deriv -> deriv -> deriv =
  AMap.merge @@ fun _c re1 re2 -> match re1, re2 with
  | Some re1, Some re2 -> Some (re1 &&& re2)
  | _, _ -> None

let rec heads = function
  | Regex.Epsilon -> AMap.empty
  | Atom a -> AMap.singleton a Regex.epsilon
  | Concat el ->
    let rec aux = function
      | [] -> AMap.empty
      | e :: t ->
        let h = suffix (heads e) (Regex.concat t) in
        if has_epsilon e
        then union h (aux t)
        else h
    in
    aux el
  | Alt el ->
    Regex.Set.fold (fun e s -> union s (heads e)) el AMap.empty
  | Rep (i, None, e) ->
    suffix (heads e) (Regex.rep (max 0 (i-1)) None e)
  | Rep (i, Some j, e) ->
    suffix (heads e) (Regex.rep (max 0 (i-1)) (Some (max 0 (j-1))) e)
  | Inter el ->
    Regex.Set.fold (fun e s -> inter s (heads e)) el AMap.empty

(** DFA construction *)

type state = { dfa : Dfa.t ; re2state : Dfa.State.t Regex.Map.t }

let add_state a re =
  let dfa, v = Dfa.new_state a.dfa in
  let a = {dfa; re2state = Regex.Map.add re v a.re2state } in
  a, v

let has_state a re = Regex.Map.find_opt re a.re2state

let add_transition a st (c,st') =
  { a with dfa = Dfa.add_transition a.dfa st (c, st') }

let rec goto st0 c re a =
  match has_state a re with
  | Some st ->
    add_transition a st0 (c, st)
  | None ->
    let a, st = add_state a re in
    let a = add_transition a st0 (c, st) in
    explore a (st, re)

and explore a (st, re) =
  let l = heads re in
  let a = AMap.fold (goto st) l a in
  a

let make re =
  let dfa, st = Dfa.create () in
  let a =
    let re2state = Regex.Map.singleton re st in
    { dfa ; re2state }
  in
  let a = explore a (st, re) in
  let final =
    Regex.Map.fold
      (fun re st set -> if has_epsilon re then Dfa.StateSet.add st set else set)
      a.re2state
      Dfa.StateSet.empty
  in
  { a.dfa with final }


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
